#!/usr/bin/env python3
"""Build the Anki package «Випассана: пали → русский» from the plain-text source in dict/ and deck/.

    python3 build.py [--out PATH] [--now SECONDS]

Writes vipassana-pali-ru.apkg next to this script (or to PATH). Python 3.10+, standard library and PyYAML.
Exit 0 on success. On a problem in the source nothing is written; a message that names the file, the entry and
the problem goes to stderr and the exit code is 1. A traceback is a bug in this script, not a problem of the source.

Source:
  dict/<n>-<subdeck title, spaces as hyphens>.yaml   the cards of one subdeck, in study order
  deck/notetype.yaml front.html back.html style.css   the note type and its card template
  deck/decks.yaml description.html                     the decks, the deck options, the deck description
  deck/collection.yaml                                 the other columns of the collection
  deck/schema.sql                                      the tables of the collection
  deck/static/                                         meta, media, collection.anki2 (copied into the package)

The HTML of the fields, the tags, the check sums and the study order (due) are made here from the plain text.
--now fixes the build time (seconds since the epoch), so that two builds give the same bytes. The bytes of the
package also depend on the SQLite library version (the database header holds it); the content does not."""
import argparse
import hashlib
import json
import os
import re
import sqlite3
import sys
import tempfile
import time
import unicodedata
import zipfile
from collections.abc import Hashable
from html.parser import HTMLParser
from pathlib import Path

sys.dont_write_bytecode = True      # set before the only third-party import: no .pyc files in the user's environment
try:
    import yaml
except ImportError:
    sys.exit("build.py: PyYAML is required (pip install pyyaml)")

HERE = Path(__file__).resolve().parent
DICT_DIR = HERE / "dict"
DECK_DIR = HERE / "deck"
DEFAULT_OUT = HERE / "vipassana-pali-ru.apkg"
APKG_ORDER = ["meta", "collection.anki21", "collection.anki2", "media"]   # member order of the package
FILE_KEYS = ("css_file", "qfmt_file", "afmt_file", "desc_file")          # key X_file: the text of a file in deck/ is X
ZIP_FIRST_TIME, ZIP_LAST_TIME = 315532800, 4354819199                    # 1980-01-01 and 2107-12-31 UTC: the dates of a zip entry

# ---------------------------------------------------------------- constants and text helpers
SEP = "\x1f"
FIELDS = ["Термин", "Чтение", "Перевод", "Пояснение", "Онтология", "Включает", "Связи", "Противоположность"]
PARENT_DECK = "Випассана"
ABBR = {"DN", "MN", "SN", "AN", "Dhp", "Sn", "Snp"}
ROMAN = re.compile(r"^[IVXLCDM]+$")
WORD = re.compile(r"[^\W\d_]+(?:['’\-][^\W\d_]+)*-?")


class BuildError(Exception):
    pass


def nfc(s):
    return unicodedata.normalize("NFC", s)


def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def _lat(ch):
    return ch.isalpha() and unicodedata.name(ch, "").startswith("LATIN")


def wrap(p):
    """plain text -> html: every run of Latin-script words (single spaces between) in span.p,
    except source abbreviations and Roman numerals; digits are never Latin words."""
    toks = []
    for m in WORD.finditer(p):
        w = m.group(0)
        if not all(_lat(c) or c in "'’-" for c in w):
            continue
        core = w.rstrip("-")
        if core in ABBR or ROMAN.match(core):
            continue
        toks.append([m.start(), m.end()])
    runs = []
    for s, e in toks:
        if runs and runs[-1][1] + 1 == s and p[runs[-1][1]] == " ":
            runs[-1][1] = e
        else:
            runs.append([s, e])
    out, pos = [], 0
    for s, e in runs:
        out.append(esc(p[pos:s]))
        out.append("<span class='p'>" + esc(p[s:e]) + "</span>")
        pos = e
    out.append(esc(p[pos:]))
    return "".join(out)


def tseg(s):
    s = strip_marks(nfc(s)).replace("ṃ", "m")
    return re.sub(r"[\s\-]+", "_", s)


class _T(HTMLParser):
    def __init__(s):
        super().__init__(convert_charrefs=True)
        s.o = []
    def handle_data(s, d):
        s.o.append(d)


def plain(h):
    p = _T(); p.feed(h); p.close()
    return "".join(p.o)


def strip_marks(s):
    return "".join(ch for ch in unicodedata.normalize("NFD", s) if not unicodedata.combining(ch))


def sub_n(deck):  # "Випассана::7 Прозрение" -> 7
    return int(deck.split("::")[1].split()[0])


def csum_of(sfld):
    return int(hashlib.sha1(plain(sfld).encode("utf-8")).hexdigest()[:8], 16)


def _sep_split(s):
    return re.split(r"([\s\-]+)", s)


def mirror_caps(term, reading):
    """word i of the reading starts with a capital exactly when word i of the headword does"""
    tp, rp = _sep_split(term), _sep_split(reading)
    if len(tp) != len(rp):
        return reading, False
    out = []
    for t, r in zip(tp, rp):
        if t and r and not re.fullmatch(r"[\s\-]+", t):
            r = (r[0].upper() if t[0].isupper() else r[0].lower()) + r[1:]
        out.append(r)
    return "".join(out), True


# ---------------------------------------------------------------- model
class Card:
    """one note. key = nid (identity). Plain text: term, reading, tr (translation), ex (explanation)."""
    def __init__(s):
        s.key = None
        s.nid = s.cid = s.guid = None
        s.term = s.reading = s.tr = s.ex = None
        s.parents = []          # [("c", key) | ("s", section title)], order = tree path order
        s.kids = []             # keys, order = Включает
        s.links = []            # keys, order = Связи
        s.opp = []              # [("c", key) | ("t", term, gloss_plain)]
        s.deck = None           # full deck name
        s.where = ""            # file and entry, for messages


class Model:
    def __init__(s):
        s.cards = {}            # key -> Card
        s.order = []            # keys in note order (subdecks 1..9, in a file: file order)
        s.decks = {}            # deck name -> id
        s.sec_n = {}            # section title -> subdeck number
        s.isep = " "            # separator between list items in the generated html
        s._pm = None

    def sub_tag(s, title):
        return f"{PARENT_DECK}::{s.sec_n[title]}_{title.replace(' ', '_')}"

    def paths(s, key, _depth=0):
        """tree paths of a card: [(section, [ancestor keys])]; a child extends path 0 of each parent"""
        if s._pm is None:
            s._pm = {}
        if key in s._pm:
            return s._pm[key]
        if _depth > 60:
            raise BuildError("cycle in the hierarchy at " + s.cards[key].term)
        out = []
        for p in s.cards[key].parents:
            if p[0] == "s":
                out.append((p[1], []))
            else:
                pp = s.paths(p[1], _depth + 1)
                if not pp:
                    raise BuildError(f"parent {s.cards[p[1]].term} of {s.cards[key].term} has no tree path")
                sec, anc = pp[0]
                out.append((sec, anc + [p[1]]))
        s._pm[key] = out
        return out

    def base_tags(s, key):
        return ["::".join([s.sub_tag(sec)] + [tseg(s.cards[a].term) for a in anc]) for sec, anc in s.paths(key)]

    def tags(s, key):
        c = s.cards[key]
        kid_bases = [b for k in c.kids for b in s.base_tags(k)]
        out = set()
        for b in s.base_tags(key):
            w = b + "::" + tseg(c.term)
            out.add(w if any(x == w or x.startswith(w + "::") for x in kid_bases) else b)
        return " " + " ".join(sorted(out)) + " " if out else ""

    def li(s, term, gloss_html):
        return f"<li><span class='p'>{esc(term)}</span> — {gloss_html}</li>"

    def ul(s, items):
        return "<ul class='refs'>" + s.isep.join(items) + "</ul>" if items else ""

    def tree_html(s, key):
        ps = s.paths(key)
        if not ps:
            return ""
        secs = []
        for sec, _ in ps:
            if sec not in secs:
                secs.append(sec)
        me = s.cards[key]
        out = []
        for sec in secs:
            root = []
            for sc, anc in ps:
                if sc != sec:
                    continue
                level = root
                for a in anc:
                    node = next((n for n in level if n.get("k") == a), None)
                    if node is None:
                        node = {"k": a, "ch": []}
                        level.append(node)
                    level = node["ch"]
                if not any(n.get("here") for n in level):
                    level.append({"here": True})

            def rnode(n):
                if n.get("here"):
                    return f"<li><span class='here'>{esc(me.term)}</span></li>"
                c = s.cards[n["k"]]
                return (f"<li><span class='p'>{esc(c.term)}</span> <span class='r'>({s.gl(c)})</span>{s.isep}"
                        f"<ul>{s.isep.join(rnode(x) for x in n['ch'])}</ul></li>")
            out.append(f"<div class='tsec'>{esc(sec)}</div>{s.isep}<ul>{s.isep.join(rnode(n) for n in root)}</ul>")
        return "<div class='tree'>" + s.isep.join(out) + "</div>"

    def gl(s, c):
        return s.text_html(c, "Перевод", c.tr)

    def text_html(s, c, fld, plain_text):
        # the field text is the plain text of the source with its Latin-script words marked up by wrap()
        return wrap(plain_text)

    def fields(s, key):
        c = s.cards[key]
        refs = lambda keys: s.ul([s.li(s.cards[k].term, s.gl(s.cards[k])) for k in keys])  # noqa: E731
        opp = []
        for o in c.opp:
            if o[0] == "c":
                opp.append(s.li(s.cards[o[1]].term, s.gl(s.cards[o[1]])))
            else:
                opp.append(s.li(o[1], wrap(o[2])))
        return [c.term, c.reading, s.text_html(c, "Перевод", c.tr), s.text_html(c, "Пояснение", c.ex),
                s.tree_html(key), refs(c.kids), refs(c.links), s.ul(opp)]

    def flds(s, key):
        return SEP.join(s.fields(key))


def ancestors(m, k):
    seen, st = set(), [k]
    while st:
        for p in m.cards[st.pop()].parents:
            if p[0] == "c" and p[1] not in seen:
                seen.add(p[1])
                st.append(p[1])
    return seen


def study_order(m):
    """due per card: subdecks 1..9; in a subdeck ancestors before descendants (preorder, children in
    Включает order after their parent), else note order; new cards without a parent in the subdeck last"""
    due, n = {}, 0
    for name in sorted({c.deck for c in m.cards.values()}, key=sub_n):
        base = [k for k in m.order if m.cards[k].deck == name]
        S = set(base)
        anc = {k: ancestors(m, k) & S for k in base}
        done, out = set(), []

        def emit(k):
            if k in done or not anc[k] <= done:
                return
            done.add(k)
            out.append(k)
            for ch in m.cards[k].kids:
                if ch in S:
                    emit(ch)
        while len(done) < len(S):
            before = len(done)
            for k in base:
                emit(k)
            if len(done) == before:
                raise BuildError("study order: cycle in " + name)
        for k in out:
            due[k] = n
            n += 1
    return due


# ---------------------------------------------------------------- reading the source
def rel(path):
    try:
        return Path(path).relative_to(HERE).as_posix()
    except ValueError:
        return str(path)


def read_text(path):
    """the text of a file as it is: no newline translation, no strip"""
    try:
        return Path(path).read_bytes().decode("utf-8")
    except (OSError, UnicodeDecodeError) as e:
        raise BuildError(f"{rel(path)}: cannot read: {e}") from None


class UniqueKeyLoader(yaml.SafeLoader):
    """safe_load that refuses a mapping with a repeated key (the plain loader keeps the last value and says nothing)"""
    def construct_mapping(self, node, deep=False):
        seen = set()
        pairs = node.value if isinstance(node, yaml.MappingNode) else []      # another kind of node: the base class says so
        for key_node, _ in pairs:
            if key_node.tag == "tag:yaml.org,2002:merge":
                continue
            key = self.construct_object(key_node, deep=True)
            if isinstance(key, Hashable):
                if key in seen:
                    raise yaml.constructor.ConstructorError("while reading a mapping", node.start_mark,
                                                            f"the key {key!r} is used twice", key_node.start_mark)
                seen.add(key)
        return super().construct_mapping(node, deep)


def load_yaml(path):
    try:
        return yaml.load(read_text(path), Loader=UniqueKeyLoader)
    except yaml.MarkedYAMLError as e:
        line = f", line {e.problem_mark.line + 1}" if e.problem_mark else ""
        raise BuildError(f"{rel(path)}{line}: not valid YAML: " + ": ".join(x for x in (e.context, e.problem) if x)) from None
    except yaml.YAMLError as e:
        raise BuildError(f"{rel(path)}: not valid YAML: {e}") from None


def is_int(v):
    """an integer that SQLite stores (signed 64 bit); True and False are not integers here"""
    return isinstance(v, int) and not isinstance(v, bool) and -2 ** 63 <= v < 2 ** 63


def need_dict(obj, path, what):
    if not isinstance(obj, dict):
        raise BuildError(f"{rel(path)}: {what} must be a mapping")
    return obj


def need_list(obj, path, what):
    """a non-empty list of mappings"""
    if not isinstance(obj, list) or not obj:
        raise BuildError(f"{rel(path)}: {what} must be a non-empty list of mappings")
    for j, x in enumerate(obj, 1):
        need_dict(x, path, f"{what} item {j}")
    return obj


def need_json(v, path, what):
    """only what json.dumps writes as it is: text, numbers, true/false, null, lists, mappings with text keys"""
    if isinstance(v, dict):
        for k, x in v.items():
            if not isinstance(k, str):
                raise BuildError(f"{rel(path)}: {what}: the key {k!r} must be text")
            need_json(x, path, f"{what}.{k}")
    elif isinstance(v, list):
        for j, x in enumerate(v, 1):
            need_json(x, path, f"{what}[{j}]")
    elif v is not None and not isinstance(v, (str, int, float)):
        raise BuildError(f"{rel(path)}: {what}: {v!r} is not text, a number, true/false, null, a list or a mapping (quote a date)")


def inline_files(d, path, what):
    """a key `X_file` names a file in deck/; the text of that file becomes the value of X, in the same place"""
    out = {}
    for k, v in d.items():
        if k in FILE_KEYS:
            if k[:-5] in d:
                raise BuildError(f"{rel(path)}: {what}: both {k[:-5]!r} and {k!r}; give one of them")
            if not isinstance(v, str) or Path(v).name != v:
                raise BuildError(f"{rel(path)}: {what}: {k} must be a file name in deck/, got {v!r}")
            out[k[:-5]] = read_text(DECK_DIR / v)
        else:
            out[k] = v
    return out


def with_times(d, mod_after, usn_after, now, path, what):
    """put mod and usn into a note type or deck at the place they have in the Anki JSON"""
    for k in ("mod", "usn"):
        if k in d:
            raise BuildError(f"{rel(path)}: {what}: remove {k!r}: the time is set by build.py")
    out = {}
    for k, v in d.items():
        out[k] = v
        if k == mod_after:
            out["mod"] = now
        if k == usn_after:
            out["usn"] = -1
    if "mod" not in out or "usn" not in out:
        raise BuildError(f"{rel(path)}: {what}: no key {mod_after!r} / {usn_after!r} to put mod and usn after")
    return out


COLLECTION_INTS = ("id", "crt", "scm", "ver", "dty", "usn", "ls")
NOTES_ROW_KEYS = {"flags", "data"}
CARDS_ROW_KEYS = {"ord", "type", "queue", "ivl", "factor", "reps", "lapses", "left", "odue", "odid", "flags", "data"}


def check_notetype(nt, p):
    need_list(nt.get("tmpls"), p, "tmpls")
    need_list(nt.get("flds"), p, "flds")
    if not is_int(nt.get("id")) or [f.get("name") for f in nt["flds"]] != FIELDS:
        raise BuildError(f"{rel(p)}: the note type needs an integer id and flds with the names {FIELDS}, in this order")


def check_collection(col, p):
    for k in COLLECTION_INTS + ("conf", "tags", "notes_row", "cards_row"):
        if k not in col:
            raise BuildError(f"{rel(p)}: missing key {k!r}")
    for k in COLLECTION_INTS:
        if not is_int(col[k]):
            raise BuildError(f"{rel(p)}: {k} must be an integer (64 bit), got {col[k]!r}")
    if not isinstance(col["tags"], str):
        raise BuildError(f"{rel(p)}: tags must be text, got {col['tags']!r}")
    need_json(need_dict(col["conf"], p, "conf"), p, "conf")
    check_rows(col, p)


def check_rows(col, p):
    """notes_row and cards_row: the columns that are the same for every row"""
    for k, keys in (("notes_row", NOTES_ROW_KEYS), ("cards_row", CARDS_ROW_KEYS)):
        row = need_dict(col[k], p, k)
        if set(row) != keys:
            raise BuildError(f"{rel(p)}: {k} needs exactly the keys {sorted(keys)}, got {sorted(row, key=str)}")
        for c, v in row.items():
            if not (isinstance(v, (str, float, bool)) or is_int(v)):
                raise BuildError(f"{rel(p)}: {k}.{c} must be text or a number (an integer of 64 bit), got {v!r}")


def read_static():
    static = {}
    for n in ("meta", "collection.anki2", "media"):
        try:
            static[n] = (DECK_DIR / "static" / n).read_bytes()
        except OSError as e:
            raise BuildError(f"deck/static/{n}: cannot read: {e}") from None
    return static


def load_deck_files(now):
    """note type, decks, options, collection columns, schema, static members"""
    p = DECK_DIR / "notetype.yaml"
    nt = need_dict(load_yaml(p), p, "the note type")
    check_notetype(nt, p)
    nt = with_times(inline_files(nt, p, "the note type"), "type", "type", now, p, "the note type")
    nt["tmpls"] = [inline_files(t, p, f"tmpls item {j}") for j, t in enumerate(nt["tmpls"], 1)]
    need_json(nt, p, "the note type")

    p = DECK_DIR / "decks.yaml"
    dk = need_dict(load_yaml(p), p, "the file")
    need_list(dk.get("decks"), p, "decks")
    need_json(need_dict(dk.get("dconf"), p, "dconf"), p, "dconf")
    decks = [with_times(inline_files(d, p, f"decks item {j}"), "id", "name", now, p, f"decks item {j}")
             for j, d in enumerate(dk["decks"], 1)]
    need_json(decks, p, "decks")

    p = DECK_DIR / "collection.yaml"
    col = need_dict(load_yaml(p), p, "the file")
    check_collection(col, p)
    return nt, decks, dk["dconf"], col, read_text(DECK_DIR / "schema.sql"), read_static()


def check_decks(decks):
    """subdeck number -> (deck name, title); the parent deck must exist"""
    names, ids, subs = set(), set(), {}
    for d in decks:
        if not is_int(d.get("id")) or not isinstance(d.get("name"), str):
            raise BuildError(f"deck/decks.yaml: every deck needs an integer id (64 bit) and a name, got {d!r}")
        if d["name"] in names or d["id"] in ids:
            raise BuildError(f"deck/decks.yaml: deck {d['name']!r}: name or id used twice")
        names.add(d["name"])
        ids.add(d["id"])
        mt = re.fullmatch(re.escape(PARENT_DECK) + r"::(\d+) (\S.*)", d["name"])
        if mt:
            n = int(mt.group(1))
            if n in subs:
                raise BuildError(f"deck/decks.yaml: subdeck number {n} used twice")
            subs[n] = (d["name"], mt.group(2))
    if PARENT_DECK not in names:
        raise BuildError(f"deck/decks.yaml: no deck {PARENT_DECK!r}")
    if len({t for _, t in subs.values()}) != len(subs):
        raise BuildError("deck/decks.yaml: two subdecks have the same title (a section is named by the title)")
    return subs


ENTRY_KEYS = ("term", "reading", "translation", "explanation", "parents", "children", "see_also", "opposites",
              "nid", "cid", "guid")
TEXT_KEYS = ("term", "reading", "translation", "explanation")        # the text that goes into the fields


def label(path, i, e):
    t = e.get("term") if isinstance(e, dict) else None
    return f"{rel(path)} entry {i}" + (f" {t!r}" if isinstance(t, str) else "")


def strings(v):
    """all the text inside a value"""
    if isinstance(v, str):
        yield v
    elif isinstance(v, dict):
        for x in v.values():
            yield from strings(x)
    elif isinstance(v, list):
        for x in v:
            yield from strings(x)


def is_free_opposite(x):
    return isinstance(x, dict) and set(x) == {"term", "gloss"} and isinstance(x["term"], str) and isinstance(x["gloss"], str)


def bad_text(t):
    """why a text cannot go into a field as it is, or None"""
    for ch in t:
        if ch == SEP:
            return "contains U+001F, the separator of the fields"
        if unicodedata.category(ch) == "Cc":
            return f"contains the control character U+{ord(ch):04X}"
    return "starts or ends with white space" if t != t.strip() else None


def check_keys(lab, e, problems):
    for k in e:
        if k not in ENTRY_KEYS:
            problems.append(f"{lab}: unknown key {k!r}")
    for k in ENTRY_KEYS:
        if k not in e:
            problems.append(f"{lab}: missing key {k!r}")


def check_types(lab, e, problems):
    for k in ("term", "reading", "translation", "explanation", "guid"):
        if not isinstance(e[k], str):
            problems.append(f"{lab}: {k} must be text, got {e[k]!r}")
    for k in ("nid", "cid"):
        if not is_int(e[k]):
            problems.append(f"{lab}: {k} must be an integer (64 bit), got {e[k]!r}")
    for k in ("parents", "children", "see_also", "opposites"):
        if not isinstance(e[k], list):
            problems.append(f"{lab}: {k} must be a list")


def check_headword(lab, e, problems):
    for k in ("term", "reading"):
        if not e[k].strip():
            problems.append(f"{lab}: {k} is empty")
        if any(ch in e[k] for ch in "<>&"):
            problems.append(f"{lab}: {k} must not contain <, > or & (it is written to the field as it is)")


def is_text(x):
    return isinstance(x, str)


def is_parent_item(x):
    return isinstance(x, str) or (isinstance(x, dict) and list(x) == ["section"] and isinstance(x["section"], str))


def is_opposite_item(x):
    return isinstance(x, str) or is_free_opposite(x)


def check_refs(lab, e, problems):
    for k, ok, expected in (("children", is_text, "a headword"), ("see_also", is_text, "a headword"),
                            ("parents", is_parent_item, "a headword or {section: <title>}"),
                            ("opposites", is_opposite_item, "a headword or {term: ..., gloss: ...}")):
        for x in e[k]:
            if not ok(x):
                problems.append(f"{lab}: {k}: {expected} is expected, got {x!r}")


def check_chars(lab, e, problems):
    """the text that is written to a field: no control character (wrap() gives \\n and \\t no meaning), no outer white space"""
    texts = [(k, e[k]) for k in TEXT_KEYS]
    for x in e["opposites"]:
        if is_free_opposite(x):
            texts += [(f"opposites {k}", x[k]) for k in ("term", "gloss")]
    for k, t in texts:
        why = bad_text(t)
        if why:
            problems.append(f"{lab}: {k} {why}: {t[:40]!r}")


def check_nfc(lab, e, problems):
    for k in ENTRY_KEYS:
        for t in strings(e[k]):
            if t != nfc(t):
                problems.append(f"{lab}: {k}: text is not in Unicode form NFC: {t[:40]!r}")


def check_entry(path, i, e, problems):
    """types and shape of one entry; returns True if it can be used"""
    lab = label(path, i, e)
    if not isinstance(e, dict):
        problems.append(f"{lab}: an entry must be a mapping")
        return False
    n = len(problems)
    check_keys(lab, e, problems)
    if len(problems) == n:
        check_types(lab, e, problems)
    if len(problems) > n:
        return False
    for check in (check_headword, check_refs, check_chars, check_nfc):
        check(lab, e, problems)
    return len(problems) == n


def dict_files(subs):
    """[(path, subdeck number)] in the order of the subdecks; a file that belongs to no subdeck is an error"""
    expected = {f"{n}-{title.replace(' ', '-')}.yaml": n for n, (_, title) in subs.items()}
    if not DICT_DIR.is_dir():
        raise BuildError("dict/: folder not found")
    for p in sorted(DICT_DIR.glob("*.yaml")):
        if p.name not in expected:
            raise BuildError(f"{rel(p)}: no subdeck for this file; the names are {sorted(expected)}")
    return [(DICT_DIR / f, n) for f, n in sorted(expected.items(), key=lambda x: x[1])]


def read_dict_file(p, deck, problems):
    """[(deck name, path, entry number, entry)] of the entries that can be used"""
    if not p.exists():
        raise BuildError(f"{rel(p)}: missing file for the subdeck {deck!r} (an empty subdeck is the list [])")
    data = load_yaml(p)
    if data is None:
        data = []
    if not isinstance(data, list):
        raise BuildError(f"{rel(p)}: the file must be a list of entries")
    return [(deck, p, i, e) for i, e in enumerate(data, 1) if check_entry(p, i, e, problems)]


def read_entries(subs):
    """all the entries of dict/*.yaml; raises BuildError with all the problems found"""
    problems, rows = [], []
    for p, n in dict_files(subs):
        rows += read_dict_file(p, subs[n][0], problems)
    if problems:
        raise_problems(problems)
    return rows


def make_model(rows, subs, decks_by_name):
    """a Model with a Card for each entry (the text only); a headword, nid, cid or guid used twice is an error"""
    m = Model()
    m.decks = decks_by_name
    for n, (name, title) in subs.items():
        m.sec_n[title] = n
    problems = []
    first = {"headword": {}, "nid": {}, "cid": {}, "guid": {}}
    for deck, p, i, e in rows:
        c = Card()
        c.key = c.nid = e["nid"]
        c.cid, c.guid = e["cid"], e["guid"]
        c.term, c.reading, c.tr, c.ex = e["term"], e["reading"], e["translation"], e["explanation"]
        c.deck, c.where = deck, label(p, i, e)
        for what, val in (("headword", c.term), ("nid", c.nid), ("cid", c.cid), ("guid", c.guid)):
            if val in first[what]:
                problems.append(f"{c.where}: duplicate {what} {val!r}, also in {first[what][val]}")
            else:
                first[what][val] = c.where
        if c.nid in m.cards:
            continue
        m.cards[c.nid] = c
        m.order.append(c.nid)
    if problems:
        raise_problems(problems)
    return m


def make_ref(m, problems):
    """(ref, by_term): by_term maps a headword to a key; ref(card, list name, headword) gives the key of the card
    with that headword, or None and a problem"""
    by_term = {m.cards[k].term: k for k in m.order}

    def ref(c, what, term):
        if term not in by_term:
            problems.append(f"{c.where}: {what}: unknown headword {term!r}")
            return None
        if by_term[term] == c.key:
            problems.append(f"{c.where}: {what}: the card names itself")
            return None
        return by_term[term]
    return ref, by_term


def resolve_parents(m, c, e, ref, problems):
    for x in e["parents"]:
        if isinstance(x, dict):
            if x["section"] not in m.sec_n:
                problems.append(f"{c.where}: parents: unknown section {x['section']!r}; the sections are {sorted(m.sec_n)}")
            else:
                c.parents.append(("s", x["section"]))
        else:
            k = ref(c, "parents", x)
            if k is not None:
                c.parents.append(("c", k))


def resolve_opposites(c, e, ref, by_term, problems):
    for x in e["opposites"]:
        if isinstance(x, dict):
            if x["term"] in by_term:
                problems.append(f"{c.where}: opposites: {x['term']!r} is a card, write its headword instead of {{term, gloss}}")
            else:
                c.opp.append(("t", x["term"], x["gloss"]))
        else:
            k = ref(c, "opposites", x)
            if k is not None:
                c.opp.append(("c", k))


def listed(m, t):
    """an item of parents, children, see_also or opposites, as the source writes it"""
    if t[0] == "c":
        return repr(m.cards[t[1]].term)
    if t[0] == "s":
        return "{section: " + repr(t[1]) + "}"
    return "{term: " + repr(t[1]) + ", gloss: " + repr(t[2]) + "}"


def check_unique(m, c, problems):
    for what, lst in (("parents", c.parents), ("children", [("c", k) for k in c.kids]),
                      ("see_also", [("c", k) for k in c.links]), ("opposites", c.opp)):
        seen = set()
        for t in lst:
            if t in seen:
                problems.append(f"{c.where}: {what}: {listed(m, t)} is listed twice")
            seen.add(t)


def resolve_refs(m, rows):
    """headwords -> keys in parents, kids, links, opp, in the order of the source; a list item used twice is an error"""
    problems = []
    ref, by_term = make_ref(m, problems)
    for deck, p, i, e in rows:
        c = m.cards[e["nid"]]
        resolve_parents(m, c, e, ref, problems)
        for what, dst in (("children", c.kids), ("see_also", c.links)):
            for x in e[what]:
                k = ref(c, what, x)
                if k is not None:
                    dst.append(k)
        resolve_opposites(c, e, ref, by_term, problems)
        check_unique(m, c, problems)
    if problems:
        raise_problems(problems)


def term_of(m, k):
    return m.cards[k].term


def tree_problems(m, k):
    """a card has a parent; parents and children list each other"""
    c, out = m.cards[k], []
    if not c.parents:
        out.append(f"{c.where}: no parents: give a parent card or {{section: <title>}}")
    for t in c.parents:
        if t[0] == "c" and k not in m.cards[t[1]].kids:
            out.append(f"{c.where}: lists {term_of(m, t[1])!r} as a parent, but {term_of(m, t[1])!r} does not list it as a child")
    for ch in c.kids:
        if ("c", k) not in m.cards[ch].parents:
            out.append(f"{c.where}: lists {term_of(m, ch)!r} as a child, but {term_of(m, ch)!r} does not list it as a parent")
    return out


def link_problems(m, k):
    """see_also and the opposites that are cards list each other"""
    c, out = m.cards[k], []
    for other in c.links:
        if k not in m.cards[other].links:
            out.append(f"{c.where}: lists {term_of(m, other)!r} in see_also, but {term_of(m, other)!r} does not list it back")
    for o in c.opp:
        if o[0] == "c" and ("c", k) not in m.cards[o[1]].opp:
            out.append(f"{c.where}: lists {term_of(m, o[1])!r} as an opposite, but {term_of(m, o[1])!r} does not list it back")
    return out


def load_cards(subs, decks_by_name):
    """Model with all cards, from dict/*.yaml; raises BuildError with all problems found"""
    rows = read_entries(subs)
    m = make_model(rows, subs, decks_by_name)
    resolve_refs(m, rows)
    problems = [x for k in m.order for x in tree_problems(m, k) + link_problems(m, k)]
    if problems:
        raise_problems(problems)
    return m


def raise_problems(problems):
    shown = problems[:25]
    more = f"\n  ... and {len(problems) - 25} more" if len(problems) > 25 else ""
    raise BuildError(f"{len(problems)} problem(s):\n  " + "\n  ".join(shown) + more)


def load_source(now):
    nt, decks, dconf, col, schema, static = load_deck_files(now)
    subs = check_decks(decks)
    m = load_cards(subs, {d["name"]: d["id"] for d in decks})
    for k in m.order:                                   # every card needs a tree path (a cycle or a parent without one is an error)
        m.paths(k)
    check_capitals(m)
    return m, nt, decks, dconf, col, schema, static


def check_capitals(m):
    """the source text is never changed here: a reading must start with a capital exactly when its headword does"""
    problems = []
    for k in m.order:
        c = m.cards[k]
        want, ok = mirror_caps(c.term, c.reading)
        if not ok:
            print(f"build.py: warning: capitals: {c.where}: {c.term!r} / {c.reading!r}: different number of words, not checked",
                  file=sys.stderr)
        elif want != c.reading:
            problems.append(f"{c.where}: capitals: the reading {c.reading!r} of the headword {c.term!r} must be {want!r}")
    if problems:
        raise_problems(problems)


# ---------------------------------------------------------------- database and package
def dump_json(o):
    return json.dumps(o, ensure_ascii=False, separators=(",", ":"))


def make_db(path, m, nt, decks, dconf, col, schema, now, now_ms):
    due = study_order(m)
    con = sqlite3.connect(str(path))
    try:
        con.execute("PRAGMA journal_mode=DELETE")
        con.executescript(schema)
        con.execute("insert into col (id, crt, mod, scm, ver, dty, usn, ls, conf, models, decks, dconf, tags) "
                    "values (?,?,?,?,?,?,?,?,?,?,?,?,?)",
                    (col["id"], col["crt"], now_ms, col["scm"], col["ver"], col["dty"], col["usn"], col["ls"],
                     dump_json(col["conf"]), dump_json({str(nt["id"]): nt}), dump_json({str(d["id"]): d for d in decks}),
                     dump_json(dconf), col["tags"]))
        nrow, crow = col["notes_row"], col["cards_row"]
        ncols = ["id", "guid", "mid", "mod", "usn", "tags", "flds", "sfld", "csum"] + list(nrow)
        ccols = ["id", "nid", "did", "mod", "usn", "due"] + list(crow)
        for k in m.order:
            c = m.cards[k]
            flds, tags = m.flds(k), m.tags(k)
            sfld = flds.split(SEP)[0]
            row = dict(nrow, id=c.nid, guid=c.guid, mid=nt["id"], mod=now, usn=-1, tags=tags, flds=flds, sfld=sfld,
                       csum=csum_of(sfld))
            con.execute(f"insert into notes ({','.join(ncols)}) values ({','.join('?' * len(ncols))})", [row[x] for x in ncols])
            row = dict(crow, id=c.cid, nid=c.nid, did=m.decks[c.deck], mod=now, usn=-1, due=due[k])
            con.execute(f"insert into cards ({','.join(ccols)}) values ({','.join('?' * len(ccols))})", [row[x] for x in ccols])
        con.commit()
        ic = con.execute("PRAGMA integrity_check").fetchall()
        if ic != [("ok",)]:
            raise BuildError(f"integrity_check: {ic}")
        con.execute("VACUUM")                           # the file shrinks and holds no text of deleted rows
    except (sqlite3.OperationalError, sqlite3.IntegrityError) as e:
        raise BuildError(f"database: {e} (the tables are in deck/schema.sql, the other columns in deck/collection.yaml)") from e
    finally:
        con.close()
    leftovers = [e for e in ("-wal", "-shm", "-journal") if os.path.exists(str(path) + e)]
    if leftovers:
        raise BuildError(f"leftover files {leftovers}")


def package(path, collection, static, now):
    """zip, deflate level 9, members in the order of APKG_ORDER; the entry date is UTC (no time zone in the bytes)"""
    dt = time.gmtime(now)[:6]
    with zipfile.ZipFile(path, "w") as out:
        for n in APKG_ORDER:
            zi = zipfile.ZipInfo(n, date_time=dt)
            zi.external_attr = 0o100644 << 16
            zi.create_system = 3
            out.writestr(zi, collection if n == "collection.anki21" else static[n],
                         compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)


def build(out, now=None):
    if now is None:
        now_ms = int(time.time() * 1000)                # the clock is read once
        now = now_ms // 1000
    else:
        now_ms = now * 1000
    if not ZIP_FIRST_TIME <= now <= ZIP_LAST_TIME:
        raise BuildError(f"build time {now} is outside 1980-01-01 .. 2107-12-31 UTC ({ZIP_FIRST_TIME} .. {ZIP_LAST_TIME}), "
                         "the dates a zip entry can hold: check --now (and the clock)")
    m, nt, decks, dconf, col, schema, static = load_source(now)
    out = Path(out)
    tmp_out = out.with_name(f"{out.name}.tmp{os.getpid()}")
    try:
        with tempfile.TemporaryDirectory(prefix="vipassana-build-") as tmp:
            db = Path(tmp) / "collection.anki21"
            make_db(db, m, nt, decks, dconf, col, schema, now, now_ms)
            package(tmp_out, db.read_bytes(), static, now)
        os.replace(tmp_out, out)
    finally:
        if tmp_out.exists():
            tmp_out.unlink()
    return len(m.order), len(m.sec_n)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", default=str(DEFAULT_OUT), help="package to write (default: vipassana-pali-ru.apkg next to build.py)")
    ap.add_argument("--now", type=int, default=None, help="build time in seconds since the epoch (default: now); same value, same bytes")
    args = ap.parse_args(argv)
    try:
        n_cards, n_decks = build(args.out, args.now)
    except BuildError as e:                             # a problem in the source: the message names the file and the entry
        print(f"build.py: error: {e}", file=sys.stderr)
        return 1
    except (yaml.YAMLError, OSError) as e:              # a file that cannot be read or written; anything else is a bug: traceback
        print(f"build.py: error: {type(e).__name__}: {e}", file=sys.stderr)
        return 1
    print(f"wrote {args.out}: {n_cards} notes, {n_decks} subdecks, {os.path.getsize(args.out)} bytes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
