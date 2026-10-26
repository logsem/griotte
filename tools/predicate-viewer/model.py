"""Build the predicate viewer's model from a case study's JSON print
(schema 1, see docs/predicate-viewer/schema.md): memory regions, the words in
them, the capabilities in registers and memory with where they point, and
each region's constraints.

    python3 -I model.py FILE.json ...   prints a summary of each model

The JSON keeps the predicate's structure; this module interprets it. Every
optional field may be missing, and an unknown statement, word or right-hand
side is kept as text."""

import json
import re

# ---------- Text helpers ----------


def txt(x):
    """The text of a Term (a string) or of an Addr ({"text": …})."""
    if x is None:
        return ""
    if isinstance(x, str):
        return x
    if isinstance(x, dict):
        if "text" in x:
            return str(x["text"])
        return json.dumps(x, ensure_ascii=False)
    return str(x)


def matching(s, i):
    """Index of the bracket closing the one at s[i], or -1."""
    pairs = {"(": ")", "[": "]", "{": "}"}
    stack = []
    j = i
    while j < len(s):
        c = s[j]
        if c == '"':
            k = s.find('"', j + 1)
            if k < 0:
                return -1
            j = k + 1
            continue
        if c in pairs:
            stack.append(pairs[c])
        elif stack and c == stack[-1]:
            stack.pop()
            if not stack:
                return j
        j += 1
    return -1


def clean(s):
    """Normalise a term for comparisons: one-line, no scope suffix, no outer
    parentheses."""
    s = " ".join(str(s or "").split())
    while True:
        t = re.sub(r"%\w+$", "", s)
        if t.startswith("(") and matching(t, 0) == len(t) - 1:
            s = t[1:-1].strip()
            continue
        return t


def split_op(s, op):
    """Split "A op B" at the first top-level " op "."""
    depth = 0
    for i, c in enumerate(s):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and s.startswith(" " + op + " ", i):
            return s[:i].strip(), s[i + len(op) + 2:].strip()
    return None


def mentions(text, term):
    """term occurs in text as a whole term (not inside a longer name)."""
    if not term:
        return False
    return re.search(r"(?<![\w'])" + re.escape(term) + r"(?![\w'])", text) is not None


def is_num(s):
    return isinstance(s, str) and re.fullmatch(r"\d+", s) is not None


def paren(s):
    s = str(s)
    return f"({s})" if " " in s and not (s.startswith("(") and matching(s, 0) == len(s) - 1) else s


# ---------- Words ----------


def word_text(w):
    """A word printed as in the .txt (FwPrintNotations), on one line."""
    if not isinstance(w, dict):
        return str(w)
    k = w.get("w")
    if k == "int":
        return "WInt " + paren(w.get("text", "?"))
    if k == "entry":
        return " ".join(["entry"] + [paren(w.get(f, "?")) for f in ("mie", "args", "stack", "off")])
    if k in ("cap", "sentry"):
        p = w.get("p", "?")
        if k == "sentry":
            p = f"E-{w.get('kind', '?')} {p}"
        return f"({p}, {w.get('g', '?')}, {txt(w.get('b'))}, {txt(w.get('e'))}, {txt(w.get('a'))})"
    if k == "sealrange":
        return f"[{w.get('perm', '?')}, {w.get('g', '?')}, {txt(w.get('b'))}, {txt(w.get('e'))}, {txt(w.get('a'))}]"
    if k == "sealed":
        return "{ " + txt(w.get("ot")) + ", " + word_text(w.get("inner")) + " }"
    if "text" in w:
        return str(w["text"])
    return json.dumps({x: y for x, y in w.items() if x != "comment"}, ensure_ascii=False)


def cap_of(w):
    """The capability a word is, if it is a structured (tagged) one."""
    if not isinstance(w, dict):
        return None
    k = w.get("w")
    if k == "sealed":
        inner = cap_of(w.get("inner"))
        if inner is None:
            return None
        inner["sealed"] = clean(txt(w.get("ot")))
        inner["text"] = word_text(w)
        return inner
    if k not in ("cap", "sentry", "sealrange"):
        return None
    addr = lambda f: w.get(f) if isinstance(w.get(f), dict) else {"text": txt(w.get(f))}
    return dict(kind="sealrange" if k == "sealrange" else "cap",
                perm=w.get("perm" if k == "sealrange" else "p", "?"),
                sentry=w.get("kind") if k == "sentry" else None,
                loc=w.get("g", "?"),
                b=clean(txt(w.get("b"))), e=clean(txt(w.get("e"))), a=clean(txt(w.get("a"))),
                a_addr=addr("a"), sealed=None, text=word_text(w))


# ---------- Statements ----------


def binders_text(bs):
    out = []
    for b in bs or []:
        names = " ".join(b.get("names", [])) if isinstance(b, dict) else str(b)
        ty = b.get("type") if isinstance(b, dict) else None
        out.append(f"({names} : {ty})" if ty else names)
    return " ".join(out)


def rhs_text(r):
    if not isinstance(r, dict):
        return str(r)
    k = r.get("r")
    if k == "word":
        t = word_text(r.get("word"))
        return "Some " + paren(t) if r.get("some") else t
    if k == "list":
        return "[" + "; ".join(word_text(w) for w in r.get("items", [])) + "]"
    if k == "addr":
        t = txt(r.get("addr"))
        return "Some " + paren(t) if r.get("some") else t
    if k == "union":
        return "\n∪ ".join(part_text(p) for p in r.get("parts", []))
    if "text" in r:
        return str(r["text"])
    return json.dumps(r, ensure_ascii=False)


def pieces_text(pieces):
    out = []
    for p in pieces or []:
        if isinstance(p, dict) and "words" in p:
            out.append("[" + "; ".join(word_text(w) for w in p["words"]) + "]")
        elif isinstance(p, dict) and "term" in p:
            out.append(str(p["term"]))
        else:
            out.append(txt(p))
    return " ++\n  ".join(out) if out else "[]"


def part_text(p):
    if not isinstance(p, dict):
        return str(p)
    if p.get("region"):
        return f"mem_region {paren(txt(p.get('base')))}\n  " + pieces_text(p.get("content"))
    return txt(p.get("text", p))


def with_comment(s, c):
    return f"{s}  -- {c}" if c else s


def stmt_text(s, ind=""):
    """A statement printed on lines, as close to the .txt as is cheap."""
    if not isinstance(s, dict):
        return ind + str(s)
    k = s.get("k")
    c = s.get("comment", "")
    if k == "section":
        return "\n".join([ind + "── " + str(s.get("title", ""))] + [stmt_text(x, ind) for x in s.get("body", [])])
    if k == "exists":
        head = with_comment(ind + "∃ " + binders_text(s.get("binders")) + ",", c)
        return "\n".join([head] + [stmt_text(x, ind + "  ") for x in s.get("body", [])])
    if k == "eq":
        r = rhs_text(s.get("rhs"))
        lhs = txt(s.get("lhs"))
        if isinstance(s.get("rhs"), dict) and s["rhs"].get("r") in ("list", "union"):
            items = s["rhs"].get("items") if s["rhs"].get("r") == "list" else None
            if items is not None and len(items) > 1:
                lines = [with_comment(ind + lhs + " =", c)]
                for i, w in enumerate(items):
                    lines.append(with_comment(f"{ind}    [{i}]  {word_text(w)}", w.get("comment", "") if isinstance(w, dict) else ""))
                return "\n".join(lines)
            if s["rhs"].get("r") == "union":
                lines = [with_comment(ind + lhs + " =", c)]
                for i, p in enumerate(s["rhs"].get("parts", [])):
                    pt = part_text(p).replace("\n", "\n" + ind + "      ")
                    lines.append(with_comment(ind + ("    " if i == 0 else "  ∪ ") + pt, p.get("comment", "") if isinstance(p, dict) else ""))
                return "\n".join(lines)
        return with_comment(f"{ind}{lhs} = {r}", c)
    if k == "disjoint":
        lines = [with_comment(ind + "ranges_disjoint", c)]
        for i, rg in enumerate(s.get("ranges", [])):
            lines.append(with_comment(f"{ind}    [{i:02}]  [{txt(rg.get('b'))}, {txt(rg.get('e'))})", rg.get("comment", "")))
        return "\n".join(lines)
    if "text" in s:
        return with_comment(ind + str(s["text"]), c)
    return with_comment(ind + json.dumps({x: y for x, y in s.items() if x != "comment"}, ensure_ascii=False), c)


def walk(stmts):
    """Every statement, through sections and existentials."""
    for s in stmts or []:
        if not isinstance(s, dict):
            continue
        yield s
        if s.get("k") in ("section", "exists"):
            yield from walk(s.get("body"))


def owner_of(label):
    head = label.split(",")[0].strip()
    if head.startswith("assert"):
        return "assert"
    return head


CMPT_TITLE = re.compile(r"^(\S+) \((trusted|untrusted)(?:, .*)?\)$")
FIELD_REGION = {"cmpt_imports": "PCC range", "cmpt_code": "PCC range",
                "cmpt_data": "CGP range", "cmpt_static_sealed": "static sealed",
                "cmpt_exp_tbl_entries": "export table",
                "cmpt_exp_tbl_handler": "export table",
                "cmpt_exp_tbl_handler_stackless": "export table"}
CMPT_SUBS = set(FIELD_REGION.values())
# Shown after the compartments, in this order of appearance.
LIBRARY_OWNERS = {"switcher", "assert", "allocator"}
FIELD_NOTE = {"cmpt_exp_tbl_handler": "error handler",
              "cmpt_exp_tbl_handler_stackless": "stackless handler"}
REG_LHS = re.compile(r"^(?:(pcc) σ|reg σ !! (\S+)|sreg σ !! (\S+))$")
FIELD_LHS = re.compile(r"^([A-Za-z_]\w*) ([A-Za-z_][\w']*)$")


# ---------- The model ----------


class Model:
    def __init__(self, doc, name=None):
        self.doc = doc if isinstance(doc, dict) else {}
        self.body = self.doc.get("body") if isinstance(self.doc.get("body"), list) else []
        code = self.doc.get("code") if isinstance(self.doc.get("code"), dict) else {}
        self.code = {k: v for k, v in code.items() if isinstance(v, dict) and isinstance(v.get("words"), list)}
        self.uid = 0
        self.rid = 0
        self.regions, self.caps, self.regs, self.reg_notes = [], [], [], []
        self.owners, self.other = {}, []
        self.els = {}
        self.name = name or self.doc.get("case_study") or str(self.doc.get("predicate", "predicate")).replace("_initial_state_ok", "")

    # --- facts read off the statements

    def index(self):
        self.all = list(walk(self.body))
        self.fields = {}       # clean lhs -> eq statement, for record projections
        self.incrs = []        # layout equations A + L = Some B: (A, L, B, lhs text)
        self.eqs = {}          # layout: clean "A + L" -> clean B, from "A + L = Some (B)"
        self.props = []
        self.binder_owner = {}  # variable -> owner name
        for s in self.all:
            k = s.get("k")
            if k == "exists":
                for b in s.get("binders") or []:
                    if isinstance(b, dict):
                        for n in b.get("names", []):
                            self.binder_owner[n] = self.owner_name(n, str(b.get("type", "")))
            elif k == "prop":
                self.props.append(str(s.get("text", "")))
            elif k == "eq":
                lhs = clean(txt(s.get("lhs")))
                lk = s.get("lhs_kind") if isinstance(s.get("lhs_kind"), dict) else {}
                kind = lk.get("kind")
                if kind == "field" or (kind is None and FIELD_LHS.match(lhs) and not lhs.endswith(" σ")):
                    self.fields.setdefault(lhs, s)
                rhs = s.get("rhs") if isinstance(s.get("rhs"), dict) else {}
                tgt = None
                if rhs.get("r") == "addr" and rhs.get("addr") is not None:
                    tgt = clean(txt(rhs.get("addr")))
                elif rhs.get("r", "term") == "term" and "text" in rhs:
                    m = re.fullmatch(r"Some (.+)", clean(rhs["text"]))
                    tgt = clean(m.group(1)) if m else None
                if tgt is None:
                    continue
                if kind == "incr" and lk.get("base") is not None and lk.get("off") is not None:
                    base, off = clean(txt(lk["base"])), clean(str(lk["off"]))
                else:
                    sp = split_op(lhs, "+")
                    if not sp:
                        continue
                    base, off = clean(sp[0]), clean(sp[1])
                self.eqs[f"{base} + {off}"] = tgt
                if lhs != f"{base} + {off}":
                    self.eqs.setdefault(lhs, tgt)
                self.incrs.append((base, off, tgt, lhs))

    def owner_name(self, var, ty):
        if ty.endswith("switcher"):
            return "switcher"
        if ty.endswith("assert"):
            return "assert"
        if ty.endswith("thread"):
            m = re.fullmatch(r"t(\d+)", var)
            return f"thread {m.group(1)}" if m else var
        return var

    def field_parts(self, s):
        lk = s.get("lhs_kind") if isinstance(s.get("lhs_kind"), dict) else {}
        if lk.get("field"):
            return lk["field"], str(lk.get("of", ""))
        m = FIELD_LHS.match(clean(txt(s.get("lhs"))))
        return (m.group(1), m.group(2)) if m else (None, None)

    def resolve_term(self, t, seen=None):
        """What a list term stands for: a code constant, a field's literal
        list, a word, the empty list, or another term."""
        t = clean(t)
        seen = seen or set()
        if t in self.code:
            return dict(k="code", name=t)
        if t == "[]":
            return dict(k="empty")
        s = self.fields.get(t)
        if s is None or t in seen:
            return None
        seen.add(t)
        field, of = self.field_parts(s)
        rhs = s.get("rhs") if isinstance(s.get("rhs"), dict) else {"r": "term", "text": txt(s.get("rhs"))}
        r = rhs.get("r")
        if r == "list":
            return dict(k="list", items=rhs.get("items") or [], field=field, of=of, stmt=s)
        if r == "word":
            return dict(k="word", word=rhs.get("word"), field=field, of=of, stmt=s)
        if r == "term" or "text" in rhs:
            inner = self.resolve_term(str(rhs.get("text", "")), seen)
            if inner:
                inner.setdefault("via", rhs.get("text"))
                inner.setdefault("field", field)
                inner.setdefault("of", of)
                return inner
            return dict(k="text", text=str(rhs.get("text", "")), field=field, of=of)
        return dict(k="text", text=rhs_text(rhs), field=field, of=of)

    def arbitrary_code(self, o):
        return any(re.search(r"Forall is_int \(cmpt_code " + re.escape(o) + r"\)", p) for p in self.props)

    def arbitrary_data(self, o):
        return any(re.search(r"Forall \(initial_data_word.*\(cmpt_data " + re.escape(o) + r"\)", p) for p in self.props)

    # --- regions

    def new_region(self, b, e, label, implicit=False, owner=None):
        label = label or f"[{b}, {e})"
        if owner is None:
            owner = owner_of(label) if label and not label.startswith("[") else self.owner_from_addr(b)
        self.rid += 1
        r = dict(id=f"r{self.rid - 1}", b=b, e=e, label=label, owner=owner,
                 sub=label.split(",", 1)[1].strip() if "," in label and not label.startswith("[") else "",
                 content=None, pieces=None, items=[], caps=[], constraints=[],
                 implicit=implicit, mem_comment="", cells=[], badges=[], code_names=[])
        self.regions.append(r)
        return r

    def owner_from_addr(self, b):
        for tok in reversed(re.findall(r"[\w']+", b)):
            if tok in self.binder_owner:
                return self.binder_owner[tok]
        return "machine"

    def region_by(self, b, e=None):
        for r in self.regions:
            if r["b"] == b and (e is None or r["e"] == e):
                return r
        return None

    def build_regions(self):
        for s in self.all:
            if s.get("k") == "disjoint":
                for rg in s.get("ranges") or []:
                    if not isinstance(rg, dict):
                        continue
                    b, e = clean(txt(rg.get("b"))), clean(txt(rg.get("e")))
                    if not self.region_by(b, e):
                        self.new_region(b, e, rg.get("comment", ""))
        mem = next((s for s in self.all if s.get("k") == "eq" and (
            (s.get("lhs_kind") or {}).get("kind") == "mem" if isinstance(s.get("lhs_kind"), dict)
            else clean(txt(s.get("lhs"))) == "mem σ")), None)
        self.mem_stmt = mem
        rhs = mem.get("rhs") if mem and isinstance(mem.get("rhs"), dict) else None
        parts = rhs.get("parts") if rhs and rhs.get("r") == "union" else ([] if rhs is None else [{"region": False, "text": rhs_text(rhs)}])
        heap = []
        for p in parts or []:
            if not isinstance(p, dict):
                p = {"region": False, "text": str(p)}
            com = p.get("comment", "")
            if p.get("region") and p.get("base") is None:
                p = {"region": False, "text": txt(p.get("text")) if "text" in p else json.dumps(p, ensure_ascii=False), "comment": com}
            if p.get("region"):
                base = clean(txt(p.get("base")))
                r = self.region_by(base)
                if r is None:
                    r = self.new_region(base, "", com or f"mem_region {paren(base)}")
                    r["e"] = ""
                if not r["sub"] and "," in com:
                    r["label"], r["owner"], r["sub"] = com, owner_of(com), com.split(",", 1)[1].strip()
                r["pieces"] = p.get("content") if isinstance(p.get("content"), list) else []
                r["content"] = f"mem_region {paren(base)}\n  " + pieces_text(r["pieces"])
                r["mem_comment"] = com
            else:
                heap.append(p)
        for p in heap:
            t = txt(p.get("text", p))
            r = dict(id=f"rheap{len(heap) > 1 and heap.index(p) or ''}", b="heap_b", e="heap_e",
                     label=p.get("comment") or t, owner="heap", sub="", content=t,
                     pieces=[{"term": t}], items=[], caps=[], constraints=[], implicit=False,
                     mem_comment=p.get("comment", ""), cells=[], badges=[], code_names=[], heap=True)
            self.regions.insert(0, r)
        # the switcher and the libraries go right after the compartments,
        # before the threads
        lib = [r for r in self.regions if r["owner"] in LIBRARY_OWNERS]
        rest = [r for r in self.regions if r["owner"] not in LIBRARY_OWNERS]
        at = max((i + 1 for i, r in enumerate(rest) if r["sub"] in CMPT_SUBS), default=len(rest))
        self.regions[:] = rest[:at] + lib + rest[at:]

    # --- cells

    def cell(self, r, kind, **kw):
        c = dict(id=f"w{self.uid}", region=r["id"], kind=kind, addr=None, aliases=[], offB=None,
                 label="", points=[], name="")
        self.uid += 1
        c.update(kw)
        self.els[c["id"]] = c
        return c

    def add_cap(self, cap, src_kind, src, where, comment=""):
        cap = dict(cap, id=f"c{len(self.caps)}", src_kind=src_kind, src=src, where=where,
                   comment=comment, target=None, anchor=None, bAnchor=None, eAnchor=None)
        self.caps.append(cap)
        return cap["id"]

    def word_cell(self, r, w, src_kind, where, field=None, of=None, index=None):
        if not isinstance(w, dict):
            w = {"w": "term", "text": str(w)}
        com = w.get("comment", "")
        k = w.get("w")
        if k == "entry":
            c = self.cell(r, "word", entry=dict(mie=w.get("mie", "?"), args=w.get("args", "?"),
                                                 stack=w.get("stack", "?"), off=w.get("off", "?"),
                                                 index=index if index is not None else 0,
                                                 owner=of or r["owner"], comment=com))
            if index is not None:
                c["aliases"].append(f"{r['b']} ^+ ExportTable_offset_entry {index}")
            return c
        cap = cap_of(w)
        if cap:
            cid = self.add_cap(cap, src_kind, r["id"], where, com)
            r["caps"].append(cid)
            return self.cell(r, "word", cap=cid, comment=com)
        if k == "term":
            res = self.resolve_term(w.get("text", ""))
            if res and res["k"] == "word":
                c = self.word_cell(r, res["word"], "item", res.get("field") or w.get("text", ""), res.get("field"), res.get("of"))
                c["note"] = FIELD_NOTE.get(res.get("field"), "= " + str(w.get("text", "")))
                c["comment"] = c.get("comment") or com or (res["stmt"].get("comment", "") if res.get("stmt") else "")
                c["via"] = w.get("text", "")
                return c
        return self.cell(r, "word", text=word_text(w), comment=com)

    def list_cells(self, r, items, field, of):
        cells = []
        for i, w in enumerate(items):
            c = self.word_cell(r, w, "item", f"{field} [{i}]", field, of,
                               index=i if field == "cmpt_exp_tbl_entries" else None)
            cells.append(c)
            if not c.get("entry"):
                r["items"].append(dict(index=i, field=field, value=word_text(w),
                                       comment=w.get("comment", "") if isinstance(w, dict) else "",
                                       caps=[c["cap"]] if c.get("cap") else []))
        if not cells:
            cells.append(self.cell(r, "empty", text="empty list: no words"))
        return cells

    def code_cell(self, r, name, what, note=""):
        n = len(self.code[name]["words"])
        if name not in r["code_names"]:
            r["code_names"].append(name)
        caps = {}  # word index -> capability id, for the capability words of the constant
        for i, w in enumerate(self.code[name]["words"]):
            cap = cap_of(w)
            if cap:
                caps[str(i)] = self.add_cap(cap, "mem", r["id"], f"{name} [{i}]", w.get("comment", ""))
        return self.cell(r, "comp", what=what, len=n, code=name, note=note, code_caps=caps)

    def piece_cells(self, r, p):
        if isinstance(p, dict) and "words" in p:
            ws = p["words"] if isinstance(p["words"], list) else []
            if not ws:
                return [self.cell(r, "empty", text="empty list: no words")]
            return [self.word_cell(r, w, "mem", "contents") for w in ws]
        t = clean(txt(p.get("term") if isinstance(p, dict) and "term" in p else p))
        if r.get("heap"):
            return [self.cell(r, "comp", what=t, note=r["label"])]
        res = self.resolve_term(t)
        m = FIELD_LHS.match(t)
        field, of = (m.group(1), m.group(2)) if m else (None, None)
        head = p.get("head", "") if isinstance(p, dict) else ""
        args = p.get("args") if isinstance(p, dict) and isinstance(p.get("args"), list) else []
        if (not res or res["k"] == "text") and isinstance(p, dict) and isinstance(p.get("unfolded"), list):
            return self.unfolded_cells(r, t, head, p["unfolded"])
        rep = self.replicate_of(t, head, args)
        if rep and not res:
            return self.replicate_cells(r, t, *rep)
        if res:
            field, of = res.get("field") or field, res.get("of") or of
            k = res["k"]
            if k == "code":
                return [self.code_cell(r, res["name"], t, "" if res["name"] == t else "= " + res["name"])]
            if k == "list":
                return self.list_cells(r, res["items"], field, of)
            if k == "word":
                return [self.word_cell(r, res["word"], "item", field or t, field, of)]
            if k == "empty":
                return [self.cell(r, "empty", text=(t + " = []: no words") if t != "[]" else "empty list: no words")]
            if k == "text":
                note = "= " + res["text"]
                if field == "cmpt_code" and re.fullmatch(r"\w+", res["text"]):
                    note += " · instructions not printed"
                return [self.cell(r, "comp", what=t, note=note)]
        if field == "cmpt_code" and of and self.arbitrary_code(of):
            return [self.cell(r, "comp", what=t, arb="arbitrary integers, any length", code_like=True)]
        if field == "cmpt_data" and of and self.arbitrary_data(of):
            return [self.cell(r, "comp", what=t, arb="arbitrary data words, any length",
                              note="initial_data_word: integers or capabilities within the CGP range")]
        note = "instructions not printed" if re.fullmatch(r"\w+_instrs", t) else ""
        c = self.cell(r, "comp", what=t, note=note, code_like=bool(note))
        caps = []
        for i, w in enumerate(args):
            cap = cap_of(w)
            if cap:
                cid = self.add_cap(cap, "mem", r["id"], f"{head or 'argument'} arg {i}",
                                   w.get("comment", "") if isinstance(w, dict) else "")
                r["caps"].append(cid)
                caps.append(cid)
        if caps:
            c["arg_caps"] = caps
            c["head"] = head
            c["args_text"] = [word_text(w) for w in args]
        return [c]

    def unfolded_cells(self, r, t, head, ws):
        """The words of a piece the printer unfolded (head constant, beta)."""
        if not ws:
            return [self.cell(r, "empty", text=f"{t} = []: no words")]
        cells = []
        for i, w in enumerate(ws):
            c = self.word_cell(r, w, "mem", f"{head or t} [{i}]")
            c["from"], c["from_i"] = t, i
            cells.append(c)
        return cells

    def replicate_of(self, t, head, args):
        """(n, w) for `replicate n w`, from head/args or from the text."""
        if head == "replicate" and len(args) == 2:
            n = args[0].get("text") if isinstance(args[0], dict) else args[0]
            w = args[1] if isinstance(args[1], dict) else {"w": "term", "text": str(args[1])}
            n = clean(str(n))
            return (int(n), w) if is_num(n) else None
        m = re.fullmatch(r"replicate (\d+) (.+)", t)
        if m:
            wt = clean(m.group(2))
            mi = re.fullmatch(r"WInt (\S+)", wt)
            return int(m.group(1)), ({"w": "int", "text": clean(mi.group(1))} if mi else {"w": "term", "text": wt})
        return None

    REP_EXPAND = 8

    def replicate_cells(self, r, t, n, w):
        """`replicate n w`: n cells of w, or one compressed cell when n is large."""
        if n == 0:
            return [self.cell(r, "empty", text=f"{t}: no words")]
        if n <= self.REP_EXPAND:
            cells = [self.word_cell(r, w, "mem", f"replicate [{i}]") for i in range(n)]
            for i, c in enumerate(cells):
                c["from"], c["from_i"] = t, i
            return cells
        cap = cap_of(w)
        cid = None
        if cap:
            cid = self.add_cap(cap, "mem", r["id"], f"replicate {n}", w.get("comment", ""))
            r["caps"].append(cid)
        return [self.cell(r, "comp", what=t, len=n, rep=dict(n=n, text=word_text(w), cap=cid))]

    def build_cells(self, r):
        if r["pieces"] is None:
            c = self.cell(r, "comp", what="not in the printed memory" if r["implicit"] else "contents not printed",
                          note="known only through the capabilities that point here")
            groups, comps = [[c]], [None]
        else:
            groups, comps = [], []
            for p in r["pieces"]:
                g = self.piece_cells(r, p)
                for c in g:
                    c["piece"] = len(groups)
                groups.append(g)
                comps.append(clean(p["term"]) if isinstance(p, dict) and "term" in p else None)
        r["cells"] = [c for g in groups for c in g]
        self.offsets(r, groups, comps)

    def offsets(self, r, groups, comps):
        """Give every cell an address: offsets from the band base while they
        are known, then named addresses from the layout equations."""
        eq = self.eqs
        cur, n, offB = r["b"], 0, 0
        short = lambda a: "b" if a == r["b"] else a
        for g, comp in zip(groups, comps):
            if comp and comp.startswith("cmpt_exp_tbl_entries ") and f"{r['b']} + ExportTable_offset_entries" in eq:
                cur, n = eq[f"{r['b']} + ExportTable_offset_entries"], 0
            start = cur if cur is not None and n == 0 else None
            goff = offB
            for c in g:
                if c["kind"] == "empty":
                    continue
                c["offB"] = offB
                if cur is not None and n and f"{cur} + {n}" in eq:
                    cur, n = eq[f"{cur} + {n}"], 0
                if cur is not None and n is not None:
                    c["addr"] = cur if n == 0 else f"{cur} ^+ {n}"
                    c["label"] = short(cur) if n == 0 else f"{short(cur)}+{n}"
                else:
                    c["label"] = "?"
                if offB is not None and c["addr"] != f"{r['b']} ^+ {offB}" and offB > 0:
                    c["aliases"].append(f"{r['b']} ^+ {offB}")
                if c["kind"] == "word":
                    n = n + 1 if n is not None else None
                    offB = offB + 1 if offB is not None else None
                else:
                    ln = c.get("len")
                    n = n + ln if ln is not None and n is not None else None
                    offB = offB + ln if ln is not None and offB is not None else None
            if start is not None and comp:
                nxt = eq.get(f"{start} + length ({comp})") or eq.get(f"{start} + length {comp}")
                if not nxt and n is None:
                    keys = sorted((k for k in eq if k.startswith(start + " + ")), key=len)
                    if keys:
                        nxt = eq[keys[0]]
                        ln = keys[0][len(start) + 3:]
                        last = g[-1]
                        if last["kind"] == "comp":
                            last["len_text"] = f"{ln} words" if is_num(ln) else ln
                            if is_num(ln) and goff is not None and last["offB"] is not None:
                                last["len"] = int(ln) - (last["offB"] - goff)
                                offB = goff + int(ln)
                            elif is_num(ln) and len(g) == 1:
                                last["len"] = int(ln)
                                offB = last["offB"] + int(ln) if last["offB"] is not None else None
                if nxt:
                    cur, n = nxt, 0
                elif n is None:
                    cur = None
        cells = r["cells"]
        k = f"{r['b']} + ExportTable_offset_cgp"
        if r.get("sub") == "export table" and len(cells) > 1 and k in eq:
            cells[1]["aliases"].append(eq[k])
        for c in cells:
            c["name"] = r["b"] if c["label"] == "b" else c["addr"] or c["label"]

    # --- addresses

    def length_of(self, t):
        t = clean(t)
        res = self.resolve_term(t)
        if res:
            if res["k"] == "code":
                return len(self.code[res["name"]]["words"])
            if res["k"] == "list":
                return len(res["items"])
            if res["k"] == "empty":
                return 0
        m = re.fullmatch(r"replicate (\d+) .+", t)
        return int(m.group(1)) if m else None

    def eval_off(self, off):
        """The value of an offset text (Z scope): numerals and lengths of known
        lists, summed; None when unknown."""
        total = 0
        parts, rest = [], clean(off)
        while (sp := split_op(rest, "+")):
            parts.append(sp[0])
            rest = sp[1]
        for part in parts + [rest]:
            part = clean(part)
            if is_num(part):
                total += int(part)
                continue
            m = re.fullmatch(r"length (.+)", part)
            n = self.length_of(m.group(1)) if m else None
            if n is None:
                return None
            total += n
        return total

    def known(self, a):
        return any(c["addr"] == a or a in c["aliases"] or any(p["key"] == a for p in c["points"])
                   for r in self.regions for c in r["cells"]) or any(r["b"] == a or r["e"] == a for r in self.regions)

    def place_named(self):
        """Named addresses inside the tape from the layout equations
        A + L = Some B, when A is located and L evaluates."""
        for base, off, tgt, lhs in self.incrs:
            if self.known(tgt):
                continue
            n = self.eval_off(off)
            if n is None:
                continue
            for r in self.regions:
                cells = [c for c in r["cells"] if c["kind"] != "empty"]
                if r["b"] == base:
                    start = 0
                else:
                    bc = next((c for c in cells if c["addr"] == base or base in c["aliases"]), None)
                    start = bc["offB"] if bc else None
                if start is None:
                    continue
                k = start + n
                for c in cells:
                    if c["offB"] is None:
                        break
                    ln = 1 if c["kind"] == "word" else c.get("len")
                    if c["offB"] == k and not c.get("code"):
                        c["aliases"].append(tgt)
                        break
                    if ln is None or k < c["offB"] + ln:
                        if k >= c["offB"]:
                            self.point(c, tgt, tgt, lhs, row=k - c["offB"] if c.get("code") and ln is not None else None)
                        break
                break

    def point(self, cell, key, text, note=None, end=False, row=None, unknown=False):
        p = next((x for x in cell["points"] if x["key"] == key), None)
        if p is None:
            p = dict(id=f"p{self.uid}", key=key, text=text, name=text, notes=[], end=end, cell=cell["id"],
                     unknown=unknown)
            self.uid += 1
            if row is not None and cell.get("code"):
                p["code_row"] = row
            cell["points"].append(p)
            self.els[p["id"]] = p
        if note and note not in p["notes"]:
            p["notes"].append(note)
        return p["id"]

    def bands(self, hint):
        rs = [r for r in self.regions if r["id"] == hint] + [r for r in self.regions if r["id"] != hint]
        return rs

    def code_labels(self, name):
        """Label (without its leading dot) -> word index, from `labels` and
        from `asm` (a label is at the next line that takes a word)."""
        e = self.code.get(name) or {}
        out = {}
        labels = e.get("labels") if isinstance(e.get("labels"), dict) else {}
        for k, v in labels.items():
            if is_num(str(k)):
                for x in str(v).split(","):
                    out.setdefault(x.strip().lstrip("."), int(k))
        pending = []
        for ln in e.get("asm") if isinstance(e.get("asm"), list) else []:
            if not isinstance(ln, dict):
                continue
            if "label" in ln:
                pending.append(str(ln["label"]).lstrip("."))
            elif isinstance(ln.get("index"), int):
                for x in pending:
                    out.setdefault(x, ln["index"])
                pending = []
        return out

    def walk_from(self, cells, i, k, key, text):
        for c in cells[i:]:
            if c["kind"] == "empty":
                continue
            if c["kind"] == "word":
                if k == 0:
                    return c["id"]
                k -= 1
                continue
            ln = c.get("len")
            if ln is None or k < ln:
                if k == 0 and not c.get("code"):
                    return c["id"]
                return self.point(c, key, text, row=k if c.get("code") else None)
            k -= ln
        return None

    def resolve(self, addr, hint=None):
        """The cell or point an address designates, or None."""
        if not isinstance(addr, dict):
            addr = {"text": txt(addr)}
        e = clean(addr.get("text", ""))
        bands = self.bands(hint)
        for r in bands:
            for c in r["cells"]:
                if c["addr"] == e or e in c["aliases"]:
                    if c.get("code") and c.get("len"):
                        return self.point(c, e, c["label"], row=0)
                    return c["id"]
                for p in c["points"]:
                    if p["key"] == e:
                        return p["id"]
        for r in bands:
            if r["b"] == e:
                f = next((c for c in r["cells"] if c["kind"] != "empty"), None)
                if f:
                    return f["id"]
        base, off, label = addr.get("base"), addr.get("off"), addr.get("label")
        if base is None:
            sp = split_op(e, "^+")
            sm = split_op(e, "^-")
            if sp:
                base, off = sp
            elif sm:
                base, off = sm[0], "-" + sm[1]
        if base is None:
            return None
        base = clean(base)
        off = clean(off) if off is not None else None
        for r in bands:
            cells = [c for c in r["cells"] if c["kind"] != "empty"]
            if r["b"] == base:
                i = 0
            else:
                i = next((j for j, c in enumerate(cells) if c["addr"] == base or base in c["aliases"]), None)
            if i is None:
                continue
            sb = "b" if r["b"] == base else base
            if label is not None:
                code = next((c for c in cells[i:] if c.get("code")), None)
                if code:
                    idx = self.code_labels(code["code"]).get(str(label).lstrip("."))
                    return self.point(code, e, f"{sb} ^+ label {label}", row=idx, unknown=idx is None)
                c = next((c for c in cells[i:] if c["kind"] == "comp"), cells[i] if i < len(cells) else None)
                return self.point(c, e, f"{sb} ^+ label {label}", unknown=True) if c else None
            if off is None:
                return cells[i]["id"] if i < len(cells) else None
            if is_num(off):
                res = self.walk_from(cells, i, int(off), e, f"{sb}+{off}")
                if res:
                    return res
                last = next((c for c in reversed(cells) if c["kind"] == "comp"), None)
                return self.point(last, e, f"{sb}+{off}") if last else None
            if off.startswith("-"):
                continue
            c = next((c for c in cells[i:] if c.get("code") or c.get("code_like")), None) or \
                next((c for c in cells[i:] if c["kind"] == "comp"), None)
            if c:
                return self.point(c, e, f"{sb} ^+ {off}", unknown=True)
        if off and off.startswith("-"):
            for r in bands:
                if r["e"] == base:
                    comp = next((c for c in reversed(r["cells"]) if c["kind"] == "comp"), None)
                    if comp:
                        return self.point(comp, e, f"e ^- {off[1:]}", end=True,
                                          row=None)
        return None

    # --- registers, compartments, sections

    def build_regs(self):
        regsec = [s for s in self.sections if str(s.get("title", "")).startswith("Registers")]
        seen = set()
        order = []
        for s in self.all:
            if s.get("k") != "eq":
                continue
            lk = s.get("lhs_kind") if isinstance(s.get("lhs_kind"), dict) else None
            lhs = clean(txt(s.get("lhs")))
            name = bank = None
            if lk is not None:
                if lk.get("kind") != "reg":
                    continue
                bank = lk.get("bank", "other")
                name = "pcc" if bank == "pc" else str(lk.get("name", lhs))
            else:
                m = REG_LHS.match(lhs)
                if not m:
                    continue
                name = m.group(1) or m.group(2) or m.group(3)
                bank = "pc" if m.group(1) else ("gpr" if m.group(2) else "sreg")
            seen.add(id(s))
            rhs = s.get("rhs") if isinstance(s.get("rhs"), dict) else {"r": "term", "text": txt(s.get("rhs"))}
            entry = dict(name=name, bank=bank, value="", comment=s.get("comment", ""), cap=None)
            if rhs.get("r") == "word":
                w = rhs.get("word")
                entry["value"] = word_text(w)
                cap = cap_of(w)
                if cap:
                    entry["cap"] = self.add_cap(cap, "reg", name, bank, entry["comment"])
            else:
                v = rhs_text(rhs)
                entry["value"] = v[5:].strip() if v.startswith("Some ") else v
            self.regs.append(entry)
        # ∀ r, r ∉ {[…]} → reg σ !! r = Some w: every other register of the bank
        explicit = {(g["bank"], g["name"]) for g in self.regs}
        for s in self.all:
            if s.get("k") != "regs_except":
                continue
            seen.add(id(s))
            bank = str(s.get("bank") or "gpr")
            exc = {str(x) for x in s.get("except") or []}
            w = s.get("value")
            listed = []
            for name in s.get("all") or []:
                name = str(name)
                if bank == "gpr":
                    order.append(name)
                if name in exc or (bank, name) in explicit:
                    continue
                explicit.add((bank, name))
                entry = dict(name=name, bank=bank, value=word_text(w), comment=s.get("comment", ""), cap=None,
                             via="others")
                cap = cap_of(w)
                if cap:
                    entry["cap"] = self.add_cap(cap, "reg", name, bank, entry["comment"])
                self.regs.append(entry)
                listed.append(name)
            text = s.get("text") or stmt_text(dict(s, comment=""))
            self.reg_notes.append(dict(text=str(text), comment=s.get("comment", ""), listed=listed, bank=bank))
        if order:
            rank = {n: i for i, n in enumerate(order)}
            self.regs.sort(key=lambda g: (g["bank"] != "gpr", rank.get(g["name"], len(rank)) if g["bank"] == "gpr" else 0))
        for sec in regsec:
            for s in walk(sec.get("body")):
                if id(s) in seen or s.get("k") == "exists":
                    continue
                if s.get("k") == "eq" and isinstance(s.get("lhs_kind"), dict) and s["lhs_kind"].get("kind") == "reg":
                    continue
                self.reg_notes.append(dict(text=stmt_text(dict(s, comment="")), comment=s.get("comment", "")))

    def attach_sections(self):
        handled = set()
        for sec in self.sections:
            title = str(sec.get("title", ""))
            m = CMPT_TITLE.match(title)
            if not m:
                continue
            handled.add(id(sec))
            c = m.group(1)
            self.owners[c] = dict(kind=m.group(2), facts=[])
            for st in sec.get("body") or []:
                whole = stmt_text(st)
                refs = [r for r in self.regions if r["owner"] == c and any(
                    mentions(whole, f"{f} {c}") and r["sub"] == sub for f, sub in FIELD_REGION.items())]
                if not refs:
                    self.owners[c]["facts"].append(whole)
                for r in refs:
                    r["constraints"].append(dict(text=whole, section=title))
        for sec in self.sections:
            title = str(sec.get("title", ""))
            if not title.endswith(", layout"):
                continue
            handled.add(id(sec))
            rest = []
            for st in sec.get("body") or []:
                if isinstance(st, dict) and st.get("k") == "disjoint":
                    continue
                whole = stmt_text(st)
                hits = [r for r in self.regions if not r.get("heap") and (mentions(whole, r["b"]) or mentions(whole, r["e"]))]
                for r in hits:
                    r["constraints"].append(dict(text=whole, section=title))
                if not hits:
                    rest.append(whole)
            if rest:
                if title == "image, layout":
                    self.other.append(dict(title=title, stmts=rest))
                else:
                    o = title.split(",")[0]
                    self.owners.setdefault(o, dict(kind="other", facts=[]))["facts"].extend(rest)
        for sec in self.sections:
            title = str(sec.get("title", ""))
            if title.startswith("Machine"):
                handled.add(id(sec))
                stmts = []
                for st in sec.get("body") or []:
                    whole = stmt_text(st)
                    stmts.append(whole)
                    for r in self.regions:
                        if (r["implicit"] or r["owner"] == "heap") and mentions(whole, r["b"]):
                            r["constraints"].append(dict(text=whole, section=title))
                self.other.append(dict(title=title, stmts=stmts))
            elif title.startswith("Memory"):
                handled.add(id(sec))
                notes = [stmt_text(st) for st in sec.get("body") or [] if st is not self.mem_stmt]
                if notes:
                    self.other.append(dict(title="Memory, other", stmts=notes))
            elif title.startswith("Registers"):
                handled.add(id(sec))
            elif id(sec) not in handled:
                self.other.append(dict(title=title, stmts=[stmt_text(st) for st in sec.get("body") or []]))

    def badges(self, r):
        out = []
        if r["sub"] == "PCC range" and self.arbitrary_code(r["owner"]):
            out.append(["arb", "arbitrary code: integers only"])
        if r["sub"] == "CGP range" and self.arbitrary_data(r["owner"]):
            out.append(["arb", "arbitrary data: initial_data_word"])
        h = self.fields.get(f"cmpt_exp_tbl_handler {r['owner']}")
        if r["sub"] == "export table" and h and re.search(r"WInt eh_", rhs_text(h.get("rhs"))):
            out.append(["arb", "arbitrary handlers"])
        for n in r["code_names"]:
            ln = len(self.code[n]["words"])
            out.append(["code", f"{n}: {ln} word{'s' if ln != 1 else ''}" + (", instructions" if self.code[n].get("instrs") else "")])
        for c in r["cells"]:
            if c.get("code_like") and not c.get("arb"):
                out.append(["code", c["what"] + " (not printed)"])
        if r["implicit"]:
            out.append(["", "implicit"])
        return out

    # --- the whole model

    def code_out(self, n):
        """A code constant for the page: its words, the instruction of each
        encoded word (no integer then), labels, and the asm listing."""
        e = self.code[n]
        words = e["words"]
        instrs = e.get("instrs") if isinstance(e.get("instrs"), list) and len(e["instrs"]) == len(words) else None
        asm = []
        covered = set()
        for ln in e.get("asm") if isinstance(e.get("asm"), list) else []:
            if not isinstance(ln, dict):
                continue
            d = ln.get("depth", 0) if isinstance(ln.get("depth"), int) else 0
            ix = ln.get("index") if isinstance(ln.get("index"), int) and 0 <= ln.get("index") < len(words) else None
            if "label" in ln:
                asm.append(["l", str(ln["label"]), None, d])
            elif "instr" in ln and ix is not None:
                asm.append(["i", str(ln["instr"]), ix, d])
                covered.add(ix)
            elif "symbol" in ln:
                asm.append(["s", str(ln["symbol"]), ix, d])
            elif "block" in ln:
                asm.append(["b", str(ln["block"]), None, 0])
        is_instr = lambda i: (instrs is not None and instrs[i] is not None) or i in covered
        out = dict(n=len(words),
                   w=[None if is_instr(i) and isinstance(w, dict) and w.get("w") == "int" else word_text(w)
                      for i, w in enumerate(words)])
        if instrs is not None:
            out["i"] = [None if x is None else str(x) for x in instrs]
        labels = e.get("labels") if isinstance(e.get("labels"), dict) else {}
        if labels:
            out["lab"] = {str(k): str(v) for k, v in labels.items()}
        if asm:
            out["asm"] = asm
            out["src"] = str(e.get("asm_source", ""))
        return out

    def region_title(self, r, with_owner=False):
        t = r["sub"] or r["label"] or ""
        if not r["sub"] and r["label"] and r["owner"] and r["label"].startswith(r["owner"] + ","):
            t = r["label"][len(r["owner"]) + 1:].strip()
        if with_owner and r["owner"] and r["owner"] != "machine" and not t.startswith(r["owner"]):
            t = r["owner"] + " · " + t
        return t

    def source_label(self, c):
        if c["src_kind"] == "reg":
            return "register " + c["src"]
        r = next((x for x in self.regions if x["id"] == c["src"]), None)
        where = c["where"]
        return (self.region_title(r, True) if r else c["src"]) + (", contents" if where == "contents" else ", " + re.sub(r"^cmpt_", "", where))

    def build(self):
        self.index()
        self.sections, top, binders = [], [], []

        def collect(stmts):
            for s in stmts or []:
                if not isinstance(s, dict):
                    top.append(s)
                elif s.get("k") == "section":
                    self.sections.append(s)
                elif s.get("k") == "exists" and any(isinstance(x, dict) and x.get("k") == "section" for x in s.get("body") or []):
                    binders.append(with_comment("∃ " + binders_text(s.get("binders")) + ",", s.get("comment", "")))
                    collect(s.get("body"))
                else:
                    top.append(s)
        collect(self.body)

        self.build_regions()
        for r in list(self.regions):
            self.build_cells(r)
        self.place_named()
        self.build_regs()
        # capabilities: their target region, then a cell or point at the cursor
        extra = {}
        for c in self.caps:
            if c["kind"] == "sealrange":
                continue
            r = self.region_by(c["b"], c["e"]) or self.region_by(c["b"])
            if r is None:
                key = (c["b"], c["e"])
                if key not in extra:
                    known = {"shadow_b": "shadow table", "revoker_addr": "revoker"}
                    nr = self.new_region(c["b"], c["e"], known.get(c["b"], f"[{c['b']}, {c['e']})"),
                                         implicit=True, owner="machine")
                    self.build_cells(nr)
                    extra[key] = nr
                r = extra[key]
            c["target"] = r["id"]
        # export entries: their PCC offsets point into the compartment's code
        for r in self.regions:
            for c in r["cells"]:
                en = c.get("entry")
                if not en:
                    continue
                pcc = next((x for x in self.regions if x["owner"] == en["owner"] and x["sub"] == "PCC range"), None)
                if pcc:
                    off = clean(str(en["off"]))
                    c["ptr"] = self.resolve({"text": f"{pcc['b']} ^+ {off}", "base": pcc["b"], "off": off}, pcc["id"])
                    p = self.els.get(c["ptr"])
                    if p is not None and "notes" in p:
                        p["notes"].append(f"export entry {en['index']}" + (" (" + re.sub(r"^export ", "", en["comment"]) + ")" if en["comment"] else ""))
        for c in self.caps:
            if not c["target"]:
                continue
            c["anchor"] = self.resolve(c["a_addr"], c["target"])
            a = self.els.get(c["anchor"]) if c["anchor"] else None
            if a is not None and "notes" in a:
                a["notes"].append(c["src"] + " cursor" if c["src_kind"] == "reg" else "cursor of " + self.source_label(c))
            r = next(x for x in self.regions if x["id"] == c["target"])
            c["bAnchor"] = self.resolve({"text": c["b"]}, c["target"])
            c["eAnchor"] = None if c["e"] == r["e"] else self.resolve({"text": c["e"]}, c["target"])
        self.attach_sections()
        for r in self.regions:
            r["badges"] = self.badges(r)
        if top:
            self.other.insert(0, dict(title="Top level", stmts=[stmt_text(s) for s in top]))

        code = {}
        for r in self.regions:
            for n in r["code_names"]:
                code[n] = self.code_out(n)
        params = binders_text(self.doc.get("params"))
        pred = str(self.doc.get("predicate", self.name + "_initial_state_ok"))
        raw = "\n".join([f"{pred} {params} :="] + binders + [stmt_text(s, "  ") for s in top] +
                        [stmt_text(s) for s in self.sections])
        for r in self.regions:
            r["cells"] = [compact(c) for c in r["cells"]]
        return dict(name=self.name, predicate=pred, binders=([params] if params else []) + binders,
                    regions=self.regions, caps=[compact(c) for c in self.caps], regs=self.regs, reg_notes=self.reg_notes,
                    owners=self.owners, other=self.other, code=code, raw=raw,
                    schema=self.doc.get("schema"))


def compact(d):
    """Drop the empty fields of a cell, point or capability (the page reads a
    missing field as empty)."""
    if isinstance(d, dict):
        return {k: compact(v) for k, v in d.items() if v is not None and v != "" and v != [] and v != {} and v is not False}
    if isinstance(d, list):
        return [compact(x) for x in d]
    return d


def build(doc, name=None):
    return Model(doc, name).build()


if __name__ == "__main__":
    import sys
    for path in sys.argv[1:]:
        with open(path, encoding="utf-8") as f:
            d = build(json.load(f))
        print(path, len(d["regions"]), "regions", len(d["caps"]), "caps", len(d["regs"]), "registers")
        els = {}
        for r in d["regions"]:
            for c in r["cells"]:
                els[c["id"]] = c
                for p in c.get("points", []):
                    els[p["id"]] = p
        where = lambda i: (lambda x: (x.get("name") or x.get("label") or i) +
                           (f" row {x['code_row']}" if "code_row" in x else "") +
                           (" (unknown)" if x.get("unknown") else ""))(els[i]) if i in els else "-"
        for r in d["regions"]:
            kinds = []
            for c in r["cells"]:
                if c.get("code"):
                    kinds.append(f"code {c['code']}[{c.get('len')}]")
                elif c.get("rep"):
                    kinds.append(f"replicate {c['rep']['n']} × {c['rep']['text']}")
                elif c.get("from"):
                    kinds.append(f"{c['from']}[{c['from_i']}]")
                elif c.get("entry"):
                    kinds.append(f"entry {c['entry']['index']} -> {where(c['ptr']) if c.get('ptr') else '-'}")
            print(f"   {r['id']:6} {r['label']:40} [{r['b']}, {r['e']})  {len(r['cells'])} cells"
                  + (" implicit" if r["implicit"] else "") + (" no content" if r["pieces"] is None else "")
                  + ("  · " + "; ".join(kinds) if kinds else ""))
        for c in d["caps"]:
            tgt = next((r for r in d["regions"] if r["id"] == c.get("target")), None)
            print(f"   {c['id']:4} {c['text'][:64]:64} -> {tgt['label'] if tgt else '-'} @ {where(c['anchor']) if c.get('anchor') else '-'}")
        print("   registers:", " ".join(g["name"] + ("*" if g.get("via") else "") for g in d["regs"]))
        for n in d["reg_notes"]:
            print("   reg note:", n["text"][:80], "· lists", n.get("listed"))
        for n, k in d["code"].items():
            print(f"   code {n}: {k['n']} words, {sum(w is None for w in k['w'])} instructions"
                  + (f", asm {len(k['asm'])} lines from {k.get('src')}" if "asm" in k else "")
                  + (f", {len(k['lab'])} labels" if "lab" in k else ""))
