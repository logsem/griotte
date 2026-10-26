"""Write one self-contained HTML page viewing Griotte initial-state predicates.

    python3 -I viewer.py OUT.html a.json [b.json ...]

Each file is a JSON print (schema 1, docs/predicate-viewer/schema.md), turned
into the viewer's model by model.build; all case studies are embedded as JSON
(code constants once) and the page draws the selected one. Vanilla JS, no external scripts."""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True
sys.path.insert(0, HERE)

from model import build  # noqa: E402

TEMPLATE_PATH = os.path.join(HERE, "viewer_template.html")


def build_page(out, paths):
    cases = []
    for p in paths:
        try:
            with open(p, encoding="utf-8") as f:
                doc = json.load(f)
        except (OSError, ValueError) as e:
            print(f"skipping {p}: {e}", file=sys.stderr)
            continue
        if doc.get("schema") not in (1, None):
            print(f"warning: {p}: schema {doc.get('schema')!r}, expected 1", file=sys.stderr)
        d = build(doc)
        d["file"] = "/".join(os.path.abspath(p).split(os.sep)[-4:])
        cases.append(d)
    if not cases:
        sys.exit("no readable JSON print")
    names = [d["name"] for d in cases]
    for d in cases:  # two files of the same case study: keep both selectable
        if names.count(d["name"]) > 1:
            d["name"] = d["name"] + " (" + os.path.basename(d["file"]) + ")"
    # vae first: the page opens on it.
    cases.sort(key=lambda d: (d["name"] != "vae", d["name"]))
    # Code constants are shared by the case studies (the switcher's 290 words
    # in each): store each distinct one once, cases name it by key.
    code, keys = {}, {}
    for d in cases:
        for n, k in list(d["code"].items()):
            body = json.dumps(k, sort_keys=True)
            if body not in keys:
                key = n if n not in code else f"{n}#{sum(x.split('#')[0] == n for x in code)}"
                keys[body] = key
                code[key] = k
            d["code"][n] = keys[body]
    data = json.dumps({"cases": cases, "code": code}, ensure_ascii=False, separators=(",", ":"))
    data = data.replace("</", "<\\/").replace("<!--", "<\\u0021--")
    with open(TEMPLATE_PATH, encoding="utf-8") as f:
        page = f.read()
    page = page.replace("/*__DATA__*/", data)
    with open(out, "w", encoding="utf-8") as f:
        f.write(page)
    print(f"wrote {out}: {len(cases)} case studies, {len(page)} bytes")


if __name__ == "__main__":
    if len(sys.argv) < 3:
        sys.exit("usage: python3 -I viewer.py OUT.html a.json [b.json ...]")
    build_page(sys.argv[1], sys.argv[2:])
