#!/usr/bin/env python3
"""Mechanically relocate line anchors of the link gate after a merge (scripts/overview-links.sh).

    scripts/relink.py REV...       REV: the commits whose expectation counts as reviewed (the merge's
                                   parents: master and the merged branches)

For every line-anchored link `$BASE/<path>#L<a>-L<b>` in the gated documents (OVERVIEW.md,
README.md), the text it cited when it was reviewed is the block under `== <path>#L<a>-L<b>` in
`scripts/overview-links-expected.txt` at one of the REVs. If the file now holds exactly that text at
the anchor, nothing changes. If it holds it at exactly one other place, the anchor is rewritten to
that place (the lines moved, the text did not). Anything else -- text not found, found twice, a link
no REV reviewed -- is not mechanical: exit 1 and list those links, changing nothing. On success the
documents are rewritten and the expectation regenerated (`overview-links.sh --update`); since every
cited text is one that was reviewed, no paragraph needs re-reading. Exit 0, and print what moved.
"""
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXPECTED = "scripts/overview-links-expected.txt"
DOCS = ["OVERVIEW.md", "README.md"]


def base_url():
    m = re.search(r'^BASE="([^"]+)"', open(os.path.join(ROOT, "scripts/overview-links.sh")).read(), re.M)
    return m.group(1)


def reviewed(revs):
    """{"path#anchor": [text lines]} from the expectation at each rev (later revs do not override)."""
    out = {}
    for rev in revs:
        r = subprocess.run(["git", "-C", ROOT, "show", f"{rev}:{EXPECTED}"], capture_output=True, text=True)
        if r.returncode:
            continue
        key, body = None, []
        for line in r.stdout.split("\n") + ["== END"]:
            if line.startswith("== ") or line.startswith(">>> "):
                if key is not None and body not in out.setdefault(key, []):
                    out[key].append(body)
                key, body = (line[3:] if line.startswith("== ") else None), []
            elif key is not None and line:
                body.append(line[8:])  # "%6d  " prefix; separator lines are empty
    return out


def parse(m):
    a = int(m.group(2))
    return m.group(1), a, int(m.group(3)) if m.group(3) else a


def norm(m):
    path, a, b = parse(m)
    return f"{path}#L{a}" if a == b else f"{path}#L{a}-L{b}"


def main():
    revs = sys.argv[1:]
    if not revs:
        sys.exit(__doc__)
    base = base_url()
    link = re.compile(re.escape(base) + r'/([^)\s#>]+)#L(\d+)(?:-L(\d+))?')
    known = reviewed(revs)
    files, moves, bad, texts = {}, {}, [], {}
    for doc in DOCS:
        p = os.path.join(ROOT, doc)
        if not os.path.isfile(p):
            continue
        texts[doc] = open(p, encoding="utf-8").read()
        for m in link.finditer(texts[doc]):
            key = norm(m)
            path, a, b = parse(m)
            if key in moves:
                continue
            if key not in known:
                bad.append(f"{doc}: {key}: no reviewed expectation names this link")
                continue
            fp = os.path.join(ROOT, path)
            if not os.path.isfile(fp):
                bad.append(f"{doc}: {key}: file missing")
                continue
            if path not in files:
                ls = open(fp, encoding="utf-8").read().split("\n")
                if ls and ls[-1] == "":
                    ls.pop()
                files[path] = ls
            ls = files[path]
            cands = known[key]
            if any(ls[a - 1:b] == c for c in cands):
                continue
            hits = set()
            for c in cands:
                k = len(c)
                hits |= {i + 1 for i in range(len(ls) - k + 1) if ls[i:i + k] == c}
            if len(hits) != 1 or len({len(c) for c in cands}) != 1:
                bad.append(f"{doc}: {key}: reviewed text found {len(hits)} times in {path}")
                continue
            na = hits.pop()
            nb = na + len(cands[0]) - 1
            moves[key] = f"{path}#L{na}" if na == nb else f"{path}#L{na}-L{nb}"
    if bad:
        print("relink: not mechanical:\n  " + "\n  ".join(bad))
        sys.exit(1)
    for doc, t in texts.items():
        new = link.sub(lambda m: base + "/" + moves[norm(m)] if norm(m) in moves else m.group(0), t)
        if new != t:
            open(os.path.join(ROOT, doc), "w", encoding="utf-8").write(new)
    for k, v in moves.items():
        print(f"relink: {k} -> {v}")
    r = subprocess.run([os.path.join(ROOT, "scripts/overview-links.sh"), "--update"], cwd=ROOT,
                       capture_output=True, text=True)
    print(r.stdout.strip())
    sys.exit(r.returncode)


if __name__ == "__main__":
    main()
