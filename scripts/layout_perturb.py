#!/usr/bin/env python3
"""Perturb the record layouts and build: find the literal offsets the names still hide.

The record layouts (`ConAgua/Arena/RecLayout/*.lean`) name every field offset as a
`@[reducible] def f : Word := n`. Because the names are reducible, a proof or model that still
says the number (`q + 12` where L says `q + ⟪Caps.nparams⟫`) keeps checking; only a changed value
finds it. This script changes the values without changing the layout's shape, builds, and
restores the files:

* every offset `n > 0` becomes `n + GAP` (a gap of `GAP` unused words after the offset-0 word),
  so the fields keep their order and a slice's length word still follows its offset word;
  offset-0 fields stay (L reads them as `A⦃q⦄`, by design) and so do definitions that are not a
  numeral (sums such as `CI.indSize`) and stored values (`…Val`, such as `ProjTbl.kindVal`);
* `scripts/lake build` (the shared cache makes the restore cheap) and the modules that fail.

A clean run fails only `ConAgua.Checker.AsmFileEq` (the committed `checker.s` is stale for the
perturbed layout, as it must be). Any other failing module names a literal to replace by its name.
Not a gate: one run is a world rebuild (about 35 minutes at `LEAN_NUM_THREADS=2` on a loaded
machine). The files are restored with `git checkout` even when the build fails or is interrupted.

Usage:
  scripts/layout_perturb.py [--gap N] [--dry-run] [LAYOUT.lean ...]
    (default: every file of ConAgua/Arena/RecLayout/ except the `…Dec.lean` lemma files and
    `Attr.lean`; `--dry-run` prints the changes and builds nothing)
"""
import argparse
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LAYOUT_DIR = os.path.join(ROOT, "ConAgua", "Arena", "RecLayout")
DEF = re.compile(r"^(@\[reducible\] def (\w+) : Word := )(\d+)(\s*)$")


def layout_files():
    return sorted(os.path.join(LAYOUT_DIR, f) for f in os.listdir(LAYOUT_DIR)
                  if f.endswith(".lean") and not f.endswith("Dec.lean") and f != "Attr.lean")


def perturb(path, gap):
    """The file's text with every nonzero numeral offset shifted by `gap`, and the changes."""
    out, changes = [], []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            m = DEF.match(line.rstrip("\n"))
            if m and int(m.group(3)) > 0 and not m.group(2).endswith("Val"):
                new = int(m.group(3)) + gap
                changes.append((m.group(2), int(m.group(3)), new))
                line = f"{m.group(1)}{new}{m.group(4)}\n"
            out.append(line)
    return "".join(out), changes


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="*")
    ap.add_argument("--gap", type=int, default=3)
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    files = [os.path.abspath(f) for f in a.files] or layout_files()
    rel = [os.path.relpath(f, ROOT) for f in files]
    dirty = subprocess.run(["git", "status", "--porcelain", "--", *rel], cwd=ROOT,
                           capture_output=True, text=True).stdout.strip()
    if dirty:
        sys.exit(f"layout_perturb: uncommitted changes in the layout files:\n{dirty}")
    texts = {}
    for f, r in zip(files, rel):
        text, changes = perturb(f, a.gap)
        texts[f] = text
        for name, old, new in changes:
            print(f"{r}: {name} {old} -> {new}")
    if a.dry_run:
        return 0
    try:
        for f, text in texts.items():
            with open(f, "w", encoding="utf-8") as fh:
                fh.write(text)
        res = subprocess.run([os.path.join(ROOT, "scripts", "lake"), "build"], cwd=ROOT,
                             capture_output=True, text=True)
        log = res.stdout + res.stderr
    finally:
        subprocess.run(["git", "checkout", "--", *rel], cwd=ROOT, check=True)
    failed = sorted(set(re.findall(r"✖ \[\d+/\d+\] Building (\S+)", log)))
    errors = [l for l in log.splitlines() if l.startswith("error: ConAgua/")]
    print(f"failed modules: {len(failed)}")
    for m in failed:
        print(f"  {m}")
    for e in errors[:40]:
        print(e)
    unexpected = [m for m in failed if m != "ConAgua.Checker.AsmFileEq"]
    print("clean: only the stale checker.s" if not unexpected else
          f"{len(unexpected)} module(s) still depend on an offset's number")
    print("restored the layout files; rebuild (`scripts/lake build`, cache hits) before other work")
    return 1 if unexpected else 0


if __name__ == "__main__":
    sys.exit(main())
