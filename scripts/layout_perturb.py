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
  numeral (sums such as `CI.indSize` or `CI.axiomSize`, which follow their parts);
* or, with `--scale K`, every numeral offset `n` becomes `K * n`, except a slice's length word
  (`fooLen` next to `fooOff`), which stays right after its offset word (`K * off + 1`). A gap
  cannot perturb a record that embeds another (the constant record embeds the constant value, the
  hint and the caps record at `CI.cv`, `CI.defnHint`, `CI.indCaps`): the embedded record grows by
  the gap while the fields after it move by the gap only, so they would overlap. Scaling is
  linear, so `CI.cv + CV.size` still ends where the next field starts;
* `scripts/lake build` (with `LAKE_ARTIFACT_CACHE=false`: the perturbed modules are of no use
  to anyone; unaffected modules still come from the cache) and the modules that fail.

A clean run fails only `ConAguaX86.Checker.AsmFileEq` (the committed `x86/checker.s` is stale for the
perturbed layout, as it must be). Any other failing module names a literal to replace by its name.
Not a gate: one run is a world rebuild (about 35 minutes at `LEAN_NUM_THREADS=2` on a loaded
machine). The files are restored with `git checkout` even when the build fails or is interrupted.

Usage:
  scripts/layout_perturb.py [--gap N | --scale K] [--dry-run] [--target MOD ...] [--keep] [LAYOUT.lean ...]
    (default: every file of ConAgua/Arena/RecLayout/ except the `…Dec.lean` lemma files and
    `Attr.lean`; `--dry-run` prints the changes and builds nothing; `--target` builds only these
    modules and what they import, not the whole library; `--keep` leaves the perturbed layout files
    in place, for `lake env lean` on a failing file against the perturbed build; restore them with
    `git checkout` before committing)
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


def perturb(path, gap, scale):
    """The file's text with every nonzero numeral offset shifted by `gap` (or scaled by `scale`,
    a slice's length word kept right after its offset word), and the changes."""
    with open(path, encoding="utf-8") as fh:
        lines = fh.readlines()
    vals = {}
    for line in lines:
        m = DEF.match(line.rstrip("\n"))
        if m:
            vals[m.group(2)] = int(m.group(3))
    out, changes = [], []
    for line in lines:
        m = DEF.match(line.rstrip("\n"))
        if m and int(m.group(3)) > 0:
            name, old = m.group(2), int(m.group(3))
            off = name[:-3] + "Off" if name.endswith("Len") else None
            if not scale:
                new = old + gap
            elif off in vals and vals[off] + 1 == old:
                new = scale * vals[off] + 1
            else:
                new = scale * old
            changes.append((name, old, new))
            line = f"{m.group(1)}{new}{m.group(4)}\n"
        out.append(line)
    return "".join(out), changes


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="*")
    ap.add_argument("--gap", type=int, default=3)
    ap.add_argument("--scale", type=int, default=0)
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--target", action="append", default=[])
    ap.add_argument("--keep", action="store_true")
    a = ap.parse_args()
    files = [os.path.abspath(f) for f in a.files] or layout_files()
    rel = [os.path.relpath(f, ROOT) for f in files]
    dirty = subprocess.run(["git", "status", "--porcelain", "--", *rel], cwd=ROOT,
                           capture_output=True, text=True).stdout.strip()
    if dirty:
        sys.exit(f"layout_perturb: uncommitted changes in the layout files:\n{dirty}")
    texts = {}
    for f, r in zip(files, rel):
        text, changes = perturb(f, a.gap, a.scale)
        texts[f] = text
        for name, old, new in changes:
            print(f"{r}: {name} {old} -> {new}")
    if a.dry_run:
        return 0
    try:
        for f, text in texts.items():
            with open(f, "w", encoding="utf-8") as fh:
                fh.write(text)
        env = dict(os.environ, LAKE_ARTIFACT_CACHE="false")
        res = subprocess.run([os.path.join(ROOT, "scripts", "lake"), "-d", "x86", "build", *a.target], cwd=ROOT,
                             capture_output=True, text=True, env=env)
        with open(os.path.join(ROOT, ".lake", "layout_perturb.log"), "w", encoding="utf-8") as fh:
            fh.write(res.stdout + res.stderr)
        log = res.stdout + res.stderr
    finally:
        if not a.keep:
            subprocess.run(["git", "checkout", "--", *rel], cwd=ROOT, check=True)
    failed = sorted(set(re.findall(r"✖ \[\d+/\d+\] Building (\S+)", log)))
    errors = [l for l in log.splitlines() if l.startswith(("error: ConAgua/", "error: ConAguaX86/"))]
    print(f"failed modules: {len(failed)}")
    for m in failed:
        print(f"  {m}")
    for e in errors[:40]:
        print(e)
    unexpected = [m for m in failed if m != "ConAguaX86.Checker.AsmFileEq"]
    print("clean: only the stale x86/checker.s" if not unexpected else
          f"{len(unexpected)} module(s) still depend on an offset's number")
    print("kept the perturbed layout files (git checkout them before committing)" if a.keep else
          "restored the layout files; rebuild (`scripts/lake build`, cache hits) before other work")
    return 1 if unexpected else 0


if __name__ == "__main__":
    sys.exit(main())
