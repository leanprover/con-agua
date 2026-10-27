#!/usr/bin/env python3
"""Path-selected gates: which steps of `scripts/gates.sh` a change can affect.

One table, used by lanes (`scripts/gates.sh --changed`, in their worktree before submitting) and by
the merge queue (`scripts/mq-next.sh`, on the merge of queued branches onto master), so both run
the same steps for the same change. Master is green, so only what the delta can break is checked.

    scripts/gate_select.py [--base REV] [--head REV]   paths changed between BASE (default: the
                                                       merge-base of HEAD and master) and HEAD
                                                       (default: the working tree, uncommitted
                                                       changes included)
    scripts/gate_select.py --paths FILE|-              the changed paths, one per line
    --why                                              also print, per step, the first path that selected it

Prints the selected steps, comma-separated, in gate order (`--why`: one `step  reason` line each).

The table (first match per path; "cheap" = links, vendor, modules, provenance, reasons, always run):

  path                                                        steps
  lakefile.toml, lake-manifest.json, lean-toolchain,          ALL (a toolchain, dependency, twin or
    vendor/**, scripts/lake, scripts/gates.sh,                gate change: everything)
    scripts/gate_select.py
  *.md (anywhere), docs/**, LICENSE, .gitignore,              cheap
    .gitattributes, .github/**
  checker.s, pins.bin                                         build, e2e (checker.s is an input file
                                                              of ConAguaAsm; both go into ./checker)
  main.c, Makefile, reasons.h, scripts/{diff-e2e,e2e}.py      e2e
  scripts/{core,loop,leaf}_fns.{py,lean}, preloop_ws.py       build + that closure check
  scripts/shake{.py,-setup.sh,-allowlist.txt,-keep.txt}       build, shake
  ConAgua.lean, ConAgua/**.lean, ConAguaAsm/**                build, shake; + the four closure checks if
                                                              the module is in the import closure of
                                                              ConAgua.Checker.Prog or of a closure's
                                                              generated file (CoreErec, LoopFns,
                                                              LeafFns, PreLoopWS, PreLoopWSStages)
  other scripts/** (not run by a gate)                        cheap
  anything else                                               ALL (when unsure, everything)

The closure checks (`core_fns.py`, `loop_fns.py`, `leaf_fns.py`, `preloop_ws.py --check`) run
`lake env lean` against ConAgua.Checker.Prog, so they imply `build`. `e2e` is `make checker` and
`scripts/diff-e2e.py`: the binary is exactly main.c + checker.s + pins.bin (a change to L code, the
compiler or the stubs that changes the program changes checker.s, or the build's `checkerFile_eq`
fails), so these files (and reasons.h, the abort messages) decide whether the verdicts can change.
"""
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CHEAP = ["links", "vendor", "modules", "provenance", "reasons"]
CLOSURES = ["core-fns", "loop-fns", "leaf-fns", "preloop-ws"]
ORDER = CHEAP + ["build", "shake"] + CLOSURES + ["e2e"]

ALL_EXACT = {"lakefile.toml", "lake-manifest.json", "lean-toolchain", "scripts/lake",
             "scripts/gates.sh", "scripts/gate_select.py"}
CHEAP_EXACT = {"LICENSE", ".gitignore", ".gitattributes"}
E2E_EXACT = {"main.c", "Makefile", "reasons.h", "scripts/diff-e2e.py", "scripts/e2e.py"}
CLOSURE_SCRIPTS = {
    "scripts/core_fns.py": "core-fns", "scripts/core_fns.lean": "core-fns",
    "scripts/loop_fns.py": "loop-fns", "scripts/loop_fns.lean": "loop-fns",
    "scripts/leaf_fns.py": "leaf-fns", "scripts/leaf_fns.lean": "leaf-fns",
    "scripts/preloop_ws.py": "preloop-ws",
}
SHAKE_FILES = {"scripts/shake.py", "scripts/shake-setup.sh", "scripts/shake-allowlist.txt",
               "scripts/shake-keep.txt"}
# the closure checks read checkerProg (ConAgua.Checker.Prog) and rewrite these files
CLOSURE_ROOTS = ["ConAgua.Checker.Prog", "ConAgua.Arena.CoreErec", "ConAgua.Arena.LoopFns",
                 "ConAgua.Arena.LeafFns", "ConAgua.Checker.PreLoopWS", "ConAgua.Checker.PreLoopWSStages"]
IMP = re.compile(r"^(?:public |private )?(?:meta )?import (?:all )?(ConAgua[\w.]*)", re.M)


def module_of(path):
    return path[:-len(".lean")].replace("/", ".") if path.endswith(".lean") else None


_closure = {}


def closure_modules(root):
    """The ConAgua modules the closure checks' inputs import, transitively (from the files in `root`)."""
    if root not in _closure:
        seen, stack = set(), list(CLOSURE_ROOTS)
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            p = os.path.join(root, m.replace(".", "/") + ".lean")
            if not os.path.isfile(p):
                continue
            seen.add(m)
            stack += IMP.findall(open(p, encoding="utf-8", errors="replace").read())
        _closure[root] = seen
    return _closure[root]


def classify(path, root):
    """The steps (beyond the cheap ones) a change to `path` selects; {"ALL"} for everything."""
    top = path.split("/")[0]
    if path in ALL_EXACT or top == "vendor":
        return {"ALL"}
    if path.endswith(".md") or path in CHEAP_EXACT or top in ("docs", ".github"):
        return set()
    if path in ("checker.s", "pins.bin"):
        return {"build", "e2e"}
    if path in E2E_EXACT:
        return {"e2e"}
    if path in CLOSURE_SCRIPTS:
        return {"build", CLOSURE_SCRIPTS[path]}
    if path in SHAKE_FILES:
        return {"build", "shake"}
    if path == "ConAgua.lean" or (top == "ConAgua" and path.endswith(".lean")) or top == "ConAguaAsm":
        m = module_of(path)
        if m and m in closure_modules(root):
            return {"build", "shake", *CLOSURES}
        return {"build", "shake"}
    if top == "scripts":
        return set()
    return {"ALL"}


def select(paths, root=ROOT):
    """[(step, reason)] in gate order."""
    why = {s: "always" for s in CHEAP}
    for p in paths:
        for s in sorted(classify(p, root)):
            if s == "ALL":
                for t in ORDER:
                    why.setdefault(t, p)
            else:
                why.setdefault(s, p)
    return [(s, why[s]) for s in ORDER if s in why]


def changed_paths(base=None, head=None, cwd=ROOT):
    def git(*a):
        return subprocess.run(["git", "-C", cwd, *a], check=True, capture_output=True, text=True).stdout
    if base is None:
        base = git("merge-base", head or "HEAD", "master").strip()
    out = git("diff", "--name-only", base, *([head] if head else []))
    return [l for l in out.splitlines() if l]


def main():
    args = sys.argv[1:]
    why = "--why" in args
    args = [a for a in args if a != "--why"]
    opts = dict(zip(args[::2], args[1::2]))
    if "--paths" in opts:
        f = sys.stdin if opts["--paths"] == "-" else open(opts["--paths"])
        paths = [l.strip() for l in f if l.strip()]
    else:
        paths = changed_paths(opts.get("--base"), opts.get("--head"))
    sel = select(paths)
    if why:
        for s, r in sel:
            print(f"{s:12s} {r}")
    else:
        print(",".join(s for s, _ in sel))


if __name__ == "__main__":
    main()
