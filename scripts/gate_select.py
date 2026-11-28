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
    x86/{lakefile.toml,lake-manifest.json,lean-toolchain},    gate change: everything)
    vendor/**, scripts/lake, scripts/gates.sh,
    scripts/gate_select.py
  *.md (anywhere), docs/**, LICENSE, .gitignore,              cheap
    .gitattributes, .github/**
  x86/checker.s, commons/pins.bin                             build, e2e (x86/checker.s is an input file
                                                              of ConAguaAsm; both go into x86/checker);
                                                              x86/checker.s also check-asm
  scripts/check-asm.sh, scripts/check_asm.py                  check-asm (which builds what it needs)
  commons/main.c, Makefile, x86/Makefile,                     e2e
    commons/reasons.h, scripts/diff-e2e.py
  scripts/{core,loop,leaf,phaseb}_fns.{py,lean}, preloop_ws.py  build + that closure check
  scripts/shake{.py,-setup.sh,-allowlist.txt,-keep.txt}       build, shake
  scripts/checker_prog.py; ConAgua/E2E/Dump.lean,             build, checker-prog (`checker_prog.py
    ConAgua/Checker/{Sources,Entry,Prelude}.lean,             --no-build --check`: the generator still
    ConAgua/Checker/{Prog*.lean};                             runs and writes the committed text);
    x86/ConAguaX86/Checker/{ProgSkt*,Asm*}.lean;              .lean files also shake + the closures,
    scripts/e2e.py                                            e2e.py also e2e
  ConAgua.lean, ConAgua/**.lean, x86/ConAguaX86.lean,         build, shake; + check-asm for the trusted
    x86/ConAguaX86/**.lean, x86/ConAguaAsm/**.lean            parser (x86/ConAguaX86/AsmFile/**), the text
                                                              emitter (x86/ConAguaX86/Compiler/{Run,Abi}) and
                                                              check-asm.sh's drivers (EmitScan,
                                                              EmitStore, WalkEmit); + the five closure checks if
                                                              the module is in the import closure of
                                                              ConAgua.Checker.Prog or of a closure's
                                                              generated file (CoreErec, LoopFns,
                                                              LeafFns, PhaseBReads, PreLoopWS,
                                                              PreLoopWSStages)
  other scripts/** (not run by a gate)                        cheap
  anything else                                               ALL (when unsure, everything)

The closure checks (`core_fns.py`, `loop_fns.py`, `leaf_fns.py`, `phaseb_fns.py`, `preloop_ws.py --check`) run
`lake env lean` against ConAgua.Checker.Prog, so they imply `build`. `e2e` is `make checker` and
`scripts/diff-e2e.py`: the binary is exactly commons/main.c + x86/checker.s + commons/pins.bin (a change to L code, the
compiler or the stubs that changes the program changes x86/checker.s, or the build's `checkerFile_eq`
fails), so these files (and commons/reasons.h, the abort messages) decide whether the verdicts can change.
`check-asm` is `scripts/check-asm.sh`: `as` + `objdump` encode every instruction of x86/checker.s (and of
the three small emitted programs) the way Kraken's semantics reads its text (a trusted-base check);
about 10 s once built. Kraken's printer itself is a dependency (lake-manifest.json: ALL).

`warnings` (scripts/lean_warnings.py: the Lean warnings of the .lean files changed since the base, from
the build's traces and the log store beside the cache) goes with every selection of `build`.
"""
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CHEAP = ["links", "vendor", "modules", "provenance", "reasons"]
CLOSURES = ["core-fns", "loop-fns", "leaf-fns", "phaseb-fns", "preloop-ws"]
ORDER = CHEAP + ["build", "warnings", "check-asm", "shake"] + CLOSURES + ["checker-prog", "e2e"]

ALL_EXACT = {"lakefile.toml", "lake-manifest.json", "lean-toolchain",
             "x86/lakefile.toml", "x86/lake-manifest.json", "x86/lean-toolchain",
             "scripts/lake", "scripts/gates.sh", "scripts/gate_select.py"}
CHEAP_EXACT = {"LICENSE", ".gitignore", ".gitattributes"}
E2E_EXACT = {"commons/main.c", "Makefile", "x86/Makefile", "commons/reasons.h", "scripts/diff-e2e.py", "scripts/e2e.py"}
CLOSURE_SCRIPTS = {
    "scripts/core_fns.py": "core-fns", "scripts/core_fns.lean": "core-fns",
    "scripts/loop_fns.py": "loop-fns", "scripts/loop_fns.lean": "loop-fns",
    "scripts/leaf_fns.py": "leaf-fns", "scripts/leaf_fns.lean": "leaf-fns",
    "scripts/phaseb_fns.py": "phaseb-fns", "scripts/phaseb_fns.lean": "phaseb-fns",
    "scripts/preloop_ws.py": "preloop-ws",
}
# `scripts/checker_prog.py --no-build --check`: the generator, its inputs' readers and its outputs
PROG_GEN = re.compile(r"^(scripts/checker_prog\.py|ConAgua/E2E/Dump\.lean|"
                      r"ConAgua/Checker/(Sources|Entry|Prelude|Prog|ProgTab|ProgNrt|ProgWf)\.lean|"
                      r"x86/ConAguaX86/Checker/(ProgSkt|ProgSktPart\d+|Asm|AsmPart\d+)\.lean)$")
CHECK_ASM_FILES = {"scripts/check-asm.sh", "scripts/check_asm.py"}
# the trusted parser, the text emitter and check-asm.sh's emitter drivers
CHECK_ASM_LEAN = re.compile(r"^x86/ConAguaX86/(AsmFile/.*|Compiler/(Run|Abi|EmitScan)|Arena/(EmitStore|WalkEmit))\.lean$")
SHAKE_FILES = {"scripts/shake.py", "scripts/shake-setup.sh", "scripts/shake-allowlist.txt",
               "scripts/shake-keep.txt"}
# the closure checks read checkerProg (ConAgua.Checker.Prog) and rewrite these files
CLOSURE_ROOTS = ["ConAgua.Checker.Prog", "ConAgua.Arena.CoreErec", "ConAgua.Arena.LoopFns",
                 "ConAgua.Arena.LeafFns", "ConAgua.Checker.PhaseBReads", "ConAgua.Checker.PreLoopWS",
                 "ConAgua.Checker.PreLoopWSStages"]
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
    if path == "x86/checker.s":
        return {"build", "check-asm", "e2e"}
    if path == "commons/pins.bin":
        return {"build", "e2e"}
    if path in CHECK_ASM_FILES:
        return {"check-asm"}
    if path == "scripts/e2e.py":
        return {"build", "checker-prog", "e2e"}  # `dump_sets`, the generator's dump
    if path in E2E_EXACT:
        return {"e2e"}
    if PROG_GEN.match(path):
        return {"build", "shake", "checker-prog", *CLOSURES} if path.endswith(".lean") else {"build", "checker-prog"}
    if path in CLOSURE_SCRIPTS:
        return {"build", CLOSURE_SCRIPTS[path]}
    if path in SHAKE_FILES:
        return {"build", "shake"}
    if (path in ("ConAgua.lean", "x86/ConAguaX86.lean") or (top == "ConAgua" and path.endswith(".lean"))
            or (path.startswith(("x86/ConAguaX86/", "x86/ConAguaAsm/")) and path.endswith(".lean"))):
        m = module_of(path[len("x86/"):] if path.startswith("x86/") else path)
        steps = {"build", "shake"} | ({"check-asm"} if CHECK_ASM_LEAN.match(path) else set())
        if m and m in closure_modules(root):
            return steps | set(CLOSURES)
        return steps
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
    if "build" in why:
        why.setdefault("warnings", why["build"])
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
