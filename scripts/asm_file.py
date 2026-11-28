#!/usr/bin/env python3
"""Regenerate the two committed generated files the binary is built from (`make`, `Makefile`):

* `x86/checker.s`: the entry stub, the trampoline and the compiled checker, printed by
  `x86/ConAguaX86/Checker/AsmEmit.lean` (run as a script, so the compiler runs as compiled Lean code;
  nothing here is trusted: the final theorems are about the file as the trusted parser reads it
  (`x86/ConAguaAsm/Checker.lean`), and the kernel checks that it is the compiler's output,
  `checkerFile_eq` in `x86/ConAguaX86/Checker/AsmFileEq.lean`). Regenerate after every change to the
  checker's L code (`ConAgua/Checker/Prog.lean`), the compiler or the stub.
* `commons/pins.bin`: the pin data `commons/main.c` embeds, written by `romgen commons/pins.bin 4`
  (`ConAgua/Rom/Gen.lean`): the checker's startup data and all of con-leche's `natOpPinSets` (4
  variants, the set con-ron embeds). Not trusted either: the theorems hold for every pin buffer.
  Regenerate after a change to the startup data or a twin bump.

Both modes also run the parser cross-check `x86/ConAguaX86/AsmFile/CrossCheck.lean` on `x86/checker.s`:
Kraken's own parser must read the code as the trusted parser does (~13 s; not in `include_asm`,
where it would double the module's elaboration time).

Usage: scripts/asm_file.py [--check] [--no-build]
  --check     fail (exit 1) if a file would change; do not write it
  --no-build  do not build ConAguaX86.Checker.AsmEmit's imports and romgen first"""
# Order after changing L code: scripts/checker_prog.py (writes Checker/Prog*.lean), then
# `scripts/lake build && scripts/lake -d x86 build` (or just this script, which builds the `ProgI` chain itself), then this
# script. `--no-build` on out-of-date oleans is refused (check_oleans_fresh).
import argparse, os, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LAKE = os.path.join(ROOT, "scripts", "lake")
PIN_VARIANTS = "4"


def cross_check():
    r = subprocess.run([LAKE, "-d", "x86", "env", "lean", "--run", "x86/ConAguaX86/AsmFile/CrossCheck.lean",
                        os.path.join(ROOT, "x86", "checker.s")],
                       cwd=ROOT, capture_output=True, text=True, timeout=1800)
    if r.returncode != 0:
        sys.exit(f"asm_file.py: parser cross-check failed:\n{r.stdout[-3000:]}\n{r.stderr[-3000:]}")
    print(r.stdout.strip())


def check_oleans_fresh():
    """Refuse to run `AsmEmit` on stale oleans (`--no-build`): after `checker_prog.py` rewrote
    `Checker/Prog*.lean`, `lean --run` silently reads the OLD `ProgI` olean, and the resulting
    `x86/checker.s` fails `checkerFile_eq` (and its binary the prelude). `lake build --no-build` fails
    iff a target would need rebuilding (mtimes are useless: cache-restored oleans look old)."""
    for cmd in (
        [LAKE, "build", "--no-build", "ConAgua.Checker.ProgTab", "ConAgua.Checker.ProgI", "romgen"],
        [LAKE, "-d", "x86", "build", "--no-build", "ConAguaX86.Checker.AsmX",
         "ConAguaX86.Compiler.Run", "ConAguaX86.Compiler.Abi"],
    ):
        r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit("asm_file.py: --no-build, but AsmEmit's imports are out of date with their sources "
                     "(did checker_prog.py just rewrite Checker/Prog*.lean?); run `scripts/lake build "
                     "ConAgua.Checker.ProgI && scripts/lake -d x86 build` first, or omit --no-build:\n"
                     + r.stdout[-1500:] + r.stderr[-1500:])


def generate(name, cmd):
    """Run `cmd(tmp)` and return what it wrote to the file `tmp`, and its output."""
    fd, out = tempfile.mkstemp(suffix="-" + name, dir=os.path.join(ROOT, "_tmp"))
    os.close(fd)
    try:
        r = subprocess.run(cmd(out), cwd=ROOT, capture_output=True, text=True, timeout=1800)
        if r.returncode != 0:
            sys.exit(f"asm_file.py: generating {name} failed:\n{r.stdout[-3000:]}\n{r.stderr[-3000:]}")
        return open(out, "rb").read(), r.stdout.strip()
    finally:
        os.unlink(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--no-build", action="store_true")
    a = ap.parse_args()
    if not a.no_build:
        for cmd in (
            [LAKE, "build", "ConAgua.Checker.Prog", "ConAgua.Checker.ProgTab",
             "ConAgua.Checker.ProgI", "romgen"],
            [LAKE, "-d", "x86", "build", "ConAguaX86.Checker.AsmX", "ConAguaX86.Compiler.Run",
             "ConAguaX86.Compiler.Abi", "ConAguaX86.Compiler.AbiCmp", "ConAguaX86.AsmFile.CrossCheck"],
        ):
            r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
            if r.returncode != 0:
                sys.exit(f"asm_file.py: build failed:\n{r.stdout[-3000:]}\n{r.stderr[-3000:]}")
    else:
        check_oleans_fresh()
    os.makedirs(os.path.join(ROOT, "_tmp"), exist_ok=True)
    stale = []
    for rel, cmd in [("x86/checker.s", lambda o: [LAKE, "-d", "x86", "env", "lean", "--run", "x86/ConAguaX86/Checker/AsmEmit.lean", o]),
                     ("commons/pins.bin", lambda o: [LAKE, "exe", "romgen", o, PIN_VARIANTS])]:
        new, msg = generate(os.path.basename(rel), cmd)
        path = os.path.join(ROOT, rel)
        old = open(path, "rb").read() if os.path.exists(path) else None
        if old == new:
            print(f"{rel} is up to date")
        elif a.check:
            stale.append(rel)
        else:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path + ".tmp", "wb") as fh:
                fh.write(new)
            os.replace(path + ".tmp", path)
            print(f"wrote {rel} ({msg})")
    if stale:
        sys.exit(f"asm_file.py --check: {', '.join(stale)} stale; run scripts/asm_file.py and commit")
    cross_check()


if __name__ == "__main__":
    main()
