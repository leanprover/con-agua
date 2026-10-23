#!/usr/bin/env python3
"""Regenerate the committed assembler file `asm/checker.s` (lane asmfile): the entry stub, the
trampoline and the compiled checker, printed by `ConAgua/Checker/AsmEmit.lean` (run as a script, so
the compiler runs as compiled Lean code; nothing here is trusted: the final theorems are about the
file as the trusted parser reads it (`ConAguaAsm/Checker.lean`), and the kernel checks that it is the
compiler's output, `checkerFile_eq` in `ConAgua/Checker/AsmFileEq.lean`). Regenerate after every
change to the checker's L code (`ConAgua/Checker/Prog.lean`), the compiler or the stub.

Both modes also run the parser cross-check `ConAgua/AsmFile/CrossCheck.lean` on the file: Kraken's own
parser must read the code as the trusted parser does (~13 s; not in `include_asm`, where it would
double the module's elaboration time).

Usage: scripts/asm_file.py [--check] [--no-build]
  --check     fail (exit 1) if the file would change; do not write it (land.sh runs this)
  --no-build  do not build ConAgua.Checker.AsmEmit's imports first"""
import argparse, os, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FILE = os.path.join(ROOT, "asm", "checker.s")
LAKE = os.path.join(ROOT, "scripts", "lake")


def cross_check():
    r = subprocess.run([LAKE, "env", "lean", "--run", "ConAgua/AsmFile/CrossCheck.lean", FILE],
                       cwd=ROOT, capture_output=True, text=True, timeout=1800)
    if r.returncode != 0:
        sys.exit(f"asm_file.py: parser cross-check failed:\n{r.stdout[-3000:]}\n{r.stderr[-3000:]}")
    print(r.stdout.strip())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--no-build", action="store_true")
    a = ap.parse_args()
    if not a.no_build:
        r = subprocess.run([LAKE, "build", "ConAgua.Checker.Prog", "ConAgua.Compiler.Run",
                            "ConAgua.Compiler.Abi", "ConAgua.AsmFile.CrossCheck"], cwd=ROOT, capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit(f"asm_file.py: build failed:\n{r.stdout[-3000:]}\n{r.stderr[-3000:]}")
    tmpdir = os.path.join(ROOT, "_tmp")
    os.makedirs(tmpdir, exist_ok=True)
    fd, out = tempfile.mkstemp(suffix=".s", dir=tmpdir)
    os.close(fd)
    try:
        r = subprocess.run([LAKE, "env", "lean", "--run", "ConAgua/Checker/AsmEmit.lean", out],
                           cwd=ROOT, capture_output=True, text=True, timeout=1800)
        if r.returncode != 0:
            sys.exit(f"asm_file.py: AsmEmit failed:\n{r.stdout[-3000:]}\n{r.stderr[-3000:]}")
        new = open(out, "rb").read()
    finally:
        os.unlink(out)
    old = open(FILE, "rb").read() if os.path.exists(FILE) else None
    if a.check:
        if old != new:
            sys.exit("asm_file.py --check: asm/checker.s is stale; run scripts/asm_file.py and commit it")
        print("asm_file.py --check: asm/checker.s is up to date")
        cross_check()
        return
    if old == new:
        print("asm/checker.s unchanged")
        cross_check()
        return
    os.makedirs(os.path.dirname(FILE), exist_ok=True)
    with open(FILE + ".tmp", "wb") as fh:
        fh.write(new)
    os.replace(FILE + ".tmp", FILE)
    print(f"wrote asm/checker.s ({r.stdout.strip()})")
    cross_check()


if __name__ == "__main__":
    main()
