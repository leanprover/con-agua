#!/usr/bin/env python3
"""Large decimal literal exports, for benchmarking `nat_dec` (docs/design/bigdec.md).

For each digit count N, writes `BigLit<N>.lean`:

    def bigLit : Nat := <N random digits>
    theorem bigLit_eq : bigLit = <the same digits> := rfl

compiles it with `lean` (toolchain v4.35.0-rc3, the one lean4export is built with), and exports
the two declarations with lean4export into `BigLit<N>.ndjson` (one `natVal` record). The checker,
con-ron and con-leche accept them. A Lean file of 10^6 digits takes about 8 minutes to elaborate.

`--resize M...` writes `sw<M>.ndjson` from an existing export by replacing the literal's digits
(no Lean needed; the same declarations, any length).

Usage: scripts/biglit_fixtures.py OUTDIR --lean4export PATH [--digits N ...] [--resize M ...]
"""
import argparse
import os
import random
import re
import subprocess


def digits(n):
    r = random.Random(n)
    return str(r.randint(1, 9)) + "".join(str(r.randint(0, 9)) for _ in range(n - 1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("outdir")
    ap.add_argument("--lean4export", required=True, help="path of the lean4export binary")
    ap.add_argument("--toolchain", default="leanprover/lean4:v4.35.0-rc3")
    ap.add_argument("--digits", type=int, nargs="*", default=[10 ** 4, 10 ** 5, 10 ** 6])
    ap.add_argument("--resize", type=int, nargs="*", default=[])
    a = ap.parse_args()
    out = os.path.abspath(a.outdir)
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "lean-toolchain"), "w") as f:
        f.write(a.toolchain + "\n")
    libdir = subprocess.run(["lean", "--print-libdir"], cwd=out, check=True, capture_output=True,
                            text=True).stdout.strip()
    env = dict(os.environ, LEAN_PATH=libdir + ":" + out)
    for n in a.digits:
        name = f"BigLit{n}"
        s = digits(n)
        with open(os.path.join(out, name + ".lean"), "w") as f:
            f.write(f"def bigLit : Nat := {s}\n\ntheorem bigLit_eq : bigLit = {s} := rfl\n")
        subprocess.run(["lean", "-o", name + ".olean", name + ".lean"], cwd=out, check=True)
        with open(os.path.join(out, name + ".ndjson"), "w") as f:
            subprocess.run([a.lean4export, name, "--", "bigLit", "bigLit_eq"], cwd=out, env=env,
                           check=True, stdout=f)
    if a.resize:
        base = os.path.join(out, f"BigLit{a.digits[0]}.ndjson")
        with open(base) as f:
            text = f.read()
        for m in a.resize:
            with open(os.path.join(out, f"sw{m}.ndjson"), "w") as f:
                f.write(re.sub(r'"natVal":"[0-9]+"', '"natVal":"' + digits(m) + '"', text))


if __name__ == "__main__":
    main()
