#!/usr/bin/env python3
"""Count the places outside the store library that know the store record layout (lane tieracc,
docs/design/tieracc.md).

The store records and their columns are reached through the accessors of
`ConAgua/L/TRec.lean` and `ConAgua/Arena/StoreFields.lean` (`R⟨t⟩[i].f`, `R⟦h⟧.f`, `R⟨t⟩.count`
in L; `tfld`, `tcnt`, `tierW`, `idxW` in proofs). This script greps every other `.lean` file under
`ConAgua/` for the raw forms:

  L       a record/column array indexed directly (`AREC.u64[...]`), a tier count read
          (`CTL.u64[4 + t]`), a handle tier decode (`(h >> 27) & 1`);
  proof   a record/column array read (`rdW (m.arr64 AREC) ...`, `rd64 m AREC ...`,
          `m.arr64 AREC`), a raw count term (`rdW (... CTL) (4 + t)`), a raw stride
          (`* 4 + ... * 2`, `* 2 + t`), the accessors unfolded (`TRec.ad` in a proof), a count
          slot by its number (`viewOK m h 4`);

and prints the counts per kind and per file (`--files`), or the lines (`--lines [REGEX]`).
Exit status 0; `--max N` exits 1 when the total exceeds N.
"""
import argparse
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")

# Record arrays and one-word columns of the stores (StoreFields.lean).
ARRS = ["REC", "AREC", "SREC", "ZREC", "MREC", "IREC", "PREC", "SOREC", "CREC", "LEREC", "BREC",
        "FVREC", "LAREC", "FAREC", "PJREC", "NAREC", "NSREC", "NNREC", "LSREC",
        "ADER", "LADER", "FADER", "LEDER", "PJDER",
        "SHP", "MHP", "IHP", "LSHP", "SOLP", "CLP", "FVLP"]
# The count slots `CTL[ca + t]` of the stores.
CNTS = [2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 26, 28, 30, 32, 34, 36, 38, 40]

# The store library: these files may know the layout.
LIBRARY = re.compile(r"^ConAgua/(L/TRec|L/Notation|L/ModelGen|Arena/StoreFields\w*|Arena/StoreLib\w*|"
                     r"Arena/StoreRel|Arena/StoreGrow\w*|Arena/ConsLib\w*|Arena/SlotGrow\w*|"
                     r"Arena/\w*Store|Arena/LpCol|Arena/ExprMk|Arena/(App|BVar|Const|Forall|FVar|Imax|Lam|Let|Level|Lit|Ls|Max|NAnon|NNum|NStr|Param|Proj|Sort|Zero)Refine)\.lean$")

A = "|".join(ARRS)
C = "|".join(str(c) for c in CNTS)
PATS = {
    "L-arr": re.compile(rf"\b({A})\.u64\["),
    "L-cnt": re.compile(rf"\bCTL\.u64\[\s*({C})\s*\+"),
    "L-tier": re.compile(r">>\s*27\)\s*&\s*1\b"),
    "P-arr": re.compile(rf"(rdW|rd64)\s+\(?\s*[\w.₀₁₂']*\s*(\.arr64\s+|\s+)({A})\b|arr64\s+({A})\)\s*\("),
    "P-cnt": re.compile(rf"\bCTL\)\s*\(\s*({C})\s*\+"),
    "P-stride": re.compile(r"\*\s*(4|6|8)\s*\+\s*[\w.() ]+\*\s*(2|3|4)\b"),
    # the accessors unfolded outside the library (bridges of not yet converted models)
    "P-unfold": re.compile(r"\bTRec\.ad\b"),
    # a store's count slot named by its number (`viewOK m h 4`, `vok 22`)
    "P-cslot": re.compile(rf"\b(viewOK [\w₀-₉']+ [\w₀-₉']+|vok) ({C})\b"),
}


def scan(path):
    out = []
    with open(path, encoding="utf-8") as f:
        for n, line in enumerate(f, 1):
            code = line.split("--", 1)[0]
            for k, p in PATS.items():
                if p.search(code):
                    out.append((k, n, line.rstrip()))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--files", action="store_true", help="counts per file")
    ap.add_argument("--lines", nargs="?", const="", default=None, help="print the lines (files matching REGEX)")
    ap.add_argument("--max", type=int, default=None)
    a = ap.parse_args()
    tot = {k: 0 for k in PATS}
    per = {}
    for d, _, fs in os.walk(os.path.join(ROOT, "ConAgua")):
        for fn in fs:
            if not fn.endswith(".lean"):
                continue
            p = os.path.join(d, fn)
            rel = os.path.relpath(p, ROOT)
            if LIBRARY.match(rel) or "/Proto/" in rel:
                continue
            hits = scan(p)
            if not hits:
                continue
            per[rel] = hits
            seen = set()
            for k, n, _ in hits:
                tot[k] += 1
    total = sum(len({n for _, n, _ in h}) for h in per.values())
    if a.lines is not None:
        rx = re.compile(a.lines)
        for rel in sorted(per):
            if rx.search(rel):
                for k, n, l in per[rel]:
                    print(f"{rel}:{n}: [{k}] {l.strip()}")
    if a.files:
        for rel in sorted(per, key=lambda r: -len(per[r])):
            print(f"{len({n for _, n, _ in per[rel]}):5d}  {rel}")
    print("  ".join(f"{k} {v}" for k, v in tot.items()), f"| lines {total} in {len(per)} files")
    if a.max is not None and total > a.max:
        sys.exit(1)


if __name__ == "__main__":
    main()
