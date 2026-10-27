#!/usr/bin/env python3
"""The checker's array names by number, read from `ConAgua/Layout.lean` (no Lean build).

`word_names()` maps a word array's number to its qualified name below `L` (`Arena.POOL`,
`Front.NID`), `byte_names()` the same for byte arrays, `tiered()` is the set of tiered word
arrays' numbers. `arr_term(n, opened)` writes word array number `n` by its name; the namespace
prefix is dropped when it is one of `opened` (e.g. `["Arena"]`). Used by the generators
that emit array lists (`scripts/preloop_ws.py`). As a script: `arr_names.py N…` prints the terms.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

ROW = re.compile(r"\|\s*/--.*?-/\s*([\w.]+)\s*:\s*(byte|word)(\s+tiered)?\s*:=\s*(\d+)", re.S)


def _rows():
    src = open(os.path.join(ROOT, "ConAgua", "Layout.lean")).read()
    body = src[src.index("declare_arrays checkerArrays"):src.index("/-! ## Aliases")]
    return [(m.group(1), m.group(2), bool(m.group(3)), int(m.group(4))) for m in ROW.finditer(body)]


def word_names():
    return {n: name for name, k, _, n in _rows() if k == "word"}


def byte_names():
    return {n: name for name, k, _, n in _rows() if k == "byte"}


def tiered():
    return {n for _, k, t, n in _rows() if k == "word" and t}


def _short(name, opened):
    ns, _, base = name.rpartition(".")
    return base if ns in opened else name


def arr_term(n, opened=()):
    w = word_names()
    if n in w:
        return _short(w[n], opened)
    raise KeyError("word array %d is not in checkerArrays" % n)


if __name__ == "__main__":
    print(", ".join(arr_term(int(a), ["Arena"]) for a in sys.argv[1:]))
