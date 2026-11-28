#!/usr/bin/env python3
"""Find simp lemma lists that name a constant the module does not import.

`simp [foo]`, `simp_all [foo]` (and `simp only`, `simpa`, `dsimp`, `l_model`'s `simp [..]`
option) fail with "unknown identifier" when `foo` is not in scope. Under `try`/`first` (like
`l_model`'s `simp` recipe, `(try simp_all [..]) <;> grind`) that error is swallowed: the step
silently never runs. This script reports every simp argument whose name is a constant of the
project (or of a package) but of none of the modules the file imports, directly or not.

Usage: scripts/simp_scope.py [--dump FILE] [--reuse] [PATH…]   (after `scripts/lake build`)

It runs `scripts/simp_scope.lean` (reads the `.olean`s of every built `ConAgua` module and of
their imports, ~40 s) to list every constant with its module and the import graph, then scans
the sources (default: `ConAgua/`). A name resolves if some constant in the file's import
closure (or the file itself) is that name or ends with `.name` (namespaces and `open`s are not
tracked: this over-approximates the scope, so it can miss a case but reports no name declared
anywhere in scope). Not reported: names declared nowhere, names that also occur outside the
file's simp lists (hypotheses, binders; an unimported constant there is a build error anyway),
constants of `Lean.*` (the builtin simprocs). Exit 1 if anything is reported.
"""
from __future__ import annotations

import argparse
import collections
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

SIMP_RE = re.compile(r"(?<![\w.'])(simp_all\??|simp\??|simpa\??|dsimp\??|simp_arith)(?![\w'])")


def blank_comments(src: str) -> str:
    """Comments and string literals replaced by spaces (newlines kept)."""
    out = list(src)
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif src.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth > 0:
            if src[i] != "\n":
                out[i] = " "
            i += 1
        elif src.startswith("'\"'", i):  # the character literal '"'
            i += 3
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            for k in range(i + 1, min(j, n)):
                if out[k] != "\n":
                    out[k] = " "
            i = j + 1
        else:
            i += 1
    return "".join(out)


IDENT_RE = re.compile(r"[A-Za-z_À-῿℀-⅏][\w'!?.À-῿₀-ₜ℀-⅏]*")


def simp_args(src: str):
    """Yield (offset, name) for each simp argument that starts with an identifier."""
    for m in SIMP_RE.finditer(src):
        i = m.end()
        # skip config/flags/`only`/location up to the `[` on the same logical call
        j = i
        depth = 0
        while j < len(src):
            c = src[j]
            if c == "(":
                depth += 1
            elif c == ")":
                if depth == 0:
                    break
                depth -= 1
            elif c == "[" and depth == 0:
                break
            elif depth == 0 and (c in "\n;|⟩<" or src.startswith("at ", j) or src.startswith("using", j)):
                break
            j += 1
        if j >= len(src) or src[j] != "[":
            continue
        # the list, split at top-level commas
        k, depth, start = j + 1, 0, j + 1
        items = []
        while k < len(src):
            c = src[k]
            if c in "([{⟨":
                depth += 1
            elif c in ")}⟩":
                depth -= 1
            elif c == "]":
                if depth == 0:
                    items.append((start, src[start:k]))
                    break
                depth -= 1
            elif c == "," and depth == 0:
                items.append((start, src[start:k]))
                start = k + 1
            k += 1
        for off, it in items:
            s = it.lstrip()
            off += len(it) - len(s)
            for pre in ("←", "<-", "↓", "↑", "-", "("):
                if s.startswith(pre):
                    s = s[len(pre):].lstrip()
            mm = IDENT_RE.match(s)
            if mm:
                name = mm.group(0).rstrip(".")
                if name.startswith("_root_."):
                    name = name[len("_root_."):]
                yield off, name


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--dump", default=os.path.join(ROOT, "_tmp", "simp_scope", "consts.txt"))
    ap.add_argument("--reuse", action="store_true", help="reuse an existing dump")
    ap.add_argument("paths", nargs="*", default=["ConAgua"])
    a = ap.parse_args()

    files = []
    for p in a.paths:
        p = os.path.join(ROOT, p) if not os.path.isabs(p) else p
        if os.path.isfile(p):
            files.append(p)
        for dp, _, fs in os.walk(p):
            files += [os.path.join(dp, f) for f in fs if f.endswith(".lean")]
    files = sorted(set(files))
    sub_prefixes = tuple(
        d + "/" for d in os.listdir(ROOT)
        if not d.startswith((".", "_")) and d not in ("vendor", "commons", "scripts", "docs", "ConAgua")
        and os.path.isfile(os.path.join(ROOT, d, "lakefile.toml"))
    )
    def mod_name(f):
        rel = os.path.relpath(f, ROOT)
        for pfx in sub_prefixes:
            if rel.startswith(pfx):
                rel = rel[len(pfx):]
                break
        return rel[:-5].replace(os.sep, ".")
    mod_of = {f: mod_name(f) for f in files}

    if not (a.reuse and os.path.exists(a.dump)):
        os.makedirs(os.path.dirname(a.dump), exist_ok=True)
        mods = []
        core_olean = os.path.join(ROOT, ".lake", "build", "lib", "lean")
        x86_olean = os.path.join(ROOT, "x86", ".lake", "build", "lib", "lean")
        for dp, _, fs in os.walk(os.path.join(ROOT, "ConAgua")):
            mods += [os.path.relpath(os.path.join(dp, f), ROOT)[:-5].replace(os.sep, ".")
                     for f in fs if f.endswith(".lean")]
        mods.append("ConAgua")
        core_built = [x for x in sorted(mods) if os.path.exists(os.path.join(core_olean, *x.split(".")) + ".olean")]
        x86_mods = []
        if os.path.isfile(os.path.join(ROOT, "x86", "ConAguaX86.lean")):
            x86_mods.append("ConAguaX86")
            for dp, _, fs in os.walk(os.path.join(ROOT, "x86", "ConAguaX86")):
                x86_mods += [os.path.relpath(os.path.join(dp, f), os.path.join(ROOT, "x86"))[:-5].replace(os.sep, ".")
                             for f in fs if f.endswith(".lean")]
        x86_built = [x for x in sorted(x86_mods) if os.path.exists(os.path.join(x86_olean, *x.split(".")) + ".olean")]
        lake_cmd = [os.path.join(ROOT, "scripts", "lake")] + (["-d", "x86"] if x86_built else [])
        r = subprocess.run(lake_cmd + ["env", "lean", "--run",
                            os.path.join(ROOT, "scripts", "simp_scope.lean"), a.dump] + core_built + x86_built, cwd=ROOT)
        if r.returncode != 0:
            sys.exit("simp_scope.lean failed (build first: scripts/lake build)")

    imports = collections.defaultdict(set)
    by_suffix = collections.defaultdict(set)  # last component -> {(name, module)}
    with open(a.dump, encoding="utf-8") as fh:
        for line in fh:
            kind, x, y = line.rstrip("\n").split(" ", 2)
            if kind == "I":
                imports[x].add(y)
            else:
                by_suffix[x.rsplit(".", 1)[-1]].add((x, y))

    closure_memo: dict[str, set[str]] = {}

    def closure(m: str) -> set[str]:
        if m in closure_memo:
            return closure_memo[m]
        seen, st = {m}, [m]
        while st:
            for y in imports.get(st.pop(), ()):
                if y not in seen:
                    seen.add(y)
                    st.append(y)
        closure_memo[m] = seen
        return seen

    bad = 0
    for f in files:
        src = blank_comments(open(f, encoding="utf-8").read())
        m = mod_of[f]
        if m not in imports:  # not in the dump (a file outside the library): its own imports
            imports[m] = set(re.findall(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", src, re.M))
        scope = closure(m)
        args = list(simp_args(src))
        # a name that also occurs outside the simp lists is a local (a hypothesis, a binder) or,
        # were it an unimported constant, an error there that no `try` hides: not reported
        rest = list(src)
        for off, name in args:
            rest[off:off + len(name)] = " " * len(name)
        rest = "".join(rest)
        for off, name in args:
            if re.search(r"(?<![\w.'])" + re.escape(name) + r"(?![\w'])", rest):
                continue
            last = name.rsplit(".", 1)[-1]
            cands = [(c, cm) for c, cm in by_suffix.get(last, ())
                     if c == name or c.endswith("." + name)]
            # `Lean.*` is the running Lean: its builtin simprocs (`reduceIte`) need no import
            if not cands or any(cm in scope or cm.startswith("Lean.") for _, cm in cands):
                continue
            line = src.count("\n", 0, off) + 1
            where = ", ".join(sorted({cm for _, cm in cands})[:3])
            print(f"{os.path.relpath(f, ROOT)}:{line}: simp argument `{name}` is not imported (declared in {where})")
            bad += 1
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
