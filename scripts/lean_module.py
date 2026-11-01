"""The header of a generated `.lean` file as a `module` (PLAN.md, "New files are modules").

`modularize(text)` turns a classic header into a module header, as every ConAgua file has one:
`module` before the first import, each `import X` as `public import X`, and
`@[expose] public section` after the imports (definitions keep their bodies visible to the
importers, theorems export only their statements). With `meta=True` the file also gets
`meta import X` for each of its imports: it runs an elaborator (`asm_lit`, `prog_wf`,
`inl_round_fns`, `chk_lk`, …) that evaluates terms over the imported definitions at elaboration
time, and the module system lets compiled code run on a definition only if its module is
imported at the meta level. `import_all` lists modules imported with `import all` (their
private part too), for definitions whose bodies a kernel check unfolds although their module
does not expose them (e.g. `Init.Data.Repr`'s `Nat.repr`, which `toString` on a function name
reaches). A text that is already a module is returned unchanged.
"""
import re

IMPORT = re.compile(r"^import\s+([\w.]+)\s*$")


def modularize(text, meta=False, import_all=()):
    lines = text.split("\n")
    if any(l.strip() == "module" for l in lines):
        return text
    first = last = None
    for i, l in enumerate(lines):
        s = l.strip()
        if s == "" or s.startswith("--"):
            continue
        if IMPORT.match(s):
            first = i if first is None else first
            last = i
            continue
        break
    if first is None:
        return "module\n\n@[expose] public section\n\n" + text
    mods = [IMPORT.match(lines[i].strip()).group(1) for i in range(first, last + 1)
            if IMPORT.match(lines[i].strip())]
    head = ["module", ""] + [f"public import {m}" for m in mods]
    if meta:
        head += [f"meta import {m}" for m in mods]
    head += [f"import all {m}" for m in import_all]
    head += ["", "@[expose] public section"]
    return "\n".join(lines[:first] + head + lines[last + 1:])
