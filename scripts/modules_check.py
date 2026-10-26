#!/usr/bin/env python3
"""Check that every ConAgua/**/*.lean module is built by some lakefile target.

The ConAgua library lists its modules by hand (`globs` in lakefile.toml), and a conflicted
merge can silently drop entries; a dropped module is then never built or checked. A module
counts as built if it is listed by a target or imported (transitively) by a listed module.
Modules that are deliberately not built go in scripts/modules_unbuilt.txt (one per line,
`#` comments). Exit 1 and list the unbuilt modules otherwise."""
import glob, os, re, sys, tomllib

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)
t = tomllib.load(open("lakefile.toml", "rb"))
targets = t.get("lean_lib", []) + t.get("lean_exe", [])
listed = set()
for l in targets:
    listed |= set(l.get("globs", [])) | set(l.get("roots", []))
    if "root" in l:
        listed.add(l["root"])
files = {f[:-5].replace("/", ".") for f in glob.glob("ConAgua/**/*.lean", recursive=True)} | {"ConAgua"}
IMP = re.compile(r"^(?:public |private )?(?:meta )?import (?:all )?(ConAgua[\w.]*)", re.M)


def imports(m):
    p = "ConAgua.lean" if m == "ConAgua" else m.replace(".", "/") + ".lean"
    return set(IMP.findall(open(p, encoding="utf-8", errors="replace").read()))


# `X.+` globs: every module under `X`
listed |= {f for g in listed if g.endswith(".+") for f in files if f.startswith(g[:-1])}
reach, stack = set(), [m for m in listed if m in files]
while stack:
    m = stack.pop()
    if m not in reach:
        reach.add(m)
        stack += [x for x in imports(m) if x in files]
allow = set()
if os.path.exists("scripts/modules_unbuilt.txt"):
    allow = {ln.split("#")[0].strip() for ln in open("scripts/modules_unbuilt.txt")} - {""}
missing = sorted(files - reach - allow)
if missing:
    print("modules_check: these modules are not built by any lakefile target (add them to the "
          "ConAgua lib's globs in lakefile.toml, or to scripts/modules_unbuilt.txt if deliberate):")
    print("\n".join("  " + m for m in missing))
    sys.exit(1)
print(f"modules_check: ok ({len(files)} modules, {len(allow)} deliberately unbuilt)")
