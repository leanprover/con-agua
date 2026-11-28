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

allow = set()
if os.path.exists("scripts/modules_unbuilt.txt"):
    allow = {ln.split("#")[0].strip() for ln in open("scripts/modules_unbuilt.txt")} - {""}

IMP = re.compile(r"^(?:public |private )?(?:meta )?import (?:all )?(ConAgua[\w.]*)", re.M)
SUBS = ["."] + sorted(
    sub for sub in os.listdir(".")
    if not sub.startswith((".", "_")) and sub not in ("vendor", "commons", "scripts", "docs", "ConAgua")
    and os.path.isfile(os.path.join(sub, "lakefile.toml"))
)

total_files = 0
missing = []
for sub in SUBS:
    lf = os.path.join(sub, "lakefile.toml")
    t = tomllib.load(open(lf, "rb"))
    targets = t.get("lean_lib", []) + t.get("lean_exe", [])
    listed = set()
    for l in targets:
        listed |= set(l.get("globs", [])) | set(l.get("roots", []))
        if "root" in l:
            listed.add(l["root"])
    tops = tuple(sorted({m.split(".")[0] for m in listed if m.startswith("ConAgua")}))
    files = set()
    for top in tops:
        top_file = os.path.join(sub, f"{top}.lean")
        if os.path.isfile(top_file):
            files.add(top)
        top_dir = os.path.join(sub, top)
        if os.path.isdir(top_dir):
            for dp, _, fs in os.walk(top_dir):
                for f in fs:
                    if f.endswith(".lean"):
                        files.add(os.path.relpath(os.path.join(dp, f), sub)[:-5].replace(os.sep, "."))
    total_files += len(files)

    def imports(m):
        p = os.path.join(sub, m.replace(".", "/") + ".lean")
        return set(IMP.findall(open(p, encoding="utf-8", errors="replace").read()))

    listed |= {f for g in listed if g.endswith(".+") for f in files if f.startswith(g[:-1])}
    reach, stack = set(), [m for m in listed if m in files]
    while stack:
        m = stack.pop()
        if m not in reach:
            reach.add(m)
            stack += [x for x in imports(m) if x in files]
    missing.extend(sorted(files - reach - allow))

if missing:
    print("modules_check: these modules are not built by any lakefile target (add them to the "
          "lib's globs in lakefile.toml, or to scripts/modules_unbuilt.txt if deliberate):")
    print("\n".join("  " + m for m in missing))
    sys.exit(1)
print(f"modules_check: ok ({total_files} modules, {len(allow)} deliberately unbuilt)")
