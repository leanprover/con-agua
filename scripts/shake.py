#!/usr/bin/env python3
"""The import gate: `lake shake` over ConAgua, every proposed removal pinned in an allowlist.

    scripts/shake.py                  check (needs a built tree: `scripts/lake build`)
    scripts/shake.py --write-allowlist   rewrite scripts/shake-allowlist.txt from the current proposals,
                                      keeping the reasons of lines that stay
    scripts/shake.py --proposals      print the tool's full output (removals and additions)

What it runs. `scripts/shake-setup.sh` builds Lean's import minimizer (`lake shake`, patched for
classic files) into `_tmp/shake-tool/<toolchain>/`; this script runs it on the modules of the default build
(the `ConAgua` and `ConAguaAsm` libraries, as `scripts/modules_check.py` reads the lakefile),
loaded into one environment, and lets it minimize every one of them except those in
`scripts/shake-keep.txt`. The tool reads what each module needs from its `.olean`: the modules of
the constants its declarations mention, plus what elaboration recorded (`recordExtraModUse`: the
simp lemmas a `simp` used, `rfl` ones included; the modules of macros, elaborators and attributes
used; the module that put an attribute on a used constant).

What it checks. Every import the tool proposes to remove must be listed in
`scripts/shake-allowlist.txt` (`<file> TAB <import line> TAB # <reason>`). A new proposal fails the
gate: delete the import (then build: the build is the arbiter), or, if the build needs it, add the
line with the reason. A listed line the tool no longer proposes fails too: delete it. Additions
the tool proposes (an import a module reaches only through another one) are not checked.

What the tool cannot see (each found by building, docs/design/shake.md):
  * a name inside a syntax quotation of a macro (`` `(L.TRec.cntE …) `` in `L/Notation.lean``): the
    macro's module must have the name's module in its environment when it is compiled, else the
    hygienic name does not resolve where the macro is used. Macro-defining modules are in
    shake-keep.txt;
  * `open N` needs `N` to exist; `set_option`, `#guard`, `#eval`, `example` leave no constant;
  * names that a command reads (`err_stmt X := name`, `l_model … extra [name]`);
  * `meta import`s and the `public` of an import that loads an attribute's initializer
    (`register_grind_attr` needs `Lean.Meta.Tactic.Grind.Attr` at meta level);
  * auxiliaries realized in several modules (`_sparseCasesOn_N.else_eq`, `match_N`): in the joint
    environment one copy wins, so the tool can name the wrong module.
Top modules that cannot be loaded with the others (an executable's `main`, `JOINT_SEPARATE`) are not
loaded; the modules only they reach are not checked.
"""
import json, os, re, subprocess, sys, tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TOOLCHAIN = re.sub(r"[^A-Za-z0-9.\n-]", "_", open(os.path.join(ROOT, "lean-toolchain")).read().strip())
TOOL = os.path.join(ROOT, "_tmp", "shake-tool", TOOLCHAIN, ".lake", "build", "bin", "shaketool")
ALLOW = os.path.join(ROOT, "scripts", "shake-allowlist.txt")
KEEP = os.path.join(ROOT, "scripts", "shake-keep.txt")
# top modules that cannot be loaded with the others (`L.Arena.bv` is declared in both
# `Arena/LiftBench.lean` and `Arena/NatBits.lean`); the modules only they reach are not checked
JOINT_SEPARATE = {"ConAgua.Compiler.WFAllBench"}
IMP = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)\s*$", re.M)


def src(m):
    return os.path.join(ROOT, "ConAgua.lean" if m == "ConAgua" else m.replace(".", "/") + ".lean")


def header_imports(m):
    out = []
    text = open(src(m), encoding="utf-8").read()
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    for line in text.split("\n"):
        s = line.strip()
        if not s or s.startswith("--") or s in ("module", "prelude"):
            continue
        mm = IMP.match(s)
        if not mm:
            break
        out.append(mm.group(1))
    return out


def default_build():
    """The ConAgua/ConAguaAsm modules the default targets build."""
    t = tomllib.load(open(os.path.join(ROOT, "lakefile.toml"), "rb"))
    files = set()
    for top in ("ConAgua", "ConAguaAsm"):
        for dp, _, fs in os.walk(os.path.join(ROOT, top)):
            for f in fs:
                if f.endswith(".lean"):
                    files.add(os.path.relpath(os.path.join(dp, f), ROOT)[:-5].replace("/", "."))
    files.add("ConAgua")
    listed = set()
    for lib in t.get("lean_lib", []):
        if lib["name"] in ("ConAgua", "ConAguaAsm"):
            listed |= set(lib.get("roots", [lib["name"]])) | set(lib.get("globs", []))
    listed |= {f for g in list(listed) if g.endswith(".+") for f in files if f.startswith(g[:-1])}
    reach, stack, imps = set(), [m for m in listed if m in files], {}
    while stack:
        m = stack.pop()
        if m in reach:
            continue
        reach.add(m)
        imps[m] = [x for x in header_imports(m) if x in files]
        stack += imps[m]
    return reach, imps


def closure(imps, ms):
    seen, stack = set(), list(ms)
    while stack:
        m = stack.pop()
        if m not in seen:
            seen.add(m)
            stack += imps.get(m, [])
    return seen


def run_tool():
    if not os.path.exists(TOOL):
        r = subprocess.run([os.path.join(ROOT, "scripts", "shake-setup.sh")], cwd=ROOT,
                           stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
        if r.returncode:
            print("SHAKE GATE ERROR: scripts/shake-setup.sh failed:\n" + r.stderr[-2000:])
            sys.exit(3)
    mods, imps = default_build()
    imported = {x for m in mods for x in imps[m]}
    tops = sorted(m for m in mods if m not in imported)
    defs_main = re.compile(r"^(?:public\s+)?(?:unsafe\s+)?def\s+main\b", re.M)
    joint = [m for m in tops if m not in JOINT_SEPARATE and not defs_main.search(open(src(m), encoding="utf-8").read())]
    keep = set()
    if os.path.exists(KEEP):
        keep = {l.split("#")[0].strip() for l in open(KEEP)} - {""}
    only = sorted(closure(imps, joint) - keep - {"ConAgua"})
    args = []
    for m in only:
        args += ["--only", m]
    env = dict(os.environ, SHAKE_SRC=ROOT)
    r = subprocess.run([os.path.join(ROOT, "scripts", "lake"), "env", TOOL] + args + joint,
                       cwd=ROOT, env=env, capture_output=True, text=True)
    out = r.stdout + r.stderr
    if "uncaught exception" in out or re.search(r"^error:", out, re.M):
        print("SHAKE GATE ERROR: the tool did not run:\n" + out[-3000:])
        sys.exit(3)
    return out


# imports the gate judges: of this repository's modules, not `meta`, not of a module that only declares
# attributes (an unused import of one costs nothing: it is a leaf that every proof module reaches)
ATTR_MODULES = {"ConAgua.Arena.GrindAttr", "ConAgua.L.GrindAttr", "ConAgua.Arena.IndGrindAttr",
                "ConAgua.Arena.LevelGrindAttr", "ConAgua.Arena.NatGrindAttr", "ConAgua.Arena.DefEqGrindAttr",
                "ConAgua.Census.Attr"}


def checked(item):
    mod = item.split()[-1]
    return mod.split(".")[0] in ("ConAgua", "ConAguaAsm") and mod not in ATTR_MODULES and " meta " not in f" {item} "


def proposals(out):
    root = ROOT.rstrip("/") + "/"
    cur, props, rem, add = None, set(), {}, {}
    for line in out.split("\n"):
        if re.match(r"^\S.*\.lean:$", line):
            cur = line[:-1].replace(root, "").lstrip("./")
        elif cur and line.strip().startswith(("remove #[", "add #[")):
            kind, body = line.strip().split(" #[", 1)
            for item in body.rstrip("]").split(", "):
                if item.strip():
                    (rem if kind == "remove" else add).setdefault(cur, set()).add(item.strip())
    for f, items in rem.items():
        added = {a.split()[-1] for a in add.get(f, ())}
        for item in items:
            # `remove public import X` with `add import X` is a demotion, not a removal (in a classic
            # file it is the same line; in a `module` file the gate does not judge `public`)
            mod = item.split()[-1]
            if mod not in added and checked(item):
                props.add((f, item))
    return props


def read_allow():
    d = {}
    if os.path.exists(ALLOW):
        for line in open(ALLOW, encoding="utf-8"):
            if not line.strip() or line.startswith("#"):
                continue
            parts = line.rstrip("\n").split("\t")
            d[(parts[0], parts[1])] = parts[2] if len(parts) > 2 else "#"
    return d


def main():
    out = run_tool()
    if "--proposals" in sys.argv:
        print(out)
        return 0
    props = proposals(out)
    allow = read_allow()
    if "--write-allowlist" in sys.argv:
        head = [l for l in open(ALLOW, encoding="utf-8") if l.startswith("#")] if os.path.exists(ALLOW) else []
        with open(ALLOW, "w", encoding="utf-8") as fh:
            fh.writelines(head)
            for p in sorted(props):
                fh.write(f"{p[0]}\t{p[1]}\t{allow.get(p, '# TODO: reason')}\n")
        print(f"shake: wrote {len(props)} lines to {os.path.relpath(ALLOW, ROOT)}")
        return 0
    new = sorted(props - set(allow))
    stale = sorted(set(allow) - props)
    if new:
        print(f"SHAKE GATE FAIL: {len(new)} import(s) the tool finds unused, not in scripts/shake-allowlist.txt:")
        for f, i in new:
            print(f"    {f}: {i}")
        print("    Delete each import and build; if the build needs it, add the line to the allowlist with")
        print("    the reason (scripts/shake.py's docstring lists what the tool cannot see).")
    if stale:
        print(f"SHAKE GATE FAIL: {len(stale)} allowlist line(s) the tool no longer proposes (delete them):")
        for f, i in stale:
            print(f"    {f}: {i}")
    if not new and not stale:
        print(f"shake: ok, {len(props)} proposed removals, all allowlisted")
    return 1 if new or stale else 0


if __name__ == "__main__":
    sys.exit(main())
