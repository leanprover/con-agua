#!/usr/bin/env python3
"""The Lean warnings of the modules a change touches, including those restored from the shared cache.

    scripts/lean_warnings.py [--base REV]     the .lean files changed since BASE (default: the merge-base of
                                              HEAD and master; uncommitted changes count), vendor/ excluded
    scripts/lean_warnings.py --all            every module under ConAgua/ and ConAguaAsm/
    scripts/lean_warnings.py FILE...          these files
    --no-elab                                 do not elaborate a module whose log is unknown (list it instead)
    scripts/lean_warnings.py --harvest DIR... publish the logs of the modules Lake compiled itself in these
                                              checkouts (their `.lake/build`) into the log store

Prints `warning: file:line:col: message` per warning (Lake's format, which scripts/fix-lean-warnings.py
reads) and exits 1 if there is any (2 with --no-elab if a log is unknown). Run it after `scripts/lake build`
(the gate `warnings` runs after `build`): it checks with `lake build --no-build` that the modules are built
(exit 3 if not), so that their traces belong to the current sources.

Why not the build log: a module that `scripts/lake build` restores from the shared artifact cache gets a
synthetic trace whose log is EMPTY (Lake's cache keeps the outputs, not the messages), so its warnings are
never printed, and a lane whose touched module some other checkout had already compiled saw a clean build.
So the warnings are kept beside the cache: scripts/lake, after a build whose sources did not change
(the same guard that publishes the cache mappings), copies the log of every module Lake compiled into
`_tmp/lake-cache-v2/logs/<pkg>/<input hash>.json`. The input hash (the trace's `depHash`, the cache key)
covers the module's source, its imports' oleans and the options, so the log is the one any compilation of
that input prints. Per module this script takes, in order:
  1. its local trace (`.lake/build/lib/lean/<module>.trace`) if Lake compiled it here (not synthetic):
     the log in it;
  2. else the log store's entry for the trace's `depHash`;
  3. else (a module compiled before logs were kept, or by a plain `lake`): `lake lean FILE`, which
     elaborates it once with the module's setup and options against the built imports (four at a time),
     and its output, which then goes into the log store too.
A module with no trace at all (not among the targets `build` built, e.g. one only an exe reaches) is
first built with `scripts/lake build` (its imports may be unbuilt, and a plain `lake lean` that has to
restore or build them fails: concurrent builds in one tree, read-only cache hard links); then 1.
"""
import json
import os
import subprocess
import sys
import tomllib
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
LIB = os.path.join(".lake", "build", "lib", "lean")
STORE = os.path.join("_tmp", "lake-cache-v2", "logs")
PKG = "ConAgua"


def discover_packages():
    pkgs = [("", "ConAgua", ("ConAgua",), ("ConAgua.lean",))]
    for sub in sorted(os.listdir(ROOT)):
        if sub.startswith((".", "_")) or sub in ("vendor", "commons", "scripts", "docs", "ConAgua"):
            continue
        pkg_dir = os.path.join(ROOT, sub)
        lf = os.path.join(pkg_dir, "lakefile.toml")
        if not os.path.isfile(lf):
            continue
        t = tomllib.load(open(lf, "rb"))
        tops = []
        roots = []
        for lib in t.get("lean_lib", []):
            tops.append(lib["name"])
            if os.path.isfile(os.path.join(pkg_dir, f"{lib['name']}.lean")):
                roots.append(f"{lib['name']}.lean")
        pkgs.append((sub, t.get("name", sub), tuple(tops), tuple(roots)))
    return pkgs


PACKAGES = discover_packages()
ELAB_JOBS = 4  # elaborations at once (each Lean with LEAN_NUM_THREADS=4)


def split_rel(rel):
    if not rel.endswith(".lean"):
        return None
    for sub, pkg, tops, roots in PACKAGES:
        prefix = f"{sub}/" if sub else ""
        if prefix and not rel.startswith(prefix):
            continue
        pkg_dir = os.path.join(ROOT, sub) if sub else ROOT
        if sub and not os.path.isfile(os.path.join(pkg_dir, "lakefile.toml")):
            continue
        inner = rel[len(prefix):]
        if inner in roots or inner.split("/")[0] in tops:
            return sub, pkg, inner
    return None


def is_module(rel):
    return split_rel(rel) is not None


def store_path(root, dep_hash, pkg=PKG):
    return os.path.join(root, STORE, pkg, f"{dep_hash}.json")


def read_json(p):
    try:
        with open(p) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return None


def kept(log):
    """The entries worth keeping: everything but Lake's `trace` lines (the lean command line)."""
    return [e for e in log if e.get("level") != "trace"]


def known_log(root, rel):
    """(the module's messages as [(level, text)], how) or (None, why unknown)."""
    info = split_rel(rel)
    if info is None:
        return None, "outside package"
    sub, pkg, inner = info
    pkg_dir = os.path.join(root, sub) if sub else root
    trace_p = os.path.join(pkg_dir, LIB, inner[:-len(".lean")] + ".trace")
    t = read_json(trace_p)
    if not isinstance(t, dict) or "depHash" not in t:
        return None, "no trace"
    if not t.get("synthetic", False):
        return [(e.get("level"), e.get("message", "")) for e in kept(t.get("log", []))], "compiled here"
    s = read_json(store_path(root, t["depHash"], pkg))
    if isinstance(s, dict) and s.get("module") in (rel, inner):
        return [(e.get("level"), e.get("message", "")) for e in s.get("log", [])], "log store"
    return None, "restored from the cache, no stored log"


def up_to_date(root, rels):
    """Whether Lake considers these modules built (`lake build --no-build`, read-only: no staging, no
    writes), i.e. whether their traces belong to the current sources and imports."""
    by_sub = {}
    for r in rels:
        info = split_rel(r)
        if info:
            sub, _, inner = info
            by_sub.setdefault(sub, []).append(inner[:-len(".lean")].replace("/", "."))
    env = dict(os.environ, LAKE_ARTIFACT_CACHE="false")
    for sub, mods in sorted(by_sub.items()):
        cmd = [os.path.join(root, "scripts", "lake")] + (["-d", sub] if sub else []) + ["build", "--no-build", *mods]
        r = subprocess.run(cmd, cwd=root, env=env, capture_output=True, text=True)
        if r.returncode != 0:
            return False
    return True


def elaborate(root, rel):
    """The messages of `lake lean FILE -- --json` (Lake runs Lean with the module's own setup and options,
    as the build does), in the log's format. Plain `lake`, read-only (no cache writes; the imports are
    built, so Lake compiles nothing): several run at once, which the wrapper's worktree lock would forbid.
    If the source did not change meanwhile, the log goes into the log store under the trace's input hash,
    so the next checkout restoring this module (the queue's merge) needs no elaboration."""
    sub, pkg, inner = split_rel(rel)
    pkg_dir = os.path.join(root, sub) if sub else root
    src = os.path.join(pkg_dir, inner)
    before = os.stat(src).st_mtime_ns, os.path.getsize(src)
    env = dict(os.environ, LAKE_CACHE_DIR=os.path.realpath(os.path.join(root, "_tmp", "lake-cache-v2")))
    env.pop("LAKE_ARTIFACT_CACHE", None)  # Lake's default: read the cache, never write it
    env.setdefault("LEAN_NUM_THREADS", "4")
    r = subprocess.run(["lake", "lean", inner, "--", "--json"], cwd=pkg_dir, env=env,
                       capture_output=True, text=True, timeout=3600)
    msgs, other = [], []
    for line in r.stdout.splitlines():
        try:
            m = json.loads(line) if line.startswith("{") else None
        except ValueError:
            m = None
        if not isinstance(m, dict) or "severity" not in m:
            other.append(line)
            continue
        pos = m.get("pos") or {}
        msgs.append((m["severity"], f"{rel}:{pos.get('line', 0)}:{pos.get('column', 0)}: {m.get('data', '')}"))
    if r.returncode != 0:
        if not any(lvl == "error" for lvl, _ in msgs):
            tail = "\n".join(other[-20:] + r.stderr.splitlines()[-20:])
            msgs.append(("error", f"{rel}: `lake lean` failed (exit {r.returncode}):\n{tail}"))
        return msgs
    t = read_json(os.path.join(pkg_dir, LIB, inner[:-len(".lean")] + ".trace"))
    if (os.stat(src).st_mtime_ns, os.path.getsize(src)) == before and isinstance(t, dict) and "depHash" in t:
        put(root, t["depHash"], rel, [{"level": lvl, "message": m} for lvl, m in msgs], pkg=pkg)
    return msgs


def harvest(checkout, root=ROOT, since=0, pkg=PKG):
    """Publish the logs of the non-synthetic traces under `checkout`/.lake/build written at or after
    `since` (ns; scripts/lake: the build's start), never overwriting an entry."""
    lib = os.path.join(checkout, LIB)
    if not os.path.isdir(lib):
        return 0
    sub_rel = os.path.relpath(checkout, root)
    prefix = "" if sub_rel == "." else sub_rel + "/"
    new = 0
    for dp, dn, fn in os.walk(lib):
        for f in fn:
            if not f.endswith(".trace"):
                continue
            rel = prefix + os.path.relpath(os.path.join(dp, f), lib)[:-len(".trace")] + ".lean"
            if not is_module(rel) or os.stat(os.path.join(dp, f)).st_mtime_ns < since:
                continue
            t = read_json(os.path.join(dp, f))
            if not isinstance(t, dict) or t.get("synthetic", True) or "depHash" not in t:
                continue
            new += put(root, t["depHash"], rel, kept(t.get("log", [])), pkg=pkg)
    return new


def put(root, dep_hash, rel, log, pkg=PKG):
    dst = store_path(root, dep_hash, pkg)
    if os.path.exists(dst):
        return 0
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    tmp = f"{dst}.tmp-{os.getpid()}"
    with open(tmp, "w") as fh:
        json.dump({"module": rel, "log": log}, fh)
    try:
        os.link(tmp, dst)
        return 1
    except FileExistsError:
        return 0
    finally:
        os.unlink(tmp)


def trace_path(root, rel):
    sub, _, inner = split_rel(rel)
    pkg_dir = os.path.join(root, sub) if sub else root
    return os.path.join(pkg_dir, LIB, inner[:-len(".lean")] + ".trace")


def main():
    args = sys.argv[1:]
    if args and args[0] == "--harvest":
        for d in args[1:]:
            d_abs = os.path.abspath(d)
            n = 0
            for sub, pkg, _, _ in PACKAGES:
                pkg_dir = os.path.join(d_abs, sub) if sub else d_abs
                if os.path.isfile(os.path.join(pkg_dir, "lakefile.toml")):
                    n += harvest(pkg_dir, ROOT, pkg=pkg)
            print(f"{d}: {n} log(s) published")
        return 0
    no_elab = "--no-elab" in args
    args = [a for a in args if a != "--no-elab"]
    if args[:1] == ["--all"]:
        files = []
        for sub, _, tops, roots in PACKAGES:
            pkg_dir = os.path.join(ROOT, sub) if sub else ROOT
            if not os.path.isfile(os.path.join(pkg_dir, "lakefile.toml")):
                continue
            prefix = f"{sub}/" if sub else ""
            files += sorted(prefix + os.path.relpath(os.path.join(dp, f), pkg_dir)
                            for top in tops for dp, dn, fn in os.walk(os.path.join(pkg_dir, top))
                            for f in fn if f.endswith(".lean"))
            files += [prefix + r for r in roots if os.path.isfile(os.path.join(pkg_dir, r))]
    elif args[:1] == ["--base"] or not args:
        import gate_select
        files = gate_select.changed_paths(args[1] if args else None)
    else:
        files = args
    files = [f for f in files if is_module(f) and os.path.isfile(os.path.join(ROOT, f))]
    traced = [f for f in files if os.path.isfile(trace_path(ROOT, f))]
    if not up_to_date(ROOT, traced):
        print("lean_warnings: the modules are not built (`scripts/lake build --no-build` fails): their traces "
              "do not belong to these sources; run `scripts/lake build` first", file=sys.stderr)
        return 3
    unknown, how, logs, todo = [], {}, {}, []
    for rel in files:
        msgs, why = known_log(ROOT, rel)
        if msgs is None:
            if no_elab:
                unknown.append(f"{rel} ({why})")
                continue
            print(f"{rel}: {why}; elaborating", file=sys.stderr, flush=True)
            todo.append(rel)
            continue
        how[why] = how.get(why, 0) + 1
        logs[rel] = msgs
    # A module with no trace is outside the targets the build gate built (e.g. `ConAgua/E2E/Ref.lean`,
    # only reached by an exe): its imports may be unbuilt too, and parallel `lake lean`s would then
    # build the same imports at once in one tree and fail. Build those modules first, once, with the
    # wrapper (cache hits, and their logs come with the build); elaborate only what is still unknown.
    untraced = [r for r in todo if known_log(ROOT, r)[1] == "no trace"]
    if untraced:
        print(f"lean_warnings: building {len(untraced)} untraced module(s) first", file=sys.stderr, flush=True)
        by_sub = {}
        for r in untraced:
            sub, _, inner = split_rel(r)
            by_sub.setdefault(sub, []).append(inner[:-len(".lean")].replace("/", "."))
        for sub, mods in sorted(by_sub.items()):
            cmd = [os.path.join(ROOT, "scripts", "lake")] + (["-d", sub] if sub else []) + ["build", *mods]
            subprocess.run(cmd, cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        still = []
        for rel in todo:
            msgs, why = known_log(ROOT, rel)
            if msgs is None:
                still.append(rel)
            else:
                how[why] = how.get(why, 0) + 1
                logs[rel] = msgs
        todo = still
    with ThreadPoolExecutor(ELAB_JOBS) as ex:
        for rel, msgs in zip(todo, ex.map(lambda r: elaborate(ROOT, r), todo)):
            how["elaborated"] = how.get("elaborated", 0) + 1
            logs[rel] = msgs
    warnings = [f"{lvl}: {m}" for rel in files for lvl, m in logs.get(rel, [])
                if lvl in ("warning", "error") and not m.startswith("vendor/")]
    for w in warnings:
        print(w)  # Lake's format, which scripts/fix-lean-warnings.py reads
    print(f"lean_warnings: {len(files)} module(s) ("
          + ", ".join(f"{n} {k}" for k, n in sorted(how.items())) + f"): {len(warnings)} warning(s)"
          + (f", {len(unknown)} with unknown log" if unknown else ""), file=sys.stderr)
    for u in unknown:
        print(f"  unknown: {u}", file=sys.stderr)
    return 1 if warnings else 2 if unknown else 0


if __name__ == "__main__":
    sys.exit(main())
