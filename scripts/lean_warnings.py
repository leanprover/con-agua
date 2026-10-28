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
"""
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
LIB = os.path.join(".lake", "build", "lib", "lean")
STORE = os.path.join("_tmp", "lake-cache-v2", "logs")
PKG = "ConAgua"
TOPS = ("ConAgua", "ConAguaAsm")
ELAB_JOBS = 4  # elaborations at once (each Lean with LEAN_NUM_THREADS=4)


def is_module(rel):
    return rel.endswith(".lean") and (rel == "ConAgua.lean" or rel.split("/")[0] in TOPS)


def store_path(root, dep_hash):
    return os.path.join(root, STORE, PKG, f"{dep_hash}.json")


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
    trace_p = os.path.join(root, LIB, rel[:-len(".lean")] + ".trace")
    t = read_json(trace_p)
    if not isinstance(t, dict) or "depHash" not in t:
        return None, "no trace"
    if not t.get("synthetic", False):
        return [(e.get("level"), e.get("message", "")) for e in kept(t.get("log", []))], "compiled here"
    s = read_json(store_path(root, t["depHash"]))
    if isinstance(s, dict) and s.get("module") == rel:
        return [(e.get("level"), e.get("message", "")) for e in s.get("log", [])], "log store"
    return None, "restored from the cache, no stored log"


def up_to_date(root, rels):
    """Whether Lake considers these modules built (`lake build --no-build`, read-only: no staging, no
    writes), i.e. whether their traces belong to the current sources and imports."""
    mods = [r[:-len(".lean")].replace("/", ".") for r in rels]
    if not mods:
        return True
    env = dict(os.environ, LAKE_ARTIFACT_CACHE="false")
    r = subprocess.run([os.path.join(root, "scripts", "lake"), "build", "--no-build", *mods], cwd=root,
                       env=env, capture_output=True, text=True)
    return r.returncode == 0


def elaborate(root, rel):
    """The messages of `lake lean FILE -- --json` (Lake runs Lean with the module's own setup and options,
    as the build does), in the log's format. Plain `lake`, read-only (no cache writes; the imports are
    built, so Lake compiles nothing): several run at once, which the wrapper's worktree lock would forbid.
    If the source did not change meanwhile, the log goes into the log store under the trace's input hash,
    so the next checkout restoring this module (the queue's merge) needs no elaboration."""
    src = os.path.join(root, rel)
    before = os.stat(src).st_mtime_ns, os.path.getsize(src)
    env = dict(os.environ, LAKE_CACHE_DIR=os.path.realpath(os.path.join(root, "_tmp", "lake-cache-v2")))
    env.pop("LAKE_ARTIFACT_CACHE", None)  # Lake's default: read the cache, never write it
    env.setdefault("LEAN_NUM_THREADS", "4")
    r = subprocess.run(["lake", "lean", rel, "--", "--json"], cwd=root, env=env,
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
    t = read_json(os.path.join(root, LIB, rel[:-len(".lean")] + ".trace"))
    if (os.stat(src).st_mtime_ns, os.path.getsize(src)) == before and isinstance(t, dict) and "depHash" in t:
        put(root, t["depHash"], rel, [{"level": lvl, "message": m} for lvl, m in msgs])
    return msgs


def harvest(checkout, root=ROOT, since=0):
    """Publish the logs of the non-synthetic traces under `checkout`/.lake/build written at or after
    `since` (ns; scripts/lake: the build's start), never overwriting an entry."""
    lib = os.path.join(checkout, LIB)
    new = 0
    for dp, dn, fn in os.walk(lib):
        for f in fn:
            if not f.endswith(".trace"):
                continue
            rel = os.path.relpath(os.path.join(dp, f), lib)[:-len(".trace")] + ".lean"
            if not is_module(rel) or os.stat(os.path.join(dp, f)).st_mtime_ns < since:
                continue
            t = read_json(os.path.join(dp, f))
            if not isinstance(t, dict) or t.get("synthetic", True) or "depHash" not in t:
                continue
            new += put(root, t["depHash"], rel, kept(t.get("log", [])))
    return new


def put(root, dep_hash, rel, log):
    dst = store_path(root, dep_hash)
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


def main():
    args = sys.argv[1:]
    if args and args[0] == "--harvest":
        for d in args[1:]:
            print(f"{d}: {harvest(os.path.abspath(d))} log(s) published")
        return 0
    no_elab = "--no-elab" in args
    args = [a for a in args if a != "--no-elab"]
    if args[:1] == ["--all"]:
        files = sorted(os.path.relpath(os.path.join(dp, f), ROOT)
                       for top in TOPS for dp, dn, fn in os.walk(os.path.join(ROOT, top))
                       for f in fn if f.endswith(".lean")) + ["ConAgua.lean"]
    elif args[:1] == ["--base"] or not args:
        import gate_select
        files = gate_select.changed_paths(args[1] if args else None)
    else:
        files = args
    files = [f for f in files if is_module(f) and os.path.isfile(os.path.join(ROOT, f))]
    traced = [f for f in files if os.path.isfile(os.path.join(ROOT, LIB, f[:-len(".lean")] + ".trace"))]
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
