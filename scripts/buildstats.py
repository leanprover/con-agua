#!/usr/bin/env python3
"""scripts/buildstats.py: file sizes and elaboration time (PLAN.md, "Build statistics").

A monitoring tool for the coordinator, NOT part of any lane's merge path: nothing here gates a merge.

    scripts/buildstats.py                 incremental: re-measure only what changed since the last run
    scripts/buildstats.py --full          wipe the measuring build and re-measure everything (~20 CPU-min)
    scripts/buildstats.py --lines-only    just the file sizes (instant; no build)
    scripts/buildstats.py --write         also write _tmp/buildstats/buildstats.md and append to _tmp/buildstats/buildstats.csv
                                          (the measurements always go to _tmp/buildstats/buildstats.json)

LINES (every .lean file under ConAgua/, vendor excluded) are counted in the measuring worktree.

TIMES are measured in a dedicated worktree `_tmp/wt/buildstats-run` (created on first use, moved to
master's HEAD on each run), built WITHOUT the shared Lake cache: plain `lake` (not scripts/lake) with
LAKE_CACHE_DIR at an empty private directory and LAKE_ARTIFACT_CACHE=false, LAKE_RESTORE_ARTIFACTS=false,
so modules really elaborate and nothing is written to the shared cache. Lean's profiler is on:
`-Dprofiler=true -Dprofiler.threshold=1000` is added to the worktree's lakefile.toml as `moreLeanArgs`
(never committed), so every elaboration step above 1 s is logged as `file:line:col: <step> took Ns`.
The per-module time is Lake's own `Built X (Ns)` line. The build is pinned to
CPUS cores, and is killed (by pid) above MEM_LIMIT_GB (PSS) memory in total or after TIMEOUT_S.

Incremental mode keeps the worktree's `.lake/build`, so Lake rebuilds only the modules whose sources
(or imports) changed; their numbers replace the stored ones in _tmp/buildstats/buildstats.json, the rest stay.
Module times are wall-clock seconds of a job under contention: compare runs, not single digits.
"""

import argparse
import csv
import datetime
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from census import tree_pids  # noqa: E402  (the memory-guard helper)

# ---- thresholds (the watch list) -------------------------------------------------------------
FILE_LINES_WATCH = 1500   # files over this many lines should be split
FILE_SECS_WATCH = 60      # files whose module takes longer than this (seconds) should be split
DECL_SECS_WATCH = 20      # declarations (elaboration steps) over this many seconds get investigated
PROFILER_THRESHOLD_MS = 1000  # the profiler logs steps above this
TOP_FILES, TOP_TIMES, TOP_DECLS = 25, 25, 40
# ---- resources -------------------------------------------------------------------------------
CPUS = "0-7"             # taskset list: at most 16 cores
MEM_LIMIT_GB = 28         # kill the whole build above this much (proportional) resident memory
TIMEOUT_S = 3 * 3600

RUN_WT = os.path.join(ROOT, "_tmp", "wt", "buildstats-run")
CACHE_DIR = os.path.join(ROOT, "_tmp", "buildstats-cache")  # private, kept empty: no cache hits
LOG = os.path.join(ROOT, "_tmp", "buildstats.log")
os.makedirs(os.path.join(ROOT, "_tmp", "buildstats"), exist_ok=True)
DATA = os.path.join(ROOT, "_tmp", "buildstats", "buildstats.json")
MD = os.path.join(ROOT, "_tmp", "buildstats", "buildstats.md")
CSV = os.path.join(ROOT, "_tmp", "buildstats", "buildstats.csv")


def git(*args, cwd=ROOT):
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True, text=True).stdout.strip()


# ---- the measuring worktree ------------------------------------------------------------------
def prepare_worktree(full):
    rev = git("rev-parse", "master")
    if not os.path.isdir(RUN_WT):
        subprocess.run([os.path.join(ROOT, "scripts", "new-worktree.sh"), "_tmp/wt/buildstats-run", rev],
                       cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
    else:
        git("checkout", "-q", "--", "lakefile.toml", cwd=RUN_WT)
        git("checkout", "-q", "--detach", rev, cwd=RUN_WT)
    if full and os.path.lexists(os.path.join(RUN_WT, ".lake", "build")):
        shutil.rmtree(os.path.join(RUN_WT, ".lake", "build"))
    shutil.rmtree(CACHE_DIR, ignore_errors=True)
    os.makedirs(CACHE_DIR)
    lf = os.path.join(RUN_WT, "lakefile.toml")
    s = open(lf).read()
    s = re.sub(r"^(defaultTargets = .*)$",
               rf'\1\nmoreLeanArgs = ["-Dprofiler=true", "-Dprofiler.threshold={PROFILER_THRESHOLD_MS}"]',
               s, count=1, flags=re.M)
    assert "moreLeanArgs" in s, "could not patch lakefile.toml"
    open(lf, "w").write(s)
    return rev


def tree_pss(pid):
    """Proportional resident memory (bytes) of `pid` and its descendants. Not RSS: every Lean job
    mmaps the same .olean files, and RSS counts those shared pages once per process."""
    total = 0
    for p in tree_pids(pid):
        try:
            with open(f"/proc/{p}/smaps_rollup") as fh:
                total += next((int(l.split()[1]) * 1024 for l in fh if l.startswith("Pss:")), 0)
        except (OSError, ValueError):
            pass
    return total


def run_guarded(cmd, env):
    """Run `cmd` (output to LOG); kill its process tree above MEM_LIMIT_GB or after TIMEOUT_S."""
    os.makedirs(os.path.dirname(LOG), exist_ok=True)
    with open(LOG, "w") as out:
        p = subprocess.Popen(cmd, cwd=RUN_WT, env=env, stdout=out, stderr=subprocess.STDOUT,
                             start_new_session=True)
        t0, peak, why = time.time(), 0, None
        while p.poll() is None:
            m = tree_pss(p.pid)
            peak = max(peak, m)
            if m > MEM_LIMIT_GB * 2**30:
                why = f"used {m / 2**30:.1f} GB, over MEM_LIMIT_GB = {MEM_LIMIT_GB}"
            elif time.time() - t0 > TIMEOUT_S:
                why = f"ran over {TIMEOUT_S} s"
            if why:
                for q in tree_pids(p.pid):
                    try:
                        os.kill(q, signal.SIGKILL)
                    except OSError:
                        pass
                p.wait()
                sys.exit(f"build killed: it {why}")
            time.sleep(0.5)
    return p.returncode, peak, time.time() - t0


# ---- parsing the log -------------------------------------------------------------------------
HEADER = re.compile(r"^\S+ \[\d+/\d+\] (Built|Replayed|Building) (\S+?)(?: \((.+)\))?$")
STEP = re.compile(r"^(?:info|warning|error): (\S+?):(\d+):(\d+): (.+?) took ([\d.]+)(ms|min|s|m)\b")


def secs(v, unit):
    return float(v) * {"ms": 0.001, "s": 1, "m": 60, "min": 60}[unit]


def parse_duration(t):
    return sum(secs(v, u) for v, u in re.findall(r"([\d.]+)\s*(ms|min|s|m)", t or ""))


def parse_log(text):
    """-> ({module: secs} for the modules actually built, {file: [steps]}, [failed modules])."""
    mods, steps, failed, cur = {}, {}, [], None
    for l in text.splitlines():
        m = HEADER.match(l)
        if m:
            kind, mod, dur = m.groups()
            cur = mod if kind == "Built" else None
            if kind == "Built":
                mods[mod] = parse_duration(dur)
            elif kind == "Building" and l.startswith("✖"):
                failed.append(mod)
            continue
        s = STEP.match(l)
        if s and cur:
            f, line, col, what, v, u = s.groups()
            if what.strip() == "blocked":  # waiting for another job, not work
                continue
            steps.setdefault(f, []).append({"line": int(line), "what": what.strip(), "secs": secs(v, u)})
    return mods, steps, failed


DECL_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
                     r"(theorem|lemma|def|abbrev|instance|example|structure|inductive|class|opaque|axiom|"
                     r"macro|syntax|elab|initialize|attribute|set_option|run_cmd|#\w+)\b\s*([^\s:({\[]*)")


def decl_name(path, line):
    try:
        lines = open(path, errors="replace").read().splitlines()
    except OSError:
        return "?"
    for i in range(line - 1, min(line + 6, len(lines))):
        m = DECL_RE.match(lines[i])
        if m:
            return f"{m.group(1)} {m.group(2)}".strip()
    return "?"


def module_file(mod):
    """ConAgua.Arena.X -> ConAgua/Arena/X.lean; vendored modules -> their vendor path."""
    rel = mod.replace(".", "/") + ".lean"
    if mod.startswith("ConAgua"):
        return rel
    if mod.startswith("ConLeche"):
        return "vendor/con-leche/" + rel
    return "vendor/con-ron/" + rel


# ---- data ------------------------------------------------------------------------------------
def load_data():
    try:
        return json.load(open(DATA))
    except (OSError, ValueError):
        return {"commit": None, "modules": {}, "decls": {}}


def count_lines():
    out = {}
    base = os.path.join(RUN_WT if os.path.isdir(RUN_WT) else ROOT, "ConAgua")
    for d, _, fs in os.walk(base):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(d, f)
                out[os.path.relpath(p, os.path.dirname(base))] = sum(1 for _ in open(p, errors="replace"))
    return out


def merge(data, mods, steps, rev):
    data["modules"].update(mods)
    for mod in mods:  # replace the steps of every re-measured module
        data["decls"].pop(module_file(mod), None)
    for f, ss in steps.items():
        by_line = {}
        for s in ss:  # steps nest (tactic inside elaboration): keep the longest per line
            if s["line"] not in by_line or s["secs"] > by_line[s["line"]]["secs"]:
                by_line[s["line"]] = s
        data["decls"][f] = [
            {"line": s["line"], "what": s["what"], "secs": round(s["secs"], 2),
             "name": decl_name(os.path.join(RUN_WT, f), s["line"])}
            for s in sorted(by_line.values(), key=lambda s: s["line"])]
    for m in list(data["modules"]):  # drop modules whose file is gone
        if not os.path.exists(os.path.join(RUN_WT, module_file(m))):
            del data["modules"][m]
    for f in list(data["decls"]):
        if not os.path.exists(os.path.join(RUN_WT, f)):
            del data["decls"][f]
    data["commit"] = rev
    data["date"] = datetime.date.today().isoformat()


# ---- report ----------------------------------------------------------------------------------
def report(data, lines):
    ca_mods = {m: s for m, s in data["modules"].items() if m.startswith("ConAgua")}
    decls = [(f, d) for f, ds in data["decls"].items() if f.startswith("ConAgua/") for d in ds]
    decls.sort(key=lambda x: -x[1]["secs"])
    by_lines = sorted(lines.items(), key=lambda x: -x[1])
    by_time = sorted(ca_mods.items(), key=lambda x: -x[1])
    return dict(
        by_lines=by_lines, by_time=by_time, decls=decls, lines=lines,
        total_lines=sum(lines.values()), total_s=sum(ca_mods.values()),
        vendor_s=sum(s for m, s in data["modules"].items() if not m.startswith("ConAgua")),
        big=[f for f, n in by_lines if n > FILE_LINES_WATCH],
        slow_files=[m for m, s in by_time if s > FILE_SECS_WATCH],
        slow_decls=[x for x in decls if x[1]["secs"] > DECL_SECS_WATCH])


def render(data, r):
    L = []
    w = L.append
    w("# Build statistics\n")
    w(f"Generated by `scripts/buildstats.py` (PLAN.md, \"Build statistics\") at master `{data['commit'][:10]}`, "
      f"{data['date']}. Monitoring only: no merge depends on it. Module times are wall-clock seconds of a "
      f"Lake job (cache off, contended); steps are Lean profiler entries above "
      f"{PROFILER_THRESHOLD_MS / 1000:g} s.\n")
    w(f"Totals: {len(r['lines'])} files under `ConAgua/`, {r['total_lines']} lines; elaboration "
      f"{r['total_s']:.0f} s in ConAgua modules ({r['vendor_s']:.0f} s in vendored ones).\n")
    w("## Watch list\n")
    w(f"Files over {FILE_LINES_WATCH} lines or {FILE_SECS_WATCH} s are split by a lane (statements and "
      f"names stay stable); steps over {DECL_SECS_WATCH} s are investigated by a separate lane, off the "
      f"critical path.\n")
    w(f"**Files over {FILE_LINES_WATCH} lines ({len(r['big'])}):**\n")
    for f in r["big"]:
        w(f"- `{f}`: {r['lines'][f]} lines")
    if not r["big"]:
        w("- none")
    w(f"\n**Files over {FILE_SECS_WATCH} s ({len(r['slow_files'])}):**\n")
    for m, s in r["by_time"]:
        if m in r["slow_files"]:
            w(f"- `{m}`: {s:.0f} s")
    if not r["slow_files"]:
        w("- none")
    w(f"\n**Declarations over {DECL_SECS_WATCH} s ({len(r['slow_decls'])}):**\n")
    for f, d in r["slow_decls"]:
        w(f"- `{f}:{d['line']}` `{d['name']}`: {d['secs']:g} s ({d['what']})")
    if not r["slow_decls"]:
        w("- none")
    w(f"\n## Top {TOP_FILES} files by lines\n")
    w("| lines | file |\n|---:|---|")
    for f, n in r["by_lines"][:TOP_FILES]:
        w(f"| {n} | `{f}` |")
    w(f"\n## Top {TOP_TIMES} files by elaboration time\n")
    w("| seconds | lines | module |\n|---:|---:|---|")
    for m, s in r["by_time"][:TOP_TIMES]:
        w(f"| {s:.1f} | {r['lines'].get(module_file(m), '')} | `{m}` |")
    w(f"\n## Top {TOP_DECLS} slowest declarations\n")
    w("Longest single profiler step starting at that line (a declaration's elaboration, or a tactic or "
      "kernel step inside it).\n")
    w("| seconds | location | declaration | step |\n|---:|---|---|---|")
    for f, d in r["decls"][:TOP_DECLS]:
        w(f"| {d['secs']:g} | `{f}:{d['line']}` | `{d['name']}` | {d['what']} |")
    return "\n".join(L) + "\n"


def write_outputs(data, r):
    open(MD, "w").write(render(data, r))
    new = not os.path.exists(CSV)
    with open(CSV, "a", newline="") as fh:
        wr = csv.writer(fh)
        if new:
            wr.writerow(["date", "commit", "total_lines", "total_elab_s", "files_over", "decls_over"])
        wr.writerow([data["date"], data["commit"][:10], r["total_lines"], round(r["total_s"]),
                     len(set(r["big"]) | {module_file(m) for m in r["slow_files"]}), len(r["slow_decls"])])


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--full", action="store_true", help="re-measure everything")
    ap.add_argument("--lines-only", action="store_true", help="file sizes only, no build")
    ap.add_argument("--write", action="store_true", help="write _tmp/buildstats/buildstats.md, .csv")
    a = ap.parse_args()

    data = load_data()
    if a.lines_only:
        r = report(data, count_lines())
        for f, n in r["by_lines"][:TOP_FILES]:
            print(f"{n:6d}  {f}")
        return
    rev = prepare_worktree(a.full)
    if a.full or not data["commit"]:
        data = {"commit": None, "modules": {}, "decls": {}}
    env = dict(os.environ, LAKE_CACHE_DIR=CACHE_DIR, LAKE_ARTIFACT_CACHE="false", LAKE_RESTORE_ARTIFACTS="false")
    print(f"measuring master {rev[:10]} ({'full' if a.full else 'incremental'}), log: {LOG}", flush=True)
    rc, peak, wall = run_guarded(["taskset", "-c", CPUS, "lake", "build"], env)
    mods, steps, failed = parse_log(open(LOG, errors="replace").read())
    merge(data, mods, steps, rev)
    json.dump(data, open(DATA, "w"), indent=1, sort_keys=True)
    r = report(data, count_lines())
    print(f"build exit {rc}, {wall:.0f} s wall, peak {peak / 2**30:.1f} GB; {len(mods)} modules re-measured"
          + (f"; FAILED: {', '.join(failed)}" if failed else ""))
    print(f"files: {len(r['lines'])}, lines: {r['total_lines']}, elab: {r['total_s']:.0f} s")
    print("top by lines: " + ", ".join(f"{f} {n}" for f, n in r["by_lines"][:5]))
    print("top by time:  " + ", ".join(f"{m} {s:.0f}s" for m, s in r["by_time"][:5]))
    print("slow steps:   " + ", ".join(f"{f}:{d['line']} {d['secs']:g}s" for f, d in r["decls"][:5]))
    if a.write:
        write_outputs(data, r)
        print(f"wrote {MD}, {CSV}")
    if rc != 0:
        sys.exit(f"build failed ({rc})")


if __name__ == "__main__":
    main()
