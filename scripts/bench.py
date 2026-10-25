#!/usr/bin/env python3
"""Benchmark harness: the compiled L checker against con-ron and e2e-ref (lane `compopt`).

Runs every *system* (one or more compiled L binaries, `con-ron --jobs=1`, `e2e-ref`) on a fixture
set with INTERLEAVED repetitions: per round, the fixtures in random order and per fixture the
systems in random order, so that drifting machine load hits every system alike. Reports per
fixture and as geometric means (over the fixtures every system accepts):
* `instructions:u` (`perf stat`; nearly deterministic, the primary measure on this shared machine),
* cycles (`cycles:u` + `cycles:k`, median: less sensitive to preemption on a loaded machine than wall),
* wall time: median and spread ((max - min) / median) over the rounds,
* peak RSS (max over the rounds).

A warm-up round (not counted) fixes each system's verdict; L binaries that disagree on a
verdict are flagged (`MISMATCH`), so comparing a candidate compiler against the baseline also
checks it.

Systems:
  --bin NAME=PATH     a compiled L binary (`cc -std=gnu23 -O2 main.c X.s`: `X FILE`); repeatable;
                      the FIRST L binary is the baseline the ratios refer to. Default: `L=<this
                      checkout's compiled check>` (printed by `checker.s`'s generator
                      `ConAgua/Checker/AsmEmit.lean`, as `scripts/e2e.py` does).
  --asm NAME=PATH.s   as --bin, but assemble the `.s` file first (with main.c).
  --no-conron / --no-ref   leave out con-ron / e2e-ref.

Fixtures: `--set quick|default|full|init` (below), `--only REGEX` (filters the set; with `--set all`,
every e2e fixture), or explicit ids/paths as positional arguments (an id is `e2e/NAME.ndjson` or
`arena/…`; any existing path also works).

`--reps 0`: only the warm-up (verdicts), printing the fixtures where the L binaries disagree; with
`--set all --no-conron --no-ref` this is the e2e agreement check of a candidate against the
baseline.

Usage: scripts/bench.py [--set S] [--reps N] [--cpus LIST] [--bin NAME=PATH]… [--json OUT] [FIXTURE…]

Every run has a timeout; `--cpus` pins every run with `taskset -c LIST` (pick a few
idle cores; the runs are sequential, so one or two cores suffice).
"""
import argparse
import json
import math
import os
import random
import re
import statistics
import subprocess
import sys
import tempfile
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import e2e  # noqa: E402  (fixture lists, the reference verdicts, the con-ron binary)

WORK = os.path.join(ROOT, "_tmp", "bench", os.path.basename(ROOT))
BIN = os.path.join(ROOT, ".lake", "build", "bin")
TIMEOUT = 600

# Fixtures every system accepts (the 2026-10-23 e2e run): small/medium ones measure the fixed
# cost (prelude, pins) and the frontend; the big ones the kernel.
QUICK = [
    "e2e/irrel_commit.ndjson",             # 69 KB, ~120M instructions: mostly the fixed cost
    "e2e/delta_chain.ndjson",
    "e2e/nested_struct_proj.ndjson",
    "e2e/mutual_struct_proj.ndjson",
    "arena/good/perf/shift-cascade.ndjson",
    "e2e/dag_tower_unfold.ndjson",
    "e2e/inmodel_nested.ndjson",
    "e2e/pinstall_ok.ndjson",
]
DEFAULT = QUICK + [
    "e2e/long_line_5mib.ndjson",           # 5 MB, the scanner
    "e2e/complete_c03d_pi_depth_1030.ndjson",
    "arena/good/perf/let-ladder.ndjson",
    "arena/good/perf/beta-ladder.ndjson",
    "e2e/complete_c04a_restart_70.ndjson",  # 9 MB, ~43G instructions
]
# where con-ron or e2e-ref are slow (e2e-ref up to ~130G instructions)
FULL = DEFAULT + [
    # L ~1.47T instructions, ~60 s: 98% in `rf_find` (the banked `rf` memo's bank is shifted out
    # of the hash)
    "e2e/complete_c05b_nest30_pi1000.ndjson",
    "arena/good/perf/app-lam.ndjson",
    "e2e/eager_open_nat_control.ndjson",
]
# The headline: Lean's `Init`, exported by lean4export 5a9a355 at v4.35.0 (the toolchain of the
# 1-variant pin buffer; recipe: clone lean4export at 5a9a355, `lake build`, `lake env
# .lake/build/bin/lean4export Init > init435.ndjson`; 346 MB, not in the repository: kept in
# _tmp/fixtures/init/, never delete),
# and the arena's `init-prelude`.
INIT_EXPORT = os.environ.get("CA_INIT_EXPORT", os.path.join(ROOT, "_tmp", "fixtures", "init", "init435.ndjson"))
INIT = ["arena/good/init-prelude.ndjson", INIT_EXPORT]
FULL += INIT
SETS = {"quick": QUICK, "default": DEFAULT, "full": FULL, "init": INIT}


def log(*a):
    print(*a, file=sys.stderr, flush=True)


def run(cmd, env=None, cpus=None, perf=True):
    """(stdout, exit code, wall seconds, instructions:u or None, cycles or None, peak RSS in bytes);
    a timeout gives exit code None. With `perf`, under `perf stat`: the wall time then includes its
    own small start-up cost, the same for every system, and the peak RSS is the larger of perf's and
    the command's (`wait4`'s `ru_maxrss` covers the children perf waited for)."""
    pre = ["taskset", "-c", cpus] if cpus else []
    statf = os.path.join(WORK, f"perf.{os.getpid()}")
    if perf:
        pre += ["perf", "stat", "-x,", "-e", "instructions:u,cycles:u,cycles:k", "-o", statf, "--"]
    with tempfile.TemporaryFile() as outf:
        t0 = time.perf_counter()
        p = subprocess.Popen(pre + cmd, stdout=outf, stderr=subprocess.DEVNULL, env=env,
                             start_new_session=True)
        killed = []

        def kill():
            killed.append(1)
            try:
                os.killpg(p.pid, 9)
            except ProcessLookupError:
                pass
        timer = threading.Timer(TIMEOUT, kill)
        timer.start()
        _, status, ru = os.wait4(p.pid, 0)
        wall = time.perf_counter() - t0
        timer.cancel()
        p.returncode = rc = None if killed else os.waitstatus_to_exitcode(status)
        outf.seek(0)
        out = outf.read()
    instr, cyc = None, 0
    if perf and os.path.exists(statf):
        for line in open(statf).read().splitlines():
            f = line.split(",")
            if len(f) > 2 and f[2].startswith("instructions") and f[0].isdigit():
                instr = int(f[0])
            if len(f) > 2 and f[2].startswith("cycles") and f[0].isdigit():
                cyc += int(f[0])
        os.remove(statf)
    return out.decode(errors="replace").strip(), rc, wall, instr, cyc or None, ru.ru_maxrss * 1024


def peak_rss(cmd, env, cpus):
    """Peak RSS of one (extra) run, without `perf stat`."""
    return run(cmd, env, cpus, perf=False)[5]


class System:
    def __init__(self, name, kind, cmd):
        self.name, self.kind, self.cmd = name, kind, cmd  # cmd: fixture path -> argv

    def verdict(self, out, rc):
        if rc is None:
            return "timeout"
        if self.kind == "L":
            return {"accept": "accept", "ok 1": "reject-front", "exhausted": "exhausted",
                    "error": "error"}.get(out, "other " + out[:40])
        if self.kind == "con-ron":
            return {0: "accept", 1: "reject", 2: "decline", 3: "error"}.get(rc, f"exit {rc}")
        return e2e.ref_verdict(out, "ok")[0]


def compiled_check(work):
    """This checkout's compiled `check`, as scripts/e2e.py builds it (the shipped code)."""
    s = os.path.join(work, "check.s")
    ok, msg = e2e.checker_asm(s)
    if not ok:
        sys.exit(f"AsmEmit failed: {msg}")
    print(msg, file=sys.stderr)
    return assemble(s)


def assemble(s):
    exe = s[:-2] + ".bin"
    c = subprocess.run(["cc", "-std=gnu23", "-O2", "-pthread", "-o", exe, os.path.join(ROOT, "main.c"), s],
                       capture_output=True, text=True)
    if c.returncode != 0:
        sys.exit(f"cc failed: {c.stderr[-2000:]}")
    return exe


def resolve(ids):
    if not ids:
        return []
    have = {f[0]: f[1] for f in e2e.fixtures()}
    out = []
    for i in ids:
        if i in have:
            out.append((i, have[i]))
        elif os.path.exists(i):
            out.append((os.path.basename(i), os.path.realpath(i)))
        else:
            sys.exit(f"unknown fixture {i}")
    return out


def gmean(xs):
    xs = [x for x in xs if x]
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else float("nan")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("fixtures", nargs="*")
    ap.add_argument("--set", default="default", choices=list(SETS) + ["all"])
    ap.add_argument("--only", default=None)
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--cpus", default=None, help="taskset CPU list for every run, e.g. 90-91")
    ap.add_argument("--bin", action="append", default=[], metavar="NAME=PATH")
    ap.add_argument("--asm", action="append", default=[], metavar="NAME=PATH.s")
    ap.add_argument("--no-conron", action="store_true")
    ap.add_argument("--no-ref", action="store_true")
    ap.add_argument("--no-wall", action="store_true", help="one counted round, instructions only")
    ap.add_argument("--json", default=None, help="write all measurements here")
    ap.add_argument("--seed", type=int, default=None)
    ap.add_argument("--no-build", action="store_true", help="do not build the tools it needs (e2e-ref, e2e-l)")
    args = ap.parse_args()
    random.seed(args.seed)
    os.makedirs(WORK, exist_ok=True)
    os.makedirs(e2e.WORK, exist_ok=True)
    if not args.no_build:
        e2e.lake("build", "ConAgua.E2E.Check", "ConAgua.Checker.Prog", "ConAgua.Compiler.Abi", "ConRon.Dump.Pins", "e2e-l",
                 "e2e-ref")  # fixtures are unpacked there (shared with scripts/e2e.py)

    ids = args.fixtures or ([f[0] for f in e2e.fixtures()] if args.set == "all" else SETS[args.set])
    if args.only:
        ids = [i for i in ids if re.search(args.only, i)]
    fx = resolve(ids)

    # pin data: the compiled checker reads byte array 1 (DESIGN.md lane `romload`)
    # the L binaries embed `pins.bin` (all of con-leche's pin variants); the references run at the
    # same pin list
    npins = e2e.PIN_VARIANTS
    cpins = os.path.join(WORK, f"pins{npins}.con-ron-pins")
    if not args.no_conron and not os.path.exists(cpins):
        e2e.write_conron_pins(cpins, npins)

    systems = []
    bins = ([("L", *b.split("=", 1)) for b in args.bin] +
            [("L", n, assemble(os.path.abspath(p))) for n, p in (a.split("=", 1) for a in args.asm)])
    if not bins:
        bins = [("L", "L", compiled_check(WORK))]
    for kind, name, path in bins:
        path = os.path.abspath(path)
        systems.append(System(name, kind, lambda f, path=path: [path, f]))
    if not args.no_conron:
        if not os.path.exists(e2e.CON_RON):
            sys.exit(f"no con-ron at {e2e.CON_RON} (--no-conron to skip)")
        systems.append(System("con-ron", "con-ron", lambda f: [e2e.CON_RON, "--jobs=1", "--pins", cpins, f]))
    if not args.no_ref:
        systems.append(System("e2e-ref", "ref", lambda f: [os.path.join(BIN, "e2e-ref"), f, f"--pins={npins}"]))

    # warm-up: verdicts
    verdict = {}
    for fid, path in fx:
        for s in systems:
            out, rc, *_ = run(s.cmd(path), None, args.cpus)
            verdict[(fid, s.name)] = s.verdict(out, rc)
        log(f"warm-up {fid}: " + ", ".join(f"{s.name} {verdict[(fid, s.name)]}" for s in systems))

    if args.reps == 0:
        # verdicts only: the warm-up's L verdicts, and every fixture where the L binaries differ
        bad = [fid for fid, _ in fx if len({verdict[(fid, s.name)] for s in systems if s.kind == "L"}) > 1]
        print(f"{len(fx)} fixtures, {len(bad)} where the L binaries disagree")
        for fid in bad:
            print(f"MISMATCH `{fid}`: " + ", ".join(f"{s.name} {verdict[(fid, s.name)]}" for s in systems))
        sys.exit(1 if bad else 0)
    meas = {(fid, s.name): [] for fid, _ in fx for s in systems}
    rounds = 1 if args.no_wall else args.reps
    t0 = time.time()
    for rnd in range(rounds):
        order = list(fx)
        random.shuffle(order)
        for fid, path in order:
            ss = list(systems)
            random.shuffle(ss)
            for s in ss:
                out, rc, wall, instr, cyc, _ = run(s.cmd(path), None, args.cpus)
                v = s.verdict(out, rc)
                if v != verdict[(fid, s.name)]:
                    log(f"  {fid} {s.name}: verdict {v} != warm-up {verdict[(fid, s.name)]}")
                meas[(fid, s.name)].append({"wall": wall, "instr": instr, "cycles": cyc, "verdict": v})
        log(f"round {rnd + 1}/{rounds} ({time.time() - t0:.0f} s)")
    rss = {}
    for fid, path in fx:
        for s in systems:
            rss[(fid, s.name)] = peak_rss(s.cmd(path), None, args.cpus)

    # report
    names = [s.name for s in systems]
    base = names[0]
    def stats(fid, n):
        ms = meas[(fid, n)]
        ws = [m["wall"] for m in ms]
        ins = [m["instr"] for m in ms if m["instr"] is not None]
        cys = [m["cycles"] for m in ms if m.get("cycles")]
        med = statistics.median(ws)
        return {"wall": med, "spread": (max(ws) - min(ws)) / med if med else 0,
                "instr": statistics.median(ins) if ins else None,
                "cycles": statistics.median(cys) if cys else None, "rss": rss[(fid, n)],
                "verdict": verdict[(fid, n)]}
    st = {(fid, n): stats(fid, n) for fid, _ in fx for n in names}
    lv = {verdict[(fid, s.name)] for fid, _ in fx for s in systems if s.kind == "L"}
    lines = [f"# bench: {len(fx)} fixtures, {rounds} rounds, systems {', '.join(names)} (baseline {base}); "
             f"cpus {args.cpus or 'any'}; load {os.getloadavg()[0]:.0f}", ""]
    hdr = "| fixture | " + " | ".join(f"{n} instr | {n} wall (spread) | {n} RSS" for n in names) + " |"
    lines += [hdr, "|" + "---|" * (1 + 3 * len(names))]
    for fid, _ in fx:
        cells = [f"`{fid}`"]
        for n in names:
            x = st[(fid, n)]
            v = "" if x["verdict"] == "accept" else f" **{x['verdict']}**"
            cells += [f"{x['instr'] / 1e6:,.0f}M{v}" if x["instr"] else "–",
                      f"{x['wall']:.3f} s ({100 * x['spread']:.0f}%)",
                      f"{x['rss'] / 2**20:,.0f} MB" if x["rss"] else "–"]
        lines.append("| " + " | ".join(cells) + " |")
        lvs = {verdict[(fid, s.name)] for s in systems if s.kind == "L"}
        if len(lvs) > 1:
            lines.append(f"| MISMATCH between L binaries on `{fid}`: {lvs} |")
    ok = [fid for fid, _ in fx if all(verdict[(fid, n)] == "accept" for n in names)]
    lines += ["", f"Geometric means of the ratio to `{base}` over the {len(ok)} fixtures every system accepts:", "",
              "| system | instructions | cycles (user+kernel, median) | wall |", "|---|---:|---:|---:|"]
    for n in names:
        gi = gmean([st[(f, n)]["instr"] / st[(f, base)]["instr"] for f in ok
                    if st[(f, n)]["instr"] and st[(f, base)]["instr"]])
        gw = gmean([st[(f, n)]["wall"] / st[(f, base)]["wall"] for f in ok])
        gc = gmean([st[(f, n)]["cycles"] / st[(f, base)]["cycles"] for f in ok
                    if st[(f, n)]["cycles"] and st[(f, base)]["cycles"]])
        lines.append(f"| {n} | {gi:.3f} | {gc:.3f} | {gw:.3f} |")
    print("\n".join(lines))
    if args.json:
        with open(args.json, "w") as fh:
            json.dump({"systems": names,
                       "fixtures": {fid: {n: {"stats": st[(fid, n)], "runs": meas[(fid, n)]} for n in names}
                                    for fid, _ in fx}}, fh, indent=1)


if __name__ == "__main__":
    main()
