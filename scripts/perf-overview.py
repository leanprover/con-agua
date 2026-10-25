#!/usr/bin/env python3
"""Measure con-agua against con-ron and regenerate OVERVIEW.md's section 3 ("Performance").

One command reproduces every number of that section:

  scripts/perf-overview.py            measure, write _tmp/perf-overview/<rev>.{md,json}
  scripts/perf-overview.py --write    ... and replace the generated blocks in OVERVIEW.md

It builds the checker of this checkout (`make checker`) and runs it against con-ron's release
binary (`$CON_RON`, default `_tmp/ref/con-ron-integrate/target/release/con-ron`, as
scripts/e2e.py and scripts/bench.py find it; its embedded pins are the same three variants as
`pins.bin`). Three sections, each interleaved (per round the runs in random order, so drifting
load hits both checkers alike), every run with bench.py's timeout:

  init     Lean's `Init` export (`$CA_INIT_EXPORT`, default `_tmp/fixtures/init/init435.ndjson`,
           recipe in scripts/bench.py), one thread (con-ron `--jobs=1`), under `perf stat`:
           instructions:u, cycles (user + kernel), wall, peak RSS; minimum and range over the
           rounds (default 4).
  threads  `Init` at `--jobs` 1, 2, 4, 8, 16 for both checkers (up to 16 cores busy at a time):
           wall (median) and peak RSS (largest `ru_maxrss`) over the rounds (default 3).
  others   the other large inputs, con-agua's default run against con-ron `--jobs=1`: wall
           (median) and peak RSS (default 3 rounds).

OVERVIEW.md holds one block per section between `<!-- perf-overview: begin NAME -->` and
`<!-- perf-overview: end NAME -->`; `--write` replaces the blocks it measured (all three, or
the `--only` one) and nothing else. The wall times need a quiet machine: above `--max-load`
(1-minute load average, default 20) the script warns, and `--write` refuses unless `--force`
(as it does for a checkout with uncommitted changes, whose revision would not name the code).

A full run takes about 10 minutes on a quiet machine. Needs: a C compiler with `#embed` (for
`make`), the con-ron binary, the `Init` export, and `perf` with `perf_event_paranoid` <= 1
(instructions:u, cycles:u, cycles:k).

Usage: scripts/perf-overview.py [--write [--force]] [--rounds N] [--only init|threads|others]
                                [--max-load L] [--dry-run] [--seed S]
"""
import argparse
import datetime
import json
import os
import random
import statistics
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import bench  # noqa: E402  (run under perf stat, verdicts, the Init export, fixtures)
import e2e  # noqa: E402  (the con-ron binary)

OUT = os.path.join(ROOT, "_tmp", "perf-overview")
OVERVIEW = os.path.join(ROOT, "OVERVIEW.md")
CHECKER = os.path.join(ROOT, "checker")
SECTIONS = ["init", "threads", "others"]
DEFAULT_ROUNDS = {"init": 4, "threads": 3, "others": 3}
JOBS = [1, 2, 4, 8, 16]
# (row name in the table, fixture id)
OTHERS = [
    ("app-lam", "arena/good/perf/app-lam.ndjson"),
    ("beta-ladder", "arena/good/perf/beta-ladder.ndjson"),
    ("let-ladder", "arena/good/perf/let-ladder.ndjson"),
    ("eager_open", "e2e/eager_open_nat_control.ndjson"),
    ("c04a", "e2e/complete_c04a_restart_70.ndjson"),
    ("c05b", "e2e/complete_c05b_nest30_pi1000.ndjson"),
    ("c03d", "e2e/complete_c03d_pi_depth_1030.ndjson"),
    ("init-prelude", "arena/good/init-prelude.ndjson"),
]
SYSTEMS = {"con-agua": bench.System("con-agua", "L", None), "con-ron": bench.System("con-ron", "con-ron", None)}


def log(*a):
    print(*a, file=sys.stderr, flush=True)


def cmd(system, path, jobs):
    """argv of one run; `jobs` None is con-agua's default run (con-ron always gets `--jobs`)."""
    if system == "con-agua":
        return [CHECKER] + ([f"--jobs={jobs}"] if jobs else []) + [path]
    return [e2e.CON_RON, f"--jobs={jobs or 1}", path]


class Loads:
    """The 1-minute load average, sampled before every run."""
    def __init__(self):
        self.xs = []

    def sample(self):
        self.xs.append(os.getloadavg()[0])
        return self.xs[-1]

    def range(self):
        return f"{min(self.xs):.0f}–{max(self.xs):.0f}" if self.xs else "?"


def measure(items, rounds, perf, loads, label):
    """items: {key: (system, argv)}; interleaved rounds. Returns {key: [run dict]}."""
    res = {k: [] for k in items}
    t0 = time.time()
    for r in range(rounds):
        keys = list(items)
        random.shuffle(keys)
        for k in keys:
            system, argv = items[k]
            load = loads.sample()
            out, rc, wall, instr, cyc, rss = bench.run(argv, None, None, perf=perf)
            v = SYSTEMS[system].verdict(out, rc)
            if v != "accept":
                log(f"  {label} {k}: verdict {v}")
            res[k].append({"wall": wall, "instr": instr, "cycles": cyc, "rss": rss, "verdict": v,
                           "load": load})
        log(f"{label}: round {r + 1}/{rounds} ({time.time() - t0:.0f} s)")
    return res


def verdict_mark(runs):
    bad = sorted({m["verdict"] for m in runs if m["verdict"] != "accept"})
    return f" **{', '.join(bad)}**" if bad else ""


def mb(b):
    return f"{b / 2**20:.0f} MB"


def rng(xs, fmt):
    """`lo–hi unit` over the rounds (one value if they print alike)."""
    lo, hi = fmt(min(xs)), fmt(max(xs))
    if lo == hi:
        return lo
    (nlo, ulo), (nhi, uhi) = lo.rsplit(" ", 1), hi.rsplit(" ", 1)
    return f"{nlo}–{nhi} {ulo}" if ulo == uhi else f"{lo}–{hi}"


def conditions(meta, sec, what, colon=False):
    s = (f"Master `{meta['rev']}`, {meta['date']}, `scripts/perf-overview.py`: {what}; load "
         f"{meta['load'][sec]} on {meta['cpus']} cores")
    return s + ":" if colon else f"({s}.)"


# ---------------------------------------------------------------- the three sections

def init_items():
    return {s: (s, cmd(s, bench.INIT_EXPORT, 1)) for s in SYSTEMS}


def init_block(res, meta):
    a, b = res["con-agua"], res["con-ron"]

    def col(runs, key):
        return [m[key] for m in runs if m[key]]
    G = lambda x: f"{x / 1e9:.1f} G"  # noqa: E731
    S = lambda x: f"{x:.1f} s"  # noqa: E731
    rows = []
    ia, ib = col(a, "instr"), col(b, "instr")
    ca, cb = col(a, "cycles"), col(b, "cycles")
    ipc = lambda runs: statistics.median(m["instr"] / m["cycles"] for m in runs if m["instr"] and m["cycles"])  # noqa: E731
    if ia and ib:
        rows.append(("instructions (`perf stat`)", G(statistics.median(ia)), G(statistics.median(ib)),
                     f"{statistics.median(ia) / statistics.median(ib):.2f}"))
        rows.append(("instructions per cycle", f"{ipc(a):.2f}", f"{ipc(b):.2f}", ""))
    if ca and cb:
        rows.append(("cycles (user + kernel)", rng(ca, G), rng(cb, G), f"{min(ca) / min(cb):.2f}"))
    wa, wb = col(a, "wall"), col(b, "wall")
    rows.append(("wall", rng(wa, S), rng(wb, S), f"{min(wa) / min(wb):.2f}"))
    ra, rb = col(a, "rss"), col(b, "rss")
    rows.append(("peak RSS", rng(ra, mb), rng(rb, mb), f"{min(ra) / min(rb):.2f}"))
    head = (f"On `Init`, on one thread, con-agua takes **{min(wa) / min(wb):.2f}× con-ron's wall time**")
    if ia and ib:
        head += (f" and executes **{statistics.median(ia) / statistics.median(ib):.2f}× its instructions**"
                 f" ({ipc(a):.2f} instructions per cycle against con-ron's {ipc(b):.2f})")
    lines = [head + ".", "",
             f"| on `Init`, one thread | con-agua{verdict_mark(a)} | con-ron{verdict_mark(b)} | con-agua ÷ con-ron |",
             "|---|---:|---:|---:|"]
    lines += [f"| {r[0]} | {r[1]} | {r[2]} | {r[3]} |" for r in rows]
    n = len(wa)
    lines += ["", conditions(meta, "init", f"{n} interleaved rounds of each checker under `perf stat`; "
                                          "the ranges are over the rounds; the ratios compare the minima, "
                                          "for instructions the medians")]
    return "\n".join(lines), {"wall": min(wa) / min(wb),
                              "instr": statistics.median(ia) / statistics.median(ib) if ia and ib else None}


def threads_items():
    return {f"{s} {j}": (s, cmd(s, bench.INIT_EXPORT, j)) for j in JOBS for s in SYSTEMS}


def threads_block(res, meta):
    wall = {k: statistics.median(m["wall"] for m in v) for k, v in res.items()}
    rss = {k: max(m["rss"] for m in v) for k, v in res.items()}
    lines = ["| `--jobs` | con-agua wall | peak RSS | con-ron wall | peak RSS | wall ÷ |",
             "|---:|---:|---:|---:|---:|---:|"]
    for j in JOBS:
        a, b = f"con-agua {j}", f"con-ron {j}"
        lines.append(f"| {j} | {wall[a]:.2f} s{verdict_mark(res[a])} | {mb(rss[a])} | "
                     f"{wall[b]:.2f} s{verdict_mark(res[b])} | {mb(rss[b])} | {wall[a] / wall[b]:.2f} |")
    sp = lambda s: [f"{wall[f'{s} 1'] / wall[f'{s} {j}']:.1f}×" for j in JOBS[1:]]  # noqa: E731
    js = [str(j) for j in JOBS[1:]]
    a_sp, b_sp = sp("con-agua"), sp("con-ron")
    n = len(next(iter(res.values())))
    lines = [conditions(meta, "threads", f"`Init` at each `--jobs`, {n} interleaved rounds, the median "
                                         "wall time, peak RSS the largest `ru_maxrss`", colon=True),
             ""] + lines
    lines += ["", f"con-agua's speedup over one thread is {', '.join(a_sp[:-1])} and {a_sp[-1]} at "
                  f"{', '.join(js[:-1])} and {js[-1]} threads (con-ron: {', '.join(b_sp)})."]
    return "\n".join(lines), {"j16": (wall["con-agua 16"], wall["con-ron 16"])}


def others_items(paths):
    return {f"{s} {name}": (s, cmd(s, paths[name], None)) for name, _ in OTHERS for s in SYSTEMS}


def others_block(res, meta):
    n = len(next(iter(res.values())))
    lines = [conditions(meta, "others", f"the default run, {n} interleaved rounds, the median wall time "
                                        "and the largest peak RSS", colon=True), "",
             "| input | con-agua | con-ron `--jobs=1` |", "|---|---|---|"]
    for name, _ in OTHERS:
        cells = []
        for s in SYSTEMS:
            v = res[f"{s} {name}"]
            cells.append(f"{statistics.median(m['wall'] for m in v):.2f} s, {mb(max(m['rss'] for m in v))}"
                         f"{verdict_mark(v)}")
        lines.append(f"| {name} | {cells[0]} | {cells[1]} |")
    return "\n".join(lines), {}


# ---------------------------------------------------------------- OVERVIEW.md

def marker(kind, sec):
    return f"<!-- perf-overview: {kind} {sec} -->"


def replace_blocks(text, blocks):
    for sec, body in blocks.items():
        b, e = marker("begin", sec), marker("end", sec)
        if text.count(b) != 1 or text.count(e) != 1 or text.index(b) > text.index(e):
            sys.exit(f"OVERVIEW.md: expected exactly one `{b}` … `{e}` pair")
        i, j = text.index(b) + len(b), text.index(e)
        text = text[:i] + "\n" + body + "\n" + text[j:]
    return text


def git(*a):
    return subprocess.run(["git", "-C", ROOT] + list(a), capture_output=True, text=True).stdout.strip()


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter, epilog=__doc__)
    ap.add_argument("--write", action="store_true", help="replace the generated blocks in OVERVIEW.md")
    ap.add_argument("--force", action="store_true", help="--write despite a high load or a dirty checkout")
    ap.add_argument("--rounds", type=int, default=None,
                    help="rounds for every section (default: init 4, threads 3, others 3)")
    ap.add_argument("--only", choices=SECTIONS, default=None)
    ap.add_argument("--max-load", type=float, default=20.0)
    ap.add_argument("--dry-run", action="store_true", help="print the plan, measure nothing")
    ap.add_argument("--seed", type=int, default=None)
    args = ap.parse_args()
    random.seed(args.seed)
    secs = [args.only] if args.only else SECTIONS
    rounds = {s: args.rounds or DEFAULT_ROUNDS[s] for s in secs}
    rev = git("rev-parse", "--short=8", "HEAD")
    dirty = bool(git("status", "--porcelain", "--untracked-files=no"))
    load0 = os.getloadavg()[0]

    problems = []
    if load0 > args.max_load:
        problems.append(f"load average {load0:.0f} > {args.max_load:.0f}: the wall times will be too high")
    if dirty:
        problems.append(f"uncommitted changes: the numbers are not those of `{rev}`")
    for p in problems:
        log("WARNING: " + p)
    if args.write and problems and not args.force:
        sys.exit("refusing --write (--force to override)")
    for path, what in [(e2e.CON_RON, "con-ron ($CON_RON)"), (bench.INIT_EXPORT, "the Init export ($CA_INIT_EXPORT)")]:
        if not os.path.exists(path):
            sys.exit(f"missing {what}: {path}")
    if args.write and not args.dry_run:
        text = open(OVERVIEW, encoding="utf-8").read()
        replace_blocks(text, {s: "" for s in secs})  # the markers exist, before measuring

    paths = {}
    if "others" in secs:
        have = dict(bench.resolve([fid for _, fid in OTHERS]))
        paths = {name: have[fid] for name, fid in OTHERS}
    plan = {"init": init_items, "threads": threads_items, "others": lambda: others_items(paths)}
    if args.dry_run:
        print(f"perf-overview plan: master `{rev}`{' (dirty)' if dirty else ''}, load {load0:.0f}; "
              f"make checker; con-ron {e2e.CON_RON}")
        for s in secs:
            items = plan[s]()
            print(f"\n{s}: {rounds[s]} interleaved rounds × {len(items)} runs"
                  f"{' under perf stat' if s == 'init' else ''}:")
            for k, (_, argv) in items.items():
                print(f"  {k:24} {' '.join(os.path.relpath(x, ROOT) if x.startswith(ROOT) else x for x in argv)}")
        print(f"\nwrites {os.path.relpath(OUT, ROOT)}/{rev}{'-' + args.only if args.only else ''}.{{md,json}}"
              + (f" and OVERVIEW.md's blocks {', '.join(secs)}" if args.write else ""))
        return

    t0 = time.time()
    r = subprocess.run(["make", "-C", ROOT, "checker"], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"make failed:\n{(r.stdout + r.stderr)[-2000:]}")
    os.makedirs(bench.WORK, exist_ok=True)  # bench.run's perf stat output
    os.makedirs(OUT, exist_ok=True)
    meta = {"rev": rev, "dirty": dirty, "date": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d"),
            "cpus": os.cpu_count(), "load_start": load0, "con_ron": e2e.CON_RON, "init_export": bench.INIT_EXPORT,
            "rounds": rounds, "load": {}}
    raw, blocks, keys = {}, {}, {}
    build = {"init": init_block, "threads": threads_block, "others": others_block}
    for s in secs:
        loads = Loads()
        raw[s] = measure(plan[s](), rounds[s], s == "init", loads, s)
        loads.sample()
        meta["load"][s] = loads.range()
        blocks[s], keys[s] = build[s](raw[s], meta)
    meta["load_end"] = os.getloadavg()[0]
    meta["minutes"] = (time.time() - t0) / 60

    stem = os.path.join(OUT, rev + (f"-{args.only}" if args.only else ""))
    with open(stem + ".md", "w", encoding="utf-8") as fh:
        fh.write(f"# perf-overview, master `{rev}`{' (dirty)' if dirty else ''}, {meta['date']}, load "
                 f"{load0:.0f} → {meta['load_end']:.0f}, {meta['minutes']:.1f} min\n\n")
        for s in secs:
            fh.write(f"{marker('begin', s)}\n{blocks[s]}\n{marker('end', s)}\n\n")
    with open(stem + ".json", "w") as fh:
        json.dump({"meta": meta, "runs": raw}, fh, indent=1)
    print("\n\n".join(blocks[s] for s in secs))
    wrote = [os.path.relpath(stem + ".md", ROOT)]
    if args.write:
        text = open(OVERVIEW, encoding="utf-8").read()
        open(OVERVIEW, "w", encoding="utf-8").write(replace_blocks(text, blocks))
        wrote.append("OVERVIEW.md")

    summary = [f"perf-overview `{rev}`"]
    if "init" in keys:
        k = keys["init"]
        summary.append(f"Init 1 thread: wall {k['wall']:.2f}×" + (f", instructions {k['instr']:.2f}×" if k["instr"] else ""))
    if "threads" in keys:
        a, b = keys["threads"]["j16"]
        summary.append(f"16 threads: {a:.2f} s vs {b:.2f} s")
    summary += [f"load {load0:.0f} → {meta['load_end']:.0f}", f"{meta['minutes']:.1f} min", "wrote " + ", ".join(wrote)]
    print("\n" + "; ".join(summary))


if __name__ == "__main__":
    main()
