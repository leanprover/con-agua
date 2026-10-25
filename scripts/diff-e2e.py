#!/usr/bin/env python3
"""The end-to-end differential of the shipped binary: `./checker FILE.ndjson` on every fixture of
con-leche's test suite that has a pinned expectation, against that expectation. No Lean needed.

    scripts/diff-e2e.py [--bin PATH] [--jobs N] [--parallel P] [--timeout S] [--tests DIR] [--only REGEX]

The fixtures and the expected exit codes are con-leche's `tests/` at the revision `vendor/UPSTREAM`
pins: `tests/e2e-expected.txt` ("<exit> <fixture>" under `tests/e2e/`, gzipped or not) and
`tests/arena-expected.txt` ("<exit> <path>" inside `tests/arena/lean-arena-tests.tar.gz`).
con-leche's exit codes are 0 accept, 1 reject, 2 decline, 3 error, 124 a deliberate non-terminating
input. `--tests` names that directory (default `$CON_LECHE_TESTS`, else `_tmp/ref/con-leche/tests`);
it is checked against `vendor/UPSTREAM` when it is a git checkout.

The checker exits 0 only on accept, 1 on a reject, 2 on a decline, 3 otherwise (`main.c`'s usage
text). Its reject/decline labels follow con-ron's twin, not con-leche, so a fixture is compared on
accept versus not-accept, and a reject/decline that differs from con-leche's is only counted
(`kind differs`):
  agree         con-leche accepts and the checker accepts, or con-leche does not accept and the
                checker exits 1, 2 or 3 (a run still going after T_LOOP seconds counts here when
                con-leche's expectation is the non-terminating 124)
  UNSOUND       the checker accepts where con-leche does not
  INCOMPLETE    con-leche accepts and the checker exits 1, 2 or 3
  CRASH         a signal, or an exit code the checker never uses
  TIMEOUT       the run did not finish in `--timeout` seconds (and 124 was not expected)
The run is green when every fixture agrees; the exit code is 0 then, 1 otherwise (2: usage, missing
fixtures).

`--jobs N` is passed to the checker (`--jobs=N`, the threaded mode; 1, the default, passes nothing
and runs the sequential path). `--parallel P` is how many fixtures run at once (default 4).
"""
import argparse
import concurrent.futures as cf
import gzip
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
T_LOOP = 10  # seconds for a fixture whose expected verdict is 124 (a non-terminating input)


def upstream_rev(repo):
    for line in open(os.path.join(ROOT, "vendor", "UPSTREAM"), encoding="utf-8"):
        w = line.split()
        if len(w) >= 2 and w[0] == repo:
            return w[1]
    sys.exit(f"diff-e2e: vendor/UPSTREAM names no {repo} revision")


def expectations(path):
    out = []
    for line in open(path, encoding="utf-8"):
        w = line.split()
        if len(w) >= 2 and not w[0].startswith("#") and w[0].isdigit():
            out.append((int(w[0]), w[1]))
    return out


def fixtures(tests, work):
    """[(id, path, expected exit code)] for every fixture with an expectation."""
    out, missing = [], []
    for want, rel in expectations(os.path.join(tests, "e2e-expected.txt")):
        src = os.path.join(tests, "e2e", rel)
        if not os.path.exists(src) and os.path.exists(src + ".gz"):
            dst = os.path.join(work, "e2e", rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            with gzip.open(src + ".gz") as fi, open(dst, "wb") as fo:
                shutil.copyfileobj(fi, fo)
            src = dst
        (out if os.path.exists(src) else missing).append(("e2e/" + rel, src, want))
    arena = os.path.join(work, "arena")
    with tarfile.open(os.path.join(tests, "arena", "lean-arena-tests.tar.gz")) as t:
        t.extractall(arena, filter="data")
    for want, rel in expectations(os.path.join(tests, "arena-expected.txt")):
        src = os.path.join(arena, rel)
        (out if os.path.exists(src) else missing).append(("arena/" + rel, src, want))
    return out, missing


def run(binary, jobs, timeout, fid, path, want):
    """Run one fixture; the verdict class, the last stdout line, wall seconds and peak RSS (MB)."""
    cmd = [binary] + ([f"--jobs={jobs}"] if jobs > 1 else []) + [path]
    if want == 124:  # con-leche's verdict is the timeout itself: no need to wait the full budget
        timeout = min(timeout, T_LOOP)
    t0 = time.monotonic()
    with tempfile.TemporaryFile() as fo, tempfile.TemporaryFile() as fe:
        p = subprocess.Popen(cmd, stdout=fo, stderr=fe)
        fired = threading.Event()

        def kill():
            fired.set()
            p.kill()
        timer = threading.Timer(timeout, kill)
        timer.start()
        _, status, ru = os.wait4(p.pid, 0)
        timer.cancel()
        timed_out = fired.is_set()
        p.returncode = os.waitstatus_to_exitcode(status)
        fo.seek(0)
        fe.seek(0)
        stdout, stderr = fo.read().decode(errors="replace"), fe.read().decode(errors="replace")
    dt, mb = time.monotonic() - t0, ru.ru_maxrss // 1024
    rc = None if timed_out else p.returncode
    out = "timeout" if rc is None else (stdout.strip().splitlines() or [""])[-1]
    if stderr.strip():
        out += f" [stderr: {stderr.strip()[:200]}]"
    if rc is None:
        cls = "agree" if want == 124 else "TIMEOUT"
    elif rc == 0:
        cls = "agree" if want == 0 else "UNSOUND"
    elif rc in (1, 2, 3):
        cls = "INCOMPLETE" if want == 0 else "agree"
    else:
        cls = "CRASH"
    return fid, want, rc, out, cls, dt, mb


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--bin", default=os.path.join(ROOT, "checker"))
    ap.add_argument("--jobs", type=int, default=1, help="the checker's --jobs=N (1: sequential)")
    ap.add_argument("--parallel", type=int, default=4, help="fixtures run at once")
    ap.add_argument("--timeout", type=float, default=300.0, help="seconds per run")
    ap.add_argument("--tests", default=os.environ.get("CON_LECHE_TESTS",
                                                      os.path.join(ROOT, "_tmp", "ref", "con-leche", "tests")))
    ap.add_argument("--only", default=None, help="regex on fixture ids")
    ap.add_argument("--log", default=None, help="write one line per fixture here")
    a = ap.parse_args()

    if not os.access(a.bin, os.X_OK):
        print(f"diff-e2e: {a.bin} is not executable (run make)", file=sys.stderr)
        return 2
    if not os.path.isfile(os.path.join(a.tests, "e2e-expected.txt")):
        print(f"diff-e2e: no con-leche tests at {a.tests} (set --tests or CON_LECHE_TESTS)", file=sys.stderr)
        return 2
    want_rev = upstream_rev("con-leche")
    r = subprocess.run(["git", "-C", a.tests, "rev-parse", "HEAD"], capture_output=True, text=True)
    if r.returncode == 0 and r.stdout.strip() != want_rev:
        print(f"diff-e2e: {a.tests} is at con-leche {r.stdout.strip()[:12]}, vendor/UPSTREAM pins "
              f"{want_rev[:12]}", file=sys.stderr)
        return 2

    with tempfile.TemporaryDirectory(prefix="diff-e2e-") as work:
        fx, missing = fixtures(a.tests, work)
        if missing:
            for fid, _, _ in missing:
                print(f"MISSING {fid}")
            return 2
        if a.only:
            fx = [f for f in fx if re.search(a.only, f[0])]
        # largest first, so the long runs do not form the tail
        fx.sort(key=lambda f: -os.path.getsize(f[1]))
        t0 = time.monotonic()
        results = []
        with cf.ThreadPoolExecutor(max_workers=a.parallel) as ex:
            futs = [ex.submit(run, a.bin, a.jobs, a.timeout, *f) for f in fx]
            for fut in cf.as_completed(futs):
                res = fut.result()
                results.append(res)
                fid, want, rc, out, cls, dt, mb = res
                if cls != "agree":
                    print(f"{cls:<10} {fid}: con-leche expects {want}, checker exit {rc} ({out})", flush=True)
        wall = time.monotonic() - t0

    results.sort()
    if a.log:
        with open(a.log, "w", encoding="utf-8") as fh:
            for fid, want, rc, out, cls, dt, mb in results:
                fh.write(f"{cls}\t{fid}\texpect {want}\texit {rc}\t{dt:.2f}s\t{mb} MB\t{out}\n")
    counts = {}
    for r_ in results:
        counts[r_[4]] = counts.get(r_[4], 0) + 1
    acc = sum(1 for r_ in results if r_[4] == "agree" and r_[1] == 0)
    print(f"\ndiff-e2e (checker {'--jobs=%d' % a.jobs if a.jobs > 1 else 'sequential'}, "
          f"con-leche {want_rev[:12]}): {len(results)} fixtures, {wall:.0f} s")
    print(f"  agree       {counts.get('agree', 0)} ({acc} accepted, {counts.get('agree', 0) - acc} not accepted)")
    kind = sum(1 for r_ in results if r_[4] == "agree" and r_[2] in (1, 2) and r_[1] in (1, 2)
               and r_[2] != r_[1])
    print(f"  (kind differs: {kind}, the checker's 1/2 against con-leche's 2/1)")
    for c in ("UNSOUND", "INCOMPLETE", "CRASH", "TIMEOUT"):
        print(f"  {c:<11} {counts.get(c, 0)}")
    slow = sorted(results, key=lambda r_: -r_[5])[:3]
    print("  slowest     " + ", ".join(f"{r_[0]} {r_[5]:.1f}s" for r_ in slow))
    big = sorted(results, key=lambda r_: -r_[6])[:3]
    print("  largest     " + ", ".join(f"{r_[0]} {r_[6]} MB" for r_ in big))
    return 0 if counts.get("agree", 0) == len(results) else 1


if __name__ == "__main__":
    sys.exit(main())
