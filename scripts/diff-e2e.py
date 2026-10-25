#!/usr/bin/env python3
"""The end-to-end differential of the shipped binary: `./checker FILE.ndjson` on every fixture of
con-leche's test suite that has a pinned expectation, against that expectation. No Lean needed.

    scripts/diff-e2e.py [--bin PATH] [--jobs N] [--parallel P] [--timeout S] [--tests DIR] [--only REGEX]
                        [--refs] [--no-cache]

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

`--refs` also runs con-ron (`--jobs=1`) and `e2e-ref` on every fixture and reports REFDIFF where either
one's accept/not-accept differs from the checker's, or where the checker rejects or declines and con-ron
does not say the same (the full differential of PLAN.md's "Verdict checks");
it replaces `bench.py --reps 0`, which no longer checks verdicts. The references' verdicts depend only
on the fixture and the reference binary, so they are cached in `_tmp/bench/verdict-cache/`, keyed by the
fixture's content hash and the hash of the reference binary (and, for con-ron, its pins file): after the
first run, `--refs` costs about as much as the plain run, until a twin sync changes a binary. Timeouts are
never cached. A fixture expecting 124 gets T_LOOP seconds on every system.
(`--no-cache` ignores the cache.) Needs the references built as `scripts/bench.py` does (`.lake/build/bin/e2e-ref`,
con-ron at `$CON_RON` or `_tmp/ref/con-ron-integrate/target/release/con-ron`).

`--jobs N` is passed to the checker (`--jobs=N`, the threaded mode; 1, the default, passes nothing
and runs the sequential path). `--parallel P` is how many fixtures run at once (default 4).
"""
import argparse
import concurrent.futures as cf
import gzip
import hashlib
import json
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
sys.path.insert(0, os.path.join(ROOT, "scripts"))
# Fixtures that genuinely need longer than the default `--timeout` under load (seconds, checker and
# references): stack_fuel_offset takes ~80 s in the checker and over 120 s in e2e-ref (5.4 GB).
ALLOW = {"e2e/stack_fuel_offset.ndjson": 900}
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
    timeout = max(timeout, ALLOW.get(fid, 0))
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


def file_hash(path):
    h = hashlib.sha1()
    with open(path, "rb") as f:
        while b := f.read(1 << 20):
            h.update(b)
    return h.hexdigest()


class Refs:
    """con-ron and e2e-ref as verdict sources, with the on-disk verdict cache (see the docstring)."""

    def __init__(self, use_cache):
        import e2e  # noqa: PLC0415  (only `--refs` needs it)
        self.e2e = e2e
        npins = e2e.PIN_VARIANTS
        self.ref_bin = os.path.join(ROOT, ".lake", "build", "bin", "e2e-ref")
        for b in (e2e.CON_RON, self.ref_bin):
            if not os.access(b, os.X_OK):
                sys.exit(f"diff-e2e --refs: {b} is not built (scripts/bench.py builds e2e-ref; con-ron: DESIGN.md, lane integrate)")
        self.pins = os.path.join(ROOT, "_tmp", "bench", os.path.basename(ROOT), f"pins{npins}.con-ron-pins")
        if not os.path.exists(self.pins):
            os.makedirs(os.path.dirname(self.pins), exist_ok=True)
            e2e.write_conron_pins(self.pins, npins)
        self.npins = npins
        self.ident = {"con-ron": f"con-ron-{file_hash(e2e.CON_RON)[:16]}-{file_hash(self.pins)[:8]}",
                      "e2e-ref": f"e2e-ref-{file_hash(self.ref_bin)[:16]}-p{npins}"}
        self.dir = os.path.join(ROOT, "_tmp", "bench", "verdict-cache")
        self.use_cache, self.data, self.lock, self.dirty, self.hits = use_cache, {}, threading.Lock(), set(), 0
        for k, ident in self.ident.items():
            try:
                self.data[k] = json.load(open(os.path.join(self.dir, ident + ".json"))) if use_cache else {}
            except (OSError, ValueError):
                self.data[k] = {}

    def cmd(self, name, path):
        if name == "con-ron":
            return [self.e2e.CON_RON, "--jobs=1", "--pins", self.pins, path]
        return [self.ref_bin, path, f"--pins={self.npins}"]

    def verdict(self, name, fid, path, want, timeout):
        """'accept', 'reject', 'decline', 'error', 'timeout', or something odd."""
        fh = file_hash(path)
        with self.lock:
            v = self.data[name].get(fh)
            if v is not None:
                self.hits += 1
                return v
        timeout = max(timeout, ALLOW.get(fid, 0))
        if want == 124:
            timeout = min(timeout, T_LOOP)
        p = subprocess.Popen(self.cmd(name, path), stdout=subprocess.PIPE,
                             stderr=subprocess.DEVNULL, start_new_session=True)
        try:
            out, _ = p.communicate(timeout=timeout)
            rc = p.returncode
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, 9)
            p.communicate()
            return "timeout"
        out = out.decode(errors="replace").strip()
        if name == "con-ron":
            v = {0: "accept", 1: "reject", 2: "decline", 3: "error"}.get(rc, f"exit {rc}")
        else:
            v = self.e2e.ref_verdict(out, "ok")[0]
        with self.lock:
            self.data[name][fh] = v
            self.dirty.add(name)
        return v

    def save(self):
        os.makedirs(self.dir, exist_ok=True)
        for name in self.dirty:
            f = os.path.join(self.dir, self.ident[name] + ".json")
            json.dump(self.data[name], open(f"{f}.{os.getpid()}", "w"))
            os.replace(f"{f}.{os.getpid()}", f)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--bin", default=os.path.join(ROOT, "checker"))
    ap.add_argument("--jobs", type=int, default=1, help="the checker's --jobs=N (1: sequential)")
    ap.add_argument("--parallel", type=int, default=4, help="fixtures run at once")
    ap.add_argument("--timeout", type=float, default=300.0, help="seconds per run")
    ap.add_argument("--tests", default=os.environ.get("CON_LECHE_TESTS",
                                                      os.path.join(ROOT, "_tmp", "ref", "con-leche", "tests")))
    ap.add_argument("--only", default=None, help="regex on fixture ids")
    ap.add_argument("--refs", action="store_true", help="also compare with con-ron and e2e-ref (cached)")
    ap.add_argument("--no-cache", action="store_true", help="with --refs: ignore the cached reference verdicts")
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

    refs = Refs(not a.no_cache) if a.refs else None
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
            def one(f):
                res = run(a.bin, a.jobs, a.timeout, *f)
                if refs is None:
                    return res
                fid, want, rc, out, cls, dt, mb = res
                acc = rc == 0
                vs = {n: refs.verdict(n, fid, f[1], want, a.timeout) for n in ("con-ron", "e2e-ref")}
                bad = [f"{n} {v}" for n, v in vs.items() if (v == "accept") != acc]
                # the checker's reject/decline must be con-ron's (its labels follow the twin)
                if rc in (1, 2) and vs["con-ron"] != {1: "reject", 2: "decline"}[rc]:
                    bad.append(f"con-ron {vs['con-ron']} (checker {'reject' if rc == 1 else 'decline'})")
                if want != 124:
                    bad = [b for b in bad if not b.endswith(" timeout")] + \
                          [f"{n} TIMEOUT" for n, v in vs.items() if v == "timeout"]
                if bad and cls == "agree":
                    cls = "REFDIFF"
                    out += " | refs: " + ", ".join(bad)
                elif bad:
                    out += " | refs: " + ", ".join(bad)
                return fid, want, rc, out, cls, dt, mb

            futs = [ex.submit(one, f) for f in fx]
            for fut in cf.as_completed(futs):
                res = fut.result()
                results.append(res)
                fid, want, rc, out, cls, dt, mb = res
                if cls != "agree":
                    print(f"{cls:<10} {fid}: con-leche expects {want}, checker exit {rc} ({out})", flush=True)
        if refs:
            refs.save()
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
    if refs:
        print(f"  references  con-ron + e2e-ref, {refs.hits} of {2 * len(results)} verdicts from the cache")
    for c in ("UNSOUND", "INCOMPLETE", "CRASH", "TIMEOUT") + (("REFDIFF",) if refs else ()):
        print(f"  {c:<11} {counts.get(c, 0)}")
    slow = sorted(results, key=lambda r_: -r_[5])[:3]
    print("  slowest     " + ", ".join(f"{r_[0]} {r_[5]:.1f}s" for r_ in slow))
    big = sorted(results, key=lambda r_: -r_[6])[:3]
    print("  largest     " + ", ".join(f"{r_[0]} {r_[6]} MB" for r_ in big))
    return 0 if counts.get("agree", 0) == len(results) else 1


if __name__ == "__main__":
    sys.exit(main())
