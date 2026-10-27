#!/usr/bin/env python3
"""The merge queue (PLAN.md, "Landing"): lanes submit gated branches, one queue agent lands them by
running short scripted steps. The entry points are the wrappers:

    scripts/submit.sh <worktree-or-branch> "<note>" [--wide]   lane: queue a committed, clean branch
    scripts/mq-wait.sh <branch> [--timeout S]                 lane: block until it landed or bounced
    scripts/mq-next.sh                                        queue agent: land the next entry/batch
    scripts/mq-wait.sh --queue [--timeout S]                  queue agent: block until an entry waits
    scripts/mq-status.sh                                      anyone: queue, entry in progress, results
    scripts/mq.py hold <branch>|'*' / release <branch>|'*'    coordinator: keep entries waiting

State, all under the main checkout's _tmp/ (shared by every worktree through the _tmp symlink):
  merge-queue        append-only, one tab-separated line per submission (entry id = line number):
                     time, branch, commit, base, touched, note, flags
  merge-queue.done   append-only, one line per finished entry: time, id, status, branch, commit, info
                     (status: landed / bounced / superseded)
  mq/current         JSON of the entry/batch mq-next is working on (absent when idle)
  mq/hold            branch names (or `*`) mq-next leaves waiting
  mq/logs/<run>/     merge, regeneration, relink and gate logs of each attempt
  mq-log.csv         per entry: queue wait, merge, gates and total seconds, the steps run, and the
                     modules the gate build compiled (`built`, of `jobs`): cache misses
  wt-mq/             the queue's worktree (branch _mq), created on first use

mq-next.sh: takes the oldest waiting entry and up to MQ_BATCH-1 (default 4 in all) later ones of the
same kind (all needing a build or none) whose changed files are disjoint, merges them onto master in
wt-mq, resolves mechanical conflicts (appends; the generated files ConAgua/Checker/{Prog,ProgWf,Asm,
AsmPart*}.lean, checker.s and pins.bin by regeneration when both sides changed them; link anchors by
scripts/relink.py), runs `scripts/gates.sh --changed <master>` (the path-selected steps of
scripts/gate_select.py; when the merge result is exactly the tree of a commit that scripts/gates.sh
stamped green (_tmp/mq/green/<commit>: the entry had merged the current master), only the cheap steps:
the build, closure checks and e2e already passed on that tree) and on green fast-forwards master in the main checkout (under
_tmp/land.lock, so it never interleaves with scripts/land.sh). A red batch is split in halves and
each half retried; a red single entry, or a non-mechanical conflict, is bounced.
Exit status: 0 all landed, 1 something bounced, 3 queue empty, 4 busy or held, 5 infrastructure
error (main checkout dirty or not on master, master keeps moving, a lock timeout): tell the coordinator.
"""
import ctypes
import csv
import fcntl
import glob
import json
import os
import re
import select
import signal
import subprocess
import sys
import time

SCRIPTS = os.path.dirname(os.path.abspath(__file__))


def sh(*a, cwd=None, check=True, **kw):
    r = subprocess.run(list(a), cwd=cwd, capture_output=True, text=True, **kw)
    if check and r.returncode:
        raise RuntimeError(f"{' '.join(a)}: exit {r.returncode}\n{r.stdout}{r.stderr}")
    return r


def git(cwd, *a, check=True):
    return sh("git", "-C", cwd, *a, check=check).stdout.strip()


MAIN = os.environ.get("MQ_MAIN") or os.path.dirname(
    os.path.realpath(git(SCRIPTS, "rev-parse", "--path-format=absolute", "--git-common-dir")))
T = os.path.join(MAIN, "_tmp")
QUEUE = os.path.join(T, "merge-queue")
DONE = os.path.join(T, "merge-queue.done")
QLOCK = os.path.join(T, ".merge-queue.lock")
MQDIR = os.path.join(T, "mq")
CURRENT = os.path.join(MQDIR, "current")
NEXTLOCK = os.path.join(MQDIR, "next.lock")
HOLD = os.path.join(MQDIR, "hold")
LOGS = os.path.join(MQDIR, "logs")
CSV = os.path.join(T, "mq-log.csv")
WT = os.environ.get("MQ_WT") or os.path.join(T, "wt-mq")
LANDLOCK = os.path.join(T, "land.lock")
BRANCH = "_mq"
INTO = "master"
MAX_BEHIND = int(os.environ.get("MQ_MAX_BEHIND", "15"))
BATCH = int(os.environ.get("MQ_BATCH", "4"))
STALL = int(os.environ.get("MQ_STALL", "1800"))  # mq-wait: entries waiting, no mq-next for this long
# Generated files the queue regenerates when both sides of a merge changed them (or they conflict),
# in order; regenerating a group regenerates every later one too.
GEN_PROG = re.compile(r"ConAgua/Checker/(Prog|ProgWf|Asm|AsmPart\d+)\.lean$")
GROUPS = [("checkerProg (scripts/checker_prog.py)", lambda f: bool(GEN_PROG.match(f)), ["python3", "scripts/checker_prog.py"]),
          ("checker.s/pins.bin (scripts/asm_file.py)", lambda f: f in ("checker.s", "pins.bin"), ["python3", "scripts/asm_file.py"]),
          ("Reasons.lean/reasons.h (scripts/reasons.py)", lambda f: f in ("ConAgua/Arena/Reasons.lean", "reasons.h"), ["python3", "scripts/reasons.py"])]
EXPECTED = "scripts/overview-links-expected.txt"


def gen_group(f):
    return next((i for i, (_, m, _) in enumerate(GROUPS) if m(f)), None)


SHAREABLE_FILES = {"checker.s", "pins.bin", EXPECTED, "docs/velocity.csv", "docs/deviations.md"}

sys.path.insert(0, SCRIPTS)
import gate_select  # noqa: E402


def now():
    return time.strftime("%Y-%m-%dT%H:%M:%S")


def parse_time(s):
    return time.mktime(time.strptime(s, "%Y-%m-%dT%H:%M:%S"))


def dur(s):
    s = int(s)
    return f"{s}s" if s < 120 else f"{s // 60}m" if s < 7200 else f"{s / 3600:.1f}h"


class Locked:
    def __init__(self, path, timeout=None, blocking=True):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        self.f = open(path, "a+")
        self.ok = True
        if not blocking:
            try:
                fcntl.flock(self.f, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                self.ok = False
            return
        deadline = None if timeout is None else time.time() + timeout
        while True:
            try:
                fcntl.flock(self.f, fcntl.LOCK_EX | (fcntl.LOCK_NB if deadline else 0))
                return
            except BlockingIOError:
                if time.time() > deadline:
                    self.ok = False
                    return
                wait_change([path], 5)

    def release(self):
        fcntl.flock(self.f, fcntl.LOCK_UN)
        self.f.close()


def lock_free(path):
    if not os.path.exists(path):
        return True
    lk = Locked(path, blocking=False)
    if lk.ok:
        lk.release()
    return lk.ok


def append(path, fields):
    lk = Locked(QLOCK)
    try:
        with open(path, "a") as f:
            f.write("\t".join(str(x).replace("\t", " ").replace("\n", " ") for x in fields) + "\n")
    finally:
        lk.release()


def read_queue():
    out = []
    if os.path.exists(QUEUE):
        for i, line in enumerate(open(QUEUE), 1):
            p = line.rstrip("\n").split("\t")
            if len(p) < 6:
                continue
            p += [""] * (7 - len(p))
            out.append(dict(id=i, time=p[0], branch=p[1], commit=p[2], base=p[3], touched=p[4],
                            note=p[5], flags=p[6]))
    return out


def read_done():
    out = {}
    if os.path.exists(DONE):
        for line in open(DONE):
            p = line.rstrip("\n").split("\t")
            if len(p) >= 6:
                out[int(p[1])] = dict(time=p[0], id=int(p[1]), status=p[2], branch=p[3], commit=p[4], info=p[5])
    return out


def holds():
    if not os.path.exists(HOLD):
        return set()
    return {l.strip() for l in open(HOLD) if l.strip()}


def pending():
    done = read_done()
    return [e for e in read_queue() if e["id"] not in done]


# ---------------------------------------------------------------------------- inotify waiting
_IN = dict(MODIFY=0x2, ATTRIB=0x4, CLOSE_WRITE=0x8, MOVE_SELF=0x800, DELETE_SELF=0x400)


def wait_change(paths, timeout):
    """Block until one of `paths` changes (inotify), or `timeout` seconds; never longer."""
    try:
        libc = ctypes.CDLL(None, use_errno=True)
        fd = libc.inotify_init1(os.O_NONBLOCK | os.O_CLOEXEC)
        if fd < 0:
            raise OSError
        try:
            mask = sum(_IN.values())
            if not any(libc.inotify_add_watch(fd, p.encode(), mask) >= 0 for p in paths if os.path.exists(p)):
                raise OSError
            r, _, _ = select.select([fd], [], [], timeout)
            if r:
                os.read(fd, 65536)
        finally:
            os.close(fd)
    except (OSError, AttributeError):
        time.sleep(min(timeout, 20))


# ---------------------------------------------------------------------------- submit
def cmd_submit(args):
    wide = "--wide" in args
    args = [a for a in args if a != "--wide"]
    if not args:
        sys.exit('usage: scripts/submit.sh <worktree-or-branch> "<note>" [--wide]')
    target, note = args[0], " ".join(args[1:])
    wt = None
    if os.path.isdir(target):
        wt = os.path.realpath(target)
        branch = git(wt, "symbolic-ref", "--quiet", "--short", "HEAD", check=False)
        if not branch:
            sys.exit(f"submit: {wt} is on a detached HEAD")
    else:
        branch = target
        if git(MAIN, "rev-parse", "--verify", "--quiet", f"refs/heads/{branch}", check=False) == "":
            sys.exit(f"submit: no branch {branch}")
        for blk in git(MAIN, "worktree", "list", "--porcelain").split("\n\n"):
            if f"branch refs/heads/{branch}" in blk.split("\n"):
                wt = blk.split("\n")[0].split(" ", 1)[1]
    if branch in (INTO, BRANCH, "_landing"):
        sys.exit(f"submit: refusing to queue {branch}")
    if wt:
        dirty = git(wt, "status", "--porcelain", "--untracked-files=no")
        if dirty:
            sys.exit(f"submit: {wt} has uncommitted changes:\n{dirty}\ncommit them (or stash) first")
    commit = git(MAIN, "rev-parse", f"refs/heads/{branch}")
    if sh("git", "-C", MAIN, "merge-base", "--is-ancestor", commit, INTO, check=False).returncode == 0:
        sys.exit(f"submit: {branch} ({commit[:10]}) is already in {INTO}: nothing to land")
    base = git(MAIN, "merge-base", commit, INTO)
    behind = int(git(MAIN, "rev-list", "--count", "--first-parent", f"{base}..{INTO}"))
    if behind > MAX_BEHIND:
        sys.exit(f"submit: {branch} is {behind} landings behind {INTO} (limit {MAX_BEHIND}): merge {INTO} "
                 f"into it, gate (scripts/gates.sh), commit, and submit again")
    for e in pending():
        if e["branch"] == branch and e["commit"] == commit:
            sys.exit(f"submit: {branch} at {commit[:10]} is already queued as #{e['id']}")
    files = git(MAIN, "diff", "--name-only", base, commit).splitlines()
    tops = sorted({"/".join(f.split("/")[:2]) for f in files})
    touched = ",".join(tops) or "none"
    flags = "wide" if wide else ""
    steps = [s for s, _ in gate_select.select(files, MAIN)]
    append(QUEUE, [now(), branch, commit, base, touched, note, flags])
    eid = len(read_queue())
    ahead = [e for e in pending() if e["id"] < eid]
    print(f"submitted {branch} {commit[:10]} as #{eid} (base {base[:10]}, {behind} behind {INTO}; "
          f"{len(ahead)} entr{'y' if len(ahead) == 1 else 'ies'} ahead){' [wide]' if wide else ''}")
    print(f"  touched: {touched}")
    print(f"  queue gates: {','.join(steps)}")
    if not os.path.exists(os.path.join(MQDIR, "green", commit)) and any(s in steps for s in ("build", "e2e")):
        print(f"  note: no green scripts/gates.sh run recorded for {commit[:10]}; the queue's build will "
              f"not be a cache hit")
    print(f"Do not commit to {branch} until it lands or bounces. Wait with: scripts/mq-wait.sh {branch}")


# ---------------------------------------------------------------------------- wait
def queue_health():
    """One line on the queue's state for messages: pending count, current entry and its age."""
    pend = pending()
    cur = read_current()
    if cur:
        alive = not lock_free(NEXTLOCK)
        age = time.time() - cur["started"]
        c = f"working on {cur['label']} for {dur(age)} ({cur.get('phase', '?')})" + ("" if alive else ", STALE: no mq-next running")
    else:
        c = "idle (no mq-next running)" if lock_free(NEXTLOCK) else "mq-next starting"
    return f"{len(pend)} waiting; {c}"


def cmd_wait(args):
    timeout = 4 * 3600
    if "--timeout" in args:
        i = args.index("--timeout")
        timeout = float(args[i + 1])
        del args[i:i + 2]
    deadline = time.time() + timeout
    if args and args[0] == "--queue":
        while True:
            hs = holds()
            p = [e for e in pending() if "*" not in hs and e["branch"] not in hs]
            if p:
                print(f"queue: #{p[0]['id']} {p[0]['branch']} waiting ({len(p)} in all)")
                return 0
            if time.time() > deadline:
                print(f"queue: still empty after {dur(timeout)}")
                return 2
            wait_change([QUEUE, HOLD], min(60, max(1, deadline - time.time())))
    if not args:
        sys.exit("usage: scripts/mq-wait.sh <branch> [--timeout S] | --queue [--timeout S]")
    branch = args[0]
    idle_since = None
    while True:
        mine = [e for e in read_queue() if e["branch"] == branch]
        if not mine:
            print(f"mq-wait: {branch} is not in the queue (scripts/submit.sh first)")
            return 2
        e = mine[-1]
        d = read_done().get(e["id"])
        if d and d["status"] == "landed":
            print(f"landed {branch} {e['commit'][:10]} (#{e['id']}): {d['info']}")
            return 0
        if d and d["status"] == "bounced":
            print(f"bounced {branch} {e['commit'][:10]} (#{e['id']}): {d['info']}")
            print("Fix it in your worktree (merge master if it is a conflict), gate, commit, submit again.")
            return 1
        if d:
            print(f"mq-wait: #{e['id']} {branch}: {d['status']} {d['info']}")
            return 1
        # stall detection: entries waiting, nothing running, nothing finished for 30 min
        hs = holds()
        if "*" in hs or branch in hs:
            idle_since = None  # held by the coordinator: waiting is deliberate
        elif read_current() is None and lock_free(NEXTLOCK):
            last = max([os.path.getmtime(p) for p in (DONE, QUEUE) if os.path.exists(p)] + [0])
            idle_since = idle_since or time.time()
            if time.time() - max(last, idle_since) > STALL:
                print(f"mq-wait: {branch} (#{e['id']}) is waiting but no mq-next has run for {dur(STALL)}: the queue "
                      f"agent seems not to be running. Tell the coordinator. ({queue_health()})")
                return 3
        else:
            idle_since = None
        if time.time() > deadline:
            held = " (held by the coordinator)" if ("*" in hs or branch in hs) else ""
            print(f"mq-wait: timed out after {dur(timeout)} waiting for {branch} (#{e['id']}){held}; the queue: "
                  f"{queue_health()}. Tell the coordinator (scripts/mq-status.sh).")
            return 2
        wait_change([DONE, QUEUE, CURRENT], min(60, max(1, deadline - time.time())))


# ---------------------------------------------------------------------------- status
def read_current():
    try:
        return json.load(open(CURRENT))
    except (OSError, ValueError):
        return None


def cmd_status(args):
    hs = holds()
    if hs:
        print(f"HOLD: {' '.join(sorted(hs))}")
    cur = read_current()
    running = not lock_free(NEXTLOCK)
    if cur:
        age = time.time() - cur["started"]
        state = "running" if running else "STALE: mq-next died (rerun scripts/mq-next.sh; it resets wt-mq)"
        warn = "  STUCK? (over 90 min)" if age > 5400 and running else ""
        print(f"in progress: {cur['label']}  phase {cur.get('phase', '?')} for "
              f"{dur(time.time() - cur.get('phase_t', cur['started']))}, {dur(age)} in all, pid {cur['pid']}, "
              f"{state}{warn}")
        if cur.get("log"):
            print(f"  log: {cur['log']}")
    else:
        print("in progress: nothing" + (" (mq-next starting)" if running else ""))
    pend = pending()
    print(f"waiting: {len(pend)}")
    for e in pend:
        age = time.time() - parse_time(e["time"])
        h = " HELD" if ("*" in hs or e["branch"] in hs) else ""
        f = f" [{e['flags']}]" if e["flags"] else ""
        print(f"  #{e['id']:<4} {e['branch']:<16} {e['commit'][:10]} {dur(age):>5}{f}{h}  {e['touched'][:70]}  {e['note'][:60]}")
    done = sorted(read_done().values(), key=lambda d: d["time"])[-10:]
    if done:
        print("recent:")
        for d in done:
            print(f"  {d['time'][5:16]} #{d['id']:<4} {d['status']:<10} {d['branch']:<16} {d['info'][:100]}")
    return 0


def cmd_hold(args, on):
    if not args:
        sys.exit("usage: scripts/mq.py hold|release <branch>|'*'")
    hs = holds()
    hs = (hs | set(args)) if on else (hs - set(args) if "*" not in args else set())
    os.makedirs(MQDIR, exist_ok=True)
    with open(HOLD + ".tmp", "w") as f:
        f.write("".join(h + "\n" for h in sorted(hs)))
    os.replace(HOLD + ".tmp", HOLD)
    print(f"held: {' '.join(sorted(hs)) or 'nothing'}")


# ---------------------------------------------------------------------------- next
class Infra(Exception):
    pass


def set_current(label, phase, log=None, entries=None, _state={}, **kw):
    if entries is not None:
        _state.update(label=label, entries=entries, started=_state.get("started") or time.time())
    if phase is not None:
        _state.update(phase=phase, phase_t=time.time(), label=label)
    _state.update(pid=os.getpid(), **kw)
    if log:
        _state["log"] = log
    with open(CURRENT + ".tmp", "w") as f:
        json.dump(_state, f)
    os.replace(CURRENT + ".tmp", CURRENT)


def ensure_wt():
    if not os.path.isdir(os.path.join(WT, ".git")) and not os.path.isfile(os.path.join(WT, ".git")):
        git(MAIN, "worktree", "prune")
        git(MAIN, "worktree", "add", "-q", "-f", "-B", BRANCH, WT, INTO)
    if not os.path.lexists(os.path.join(WT, "_tmp")):
        os.symlink(T, os.path.join(WT, "_tmp"))
    os.makedirs(os.path.join(WT, ".lake"), exist_ok=True)
    pk = os.path.join(WT, ".lake", "packages")
    if not os.path.lexists(pk) and os.path.exists(os.path.join(MAIN, ".lake", "packages")):
        os.symlink(os.path.join(MAIN, ".lake", "packages"), pk)


def reset_wt(rev):
    git(WT, "merge", "--abort", check=False)
    git(WT, "reset", "-q", "--hard")
    git(WT, "checkout", "-q", "-f", "-B", BRANCH, rev)
    git(WT, "clean", "-fdq")


def changed(a, b, cwd=None):
    return set(git(cwd or WT, "diff", "--name-only", a, b).splitlines())


def entry_files(e):
    base = git(MAIN, "merge-base", e["commit"], INTO)
    return changed(base, e["commit"], MAIN)


def is_wide(e, files):
    return e["flags"] == "wide" or any("ALL" in gate_select.classify(f, MAIN) for f in files)


def needs_build(files):
    return any(s == "build" for s, _ in gate_select.select(files, MAIN))


def union_resolve(path):
    """Resolve a conflict whose every hunk only adds lines on both sides (empty base): ours, then
    theirs. Returns True if done."""
    def stage(n):
        r = subprocess.run(["git", "-C", WT, "show", f":{n}:{path}"], capture_output=True)
        return r.stdout if r.returncode == 0 else None
    ours, base, theirs = stage(2), stage(1) or b"", stage(3)
    if ours is None or theirs is None:
        return False
    d = os.path.join(MQDIR, "tmp")
    os.makedirs(d, exist_ok=True)
    fs = []
    for n, data in (("o", ours), ("b", base), ("t", theirs)):
        p = os.path.join(d, n)
        open(p, "wb").write(data)
        fs.append(p)
    r = subprocess.run(["git", "merge-file", "-p", "--diff3", *fs], capture_output=True)
    try:
        text = r.stdout.decode()
    except UnicodeDecodeError:
        return False
    out, mode, ok = [], None, True
    o, b, t = [], [], []
    for line in text.splitlines(keepends=True):
        if line.startswith("<<<<<<< ") and mode is None:
            mode, o, b, t = "o", [], [], []
        elif line.startswith("||||||| ") and mode == "o":
            mode = "b"
        elif line.startswith("=======") and mode == "b":
            mode = "t"
        elif line.startswith(">>>>>>> ") and mode == "t":
            if b:
                ok = False
            out += o + t
            mode = None
        elif mode == "o":
            o.append(line)
        elif mode == "b":
            b.append(line)
        elif mode == "t":
            t.append(line)
        else:
            out.append(line)
    if not ok or mode is not None:
        return False
    open(os.path.join(WT, path), "w").write("".join(out))
    return True


def merge_entry(e, log):
    """Merge e's commit onto the wt-mq tip. Returns (ok, notes, need_regen)."""
    before = git(WT, "rev-parse", "HEAD")
    base = git(WT, "merge-base", before, e["commit"])
    mine, theirs = changed(base, e["commit"]), changed(base, before)
    need_regen = {gen_group(f) for f in mine & theirs} - {None}
    msg = f"Merge branch '{e['branch']}'"
    r = sh("git", "-C", WT, "merge", "--no-ff", "--no-edit", "-m", msg, e["commit"], check=False)
    log.write(r.stdout + r.stderr)
    if r.returncode == 0:
        return True, [], need_regen
    conflicted = git(WT, "diff", "--name-only", "--diff-filter=U").splitlines()
    if not conflicted:
        return False, [f"merge failed: {r.stderr.strip()[:200]}"], set()
    notes, bad = [], []
    for f in conflicted:
        if gen_group(f) is not None:
            if sh("git", "-C", WT, "checkout", "--ours", "--", f, check=False).returncode:
                git(WT, "rm", "-q", "--", f)  # deleted on master's side; regeneration decides
            need_regen.add(gen_group(f))
            notes.append(f"{f} regenerated")
        elif f == EXPECTED:
            git(WT, "checkout", "--ours", "--", f)
            notes.append(f"{f} by relink")
        elif union_resolve(f):
            notes.append(f"{f} appended")
        else:
            bad.append(f)
            continue
        if os.path.exists(os.path.join(WT, f)):
            git(WT, "add", "--", f)
    if bad:
        git(WT, "merge", "--abort", check=False)
        return False, bad, set()
    git(WT, "commit", "-q", "--no-edit", "-m", f"{msg}\n\nmq: mechanical conflict resolution: {'; '.join(notes)}")
    log.write(f"mq: resolved {notes}\n")
    return True, notes, need_regen


def run_group(cmd, f, timeout, env=None):
    """Run cmd in its own process group (recorded in mq/current, so a later mq-next can stop what a
    killed one left running); stop the whole group on a timeout or when we are stopped."""
    p = subprocess.Popen(cmd, cwd=WT, stdout=f, stderr=subprocess.STDOUT, env=env, start_new_session=True)
    set_current(None, None, pgid=p.pid)
    try:
        return p.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        f.write(f"\nmq: timed out after {timeout}s\n")
        return 124
    finally:
        if p.poll() is None:
            try:
                os.killpg(p.pid, signal.SIGTERM)
                p.wait(timeout=30)
            except (ProcessLookupError, subprocess.TimeoutExpired):
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        set_current(None, None, pgid=None)


def stop_leftovers(cur):
    """A killed mq-next may have left a gate running in wt-mq: stop its process group (only if that
    process still runs in wt-mq)."""
    pg = cur.get("pgid") if cur else None
    if not pg:
        return
    try:
        if os.path.realpath(f"/proc/{pg}/cwd") != os.path.realpath(WT):
            return
        os.killpg(pg, signal.SIGTERM)
        print(f"note: stopped process group {pg} a killed mq-next left running in {WT}")
        time.sleep(5)
    except (OSError, ProcessLookupError):
        pass


EXPENSIVE = ("build", "shake") + tuple(gate_select.CLOSURES) + ("e2e",)


def green_steps(merged, steps):
    """When the merge result is exactly a tree that scripts/gates.sh ran green on (_tmp/mq/green/<commit>:
    the lane's gated commit, merged onto the master it had already merged), the expensive steps that
    run covered are not rerun: same tree, same result. Returns (steps to run, the green commit or None)."""
    if len(merged) != 1:
        return steps, None
    c = merged[0]["commit"]
    try:
        ran = open(os.path.join(MQDIR, "green", c)).read().strip()
    except OSError:
        return steps, None
    if git(WT, "rev-parse", "HEAD^{tree}") != git(WT, "rev-parse", c + "^{tree}"):
        return steps, None
    covered = set(gate_select.ORDER) if ran == "all" else set(ran.strip(",").split(","))
    keep = [s for s in steps.split(",") if not (s in EXPENSIVE and s in covered)]
    if keep == steps.split(","):
        return steps, None
    return ",".join(keep), c


def steps_minus(a, b):
    return "+".join(s for s in a.split(",") if s not in b.split(",")) or "nothing"


def build_counts(gates_logdir):
    """(modules Lake compiled, jobs) of the gate's build step, from its log: every compiled module is
    printed as `[i/n] Built M`; cache restores and up-to-date modules are silent. ("", "") without a build."""
    logs = glob.glob(os.path.join(gates_logdir, "*-build.log"))
    if not logs:
        return "", ""
    text = open(logs[0], errors="replace").read()
    built = len(re.findall(r"^\S+ \[\d+/\d+\] Built ", text, re.M))
    m = re.findall(r"\((\d+) jobs\)", text) or re.findall(r"\[\d+/(\d+)\]", text)
    return built, (m[-1] if m else "")


def run_logged(cmd, log, timeout):
    with open(log, "w") as f:
        return run_group(cmd, f, timeout)


CSV_HEADER = ["end", "id", "branch", "commit", "status", "batch", "queue_wait_s", "merge_s", "gates_s",
              "total_s", "steps", "info", "built", "jobs"]  # built: modules the gate build compiled (cache misses)


def csv_header():
    """Create mq-log.csv, or extend an older file's header with the columns added since."""
    if not os.path.exists(CSV):
        with open(CSV, "w", newline="") as f:
            csv.writer(f).writerow(CSV_HEADER)
        return
    with open(CSV, newline="") as f:
        rows = list(csv.reader(f))
    if rows and rows[0] != CSV_HEADER and CSV_HEADER[:len(rows[0])] == rows[0]:
        rows[0] = CSV_HEADER
        with open(CSV + ".tmp", "w", newline="") as f:
            csv.writer(f).writerows(rows)
        os.replace(CSV + ".tmp", CSV)


class Run:
    def __init__(self):
        self.timing = {}   # id -> dict(merge, gates)
        self.results = []  # printed lines
        self.status = 0
        self.steps = {}
        self.build = {}    # id -> (modules built, jobs) of the gate build

    def t(self, e, k, v):
        self.timing.setdefault(e["id"], {"merge": 0.0, "gates": 0.0, "start": time.time()})[k] += v

    def finish(self, e, status, info, size):
        append(DONE, [now(), e["id"], status, e["branch"], e["commit"], info])
        tm = self.timing.get(e["id"], {"merge": 0, "gates": 0, "start": time.time()})
        sub = parse_time(e["time"])
        csv_header()
        built, jobs = self.build.get(e["id"], ("", ""))
        with open(CSV, "a", newline="") as f:
            csv.writer(f).writerow([now(), e["id"], e["branch"], e["commit"][:12], status, size,
                                    int(tm["start"] - sub), int(tm["merge"]), int(tm["gates"]),
                                    int(time.time() - sub), self.steps.get(e["id"], ""), info, built, jobs])
        line = (f"{status} #{e['id']} {e['branch']} {e['commit'][:10]}: {info} "
                f"(wait {dur(tm['start'] - sub)}, merge {dur(tm['merge'])}, gates {dur(tm['gates'])})")
        print(line, flush=True)
        if status == "bounced":
            self.status = 1


def process(batch, run, attempt_label=""):
    """Merge, gate and land `batch` (a list of entries); split it when red."""
    label = "+".join(f"#{e['id']} {e['branch']}" for e in batch)
    for tries in range(3):
        master0 = git(MAIN, "rev-parse", INTO)
        logdir = os.path.join(LOGS, time.strftime("%Y%m%d-%H%M%S") + "-" + "+".join(e["branch"] for e in batch)[:80])
        os.makedirs(logdir, exist_ok=True)
        set_current(label, "merging", logdir, entries=[e["id"] for e in batch])
        reset_wt(master0)
        merged, regen, notes, own = [], set(), [], {}
        with open(os.path.join(logdir, "merge.log"), "w") as log:
            for e in batch:
                t0 = time.time()
                ok, info, need = merge_entry(e, log)
                run.t(e, "merge", time.time() - t0)
                if ok:
                    merged.append(e)
                    regen |= need
                    own[e["id"]] = info
                elif len(batch) > 1:
                    log.write(f"mq: {e['branch']} conflicts within the batch; it goes alone, after the rest\n")
                    process([x for x in batch if x is not e], run)
                    process([e], run)  # alone against master: lands, or bounces with its own conflict
                    return
                else:
                    run.finish(e, "bounced", f"merge conflict in {', '.join(info)}: merge master into "
                               f"{e['branch']}, resolve, gate, commit, resubmit", 1)
                    return
        tip_entries = merged
        t0 = time.time()
        fail = None
        for i in range(min(regen), len(GROUPS)) if regen else ():
            what, _, cmd = GROUPS[i]
            set_current(label, f"regenerating {what}", logdir)
            rl = os.path.join(logdir, f"regen-{i}.log")
            if run_logged(cmd, rl, 3600):
                fail = (f"regenerating {what} failed", rl)
                break
            git(WT, "add", "-A", "ConAgua", "checker.s", "pins.bin", "reasons.h")
            if git(WT, "status", "--porcelain", "--untracked-files=no"):
                git(WT, "commit", "-q", "-m", f"mq: regenerate {what.split(' ')[0]} after merging "
                    + ", ".join(e["branch"] for e in merged))
                notes.append(f"{what.split(' ')[0]} regenerated")
        if not fail and run_logged(["scripts/overview-links.sh"], os.path.join(logdir, "links-pre.log"), 120):
            set_current(label, "relinking", logdir)
            rc = run_logged(["python3", "scripts/relink.py", master0] + [e["commit"] for e in merged],
                            os.path.join(logdir, "relink.log"), 300)
            if rc == 0 and git(WT, "status", "--porcelain", "--untracked-files=no"):
                git(WT, "commit", "-q", "-a", "-m", "mq: relocate link anchors after merging "
                    + ", ".join(e["branch"] for e in merged))
                notes.append("link anchors relocated")
        if not fail:
            steps = ",".join(s for s, _ in gate_select.select(sorted(changed(master0, "HEAD")), WT))
            reduced, green = green_steps(merged, steps)
            if green:
                notes.append(f"tree gated green at {green[:10]}: {steps_minus(steps, reduced)} not rerun")
                steps = reduced
            set_current(label, f"gates {steps}", logdir)
            for e in merged:
                run.steps[e["id"]] = steps
            gl = os.path.join(logdir, "gates.log")
            gates = os.path.join(WT, "scripts", "gates.sh")
            cmd = ([gates, "--changed", master0] if os.path.exists(gates) and not green
                   else [gates if os.path.exists(gates) else os.path.join(SCRIPTS, "gates.sh"), "--only", steps])
            env = dict(os.environ, GATES_LOGDIR=os.path.join(logdir, "gates"))
            with open(gl, "w") as f:
                rc = run_group(cmd, f, 4 * 3600, env=env)
            if rc:
                m = re.search(r"^FAIL (\S+).* -- (\S+)$", open(gl).read(), re.M)
                fail = (f"gate {m.group(1)} failed" if m else "gates failed", m.group(2) if m else gl)
        counts = build_counts(os.path.join(logdir, "gates"))
        for e in merged:
            run.t(e, "gates", time.time() - t0)
            run.build[e["id"]] = counts
        if fail:
            if len(merged) > 1:
                h = len(merged) // 2
                print(f"split {label}: {fail[0]} on the batch; retrying in halves", flush=True)
                process(merged[:h], run)
                process(merged[h:], run)
            else:
                run.finish(merged[0], "bounced", f"{fail[0]}; log {fail[1]}", 1)
            return
        # land: fast-forward master in the main checkout
        set_current(label, "landing", logdir)
        tip = git(WT, "rev-parse", "HEAD")
        lk = Locked(LANDLOCK, timeout=3600)
        if not lk.ok:
            raise Infra("could not get _tmp/land.lock in 60 min (a scripts/land.sh stuck?)")
        try:
            if git(MAIN, "rev-parse", INTO) != master0:
                continue  # master moved (scripts/land.sh): merge again
            if git(MAIN, "symbolic-ref", "--short", "HEAD", check=False) != INTO:
                raise Infra(f"main checkout {MAIN} is not on {INTO}")
            dirty = git(MAIN, "status", "--porcelain", "--untracked-files=no")
            if dirty:
                raise Infra(f"main checkout {MAIN} is not clean:\n{dirty}")
            r = sh("git", "-C", MAIN, "merge", "-q", "--ff-only", tip, check=False)
            if r.returncode:
                raise Infra(f"fast-forward of {INTO} in {MAIN} failed: {r.stderr.strip()}")
        finally:
            lk.release()
        for e in tip_entries:
            n = own.get(e["id"], []) + notes
            run.finish(e, "landed", f"master {tip[:10]}" + (f"; {'; '.join(n)}" if n else ""), len(tip_entries))
        return
    raise Infra("master moved under the queue three times in a row (scripts/land.sh running?)")


def cmd_next(args):
    os.makedirs(MQDIR, exist_ok=True)
    lk = Locked(NEXTLOCK, blocking=False)
    if not lk.ok:
        cur = read_current()
        print(f"busy: another mq-next is running ({cur['label'] + ', ' + cur.get('phase', '') if cur else 'starting'})")
        return 4
    def stopped(sig, frame):
        raise KeyboardInterrupt(f"signal {sig}")
    signal.signal(signal.SIGTERM, stopped)
    signal.signal(signal.SIGHUP, stopped)
    stop_leftovers(read_current())
    try:
        hs = holds()
        if "*" in hs:
            print(f"held: the whole queue is on hold ({len(pending())} waiting)")
            return 4
        queue = pending()
        latest = {}
        for e in queue:
            latest[e["branch"]] = e["id"]
        run = Run()
        todo = []
        for e in queue:
            if latest[e["branch"]] != e["id"]:
                run.finish(e, "superseded", f"by #{latest[e['branch']]}", 0)
            elif e["branch"] in hs:
                continue
            elif sh("git", "-C", MAIN, "merge-base", "--is-ancestor", e["commit"], INTO, check=False).returncode == 0:
                run.finish(e, "landed", f"already in {INTO}", 0)
            else:
                todo.append(e)
        if not todo:
            held = [e for e in queue if e["branch"] in hs]
            print(f"empty{f' ({len(held)} held)' if held else ''}")
            return 3
        ensure_wt()
        first = todo[0]
        files = {first["id"]: entry_files(first)}
        batch = [first]
        if not is_wide(first, files[first["id"]]) and BATCH > 1:
            kind = needs_build(files[first["id"]])
            used = set(files[first["id"]])
            for e in todo[1:8]:
                if len(batch) >= BATCH:
                    break
                fe = entry_files(e)
                if is_wide(e, fe) or needs_build(fe) != kind or (fe & used) - SHAREABLE_FILES:
                    continue
                batch.append(e)
                used |= fe
        for e in batch:
            run.t(e, "merge", 0)
        try:
            process(batch, run)
        except Infra as ex:
            print(f"error: {ex}\n(the entries stay queued; tell the coordinator)", flush=True)
            return 5
        except KeyboardInterrupt as ex:
            print(f"stopped ({ex}); the entries stay queued", flush=True)
            return 5
        rest = len(pending())
        print(f"queue: {rest} waiting")
        return run.status
    finally:
        try:
            os.unlink(CURRENT)
        except FileNotFoundError:
            pass
        lk.release()


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    c, a = sys.argv[1], sys.argv[2:]
    if c == "submit":
        cmd_submit(a)
    elif c == "wait":
        sys.exit(cmd_wait(a))
    elif c == "status":
        sys.exit(cmd_status(a))
    elif c == "next":
        sys.exit(cmd_next(a))
    elif c in ("hold", "release"):
        cmd_hold(a, c == "hold")
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
