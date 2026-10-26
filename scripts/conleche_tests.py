"""con-leche's `tests/` at exactly the revision `vendor/UPSTREAM` pins, read from git.

`tests_dir()` returns a directory holding that tree: `$CON_LECHE_TESTS` if set (an override, not
checked), else a cache `_tmp/ref/con-leche-tests/<rev>/tests` extracted with `git archive` from the
reference clone `_tmp/ref/con-leche` (fetched if it lacks the revision). The clone's working tree
and checked-out revision are never consulted, so a twin sync needs no manual checkout.
"""
import os
import shutil
import subprocess
import sys
import tarfile
import io

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CLONE = os.path.join(ROOT, "_tmp", "ref", "con-leche")
CACHE = os.path.join(ROOT, "_tmp", "ref", "con-leche-tests")


def pinned(repo="con-leche"):
    with open(os.path.join(ROOT, "vendor", "UPSTREAM"), encoding="utf-8") as f:
        for line in f:
            w = line.split()
            if len(w) >= 3 and w[0] == repo:
                return w[1], w[2]
    sys.exit(f"vendor/UPSTREAM names no {repo} revision")


def _has(rev):
    return subprocess.run(["git", "-C", CLONE, "cat-file", "-e", rev + "^{commit}"],
                          capture_output=True).returncode == 0


def tests_dir():
    env = os.environ.get("CON_LECHE_TESTS")
    if env:
        return env
    rev, url = pinned()
    out = os.path.join(CACHE, rev, "tests")
    if os.path.isfile(os.path.join(out, "e2e-expected.txt")):
        return out
    if not os.path.isdir(os.path.join(CLONE, ".git")) and not os.path.isfile(os.path.join(CLONE, "HEAD")):
        os.makedirs(os.path.dirname(CLONE), exist_ok=True)
        subprocess.run(["git", "clone", "--no-checkout", url, CLONE], check=True)
    if not _has(rev):
        subprocess.run(["git", "-C", CLONE, "fetch", "origin", rev], check=True)
        if not _has(rev):
            subprocess.run(["git", "-C", CLONE, "fetch", "origin"], check=True)
    if not _has(rev):
        sys.exit(f"con-leche revision {rev} (vendor/UPSTREAM) is not in {CLONE}, even after fetching")
    tmp = os.path.join(CACHE, f"{rev}.part{os.getpid()}")
    shutil.rmtree(tmp, ignore_errors=True)
    os.makedirs(tmp)
    data = subprocess.run(["git", "-C", CLONE, "archive", rev, "tests"], check=True, capture_output=True).stdout
    with tarfile.open(fileobj=io.BytesIO(data)) as t:
        t.extractall(tmp, filter="data")
    try:
        os.rename(tmp, os.path.join(CACHE, rev))
    except OSError:  # a concurrent run won
        shutil.rmtree(tmp, ignore_errors=True)
    return out
