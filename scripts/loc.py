#!/usr/bin/env python3
"""Lines of L code and of proofs in ConAgua/ at a git commit (for the progress report).

    scripts/loc.py [COMMIT ...]   print `commit,l_lines,proof_lines` per commit (default HEAD)

L code = the non-blank lines of `lfn … { … }` blocks (from `lfn` to the matching brace); proofs = all
other non-blank lines of `.lean` files under ConAgua/ (specs, models, refinements, libraries, the
compiler and its proof). A rough split, but the same rule at every commit, so trends are comparable."""
import subprocess, sys, pathlib, json

root = pathlib.Path(__file__).resolve().parent.parent


def git(*a):
    return subprocess.run(["git", "-C", str(root), *a], capture_output=True, text=True, errors="replace").stdout


def split(text):
    lines = text.splitlines()
    l_lines = 0
    i = 0
    total = sum(1 for x in lines if x.strip())
    while i < len(lines):
        ln = lines[i]
        k = ln.find("lfn")
        if k >= 0 and (k == 0 or not (ln[k - 1].isalnum() or ln[k - 1] in "_.")) and \
                (k + 3 == len(ln) or not (ln[k + 3].isalnum() or ln[k + 3] in "_")):
            depth, started, j = 0, False, i
            while j < len(lines):
                seg = lines[j][k:] if j == i else lines[j]
                for ch in seg:
                    if ch == "{":
                        depth += 1; started = True
                    elif ch == "}":
                        depth -= 1
                if lines[j].strip():
                    l_lines += 1
                if started and depth <= 0:
                    break
                j += 1
            i = j + 1
        else:
            i += 1
    return l_lines, total - l_lines


def at(commit):
    files = [f for f in git("ls-tree", "-r", "--name-only", commit, "ConAgua").splitlines() if f.endswith(".lean")]
    if not files:
        return 0, 0
    # one `git cat-file --batch` for all files (sizes are in bytes, so read bytes)
    p = subprocess.run(["git", "-C", str(root), "cat-file", "--batch"],
                       input="".join(f"{commit}:{f}\n" for f in files).encode(), capture_output=True)
    out, L, P, pos = p.stdout, 0, 0, 0
    while pos < len(out):
        nl = out.index(b"\n", pos)
        hdr = out[pos:nl].split()
        if len(hdr) < 3 or hdr[1] != b"blob":
            pos = nl + 1
            continue
        size = int(hdr[2])
        body = out[nl + 1: nl + 1 + size].decode("utf-8", "replace")
        pos = nl + 1 + size + 1
        a, b = split(body)
        L += a; P += b
    return L, P


if __name__ == "__main__":
    for c in sys.argv[1:] or ["HEAD"]:
        a, b = at(c)
        print(f"{c},{a},{b}")
