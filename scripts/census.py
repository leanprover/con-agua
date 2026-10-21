#!/usr/bin/env python3
"""scripts/census.py: the progress census (PLAN.md, "Progress census").

Counts how much of the twin (con-ron's arena model, plus the con-leche functions it calls) has
an L counterpart and a refinement proof. The data comes from `lake exe census`
(`ConAgua/Census/Main.lean`); this script adds weights and writes the report.

    scripts/census.py                 print the summary (build the census exe first if needed)
    scripts/census.py --write         also write docs/progress.md and append to docs/progress.csv
    scripts/census.py --list [REGEX]  print every target (or those matching REGEX) with its status
    scripts/census.py --rust DIR      regenerate scripts/census-rust.tsv from a con-ron checkout
    scripts/census.py --stale         print the stale targets (the work queue after a twin bump)
    scripts/census.py --record        add missing fingerprint rows, settle changed todo targets
                                      that no linked target reaches (--write does this too)
    scripts/census.py --reviewed REGEX  record the current fingerprint of the linked (or covered)
                                      targets matching REGEX: their L code and proofs were checked
                                      against the twin as vendored now

TARGETS. Every definition of `ConRon.*` and `ConLeche.*` reached from
`ConAgua.Final.TwinAccepts` through definition bodies, without instances, compiler/elaborator
auxiliaries, projections, type formers and predicates (see Main.lean), and without the con-leche
modules that are constant data (basis blocks, axiom shapes, pins: ROM, roadmap §2 item 11).

STATUS of a target, best first:
  proven      every `@[refines T]` theorem is free of sorry and of non-standard axioms
              (or every part named in COMPLETE_BY_PARTS below is), or every path from the
              entry to T passes through a proven target ("covered": e.g. the store helpers
              under `internE`)
  sorry       T's own `@[refines T]` theorems are proved, some modulo `sorryAx`; covers nothing
  written     an `@[l_impl T]` L function exists
  todo        nothing yet
Partial refinements (`@[refines_part T "label"]`) are listed separately; they never make T
proven, except through COMPLETE_BY_PARTS.

STALE (a flag beside the status). docs/twin-fingerprints.tsv records, for every target, the
fingerprint of its twin definition (Main.lean: a hash of its elaborated code and of the non-target
helpers it walks through); for a target that is not `todo`, as of the last review of its L code
or proof. Such a target is stale when its fingerprint differs from the recorded one, or when a
`todo` target below it (reached through `todo` targets only: twin code that its own L code stands
for, e.g. `Caches.empty` under `flushCaches`) changed: the vendored twin changed under the L code
(a con-ron/con-leche bump, scripts/bump-con-ron.sh). A stale covered target (no link of its own)
names the linked targets above it whose proofs cover it. `--reviewed REGEX` re-records the
matching targets (run by the lane that checked them) and every changed `todo` target no other
stale target still reaches; `--write` only adds rows for targets that have none (new links).

WEIGHTS. `lean`: lines of the target's own definition (blank lines, comments and doc comments
excluded, nested target definitions subtracted). `rust`: lines of the con-ron Rust functions
whose doc comment cites the target (`Lean twin: proof/ConRon/Arena/F.lean:a-b name`, or for
con-leche targets `con-leche: ConLeche/F.lean:a-b name`), from scripts/census-rust.tsv.
"""

import argparse
import collections
import csv
import datetime
import os
import re
import subprocess
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RUST_TSV = os.path.join(ROOT, "scripts", "census-rust.tsv")
FP_TSV = os.path.join(ROOT, "docs", "twin-fingerprints.tsv")
UPSTREAM = os.path.join(ROOT, "vendor", "UPSTREAM")

# A target whose refinement is split over parts: it is proven when every listed part is (status =
# the worst part). Value: (the target the parts are tagged on, the `@[refines_part T "label"]`
# labels). The alias form lets one tag serve the dispatcher and the function the arm calls.
_E = ["bvar", "fvar", "sort", "const", "app", "letE", "lit", "proj"]
COMPLETE_BY_PARTS = {
    "ConRon.Arena.internE": ("ConRon.Arena.internE", _E + ["lam", "forallE"]),
    "ConRon.Arena.internNodeE": ("ConRon.Arena.internE", _E),
    "ConRon.Arena.internLamE": ("ConRon.Arena.internE", ["lam"]),
    "ConRon.Arena.internForallEE": ("ConRon.Arena.internE", ["forallE"]),
    "ConRon.Arena.internLNode": ("ConRon.Arena.internLNode", ["zero", "succ", "max", "imax", "param"]),
    "ConRon.Arena.internNNode": ("ConRon.Arena.internNNode", ["anon", "str", "num"]),
    "ConRon.Arena.Frontend.parseNameEntryD": ("ConRon.Arena.Frontend.parseNameEntryD", ["str", "num"]),
}

# Modules that are constant data, not code: ROM (roadmap §2 item 11: basis blocks, axiom shapes,
# pins; the prelude text). Not targets.
ROM_MODULES = re.compile(r"^(ConLeche\.Kernel\.(Basis|BasisA|StdAxioms|TrustAxioms|TrustPins|CoreDefs)(\.|$)"
                         r"|ConRon\.Arena\.Frontend\.PreludeText$)")

STATUS_ORDER = ["proven", "sorry", "written", "todo"]

PHASES = [
    ("0", "stores, handles, monad"),
    ("1", "frontend (scanner, records)"),
    ("2", "env, pins, declarations"),
    ("3", "levels"),
    ("4", "expr ops"),
    ("5", "whnf"),
    ("6", "defeq"),
    ("7", "infer, knot"),
    ("8", "inductives"),
    ("9", "Nat/String literals"),
    ("10", "driver"),
]

PHASE9_NAMES = {"natOpResult", "natLitToConstructor", "natPred?", "isNatZero", "strLitConsSpine",
                "strLitToConstructor"}


def phase_of(name, module, line):
    m = module
    short = name.rsplit(".", 1)[-1]
    if m.startswith("ConRon.Arena.Frontend") or m.startswith("ConLeche.Frontend"):
        return "1"
    if m.startswith("ConRon.Arena.Inductives") or m == "ConLeche.Kernel.PropWhen":
        return "8"
    if m == "ConRon.Arena.Core":
        if short in PHASE9_NAMES:
            return "9"
        if line < 2440:
            return "5"
        if line < 2880:
            return "7"
        if line < 3540:
            return "6"
        return "7"
    if m in ("ConRon.Arena.CoreIO",):
        return "7"
    if m == "ConRon.Arena.ExprOps":
        return "4"
    if m == "ConLeche.Kernel.Level":
        return "3"
    if m in ("ConRon.Arena.Main", "ConRon.Arena.Phased", "ConRon.Arena.Pooled"):
        return "10"
    if m in ("ConRon.Arena.Store", "ConRon.Arena.Handle", "ConRon.Arena.Monad", "ConRon.Arena.Intern",
             "ConRon.Arena.Denote", "ConLeche.Kernel.Expr", "ConLeche.Kernel.Name"):
        return "0"
    return "2"


def src_path(module):
    rel = module.replace(".", "/") + ".lean"
    for base in ("vendor/con-ron", "vendor/con-leche", "."):
        p = os.path.join(ROOT, base, rel)
        if os.path.exists(p):
            return p
    return None


def code_lines(lines, start, end, skip):
    """Count code lines in 1-based [start, end], skipping the leading doc comment, comments,
    blank lines and the lines in `skip`."""
    n = 0
    in_block = 0
    for i in range(start, end + 1):
        if i in skip or i - 1 >= len(lines):
            continue
        s = lines[i - 1].strip()
        if in_block:
            if "-/" in s:
                in_block -= 1
            continue
        if s.startswith("/-"):
            if "-/" not in s[2:]:
                in_block = 1
            continue
        if not s or s.startswith("--"):
            continue
        n += 1
    return n


def lean_weights(targets):
    by_file = collections.defaultdict(list)
    for t in targets.values():
        p = src_path(t["module"])
        if p and t["start"] > 0:
            by_file[p].append(t)
    for p, ts in by_file.items():
        lines = open(p, encoding="utf-8").read().split("\n")
        for t in ts:
            skip = set()
            for u in ts:
                if u is not t and t["start"] <= u["start"] and u["end"] <= t["end"] and \
                        (u["start"], u["end"]) != (t["start"], t["end"]):
                    skip.update(range(u["start"], u["end"] + 1))
            t["lean"] = code_lines(lines, t["start"], t["end"], skip)


# ---------------------------------------------------------------- Rust weights

CITE = re.compile(r"(Lean twin|con-leche):\s*`?(?:proof/)?(ConRon|ConLeche)/([\w/]+)\.lean:\d+(?:-\d+)?\s+([\w.?!']+)")


def rust_fn_lines(lines, i):
    """Lines of the Rust item starting at line index i (the `fn` line) up to its closing brace."""
    depth = 0
    started = False
    n = 0
    j = i
    while j < len(lines):
        s = lines[j]
        code = re.sub(r"//.*", "", s)
        code = re.sub(r'"(\\.|[^"\\])*"', '""', code)
        code = re.sub(r"'(\\.|[^'\\])'", "''", code)
        if code.strip():
            n += 1
        for ch in code:
            if ch == "{":
                depth += 1
                started = True
            elif ch == "}":
                depth -= 1
        if started and depth <= 0:
            break
        if not started and code.rstrip().endswith(";"):
            break
        j += 1
    return n


def regen_rust(ref):
    src = os.path.join(ref, "crates")
    rows = collections.Counter()
    for dp, _, fs in os.walk(src):
        for f in fs:
            if not f.endswith(".rs"):
                continue
            path = os.path.join(dp, f)
            lines = open(path, encoding="utf-8").read().split("\n")
            doc = []
            for i, l in enumerate(lines):
                s = l.strip()
                if s.startswith("///") or s.startswith("#["):
                    doc.append(s)
                    continue
                if re.match(r"(pub(\([\w:]+\))?\s+)?(const\s+)?(unsafe\s+)?fn\s", s) and doc:
                    twin = [c for c in (CITE.search(d) for d in doc) if c and c.group(1) == "Lean twin"]
                    leche = [c for c in (CITE.search(d) for d in doc) if c and c.group(1) == "con-leche"]
                    cites = twin or leche
                    if cites:
                        c = cites[0]
                        key = f"{c.group(2)}/{c.group(3)}\t{c.group(4)}"
                        rows[key] += rust_fn_lines(lines, i)
                doc = []
    with open(RUST_TSV, "w") as fh:
        fh.write("# file\tname\trust_lines  (generated by scripts/census.py --rust <con-ron checkout>)\n")
        for k in sorted(rows):
            fh.write(f"{k}\t{rows[k]}\n")
    print(f"wrote {RUST_TSV}: {len(rows)} cited names, {sum(rows.values())} Rust lines")


def rust_weights(targets):
    if not os.path.exists(RUST_TSV):
        return 0
    by_mod = collections.defaultdict(list)
    for t in targets.values():
        by_mod[t["module"]].append(t)
    unmatched = 0
    for row in open(RUST_TSV):
        if row.startswith("#"):
            continue
        f, name, n = row.rstrip("\n").split("\t")
        mod = f.replace("/", ".")
        cands = [t for t in by_mod.get(mod, []) if t["name"] == name or t["name"].endswith("." + name)]
        if not cands:
            unmatched += int(n)
            continue
        cands.sort(key=lambda t: len(t["name"]))
        cands[0]["rust"] += int(n)
    return unmatched


# ---------------------------------------------------------------- the census


def modules_to_scan():
    cfg = tomllib.load(open(os.path.join(ROOT, "lakefile.toml"), "rb"))
    mods = []
    for lib in cfg.get("lean_lib", []):
        if lib["name"] == "ConAgua":
            mods += lib.get("roots", ["ConAgua"]) + lib.get("globs", [])
    seen = set()
    out = []
    for m in mods:
        if m not in seen and not m.endswith("+"):
            seen.add(m)
            out.append(m)
    return out


def lake():
    w = os.path.join(ROOT, "scripts", "lake")
    return [w] if os.path.exists(w) else ["lake"]


def run_census(build):
    if build:
        subprocess.run(lake() + ["build", "census"] + modules_to_scan(), cwd=ROOT, check=True,
                       stdout=subprocess.DEVNULL)
    r = subprocess.run(lake() + ["exe", "census", "ConAgua.Final.Twin"] + modules_to_scan(), cwd=ROOT,
                       capture_output=True, text=True, timeout=600)
    if r.returncode != 0:
        sys.stderr.write(r.stderr)
        sys.exit(f"census exe failed ({r.returncode})")
    for l in r.stderr.splitlines():
        if not l.startswith("census: module clash"):
            sys.stderr.write(l + "\n")
    return r.stdout


def analyse(out):
    targets, edges, roots, links, fps = {}, collections.defaultdict(set), [], [], {}
    for line in out.splitlines():
        f = line.split("\t")
        if f[0] == "F":
            fps[f[1]] = f[2]
        elif f[0] == "T":
            if ROM_MODULES.match(f[2]):
                continue
            targets[f[1]] = dict(name=f[1], module=f[2], start=int(f[3]), end=int(f[4]), kind=f[5],
                                 lean=0, rust=0)
        elif f[0] == "E":
            edges[f[1]].add(f[2])
        elif f[0] == "R":
            roots.append(f[1])
        elif f[0] == "L":
            links.append(dict(kind=f[1], decl=f[2], target=f[3], label=f[4], module=f[5], status=f[6]))
    lean_weights(targets)
    rust_unmatched = rust_weights(targets)

    impl = collections.defaultdict(list)
    refs = collections.defaultdict(list)
    parts = collections.defaultdict(list)
    dangling = []
    bad = [l for l in links if l["status"].startswith("error")]
    links = [l for l in links if not l["status"].startswith("error")]
    for l in links:
        if l["target"] not in targets:
            dangling.append(l)
            continue
        {"impl": impl, "refines": refs, "part": parts}[l["kind"]][l["target"]].append(l)

    def proof_status(ls):
        if any(l["status"] == "sorry" for l in ls):
            return "sorry"
        if all(l["status"] == "ok" for l in ls):
            return "proven"
        return "written"  # non-standard axioms: not counted as proven

    own = {}
    for n in targets:
        st = "todo"
        if impl[n]:
            st = "written"
        if refs[n]:
            st = proof_status(refs[n])
        elif n in COMPLETE_BY_PARTS:
            src, need = COMPLETE_BY_PARTS[n]
            got = collections.defaultdict(list)
            for l in parts[src]:
                got[l["label"]].append(l)
            if all(got[lbl] for lbl in need):
                st = proof_status([l for lbl in need for l in got[lbl]])
        own[n] = st

    # Coverage: a target counts as proven if every path from the entry to it passes through a
    # proven target: reachability with those targets cut. A complete refinement of the caller
    # accounts for every callee it reaches. Only from sorry-free proofs: a refinement proved modulo
    # `sorry` (a top-down skeleton over stub specs) counts as `sorry` itself but covers nothing,
    # its callees keep their own status. Not for `written` either: an L function may abort where
    # its twin calls on (`frontRun` on declaration lines).
    def reach_cut(cut):
        seen = set()
        st = [r for r in roots if r in targets]
        while st:
            n = st.pop()
            if n in seen:
                continue
            seen.add(n)
            if n in cut:
                continue
            st.extend(m for m in edges[n] if m in targets)
        return seen

    status = {}
    covered = set()
    for i, lvl in enumerate(STATUS_ORDER[:-1]):
        ok = {n for n in targets if own[n] in STATUS_ORDER[: i + 1]}
        r = reach_cut(ok)
        for n in targets:
            if n in status:
                continue
            if n in ok:
                status[n] = lvl
            elif lvl == "proven" and n not in r:
                status[n] = lvl
                covered.add(n)
    for n in targets:
        status.setdefault(n, "todo")
    for n, t in targets.items():
        t["status"] = status[n]
        t["own"] = own[n]
        t["covered"] = n in covered
        t["phase"] = phase_of(n, t["module"], t["start"])
        t["parts"] = parts[n]
        t["impl"] = impl[n]
        t["refs"] = refs[n]
        t["fp"] = fps.get(n, "")
    stale_marks(targets, edges)
    return targets, links, dangling + bad, rust_unmatched, edges


# ---------------------------------------------------------------- fingerprints


def upstream_revs():
    revs = {}
    if os.path.exists(UPSTREAM):
        for row in open(UPSTREAM):
            if row.strip() and not row.startswith("#"):
                f = row.split("\t")
                revs[f[0]] = f[1].strip()
    return revs


def repo_of(t):
    return "con-ron" if t["module"].startswith("ConRon") else "con-leche"


def read_fps():
    rec = {}
    if os.path.exists(FP_TSV):
        for row in open(FP_TSV):
            if row.strip() and not row.startswith("#"):
                name, fp, rev = row.rstrip("\n").split("\t")
                rec[name] = (fp, rev)
    return rec


def write_fps(rec):
    with open(FP_TSV, "w") as fh:
        fh.write("# The twin fingerprint of every census target; for one with L code, a proof or coverage, as of\n"
                 "# the last review of that code (scripts/census.py, \"STALE\"; DESIGN.md, \"Twin fingerprints\").\n"
                 "# Columns: target, fingerprint, upstream rev (con-ron or con-leche) it was recorded at. Update\n"
                 "# with `scripts/census.py --reviewed REGEX` after checking the L code against the new twin.\n")
        for n in sorted(rec):
            fh.write(f"{n}\t{rec[n][0]}\t{rec[n][1]}\n")


def via_changed(targets, edges, rec, n):
    """The `todo` targets reachable from n through `todo` targets only (the part of the twin n's
    own L code stands for) whose fingerprint differs from their recorded one."""
    out, seen, st = set(), set(), list(edges.get(n, ()))
    while st:
        m = st.pop()
        if m in seen or m not in targets:
            continue
        seen.add(m)
        u = targets[m]
        if u["status"] != "todo":
            continue  # linked or covered: flagged on its own
        r = rec.get(m)
        if r is not None and r[0] != u["fp"]:
            out.add(m)
        st.extend(edges.get(m, ()))
    return out


def stale_marks(targets, edges, rec=None):
    """Set, on every target that is not todo: t["via"] (changed todo targets below it, see
    via_changed), t["stale"] (its own recorded fingerprint differs, or `via` is not empty),
    t["unrecorded"] (no row); and t["above"] (the linked targets whose proofs cover a stale
    covered target)."""
    if rec is None:
        rec = read_fps()
    for t in targets.values():
        r = rec.get(t["name"])
        live = t["status"] != "todo"
        t["recorded"] = r
        t["own_stale"] = live and r is not None and r[0] != t["fp"]
        t["via"] = sorted(via_changed(targets, edges, rec, t["name"])) if live and r is not None else []
        t["stale"] = t["own_stale"] or bool(t["via"])
        t["unrecorded"] = live and r is None
        t["above"] = []
    callers = collections.defaultdict(set)
    for a, bs in edges.items():
        for b in bs:
            callers[b].add(a)
    for t in targets.values():
        if not (t["stale"] and t["covered"]):
            continue
        seen, st, above = set(), list(callers[t["name"]]), set()
        while st:
            n = st.pop()
            if n in seen or n not in targets:
                continue
            seen.add(n)
            u = targets[n]
            if u["own"] in ("proven", "sorry"):
                above.add(n)
            else:
                st.extend(callers[n])
        t["above"] = sorted(above)


def record_fps(targets, edges, rx=None):
    """Record fingerprints. Every target gets a row (todo ones too: a linked target is also stale
    when a todo target below it changed). Rows of targets without one, and with `rx` of the matching
    targets that are not todo, are set to the current fingerprint (= reviewed). A changed todo target
    is then re-recorded unless a linked target outside this review is still stale through it.
    Returns the names written."""
    rec = read_fps()
    revs = upstream_revs()
    cur = lambda t: (t["fp"], revs.get(repo_of(t), "?")[:8])
    done = set()
    for t in targets.values():
        n = t["name"]
        if n not in rec or (rx and rx.search(n) and t["status"] != "todo"):
            if rec.get(n) != cur(t):
                rec[n] = cur(t)
                done.add(n)
    reviewed = {t["name"] for t in targets.values() if t["status"] != "todo" and
                (t["name"] in done or (rx and rx.search(t["name"])))}
    pending = set()
    for t in targets.values():
        if t["status"] == "todo" or t["name"] in reviewed or t["name"] not in rec:
            continue
        pending |= via_changed(targets, edges, rec, t["name"])
    for t in targets.values():
        n = t["name"]
        if t["status"] == "todo" and rec[n][0] != t["fp"] and n not in pending:
            rec[n] = cur(t)
            done.add(n)
    for n in [n for n in rec if n not in targets and (rx is None or rx.search(n))]:
        del rec[n]
        done.add(n)
    write_fps(rec)
    stale_marks(targets, edges, rec)
    return sorted(done)


def stale_lines(targets):
    """The work queue: one entry per stale target, with what to look at."""
    revs = upstream_revs()
    out = []
    st = sorted((t for t in targets.values() if t["stale"]), key=lambda t: (int(t["phase"]), t["name"]))
    for t in st:
        repo = repo_of(t)
        mods = {t["module"]} | {targets[v]["module"] for v in t["via"] if repo_of(targets[v]) == repo}
        path = " ".join(sorted(("proof/" if repo == "con-ron" else "") + m.replace(".", "/") + ".lean"
                               for m in mods))
        old = t["recorded"][1]
        new = revs.get(repo, "?")[:8]
        what = describe(t) or "covered"
        if not t["own_stale"]:
            what += "; its own code is unchanged"
        if t["via"]:
            what += "; changed below it (no L code of their own): " + ", ".join(f"`{v}`" for v in t["via"])
        if t["above"]:
            what += "; covered by " + ", ".join(f"`{a}`" for a in t["above"])
        out.append((t, f"`{t['name']}` ({t['status']}, phase {t['phase']}): {what}. "
                       f"Diff: `git -C _tmp/ref/{repo} diff {old} {new} -- {path}`"))
    return out


def totals(ts):
    c = collections.Counter()
    for t in ts:
        c[(t["status"], "n")] += 1
        c[(t["status"], "lean")] += t["lean"]
        c[(t["status"], "rust")] += t["rust"]
        c[("all", "n")] += 1
        c[("all", "lean")] += t["lean"]
        c[("all", "rust")] += t["rust"]
    return c


def pct(a, b):
    return f"{100 * a / b:.1f}%" if b else "-"


def summary_rows(targets):
    rows = []
    for ph, title in PHASES + [("all", "total")]:
        ts = [t for t in targets.values() if ph == "all" or t["phase"] == ph]
        if not ts:
            continue
        c = totals(ts)
        rows.append((ph, title, c))
    return rows


def fmt_table(rows):
    hdr = ("phase", "targets", "proven", "sorry", "written", "todo", "Lean lines: proven / with L / all",
           "Rust lines: proven / with L / all")
    out = ["| " + " | ".join(hdr) + " |", "|" + "---|" * len(hdr)]
    for ph, title, c in rows:
        wl = c[("proven", "lean")] + c[("sorry", "lean")] + c[("written", "lean")]
        wr = c[("proven", "rust")] + c[("sorry", "rust")] + c[("written", "rust")]
        out.append("| " + " | ".join([
            f"{ph} {title}" if ph != "all" else "**total**",
            str(c[("all", "n")]),
            str(c[("proven", "n")]), str(c[("sorry", "n")]), str(c[("written", "n")]), str(c[("todo", "n")]),
            f"{c[('proven', 'lean')]} / {wl} / {c[('all', 'lean')]} ({pct(c[('proven', 'lean')], c[('all', 'lean')])})",
            f"{c[('proven', 'rust')]} / {wr} / {c[('all', 'rust')]} ({pct(c[('proven', 'rust')], c[('all', 'rust')])})",
        ]) + " |")
    return "\n".join(out)


def git(*a):
    return subprocess.run(["git", "-C", ROOT] + list(a), capture_output=True, text=True).stdout.strip()


def describe(t):
    bits = []
    if t["covered"]:
        bits.append("covered")
    for l in t["refs"]:
        bits.append(f"`{l['decl']}` ({l['status']})")
    if not t["refs"] and t["impl"]:
        bits.append("L: " + ", ".join(f"`{l['decl']}`" for l in t["impl"]))
    if t["parts"]:
        bits.append("parts: " + ", ".join(f"{l['label']} ({l['status']})" for l in t["parts"]))
    return "; ".join(bits)


def write_md(targets, links, dangling, rows, path):
    date = datetime.date.today().isoformat()
    commit = git("rev-parse", "--short", "HEAD")
    o = []
    o.append("# Progress census\n")
    o.append(f"Generated by `scripts/census.py --write` on {date} at `{commit}`; do not edit by hand. "
             "Definitions and rules: `scripts/census.py` (docstring) and PLAN.md, \"Progress census\". "
             "Time series: `docs/progress.csv`.\n")
    o.append("Targets: the definitions of con-ron's arena twin and of con-leche that "
             "`ConAgua.Final.TwinAccepts` reaches (no instances, auxiliaries, types, predicates or ROM "
             "data). **proven**: refinement proved without `sorry` (or every path to it goes through "
             "a proven target); **sorry**: proved modulo `sorry`; **written**: L code exists; "
             "**todo**: nothing. Weights: Lean code lines of the twin definition, and con-ron Rust "
             "lines citing it.\n")
    o.append("## Summary\n")
    o.append(fmt_table(rows) + "\n")
    st = stale_lines(targets)
    o.append("## Stale targets\n")
    if st:
        o.append("The twin changed under the L code (fingerprint differs from `docs/twin-fingerprints.tsv`): "
                 "check the L code and proofs against the new twin, then `scripts/census.py --reviewed "
                 "REGEX`.\n")
        for _, line in st:
            o.append("* " + line)
        o.append("")
    else:
        o.append("None: every linked or covered target's twin is as recorded in `docs/twin-fingerprints.tsv`.\n")
    # partial refinements
    plist = [(t, l) for t in targets.values() for l in t["parts"]]
    if plist:
        o.append("## Partial refinements (`@[refines_part]`)\n")
        o.append("| target | status of target | part | theorem | proof |")
        o.append("|---|---|---|---|---|")
        for t, l in sorted(plist, key=lambda x: (x[0]["name"], x[1]["label"])):
            o.append(f"| `{t['name']}` | {t['status']} | {l['label']} | `{l['decl']}` | {l['status']} |")
        o.append("")
    o.append("## Linked targets\n")
    o.append("Every target with an L function or a theorem linked to it.\n")
    o.append("| target | phase | lean | rust | status | links |")
    o.append("|---|---|---:|---:|---|---|")
    for t in sorted(targets.values(), key=lambda t: (int(t["phase"]), t["name"])):
        if t["impl"] or t["refs"] or t["parts"]:
            o.append(f"| `{t['name']}` | {t['phase']} | {t['lean']} | {t['rust']} | {t['status']} | {describe(t)} |")
    o.append("")
    cov = [t for t in targets.values() if t["covered"]]
    if cov:
        o.append("## Covered targets\n")
        o.append("Reached only through proven (or sorry) targets; they need no link of their own.\n")
        o.append(", ".join(f"`{t['name']}` ({t['status']})" for t in sorted(cov, key=lambda t: t["name"])) + "\n")
    if dangling:
        o.append("## Bad links\n")
        o.append("Links whose target is not in the target set (a helper the entry does not reach, ROM "
                 "data, or a misspelt name) or whose declaration has the wrong kind. They do not count.\n")
        for l in dangling:
            o.append(f"* `{l['decl']}` ({l['kind']}) → `{l['target']}`"
                     + (f" ({l['status']})" if l["status"].startswith("error") else ""))
        o.append("")
    o.append("## Per file\n")
    o.append("| module | targets | proven | sorry | written | todo | lean lines | rust lines |")
    o.append("|---|---:|---:|---:|---:|---:|---:|---:|")
    by_mod = collections.defaultdict(list)
    for t in targets.values():
        by_mod[t["module"]].append(t)
    for m in sorted(by_mod):
        c = totals(by_mod[m])
        o.append(f"| `{m}` | {c[('all', 'n')]} | {c[('proven', 'n')]} | {c[('sorry', 'n')]} | "
                 f"{c[('written', 'n')]} | {c[('todo', 'n')]} | {c[('all', 'lean')]} | {c[('all', 'rust')]} |")
    o.append("")
    open(path, "w").write("\n".join(o))


CSV_FIELDS = ["date", "commit", "targets", "proven", "sorry", "written", "todo",
              "lean_all", "lean_proven", "lean_sorry", "lean_written",
              "rust_all", "rust_proven", "rust_sorry", "rust_written", "parts_proven"]


def append_csv(targets, path):
    c = totals(targets.values())
    row = dict(date=datetime.datetime.now().strftime("%Y-%m-%d %H:%M"), commit=git("rev-parse", "--short", "HEAD"),
               targets=c[("all", "n")], proven=c[("proven", "n")], sorry=c[("sorry", "n")],
               written=c[("written", "n")], todo=c[("todo", "n")],
               lean_all=c[("all", "lean")], lean_proven=c[("proven", "lean")], lean_sorry=c[("sorry", "lean")],
               lean_written=c[("written", "lean")], rust_all=c[("all", "rust")], rust_proven=c[("proven", "rust")],
               rust_sorry=c[("sorry", "rust")], rust_written=c[("written", "rust")],
               parts_proven=sum(1 for t in targets.values() for l in t["parts"] if l["status"] == "ok"))
    new = not os.path.exists(path)
    with open(path, "a", newline="") as fh:
        w = csv.DictWriter(fh, CSV_FIELDS)
        if new:
            w.writeheader()
        w.writerow(row)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--write", action="store_true", help="write docs/progress.md, append docs/progress.csv")
    ap.add_argument("--list", nargs="?", const=".", metavar="REGEX", help="list targets")
    ap.add_argument("--no-build", action="store_true", help="do not build the census exe and modules first")
    ap.add_argument("--rust", metavar="DIR", help="regenerate scripts/census-rust.tsv from a con-ron checkout")
    ap.add_argument("--stale", action="store_true", help="print the stale targets (and unrecorded ones)")
    ap.add_argument("--reviewed", metavar="REGEX", help="record the current fingerprints of matching targets")
    ap.add_argument("--record", action="store_true",
                    help="only add missing fingerprint rows and settle changed todo targets (as --write does)")
    a = ap.parse_args()
    if a.rust:
        regen_rust(a.rust)
        return
    out = run_census(not a.no_build)
    targets, links, dangling, rust_unmatched, edges = analyse(out)
    if a.reviewed or a.record:
        done = record_fps(targets, edges, re.compile(a.reviewed) if a.reviewed else None)
        print(f"recorded {len(done)} fingerprint(s) in docs/twin-fingerprints.tsv" +
              "".join(f"\n  {n}" for n in sorted(done)))
        return
    if a.stale:
        st = stale_lines(targets)
        print(f"{len(st)} stale target(s):")
        for _, line in st:
            print("  " + line)
        unrec = sorted(t["name"] for t in targets.values() if t["unrecorded"])
        if unrec:
            print(f"{len(unrec)} linked/covered target(s) without a recorded fingerprint "
                  f"(--write records them): " + ", ".join(unrec))
        return
    if a.list:
        rx = re.compile(a.list)
        for t in sorted(targets.values(), key=lambda t: (int(t["phase"]), t["module"], t["start"])):
            if rx.search(t["name"]):
                flag = "+stale" if t["stale"] else ""
                print(f"{t['phase']}\t{t['status']}{flag}\t{t['lean']}\t{t['rust']}\t{t['name']}\t{describe(t)}")
        return
    rows = summary_rows(targets)
    print(fmt_table(rows))
    nparts = sum(len(t["parts"]) for t in targets.values())
    print(f"\nparts: {nparts} partial refinements "
          f"({sum(1 for t in targets.values() for l in t['parts'] if l['status'] == 'ok')} sorry-free); "
          f"links: {len(links)}; bad links: {len(dangling)}; "
          f"Rust lines citing no target: {rust_unmatched}")
    for l in dangling:
        print(f"  bad link: {l['decl']} ({l['kind']}) -> {l['target']}"
              + (f": {l['status']}" if l["status"].startswith("error") else ": not a target"))
    nstale = sum(1 for t in targets.values() if t["stale"])
    nunrec = sum(1 for t in targets.values() if t["unrecorded"])
    print(f"stale: {nstale} (`--stale` lists them); without a recorded fingerprint: {nunrec}")
    if a.write:
        record_fps(targets, edges)
        write_md(targets, links, dangling, rows, os.path.join(ROOT, "docs", "progress.md"))
        append_csv(targets, os.path.join(ROOT, "docs", "progress.csv"))
        print("wrote docs/progress.md, appended docs/progress.csv, recorded new fingerprints")


if __name__ == "__main__":
    main()
