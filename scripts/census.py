#!/usr/bin/env python3
"""scripts/census.py: the progress census (PLAN.md, "Progress census").

Counts how much of the twin (con-ron's arena model, plus the con-leche functions it calls) has
an L counterpart and a refinement proof. The data comes from `lake exe census`
(`ConAgua/Census/Main.lean`); this script adds weights and writes the report.

    scripts/census.py                 print the summary (build the census exe first if needed)
    scripts/census.py --write         also write _tmp/census/progress.md and append to _tmp/census/progress.csv
    scripts/census.py --list [REGEX]  print every target (or those matching REGEX) with its status
    scripts/census.py --rust DIR      regenerate scripts/census-rust.tsv from a con-ron checkout

TARGETS. Every definition of `ConRon.*` and `ConLeche.*` reached from
`ConAgua.Final.TwinAccepts` through definition bodies, without instances, compiler/elaborator
auxiliaries, projections, type formers and predicates (see Main.lean), and without the con-leche
modules that are constant data (basis blocks, axiom shapes, pins: ROM, roadmap §2 item 11).

STATUS of a target, best first:
  proven      every `@[refines T]` theorem is free of sorry and of non-standard axioms
              (or every part named in COMPLETE_BY_PARTS below is), or every path from the
              entry to T passes through a proven target ("covered": e.g. the store helpers
              under `internE`)
  local       T's `@[refines T]` theorems are proved, their own terms (and generated auxiliaries:
              `proof_N`, `match_N`, `eq_N`) free of `sorryAx`, but they use other constants that
              carry it ("proven locally"); covers nothing. The nearest constants carrying
              `sorryAx` directly are the "sorry sources" (_tmp/census/progress.md: a work queue)
              (the "sorry" columns of the report count local + sorry: everything depending on `sorryAx`)
  sorry       `sorryAx` occurs directly in T's own `@[refines T]` proof term (or its auxiliaries);
              covers nothing
  written     an `@[l_impl T]` L function exists
  n/a         "not needed": the L checker deliberately implements nothing for T (a Deliberate row of
              docs/deviations.md, an error text, an unused mode). Listed with a reason in
              docs/not-needed.md; census.py fails if a listed target does not exist or has an L
              function or refinement of its own (stale entry). Excluded from the denominators of
              every share, so 100% is reachable.
  todo        nothing yet. Informational: "pending" = todo targets every path to which from the entry
              passes through a target that has its own link (an L function or theorem), so that they
              become covered when those callers are proven (accessors, tags, hash cluster)
Partial refinements (`@[refines_part T "label"]`) are listed separately; they never make T
proven, except through COMPLETE_BY_PARTS.

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
import json
import signal
import subprocess
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RUST_TSV = os.path.join(ROOT, "scripts", "census-rust.tsv")

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
    "ConRon.Arena.BasisKind.decls": ("ConRon.Arena.BasisKind.decls", ["the four kinds basisPinHit tries", "the quotient block"]),
    "ConRon.Arena.BasisKind.declsA": ("ConRon.Arena.BasisKind.declsA", ["the four kinds basisPinHit tries", "the quotient block"]),
    "ConRon.Arena.Frontend.processLineCoreD": ("ConRon.Arena.Frontend.processLineCoreD",
                                               ["axiom, def, thm, opaque, quot", "inductive"]),
}

# Modules that are constant data, not code: ROM (roadmap §2 item 11: basis blocks, axiom shapes,
# pins; the prelude text). Not targets.
ROM_MODULES = re.compile(r"^(ConLeche\.Kernel\.(Basis|BasisA|StdAxioms|TrustAxioms|TrustPins|CoreDefs)(\.|$)"
                         r"|ConRon\.Arena\.Frontend\.PreludeText$)")

STATUS_ORDER = ["proven", "local", "sorry", "written", "todo"]
NOT_NEEDED = os.path.join(ROOT, "docs", "not-needed.md")


def read_not_needed():
    """{target: (reason, deviation ids)} from the table in docs/not-needed.md:
    `| `Target` | reason | D29 |` (the deviation cell may be `-`)."""
    out = {}
    if not os.path.exists(NOT_NEEDED):
        return out
    for line in open(NOT_NEEDED, encoding="utf-8"):
        m = re.match(r"\|\s*`([^`]+)`\s*\|(.*)\|\s*$", line)
        if not m:
            continue
        cells = [c.strip() for c in m.group(2).split("|")]
        if len(cells) != 2 or not cells[0]:
            sys.exit(f"{NOT_NEEDED}: row of {m.group(1)} needs exactly: target | reason | deviation")
        if m.group(1) in out:
            sys.exit(f"{NOT_NEEDED}: {m.group(1)} listed twice")
        out[m.group(1)] = (cells[0], cells[1])
    return out

PHASES = [
    ("0", "stores, handles, monad"),
    ("1a", "scanner (lexing)"),
    ("1b", "records (line to record)"),
    ("1c", "frontend: intern, prelude, export"),
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


# The lexing half of con-leche's NDJSON scanner (ConLeche.Frontend.Scan.Fast): byte classes, number,
# string and name tokens, literal matching, bracket skipping. What is left of the scan modules turns
# tokens into records: `scanXxxExpr`, `scanXxxDecl`, `scanInd*`, `scanRule(s)`, `scanHints`,
# `scanLineFwd`/`scanLineLoop`, and the error and id-table types.
SCANNER_NAMES = re.compile(
    r"^(byteAt|isWs|isDigit|skipWs|skipDigits|readNat\w*|numEnd|matchLit|lit\d+|keyEnd|keyAt|valueAt|"
    r"newlineFrom|scanBool|strClose|hasEscape|hex\w*|utf8Of|replacementChar|unescape|scanString|"
    r"scanQuotedNat|scanBinderInfo|scanNatList\w*|skipBraced|scanStrName\w*|scanNumName\w*)$")


def phase_key(ph):
    """Sort key of a phase id (`"7"`, `"1b"`): numeric part, then suffix."""
    m = re.fullmatch(r"(\d+)([a-z]*)", ph)
    return (int(m.group(1)), m.group(2))


def phase_of(name, module, line):
    m = module
    short = name.rsplit(".", 1)[-1]
    if m.startswith("ConLeche.Frontend.Scan"):
        return "1a" if m == "ConLeche.Frontend.Scan.Fast" and SCANNER_NAMES.match(short) else "1b"
    if m.startswith("ConRon.Arena.Frontend") or m.startswith("ConLeche.Frontend"):
        return "1c"
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


MEM_LIMIT_GB = 6  # the census exe peaks at about 2.8 GB (DESIGN.md, "Census memory")


def tree_pids(pid):
    out, todo = [], [pid]
    while todo:
        p = todo.pop()
        out.append(p)
        try:
            for tid in os.listdir(f"/proc/{p}/task"):
                with open(f"/proc/{p}/task/{tid}/children") as fh:
                    todo += [int(x) for x in fh.read().split()]
        except (OSError, ValueError):
            pass
    return out


def tree_rss(pid):
    """Resident memory (bytes) of `pid` and all its descendants, from /proc."""
    total = 0
    for p in tree_pids(pid):
        try:
            with open(f"/proc/{p}/status") as fh:
                total += next((int(l.split()[1]) * 1024 for l in fh if l.startswith("VmRSS:")), 0)
        except (OSError, ValueError):
            pass
    return total


def run_guarded(cmd, limit_gb=MEM_LIMIT_GB, timeout=int(os.environ.get("CENSUS_TIMEOUT", "600"))):
    """Run `cmd` with its output in temporary files; poll the resident memory of its process
    tree every 0.2 s and kill that tree (by pid) above `limit_gb` GB or after `timeout` s, so a
    runaway census can never exhaust the session's memory (it took the machine down twice)."""
    import tempfile
    import time
    with tempfile.TemporaryFile("w+") as out, tempfile.TemporaryFile("w+") as err:
        p = subprocess.Popen(cmd, cwd=ROOT, stdout=out, stderr=err, text=True, start_new_session=True)
        t0, peak, why = time.time(), 0, None
        while p.poll() is None:
            m = tree_rss(p.pid)
            peak = max(peak, m)
            if m > limit_gb * 2**30:
                why = f"used {m / 2**30:.1f} GB, over the census memory limit of {limit_gb} GB"
            elif time.time() - t0 > timeout:
                why = f"ran over {timeout} s"
            if why:
                for q in tree_pids(p.pid):
                    try:
                        os.kill(q, signal.SIGKILL)
                    except OSError:
                        pass
                p.wait()
                sys.exit(f"census exe killed: it {why} (MEM_LIMIT_GB in scripts/census.py)")
            time.sleep(0.2)
        out.seek(0)
        err.seek(0)
        return p.returncode, out.read(), err.read(), peak


def stage_done(name, t0):
    """Timing line for the census log (stderr, like the exe's own `census: stage ...` lines)."""
    import time
    sys.stderr.write(f"census: stage {name}: {time.time() - t0:.1f} s\n")
    sys.stderr.flush()


def run_census(build):
    import time
    if build:
        t0 = time.time()
        subprocess.run(lake() + ["build", "census"] + modules_to_scan(), cwd=ROOT, check=True,
                       stdout=subprocess.DEVNULL)
        stage_done("lake build (census exe and all scanned modules)", t0)
    t0 = time.time()
    rc, out, err, peak = run_guarded(lake() + ["exe", "census", "ConAgua.Final.Twin"] + modules_to_scan())
    stage_done("census exe (targets + links, total)", t0)
    if rc != 0:
        sys.stderr.write(err)
        sys.exit(f"census exe failed ({rc})")
    for l in err.splitlines():
        if not l.startswith("census: module clash"):
            sys.stderr.write(l + "\n")
    if os.environ.get("CENSUS_PEAK"):
        sys.stderr.write(f"census exe peak memory: {peak / 2**30:.2f} GB\n")
    return out


def e2e_metrics(targets):
    """The critical-path metrics (percent, None when unknown): sorry-free share of the end-to-end
    theorem's cone, and the count of remaining sorry sources. `stagec_pct` (lane indstaget's StageC
    migration, finished) is retired: always None, its CSV column kept for the older rows."""
    cone = ASM.get("cone")
    nsrc = len(ASM.get("src") or []) if ASM.get("hyp") else None  # no "src" once the theorem is sorry-free
    return dict(
        stagec_pct=None,
        cone_pct=round(100 * int(cone[0]["type"]) / int(cone[0]["name"]), 1) if cone and int(cone[0]["name"]) else None,
        sorry_sources=nsrc if nsrc is not None else None,
        layout_leaks=layout_leaks())


def layout_leaks():
    """Lines outside the store library that compute the store record layout themselves (scripts/layout_leaks.py), or None."""
    try:
        r = subprocess.run([sys.executable, os.path.join(ROOT, "scripts", "layout_leaks.py")], capture_output=True, text=True, timeout=300, cwd=ROOT)
        m = re.search(r"lines (\d+) in \d+ files", r.stdout)
        return int(m.group(1)) if m else None
    except Exception:
        return None


ASM = {}  # the end-to-end theorem's `A` lines (ConAgua/Census/Main.lean `asmLines`), by kind


def asm_data(targets):
    """The end-to-end theorem's remaining assumptions: hypotheses, axioms, sorry sources (ranked by
    the proven-locally targets they block), or None when the census exe printed none."""
    if not ASM.get("hyp"):
        return None
    blocked = dict(sorry_sources(targets))
    srcs = [dict(name=a["name"], blocks=len(blocked.get(a["name"], ())))
            for a in ASM.get("src", [])]
    srcs.sort(key=lambda x: (-x["blocks"], x["name"]))
    return dict(theorem="ConAgua.Final.checkerFile_accepts",
                hyps=[dict(name=h["name"], type=h["type"], prop=h["kind"] == "prop")
                      for h in ASM["hyp"] if not h["name"].startswith("inst")],
                axioms=[a["name"] for a in ASM.get("axiom", [])], sorry_sources=srcs)


def write_asm(targets, md=None):
    """The progress.md section (with `md`); its machine-readable twin is the JSON comment in it,
kept for tools that read progress.md."""
    d = asm_data(targets)
    if d is None:
        return
    if md is not None:
        std = {"propext", "Classical.choice", "Quot.sound"}
        md.append("## What the end-to-end theorem still assumes\n")
        md.append(f"`{d['theorem']}`. Axioms: "
                  + ", ".join(f"`{a}`" for a in d["axioms"])
                  + (" (only the standard ones)" if set(d["axioms"]) <= std else
                     " (besides the standard ones: sorry from the sources below)") + "\n")
        md.append("| hypothesis | statement |")
        md.append("|---|---|")
        for h in d["hyps"]:
            if h["prop"]:
                t = re.sub(r"\s+", " ", h["type"]).replace("|", "\\|")
                md.append(f"| `{h['name']}` | `{t[:200]}{'...' if len(t) > 200 else ''}` |")
        md.append("")
        md.append("| sorry source | blocks |")
        md.append("|---|---:|")
        for x in d["sorry_sources"]:
            md.append(f"| `{x['name']}` | {x['blocks']} |")
        md.append("")
        md.append("<!-- assumptions-json " + json.dumps(d).replace("--", "- -") + " -->\n")


def analyse(out):
    targets, edges, roots, links = {}, collections.defaultdict(set), [], []
    for line in out.splitlines():
        f = line.split("\t")
        if f[0] == "T":
            if ROM_MODULES.match(f[2]):
                continue
            targets[f[1]] = dict(name=f[1], module=f[2], start=int(f[3]), end=int(f[4]), kind=f[5],
                                 lean=0, rust=0)
        elif f[0] == "E":
            edges[f[1]].add(f[2])
        elif f[0] == "R":
            roots.append(f[1])
        elif f[0] == "A" and len(f) >= 6:
            ASM.setdefault(f[1], []).append(dict(name=f[2], type=f[3], kind=f[4]))
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
        if any(l["status"].startswith("local") for l in ls):
            return "local"
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

    # pending: todo targets that every path to which passes through a linked target
    linked = {n for n in targets if own[n] != "todo"} | {n for n in targets if status[n] == "proven"}
    r = reach_cut(linked)
    pending = {n for n in targets if status[n] == "todo" and n not in r}

    # not needed: a reviewed list; stale entries are errors
    nn = read_not_needed()
    problems = []
    for n, (reason, dev) in nn.items():
        if n not in targets:
            problems.append(f"{n}: not a target (typo, or no longer reached)")
        elif own[n] != "todo" or impl[n] or refs[n] or parts[n]:
            problems.append(f"{n}: has an L function or refinement of its own ({own[n]}); remove it from the list")
        elif not reason or (not dev.startswith("D") and dev != "-"):
            problems.append(f"{n}: needs a reason and a deviation id (D<n>) or -")
    if problems:
        sys.exit("docs/not-needed.md is stale:\n  " + "\n  ".join(problems))
    for n in nn:
        status[n] = "n/a"
        pending.discard(n)
    for n, t in targets.items():
        t["pending"] = n in pending
        t["na"] = nn.get(n)
        t["status"] = status[n]
        t["own"] = own[n]
        t["covered"] = n in covered
        t["phase"] = phase_of(n, t["module"], t["start"])
        t["parts"] = parts[n]
        t["impl"] = impl[n]
        t["refs"] = refs[n]
    return targets, links, dangling + bad, rust_unmatched, edges


def totals(ts):
    c = collections.Counter()
    for t in ts:
        # "sorry" = everything depending on `sorryAx`, own or through callees; "local" = the subset
        # proven locally (its own term is sorry-free)
        if t.get("pending"):
            c[("pending", "n")] += 1
            c[("pending", "lean")] += t["lean"]
            c[("pending", "rust")] += t["rust"]
        for k in ([t["status"], "sorry"] if t["status"] == "local" else [t["status"]]):
            c[(k, "n")] += 1
            c[(k, "lean")] += t["lean"]
            c[(k, "rust")] += t["rust"]
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
    """Shares are over the targets minus n/a ("needed")."""
    hdr = ("phase", "targets", "proven", "sorry", "of which proven locally", "written", "todo",
           "of which pending", "n/a", "n/a Lean lines", "Lean lines: proven / with L / needed",
           "Rust lines: proven / with L / needed")
    out = ["| " + " | ".join(hdr) + " |", "|" + "---|" * len(hdr)]
    for ph, title, c in rows:
        wl = sum(c[(k, "lean")] for k in ("proven", "sorry", "written"))
        wr = sum(c[(k, "rust")] for k in ("proven", "sorry", "written"))
        nl = c[("all", "lean")] - c[("n/a", "lean")]
        nr = c[("all", "rust")] - c[("n/a", "rust")]
        out.append("| " + " | ".join([
            f"{ph} {title}" if ph != "all" else "**total**",
            str(c[("all", "n")]),
            str(c[("proven", "n")]), str(c[("sorry", "n")]), str(c[("local", "n")]), str(c[("written", "n")]), str(c[("todo", "n")]),
            str(c[("pending", "n")]), str(c[("n/a", "n")]), str(c[("n/a", "lean")]),
            f"{c[('proven', 'lean')]} / {wl} / {nl} ({pct(c[('proven', 'lean')], nl)})",
            f"{c[('proven', 'rust')]} / {wr} / {nr} ({pct(c[('proven', 'rust')], nr)})",
        ]) + " |")
    return "\n".join(out)


def git(*a):
    return subprocess.run(["git", "-C", ROOT] + list(a), capture_output=True, text=True).stdout.strip()


def describe(t):
    bits = []
    if t["na"]:
        bits.append(f"not needed: {t['na'][0]} ({t['na'][1]})")
    if t["pending"]:
        bits.append("pending")
    if t["covered"]:
        bits.append("covered")
    for l in t["refs"]:
        st = l["status"]
        if st.startswith("local:"):
            st = "proven locally, sorry via " + ", ".join(f"`{x}`" for x in st.split(":", 1)[1].split(","))
        bits.append(f"`{l['decl']}` ({st})")
    if not t["refs"] and t["impl"]:
        bits.append("L: " + ", ".join(f"`{l['decl']}`" for l in t["impl"]))
    if t["parts"]:
        bits.append("parts: " + ", ".join(f"{l['label']} ({l['status']})" for l in t["parts"]))
    return "; ".join(bits)


def sorry_sources(targets):
    """[(source, [blocked proven-locally targets])], most blocking first."""
    by = collections.defaultdict(set)
    for t in targets.values():
        if t["status"] != "local":
            continue
        for l in t["refs"]:
            if l["status"].startswith("local:"):
                for x in l["status"].split(":", 1)[1].split(","):
                    by[x].add(t["name"])
    return sorted(by.items(), key=lambda kv: (-len(kv[1]), kv[0]))


def write_md(targets, links, dangling, rows, path):
    date = datetime.date.today().isoformat()
    commit = git("rev-parse", "--short", "HEAD")
    o = []
    o.append("# Progress census\n")
    o.append(f"Generated by `scripts/census.py --write` on {date} at `{commit}`; do not edit by hand. "
             "Definitions and rules: `scripts/census.py` (docstring) and PLAN.md, \"Progress census\". "
             "Time series: `_tmp/census/progress.csv`.\n")
    o.append("Targets: the definitions of con-ron's arena twin and of con-leche that "
             "`ConAgua.Final.TwinAccepts` reaches (no instances, auxiliaries, types, predicates or ROM "
             "data). **proven**: refinement proved without `sorry` (or every path to it goes through "
             "a proven target); **sorry**: proved modulo `sorry`, of which **proven locally** are those whose own "
             "proof term has no `sorry` (only constants it uses do); **written**: L code exists; "
             "**todo**: nothing (**pending**: becomes covered when its linked callers are proven); "
             "**n/a**: not needed, deliberately not implemented, listed with reasons in `docs/not-needed.md` and "
             "left out of every share (the \"needed\" column). Weights: Lean code lines of the twin definition, and con-ron Rust "
             "lines citing it.\n")
    o.append("## Summary\n")
    o.append(fmt_table(rows) + "\n")
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
    for t in sorted(targets.values(), key=lambda t: (phase_key(t["phase"]), t["name"])):
        if t["impl"] or t["refs"] or t["parts"]:
            o.append(f"| `{t['name']}` | {t['phase']} | {t['lean']} | {t['rust']} | {t['status']} | {describe(t)} |")
    o.append("")
    write_asm(targets, o)
    srcs = sorry_sources(targets)
    if srcs:
        o.append("## Sorry sources\n")
        o.append("Constants whose own term contains `sorryAx` and through which proven-locally targets get "
                 "theirs (nearest ones), by number of targets blocked. A work queue: fill these in. "
                 "`target?` is the census status of the source when it is a target.\n")
        o.append("| source | blocks | target? | blocked targets |")
        o.append("|---|---:|---|---|")
        for src, ts in srcs:
            st = targets[src]["status"] if src in targets else "-"
            names = ", ".join(f"`{x}`" for x in sorted(ts)[:6]) + (", ..." if len(ts) > 6 else "")
            o.append(f"| `{src}` | {len(ts)} | {st} | {names} |")
        o.append("")
    nal = [t for t in targets.values() if t["na"]]
    if nal:
        o.append("## Not needed (n/a)\n")
        o.append("Source: `docs/not-needed.md`. Excluded from the denominators.\n")
        o.append("| target | phase | lean | reason | deviation |")
        o.append("|---|---|---:|---|---|")
        for t in sorted(nal, key=lambda t: (phase_key(t["phase"]), t["name"])):
            o.append(f"| `{t['name']}` | {t['phase']} | {t['lean']} | {t['na'][0]} | {t['na'][1]} |")
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
    o.append("| module | targets | proven | sorry | of which proven locally | written | todo | pending | n/a | lean lines | rust lines |")
    o.append("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    by_mod = collections.defaultdict(list)
    for t in targets.values():
        by_mod[t["module"]].append(t)
    for m in sorted(by_mod):
        c = totals(by_mod[m])
        o.append(f"| `{m}` | {c[('all', 'n')]} | {c[('proven', 'n')]} | {c[('sorry', 'n')]} | {c[('local', 'n')]} | "
                 f"{c[('written', 'n')]} | {c[('todo', 'n')]} | {c[('pending', 'n')]} | {c[('n/a', 'n')]} | {c[('all', 'lean')]} | {c[('all', 'rust')]} |")
    o.append("")
    open(path, "w").write("\n".join(o))


CSV_FIELDS = ["date", "commit", "targets", "proven", "sorry", "written", "todo",
              "lean_all", "lean_proven", "lean_sorry", "lean_written",
              "rust_all", "rust_proven", "rust_sorry", "rust_written", "parts_proven",
              "local", "lean_local", "na", "lean_na", "rust_na", "pending", "lean_pending",
              "stagec_pct", "cone_pct", "sorry_sources", "layout_leaks"]  # appended at the end: older rows lack them


def append_csv(targets, path):
    c = totals(targets.values())
    row = dict(date=datetime.datetime.now().strftime("%Y-%m-%d %H:%M"), commit=git("rev-parse", "--short", "HEAD"),
               targets=c[("all", "n")], proven=c[("proven", "n")], sorry=c[("sorry", "n")],
               written=c[("written", "n")], todo=c[("todo", "n")],
               lean_all=c[("all", "lean")], lean_proven=c[("proven", "lean")], lean_sorry=c[("sorry", "lean")],
               lean_written=c[("written", "lean")], rust_all=c[("all", "rust")], rust_proven=c[("proven", "rust")],
               rust_sorry=c[("sorry", "rust")], rust_written=c[("written", "rust")],
               parts_proven=sum(1 for t in targets.values() for l in t["parts"] if l["status"] == "ok"),
               local=c[("local", "n")], lean_local=c[("local", "lean")],
               na=c[("n/a", "n")], lean_na=c[("n/a", "lean")], rust_na=c[("n/a", "rust")],
               pending=c[("pending", "n")], lean_pending=c[("pending", "lean")],
               **{k: ("" if v is None else v) for k, v in e2e_metrics(targets).items()})
    new = not os.path.exists(path)
    if not new:  # an older file lacks the newest columns: extend the header, keep the old rows as they are
        lines = open(path, newline="").read().split("\n", 1)
        if lines[0].split(",") != CSV_FIELDS:  # (shares: lean_all minus lean_na is the denominator from the `na` columns on)
            open(path, "w", newline="").write(",".join(CSV_FIELDS) + "\n" + (lines[1] if len(lines) > 1 else ""))
    with open(path, "a", newline="") as fh:
        w = csv.DictWriter(fh, CSV_FIELDS)
        if new:
            w.writeheader()
        w.writerow(row)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--write", action="store_true", help="write _tmp/census/progress.md, append _tmp/census/progress.csv")
    ap.add_argument("--list", nargs="?", const=".", metavar="REGEX", help="list targets")
    ap.add_argument("--no-build", action="store_true", help="do not build the census exe and modules first")
    ap.add_argument("--from-output", metavar="FILE", help="analyse the census exe's saved output instead of running it")
    ap.add_argument("--rust", metavar="DIR", help="regenerate scripts/census-rust.tsv from a con-ron checkout")
    a = ap.parse_args()
    if a.rust:
        regen_rust(a.rust)
        return
    import time
    out = open(a.from_output).read() if a.from_output else run_census(not a.no_build)
    t0 = time.time()
    targets, links, dangling, rust_unmatched, edges = analyse(out)
    stage_done("analyse (weights, statuses, coverage)", t0)
    if a.list:
        rx = re.compile(a.list)
        for t in sorted(targets.values(), key=lambda t: (phase_key(t["phase"]), t["module"], t["start"])):
            if rx.search(t["name"]):
                print(f"{t['phase']}\t{t['status']}\t{t['lean']}\t{t['rust']}\t{t['name']}\t{describe(t)}")
        return
    rows = summary_rows(targets)
    print(fmt_table(rows))
    srcs = sorry_sources(targets)
    if srcs:
        print("\nsorry sources (blocked proven-locally targets):")
        for src, ts in srcs[:10]:
            print(f"  {len(ts):3d}  {src}")
    em = e2e_metrics(targets)
    print("\ncritical path: sorry-free e2e cone " + (f"{em['cone_pct']}% ({ASM['cone'][0]['type']}/{ASM['cone'][0]['name']})" if em["cone_pct"] is not None else "n/a")
          + f"; sorry sources {em['sorry_sources']}")
    nparts = sum(len(t["parts"]) for t in targets.values())
    print(f"\nparts: {nparts} partial refinements "
          f"({sum(1 for t in targets.values() for l in t['parts'] if l['status'] == 'ok')} sorry-free); "
          f"links: {len(links)}; bad links: {len(dangling)}; "
          f"Rust lines citing no target: {rust_unmatched}")
    for l in dangling:
        print(f"  bad link: {l['decl']} ({l['kind']}) -> {l['target']}"
              + (f": {l['status']}" if l["status"].startswith("error") else ": not a target"))
    if a.write:
        t0 = time.time()
        os.makedirs(os.path.join(ROOT, "_tmp", "census"), exist_ok=True)
        write_md(targets, links, dangling, rows, os.path.join(ROOT, "_tmp", "census", "progress.md"))
        append_csv(targets, os.path.join(ROOT, "_tmp", "census", "progress.csv"))
        print("wrote _tmp/census/progress.md, appended _tmp/census/progress.csv")
        stage_done("write report", t0)


if __name__ == "__main__":
    main()
