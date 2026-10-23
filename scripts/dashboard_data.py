#!/usr/bin/env python3
"""Write the progress dashboard's data files to _tmp/dash/ from docs/progress.{md,csv},
docs/velocity.csv, docs/lanes.json and the git worktrees. The coordinator uploads them."""
import json, re, shutil, pathlib, subprocess, time
root = pathlib.Path(__file__).resolve().parent.parent
out = root / "_tmp" / "dash"; out.mkdir(parents=True, exist_ok=True)
md = (root / "docs/progress.md").read_text()
rows = []
for line in md.splitlines():
    m = re.match(r"\| (\d+[a-z]?) ([^|]+?) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) / (\d+) / (\d+) [^|]*\| (\d+) / (\d+) / (\d+) ", line)
    if m:
        g = m.groups()
        # columns: targets proven sorry local written todo pending n/a n/a-lean; lean and rust "proven / with L / needed"
        # (needed = all minus n/a); "targets" is reported minus n/a as well
        rows.append({"phase": g[0], "name": g[1].strip(), "targets": int(g[2]) - int(g[9]), "proven": int(g[3]),
                     "sorry": int(g[4]), "local": int(g[5]), "written": int(g[6]), "todo": int(g[7]),
                     "pending": int(g[8]), "na": int(g[9]), "lean_na": int(g[10]),
                     "lean_proven": int(g[11]), "lean_with_l": int(g[12]), "lean_all": int(g[13]),
                     "rust_proven": int(g[14]), "rust_with_l": int(g[15]), "rust_all": int(g[16])})
(out / "phases.json").write_text(json.dumps(rows, indent=1))
# upstream changes: the CHANGED markers `scripts/provenance.py check` lists as its queue
stale = []
chk = subprocess.run(["python3", str(root / "scripts/provenance.py"), "check"], cwd=root, capture_output=True, text=True).stdout
owners = [("Ind", "indproofs"), ("Whnf", "whnf"), ("Core", "whnf"), ("Level", "whnf"), ("Checker", "decls"), ("Decl", "decls"),
          ("Rom", "decls"), ("Env", "decls"), ("Pins", "decls"), ("Front", "front"), ("Scan", "front")]
for line in chk.splitlines():
    m = re.match(r"queue: (\S+):(\d+) — (.*)", line)
    if m:
        f = m.group(1)
        owner = next((o for k, o in owners if k in f), "")
        stale.append({"target": f"{f}:{m.group(2)}", "status": "CHANGED", "phase": "", "owner": owner, "theorems": m.group(3)})
(out / "stale.json").write_text(json.dumps(stale, indent=1))
# lanes with helper worktrees and last-commit age
lanes = json.loads((root / "docs/lanes.json").read_text())
wt = subprocess.run(["git", "-C", str(root), "worktree", "list", "--porcelain"], capture_output=True, text=True).stdout
paths = [l.split(" ", 1)[1] for l in wt.splitlines() if l.startswith("worktree ")]
now = time.time()
def age(p):
    r = subprocess.run(["git", "-C", p, "log", "-1", "--format=%ct"], capture_output=True, text=True).stdout.strip()
    return round((now - int(r)) / 60) if r else None
for l in lanes:
    l["helpers"] = 0; l["last_commit_min"] = None
    if l["status"] != "running": continue
    mine = [p for p in paths if pathlib.Path(p).name == l["lane"]]
    helpers = [p for p in paths if pathlib.Path(p).name.startswith(l["lane"] + "-")]
    l["helpers"] = len(helpers)
    ages = [a for a in map(age, mine + helpers) if a is not None]
    l["last_commit_min"] = min(ages) if ages else None
(out / "lanes.json").write_text(json.dumps(lanes, indent=1))
shutil.copy(root / "docs/progress.csv", out / "progress.csv")
m = re.search(r"<!-- assumptions-json (.*?) -->", md)  # census.py's section of progress.md
if m:
    (out / "assumptions.json").write_text(m.group(1))
for f in ("assumption-owners.json",):
    if (root / "docs" / f).exists():
        shutil.copy(root / "docs" / f, out / f)
# velocity: repair rows with unquoted commas in the note (lanes append by hand)
import csv
vrows = list(csv.reader(open(root / "docs/velocity.csv")))
with open(out / "velocity.csv", "w", newline="") as f:
    csv.writer(f, lineterminator="\n").writerows([r[:5] + [",".join(r[5:])] if len(r) > 6 else r for r in vrows])
# landings: master's merge commits, newest first (authoritative; velocity notes are optional)
lg = subprocess.run(["git", "-C", str(root), "log", "--first-parent", "master", "--merges", "-40",
                     "--format=%cI%x09%s"], capture_output=True, text=True).stdout
landings = []
for i, line in enumerate(lg.splitlines()):
    at, subj = line.split("\t", 1)
    m = re.match(r"Merge (?:branch )?'?([\w-]+)'?(?: into \w+)?\s*(?:\((.*)\))?", subj)
    lane = m.group(1) if m else ""
    what = (m.group(2) if m and m.group(2) else subj)
    landings.append({"n": i + 1, "at": at, "lane": lane, "what": what})
(out / "landings.json").write_text(json.dumps(landings, indent=1))
print("phases:", len(rows), "stale:", len(stale), "running lanes:", sum(l["status"] == "running" for l in lanes))
