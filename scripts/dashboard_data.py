#!/usr/bin/env python3
"""Write the progress dashboard's data files to _tmp/dash/ from docs/progress.{md,csv},
docs/velocity.csv, docs/lanes.json and the git worktrees. The coordinator uploads them."""
import json, re, shutil, pathlib, subprocess, time
root = pathlib.Path(__file__).resolve().parent.parent
out = root / "_tmp" / "dash"; out.mkdir(parents=True, exist_ok=True)
md = (root / "docs/progress.md").read_text()
rows = []
for line in md.splitlines():
    m = re.match(r"\| (\d+) ([^|]+?) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) / (\d+) / (\d+) [^|]*\| (\d+) / (\d+) / (\d+) ", line)
    if m:
        g = m.groups()
        rows.append({"phase": int(g[0]), "name": g[1].strip(), "targets": int(g[2]), "proven": int(g[3]),
                     "sorry": int(g[4]), "written": int(g[5]), "todo": int(g[6]),
                     "lean_proven": int(g[7]), "lean_with_l": int(g[8]), "lean_all": int(g[9]),
                     "rust_proven": int(g[10]), "rust_with_l": int(g[11]), "rust_all": int(g[12])})
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
shutil.copy(root / "docs/velocity.csv", out / "velocity.csv")
print("phases:", len(rows), "stale:", len(stale), "running lanes:", sum(l["status"] == "running" for l in lanes))
