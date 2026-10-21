#!/usr/bin/env python3
"""Write the progress dashboard's data files to _tmp/dash/ from docs/progress.{md,csv},
docs/velocity.csv and docs/lanes.json. The coordinator uploads them to the dashboard."""
import csv, json, re, shutil, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
out = root / "_tmp" / "dash"; out.mkdir(parents=True, exist_ok=True)
rows = []
for line in (root / "docs/progress.md").read_text().splitlines():
    m = re.match(r"\| (\d+) ([^|]+?) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) / (\d+) / (\d+) [^|]*\| (\d+) / (\d+) / (\d+) ", line)
    if m:
        g = m.groups()
        rows.append({"phase": int(g[0]), "name": g[1].strip(), "targets": int(g[2]), "proven": int(g[3]),
                     "sorry": int(g[4]), "written": int(g[5]), "todo": int(g[6]),
                     "lean_proven": int(g[7]), "lean_with_l": int(g[8]), "lean_all": int(g[9]),
                     "rust_proven": int(g[10]), "rust_with_l": int(g[11]), "rust_all": int(g[12])})
(out / "phases.json").write_text(json.dumps(rows, indent=1))
shutil.copy(root / "docs/progress.csv", out / "progress.csv")
shutil.copy(root / "docs/velocity.csv", out / "velocity.csv")
shutil.copy(root / "docs/lanes.json", out / "lanes.json")
print("phases:", len(rows))
