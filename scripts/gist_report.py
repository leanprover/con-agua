#!/usr/bin/env python3
"""Render the progress dashboard as a Markdown report (GitHub renders the Mermaid charts) and
publish it to the project's gist.

    scripts/gist_report.py            write _tmp/dash/con-agua-progress.md
    scripts/gist_report.py --publish  also update the gist named in docs/gist.txt (creating it, secret,
                                      when that file is missing)

Reads the files scripts/dashboard_data.py writes (run that first) and docs/deviations.md."""
import csv, json, pathlib, re, subprocess, sys, datetime

root = pathlib.Path(__file__).resolve().parent.parent
dash = root / "_tmp" / "dash"
out = dash / "con-agua-progress.md"


def git(*a):
    return subprocess.run(["git", "-C", str(root), *a], capture_output=True, text=True).stdout.strip()


def bar(frac, width=20):
    n = round(frac * width)
    return "█" * n + "░" * (width - n)


def pct(x):
    return f"{100 * x:.1f}%"


phases = json.loads((dash / "phases.json").read_text())
progress = list(csv.DictReader(open(dash / "progress.csv")))
lanes = json.loads((dash / "lanes.json").read_text())
landings = json.loads((dash / "landings.json").read_text())
velocity = list(csv.DictReader(open(dash / "velocity.csv")))

S = lambda k: sum(p[k] for p in phases)
targets, proven, sorry, written = S("targets"), S("proven"), S("sorry"), S("written")
lean_share = S("lean_proven") / S("lean_all")
rust_share = S("rust_proven") / S("rust_all")
lean_l = S("lean_with_l") / S("lean_all")
work = sum(int(r["work_min"]) for r in velocity)
over = sum(int(r["overhead_min"]) for r in velocity)
running = [l for l in lanes if l["status"] == "running"]
done = [l for l in lanes if l["status"] == "done"]

dev_open = 0
devf = root / "docs" / "deviations.md"
if devf.exists():
    for line in devf.read_text().splitlines():
        if re.match(r"\|\s*D\d+", line) and "fixed" not in line.lower():
            dev_open += 1

now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
head = git("rev-parse", "--short", "HEAD")
L = []
w = L.append
w("# con-agua: a Lean checker in verified x64\n")
w(f"_Progress report, generated {now} from master `{head}` by `scripts/gist_report.py`._\n")
w(f"**{proven} of {targets}** functions of con-ron's checker have L code refined against con-ron's model, "
  f"down to verified x64: **{pct(lean_share)}** of the model by Lean lines, **{pct(rust_share)}** by Rust lines.\n")
w("| Proven (count) | Proven (Lean lines) | Proven (Rust lines) | L written (Lean lines) | Proven with `sorry` | Lanes running | Merge overhead |")
w("|---:|---:|---:|---:|---:|---:|---:|")
w(f"| {proven} / {targets} | {pct(lean_share)} | {pct(rust_share)} | {pct(lean_l)} | {sorry} | {len(running)} | {pct(over / max(1, work + over))} |\n")

# trend chart
pts = progress[-30:]
labels = [p["date"][5:16].replace(" ", " ") for p in pts]
lean = [round(100 * int(p["lean_proven"]) / int(p["lean_all"]), 1) for p in pts]
cnt = [round(100 * int(p["proven"]) / int(p["targets"]), 1) for p in pts]
wr = [round(100 * (int(p["lean_proven"]) + int(p["lean_sorry"]) + int(p["lean_written"])) / int(p["lean_all"]), 1) for p in pts]
top = max(wr + lean + cnt + [10])
w("## Proven over time\n")
w("Share of the twin proven by Lean lines (first line), by target count (second), and with L code written (third), one point per census run.\n")
w("```mermaid")
w("xychart-beta")
w('    title "Proven share (%) per census run"')
w("    x-axis [" + ", ".join(f'"{l}"' for l in labels) + "]")
w(f'    y-axis "%" 0 --> {min(100, int(top) + 5)}')
w("    line [" + ", ".join(map(str, lean)) + "]")
w("    line [" + ", ".join(map(str, cnt)) + "]")
w("    line [" + ", ".join(map(str, wr)) + "]")
w("```\n")

# phases
w("## By phase\n")
w("Lean lines of con-ron's arena twin per phase. Bar: █ proven, ░ not yet.\n")
w("| Phase | Proven | | Targets proven / sorry / L only / todo |")
w("|---|---|---:|---|")
for p in phases:
    f = p["lean_proven"] / p["lean_all"] if p["lean_all"] else 0
    w(f"| {p['phase']} {p['name']} | `{bar(f)}` | {pct(f)} | {p['proven']} / {p['sorry']} / {p['written']} / {p['todo']} of {p['targets']} |")
w("")
w("```mermaid")
w("xychart-beta")
w('    title "Proven share by phase (% of Lean lines)"')
w("    x-axis [" + ", ".join(f'"{p["phase"]}"' for p in phases) + "]")
w('    y-axis "%" 0 --> 100')
w("    bar [" + ", ".join(str(round(100 * p["lean_proven"] / p["lean_all"], 1)) if p["lean_all"] else "0" for p in phases) + "]")
w("```\n")

# lanes
w(f"## Lanes ({len(running)} running, {len(done)} finished)\n")
w("| Lane | Model | Helpers | Last commit | Focus |")
w("|---|---|---:|---|---|")
for l in running:
    lc = l.get("last_commit_min")
    lc = "" if lc is None else (f"{lc} min ago" if lc < 90 else f"{round(lc / 60)} h ago")
    w(f"| **{l['lane']}** | {l['model']} | {l.get('helpers') or ''} | {lc} | {l['focus']} |")
w("")
w("<details><summary>Finished lanes</summary>\n")
w("| Lane | Model | Focus |")
w("|---|---|---|")
for l in reversed(done):
    w(f"| {l['lane']} | {l['model']} | {l['focus']} |")
w("\n</details>\n")

# landings
w("## Recent landings on master\n")
w("| When (UTC) | Lane | What landed |")
w("|---|---|---|")
for r in landings[:20]:
    w(f"| {r['at'][5:16].replace('T', ' ')} | {r['lane']} | {r['what'].replace('|', '/')} |")
w("")
w(f"Open deviations from the twin (`docs/deviations.md`): **{dev_open}**.\n")

out.write_text("\n".join(L) + "\n")
print("wrote", out)

if "--publish" in sys.argv:
    gf = root / "docs" / "gist.txt"
    if gf.exists():
        gid = gf.read_text().strip()
        subprocess.run(["gh", "gist", "edit", gid, "-f", out.name, str(out)], check=True)
        print("updated gist", gid)
    else:
        r = subprocess.run(["gh", "gist", "create", "--desc", "con-agua progress", str(out)],
                           capture_output=True, text=True, check=True)
        url = r.stdout.strip().splitlines()[-1]
        gf.write_text(url.rsplit("/", 1)[-1] + "\n")
        print("created gist", url)
