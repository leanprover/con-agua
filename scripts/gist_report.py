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


def raw_url(name):
    gf = root / "docs" / "gist.txt"
    gid = gf.read_text().strip() if gf.exists() else "GIST"
    # the query string defeats GitHub's image cache between updates
    # a hash of the file's content defeats GitHub's image cache exactly when the image changed
    import hashlib
    f = dash / name
    v = hashlib.sha1(f.read_bytes()).hexdigest()[:10] if f.exists() else git('rev-parse', '--short', 'HEAD')
    return f"https://gist.githubusercontent.com/nomeata/{gid}/raw/{name}?v={v}"


def phases_svg():
    """Horizontal stacked bars, one per phase, length = the phase's Lean lines."""
    W, bh, gap, lw, rw = 900, 22, 10, 230, 150
    H = len(phases) * (bh + gap) + 50
    mx = max(p["lean_all"] for p in phases)
    sc = (W - lw - rw) / mx
    cols = [("proven", "#2e7d5b"), ("sorry", "#d9a520"), ("L only", "#7aa6d6"), ("todo", "#d0d0d0")]
    o = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" font-family="Helvetica, Arial, sans-serif" font-size="13">',
         f'<rect width="{W}" height="{H}" fill="#ffffff"/>']
    for i, p in enumerate(phases):
        y = 10 + i * (bh + gap)
        lp = p["lean_proven"]
        # Lean lines with sorry are not in phases.json; split "with L but not proven" by the target counts
        rest_l = p["lean_with_l"] - lp
        ns, nw = p["sorry"], p["written"]
        ls = round(rest_l * ns / (ns + nw)) if ns + nw else 0
        segs = [lp, ls, rest_l - ls, p["lean_all"] - p["lean_with_l"]]
        o.append(f'<text x="{lw - 8}" y="{y + bh / 2 + 4}" text-anchor="end" fill="#222">{p["phase"]} {p["name"]}</text>')
        x = lw
        for (name, c), v in zip(cols, segs):
            if v > 0:
                o.append(f'<rect x="{x:.1f}" y="{y}" width="{v * sc:.1f}" height="{bh}" fill="{c}"/>')
                x += v * sc
        f = lp / p["lean_all"] if p["lean_all"] else 0
        o.append(f'<text x="{x + 6:.1f}" y="{y + bh / 2 + 4}" fill="#555">{100 * f:.0f}% · {p["proven"]}/{p["targets"]}</text>')
    ly = H - 22
    x = lw
    for name, c in cols:
        o.append(f'<rect x="{x}" y="{ly}" width="12" height="12" fill="{c}"/><text x="{x + 17}" y="{ly + 11}" fill="#333">{name}</text>')
        x += 95
    o.append("</svg>")
    return "\n".join(o) + "\n"


def loc_series(commits):
    """Lines of L code and of proofs at each census commit (scripts/loc.py), cached by commit."""
    cache_f = dash / "loc-cache.json"
    try:
        cache = json.loads(cache_f.read_text())
    except Exception:
        cache = {}
    todo = [c for c in commits if c not in cache]
    if todo:
        r = subprocess.run([sys.executable, str(root / "scripts" / "loc.py"), *todo], capture_output=True, text=True)
        for line in r.stdout.splitlines():
            c, l, p = line.split(",")
            cache[c] = [int(l), int(p)]
        cache_f.write_text(json.dumps(cache))
    return [cache.get(c, [0, 0]) for c in commits]


def trend_svg(pts):
    """Proven shares (left axis, %) and lines of L code / proofs (right axis, thousands) per census run."""
    W, H, ml, mr, mt, mb = 900, 360, 50, 70, 20, 70
    n = len(pts)
    xs = [ml + (W - ml - mr) * (i / max(1, n - 1)) for i in range(n)]
    lean = [100 * int(p["lean_proven"]) / int(p["lean_all"]) for p in pts]
    cnt = [100 * (int(p["lean_proven"]) + int(p.get("lean_sorry") or 0)) / int(p["lean_all"]) for p in pts]
    wr = [100 * (int(p["lean_proven"]) + int(p["lean_sorry"]) + int(p["lean_written"])) / int(p["lean_all"]) for p in pts]
    loc = loc_series([p["commit"] for p in pts])
    lk = [a / 1000 for a, _ in loc]; pk = [b / 1000 for _, b in loc]
    ytop = 100
    ktop = max(pk + lk + [1])
    step = 50 if ktop > 200 else 25 if ktop > 100 else 10
    ktop = (int(ktop / step) + 1) * step
    yl = lambda v: mt + (H - mt - mb) * (1 - v / ytop)
    yr = lambda v: mt + (H - mt - mb) * (1 - v / ktop)
    o = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" font-family="Helvetica, Arial, sans-serif" font-size="12">',
         f'<rect width="{W}" height="{H}" fill="#ffffff"/>']
    for t in range(0, ytop + 1, 10):
        o.append(f'<line x1="{ml}" x2="{W - mr}" y1="{yl(t):.1f}" y2="{yl(t):.1f}" stroke="#eeeeee"/>')
        o.append(f'<text x="{ml - 6}" y="{yl(t) + 4:.1f}" text-anchor="end" fill="#666">{t}%</text>')
    for t in range(0, ktop + 1, step):
        o.append(f'<text x="{W - mr + 6}" y="{yr(t) + 4:.1f}" fill="#666">{t}k</text>')
    for i, p in enumerate(pts):
        if n <= 12 or i % max(1, n // 10) == 0 or i == n - 1:
            o.append(f'<text x="{xs[i]:.1f}" y="{H - mb + 16}" text-anchor="end" fill="#666" transform="rotate(-35 {xs[i]:.1f} {H - mb + 16})">{p["date"][5:16]}</text>')
    def line(vals, y, color, dash=""):
        d = " ".join(f"{'M' if i == 0 else 'L'}{xs[i]:.1f},{y(v):.1f}" for i, v in enumerate(vals))
        o.append(f'<path d="{d}" fill="none" stroke="{color}" stroke-width="2" stroke-linejoin="round" {dash}/>')
    series = [("proven", lean, yl, "#2e7d5b", ""), ("proven, counting sorry", cnt, yl, "#7aa6d6", ""),
              ("L written", wr, yl, "#d9a520", ""),
              ("proof lines (k)", pk, yr, "#8a5cb8", 'stroke-dasharray="6 4"'), ("L code lines (k)", lk, yr, "#c0504d", 'stroke-dasharray="6 4"')]
    for name, vals, y, c, dash in series:
        line(vals, y, c, dash)
    lx = ml
    for name, vals, y, c, dash in series:
        o.append(f'<line x1="{lx}" x2="{lx + 22}" y1="{H - 12}" y2="{H - 12}" stroke="{c}" stroke-width="2" {dash}/>'
                 f'<text x="{lx + 27}" y="{H - 8}" fill="#333">{name}</text>')
        lx += 170
    o.append("</svg>")
    return "\n".join(o) + "\n"


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
# the images first: the report links them by a hash of their content
(dash / "phases.svg").write_text(phases_svg())
(dash / "trend.svg").write_text(trend_svg(progress[-40:]))

S = lambda k: sum(p[k] for p in phases)
targets, proven, sorry, written = S("targets"), S("proven"), S("sorry"), S("written")
lean_share = S("lean_proven") / S("lean_all")
rust_share = S("rust_proven") / S("rust_all")
lean_l = S("lean_with_l") / S("lean_all")
work = sum(int(r["work_min"]) for r in velocity)
over = sum(int(r["overhead_min"]) for r in velocity)
running = [l for l in lanes if l["status"] == "running"]

def eta():
    """Least-squares rate of Lean lines proven per day over the census runs of the last 3 days,
    and the date the rest would be done at that rate (as on the dashboard)."""
    pts = [(datetime.datetime.fromisoformat(r["date"].replace(" ", "T") + ":00+00:00").timestamp() / 86400,
            int(r["lean_proven"]), int(r["lean_all"])) for r in progress]
    last = pts[-1]
    win = [q for q in pts if q[0] >= last[0] - 3]
    if len(win) < 2:
        return None, None
    mt = sum(q[0] for q in win) / len(win); mp = sum(q[1] for q in win) / len(win)
    sxx = sum((q[0] - mt) ** 2 for q in win); sxy = sum((q[0] - mt) * (q[1] - mp) for q in win)
    rate = sxy / sxx if sxx else 0
    if rate <= 0:
        return None, rate
    when = datetime.datetime.fromtimestamp((last[0] + (last[2] - last[1]) / rate) * 86400, datetime.timezone.utc)
    return when, rate
eta_when, eta_rate = eta()
done = [l for l in lanes if l["status"] == "done"]

dev_open = 0
devf = root / "docs" / "deviations.md"
if devf.exists():
    for line in devf.read_text().splitlines():
        if re.match(r"\|\s*D\d+", line) and "fixed" not in line.lower():
            dev_open += 1  # superseded by the per-section counts below

now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
head = git("rev-parse", "--short", "HEAD")
L = []
w = L.append
w("# con-agua: a Lean checker in verified x64\n")
w(f"_Progress report, generated {now} from master `{head}` by `scripts/gist_report.py`._\n")
w(f"**{proven} of {targets}** functions of con-ron's checker have L code refined against con-ron's model, "
  f"down to verified x64: **{pct(lean_share)}** of the model. Percentages are of the twin's Lean lines.\n")
w("| Proven | Proven, counting `sorry` | L written | Projected completion | Lanes running | Merge overhead |")
w("|---:|---:|---:|---:|---:|---:|")
eta_s = eta_when.strftime("%b %-d") if eta_when else "—"
sorry_share = int(progress[-1]["lean_sorry"]) / int(progress[-1]["lean_all"]) if progress and progress[-1].get("lean_sorry") else None
w(f"| **{pct(lean_share)}** | {pct(lean_share + sorry_share) if sorry_share is not None else '—'} | {pct(lean_l)} | **{eta_s}** | {len(running)} | {pct(over / max(1, work + over))} |\n")
w("_The three shares are cumulative: proven ⊆ proven counting `sorry` (also proofs that rest on unproven callees) ⊆ L code written._\n")
# the safety net under the shared Lake cache (DESIGN.md, "Cache incident"), written by scripts/buildstats.py
bcf = root / "_tmp" / "buildcheck.json"
if bcf.exists():
    bc = json.loads(bcf.read_text())
    behind = git("rev-list", "--count", f"{bc['commit']}..HEAD") if bc.get("commit", "?") != "?" else "?"
    w(f"Last cache-free build of master: `{bc['commit'][:10]}` ({behind} commits behind HEAD, {bc['date']}, "
      f"{bc['mode']}): " + ("**OK**" if bc["ok"] else f"**FAILED** ({bc['detail']})") + "\n")
else:
    w("Last cache-free build of master: **none recorded** (run `scripts/buildstats.py`).\n")
if eta_rate:
    w(f"_Projected completion: at the least-squares rate of the last 3 days of census runs, {eta_rate:,.0f} Lean lines proven per day; "
      "a straight-line extrapolation, so treat it as a trend, not a promise._\n")

# trend chart
pts = progress[-30:]
labels = [p["date"][5:16].replace(" ", " ") for p in pts]
lean = [round(100 * int(p["lean_proven"]) / int(p["lean_all"]), 1) for p in pts]
cnt = [round(100 * int(p["proven"]) / int(p["targets"]), 1) for p in pts]
wr = [round(100 * (int(p["lean_proven"]) + int(p["lean_sorry"]) + int(p["lean_written"])) / int(p["lean_all"]), 1) for p in pts]
top = max(wr + lean + cnt + [10])
w("## Proven over time\n")
w("Left axis: share of the twin's Lean lines proven, proven counting `sorry` (proofs resting on unproven callees), and with L code written. "
  "Right axis: lines of L code and of proofs in `ConAgua/` (thousands), so infrastructure work shows too. One point per census run.\n")
w(f"![Proven share and lines of code per census run]({raw_url('trend.svg')})\n")

# phases
w("## By phase\n")
w("Lean lines of con-ron's arena twin per phase.\n")
w(f"![Lean lines per phase: proven, proven with sorry, L written, not started]({raw_url('phases.svg')})\n")

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
# deviations, by section (docs/deviations.md: Temporary, Deliberate, Fixed)
def dev_rows(section):
    if not devf.exists():
        return []
    txt = devf.read_text()
    if f"\n## {section}\n" not in txt:
        return []
    sec = re.split(r"\n## ", txt.split(f"\n## {section}\n", 1)[1], maxsplit=1)[0]
    rows = []
    for line in sec.splitlines():
        m = re.match(r"\|\s*(D\d+)\s*\|(.*)\|\s*$", line)
        if m:
            cells = [c.strip() for c in m.group(2).split("|")]
            if len(cells) >= 6:
                rows.append((m.group(1), cells))
    return rows

def short(t, n=140):
    t = re.sub(r"\s+", " ", t)
    return t if len(t) <= n else t[:n - 1].rstrip() + "…"

def dev_table(title, intro, rows, last_col):
    rows = [(d, c) for d, c in rows if not c[3].strip().lower().startswith("none")]
    w(f"### {title} ({len(rows)})\n")
    w(intro + "\n")
    if not rows:
        return
    w(f"| id | effect | deviation | owner | {last_col} |")
    w("|---|---|---|---|---|")
    for did, c in rows:
        kind = re.split(r"[\s(;,]", c[3].strip(), maxsplit=1)[0] or c[3]
        if kind.lower().startswith("none"):
            continue  # representation only: not visible to users, not reported
        where = re.sub(r"`", "", c[0]).split(";")[0]
        dev = f"**twin:** {short(c[1], 150)}<br>**L:** {short(c[2], 150)}<br><sub>{short(where, 80)}</sub>"
        w(f"| {did} | {kind} | {dev} | {short(c[4], 40)} | {short(c[5], 110)} |")
    w("")

w("## Deviations from the twin\n")
w("Places where L does something other than con-ron beyond fuel and fixed capacities, from `docs/deviations.md`. "
  "Effect: completeness = L declines where the twin accepts; performance = same verdicts, more work or memory. Representation-only differences (no visible effect) are not listed.\n")
dev_table("Temporary: to be fixed", "L differs from the twin for now; each row has an owner and a fix.", dev_rows("Temporary"), "fix")
dev_table("Deliberate: by design", "L differs from the twin on purpose and stays that way.", dev_rows("Deliberate"), "why")

out.write_text("\n".join(L) + "\n")
print("wrote", out)

if "--publish" in sys.argv:
    gf = root / "docs" / "gist.txt"
    if gf.exists():
        gid = gf.read_text().strip()
        subprocess.run(["gh", "gist", "edit", gid, "-f", out.name, str(out)], check=True)
        for extra in ("phases.svg", "trend.svg", "progress.csv", "lanes.json"):  # the chart, and the census history (durable copy)
            r = subprocess.run(["gh", "gist", "edit", gid, "-f", extra, str(dash / extra)])
            if r.returncode != 0:  # first time: add the file
                subprocess.run(["gh", "gist", "edit", gid, "-a", str(dash / extra)], check=True)
        print("updated gist", gid)
    else:
        r = subprocess.run(["gh", "gist", "create", "--desc", "con-agua progress", str(out)],
                           capture_output=True, text=True, check=True)
        url = r.stdout.strip().splitlines()[-1]
        gf.write_text(url.rsplit("/", 1)[-1] + "\n")
        print("created gist", url)
