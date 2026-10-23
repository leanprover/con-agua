#!/usr/bin/env python3
"""Render the progress dashboard as a Markdown report (GitHub renders the Mermaid charts) and
publish it to the project's gist.

    scripts/gist_report.py            write _tmp/dash/con-agua-progress.md
    scripts/gist_report.py --publish  also update the gist named in docs/gist.txt (creating it, secret,
                                      when that file is missing)

Reads the files scripts/dashboard_data.py writes (run that first) and docs/deviations.md."""
import datetime
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
    W, bh, gap, lw, rw = 940, 22, 10, 270, 150
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


def den(p):
    """Denominator of the shares: the twin's Lean lines minus the not-needed (n/a) ones. Census rows
    before the n/a status (2026-10-23) have no `lean_na` column: nothing was n/a then."""
    return int(p["lean_all"]) - int(p.get("lean_na") or 0)


def trend_svg(pts):
    """Proven shares (left axis, %) and lines of L code / proofs (right axis, thousands) per census run."""
    W, H, ml, mr, mt, mb = 900, 395, 50, 70, 20, 105
    n = len(pts)
    # x is time (not run index), so the whole history keeps its real proportions
    ts = [datetime.datetime.strptime(p["date"][:16], "%Y-%m-%d %H:%M").timestamp() for p in pts]
    t0, t1 = ts[0], max(ts[-1], ts[0] + 1)
    xs = [ml + (W - ml - mr) * (t - t0) / (t1 - t0) for t in ts]
    lean = [100 * int(p["lean_proven"]) / den(p) for p in pts]
    cnt = [100 * (int(p["lean_proven"]) + int(p.get("lean_local") or p.get("lean_sorry") or 0)) / den(p) for p in pts]
    wr = [100 * (int(p["lean_proven"]) + int(p["lean_sorry"]) + int(p["lean_written"])) / den(p) for p in pts]
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
    span_h = (t1 - t0) / 3600
    every = next(h for h in (1, 2, 3, 6, 12, 24, 48, 168, 10**6) if span_h / h <= 12)
    tick = datetime.datetime.fromtimestamp(t0).replace(minute=0, second=0, microsecond=0)
    while tick.timestamp() <= t1:
        if tick.timestamp() >= t0 and tick.hour % min(every, 24) == 0:
            x = ml + (W - ml - mr) * (tick.timestamp() - t0) / (t1 - t0)
            o.append(f'<line x1="{x:.1f}" x2="{x:.1f}" y1="{mt}" y2="{H - mb}" stroke="#f3f3f3"/>')
            o.append(f'<text x="{x:.1f}" y="{H - mb + 16}" text-anchor="end" fill="#666" transform="rotate(-35 {x:.1f} {H - mb + 16})">{tick.strftime("%m-%d %H:%M")}</text>')
        tick += datetime.timedelta(hours=1)
    def line(vals, y, color, dash=""):
        # vals may hold None (older census rows lack the critical-path columns): those points are skipped
        d = " ".join(f"{'M' if i == 0 else 'L'}{xs[i]:.1f},{y(v):.1f}" for i, v in enumerate(vals) if v is not None)
        d = "M" + d[1:] if d else d
        if not d:
            return
        o.append(f'<path d="{d}" fill="none" stroke="{color}" stroke-width="2" stroke-linejoin="round" {dash}/>')
    def col(k):
        return [float(p[k]) if p.get(k) not in (None, "") else None for p in pts]
    srcs = col("sorry_sources")
    n0 = next((v for v in srcs if v), None)  # first recorded count of sorry sources
    elim = [None if v is None or not n0 else 100 * (1 - v / n0) for v in srcs]
    series = [("proven", lean, yl, "#2e7d5b", ""), ("proven locally", cnt, yl, "#7aa6d6", ""),
              ("L written", wr, yl, "#d9a520", ""),
              ("StageC migration", col("stagec_pct"), yl, "#e07b39", ''),
              ("sorry-free e2e cone", col("cone_pct"), yl, "#1b1b1b", 'stroke-dasharray="2 3"'),
              (f"sorry sources removed (of {int(n0) if n0 else '?'})", elim, yl, "#d6457f", 'stroke-dasharray="10 3 2 3"'),
              ("proof lines (k)", pk, yr, "#8a5cb8", 'stroke-dasharray="6 4"'), ("L code lines (k)", lk, yr, "#c0504d", 'stroke-dasharray="6 4"')]
    for name, vals, y, c, dash in series:
        line(vals, y, c, dash)
    # legend: two rows of four (the labels do not fit in one row)
    for i, (name, vals, y, c, dash) in enumerate(series):
        lx = ml + (i % 4) * 205
        ly = H - 30 + 18 * (i // 4)
        o.append(f'<line x1="{lx}" x2="{lx + 22}" y1="{ly}" y2="{ly}" stroke="{c}" stroke-width="2" {dash}/>'
                 f'<text x="{lx + 27}" y="{ly + 4}" fill="#333">{name}</text>')
    o.append("</svg>")
    return "\n".join(o) + "\n"


def perf_data():
    """The per-fixture instruction counts scripts/e2e.py writes (_tmp/e2e/latest/results.json), or None."""
    try:
        d = json.loads((root / "_tmp" / "e2e" / "latest" / "results.json").read_text())
        d["rows"] = [r for r in d["rows"] if r["perf"].get("L") and r["perf"].get("con-ron")]
        return d if d["rows"] else None
    except Exception:
        return None


def perf_svg(rows):
    """Left: L vs con-ron instructions per fixture (log-log, guides y=x and y=10x). Right: ratio vs input size."""
    import math
    W, H, mt, mb = 940, 440, 24, 64
    pw = 380
    panels = [(80, 80 + pw), (545, 545 + pw)]
    xs = [r["perf"]["con-ron"] for r in rows]; ys = [r["perf"]["L"] for r in rows]
    lo = 10 ** math.floor(math.log10(min(xs + ys))); hi = 10 ** math.ceil(math.log10(max(xs + ys)))
    sz = [max(1, r["size"]) for r in rows]; rt = [r["perf"]["L"] / r["perf"]["con-ron"] for r in rows]
    slo = 10 ** math.floor(math.log10(min(sz))); shi = 10 ** math.ceil(math.log10(max(sz)))
    rlo = 10 ** math.floor(math.log10(min(rt + [1]))); rhi = 10 ** math.ceil(math.log10(max(rt + [10])))
    def sc(v, a, b, p0, p1):
        return p0 + (p1 - p0) * (math.log10(v) - math.log10(a)) / (math.log10(b) - math.log10(a))
    def si(v):
        e = round(math.log10(v))
        return f"1e{e}" if e >= 4 else f"{v:g}"
    o = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" font-family="Helvetica, Arial, sans-serif" font-size="12">',
         f'<rect width="{W}" height="{H}" fill="#ffffff"/>']
    def frame(x0, x1, ax, ay, xlab, ylab, title):
        y0, y1 = mt + 10, H - mb
        o.append(f'<text x="{(x0 + x1) / 2}" y="{mt - 6}" text-anchor="middle" fill="#222" font-size="13" font-weight="bold">{title}</text>')
        for (a, b, horiz) in ((ax[0], ax[1], False), (ay[0], ay[1], True)):
            e = round(math.log10(a))
            while 10 ** e <= b * 1.0001:
                v = 10.0 ** e
                if horiz:
                    y = sc(v, ay[0], ay[1], y1, y0)
                    o.append(f'<line x1="{x0}" x2="{x1}" y1="{y:.1f}" y2="{y:.1f}" stroke="#eeeeee"/>'
                             f'<text x="{x0 - 6}" y="{y + 4:.1f}" text-anchor="end" fill="#666">{si(v)}</text>')
                else:
                    x = sc(v, ax[0], ax[1], x0, x1)
                    o.append(f'<line x1="{x:.1f}" x2="{x:.1f}" y1="{y0}" y2="{y1}" stroke="#eeeeee"/>'
                             f'<text x="{x:.1f}" y="{y1 + 16}" text-anchor="middle" fill="#666">{si(v)}</text>')
                e += 1
        o.append(f'<rect x="{x0}" y="{y0}" width="{x1 - x0}" height="{y1 - y0}" fill="none" stroke="#999"/>')
        o.append(f'<text x="{(x0 + x1) / 2}" y="{H - 28}" text-anchor="middle" fill="#333">{xlab}</text>')
        o.append(f'<text transform="translate({x0 - 52} {(y0 + y1) / 2}) rotate(-90)" text-anchor="middle" fill="#333">{ylab}</text>')
        return y0, y1
    (a0, a1), (b0, b1) = panels
    y0, y1 = frame(a0, a1, (lo, hi), (lo, hi), "con-ron instructions (user)", "L instructions (user)", "Instructions per fixture")
    for k, c, name in ((1, "#999999", "y = x"), (10, "#c0504d", "y = 10x")):
        pts = [(v, v * k) for v in (lo, hi)]
        # clip the guide to the plot box
        t0, t1 = max(lo, lo / k), min(hi, hi / k)
        if t0 < t1:
            o.append(f'<line x1="{sc(t0, lo, hi, a0, a1):.1f}" y1="{sc(t0 * k, lo, hi, y1, y0):.1f}" x2="{sc(t1, lo, hi, a0, a1):.1f}" '
                     f'y2="{sc(t1 * k, lo, hi, y1, y0):.1f}" stroke="{c}" stroke-dasharray="5 4"/>'
                     f'<text x="{sc(t1, lo, hi, a0, a1) - 4:.1f}" y="{sc(t1 * k, lo, hi, y1, y0) + 14:.1f}" text-anchor="end" fill="{c}">{name}</text>')
    for x, y in zip(xs, ys):
        o.append(f'<circle cx="{sc(x, lo, hi, a0, a1):.1f}" cy="{sc(y, lo, hi, y1, y0):.1f}" r="2.6" fill="#2e6fb5" fill-opacity="0.55"/>')
    y0, y1 = frame(b0, b1, (slo, shi), (rlo, rhi), "input size (bytes)", "L / con-ron instructions", "Ratio by input size")
    gm = math.exp(sum(math.log(v) for v in rt) / len(rt))
    for k, c, dsh in ((1, "#999999", "5 4"), (gm, "#2e7d5b", "2 3")):
        if rlo <= k <= rhi:
            y = sc(k, rlo, rhi, y1, y0)
            o.append(f'<line x1="{b0}" x2="{b1}" y1="{y:.1f}" y2="{y:.1f}" stroke="{c}" stroke-dasharray="{dsh}"/>'
                     f'<text x="{b1 - 4}" y="{y - 4:.1f}" text-anchor="end" fill="{c}">{"parity" if k == 1 else f"geometric mean {gm:.2f}"}</text>')
    for x, y in zip(sz, rt):
        o.append(f'<circle cx="{sc(x, slo, shi, b0, b1):.1f}" cy="{sc(y, rlo, rhi, y1, y0):.1f}" r="2.6" fill="#8a5cb8" fill-opacity="0.55"/>')
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
(dash / "trend.svg").write_text(trend_svg(progress))
perf = perf_data()
if perf:
    (dash / "perf.svg").write_text(perf_svg(perf["rows"]))

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
            int(r["lean_proven"]), den(r)) for r in progress]
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

def _shorten(t, n=110):
    t = re.sub(r"\s+", " ", t)
    return t if len(t) <= n else t[:n - 1].rstrip() + "…"


def assumptions_section(w):
    """"What the end-to-end theorem still assumes": from _tmp/dash/assumptions.json (census.py's
    section of progress.md, extracted by dashboard_data.py) and docs/assumption-owners.json."""
    f = dash / "assumptions.json"
    if not f.exists():
        return
    try:
        d = json.loads(f.read_text())
        of = root / "docs" / "assumption-owners.json"
        own = json.loads(of.read_text()) if of.exists() else {}
    except (ValueError, OSError):
        return
    hyps, srcs = d.get("hyps", []), d.get("sorry_sources", [])
    owners = own.get("hyps", {})
    named = [h for h in hyps if h["name"] in owners]
    other = [h["name"] for h in hyps if h["prop"] and h["name"] not in owners]
    w("## What the end-to-end theorem still assumes\n")
    w(f"`{d['theorem'].rsplit('.', 1)[-1]}` is the x64 theorem \"the machine code accepts only what the twin accepts\" "
      f"from exactly {len(named)} open hypotheses; each landing discharges one. Owning lane in brackets "
      "(`docs/assumption-owners.json`).\n")
    for h in named:
        lane, note = owners[h["name"]]
        w(f"- **`{h['name']}`** [{lane}]: {note}. `{_shorten(h['type'])}`")
    w("")
    if other:
        w(f"_Plus {len(other)} harness and statement premises, not proof obligations of the pipeline: "
          + ", ".join(f"`{n}`" for n in other) + "._\n")
    ax = d.get("axioms", [])
    std = {"propext", "Classical.choice", "Quot.sound"}
    extra = [a for a in ax if a not in std and a != "sorryAx"]
    if extra:
        w(f"**Axioms beyond the standard ones: {', '.join(f'`{a}`' for a in extra)}.**\n")
    elif "sorryAx" in ax:
        w("**Axioms:** only `propext`, `Classical.choice`, `Quot.sound`, plus `sorryAx` from the stub contracts below.\n")
    else:
        w("**Axioms:** only `propext`, `Classical.choice`, `Quot.sound`; no `sorry` left.\n")
    if srcs:
        w("**Sorry sources** (declarations that use `sorryAx` directly; blocks = census targets proven locally that get their `sorry` through it):\n")
        w("| Source | Blocks | Lane |")
        w("|---|---:|---|")
        for x in srcs[:8]:
            lane = next((v[0] for k, v in own.get("sources", {}).items() if x["name"].startswith(k)), "")
            w(f"| `{x['name']}` | {x['blocks']} | {lane} |")
        w("")


now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
head = git("rev-parse", "--short", "HEAD")
L = []
w = L.append
w("# con-agua: a Lean checker in verified x64\n")
w(f"_Progress report, generated {now} from master `{head}` by `scripts/gist_report.py`._\n")
w(f"**{proven} of {targets}** functions of con-ron's checker have L code refined against con-ron's model, "
  f"down to verified x64: **{pct(lean_share)}** of the model. Percentages are of the twin's Lean lines.\n")
w("| Proven | Proven locally | L written | Projected completion | Lanes running | Merge overhead |")
w("|---:|---:|---:|---:|---:|---:|")
eta_s = eta_when.strftime("%b %-d") if eta_when else "—"
# "proven locally": own proof complete, any sorry only in callees' stub specs (census status `local`);
# older census rows lack the column, then all `sorry` targets count (they were all local when measured)
_last = progress[-1] if progress else {}
_loc = _last.get("lean_local") or _last.get("lean_sorry")
sorry_share = int(_loc) / den(_last) if _loc else None
na_n, na_lines = int(_last.get("na") or 0), int(_last.get("lean_na") or 0)
w(f"| **{pct(lean_share)}** | {pct(lean_share + sorry_share) if sorry_share is not None else '—'} | {pct(lean_l)} | **{eta_s}** | {len(running)} | {pct(over / max(1, work + over))} |\n")
# the critical path to a sorry-free end-to-end theorem (columns added by census.py; older rows lack them)
def _f(k, fmt):
    v = _last.get(k)
    return fmt(float(v)) if v not in (None, "") else "n/a"
_n0 = next((int(float(p["sorry_sources"])) for p in progress if p.get("sorry_sources") not in (None, "")), None)
w("| StageC migration | Sorry-free share of the end-to-end cone | Remaining sorry sources |")
w("|---:|---:|---:|")
w(f"| **{_f('stagec_pct', lambda v: f'{v:.1f}%')}** | **{_f('cone_pct', lambda v: f'{v:.1f}%')}** | "
  f"**{_f('sorry_sources', lambda v: str(int(v)))}**{f' (first recorded: {_n0})' if _n0 is not None else ''} |\n")
w(f"_Not counted: {na_n} \"not needed\" functions ({na_lines} Lean lines; `docs/not-needed.md`, each with a reason), "
  "which L deliberately does not implement. From the census of 2026-10-23 on, every percentage is over the twin's Lean lines minus these, "
  f"so 100% is reachable; the trend curves use that denominator throughout (earlier points were not rescaled, there was nothing n/a then)._\n")
w("_The three shares are cumulative: proven ⊆ proven locally (own proof complete; `sorry` only in callees' stub specs) ⊆ L code written._\n")
if eta_rate:
    w(f"_Projected completion: at the least-squares rate of the last 3 days of census runs, {eta_rate:,.0f} Lean lines proven per day; "
      "a straight-line extrapolation, so treat it as a trend, not a promise._\n")

assumptions_section(w)

# trend chart
pts = progress[-30:]
labels = [p["date"][5:16].replace(" ", " ") for p in pts]
lean = [round(100 * int(p["lean_proven"]) / den(p), 1) for p in pts]
cnt = [round(100 * int(p["proven"]) / int(p["targets"]), 1) for p in pts]
wr = [round(100 * (int(p["lean_proven"]) + int(p["lean_sorry"]) + int(p["lean_written"])) / den(p), 1) for p in pts]
top = max(wr + lean + cnt + [10])
w("## Proven over time\n")
w("Left axis: share of the twin's Lean lines proven, proven locally (own proof complete, `sorry` only in callees' stubs), and with L code written. "
  "Right axis: lines of L code and of proofs in `ConAgua/` (thousands), so infrastructure work shows too. One point per census run.\n")
w(f"![Proven share and lines of code per census run]({raw_url('trend.svg')})\n")

# phases
w("## By phase\n")
w("Lean lines of con-ron's arena twin per phase.\n")
w(f"![Lean lines per phase: proven, proven with sorry, L written, not started]({raw_url('phases.svg')})\n")

# performance
if perf:
    import math
    rows = sorted(perf["rows"], key=lambda r: r["perf"]["L"] / r["perf"]["con-ron"])
    ratios = [r["perf"]["L"] / r["perf"]["con-ron"] for r in rows]
    gm = math.exp(sum(math.log(v) for v in ratios) / len(ratios))
    med = (ratios[len(ratios) // 2] + ratios[(len(ratios) - 1) // 2]) / 2
    tl = sum(r["perf"]["L"] for r in rows); tc = sum(r["perf"]["con-ron"] for r in rows)
    w("## Performance\n")
    w(f"CPU instructions (`perf stat -e instructions:u`, one run each) of the compiled L `check` against `con-ron --jobs=1` on the "
      f"**{len(rows)}** end-to-end fixtures both accept (of {perf['fixtures']}). Measured {perf['date']} on master `{perf['rev']}` by `scripts/e2e.py`.\n")
    w("| Fixtures | Geometric mean L / con-ron | Median | Fastest relative | Slowest relative | Total L | Total con-ron | Total ratio |")
    w("|---:|---:|---:|---|---|---:|---:|---:|")
    w(f"| {len(rows)} | **{gm:.2f}** | {med:.2f} | {ratios[0]:.2f} (`{rows[0]['id']}`) | {ratios[-1]:.2f} (`{rows[-1]['id']}`) | "
      f"{tl / 1e9:.2f} G | {tc / 1e9:.2f} G | {tl / tc:.2f} |\n")
    w(f"![L against con-ron instructions per fixture, and ratio by input size]({raw_url('perf.svg')})\n")

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
        for extra in ("phases.svg", "trend.svg", "perf.svg", "progress.csv", "lanes.json"):  # the chart, and the census history (durable copy)
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
