"""Per system: instructions, and the MINIMUM cycles and wall over the rounds of a bench.py --json file
(the least disturbed run on a loaded machine; lane perfgap)."""
import json,sys
for p in sys.argv[1:]:
    d=json.load(open(p));
    for k,v in d['fixtures'].items():
        b=None
        for s,m in v.items():
            if not isinstance(m,dict) or 'runs' not in m: continue
            cy=min(r['cycles'] for r in m['runs']); w=min(r['wall'] for r in m['runs']); ins=m['stats']['instr']
            if b is None: b=(cy,w,ins)
            print(f"{s:14s} instr {ins/1e9:6.1f}G ({ins/b[2]:.3f})  min cycles {cy/1e9:6.1f}G ({cy/b[0]:.3f})  min wall {w:5.1f}s ({w/b[1]:.3f})  runs {len(m['runs'])}")
