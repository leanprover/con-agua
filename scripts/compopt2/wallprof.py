#!/usr/bin/env python3
"""Where the wall time of a compiled L checker goes (lane compopt2): user/kernel time, page faults,
and the core's stall counters (AMD Zen 5 PMU, user mode only), one run per event group so nothing
is multiplexed.

  scripts/compopt2/wallprof.py [--cpus C] [--words W] BIN FIXTURE...   (CA_PINS from the env or _tmp/bench/<wt>/pins.bin)
"""
import argparse, os, subprocess, sys, json

GROUPS = [
    ["cycles:u", "instructions:u", "cycles:k", "page-faults", "task-clock"],
    ["cycles:u", "ex_no_retire.load_not_complete:u", "ex_no_retire.not_complete:u", "ex_no_retire.empty:u",
     "ex_no_retire.all:u", "ex_ret_brn_misp:u"],
    ["cycles:u", "de_no_dispatch_per_slot.no_ops_from_frontend:u", "de_no_dispatch_per_slot.backend_stalls:u",
     "ic_tag_hit_miss.instruction_cache_miss:u", "op_cache_hit_miss.op_cache_miss:u",
     "op_cache_hit_miss.all_op_cache_accesses:u"],
    ["cycles:u", "ls_dmnd_fills_from_sys.all:u", "ls_dmnd_fills_from_sys.local_l2:u",
     "ls_dmnd_fills_from_sys.dram_io_all:u", "ls_l1_d_tlb_miss.all:u", "ls_bad_status2.stli_other:u"],
]


def stat(cmd, events, env, cpus):
    pre = ["nice", "-n", "10"] + (["taskset", "-c", cpus] if cpus else [])
    r = subprocess.run(pre + ["perf", "stat", "-x,", "-e", ",".join(events), "--"] + cmd,
                       env=env, capture_output=True, text=True, timeout=900)
    out = {}
    for ln in r.stderr.splitlines():
        f = ln.split(",")
        if len(f) > 3:
            try:
                out[f[2]] = float(f[0])
            except ValueError:
                pass
    return r.stdout.strip(), out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("bin")
    ap.add_argument("fixtures", nargs="+")
    ap.add_argument("--cpus")
    ap.add_argument("--words", type=int, default=1 << 25)
    ap.add_argument("--json")
    a = ap.parse_args()
    root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    pins = os.environ.get("CA_PINS", os.path.join(root, "_tmp", "bench", os.path.basename(root), "pins.bin"))
    env = dict(os.environ, CA_PINS=pins, CA_WORDS=str(a.words))
    res = {}
    for fx in a.fixtures:
        m = {}
        for g in GROUPS:
            v, o = stat([os.path.abspath(a.bin), fx], g, env, a.cpus)
            for k, x in o.items():
                m.setdefault(k, x)
        m["verdict"] = v
        res[os.path.basename(fx)] = m
        c = m["cycles:u"]
        slots = 8 * c
        print(f"## {os.path.basename(fx)}: {v}")
        print(f"  task-clock {m['task-clock']/1e3:.3f} s; cycles u {c/1e9:.2f} G, k {m['cycles:k']/1e9:.2f} G "
              f"(kernel {100*m['cycles:k']/(c+m['cycles:k']):.0f}%); page faults {m['page-faults']:,.0f}")
        print(f"  instr {m['instructions:u']/1e9:.2f} G, IPC {m['instructions:u']/c:.2f}; "
              f"retire stalled on load {100*m['ex_no_retire.load_not_complete:u']/c:.0f}% of cycles, "
              f"not complete {100*m['ex_no_retire.not_complete:u']/c:.0f}%, empty {100*m['ex_no_retire.empty:u']/c:.0f}%; "
              f"br misp {m['ex_ret_brn_misp:u']/1e6:.1f} M")
        print(f"  slots: frontend {100*m['de_no_dispatch_per_slot.no_ops_from_frontend:u']/slots:.0f}%, "
              f"backend {100*m['de_no_dispatch_per_slot.backend_stalls:u']/slots:.0f}%; "
              f"icache miss {m['ic_tag_hit_miss.instruction_cache_miss:u']/1e6:.1f} M "
              f"({1000*m['ic_tag_hit_miss.instruction_cache_miss:u']/m['instructions:u']:.1f}/kinstr), "
              f"op cache miss {100*m['op_cache_hit_miss.op_cache_miss:u']/max(1,m['op_cache_hit_miss.all_op_cache_accesses:u']):.0f}%")
        print(f"  L1d demand fills {m['ls_dmnd_fills_from_sys.all:u']/1e6:.1f} M (L2 {m['ls_dmnd_fills_from_sys.local_l2:u']/1e6:.1f} M, "
              f"DRAM {m['ls_dmnd_fills_from_sys.dram_io_all:u']/1e6:.2f} M); dTLB miss {m['ls_l1_d_tlb_miss.all:u']/1e6:.1f} M; "
              f"stlf-fail {m['ls_bad_status2.stli_other:u']/1e6:.2f} M", flush=True)
    if a.json:
        json.dump(res, open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()
