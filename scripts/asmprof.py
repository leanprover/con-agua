#!/usr/bin/env python3
"""Exact dynamic instruction profile of the compiled L checker (lane `compopt`).

`perf record` on this AMD machine has no precise `instructions` event, so per-instruction samples
pile up behind cache misses. Instead this instruments the assembler text `e2e-l asm` writes: at
every basic-block start (a label, the instruction after a jump or call) it inserts
`incq ca_bb+8i(%rip)` (the compiled code never has live flags across a label or after a jump, so
the `inc` clobbers nothing), links with `harness/e2e.c` and a destructor that writes the counters,
runs a fixture, and attributes every executed instruction (count of its block) to its function and
to a category of the code generator's patterns (local loads/stores, bounds checks, fuel, prologue,
result registers, …).

  scripts/asmprof.py build X.s OUT.bin         instrumented binary (+ OUT.bin.map: blocks)
  scripts/asmprof.py run OUT.bin FIXTURE CNT   run it (CA_PINS/CA_WORDS from the environment)
  scripts/asmprof.py report OUT.bin CNT... [--top N] [--fn F]   per function and per category
"""
import collections
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

DUMP_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
extern uint64_t ca_bb[];
extern const uint64_t ca_bb_n;
__attribute__((destructor)) static void ca_bb_dump(void) {
  const char *e = getenv("CA_BBOUT");
  if (!e) return;
  FILE *f = fopen(e, "wb");
  if (!f) return;
  fwrite(ca_bb, 8, ca_bb_n, f);
  fclose(f);
}
"""

JUMP = re.compile(r"^(j[a-z]+|call|ret)\b")


def build(s_path, out):
    lines = open(s_path).read().split("\n")
    res, blocks = [], []  # blocks: list of lists of instruction texts, with the function
    in_text = True
    fn = None
    cur = None

    def new_block():
        nonlocal cur
        i = len(blocks)
        cur = {"fn": fn, "ins": []}
        blocks.append(cur)
        res.append(f"incq ca_bb+{8 * i}(%rip)")

    start = True
    for ln in lines:
        t = ln.strip()
        if t.startswith(".section"):
            in_text = False
        if t == ".text":
            in_text = True
        if not in_text or not t or t.startswith("."):
            if t.endswith(":") and in_text:  # a local label
                res.append(ln)
                start = True
                continue
            res.append(ln)
            continue
        if t.endswith(":"):
            if t.startswith("ca_f_"):
                fn = t[5:-1]
            elif not t.startswith(".L"):
                fn = "<" + t[:-1] + ">"
            res.append(ln)
            start = True
            continue
        if start:
            new_block()
            start = False
        res.append(ln)
        cur["ins"].append(t)
        if JUMP.match(t):
            start = True
    n = len(blocks)
    res.append(f".section .bss\n.globl ca_bb\n.p2align 3\nca_bb: .zero {8 * n}\n"
               f".section .rodata\n.globl ca_bb_n\nca_bb_n: .quad {n}\n")
    si = out + ".s"
    with open(si, "w") as fh:
        fh.write("\n".join(res))
    dc = out + ".dump.c"
    with open(dc, "w") as fh:
        fh.write(DUMP_C)
    subprocess.run(["cc", "-O2", "-o", out, os.path.join(ROOT, "harness", "e2e.c"), dc, si], check=True)
    # table layout, for the categories: from the source text
    src = "\n".join(lines)
    meta = {}
    for k in ("ca_nw", "ca_nb", "ca_ng", "ca_rom_len"):
        m = re.search(rf"^{k}: \.quad (\d+)", src, re.M)
        meta[k] = int(m.group(1)) if m else 0
    m = re.search(r"^lea (\d+)\(%r15\), %rsi", src, re.M)
    meta["args"] = int(m.group(1))
    with open(out + ".map", "w") as fh:
        json.dump({"blocks": blocks, "meta": meta}, fh)
    print(f"{out}: {n} blocks")


def category(ins, meta):
    arr_end = 16 + 16 * (meta["ca_nb"] + meta["ca_nw"])
    glob_base = meta["args"] - 8 * meta["ca_ng"]
    rom_end = arr_end + 8 * ((meta["ca_rom_len"] + 7) // 8)

    def tab(off):
        off = int(off)
        if off < 16:
            return "stack"
        if off < arr_end:
            return "len" if (off // 8) % 2 == 1 else "base"
        if off < rom_end:
            return "rom"
        if off < glob_base:
            return "res"
        return "glob"

    op = ins.split()[0]
    if ins in ("subq $1, %r14",) or (op == "jb" and "ca_exhausted" in ins):
        return "fuel/stack check"
    if op in ("jae",) and "ca_error" in ins:
        return "bounds check (jae)"
    m = re.match(r"cmpq? (-?\d+)\(%r15\), %rax", ins)
    if m:
        return "bounds check (cmp len)"
    if op.startswith("j"):
        return "jmp" if op == "jmp" else "jcc"
    if op in ("call", "ret"):
        return op
    if re.match(r"movq? %rsp, %rax|subq 8\(%r15\), %rax|subq \$\d+, %rsp|addq \$\d+, %rsp", ins):
        return "prologue/epilogue (the stack check's cmp counts as cmp)"
    if ins.startswith("lea") and "(%rsp), %rsi" in ins:
        return "call: arg pointer"
    m = re.match(r"movq? (-?\d*)\(%rsi\), %rax", ins)
    if m:
        return "param copy (load)"
    m = re.match(r"movq? \$0, (\d*)\(%rsp\)", ins)
    if m:
        return "zero locals"
    m = re.match(r"movq? \$(-?\d+), %(rdi|r8|r9|r10|r11)$", ins)
    if m:
        return "result regs (zero)"
    m = re.match(r"movq? \$0, (\d+)\(%r15\)", ins)
    if m:
        return "result area (zero)"
    m = re.match(r"movq? (\d*)\(%rsp\), %(rdi|r8|r9|r10|r11)$", ins)
    if m:
        return "result regs (load)"
    m = re.match(r"movq? (\d*)\(%rsp\), %r(ax|cx|dx)$", ins)
    if m:
        return "frame load"
    m = re.match(r"movq? %r(ax|cx|dx|di|8|9|10|11), (\d*)\(%rsp\)$", ins)
    if m:
        return "frame store"
    m = re.match(r"movq? (\d+)\(%r15\), %r(ax|cx)$", ins)
    if m:
        k = tab(m.group(1))
        return {"base": "array base load", "len": "array len load", "glob": "global load",
                "res": "result area load"}.get(k, "table load " + k)
    m = re.match(r"movq? %r(ax|cx), (\d+)\(%r15\)$", ins)
    if m:
        k = tab(m.group(2))
        return {"glob": "global store", "res": "result area store"}.get(k, "table store " + k)
    if re.match(r"mov[a-z]* \(%rcx,%rax,8\), %rax|movzbq \(%rcx,%rax(,1)?\), %rax|movzx", ins):
        return "array element load"
    if re.match(r"movq? %rdx, \(%rcx,%rax,8\)|movb %dl, \(%rcx,%rax(,1)?\)", ins):
        return "array element store"
    if re.match(r"movq? %r(bx|12|13|si|di|8|9|10|11), %r(ax|cx|dx)$", ins):
        return "register local load"
    if re.match(r"movq? %r(ax|cx|dx), %r(bx|12|13|si|di|8|9|10|11)$", ins):
        return "register local store"
    if re.match(r"movq? \$-?\d+, %r(bx|12|13|si|di|8|9|10|11)$", ins):
        return "register local const"
    if re.match(r"movq? -?\d*\(%rsi\), %r(bx|12|13|di|si|8|9|10|11)$", ins):
        return "param copy (load)"
    if re.match(r"movq? %r(bx|12|13|si|di|8|9|10|11), %r(bx|12|13|si|di|8|9|10|11)$", ins):
        return "register local move"
    if re.match(r"(movq?|movabsq?) \$-?\d+, %r(ax|cx|dx)$", ins):
        return "const"
    if re.match(r"movq? %rax, %r(cx|dx)$|movq? %rdx, %rax$", ins):
        return "reg move"
    if re.match(r"movq? \$[01], %r(ax|dx)$", ins) or op.startswith("cmov"):
        return "cmpw (setcc)"
    if op.startswith("cmp"):
        return "cmp"
    if op.startswith("lea"):
        return "lea (rom)"
    if re.match(r"(add|sub|imul|and|or|xor|shl|shr|mul)", op):
        return "alu"
    return "other: " + op


def report(binp, cnts, top=40, fn_only=None):
    mp = json.load(open(binp + ".map"))
    blocks, meta = mp["blocks"], mp["meta"]
    import array
    tot = [0] * len(blocks)
    for c in cnts:
        a = array.array("Q")
        with open(c, "rb") as fh:
            a.frombytes(fh.read())
        for i, v in enumerate(a):
            tot[i] += v
    by_fn = collections.Counter()
    by_cat = collections.Counter()
    by_fn_cat = collections.defaultdict(collections.Counter)
    calls = collections.Counter()
    for b, n in zip(blocks, tot):
        if not n:
            continue
        if b["ins"] and b["fn"] and b["ins"][0].startswith("movq %rsp, %rax") is False:
            pass
        for ins in b["ins"]:
            c = category(ins, meta)
            by_fn[b["fn"]] += n
            by_cat[c] += n
            by_fn_cat[b["fn"]][c] += n
    # function entries: the first block of each function
    seen = set()
    for b, n in zip(blocks, tot):
        if b["fn"] not in seen:
            seen.add(b["fn"])
            calls[b["fn"]] = n
    total = sum(by_cat.values())
    leaf = {b["fn"] for b in blocks} - {b["fn"] for b in blocks if any(i.startswith("call") for i in b["ins"])}
    nleaf = sum(n for f, n in by_fn.items() if f in leaf)
    print(f"total {total:,} instructions (counted, without the counters), {sum(calls.values()):,} calls; "
          f"{100 * nleaf / total:.1f}% of the instructions in leaf functions (no calls), "
          f"{sum(calls[f] for f in leaf):,} calls of leaf functions")
    print("\n## by category\n")
    for c, n in by_cat.most_common():
        print(f"{100 * n / total:6.2f}%  {n:>16,}  {c}")
    print(f"\n## top {top} functions\n")
    print(f"{'share':>7} {'cum':>7} {'instructions':>16} {'calls':>14} {'ins/call':>9}  function")
    cum = 0
    for f, n in by_fn.most_common(top):
        cum += n
        print(f"{100 * n / total:6.2f}% {100 * cum / total:6.2f}% {n:>16,} {calls[f]:>14,} {n / max(calls[f], 1):9.1f}  {f}{' (leaf)' if f in leaf else ''}")
    if fn_only:
        print(f"\n## {fn_only}\n")
        for c, n in by_fn_cat[fn_only].most_common():
            print(f"{100 * n / by_fn[fn_only]:6.2f}%  {n:>14,}  {c}")


def main():
    a = sys.argv[1:]
    if a and a[0] == "build":
        build(a[1], os.path.abspath(a[2]))
    elif a and a[0] == "run":
        env = dict(os.environ, CA_BBOUT=os.path.abspath(a[3]))
        r = subprocess.run([os.path.abspath(a[1]), a[2]], env=env, capture_output=True, text=True)
        print(r.stdout.strip())
    elif a and a[0] == "report":
        top, fn = 40, None
        rest = []
        i = 2
        while i < len(a):
            if a[i] == "--top":
                top = int(a[i + 1]); i += 2
            elif a[i] == "--fn":
                fn = a[i + 1]; i += 2
            else:
                rest.append(a[i]); i += 1
        report(a[1], rest, top, fn)
    else:
        print(__doc__)
        sys.exit(2)


if __name__ == "__main__":
    main()
