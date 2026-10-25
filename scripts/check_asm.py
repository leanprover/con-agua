#!/usr/bin/env python3
"""Compare the instructions the compiler intended (the `.s` text `asmText` printed, i.e. what
Kraken's AT&T printer says the compiled `Directive`s are) against what the assembled, then
disassembled, object code actually contains (`as` + `objdump -d`). One mismatch here is exactly
the `imul` bug's shape: the printer and the assembler disagreeing about what instruction a line
of text denotes. See `scripts/check-asm.sh`, `DESIGN.md` ("the compiler", lane `walk`), and
`docs/gaps/kraken-att-imul-three-operand.lean`.

Usage: check_asm.py FILE.s NAME
Exits 0 if every instruction matches, 1 otherwise (with a diagnostic per mismatch).
"""
import re
import subprocess
import sys
import tempfile
import os

# Mnemonics the compiler emits with a conditional AT&T width suffix (`b`/`w`/`l`/`q`) that
# `objdump` omits whenever the operands already determine the width (e.g. two registers).
# `movzx`/`movsx`/`jcc`/`cmovcc`/`setcc`/`call`/`jmp`/`ret`/`lea` are deliberately absent: their
# trailing letter (if any) is part of the mnemonic (a condition code, or an embedded width code
# compared verbatim), not an elidable size suffix.
SUFFIXED = {"mov", "add", "sub", "and", "or", "xor", "cmp", "test", "not", "neg", "inc", "dec",
            "imul", "mul", "shl", "shr", "sar", "rol", "ror", "rcl", "rcr", "push", "pop"}


def strip_suffix(mnem):
    # `mov $imm64, %reg` with an immediate that doesn't fit a sign-extended 32-bit field has no
    # memory-destination encoding, but for a register destination the assembler transparently
    # widens it to `movabs` (opcode B8+r, a full 8-byte immediate) -- the same instruction
    # (load the immediate into the register), just a different, imm-size-dependent spelling that
    # Kraken's printer (always "mov") does not need to anticipate. Treated as `mov` here too.
    if mnem == "movabs":
        return "mov"
    if len(mnem) > 1 and mnem[-1] in "bwlq" and mnem[:-1] in SUFFIXED:
        return mnem[:-1]
    return mnem


def split_operands(s):
    """Split on top-level commas (a memory operand's `,index,scale` commas are inside parens)."""
    out, depth, cur = [], 0, ""
    for c in s:
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        if c == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += c
    if cur.strip():
        out.append(cur.strip())
    return out


MEM_RE = re.compile(r"^(?P<disp>-?(?:0x[0-9a-fA-F]+|\d+))?\((?P<base>%\w+)?(?:,(?P<idx>%\w+),(?P<scale>\d+))?\)$")


def parse_int(s):
    s = s.strip()
    neg = s.startswith("-")
    if neg:
        s = s[1:]
    v = int(s, 0) if s else 0
    return -v if neg else v


def operand_kind(op):
    if op.startswith("%"):
        return "reg"
    if op.startswith("$"):
        return "imm"
    if "(" in op:
        return "mem"
    return "target"


def operands_equal(a, b):
    """`a` from our `.s`, `b` from `objdump` (its target operands may carry a `<sym[+off]>`
    annotation, stripped by the caller before this is called; kept untouched here otherwise)."""
    ka, kb = operand_kind(a), operand_kind(b)
    if ka != kb:
        return False, f"operand kind {ka} ({a!r}) vs {kb} ({b!r})"
    if ka == "reg":
        return (a == b), None if a == b else f"register {a!r} vs {b!r}"
    if ka == "imm":
        va, vb = parse_int(a[1:]), parse_int(b[1:])
        ok = (va % (1 << 64)) == (vb % (1 << 64))
        return ok, None if ok else f"immediate {a!r} ({va}) vs {b!r} ({vb})"
    if ka == "mem":
        ma, mb = MEM_RE.match(a), MEM_RE.match(b)
        if not ma or not mb:
            return (a == b), None if a == b else f"unparsed memory operand {a!r} vs {b!r}"
        da = parse_int(ma.group("disp")) if ma.group("disp") else 0
        db = parse_int(mb.group("disp")) if mb.group("disp") else 0
        if (da % (1 << 64)) != (db % (1 << 64)):
            return False, f"memory displacement {a!r} vs {b!r}"
        if (ma.group("base"), ma.group("idx"), ma.group("scale")) != \
           (mb.group("base"), mb.group("idx"), mb.group("scale")):
            return False, f"memory base/index/scale {a!r} vs {b!r}"
        return True, None
    # target: a branch/call operand (a label on our side, a resolved address on objdump's); the
    # assembler/linker's job to get the address right, not the printer's, so only the *kind* is
    # checked here (that this is a direct target operand, not something that decayed into a
    # register/immediate/memory operand, which is the family of bug `imul` is: a destination
    # operand silently gaining a form the compiler did not intend).
    return True, None


def parse_instr_line(mnem_and_rest):
    parts = mnem_and_rest.split(None, 1)
    mnem = parts[0]
    rest = parts[1] if len(parts) > 1 else ""
    return mnem, split_operands(rest)


def our_instructions(path):
    """The instruction lines of the `.text` section of an `asmText` `.s` file, in order."""
    out = []
    in_text = False
    for line in open(path):
        line = line.rstrip("\n")
        s = line.strip()
        if s == ".text":
            in_text = True
            continue
        if s.startswith(".section"):
            in_text = False
            continue
        if not in_text or not s:
            continue
        if s.startswith("."):  # .globl, other directives
            continue
        if re.match(r"^[.\w]+:$", s):  # a bare label
            continue
        out.append(s)
    return out


# The prefix byte of an APX-encoded instruction: EVEX (0x62, e.g. the "new data destination"
# 3-operand `imul`) or REX2 (0xd5). Kraken's `Instr`/`Operation` syntax and semantics have no APX
# case at all (`Kraken/X64/Syntax.lean`), so *any* instruction the assembler encodes this way is
# outside what `compile_correct` proves anything about, regardless of what objdump's disassembler
# prints it back as -- an EVEX `imul %rcx,%rax,%rax` and the intended legacy `imul %rcx,%rax` can
# disassemble to confusingly similar (even once-normalised-identical) text while being completely
# different instructions (one SIGILLs without APX hardware). So this is checked on the raw
# opcode bytes, not on the disassembled text.
APX_PREFIXES = {"62": "EVEX", "d5": "REX2"}

PRIMARY_LINE_RE = re.compile(r"^\s*[0-9a-f]+:\t([0-9a-f ]+?)\t(.*)$")


def objdump_instructions(obj_path):
    """The instructions of `objdump -d`'s `.text` disassembly, in order: `(first_opcode_byte,
    text)`. Only "primary" lines (address + bytes + mnemonic) are instructions; an instruction
    longer than 7 bytes (e.g. `movabs`'s 10) continues on a bytes-only line with no mnemonic,
    which is skipped -- the first byte, all we need, is always on the primary line."""
    r = subprocess.run(
        ["objdump", "-d", "-M", "att", "-j", ".text", obj_path],
        capture_output=True, text=True, check=True)
    out = []
    for line in r.stdout.splitlines():
        m = PRIMARY_LINE_RE.match(line)
        if m:
            out.append((m.group(1).split()[0], m.group(2).strip()))
    return out


def strip_annotation(s):
    """Drop objdump's ` <symbol[+0xoff]>` branch/call annotation, returning (value, annotation)."""
    m = re.match(r"^(.*?)\s*<([^>]*)>\s*$", s)
    if m:
        return m.group(1).strip(), m.group(2)
    return s, None


def check(s_path, name):
    ours = our_instructions(s_path)
    with tempfile.TemporaryDirectory() as td:
        obj = os.path.join(td, name + ".o")
        asm = subprocess.run(["as", s_path, "-o", obj], capture_output=True, text=True)
        if asm.returncode != 0:
            print(f"[{name}] FAIL: `as` rejected the printed assembly:\n{asm.stderr}")
            return False
        dumped = objdump_instructions(obj)

    ok = True
    if len(ours) != len(dumped):
        print(f"[{name}] FAIL: {len(ours)} printed instructions vs {len(dumped)} disassembled")
        ok = False
    for i, (o, (first_byte, d)) in enumerate(zip(ours, dumped)):
        if first_byte in APX_PREFIXES:
            print(f"[{name}] FAIL at instruction {i} ({o!r}): assembled with a "
                  f"{APX_PREFIXES[first_byte]} prefix (0x{first_byte}) -- an APX encoding, "
                  f"outside Kraken's modelled instruction set")
            ok = False
            continue
        dval, _ann = strip_annotation(d)
        o_mnem, o_ops = parse_instr_line(o)
        d_mnem, d_ops = parse_instr_line(dval) if dval else ("", [])
        if strip_suffix(o_mnem) != strip_suffix(d_mnem):
            print(f"[{name}] FAIL at instruction {i}: mnemonic {o!r} vs disassembled {d!r}")
            ok = False
            continue
        if len(o_ops) != len(d_ops):
            print(f"[{name}] FAIL at instruction {i}: operand count {o!r} vs {d!r}")
            ok = False
            continue
        for oo, do in zip(o_ops, d_ops):
            doval, _ = strip_annotation(do)
            same, why = operands_equal(oo, doval)
            if not same:
                print(f"[{name}] FAIL at instruction {i} ({o!r} vs {d!r}): {why}")
                ok = False
    if ok:
        print(f"[{name}] OK: {len(ours)} instructions match ({s_path})")
    return ok


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(2)
    sys.exit(0 if check(sys.argv[1], sys.argv[2]) else 1)
