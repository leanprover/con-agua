module

public import ConAguaX86.AsmEsc.Chain2
import Kraken.X64.Registers

@[expose] public section

/-!
# Templates: the bitwise passes and the copy

`bitAsm tab f op`: a hand-written body for a leaf `f(o, oa, ob, n)` whose L code computes
`P[o + i] := A[oa + i] op B[ob + i]` for `i < n` and returns `0` (`and_n`, `or_n`, `xor_n`,
linleaf's `bitNG op`). `copyAsm tab f`: the same for `f(o, oa, n)` with `P[o + i] := A[oa + i]`
(`copy_n`). Up front: each window inside its tier and fuel for the loop, else `ca_exhausted`;
`n = 0` returns `0`. The loops are 6 and 5 instructions per limb.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- `op rax, [a]` for `op` one of `and`, `or`, `xor` (anything else is read as `xor`). -/
abbrev bitOp (op : BinOp) (d : Reg64) (a : AddrExpr) : Directive :=
  match op with
  | .and => i64 (.and (.reg (rr d)) (oM a))
  | .or => i64 (.or (.reg (rr d)) (oM a))
  | _ => i64 (.xor (.reg (rr d)) (oM a))

/-- The bitwise template, for the table `tab` (the descriptor offsets of `POOL` = 0). Arguments:
`rdi o`, `r8 oa`, `r9 ob`, `r10 n`. -/
def bitAsm (tab : Tab) (f : FnName) (op : BinOp) : Program :=
  [ .label (fnL f),                                                    -- 0
    i64 (.cmp (.reg (rr .r10)) (.imm (.int64 (0 : Word).toInt64))),    -- 1
    jccL .z (chL f "Z"),                                               -- 2  n = 0
    movRI .rax idxMask,                                                -- 3
    movRR .rcx .rdi,                                                   -- 4
    i64 (.shr (.reg (rr .rcx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 5
    i64 (.and (.reg (rr .rcx)) (.imm (.int64 (1 : Word).toInt64))),    -- 6  out tier bit
    i64 (.and (.reg (rr .rdi)) (oR .rax)),                             -- 7  pb
    movRR .rdx .r8,                                                    -- 8
    i64 (.shr (.reg (rr .rdx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 9
    i64 (.and (.reg (rr .rdx)) (.imm (.int64 (1 : Word).toInt64))),    -- 10 a tier bit
    i64 (.and (.reg (rr .r8)) (oR .rax)),                              -- 11 qa
    movRR .r12 .r9,                                                    -- 12
    i64 (.shr (.reg (rr .r12)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 13
    i64 (.and (.reg (rr .r12)) (.imm (.int64 (1 : Word).toInt64))),    -- 14 b tier bit
    i64 (.and (.reg (rr .r9)) (oR .rax)),                              -- 15 qb
    movRM .rax (tdesc .rdx (tab.len64 (0 : ArrId))),                   -- 16
    i64 (.sub (.reg (rr .rax)) (oR .r8)),                              -- 17
    jccL .c exhaustedL,                                                -- 18
    i64 (.cmp (.reg (rr .rax)) (oR .r10)),                             -- 19
    jccL .c exhaustedL,                                                -- 20
    movRM .rsi (tdesc .rdx (tab.base64 (0 : ArrId))),                  -- 21
    i64 (.lea (rr .rsi) (mbi .rsi .r8 .W64)),                          -- 22 rsi := &a[qa]
    movRM .rax (tdesc .r12 (tab.len64 (0 : ArrId))),                   -- 23
    i64 (.sub (.reg (rr .rax)) (oR .r9)),                              -- 24
    jccL .c exhaustedL,                                                -- 25
    i64 (.cmp (.reg (rr .rax)) (oR .r10)),                             -- 26
    jccL .c exhaustedL,                                                -- 27
    movRM .rbx (tdesc .r12 (tab.base64 (0 : ArrId))),                  -- 28
    i64 (.lea (rr .rbx) (mbi .rbx .r9 .W64)),                          -- 29 rbx := &b[qb]
    movRM .rax (tdesc .rcx (tab.len64 (0 : ArrId))),                   -- 30
    i64 (.sub (.reg (rr .rax)) (oR .rdi)),                             -- 31
    jccL .c exhaustedL,                                                -- 32
    i64 (.cmp (.reg (rr .rax)) (oR .r10)),                             -- 33
    jccL .c exhaustedL,                                                -- 34
    movRM .rcx (tdesc .rcx (tab.base64 (0 : ArrId))),                  -- 35
    i64 (.lea (rr .rdi) (mbi .rcx .rdi .W64)),                         -- 36 rdi := &out[pb]
    i64 (.sub (.reg (rr .r14)) (oR .r10)),                             -- 37
    jccL .c exhaustedL,                                                -- 38 fuel < n
    movRI .r13 0,                                                      -- 39 i := 0
    .label (chL f "L"),                                                -- 40
    movRM .rax (mbi .rsi .r13 .W64),                                   -- 41
    bitOp op .rax (mbi .rbx .r13 .W64),                                -- 42
    movMR (mbi .rdi .r13 .W64) .rax,                                   -- 43
    i64 (.add (.reg (rr .r13)) (oI 1)),                                -- 44
    i64 (.cmp (.reg (rr .r13)) (oR .r10)),                             -- 45
    jccL .c (chL f "L"),                                               -- 46
    .label (chL f "Z"),                                                -- 47
    movRI .rax 0,                                                      -- 48
    i64 .ret ]                                                         -- 49

/-- The copy template, for the table `tab`. Arguments: `rdi o`, `r8 oa`, `r9 n`. -/
def copyAsm (tab : Tab) (f : FnName) : Program :=
  [ .label (fnL f),                                                    -- 0
    i64 (.cmp (.reg (rr .r9)) (.imm (.int64 (0 : Word).toInt64))),     -- 1
    jccL .z (chL f "Z"),                                               -- 2  n = 0
    movRI .rax idxMask,                                                -- 3
    movRR .rcx .rdi,                                                   -- 4
    i64 (.shr (.reg (rr .rcx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 5
    i64 (.and (.reg (rr .rcx)) (.imm (.int64 (1 : Word).toInt64))),    -- 6  out tier bit
    i64 (.and (.reg (rr .rdi)) (oR .rax)),                             -- 7  pb
    movRR .rdx .r8,                                                    -- 8
    i64 (.shr (.reg (rr .rdx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 9
    i64 (.and (.reg (rr .rdx)) (.imm (.int64 (1 : Word).toInt64))),    -- 10 a tier bit
    i64 (.and (.reg (rr .r8)) (oR .rax)),                              -- 11 qa
    movRM .rax (tdesc .rdx (tab.len64 (0 : ArrId))),                   -- 12
    i64 (.sub (.reg (rr .rax)) (oR .r8)),                              -- 13
    jccL .c exhaustedL,                                                -- 14
    i64 (.cmp (.reg (rr .rax)) (oR .r9)),                              -- 15
    jccL .c exhaustedL,                                                -- 16
    movRM .rsi (tdesc .rdx (tab.base64 (0 : ArrId))),                  -- 17
    i64 (.lea (rr .rsi) (mbi .rsi .r8 .W64)),                          -- 18 rsi := &a[qa]
    movRM .rax (tdesc .rcx (tab.len64 (0 : ArrId))),                   -- 19
    i64 (.sub (.reg (rr .rax)) (oR .rdi)),                             -- 20
    jccL .c exhaustedL,                                                -- 21
    i64 (.cmp (.reg (rr .rax)) (oR .r9)),                              -- 22
    jccL .c exhaustedL,                                                -- 23
    movRM .rcx (tdesc .rcx (tab.base64 (0 : ArrId))),                  -- 24
    i64 (.lea (rr .rdi) (mbi .rcx .rdi .W64)),                         -- 25 rdi := &out[pb]
    i64 (.sub (.reg (rr .r14)) (oR .r9)),                              -- 26
    jccL .c exhaustedL,                                                -- 27 fuel < n
    movRI .r13 0,                                                      -- 28 i := 0
    .label (chL f "L"),                                                -- 29
    movRM .rax (mbi .rsi .r13 .W64),                                   -- 30
    movMR (mbi .rdi .r13 .W64) .rax,                                   -- 31
    i64 (.add (.reg (rr .r13)) (oI 1)),                                -- 32
    i64 (.cmp (.reg (rr .r13)) (oR .r9)),                              -- 33
    jccL .c (chL f "L"),                                               -- 34
    .label (chL f "Z"),                                                -- 35
    movRI .rax 0,                                                      -- 36
    i64 .ret ]                                                         -- 37

end L.AsmEsc

namespace L.AsmEsc

open L L.Arena L.Compiler

section
variable [Host] {k : Nat} {s : MachineData} {Q : MachineState → Prop}

/-- `and`/`or`/`xor rax, [b + 8 i]`: the operation on the register and the limb. -/
theorem ev_bitOpS {op : BinOp} (hop : op = .and ∨ op = .or ∨ op = .xor) {d b i : Reg64}
    (hk : Host.prog[k]? = some (bitOp op d (mbi b i .W64)))
    {v : Word} (hv : rdW s.dmem (s.regs.get64 b + s.regs.get64 i * 8) = some v)
    (h : ∀ st : StatusFlags, Ev Q { s with
        regs := s.regs.set64 d (op.eval (UInt64.ofBitVec (s.regs.get64 d)) v).toBitVec,
        status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  rcases hop with rfl | rfl | rfl
  · exact ev_andRS hk hv h
  · exact ev_orRS hk hv h
  · exact ev_xorRS hk hv h

end

end L.AsmEsc
