module

public import ConAguaX86.AsmEsc.Chain2
import Kraken.X64.Registers

@[expose] public section

/-!
# Hand-written shifts and zeroing

`shlAsm tab` for linleaf's `shl_n(o, oa, n, s, c)`: `P[o + i] := (A[i] << s) | c`, carry
`c := A[i] >> (64 − s)`. It shifts the first limb with `shl`/`or` (the carry in), then each next limb
with one `shld` (the previous limb's top bits). `shrAsm tab` for `shr_n(o, oa, n, s)`: one `shrd` per
limb. `zeroAsm tab` for `zero_n(o, n)`: a store loop.

Up front: `s < 64`, the windows inside their tiers (`shr_n` reads `n + 1` limbs), and fuel, else
`ca_exhausted`. A count of 0 leaves `shld`/`shrd`'s destination unchanged, which is L's result for
`s = 0`.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- The left shift, for the table `tab`. Arguments: `rdi o`, `r8 oa`, `r9 n`, `r10 s`, `r11 c`. -/
def shlAsm (tab : Tab) : Program :=
  [ .label (fnL "shl_n"),                                              -- 0
    i64 (.cmp (.reg (rr .r10)) (.imm (.int64 (63 : Word).toInt64))),   -- 1
    jccL .a exhaustedL,                                                -- 2  s > 63
    i64 (.cmp (.reg (rr .r9)) (.imm (.int64 (0 : Word).toInt64))),     -- 3
    jccL .z (chL "shl_n" "Z"),                                         -- 4  n = 0
    movRI .rax idxMask,                                                -- 5
    movRR .rcx .rdi,                                                   -- 6
    i64 (.shr (.reg (rr .rcx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 7
    i64 (.and (.reg (rr .rcx)) (.imm (.int64 (1 : Word).toInt64))),    -- 8  out tier bit
    i64 (.and (.reg (rr .rdi)) (oR .rax)),                             -- 9  pb
    movRR .rdx .r8,                                                    -- 10
    i64 (.shr (.reg (rr .rdx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 11
    i64 (.and (.reg (rr .rdx)) (.imm (.int64 (1 : Word).toInt64))),    -- 12 a tier bit
    i64 (.and (.reg (rr .r8)) (oR .rax)),                              -- 13 qa
    movRM .rax (tdesc .rdx (tab.len64 (0 : ArrId))),                   -- 14
    i64 (.sub (.reg (rr .rax)) (oR .r8)),                              -- 15
    jccL .c exhaustedL,                                                -- 16
    i64 (.cmp (.reg (rr .rax)) (oR .r9)),                              -- 17
    jccL .c exhaustedL,                                                -- 18
    movRM .rsi (tdesc .rdx (tab.base64 (0 : ArrId))),                  -- 19
    i64 (.lea (rr .rsi) (mbi .rsi .r8 .W64)),                          -- 20 rsi := &a[qa]
    movRM .rax (tdesc .rcx (tab.len64 (0 : ArrId))),                   -- 21
    i64 (.sub (.reg (rr .rax)) (oR .rdi)),                             -- 22
    jccL .c exhaustedL,                                                -- 23
    i64 (.cmp (.reg (rr .rax)) (oR .r9)),                              -- 24
    jccL .c exhaustedL,                                                -- 25
    movRM .rcx (tdesc .rcx (tab.base64 (0 : ArrId))),                  -- 26
    i64 (.lea (rr .rdi) (mbi .rcx .rdi .W64)),                         -- 27 rdi := &out[pb]
    i64 (.sub (.reg (rr .r14)) (oR .r9)),                              -- 28
    jccL .c exhaustedL,                                                -- 29 fuel < n
    movRI .r13 0,                                                      -- 30
    movRR .rcx .r10,                                                   -- 31 cl := s
    movRM .rdx (mbi .rsi .r13 .W64),                                   -- 32 x0
    movRR .rax .rdx,                                                   -- 33
    i64 (.shl (.reg (rr .rax)) .cl),                                   -- 34
    i64 (.or (.reg (rr .rax)) (oR .r11)),                              -- 35 (x0 << s) | c
    movMR (mbi .rdi .r13 .W64) .rax,                                   -- 36
    i64 (.add (.reg (rr .r13)) (oI 1)),                                -- 37
    i64 (.cmp (.reg (rr .r13)) (oR .r9)),                              -- 38
    jccL .nc (chL "shl_n" "T"),                                        -- 39 n = 1
    .label (chL "shl_n" "L"),                                          -- 40
    movRM .rax (mbi .rsi .r13 .W64),                                   -- 41 x
    movRR .r8 .rax,                                                    -- 42
    i64 (.shld (.reg (rr .rax)) (rr .rdx) .cl),                        -- 43 (x << s) | (prev >> (64 - s))
    movMR (mbi .rdi .r13 .W64) .rax,                                   -- 44
    movRR .rdx .r8,                                                    -- 45 prev := x
    i64 (.add (.reg (rr .r13)) (oI 1)),                                -- 46
    i64 (.cmp (.reg (rr .r13)) (oR .r9)),                              -- 47
    jccL .c (chL "shl_n" "L"),                                         -- 48
    .label (chL "shl_n" "T"),                                          -- 49
    i64 (.shr (.reg (rr .rdx)) (.imm8 (.int64 (Int64.ofInt 1)))),     -- 50
    movRI .rcx 63,                                                     -- 51
    i64 (.sub (.reg (rr .rcx)) (oR .r10)),                             -- 52
    i64 (.shr (.reg (rr .rdx)) .cl),                                   -- 53 (prev >> 1) >> (63 - s)
    movRR .rax .rdx,                                                   -- 54
    i64 .ret,                                                          -- 55
    .label (chL "shl_n" "Z"),                                          -- 56
    movRR .rax .r11,                                                   -- 57
    i64 .ret ]                                                         -- 58

/-- The right shift, for the table `tab`. Arguments: `rdi o`, `r8 oa`, `r9 n`, `r10 s`. -/
def shrAsm (tab : Tab) : Program :=
  [ .label (fnL "shr_n"),                                              -- 0
    i64 (.cmp (.reg (rr .r10)) (.imm (.int64 (63 : Word).toInt64))),   -- 1
    jccL .a exhaustedL,                                                -- 2  s > 63
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
    jccL .be exhaustedL,                                               -- 16 len - qa ≤ n
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
    movRI .r13 0,                                                      -- 28
    movRR .rcx .r10,                                                   -- 29 cl := s
    movRM .rdx (mbi .rsi .r13 .W64),                                   -- 30 x := A[0]
    movRR .r11 .rdi,                                                   -- 31
    i64 (.sub (.reg (rr .r11)) (oI 8)),                                -- 32 r11 := &out[pb] - 8
    i64 (.cmp (.reg (rr .r9)) (.imm (.int64 (0 : Word).toInt64))),     -- 33
    jccL .z (chL "shr_n" "Z"),                                         -- 34 n = 0
    .label (chL "shr_n" "L"),                                          -- 35
    movRR .rax .rdx,                                                   -- 36
    i64 (.add (.reg (rr .r13)) (oI 1)),                                -- 37 i + 1
    movRM .rdx (mbi .rsi .r13 .W64),                                   -- 38 y := A[i + 1]
    i64 (.shrd (.reg (rr .rax)) (rr .rdx) .cl),                        -- 39 (x >> s) | (y << (64 - s))
    movMR (mbi .r11 .r13 .W64) .rax,                                   -- 40 P[i]
    i64 (.cmp (.reg (rr .r13)) (oR .r9)),                              -- 41
    jccL .c (chL "shr_n" "L"),                                         -- 42
    .label (chL "shr_n" "Z"),                                          -- 43
    movRI .rax 0,                                                      -- 44
    i64 .ret ]                                                         -- 45

/-- Zeroing, for the table `tab`. Arguments: `rdi o`, `r8 n`. -/
def zeroAsm (tab : Tab) : Program :=
  [ .label (fnL "zero_n"),                                             -- 0
    i64 (.cmp (.reg (rr .r8)) (.imm (.int64 (0 : Word).toInt64))),     -- 1
    jccL .z (chL "zero_n" "Z"),                                        -- 2  n = 0
    movRI .rax idxMask,                                                -- 3
    movRR .rcx .rdi,                                                   -- 4
    i64 (.shr (.reg (rr .rcx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 5
    i64 (.and (.reg (rr .rcx)) (.imm (.int64 (1 : Word).toInt64))),    -- 6  out tier bit
    i64 (.and (.reg (rr .rdi)) (oR .rax)),                             -- 7  pb
    movRM .rax (tdesc .rcx (tab.len64 (0 : ArrId))),                   -- 8
    i64 (.sub (.reg (rr .rax)) (oR .rdi)),                             -- 9
    jccL .c exhaustedL,                                                -- 10
    i64 (.cmp (.reg (rr .rax)) (oR .r8)),                              -- 11
    jccL .c exhaustedL,                                                -- 12
    movRM .rcx (tdesc .rcx (tab.base64 (0 : ArrId))),                  -- 13
    i64 (.lea (rr .rdi) (mbi .rcx .rdi .W64)),                         -- 14 rdi := &out[pb]
    i64 (.sub (.reg (rr .r14)) (oR .r8)),                              -- 15
    jccL .c exhaustedL,                                                -- 16 fuel < n
    movRI .r13 0,                                                      -- 17
    movRI .rdx 0,                                                      -- 18
    .label (chL "zero_n" "L"),                                         -- 19
    movMR (mbi .rdi .r13 .W64) .rdx,                                   -- 20
    i64 (.add (.reg (rr .r13)) (oI 1)),                                -- 21
    i64 (.cmp (.reg (rr .r13)) (oR .r8)),                              -- 22
    jccL .c (chL "zero_n" "L"),                                        -- 23
    .label (chL "zero_n" "Z"),                                         -- 24
    movRI .rax 0,                                                      -- 25
    i64 .ret ]                                                         -- 26

end L.AsmEsc
