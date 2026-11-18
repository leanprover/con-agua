module

public import ConAgua.AsmEsc.Chain2
import Kraken.X64.Registers

@[expose] public section

/-!
# Hand-written `nat_cmp` and its simulation contract

`natCmpAsm tab` is a hand-written body for `nat_cmp(oa, la, ob, lb)` (`L.Arena.natCmp`): `0`, `1`
or `2` as the number at `oa` (`la` limbs) is below, equal to or above the one at `ob` (`lb`
limbs). Different lengths decide; equal lengths compare from the top limb down. Up front (for
`la = lb > 0`): both windows inside their tiers and below `2^40` and fuel for the loop, else
`ca_exhausted`. The loop is 8 instructions per limb.

Registers: `rdi oa`, `r8 la`, `r9 ob`, `r10 lb`; in the loop `rdi`, `r9` the addresses of the
limbs 0 and `r8` the index.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- A local label of the hand-written `nat_cmp`. -/
abbrev ncL (m : String) : Label := ".Lasm_nat_cmp_" ++ m

/-- The hand-written `nat_cmp`, for the table `tab` (the descriptor offsets of `POOL` = 0). -/
def natCmpAsm (tab : Tab) : Program :=
  [ .label (fnL "nat_cmp"),                                            -- 0
    i64 (.cmp (.reg (rr .r8)) (oR .r10)),                              -- 1
    jccL .c (ncL "Z0"),                                                -- 2  la < lb
    jccL .a (ncL "Z2"),                                                -- 3  la > lb
    i64 (.cmp (.reg (rr .r8)) (.imm (.int64 (0 : Word).toInt64))),     -- 4
    jccL .z (ncL "Z1"),                                                -- 5  la = lb = 0
    movRI .rax idxMask,                                                -- 6
    movRR .rcx .rdi,                                                   -- 7
    i64 (.shr (.reg (rr .rcx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 8
    i64 (.and (.reg (rr .rcx)) (.imm (.int64 (1 : Word).toInt64))),    -- 9  A's tier bit
    i64 (.and (.reg (rr .rdi)) (oR .rax)),                             -- 10 qa
    movRR .rdx .r9,                                                    -- 11
    i64 (.shr (.reg (rr .rdx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 12
    i64 (.and (.reg (rr .rdx)) (.imm (.int64 (1 : Word).toInt64))),    -- 13 B's tier bit
    i64 (.and (.reg (rr .r9)) (oR .rax)),                              -- 14 qb
    movRR .r11 .rax,                                                   -- 15
    i64 (.sub (.reg (rr .r11)) (oR .rdi)),                             -- 16
    i64 (.cmp (.reg (rr .r11)) (oR .r8)),                              -- 17
    jccL .c exhaustedL,                                                -- 18 qa + la ≥ 2^40
    movRR .r11 .rax,                                                   -- 19
    i64 (.sub (.reg (rr .r11)) (oR .r9)),                              -- 20
    i64 (.cmp (.reg (rr .r11)) (oR .r8)),                              -- 21
    jccL .c exhaustedL,                                                -- 22 qb + la ≥ 2^40
    movRM .rax (tdesc .rcx (tab.len64 (0 : ArrId))),                   -- 23
    i64 (.sub (.reg (rr .rax)) (oR .rdi)),                             -- 24
    jccL .c exhaustedL,                                                -- 25
    i64 (.cmp (.reg (rr .rax)) (oR .r8)),                              -- 26
    jccL .c exhaustedL,                                                -- 27 len - qa < la
    movRM .rcx (tdesc .rcx (tab.base64 (0 : ArrId))),                  -- 28
    i64 (.lea (rr .rdi) (mbi .rcx .rdi .W64)),                         -- 29 rdi := &A[0]
    movRM .rax (tdesc .rdx (tab.len64 (0 : ArrId))),                   -- 30
    i64 (.sub (.reg (rr .rax)) (oR .r9)),                              -- 31
    jccL .c exhaustedL,                                                -- 32
    i64 (.cmp (.reg (rr .rax)) (oR .r8)),                              -- 33
    jccL .c exhaustedL,                                                -- 34 len - qb < la
    movRM .rdx (tdesc .rdx (tab.base64 (0 : ArrId))),                  -- 35
    i64 (.lea (rr .r9) (mbi .rdx .r9 .W64)),                           -- 36 r9 := &B[0]
    i64 (.sub (.reg (rr .r14)) (oR .r8)),                              -- 37
    jccL .c exhaustedL,                                                -- 38 fuel < la
    .label (ncL "L"),                                                  -- 39
    i64 (.sub (.reg (rr .r8)) (oI 1)),                                 -- 40 k := k - 1
    movRM .rax (mbi .rdi .r8 .W64),                                    -- 41
    movRM .rdx (mbi .r9 .r8 .W64),                                     -- 42
    i64 (.cmp (.reg (rr .rax)) (oR .rdx)),                             -- 43
    jccL .c (ncL "Z0"),                                                -- 44
    jccL .a (ncL "Z2"),                                                -- 45
    i64 (.cmp (.reg (rr .r8)) (.imm (.int64 (0 : Word).toInt64))),     -- 46
    jccL .nz (ncL "L"),                                                -- 47
    .label (ncL "Z1"),                                                 -- 48
    movRI .rax 1,                                                      -- 49
    i64 .ret,                                                          -- 50
    .label (ncL "Z0"),                                                 -- 51
    movRI .rax 0,                                                      -- 52
    i64 .ret,                                                          -- 53
    .label (ncL "Z2"),                                                 -- 54
    movRI .rax 2,                                                      -- 55
    i64 .ret ]                                                         -- 56

end L.AsmEsc
