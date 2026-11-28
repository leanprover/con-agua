module

public import ConAgua.Final.Statement
public import ConAgua.Compiler.Compile

@[expose] public section

/-!
# The compared run's driver `ca_compare`: the calls and what a run means (lane compare)

The compared run's entries (`ca_start_ac` threaded, `ca_start_c` sequential): how the L runs work
(the front `CmpFront45`, then mode `7` or `6` and the jobs), and what an accepting or failing run
means (`CmpAccT`, `CmpErrT`, `CmpAccS`, `CmpErrS`), together with their `sz`-parametric
counterparts (`CmpFront45Sz`, `CmpFrontAcc45Sz`, `CmpAccSSz`).
-/

namespace L.Compiler

/-- The fuel of the L program's run that the final theorems speak of. -/
def abiFuel : Nat := 2 ^ 62 - 1

/-- Every word array gets its whole slot. -/
def abiWords : Nat := 2 ^ 32

/-- The length the stubs give word array `s` where they give it memory: the table-relative array
(`Tab.tbl64`) its minimum length, every other a whole slot. -/
def abiSz (tab : Tab) (s : TieredArray) : Nat :=
  match tab.tbl64 s with
  | some _ => tab.min64 s
  | none => abiWords

end L.Compiler

namespace ConAgua.Final

open L L.Compiler L.Arena

/-- The L memory `m` with the input `IN` replaced by the bytes `bs`. -/
def cmpIn (m : Mem) (bs : ByteArray) : Mem :=
  { m with bytes := fun a => if a = IN then bs.data else m.bytes a }

/-- Replacing the input by itself changes nothing. -/
theorem cmpIn_self (m : Mem) : cmpIn m ⟨m.arr8 IN⟩ = m := by
  cases m with
  | mk bytes words glob =>
    simp only [cmpIn, Mem.arr8, Mem.mk.injEq, and_true]
    funext a
    by_cases h : a = IN
    · subst h; simp
    · simp [h]

theorem cmpIn_arr64 (m : Mem) (bs : ByteArray) (s : TieredArray) : (cmpIn m bs).arr64 s = m.arr64 s := rfl
theorem cmpIn_glob (m : Mem) (bs : ByteArray) : (cmpIn m bs).glob = m.glob := rfl
theorem cmpIn_setG (m : Mem) (bs : ByteArray) (g : GVar) (v : Word) :
    (cmpIn m bs).setG g v = cmpIn (m.setG g v) bs := rfl

/-- `ca_check_seq`'s memory before the globals: `m`'s word arrays and globals, but `out`, `ctlf`
and the byte arrays empty and `hdrf` the first `hw` words of `out`. -/
def seqMem0 (m : Mem) (out hdrf ctlf : ArrId) (hw : Nat) : Mem where
  bytes _ := #[]
  words s := if s = ↑out ∨ s = ↑ctlf then #[] else if s = ↑hdrf then (m.arr64 out).extract 0 hw else m.words s
  glob := m.glob

/-- `M` with `plo := lo`, `phi := hi`, `mode := w` (what `ca_check_seq_g` stores). -/
def seqNext (M : Mem) (mode plo phi : GVar) (w lo hi : Word) : Mem :=
  ((M.setG plo lo).setG phi hi).setG mode w

/-- **The memory `ca_check_seq_m` runs `check` on**: `seqMem0 m` with `plo := lo`, `phi := hi`,
`mode := w`. -/
def seqMemW (m : Mem) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat) (w lo hi : Word) : Mem :=
  seqNext (seqMem0 m out hdrf ctlf hw) mode plo phi w lo hi

/-- **The memory `ca_check_seq` runs `check` on**: `seqMem0 m` with `plo := lo`, `phi := hi`,
`mode := 2`. -/
def seqMem (m : Mem) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat) (lo hi : Word) : Mem :=
  seqMemW m mode plo phi out hdrf ctlf hw 2 lo hi

theorem seqMem0_arr8 (m : Mem) (out hdrf ctlf : ArrId) (hw a : Nat) :
    (seqMem0 m out hdrf ctlf hw).arr8 a = #[] := rfl

theorem seqMem0_arr64 (m : Mem) (out hdrf ctlf : ArrId) (hw : Nat) (s : TieredArray) :
    (seqMem0 m out hdrf ctlf hw).arr64 s =
      if s = ↑out ∨ s = ↑ctlf then #[] else if s = ↑hdrf then (m.arr64 out).extract 0 hw else m.arr64 s := rfl

/-- A run of `check` with the final theorems' fuel. -/
abbrev cmpRun (p : Prog) (m : Mem) : Except Err (List Word × Mem) := L.run p abiFuel "check" [] m

/-- Mode `4`'s memory (parametric in word-array sizes `sz`). -/
def cmpM4Sz (sz : TieredArray → Nat) (mode : GVar) (bC pb : ByteArray) : Mem :=
  (loadMem bC pb sz).setG mode 4

/-- Mode `4`'s memory: the loaded memory of the challenge's bytes with the mode word `4`. -/
def cmpM4 (tab : Tab) (mode : GVar) (bC pb : ByteArray) : Mem :=
  cmpM4Sz (abiSz tab) mode bC pb

/-- Mode `5`'s memory: mode `4`'s final memory with the input replaced by the solution's bytes and
the mode word `5`. -/
def cmpM5 (mode : GVar) (m4 : Mem) (bS : ByteArray) : Mem := (cmpIn m4 bS).setG mode 5

/-! ## The compared run of lane compare2: `ca_start_ac`, `ca_start_c`

Both run modes `4` and `5` (the front, `CmpFront45`), then on mode `5`'s final memory with the
mode word `7` (threaded: one frozen buffer with two headers) or `6` (sequential: the header only),
the sequential run then entry 2 in place with the mode word `8` (the solution's jobs `[0, kS)`)
and, on the memory that run left, `9` (the challenge's jobs `[0, kC)`). -/

/-- **The front (parametric in `sz`)**: modes `4` and `5` (the solution's bytes) ran, each
returning `2^63` or more, mode `5` ending in `m5` with the result `rs5` (`2^63 + kS`). -/
def CmpFront45Sz (sz : TieredArray → Nat) (p : Prog) (mode : GVar) (bC bS pb : ByteArray)
    (rs5 : List Word) (m5 : Mem) : Prop :=
  bC.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧ bS.size < 2 ^ 63 ∧
  ∃ rs4 m4, cmpRun p (cmpM4Sz sz mode bC pb) = .ok (rs4, m4) ∧ 2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧
    cmpRun p (cmpM5 mode m4 bS) = .ok (rs5, m5) ∧ 2 ^ 63 ≤ (rs5.getD 0 0).toNat

/-- **The front stops with an accept (parametric in `sz`)**: mode `4` returns `ACCEPT`, or it
returns `2^63` or more and mode `5` returns `ACCEPT`. -/
def CmpFrontAcc45Sz (sz : TieredArray → Nat) (p : Prog) (mode : GVar) (bC bS pb : ByteArray) : Prop :=
  bC.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧
  ∃ rs4 m4, cmpRun p (cmpM4Sz sz mode bC pb) = .ok (rs4, m4) ∧
    (rs4.getD 0 0 = ACCEPT ∨ (2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧ bS.size < 2 ^ 63 ∧
      ∃ rs5 m5, cmpRun p (cmpM5 mode m4 bS) = .ok (rs5, m5) ∧ rs5.getD 0 0 = ACCEPT))

/-- **An accepting return of `ca_start_c` (parametric in `sz`)**: the front stopped with an
accept; or mode `6` returned `ACCEPT`; or it returned `2^63 + kC`, entry 2 in place with the mode
word `8` over `[0, kS)` returned `ACCEPT`, and on the memory that run left, with the mode word
`9` over `[0, kC)`, too. -/
def CmpAccSSz (sz : TieredArray → Nat) (p : Prog) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (bC bS pb : ByteArray) : Prop :=
  CmpFrontAcc45Sz sz p mode bC bS pb ∨ ∃ rs5 m5, CmpFront45Sz sz p mode bC bS pb rs5 m5 ∧
    ∃ rs6 m6, cmpRun p (m5.setG mode 6) = .ok (rs6, m6) ∧
    (rs6.getD 0 0 = ACCEPT ∨ (2 ^ 63 ≤ (rs6.getD 0 0).toNat ∧
      ∃ rs8 m8, cmpRun p (seqMemW m6 mode plo phi out hdrf ctlf hw 8 0 (rs5.getD 0 0 - 9223372036854775808)) =
        .ok (rs8, m8) ∧ rs8.getD 0 0 = ACCEPT ∧
      ∃ rs9 m9, cmpRun p (seqNext m8 mode plo phi 9 0 (rs6.getD 0 0 - 9223372036854775808)) = .ok (rs9, m9) ∧
        rs9.getD 0 0 = ACCEPT))

/-- **The front**: modes `4` and `5` (the solution's bytes) ran, each returning `2^63` or more, mode
`5` ending in `m5` with the result `rs5` (`2^63 + kS`). -/
abbrev CmpFront45 (tab : Tab) (p : Prog) (mode : GVar) (bC bS pb : ByteArray) (rs5 : List Word) (m5 : Mem) :
    Prop :=
  CmpFront45Sz (abiSz tab) p mode bC bS pb rs5 m5

/-- **The front stops with an accept**: mode `4` returns `ACCEPT`, or it returns `2^63` or more and
mode `5` returns `ACCEPT`. -/
abbrev CmpFrontAcc45 (tab : Tab) (p : Prog) (mode : GVar) (bC bS pb : ByteArray) : Prop :=
  CmpFrontAcc45Sz (abiSz tab) p mode bC bS pb

/-- **The front fails**: mode `4`'s run, or (mode `4` returning `2^63` or more) mode `5`'s, fails
with an error of code `k`. -/
def CmpFrontErr45 (tab : Tab) (p : Prog) (mode : GVar) (bC bS pb : ByteArray) (k : Word) : Prop :=
  bC.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧
  ((∃ e, cmpRun p (cmpM4 tab mode bC pb) = .error e ∧ e.code = k) ∨
   ∃ rs4 m4, cmpRun p (cmpM4 tab mode bC pb) = .ok (rs4, m4) ∧ 2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧
    bS.size < 2 ^ 63 ∧ ∃ e, cmpRun p (cmpM5 mode m4 bS) = .error e ∧ e.code = k)

/-- **An accepting return of `ca_start_ac`** (`rdx = 0`, `rax = ACCEPT`): the front stopped with an
accept, or mode `7` returned `ACCEPT`. -/
def CmpAccT (tab : Tab) (p : Prog) (mode : GVar) (bC bS pb : ByteArray) : Prop :=
  CmpFrontAcc45 tab p mode bC bS pb ∨ ∃ rs5 m5, CmpFront45 tab p mode bC bS pb rs5 m5 ∧
    ∃ rs7 m7, cmpRun p (m5.setG mode 7) = .ok (rs7, m7) ∧ rs7.getD 0 0 = ACCEPT

/-- **A failing return of `ca_start_ac`** (`rdx = 2`): the front, or mode `7`, failed with an error
of code `k`. -/
def CmpErrT (tab : Tab) (p : Prog) (mode : GVar) (bC bS pb : ByteArray) (k : Word) : Prop :=
  CmpFrontErr45 tab p mode bC bS pb k ∨ ∃ rs5 m5, CmpFront45 tab p mode bC bS pb rs5 m5 ∧
    ∃ e, cmpRun p (m5.setG mode 7) = .error e ∧ e.code = k

/-- **An accepting return of `ca_start_c`** (`rdx = 0`, `rax = ACCEPT`): the front stopped with an
accept; or mode `6` returned `ACCEPT`; or it returned `2^63 + kC`, entry 2 in place with the mode
word `8` over `[0, kS)` returned `ACCEPT`, and on the memory that run left, with the mode word
`9` over `[0, kC)`, too. -/
abbrev CmpAccS (tab : Tab) (p : Prog) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (bC bS pb : ByteArray) : Prop :=
  CmpAccSSz (abiSz tab) p mode plo phi out hdrf ctlf hw bC bS pb

/-- **A failing return of `ca_start_c`** (`rdx = 2`): the front, mode `6`, the solution's jobs or
(those accepting) the challenge's jobs failed with an error of code `k`. -/
def CmpErrS (tab : Tab) (p : Prog) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (bC bS pb : ByteArray) (k : Word) : Prop :=
  CmpFrontErr45 tab p mode bC bS pb k ∨ ∃ rs5 m5, CmpFront45 tab p mode bC bS pb rs5 m5 ∧
    ((∃ e, cmpRun p (m5.setG mode 6) = .error e ∧ e.code = k) ∨
     ∃ rs6 m6, cmpRun p (m5.setG mode 6) = .ok (rs6, m6) ∧ 2 ^ 63 ≤ (rs6.getD 0 0).toNat ∧
      ((∃ e, cmpRun p (seqMemW m6 mode plo phi out hdrf ctlf hw 8 0 (rs5.getD 0 0 - 9223372036854775808)) =
          .error e ∧ e.code = k) ∨
       ∃ rs8 m8, cmpRun p (seqMemW m6 mode plo phi out hdrf ctlf hw 8 0 (rs5.getD 0 0 - 9223372036854775808)) =
          .ok (rs8, m8) ∧ rs8.getD 0 0 = ACCEPT ∧
        ∃ e, cmpRun p (seqNext m8 mode plo phi 9 0 (rs6.getD 0 0 - 9223372036854775808)) = .error e ∧ e.code = k))

end ConAgua.Final
