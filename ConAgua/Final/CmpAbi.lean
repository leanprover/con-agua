module

public import ConAgua.Final.CmpStub
public import ConAgua.Final.BufChain
public import ConAgua.Final.SeqLayout
import Kraken.X64.Registers

@[expose] public section

/-!
# The compared run's driver `ca_compare`: the calls and what a run means (lane compare)

The compared run's entries (`ca_start_ac` threaded, `ca_start_c` sequential): how the harness
calls them (`CmpCall`), the L runs they make (the front `CmpFront45`, then mode `7` or `6` and the
jobs), and what an accepting or failing run means (`CmpAccT`, `CmpErrT`, `CmpAccS`, `CmpErrS`).
-/

namespace ConAgua.Final

open L L.Compiler L.Arena

/-- **A compared run's call, with the solution's address as a parameter** (internal: the machine
proofs' form of `AbiCall bC (some bS) pb dm ra`, `AbiCall.cmp`): `ca_start`'s six arguments as `AbiArgs` says (the
challenge's bytes `bC` as the input, the pin data `pb`, a zero region), and on the machine stack
past the return address the solution's buffer `sa` and its length; the buffer holds `bS`, is in
the address space, apart from the region, from both other buffers and from the stack window. -/
structure CmpCall (bC bS pb : ByteArray) (sa : Word) (dm : MachineData) (ra : Word) : Prop
    extends AbiArgs bC pb dm ra where
  hsa : rdW dm.dmem (A (dm.regs.rsp.toNat + 8)) = some sa
  hsn : rdW dm.dmem (A (dm.regs.rsp.toNat + 16)) = some (UInt64.ofNat bS.size)
  hS : ∀ i (h : i < bS.size), dm.dmem.get? (A (sa.toNat + i)) = some bS[i]
  hSEnd : sa.toNat + bS.size < 2 ^ 64
  hSDisj : ∀ x, sa.toNat ≤ x → x < sa.toNat + bS.size →
    (x < dm.regs.r8.toNat ∨ dm.regs.r8.toNat + dm.regs.r9.toNat ≤ x) ∧
    ¬ (dm.regs.rdi.toNat ≤ x ∧ x < dm.regs.rdi.toNat + bC.size) ∧
    ¬ (dm.regs.rdx.toNat ≤ x ∧ x < dm.regs.rdx.toNat + pb.size) ∧
    (x < dm.regs.rsp.toNat - 24 ∨ dm.regs.rsp.toNat + 8 ≤ x)
  hsEnd : dm.regs.rsp.toNat + 24 < 2 ^ 64
  hsArgs : ∀ x, dm.regs.rsp.toNat + 8 ≤ x → x < dm.regs.rsp.toNat + 24 →
    x < dm.regs.r8.toNat ∨ dm.regs.r8.toNat + dm.regs.r9.toNat ≤ x

/-- **A compared run's call** (`AbiCall` with a solution) as the machine proofs take it, at the
solution's address `solAddr dm`. -/
theorem AbiCall.cmp {bC bS pb : ByteArray} {dm : MachineData} {ra : Word}
    (hc : AbiCall bC (some bS) pb dm ra) : CmpCall bC bS pb (solAddr dm) dm ra := by
  have h := hc.hsol bS rfl
  exact ⟨hc.toAbiArgs, h.hsa, h.hsn, h.hS, h.hSEnd, h.hSDisj, h.hsEnd, h.hsArgs⟩

/-- A run of `check` with the final theorems' fuel. -/
abbrev cmpRun (p : Prog) (m : Mem) : Except Err (List Word × Mem) := L.run p abiFuel "check" [] m

/-- Mode `4`'s memory: the loaded memory of the challenge's bytes with the mode word `4`. -/
def cmpM4 (tab : Tab) (mode : GVar) (bC pb : ByteArray) : Mem := (loadMem bC pb (abiSz tab)).setG mode 4

/-- Mode `5`'s memory: mode `4`'s final memory with the input replaced by the solution's bytes and
the mode word `5`. -/
def cmpM5 (mode : GVar) (m4 : Mem) (bS : ByteArray) : Mem := (cmpIn m4 bS).setG mode 5

/-- The frozen buffer mode `5` leaves: the first `OUT[1]` words of `out`. -/
def cmpBuf (out : ArrId) (m : Mem) : Array Word := (m.arr64 out).extract 0 ((m.arr64 out).getD 1 0).toNat

/-! ## The compared run of lane compare2: `ca_start_ac`, `ca_start_c`

Both run modes `4` and `5` (the front, `CmpFront45`), then on mode `5`'s final memory with the
mode word `7` (threaded: one frozen buffer with two headers) or `6` (sequential: the header only),
the sequential run then entry 2 in place with the mode word `8` (the solution's jobs `[0, kS)`)
and, on the memory that run left, `9` (the challenge's jobs `[0, kC)`). -/

/-- **The front**: modes `4` and `5` (the solution's bytes) ran, each returning `2^63` or more, mode
`5` ending in `m5` with the result `rs5` (`2^63 + kS`). -/
def CmpFront45 (tab : Tab) (p : Prog) (mode : GVar) (bC bS pb : ByteArray) (rs5 : List Word) (m5 : Mem) :
    Prop :=
  bC.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧ bS.size < 2 ^ 63 ∧
  ∃ rs4 m4, cmpRun p (cmpM4 tab mode bC pb) = .ok (rs4, m4) ∧ 2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧
    cmpRun p (cmpM5 mode m4 bS) = .ok (rs5, m5) ∧ 2 ^ 63 ≤ (rs5.getD 0 0).toNat

/-- **The front stops with an accept**: mode `4` returns `ACCEPT`, or it returns `2^63` or more and
mode `5` returns `ACCEPT`. -/
def CmpFrontAcc45 (tab : Tab) (p : Prog) (mode : GVar) (bC bS pb : ByteArray) : Prop :=
  bC.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧ ∃ rs4 m4, cmpRun p (cmpM4 tab mode bC pb) = .ok (rs4, m4) ∧
    (rs4.getD 0 0 = ACCEPT ∨ (2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧ bS.size < 2 ^ 63 ∧
      ∃ rs5 m5, cmpRun p (cmpM5 mode m4 bS) = .ok (rs5, m5) ∧ rs5.getD 0 0 = ACCEPT))

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

/-- **A return of `ca_start_ac` with `rdx = 0`, `rax ≥ 2^63`** (the jobs' count `kS + kC` in `rax`,
the memory `d`): the front, mode `7` returning `2^63 + kC`, `rax = 2^63 + kS + kC`, and the region at
`base` holds mode `7`'s final memory in the stub's layout (the solution's bytes at `sa` as the
input, the pin data at `pins`). -/
def CmpHiT (tab : Tab) (p : Prog) (mode : GVar) (bC bS pb : ByteArray) (base sa pins : Nat) (rax : Word)
    (d : DataMem) : Prop :=
  ∃ rs5 m5 rs7 m7, CmpFront45 tab p mode bC bS pb rs5 m5 ∧ cmpRun p (m5.setG mode 7) = .ok (rs7, m7) ∧
    2 ^ 63 ≤ (rs7.getD 0 0).toNat ∧
    rax = 9223372036854775808 + ((rs5.getD 0 0 - 9223372036854775808) + (rs7.getD 0 0 - 9223372036854775808)) ∧
    MemRel (abiLayout tab base sa bS.size pins pb.size) m7 d

/-- **An accepting return of `ca_start_c`** (`rdx = 0`, `rax = ACCEPT`): the front stopped with an
accept; or mode `6` returned `ACCEPT`; or it returned `2^63 + kC`, entry 2 in place with the mode
word `8` over `[0, kS)` returned `ACCEPT`, and on the memory that run left, with the mode word
`9` over `[0, kC)`, too. -/
def CmpAccS (tab : Tab) (p : Prog) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (bC bS pb : ByteArray) : Prop :=
  CmpFrontAcc45 tab p mode bC bS pb ∨ ∃ rs5 m5, CmpFront45 tab p mode bC bS pb rs5 m5 ∧
    ∃ rs6 m6, cmpRun p (m5.setG mode 6) = .ok (rs6, m6) ∧
    (rs6.getD 0 0 = ACCEPT ∨ (2 ^ 63 ≤ (rs6.getD 0 0).toNat ∧
      ∃ rs8 m8, cmpRun p (seqMemW m6 mode plo phi out hdrf ctlf hw 8 0 (rs5.getD 0 0 - 9223372036854775808)) =
        .ok (rs8, m8) ∧ rs8.getD 0 0 = ACCEPT ∧
      ∃ rs9 m9, cmpRun p (seqNext m8 mode plo phi 9 0 (rs6.getD 0 0 - 9223372036854775808)) = .ok (rs9, m9) ∧
        rs9.getD 0 0 = ACCEPT))

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
