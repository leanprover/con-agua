module

public import ConAgua.Final.CmpStub
public import ConAgua.Final.BufChain
public import ConAgua.Final.SeqLayout
import Kraken.X64.Registers

@[expose] public section

/-!
# The compared run's driver `ca_compare`: the calls and what a run means (lane compare)

`ca_compare(c, c_len, pins, pins_len, base, base_len, s, s_len)` (`ConAgua/Compiler/AbiCmp.lean`)
runs `check` on one region `R = [base, base + abiNeed)` in modes `4`, `5`, `6`, the solution's
jobs on a worker region `W = [base + cmpW, base + cmpNeed)` (`ca_check_b`, one call per job), and
the challenge's jobs in place (`ca_check_seq`). Here: how the harness calls it (`CmpCall`), the
L-level facts about `check` the machine proof needs and cannot see (`CmpGuard`: the buffer's
geometry after mode `5` and that every job keeps the buffer's header; discharged at the L level).
The jobs run on the buffer as the previous job left it (`bufSeq`: a job's stores into the frozen
arrays are stores into the buffer), and mode `6` on mode `5`'s memory with that buffer (`cmpM6`), and what an accepting or failing run means (`CmpAccepts`, `CmpErr`). The theorem:
`ConAgua/Final/CmpOutcome.lean`.
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

/-! ## The buffer along the solution's jobs

A job runs on the buffer as the previous job left it: its frozen arrays are the buffer's entries
(`bufMemG`), so the job's stores into them are stores into the buffer. `bufNext fz B r`: the
buffer after a job that ends in `r`; `bufSeq`: the buffer before each job. -/

/-- `B` with the words `[o, o + l)` replaced by `a`'s words `0‥l - 1`. -/
def bufPut (B : Array Word) (o l : Nat) (a : Array Word) : Array Word :=
  B.mapIdx fun w x => if o ≤ w ∧ w < o + l then a.getD (w - o) 0 else x

theorem bufPut_size (B : Array Word) (o l : Nat) (a : Array Word) : (bufPut B o l a).size = B.size :=
  Array.size_mapIdx ..

theorem bufPut_getD (B : Array Word) (o l : Nat) (a : Array Word) (w : Nat) :
    (bufPut B o l a).getD w 0 = if w < B.size ∧ o ≤ w ∧ w < o + l then a.getD (w - o) 0 else B.getD w 0 := by
  by_cases hw : w < B.size
  · simp [bufPut, Array.getD_eq_getD_getElem?, hw]
  · simp [bufPut, Array.getD_eq_getD_getElem?, hw]

section puts
variable (O Ln : Nat → Nat) (V : Nat → Array Word)

theorem puts_size : ∀ (L : List Nat) (B : Array Word),
    (L.foldl (fun B' i => bufPut B' (O i) (Ln i) (V i)) B).size = B.size
  | [], _ => rfl
  | i :: L, B => by rw [List.foldl_cons, puts_size L, bufPut_size]

theorem puts_out (w : Nat) : ∀ (L : List Nat) (B : Array Word), (∀ i ∈ L, ¬ (O i ≤ w ∧ w < O i + Ln i)) →
    (L.foldl (fun B' i => bufPut B' (O i) (Ln i) (V i)) B).getD w 0 = B.getD w 0
  | [], _, _ => rfl
  | i :: L, B, h => by
    rw [List.foldl_cons, puts_out w L _ (fun i' hi' => h i' (List.mem_cons_of_mem _ hi')), bufPut_getD]
    have := h i List.mem_cons_self
    simp only [this, and_false, ite_false]

theorem puts_in (w k : Nat) (hk : O k ≤ w ∧ w < O k + Ln k) : ∀ (L : List Nat) (B : Array Word), k ∈ L →
    (∀ i ∈ L, O i ≤ w ∧ w < O i + Ln i → i = k) → w < B.size →
    (L.foldl (fun B' i => bufPut B' (O i) (Ln i) (V i)) B).getD w 0 = (V k).getD (w - O k) 0
  | [], _, h, _, _ => absurd h (by simp)
  | i :: L, B, hm, hu, hw => by
    rw [List.foldl_cons]
    by_cases hkL : k ∈ L
    · exact puts_in w k hk L _ hkL (fun i' hi' => hu i' (List.mem_cons_of_mem _ hi')) (by rw [bufPut_size]; exact hw)
    · have hik : i = k := by
        rcases List.mem_cons.mp hm with h | h
        · exact h.symm
        · exact absurd h hkL
      subst hik
      rw [puts_out O Ln V w L _ (fun i' hi' hin => hkL (hu i' (List.mem_cons_of_mem _ hi') hin ▸ hi')), bufPut_getD]
      simp only [hw, hk, and_self, ite_true]

end puts

/-- Word `w` is in entry `i` of `B`. -/
def InEnt (B : Array Word) (i w : Nat) : Prop := (bufEntry B i).1 ≤ w ∧ w < (bufEntry B i).1 + (bufEntry B i).2

/-- **The buffer after a job**: `B` with each frozen entry `i`'s words replaced by `r`'s array
`fz[i]` (the job's final memory). -/
def bufNext (fz : List TieredArray) (B : Array Word) (r : Mem) : Array Word :=
  (List.range fz.length).foldl
    (fun B' i => bufPut B' (bufEntry B i).1 (bufEntry B i).2 ((fz.map r.arr64).getD i #[])) B

/-- **The buffer's sequence**: the buffer before job `j`, from `B` before job `0` and the worker
memories `rm` (`rm (j + 1)` the memory job `j` ends in). -/
def bufSeq (fz : List TieredArray) (B : Array Word) (rm : Nat → Mem) : Nat → Array Word
  | 0 => B
  | j + 1 => bufNext fz (bufSeq fz B rm j) (rm (j + 1))

/-- **The buffer's own geometry** (what stays the same along the jobs): the header is entry `0`
(at word `0`, holding every entry's words `8 + 2i`, `9 + 2i`); the entries inside `B` and
pairwise apart (or empty). -/
structure BufOk (n : Nat) (B : Array Word) : Prop where
  hdr0 : (bufEntry B 0).1 = 0
  hdr : ∀ i < n, 9 + 2 * i < (bufEntry B 0).2
  ent : ∀ i < n, (bufEntry B i).1 + (bufEntry B i).2 ≤ B.size
  disj : ∀ i < n, ∀ i' < n, i ≠ i' →
    (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1 ∨
    (bufEntry B i').1 + (bufEntry B i').2 ≤ (bufEntry B i).1 ∨ (bufEntry B i).2 = 0 ∨ (bufEntry B i').2 = 0

/-- Two entries apart (or empty) share no word. -/
theorem inEnt_uniq {B : Array Word} {n : Nat}
    (hd : ∀ i < n, ∀ i' < n, i ≠ i' →
      (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1 ∨
      (bufEntry B i').1 + (bufEntry B i').2 ≤ (bufEntry B i).1 ∨ (bufEntry B i).2 = 0 ∨ (bufEntry B i').2 = 0)
    {i i' w : Nat} (hi : i < n) (hi' : i' < n) (h : InEnt B i w) (h' : InEnt B i' w) : i' = i := by
  refine Classical.byContradiction fun hne => ?_
  unfold InEnt at h h'
  rcases hd i hi i' hi' (Ne.symm hne) with e | e | e | e <;> omega

section next
variable {fz : List TieredArray} {B : Array Word} {r : Mem}

theorem map_getD_arr (r : Mem) {i : Nat} (hi : i < fz.length) : (fz.map r.arr64).getD i #[] = r.arr64 fz[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem bufNext_size (fz : List TieredArray) (B : Array Word) (r : Mem) : (bufNext fz B r).size = B.size :=
  puts_size _ _ _ _ _

theorem bufNext_out {w : Nat} (h : ∀ i < fz.length, ¬ InEnt B i w) : (bufNext fz B r).getD w 0 = B.getD w 0 :=
  puts_out _ _ _ w _ _ fun i hi => h i (List.mem_range.mp hi)

theorem bufNext_in (hd : ∀ i < fz.length, ∀ i' < fz.length, i ≠ i' →
      (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1 ∨
      (bufEntry B i').1 + (bufEntry B i').2 ≤ (bufEntry B i).1 ∨ (bufEntry B i).2 = 0 ∨ (bufEntry B i').2 = 0)
    {i w : Nat} (hi : i < fz.length) (h : InEnt B i w) (hw : w < B.size) :
    (bufNext fz B r).getD w 0 = (r.arr64 fz[i]).getD (w - (bufEntry B i).1) 0 := by
  rw [← map_getD_arr r hi]
  exact puts_in (fun i => (bufEntry B i).1) (fun i => (bufEntry B i).2) (fun i => (fz.map r.arr64).getD i #[])
    w i h _ _ (List.mem_range.mpr hi)
    (fun i' hi' h' => inEnt_uniq hd hi (List.mem_range.mp hi') h h') hw

/-- **The header survives a job that keeps it**: entries the same. -/
theorem bufNext_entry (hB : BufOk fz.length B) (hh : ∀ h : 0 < fz.length, r.arr64 fz[0] = bufImg B 0)
    {i : Nat} (hi : i < fz.length) : bufEntry (bufNext fz B r) i = bufEntry B i := by
  have h0 : 0 < fz.length := by omega
  have hs := hB.ent 0 h0
  have hd := hB.hdr i hi
  have key : ∀ w, w < (bufEntry B 0).2 → (bufNext fz B r).getD w 0 = B.getD w 0 := by
    intro w hw
    have hin : InEnt B 0 w := ⟨by rw [hB.hdr0]; omega, by omega⟩
    rw [bufNext_in hB.disj h0 hin (by omega), hh h0, hB.hdr0, Nat.sub_zero]
    simp only [bufImg, hB.hdr0, Nat.zero_add, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
    rw [ite_eq_left (by omega)]
  simp only [bufEntry]
  rw [key _ (by omega), key _ (by omega)]

theorem BufOk.next (hB : BufOk fz.length B) (hh : ∀ h : 0 < fz.length, r.arr64 fz[0] = bufImg B 0) :
    BufOk fz.length (bufNext fz B r) := by
  have e := fun {i} (hi : i < fz.length) => bufNext_entry (r := r) hB hh hi
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i hi i' hi' hne => ?_⟩
  · by_cases h0 : 0 < fz.length
    · rw [e h0]; exact hB.hdr0
    · have h0' : fz.length = 0 := by omega
      simp only [bufNext, h0', List.range_zero, List.foldl_nil]; exact hB.hdr0
  · rw [e (by omega)]; exact hB.hdr i hi
  · rw [e hi, bufNext_size]; exact hB.ent i hi
  · rw [e hi, e hi']; exact hB.disj i hi i' hi' hne

/-- **A frozen entry of the next buffer** is the job's array (of the entry's length). -/
theorem bufNext_img (hB : BufOk fz.length B) {i : Nat} (hi : i < fz.length)
    (he : bufEntry (bufNext fz B r) i = bufEntry B i) (hs : (r.arr64 fz[i]).size = (bufEntry B i).2) :
    bufImg (bufNext fz B r) i = r.arr64 fz[i] := by
  have hent := hB.ent i hi
  apply Array.ext
  · simp only [bufImg, he, Array.size_extract, bufNext_size, hs]; omega
  · intro t h1 h2
    simp only [bufImg, he, Array.getElem_extract]
    have hw : (bufEntry B i).1 + t < B.size := by
      simp only [bufImg, he, Array.size_extract, bufNext_size] at h1; omega
    have := bufNext_in (r := r) hB.disj hi ⟨Nat.le_add_right _ _, by omega⟩ hw
    simp only [Nat.add_sub_cancel_left] at this
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [bufNext_size]; exact hw),
      Option.getD_some, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2, Option.getD_some] at this
    exact this

theorem bufSeq_congr {fz : List TieredArray} {B : Array Word} {rm rm' : Nat → Mem} :
    ∀ j, (∀ i ≤ j, rm i = rm' i) → bufSeq fz B rm j = bufSeq fz B rm' j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [bufSeq]
    rw [bufSeq_congr j (fun i hi => h i (by omega)), h (j + 1) (Nat.le_refl _)]

theorem bufSeq_size (fz : List TieredArray) (B : Array Word) (rm : Nat → Mem) :
    ∀ j, (bufSeq fz B rm j).size = B.size
  | 0 => rfl
  | j + 1 => by simp only [bufSeq]; rw [bufNext_size, bufSeq_size fz B rm j]

end next

/-- **The buffer's geometry after mode `5`** (`BufGeom`'s L-level part): its length word inside
`out`, and `BufOk`. -/
def CmpBufOk (fz : List TieredArray) (out : ArrId) (m : Mem) : Prop :=
  ((m.arr64 out).getD 1 0).toNat ≤ (m.arr64 out).size ∧ BufOk fz.length (cmpBuf out m)

/-- **A job keeps the header**: every run of `check` on a job's memory ends with the frozen array
`fz[0]` (the header) as it started, the buffer's entry `0`. -/
def CmpHdrKeep (p : Prog) (mode plo phi : GVar) (fz own : List TieredArray) : Prop :=
  ∀ (B : Array Word) (r : Mem) (j : Word) rs r', cmpRun p (bufMemG fz own plo phi mode B r j) = .ok (rs, r') →
    ∀ h : 0 < fz.length, r'.arr64 fz[0] = bufImg B 0

/-- The jobs `j < n` of the solution, from the worker memories `rm`, each on the buffer as the
previous job left it (`bufSeq`, from `B`): each accepts and ends in the next. -/
def CmpJobs (p : Prog) (mode plo phi : GVar) (fz own : List TieredArray) (B : Array Word) (rm : Nat → Mem)
    (n : Nat) : Prop :=
  ∀ j < n, ∃ rs, cmpRun p (bufMemG fz own plo phi mode (bufSeq fz B rm j) (rm j) (UInt64.ofNat j)) =
    .ok (rs, rm (j + 1)) ∧ rs.getD 0 0 = ACCEPT

/-- **The buffers along accepting jobs keep their geometry** (the header kept by each job). -/
theorem bufSeq_ok {p : Prog} {mode plo phi : GVar} {fz own : List TieredArray} {B : Array Word}
    {rm : Nat → Mem} (hB : BufOk fz.length B) (hh : CmpHdrKeep p mode plo phi fz own) :
    ∀ n, CmpJobs p mode plo phi fz own B rm n → ∀ j ≤ n, BufOk fz.length (bufSeq fz B rm j) := by
  intro n hj j hjn
  induction j with
  | zero => exact hB
  | succ j ih =>
    obtain ⟨rs, hr, -⟩ := hj j (by omega)
    exact (ih (by omega)).next (hh _ _ _ _ _ hr)

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

/-! ## A memory relation survives a change outside its cells -/

/-! ## The region `R` across the solution's jobs -/

end ConAgua.Final
