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

/-- **How the harness calls `ca_compare`**: `ca_start`'s six arguments as `AbiCall` says (the
challenge's bytes `bC` as the input, the pin data `pb`, a zero region), and on the machine stack
past the return address the solution's buffer `sa` and its length; the buffer holds `bS`, is in
the address space, apart from the region, from both other buffers and from the stack window. -/
structure CmpCall (bC bS pb : ByteArray) (sa : Word) (dm : MachineData) (ra : Word) : Prop
    extends AbiCall bC pb dm ra where
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

/-- `m` with the first `|B|` words of `out` replaced by `B`'s. -/
def cmpSetOut (out : ArrId) (m : Mem) (B : Array Word) : Mem :=
  { m with words := fun a => if a = (out : TieredArray) then
      (m.arr64 out).mapIdx (fun i x => if i < B.size then B.getD i 0 else x) else m.words a }

section setOut
variable (out : ArrId) (m : Mem) (B : Array Word)

theorem cmpSetOut_ne {c : TieredArray} (h : c ≠ (out : TieredArray)) : (cmpSetOut out m B).arr64 c = m.arr64 c := by
  simp [cmpSetOut, Mem.arr64, h]

theorem cmpSetOut_size (c : TieredArray) : ((cmpSetOut out m B).arr64 c).size = (m.arr64 c).size := by
  by_cases h : c = (out : TieredArray)
  · subst h; simp [cmpSetOut, Mem.arr64]
  · rw [cmpSetOut_ne out m B h]

theorem cmpSetOut_get {i : Nat} (h : i < ((cmpSetOut out m B).arr64 out).size) :
    ((cmpSetOut out m B).arr64 out)[i] =
      if i < B.size then B.getD i 0 else (m.arr64 out)[i]'(by rw [cmpSetOut_size] at h; exact h) := by
  simp [cmpSetOut, Mem.arr64]

@[simp] theorem cmpSetOut_bytes : (cmpSetOut out m B).bytes = m.bytes := rfl
@[simp] theorem cmpSetOut_glob : (cmpSetOut out m B).glob = m.glob := rfl

end setOut

/-- Mode `6`'s memory: mode `5`'s final memory with the buffer as the solution's jobs left it
(`B`) and the mode word `6`. -/
def cmpM6 (mode : GVar) (out : ArrId) (m5 : Mem) (B : Array Word) : Mem := (cmpSetOut out m5 B).setG mode 6

/-- **What the machine proof needs of `check` and cannot see** (L-level; for `checkerProg` a lemma,
not an assumption of the final theorem): after modes `4` and `5` (`4` returning `2^63` or more,
`5` too), the buffer's geometry holds; and every job keeps the header (`CmpHdrKeep`). -/
def CmpGuard (tab : Tab) (p : Prog) (mode plo phi : GVar) (out : ArrId) (fz own : List TieredArray)
    (bC bS pb : ByteArray) : Prop :=
  (∀ rs4 m4 rs5 m5, cmpRun p (cmpM4 tab mode bC pb) = .ok (rs4, m4) → 2 ^ 63 ≤ (rs4.getD 0 0).toNat →
    cmpRun p (cmpM5 mode m4 bS) = .ok (rs5, m5) → 2 ^ 63 ≤ (rs5.getD 0 0).toNat → CmpBufOk fz out m5) ∧
  CmpHdrKeep p mode plo phi fz own

/-- **What an accepting compared run means** (`9223372036854775808 = 2^63`): the buffers below
`2^63` bytes; mode `4` returns `ACCEPT` or `2^63 + _`; then mode `5` (from mode `4`'s memory with
the solution's bytes) returns `ACCEPT` or `2^63 + k`; then the jobs `j < k` on the buffer as the
jobs before left it, from the zero worker memory, each accepting; mode `6` from mode `5`'s memory
with that buffer returns `ACCEPT` or `2^63 + k'`; then `ca_check_seq`'s run for `[0, k')` accepts. -/
def CmpAccepts (tab : Tab) (p : Prog) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (fz own : List TieredArray) (bC bS pb : ByteArray) : Prop :=
  bC.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧ ∃ rs4 m4, cmpRun p (cmpM4 tab mode bC pb) = .ok (rs4, m4) ∧
    (rs4.getD 0 0 = ACCEPT ∨ (2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧ bS.size < 2 ^ 63 ∧
      ∃ rs5 m5, cmpRun p (cmpM5 mode m4 bS) = .ok (rs5, m5) ∧
      (rs5.getD 0 0 = ACCEPT ∨ (2 ^ 63 ≤ (rs5.getD 0 0).toNat ∧
        ∃ rm : Nat → Mem, rm 0 = zeroMem tab ∧
        CmpJobs p mode plo phi fz own (cmpBuf out m5) rm (rs5.getD 0 0 - 9223372036854775808).toNat ∧
        ∃ rs6 m6, cmpRun p (cmpM6 mode out m5 (bufSeq fz (cmpBuf out m5) rm
          (rs5.getD 0 0 - 9223372036854775808).toNat)) = .ok (rs6, m6) ∧
        (rs6.getD 0 0 = ACCEPT ∨ (2 ^ 63 ≤ (rs6.getD 0 0).toNat ∧ ∃ rs7 m7,
          cmpRun p (seqMem m6 mode plo phi out hdrf ctlf hw 0 (rs6.getD 0 0 - 9223372036854775808)) =
            .ok (rs7, m7) ∧ rs7.getD 0 0 = ACCEPT))))))

/-- **What a failing compared run means**: the same sequence up to one run that fails with an
error of code `k`. -/
def CmpErr (tab : Tab) (p : Prog) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (fz own : List TieredArray) (bC bS pb : ByteArray) (k : Word) : Prop :=
  bC.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧
  ((∃ e, cmpRun p (cmpM4 tab mode bC pb) = .error e ∧ e.code = k) ∨
   ∃ rs4 m4, cmpRun p (cmpM4 tab mode bC pb) = .ok (rs4, m4) ∧ 2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧
    bS.size < 2 ^ 63 ∧
    ((∃ e, cmpRun p (cmpM5 mode m4 bS) = .error e ∧ e.code = k) ∨
     ∃ rs5 m5, cmpRun p (cmpM5 mode m4 bS) = .ok (rs5, m5) ∧ 2 ^ 63 ≤ (rs5.getD 0 0).toNat ∧
      ∃ rm : Nat → Mem, rm 0 = zeroMem tab ∧
      ((∃ j < (rs5.getD 0 0 - 9223372036854775808).toNat, CmpJobs p mode plo phi fz own (cmpBuf out m5) rm j ∧
          ∃ e, cmpRun p (bufMemG fz own plo phi mode (bufSeq fz (cmpBuf out m5) rm j) (rm j) (UInt64.ofNat j)) =
            .error e ∧ e.code = k) ∨
       (CmpJobs p mode plo phi fz own (cmpBuf out m5) rm (rs5.getD 0 0 - 9223372036854775808).toNat ∧
        ((∃ e, cmpRun p (cmpM6 mode out m5 (bufSeq fz (cmpBuf out m5) rm
            (rs5.getD 0 0 - 9223372036854775808).toNat)) = .error e ∧ e.code = k) ∨
         ∃ rs6 m6, cmpRun p (cmpM6 mode out m5 (bufSeq fz (cmpBuf out m5) rm
            (rs5.getD 0 0 - 9223372036854775808).toNat)) = .ok (rs6, m6) ∧ 2 ^ 63 ≤ (rs6.getD 0 0).toNat ∧
          ∃ e, cmpRun p (seqMem m6 mode plo phi out hdrf ctlf hw 0 (rs6.getD 0 0 - 9223372036854775808)) =
            .error e ∧ e.code = k)))))

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

/-- `BufGeom` for another buffer of the same size with the same geometry. -/
theorem BufGeom.of_ok {tab : Tab} {fz own : List TieredArray} {B B' : Array Word} {buf base blen : Nat}
    (hg : BufGeom tab fz own B buf base blen) (hB : BufOk fz.length B') (hs : B'.size = B.size) :
    BufGeom tab fz own B' buf base blen :=
  ⟨hg.need, hg.fits, by rw [hs]; exact hg.bend, fun i hi => by
      have := hB.hdr i hi; have := hB.ent 0 (by omega); omega,
    hB.ent, hB.disj, fun x h1 h2 => hg.apart x h1 (by rw [← hs]; exact h2)⟩

/-! ## A memory relation survives a change outside its cells -/

/-- `MemRel` reads the table's bytes, the byte arrays' bytes and the word arrays' words: a memory
that agrees there (and has every byte the old one has) holds the same L memory. -/
theorem MemRel.congrW {G : L.Compiler.Layout} (hG : G.Ok) {m : Mem} {d d' : DataMem} (hm : MemRel G m d)
    (hgrow : ∀ y, (d.get? y).isSome → (d'.get? y).isSome)
    (htab : ∀ x, G.InTab x → d'.get? (A x) = d.get? (A x))
    (h8 : ∀ p < G.tab.nb, ∀ x, G.In8 p x → d'.get? (A x) = d.get? (A x))
    (h64 : ∀ p, G.tab.nb ≤ p → p < G.tab.nb + G.tab.nw → ∀ i < G.s p,
      rdW d' (A (G.b p + 8 * i)) = rdW d (A (G.b p + 8 * i))) :
    MemRel G m d' := by
  have hte := hG.tab_end
  have hw : G.tab.rom.length ≤ 8 * G.tab.romWords := G.tab.rom_length_le
  have hcell : ∀ off, off + 8 ≤ 16 + 24 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres +
      8 * G.tab.ng → rdW d' (A (G.T + off)) = rdW d (A (G.T + off)) := fun off h =>
    rdW_congr fun j hj => by
      rw [A_add]; exact htab _ ⟨by omega, by simp only [Layout.tabEnd]; omega⟩
  exact {
    size8 := hm.size8
    size64 := hm.size64
    get8 := fun c hc i hi => by
      have hs := hm.size8 c hc
      have hp := G.tab.pos8_lt hc
      rw [h8 _ hp _ ⟨by omega, by omega⟩, hm.get8 c hc i hi]
    get64 := fun c hc i hi => by
      have hs := hm.size64 c hc
      have hp := G.tab.pos64_lt hc
      rw [h64 _ hp.1 hp.2 i (by omega)]; exact hm.get64 c hc i hi
    limit := by rw [hcell 8 (by omega)]; exact hm.limit
    base := fun c hc => (by rw [hcell _ (by simp only [Tab.dbase]; omega)]; exact hm.base c hc)
    «len» := fun c hc => (by rw [hcell _ (by simp only [Tab.dlen]; omega)]; exact hm.len c hc)
    len32 := fun c h1 h2 => (by rw [hcell _ (by simp only [Tab.dlen32]; omega)]; exact hm.len32 c h1 h2)
    rom := fun i hi => by
      rw [htab _ ⟨by omega, by simp only [Layout.tabEnd]; omega⟩]; exact hm.rom i hi
    stack := fun x hx => hgrow _ (hm.stack x hx)
    res := fun x hx => hgrow _ (hm.res x hx)
    glob := fun g hg => by
      rw [← hm.glob g hg]
      refine rdW_congr fun j hj => ?_
      rw [A_add]
      exact htab _ (Layout.InGlob.tab (Layout.inGlob_cell hg j hj)) }

/-- `MemRel.congrW` for another L memory `m'` with the same byte arrays, globals and sizes, whose
word arrays the new memory holds. -/
theorem MemRel.congrM {G : L.Compiler.Layout} (hG : G.Ok) {m m' : Mem} {d d' : DataMem} (hm : MemRel G m d)
    (hb : m'.bytes = m.bytes) (hgl : m'.glob = m.glob) (hs : ∀ c, (m'.arr64 c).size = (m.arr64 c).size)
    (hgrow : ∀ y, (d.get? y).isSome → (d'.get? y).isSome)
    (htab : ∀ x, G.InTab x → d'.get? (A x) = d.get? (A x))
    (h8 : ∀ p < G.tab.nb, ∀ x, G.In8 p x → d'.get? (A x) = d.get? (A x))
    (h64 : ∀ c, G.tab.dom64 c = true → ∀ i (h : i < (m'.arr64 c).size),
      rdW d' (A (G.b (G.tab.pos64 c) + 8 * i)) = some (m'.arr64 c)[i]) :
    MemRel G m' d' := by
  have hte := hG.tab_end
  have hw : G.tab.rom.length ≤ 8 * G.tab.romWords := G.tab.rom_length_le
  have hcell : ∀ off, off + 8 ≤ 16 + 24 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres +
      8 * G.tab.ng → rdW d' (A (G.T + off)) = rdW d (A (G.T + off)) := fun off h =>
    rdW_congr fun j hj => by
      rw [A_add]; exact htab _ ⟨by omega, by simp only [Layout.tabEnd]; omega⟩
  have e8 : ∀ a, m'.arr8 a = m.arr8 a := fun a => by simp only [Mem.arr8, hb]
  exact {
    size8 := fun a ha => by rw [e8]; exact hm.size8 a ha
    size64 := fun c hc => by rw [hs]; exact hm.size64 c hc
    get8 := fun c hc i hi => by
      simp only [e8] at hi ⊢
      have hs := hm.size8 c hc
      have hp := G.tab.pos8_lt hc
      rw [h8 _ hp _ ⟨by omega, by omega⟩, hm.get8 c hc i hi]
    get64 := h64
    limit := by rw [hcell 8 (by omega)]; exact hm.limit
    base := fun c hc => (by rw [hcell _ (by simp only [Tab.dbase]; omega)]; exact hm.base c hc)
    «len» := fun c hc => (by rw [hcell _ (by simp only [Tab.dlen]; omega)]; exact hm.len c hc)
    len32 := fun c h1 h2 => (by rw [hcell _ (by simp only [Tab.dlen32]; omega)]; exact hm.len32 c h1 h2)
    rom := fun i hi => by
      rw [htab _ ⟨by omega, by simp only [Layout.tabEnd]; omega⟩]; exact hm.rom i hi
    stack := fun x hx => hgrow _ (hm.stack x hx)
    res := fun x hx => hgrow _ (hm.res x hx)
    glob := fun g hg => by
      rw [hgl, ← hm.glob g hg]
      refine rdW_congr fun j hj => ?_
      rw [A_add]
      exact htab _ (Layout.InGlob.tab (Layout.inGlob_cell hg j hj)) }

/-! ## The region `R` across the solution's jobs -/

/-- **What the jobs leave of the memory `d5` after mode `5`**: every byte the same but in the
worker region `[wlo, whi)`, the stack window around `rsp0`, the save area `[slo, shi)` and the
buffer at `buf`; the buffer's words still `B`; every byte `d5` has. -/
structure CmpAgree (B : Array Word) (buf wlo whi slo shi rsp0 : Nat) (d5 d : DataMem) : Prop where
  grows : ∀ y, (d5.get? y).isSome → (d.get? y).isSome
  same : ∀ x < 2 ^ 64, ¬ (wlo ≤ x ∧ x < whi) → (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x) → ¬ (slo ≤ x ∧ x < shi) →
    ¬ (buf ≤ x ∧ x < buf + 8 * B.size) → d.get? (A x) = d5.get? (A x)
  words : ∀ i (h : i < B.size), rdW d (A (buf + 8 * i)) = some B[i]

/-- **A job moves `CmpAgree` to the next buffer**: `ca_check_b`'s run on the worker region
`[wb, wb + blen)` inside `[wlo, whi)` changes only its layout's cells, the stack window and its save
area (`MemFrame`); its frozen arrays are the buffer's entries (`MemRel`: every frozen array is in
the table, `hdom`, at its own entry, `hnd`), so the buffer's words are `bufNext fz B r'`. -/
theorem CmpAgree.job {tab : Tab} (hok : abiTabOk tab = true) {fz own : List TieredArray} {B : Array Word}
    (hnd : fz.Nodup) (hdom : ∀ a ∈ fz, tab.dom64 a = true)
    {buf wb blen wlo whi slo shi rsp0 : Nat} (hg : BufGeom tab fz own B buf wb blen)
    (hW : wlo ≤ wb ∧ wb + blen ≤ whi)
    (hbuf : ∀ x, buf ≤ x → x < buf + 8 * B.size → ¬ (wlo ≤ x ∧ x < whi) ∧ (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x))
    {d5 d d' : DataMem} {r' : Mem}
    (hfr : MemFrame (bufLayout tab buf B wb fz own) rsp0 d d')
    (hm : MemRel (bufLayout tab buf B wb fz own) r' d')
    (hA : CmpAgree B buf wlo whi slo shi rsp0 d5 d) :
    CmpAgree (bufNext fz B r') buf wlo whi slo shi rsp0 d5 d' := by
  have hbend := hg.bend
  -- a byte outside the worker region and the window is in none of the layout's parts
  have hout : ∀ x < 2 ^ 64, ¬ (wlo ≤ x ∧ x < whi) → (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x) →
      ¬ (bufLayout tab buf B wb fz own).InArr x → d'.get? (A x) = d.get? (A x) := by
    intro x hx hw hwin hA'
    refine hfr.same x hx (fun h => ?_) hA' (fun h => ?_) (by omega) ?_
    · have h' := (buf_inStack h).region hg (by omega)
      exact hw ⟨by omega, by omega⟩
    · have h' := (buf_inTab hok h).1.region hg (by omega)
      exact hw ⟨by omega, by omega⟩
    · refine Classical.byContradiction fun hn => ?_
      simp only [not_or, Nat.not_lt, Nat.not_le] at hn
      have := buf_save hok hg hn.1 hn.2
      exact hw ⟨by omega, by omega⟩
  have hsz := bufNext_size fz B r'
  refine ⟨fun y hy => hfr.grows y (hA.grows y hy), fun x hx hw hwin hs hb => ?_, fun i hi => ?_⟩
  · rw [hsz] at hb
    rw [hout x hx hw hwin fun h => ?_]
    · exact hA.same x hx hw hwin hs hb
    · obtain ⟨p, hp1, hp2, h⟩ := buf_inArr h
      rcases buf_in64 hok hg hp1 h with ⟨e, he, h1, h2⟩ | ⟨-, k, hk, hsl⟩
      · have := hg.ent e (idxOf?_lt he); exact hb ⟨by omega, by omega⟩
      · have := own_region hg (idxOf?_lt hk) (hsl.imp (fun h => h.2) (fun h => h.2))
        exact hw ⟨by omega, by omega⟩
  · rw [hsz] at hi
    have hget : (bufNext fz B r')[i]'(by rw [hsz]; exact hi) = (bufNext fz B r').getD i 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsz]; exact hi), Option.getD_some]
    rw [hget]
    by_cases hin : ∃ j < 8, (bufLayout tab buf B wb fz own).InArr (buf + 8 * i + j)
    · obtain ⟨j, hj, h⟩ := hin
      obtain ⟨p, hp1, hp2, h⟩ := buf_inArr h
      rcases buf_in64 hok hg hp1 h with ⟨e, he, h1, h2⟩ | ⟨-, k, hk, hsl⟩
      · obtain ⟨hdom', hpos⟩ := tab.dom64_wAt hp1 hp2
        have hent := hg.ent e (idxOf?_lt he)
        obtain ⟨hel, hfe, -⟩ := List.idxOf?_eq_some_iff.mp he
        have hs := hm.size64 _ hdom'
        simp only [bufLayout_tab, hpos] at hs
        rw [bufLayout_s64 _ _ _ _ _ _ hp1] at hs
        simp only [bufL, he] at hs
        have ht : i - (bufEntry B e).1 < (r'.arr64 (tab.wAt p)).size := by rw [hs]; omega
        have hg64 := hm.get64 _ hdom' (i - (bufEntry B e).1) ht
        simp only [bufLayout_tab, hpos] at hg64
        rw [bufLayout_b64 _ _ _ _ _ _ hp1] at hg64
        simp only [bufB, he] at hg64
        rw [show buf + 8 * (bufEntry B e).1 + 8 * (i - (bufEntry B e).1) = buf + 8 * i by omega] at hg64
        rw [hg64, bufNext_in hg.disj hel ⟨by omega, by omega⟩ hi, hfe, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_getElem ht, Option.getD_some]
      · have := own_region hg (idxOf?_lt hk) (hsl.imp (fun h => h.2) (fun h => h.2))
        exact absurd ⟨by omega, by omega⟩ (hbuf (buf + 8 * i + j) (by omega) (by omega)).1
    · simp only [not_exists, not_and] at hin
      rw [bufNext_out fun e he hie => ?_]
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some, ← hA.words i hi]
        refine rdW_congr fun j hj => ?_
        rw [A_add]
        have := hbuf (buf + 8 * i + j) (by omega) (by omega)
        exact hout _ (by omega) this.1 this.2 (hin j hj)
      · -- entry `e` holds word `i`: its array is laid out there
        have hd := hdom fz[e] (List.getElem_mem he)
        obtain ⟨hq1, hq2⟩ := tab.pos64_lt hd
        have hwq := tab.wAt_pos64 hd
        have hidx : fz.idxOf? fz[e] = some e := List.idxOf?_eq_some_iff.mpr
          ⟨he, rfl, fun j hj e' => by
            have := (List.Nodup.getElem_inj hnd (hi := by omega) (hj := he)).mp e'; omega⟩
        refine hin 0 (by omega) ⟨tab.pos64 fz[e], by simpa using hq2, ?_⟩
        unfold Layout.In
        simp only [bufLayout_tab, Tab.wd, show ¬ tab.pos64 fz[e] < tab.nb by omega, ite_false]
        rw [bufLayout_b64 _ _ _ _ _ _ hq1, bufLayout_s64 _ _ _ _ _ _ hq1, hwq]
        simp only [bufB, bufL, hidx]
        unfold InEnt at hie
        omega

/-- A store into the stack window or the save area keeps `CmpAgree`. -/
theorem CmpAgree.wrW {B : Array Word} {buf wlo whi slo shi rsp0 : Nat} {d5 d : DataMem}
    (hA : CmpAgree B buf wlo whi slo shi rsp0 d5 d) {y : Nat} {v : BitVec 64} (hy8 : y + 8 ≤ 2 ^ 64)
    (hex : ∀ x, y ≤ x → x < y + 8 → (rsp0 - 24 ≤ x ∧ x < rsp0 + 8) ∨ (slo ≤ x ∧ x < shi))
    (hbuf : y + 8 ≤ buf ∨ buf + 8 * B.size ≤ y) (hbend : buf + 8 * B.size ≤ 2 ^ 64) :
    CmpAgree B buf wlo whi slo shi rsp0 d5 (wrW d (A y) v) := by
  refine ⟨fun z hz => isSome_get?_storeInt (hA.grows z hz), fun x hx hw hwin hs hb => ?_, fun i hi => ?_⟩
  · rw [get?_wrW_A hy8 hx ?_]
    · exact hA.same x hx hw hwin hs hb
    · refine Classical.byContradiction fun hn => ?_
      simp only [not_or, Nat.not_lt, Nat.not_le] at hn
      rcases hex x hn.1 hn.2 with h | h
      · omega
      · exact hs h
  · rw [rdW_wrW_A hy8 (by omega) (by omega)]
    exact hA.words i hi

end ConAgua.Final
