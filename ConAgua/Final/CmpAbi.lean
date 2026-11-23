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
geometry after mode `5` and that the jobs leave the frozen arrays alone; the lead discharges them
at the L level), and what an accepting or failing run means (`CmpAccepts`, `CmpErr`). The theorem:
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

/-- **The buffer's geometry** (`BufGeom`'s L-level part): its length word inside `out`, its
header and entries inside it, the entries pairwise apart (or empty). -/
def CmpBufOk (fz : List TieredArray) (out : ArrId) (m : Mem) : Prop :=
  ((m.arr64 out).getD 1 0).toNat ≤ (m.arr64 out).size ∧
  (∀ i < fz.length, 9 + 2 * i < (cmpBuf out m).size) ∧
  (∀ i < fz.length, (bufEntry (cmpBuf out m) i).1 + (bufEntry (cmpBuf out m) i).2 ≤ (cmpBuf out m).size) ∧
  (∀ i < fz.length, ∀ i' < fz.length, i ≠ i' →
    (bufEntry (cmpBuf out m) i).1 + (bufEntry (cmpBuf out m) i).2 ≤ (bufEntry (cmpBuf out m) i').1 ∨
    (bufEntry (cmpBuf out m) i').1 + (bufEntry (cmpBuf out m) i').2 ≤ (bufEntry (cmpBuf out m) i).1 ∨
    (bufEntry (cmpBuf out m) i).2 = 0 ∨ (bufEntry (cmpBuf out m) i').2 = 0)

/-- A job's final memory `r` keeps the frozen arrays: each is the buffer's image. -/
def CmpKept (fz : List TieredArray) (B : Array Word) (r : Mem) : Prop :=
  ∀ i (h : i < fz.length), r.arr64 fz[i] = bufImg B i

/-- **What the machine proof needs of `check` and cannot see** (L-level; for `checkerProg` a lemma,
not an assumption of the final theorem): after modes `4` and `5` (`5` returning `2^63 + k`), the
buffer's geometry holds, and every job's run on it keeps the frozen arrays. -/
def CmpGuard (tab : Tab) (p : Prog) (mode plo phi : GVar) (out : ArrId) (fz own : List TieredArray)
    (bC bS pb : ByteArray) : Prop :=
  ∀ rs4 m4 rs5 m5, cmpRun p (cmpM4 tab mode bC pb) = .ok (rs4, m4) →
    cmpRun p (cmpM5 mode m4 bS) = .ok (rs5, m5) → 2 ^ 63 ≤ (rs5.getD 0 0).toNat →
    CmpBufOk fz out m5 ∧ ∀ r j rs r', cmpRun p (bufMemG fz own plo phi mode (cmpBuf out m5) r j) = .ok (rs, r') →
      CmpKept fz (cmpBuf out m5) r'

/-- The jobs `j < n` of the solution, from the worker memories `rm`: each accepts and ends in the
next. -/
def CmpJobs (p : Prog) (mode plo phi : GVar) (fz own : List TieredArray) (B : Array Word) (rm : Nat → Mem)
    (n : Nat) : Prop :=
  ∀ j < n, ∃ rs, cmpRun p (bufMemG fz own plo phi mode B (rm j) (UInt64.ofNat j)) = .ok (rs, rm (j + 1)) ∧
    rs.getD 0 0 = ACCEPT

/-- **What an accepting compared run means** (`9223372036854775808 = 2^63`): the buffers below
`2^63` bytes; mode `4` returns `ACCEPT` or `2^63 + _`; then mode `5` (from mode `4`'s memory with
the solution's bytes) returns `ACCEPT` or `2^63 + k`; then the jobs `j < k` on the buffer, from
the zero worker memory, each accepting; mode `6` from mode `5`'s memory returns `ACCEPT` or
`2^63 + k'`; then `ca_check_seq`'s run for `[0, k')` accepts. -/
def CmpAccepts (tab : Tab) (p : Prog) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (fz own : List TieredArray) (bC bS pb : ByteArray) : Prop :=
  bC.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧ ∃ rs4 m4, cmpRun p (cmpM4 tab mode bC pb) = .ok (rs4, m4) ∧
    (rs4.getD 0 0 = ACCEPT ∨ (2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧ bS.size < 2 ^ 63 ∧
      ∃ rs5 m5, cmpRun p (cmpM5 mode m4 bS) = .ok (rs5, m5) ∧
      (rs5.getD 0 0 = ACCEPT ∨ (2 ^ 63 ≤ (rs5.getD 0 0).toNat ∧
        ∃ rm : Nat → Mem, rm 0 = zeroMem tab ∧
        CmpJobs p mode plo phi fz own (cmpBuf out m5) rm (rs5.getD 0 0 - 9223372036854775808).toNat ∧
        ∃ rs6 m6, cmpRun p (m5.setG mode 6) = .ok (rs6, m6) ∧
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
          ∃ e, cmpRun p (bufMemG fz own plo phi mode (cmpBuf out m5) (rm j) (UInt64.ofNat j)) = .error e ∧
            e.code = k) ∨
       (CmpJobs p mode plo phi fz own (cmpBuf out m5) rm (rs5.getD 0 0 - 9223372036854775808).toNat ∧
        ((∃ e, cmpRun p (m5.setG mode 6) = .error e ∧ e.code = k) ∨
         ∃ rs6 m6, cmpRun p (m5.setG mode 6) = .ok (rs6, m6) ∧ 2 ^ 63 ≤ (rs6.getD 0 0).toNat ∧
          ∃ e, cmpRun p (seqMem m6 mode plo phi out hdrf ctlf hw 0 (rs6.getD 0 0 - 9223372036854775808)) =
            .error e ∧ e.code = k)))))

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

/-! ## The region `R` across the solution's jobs -/

/-- **What the jobs leave of the memory `d5` after mode `5`**: every byte the same but in the
worker region `[wlo, whi)`, the stack window around `rsp0`, the save area `[slo, shi)` and the
buffer at `buf`; the buffer's words still `B`; every byte `d5` has. -/
structure CmpAgree (B : Array Word) (buf wlo whi slo shi rsp0 : Nat) (d5 d : DataMem) : Prop where
  grows : ∀ y, (d5.get? y).isSome → (d.get? y).isSome
  same : ∀ x < 2 ^ 64, ¬ (wlo ≤ x ∧ x < whi) → (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x) → ¬ (slo ≤ x ∧ x < shi) →
    ¬ (buf ≤ x ∧ x < buf + 8 * B.size) → d.get? (A x) = d5.get? (A x)
  words : ∀ i (h : i < B.size), rdW d (A (buf + 8 * i)) = some B[i]

/-- **A job keeps `CmpAgree`**: `ca_check_b`'s run on the worker region `[wb, wb + blen)` inside
`[wlo, whi)` changes only its layout's cells, the stack window and its save area (`MemFrame`); its
frozen arrays are the buffer's (`MemRel`) and the job kept them (`CmpKept`), so the buffer's words
are still `B`. -/
theorem CmpAgree.job {tab : Tab} (hok : abiTabOk tab = true) {fz own : List TieredArray} {B : Array Word}
    {buf wb blen wlo whi slo shi rsp0 : Nat} (hg : BufGeom tab fz own B buf wb blen)
    (hW : wlo ≤ wb ∧ wb + blen ≤ whi)
    (hbuf : ∀ x, buf ≤ x → x < buf + 8 * B.size → ¬ (wlo ≤ x ∧ x < whi) ∧ (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x))
    {d5 d d' : DataMem} {r' : Mem}
    (hfr : MemFrame (bufLayout tab buf B wb fz own) rsp0 d d')
    (hm : MemRel (bufLayout tab buf B wb fz own) r' d') (hkept : CmpKept fz B r')
    (hA : CmpAgree B buf wlo whi slo shi rsp0 d5 d) : CmpAgree B buf wlo whi slo shi rsp0 d5 d' := by
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
  refine ⟨fun y hy => hfr.grows y (hA.grows y hy), fun x hx hw hwin hs hb => ?_, fun i hi => ?_⟩
  · rw [hout x hx hw hwin fun h => ?_]
    · exact hA.same x hx hw hwin hs hb
    · obtain ⟨p, hp1, hp2, h⟩ := buf_inArr h
      rcases buf_in64 hok hg hp1 h with ⟨e, he, h1, h2⟩ | ⟨-, k, hk, hsl⟩
      · have := hg.ent e (idxOf?_lt he); exact hb ⟨by omega, by omega⟩
      · have := own_region hg (idxOf?_lt hk) (hsl.imp (fun h => h.2) (fun h => h.2))
        exact hw ⟨by omega, by omega⟩
  · by_cases hin : ∃ j < 8, (bufLayout tab buf B wb fz own).InArr (buf + 8 * i + j)
    · obtain ⟨j, hj, h⟩ := hin
      obtain ⟨p, hp1, hp2, h⟩ := buf_inArr h
      rcases buf_in64 hok hg hp1 h with ⟨e, he, h1, h2⟩ | ⟨-, k, hk, hsl⟩
      · obtain ⟨hdom, hpos⟩ := tab.dom64_wAt hp1 hp2
        have hent := hg.ent e (idxOf?_lt he)
        obtain ⟨hel, hfe, -⟩ := List.idxOf?_eq_some_iff.mp he
        have hs := hm.size64 _ hdom
        simp only [bufLayout_tab, hpos] at hs
        rw [bufLayout_s64 _ _ _ _ _ _ hp1] at hs
        simp only [bufL, he] at hs
        have ht : i - (bufEntry B e).1 < (r'.arr64 (tab.wAt p)).size := by rw [hs]; omega
        have hg64 := hm.get64 _ hdom (i - (bufEntry B e).1) ht
        simp only [bufLayout_tab, hpos] at hg64
        rw [bufLayout_b64 _ _ _ _ _ _ hp1] at hg64
        simp only [bufB, he] at hg64
        rw [show buf + 8 * (bufEntry B e).1 + 8 * (i - (bufEntry B e).1) = buf + 8 * i by omega] at hg64
        rw [hg64]
        have hk := hkept e hel
        rw [hfe] at hk
        simp only [hk, bufImg, Array.getElem_extract]
        congr 2; omega
      · have := own_region hg (idxOf?_lt hk) (hsl.imp (fun h => h.2) (fun h => h.2))
        exact absurd ⟨by omega, by omega⟩ (hbuf (buf + 8 * i + j) (by omega) (by omega)).1
    · simp only [not_exists, not_and] at hin
      rw [← hA.words i hi]
      refine rdW_congr fun j hj => ?_
      rw [A_add]
      have := hbuf (buf + 8 * i + j) (by omega) (by omega)
      exact hout _ (by omega) this.1 this.2 (hin j hj)

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
