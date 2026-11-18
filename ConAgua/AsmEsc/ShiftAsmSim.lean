module

public import ConAgua.AsmEsc.ShiftAsm
public import ConAgua.AsmEsc.ShiftL
public import ConAgua.AsmEsc.BitAsmSim
import Kraken.X64.Registers
import Std.Tactic.BVDecide

@[expose] public section

/-!
# The shift and zeroing bodies meet the compiler's contract

`shlAsm_sim`, `shrAsm_sim`, `zeroAsm_sim`: the per-function contract (`FnSimAt`) of the bodies of
`ShiftAsm.lean`, against the L sides of `ShiftL.lean`. `dshl_eq`, `dshr_eq`: for `s < 64`, `shld`
and `shrd` compute L's `(x << s) | ((p >> 1) >> (63 - s))` and `(x >> s) | ((y << 1) << (63 - s))`.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

theorem dshl_eq (x p s : UInt64) (hs : s < 64) : dshl x p s = (x <<< s) ||| ((p >>> 1) >>> (63 - s)) := by
  unfold dshl
  have : s.toNat < 64 := hs
  split
  · rename_i h0
    have : s = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst this
    bv_decide
  · rename_i h0
    have h1 : s ≠ 0 := fun e => h0 (by subst e; rfl)
    bv_decide

theorem dshr_eq (x y s : UInt64) (hs : s < 64) : dshr x y s = (x >>> s) ||| ((y <<< 1) <<< (63 - s)) := by
  unfold dshr
  have : s.toNat < 64 := hs
  split
  · rename_i h0
    have : s = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst this
    bv_decide
  · rename_i h0
    have h1 : s ≠ 0 := fun e => h0 (by subst e; rfl)
    bv_decide

/-! ## `zero_n` -/

section
variable [Host] {kf : Nat} {tab : Tab}

theorem z_code (hc : Code (zeroAsm tab) kf) {i : Nat} {x : Directive}
    (hi : (zeroAsm tab)[i]? = some x) : Host.prog[kf + i]? = some x := Code.get hc hi

end

section
variable [Host] {G : L.Compiler.Layout} (hG : G.Ok) {kf : Nat} (hc : Code (zeroAsm G.tab) kf)
  {d : MachineData} {Q : MachineState → Prop}
include hG hc

theorem z_step (TO : TieredArray) (hTO : G.tab.dom64 TO = true) (ob n : Word) (R14 : UInt64) (m0 : Mem)
    (hoa : ob.toNat + n.toNat ≤ G.s (G.tab.pos64 TO))
    (s : MachineData) (j : Word) (hF : MrFr G d s)
    (hm : MemRel G (g0Rows (zeroStep TO ob) j.toNat m0 0) s.dmem)
    (hrdi : s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat))
    (hr13 : s.regs.r13 = j) (hr8 : s.regs.r8 = n) (hrdx : s.regs.rdx = 0) (hr14 : s.regs.r14 = R14)
    (hj : j.toNat < n.toNat)
    (hnext : ∀ s', MrFr G d s' → MemRel G (g0Rows (zeroStep TO ob) (j + 1).toNat m0 0) s'.dmem →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s'.regs.r13 = j + 1 → s'.regs.r8 = n → s'.regs.rdx = 0 → s'.regs.r14 = R14 →
      (j + 1).toNat < n.toNat → Ev Q s' (at_ (kf + 19)))
    (hE : ∀ s', MrFr G d s' → MemRel G (g0Rows (zeroStep TO ob) n.toNat m0 0) s'.dmem →
      Ev Q s' (at_ (kf + 24))) :
    Ev Q s (at_ (kf + 19)) := by
  have hpO := G.tab.pos64_lt hTO
  have heO := hG.end64 _ hpO
  generalize hMc : g0Rows (zeroStep TO ob) j.toNat m0 0 = M at hm
  have hszO := hm.size64 TO hTO
  generalize hBO : G.b (G.tab.pos64 TO) = BO at *
  have hoj : (ob + j).toNat = ob.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hinO : (ob + j).toNat < (M.arr64 TO).size := by rw [hoj, hszO]; omega
  have haO : s.regs.rdi.toBitVec + s.regs.r13.toBitVec * 8 = A (BO + 8 * (ob + j).toNat) := by
    rw [hrdi, hr13, addr_idx BO ob.toNat j (by omega), hoj]
  have hrO : rdW s.dmem (A (BO + 8 * (ob + j).toNat)) = some (M.arr64 TO)[(ob + j).toNat] := by
    have := hm.get64 TO hTO (ob + j).toNat hinO; rw [hBO] at this; exact this
  refine ev_label (z_code hc (i := 19) rfl) ?_
  refine ev_stX (z_code hc (i := 20) rfl) (by rs; rw [haO, hrO]; rfl) ?_
  refine ev_addRI (z_code hc (i := 21) rfl) fun st2 => ?_
  refine ev_cmpRO (z_code hc (i := 22) rfl) (v := n) (Or.inr (Or.inr ⟨.r8, rfl, by rs [hr8]⟩)) ?_
  have hj1 : (j + 1).toNat = j.toNat + 1 := L.toNat_add_one_of_lt (by omega)
  have hrow : g0Rows (zeroStep TO ob) (j + 1).toNat m0 0 = M.set64 TO (ob + j) 0 := by
    rw [hj1, g0Rows_succ, hMc, UInt64.zero_add, L.ofNat_toNat]; rfl
  rw [hrow] at hnext
  have hm' := MemRel.store64 hG hm hTO hinO 0
  rw [hBO] at hm'
  have hpres := hF.pres.trans (Pres.store64 hG (top := d.regs.rsp.toNat) (d := s.dmem) hTO
    (j := (ob + j).toNat) (by omega) (0 : Word).toBitVec)
  rw [hBO] at hpres
  have haO' : (UInt64.ofNat (BO + 8 * ob.toNat)).toBitVec + j.toBitVec * 8 = A (BO + 8 * (ob + j).toNat) := by
    have := haO; rw [hrdi, hr13] at this; exact this
  refine ev_jcc (z_code hc (i := 23) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · refine ev_lbl (Code.label hc (i := 19) rfl) ?_
    refine hnext _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrdi, hr13, hr8, hrdx, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haO']; exact hpres
    · rw [haO']; exact hm'
    · rfl
    · simp only [CondCode.interp, cmpFlags_cf, decide_eq_true_eq] at hcc
      rs [hr13] at hcc
      exact hcc
    all_goals done
  · simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc
    rs [hr13] at hcc
    have e1 : (j + 1).toNat = (j.toBitVec + (Int64.ofInt 1).toBitVec).toNat := rfl
    have e2 : n.toNat = n.toBitVec.toNat := rfl
    have hla : j + 1 = n := UInt64.toNat_inj.mp (by omega)
    rw [← hla, hrow] at hE
    refine hE _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrdi, hr13, hr8, hrdx, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haO']; exact hpres
    · rw [haO']; exact hm'

theorem z_loop (TO : TieredArray) (hTO : G.tab.dom64 TO = true) (ob n : Word) (R14 : UInt64) (m0 : Mem)
    (hoa : ob.toNat + n.toNat ≤ G.s (G.tab.pos64 TO))
    (hE : ∀ s', MrFr G d s' → MemRel G (g0Rows (zeroStep TO ob) n.toNat m0 0) s'.dmem →
      Ev Q s' (at_ (kf + 24))) :
    ∀ (r : Nat) (s : MachineData) (j : Word), n.toNat = j.toNat + r → MrFr G d s →
      MemRel G (g0Rows (zeroStep TO ob) j.toNat m0 0) s.dmem →
      s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s.regs.r13 = j → s.regs.r8 = n → s.regs.rdx = 0 → s.regs.r14 = R14 → j.toNat < n.toNat →
      Ev Q s (at_ (kf + 19)) := by
  intro r
  induction r with
  | zero => intro s j hr _ _ _ _ _ _ _ hj; omega
  | succ r ih =>
    intro s j hr hF hm h1 h2 h3 h4 h5 hj
    refine z_step hG hc TO hTO ob n R14 m0 hoa s j hF hm h1 h2 h3 h4 h5 hj ?_ hE
    intro s' g1 g2 g3 g4 g5 g6 g7 g8
    have := n.toNat_lt
    exact ih s' (j + 1) (by rw [L.toNat_add_one_of_lt (by omega)]; omega) g1 g2 g3 g4 g5 g6 g7 g8

theorem z_exit {ra : Word} (hra : rdW d.dmem (A d.regs.rsp.toNat) = some ra) (hlo : G.lo ≤ d.regs.rsp.toNat)
    (hhi : d.regs.rsp.toNat + 8 ≤ G.hi) (s : MachineData) (hF : MrFr G d s)
    (hok : ∀ s', s'.dmem = s.dmem → s'.regs.rsp.toNat = d.regs.rsp.toNat + 8 →
      s'.regs.rbp = d.regs.rbp → s'.regs.r15 = d.regs.r15 → s'.regs.r14.toNat ≤ d.regs.r14.toNat →
      s'.regs.rax = 0 → Ev Q s' (Int64.ofBitVec ra.toBitVec)) :
    Ev Q s (at_ (kf + 24)) := by
  refine ev_label (z_code hc (i := 24) rfl) ?_
  refine ev_movRI (z_code hc (i := 25) rfl) ?_
  refine frame_ret hG hra hlo hhi ⟨?_, ?_, ?_, ?_, ?_⟩ (z_code hc (i := 26) rfl) fun s' e1 e2 e3 e4 e5 e6 => ?_
  all_goals try rs [hF.rsp, hF.rbp, hF.r15]
  · exact hF.r14
  · exact hF.pres
  · exact hok s' e1 e2 e3 e4 (by rw [e5]; rs; exact hF.r14) (by rw [e6]; rs)

end

/-- **The zeroing body meets the compiler's per-function contract.** -/
theorem zeroAsm_sim [Host] (p : Prog) (G : L.Compiler.Layout) (hG : G.Ok)
    (hspec : ZeroSpec p) (fd : FunDecl) (hnp : fd.nparams = 2) (hnr : Stmt.nret fd.body = 1)
    (hdom : G.tab.dom64 (tier1 0) = true)
    (hoffL : SmallOff (G.tab.len64 (0 : ArrId))) (hoffB : SmallOff (G.tab.base64 (0 : ArrId)))
    (kf : Nat) (hc : Code (zeroAsm G.tab) kf) (sk : NTree) (n : Nat) :
    FnSimAt p G sk n "zero_n" fd kf := by
  intro vs σ d ra Q hlen hra hargs hlo8 hhi h15 hmem h14 hok herr habrt hexh
  have hlo : G.lo ≤ d.regs.rsp.toNat := by omega
  rw [hnp] at hlen
  obtain ⟨o, nn, rfl⟩ : ∃ o nn, vs = [o, nn] := by
    match vs, hlen with
    | [o, nn], _ => exact ⟨o, nn, rfl⟩
  have hA := hargs.1 (by simp [argRegs])
  have hrdi : d.regs.rdi = o := UInt64.toBitVec_inj.mp (hA 0 (by simp))
  have hr8 : d.regs.r8 = nn := UInt64.toBitVec_inj.mp (hA 1 (by simp))
  have hn0 : 0 < n := by omega
  have hh := hG.hi_le
  have hfin : ∀ (M : Mem), (invoke p (exec p n) "zero_n" [o, nn]).run σ = .ok ([0], { σ with mem := M }) →
      ∀ s, MrFr G d s → MemRel G M s.dmem → Ev Q s (at_ (kf + 24)) := by
    intro M hrun s hF hm
    refine z_exit hG hc hra hlo hhi s hF fun s' e1 e2 e3 e4 e5 e6 => ?_
    refine hok _ _ s' hrun (by rw [e1]; exact hm) rfl e2 e3 e4 e5 ?_ (by rw [e1]; exact hF.pres)
    rw [hnr]; exact resOut_zero' e6
  refine ev_label (z_code hc (i := 0) rfl) ?_
  refine ev_cmpRO (z_code hc (i := 1) rfl) (v := 0) (Or.inl rfl) ?_
  refine ev_jcc (z_code hc (i := 2) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · simp only [CondCode.interp, cmpFlags_zf, beq_iff_eq] at hcc
    rs [hr8] at hcc
    have hn0' : nn = 0 := UInt64.toBitVec_inj.mp hcc
    subst hn0'
    have hrun := hspec σ o 0 n (by simp; omega) (Or.inl rfl)
    simp only [UInt64.toNat_zero, g0Rows] at hrun
    refine ev_lbl (Code.label hc (i := 24) rfl) ?_
    exact hfin σ.mem hrun _ ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.refl _ _⟩ hmem
  simp only [CondCode.interp, cmpFlags_zf, beq_eq_false_iff_ne] at hcc
  rs [hr8] at hcc
  have hnz : nn ≠ 0 := fun h => hcc (by rw [h])
  refine ev_movRI (z_code hc (i := 3) rfl) ?_
  refine ev_movRR (z_code hc (i := 4) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (z_code hc (i := 5) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (z_code hc (i := 6) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (z_code hc (i := 7) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_gen (fun s1 => s1.regs.rcx = (o >>> 40) &&& 1 ∧ s1.regs.rdi = o &&& idxMask ∧ s1.regs.r8 = nn ∧
      s1.regs.r14 = d.regs.r14 ∧ s1.regs.r15 = d.regs.r15 ∧
      s1.regs.rsp = d.regs.rsp ∧ s1.regs.rbp = d.regs.rbp ∧ s1.dmem = d.dmem)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rs [hrdi, hr8, BinOp.eval]
        all_goals rfl)
    fun s1 ⟨g1, g2, g7, g9, g10, g11, g12, g13⟩ => ?_
  have hTO := G.tab.dom64_tierA hdom (o >>> 40)
  have heO := hG.end64 _ (G.tab.pos64_lt hTO)
  have hm1 : MemRel G σ.mem s1.dmem := by rw [g13]; exact hmem
  have h15' : s1.regs.r15.toNat = G.T := by rw [g10]; exact h15
  have hdO := pool_desc hm1 hdom (o >>> 40) (r := .rcx) (by rs [g1]) h15'
  have hszO := hmem.size64 _ hTO
  generalize hSO : G.s (G.tab.pos64 (tierA 0 (o >>> 40))) = SO at *
  generalize hBO : G.b (G.tab.pos64 (tierA 0 (o >>> 40))) = BO at *
  have hSOn : (UInt64.ofNat SO).toNat = SO := L.toNat_ofNat_of_lt (by omega)
  have hsub : ∀ (S : Nat) (w : Word), S < 2 ^ 64 → w.toNat ≤ S →
      ((UInt64.ofNat S).toBitVec - w.toBitVec).toNat = S - w.toNat := by
    intro S w h1 h2
    rw [BitVec.toNat_sub, UInt64.toNat_toBitVec, show (UInt64.ofNat S).toBitVec.toNat = S from
      L.toNat_ofNat_of_lt h1]
    have := w.toNat_lt; omega
  have hX : ∀ s', s'.regs.rbp = d.regs.rbp → s'.dmem = s1.dmem → Ev Q s' (label exhaustedL) :=
    fun s' e1 e2 => hexh _ ⟨e1, by rw [e2, g13]; exact Pres.refl _ _⟩
  refine ev_movRMt (z_code hc (i := 8) rfl) hoffL (v := UInt64.ofNat SO) (by rs; exact hdO.1) ?_
  refine ev_subRR (z_code hc (i := 9) rfl) fun st hcf => ?_
  rs [g2, hSOn] at hcf
  refine ev_jcc (z_code hc (i := 10) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc5 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSOn] at hcc5
  refine ev_cmpRO (z_code hc (i := 11) rfl) (v := nn) (Or.inr (Or.inr ⟨.r8, rfl, by rs [g7]⟩)) ?_
  refine ev_jcc (z_code hc (i := 12) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc6 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc6
  rs [g2] at hcc6
  rw [hsub SO _ (by omega) (by omega)] at hcc6
  simp only [UInt64.toNat_toBitVec] at hcc6
  have hoa : (o &&& idxMask).toNat + nn.toNat ≤ SO := by omega
  refine ev_movRMt (z_code hc (i := 13) rfl) hoffB (v := UInt64.ofNat BO) (by rs; exact hdO.2) ?_
  refine ev_leaX (z_code hc (i := 14) rfl) ?_
  refine ev_subRR (z_code hc (i := 15) rfl) fun st hcf => ?_
  rs [g7, g9] at hcf
  refine ev_jcc (z_code hc (i := 16) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc7 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec] at hcc7
  refine ev_movRI (z_code hc (i := 17) rfl) ?_
  refine ev_movRI (z_code hc (i := 18) rfl) ?_
  have hl14 : nn.toNat ≤ d.regs.r14.toNat := by omega
  have hnF : nn.toNat < n := by omega
  have hrun := hspec σ o nn n hnF (Or.inr ⟨by rw [hszO]; exact hoa, by rw [hszO]; omega⟩)
  rw [← hSO] at hoa
  refine z_loop (d := d) hG hc _ hTO (o &&& idxMask) nn (d.regs.r14 - nn) σ.mem hoa
    (fun s' fr hm' => hfin _ hrun s' fr hm') nn.toNat _ 0 (by simp) ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_
    (by have := L.toNat_ne_zero_of_ne _ hnz; simp only [UInt64.toNat_zero]; omega)
  all_goals try rs [g1, g2, g7, g9, g10, g11, g12, g13]
  · show (d.regs.r14 - nn).toNat ≤ _
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hl14)]; omega
  · exact Pres.refl _ _
  · simpa [g0Rows] using hmem
  · apply UInt64.toBitVec_inj.mp
    rw [hBO]
    have := addr_idx BO 0 (o &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  · rfl


/-! ## `shl_n` -/

section
variable [Host] {kf : Nat} {tab : Tab}

theorem sh_code (hc : Code (shlAsm tab) kf) {i : Nat} {x : Directive}
    (hi : (shlAsm tab)[i]? = some x) : Host.prog[kf + i]? = some x := Code.get hc hi

end

section
variable [Host] {G : L.Compiler.Layout} (hG : G.Ok) {kf : Nat} (hc : Code (shlAsm G.tab) kf)
  {d : MachineData} {Q : MachineState → Prop}
include hG hc

/-- One step of `shl_n`'s loop (`.L`) at limb `j`, the previous limb in `rdx`. -/
theorem sh_step (TA TO : TieredArray) (hTA : G.tab.dom64 TA = true) (hTO : G.tab.dom64 TO = true)
    (qa ob n sh : Word) (hs : sh < 64) (R14 : UInt64) (m0 : Mem) (c0 : Word)
    (hqa : qa.toNat + n.toNat ≤ G.s (G.tab.pos64 TA)) (hoa : ob.toNat + n.toNat ≤ G.s (G.tab.pos64 TO))
    (s : MachineData) (j : Word) (hF : MrFr G d s)
    (hm : MemRel G (wRows (shlStep TA TO qa ob sh (63 - sh)) j.toNat m0 0 c0).1 s.dmem)
    (hcy : (wRows (shlStep TA TO qa ob sh (63 - sh)) j.toNat m0 0 c0).2 = (s.regs.rdx >>> 1) >>> (63 - sh))
    (hrsi : s.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat))
    (hrdi : s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat))
    (hr13 : s.regs.r13 = j) (hr9 : s.regs.r9 = n) (hr10 : s.regs.r10 = sh) (hrcx : s.regs.rcx = sh)
    (hr14 : s.regs.r14 = R14) (hj : j.toNat < n.toNat)
    (hnext : ∀ s', MrFr G d s' →
      MemRel G (wRows (shlStep TA TO qa ob sh (63 - sh)) (j + 1).toNat m0 0 c0).1 s'.dmem →
      (wRows (shlStep TA TO qa ob sh (63 - sh)) (j + 1).toNat m0 0 c0).2 = (s'.regs.rdx >>> 1) >>> (63 - sh) →
      s'.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat) →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s'.regs.r13 = j + 1 → s'.regs.r9 = n → s'.regs.r10 = sh → s'.regs.rcx = sh → s'.regs.r14 = R14 →
      (j + 1).toNat < n.toNat → Ev Q s' (at_ (kf + 40)))
    (hE : ∀ s', MrFr G d s' →
      MemRel G (wRows (shlStep TA TO qa ob sh (63 - sh)) n.toNat m0 0 c0).1 s'.dmem →
      (wRows (shlStep TA TO qa ob sh (63 - sh)) n.toNat m0 0 c0).2 = (s'.regs.rdx >>> 1) >>> (63 - sh) →
      s'.regs.r10 = sh → Ev Q s' (at_ (kf + 49))) :
    Ev Q s (at_ (kf + 40)) := by
  have hpA := G.tab.pos64_lt hTA
  have hpO := G.tab.pos64_lt hTO
  have heA := hG.end64 _ hpA
  have heO := hG.end64 _ hpO
  generalize hMc : wRows (shlStep TA TO qa ob sh (63 - sh)) j.toNat m0 0 c0 = Mc at hm hcy
  obtain ⟨M, c⟩ := Mc
  simp only at hm hcy
  have hszA := hm.size64 TA hTA
  have hszO := hm.size64 TO hTO
  generalize hBA : G.b (G.tab.pos64 TA) = BA at *
  generalize hBO : G.b (G.tab.pos64 TO) = BO at *
  have hqj : (qa + j).toNat = qa.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hoj : (ob + j).toNat = ob.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hinA : (qa + j).toNat < (M.arr64 TA).size := by rw [hqj, hszA]; omega
  have hinO : (ob + j).toNat < (M.arr64 TO).size := by rw [hoj, hszO]; omega
  have haA : s.regs.rsi.toBitVec + s.regs.r13.toBitVec * 8 = A (BA + 8 * (qa + j).toNat) := by
    rw [hrsi, hr13, addr_idx BA qa.toNat j (by omega), hqj]
  have haO : s.regs.rdi.toBitVec + s.regs.r13.toBitVec * 8 = A (BO + 8 * (ob + j).toNat) := by
    rw [hrdi, hr13, addr_idx BO ob.toNat j (by omega), hoj]
  have hrA : rdW s.dmem (A (BA + 8 * (qa + j).toNat)) = some (M.arr64 TA)[(qa + j).toNat] := by
    have := hm.get64 TA hTA (qa + j).toNat hinA; rw [hBA] at this; exact this
  have hrO : rdW s.dmem (A (BO + 8 * (ob + j).toNat)) = some (M.arr64 TO)[(ob + j).toNat] := by
    have := hm.get64 TO hTO (ob + j).toNat hinO; rw [hBO] at this; exact this
  obtain ⟨x, hx⟩ : ∃ x, (M.arr64 TA)[(qa + j).toNat]'hinA = x := ⟨_, rfl⟩
  rw [hx] at hrA
  have hx' : (M.arr64 TA)[(qa + j).toNat]! = x := by simp only [getElem!_pos, hinA]; exact hx
  have hval : dshl x s.regs.rdx sh = (x <<< sh) ||| c := by rw [dshl_eq _ _ _ hs, hcy]
  refine ev_label (sh_code hc (i := 40) rfl) ?_
  refine ev_ldX (sh_code hc (i := 41) rfl) (v := x) (by rs; rw [haA]; exact hrA) ?_
  refine ev_movRR (sh_code hc (i := 42) rfl) ?_
  refine ev_shldCl (sh_code hc (i := 43) rfl) fun st1 => ?_
  refine ev_stX (sh_code hc (i := 44) rfl) (by rs; rw [haO, hrO]; rfl) ?_
  refine ev_movRR (sh_code hc (i := 45) rfl) ?_
  refine ev_addRI (sh_code hc (i := 46) rfl) fun st2 => ?_
  refine ev_cmpRO (sh_code hc (i := 47) rfl) (v := n) (Or.inr (Or.inr ⟨.r9, rfl, by rs [hr9]⟩)) ?_
  have hj1 : (j + 1).toNat = j.toNat + 1 := L.toNat_add_one_of_lt (by omega)
  have hrow : wRows (shlStep TA TO qa ob sh (63 - sh)) (j + 1).toNat m0 0 c0 =
      (M.set64 TO (ob + j) ((x <<< sh) ||| c), (x >>> 1) >>> (63 - sh)) := by
    rw [hj1, wRows_succ, hMc, UInt64.zero_add, L.ofNat_toNat]
    simp only [shlStep, hx']
  rw [hrow] at hnext
  have hm' := MemRel.store64 hG hm hTO hinO ((x <<< sh) ||| c)
  rw [hBO] at hm'
  have hpres := hF.pres.trans (Pres.store64 hG (top := d.regs.rsp.toNat) (d := s.dmem) hTO
    (j := (ob + j).toNat) (by omega) ((x <<< sh) ||| c).toBitVec)
  rw [hBO] at hpres
  have haO' : (UInt64.ofNat (BO + 8 * ob.toNat)).toBitVec + j.toBitVec * 8 = A (BO + 8 * (ob + j).toNat) := by
    have := haO; rw [hrdi, hr13] at this; exact this
  refine ev_jcc (sh_code hc (i := 48) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · refine ev_lbl (Code.label hc (i := 40) rfl) ?_
    refine hnext _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrsi, hrdi, hr13, hr9, hr10, hrcx, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haO', hval]; exact hpres
    · rw [haO', hval]; exact hm'
    · rfl
    · simp only [CondCode.interp, cmpFlags_cf, decide_eq_true_eq] at hcc
      rs [hr13] at hcc
      exact hcc
    all_goals done
  · simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc
    rs [hr13] at hcc
    have e1 : (j + 1).toNat = (j.toBitVec + (Int64.ofInt 1).toBitVec).toNat := rfl
    have e2 : n.toNat = n.toBitVec.toNat := rfl
    have hla : j + 1 = n := UInt64.toNat_inj.mp (by omega)
    rw [← hla, hrow] at hE
    refine hE _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrsi, hrdi, hr13, hr9, hr10, hrcx, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haO', hval]; exact hpres
    · rw [haO', hval]; exact hm'
    all_goals rfl

theorem sh_loop (TA TO : TieredArray) (hTA : G.tab.dom64 TA = true) (hTO : G.tab.dom64 TO = true)
    (qa ob n sh : Word) (hs : sh < 64) (R14 : UInt64) (m0 : Mem) (c0 : Word)
    (hqa : qa.toNat + n.toNat ≤ G.s (G.tab.pos64 TA)) (hoa : ob.toNat + n.toNat ≤ G.s (G.tab.pos64 TO))
    (hE : ∀ s', MrFr G d s' →
      MemRel G (wRows (shlStep TA TO qa ob sh (63 - sh)) n.toNat m0 0 c0).1 s'.dmem →
      (wRows (shlStep TA TO qa ob sh (63 - sh)) n.toNat m0 0 c0).2 = (s'.regs.rdx >>> 1) >>> (63 - sh) →
      s'.regs.r10 = sh → Ev Q s' (at_ (kf + 49))) :
    ∀ (r : Nat) (s : MachineData) (j : Word), n.toNat = j.toNat + r → MrFr G d s →
      MemRel G (wRows (shlStep TA TO qa ob sh (63 - sh)) j.toNat m0 0 c0).1 s.dmem →
      (wRows (shlStep TA TO qa ob sh (63 - sh)) j.toNat m0 0 c0).2 = (s.regs.rdx >>> 1) >>> (63 - sh) →
      s.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat) →
      s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s.regs.r13 = j → s.regs.r9 = n → s.regs.r10 = sh → s.regs.rcx = sh → s.regs.r14 = R14 →
      j.toNat < n.toNat → Ev Q s (at_ (kf + 40)) := by
  intro r
  induction r with
  | zero => intro s j hr _ _ _ _ _ _ _ _ _ _ hj; omega
  | succ r ih =>
    intro s j hr hF hm hcy h1 h2 h3 h4 h5 h6 h7 hj
    refine sh_step hG hc TA TO hTA hTO qa ob n sh hs R14 m0 c0 hqa hoa s j hF hm hcy h1 h2 h3 h4 h5 h6 h7 hj
      ?_ hE
    intro s' g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
    have := n.toNat_lt
    exact ih s' (j + 1) (by rw [L.toNat_add_one_of_lt (by omega)]; omega) g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11

/-- `.T`: the carry out `(prev >> 1) >> (63 - s)`, the return. -/
theorem sh_tail {ra : Word} (hra : rdW d.dmem (A d.regs.rsp.toNat) = some ra) (hlo : G.lo ≤ d.regs.rsp.toNat)
    (hhi : d.regs.rsp.toNat + 8 ≤ G.hi) (s : MachineData) (hF : MrFr G d s) (sh : Word) (hr10 : s.regs.r10 = sh)
    (hok : ∀ s', s'.dmem = s.dmem → s'.regs.rsp.toNat = d.regs.rsp.toNat + 8 →
      s'.regs.rbp = d.regs.rbp → s'.regs.r15 = d.regs.r15 → s'.regs.r14.toNat ≤ d.regs.r14.toNat →
      s'.regs.rax = (s.regs.rdx >>> 1) >>> (63 - sh) → Ev Q s' (Int64.ofBitVec ra.toBitVec)) :
    Ev Q s (at_ (kf + 49)) := by
  refine ev_label (sh_code hc (i := 49) rfl) ?_
  refine ev_shiftR (n := 1) (op := .shr) (by decide) (Or.inr rfl) (sh_code hc (i := 50) rfl) fun st1 => ?_
  refine ev_movRI (sh_code hc (i := 51) rfl) ?_
  refine ev_subRR (sh_code hc (i := 52) rfl) fun st2 _ => ?_
  refine ev_shrCl (sh_code hc (i := 53) rfl) fun st3 => ?_
  refine ev_movRR (sh_code hc (i := 54) rfl) ?_
  refine frame_ret hG hra hlo hhi ⟨?_, ?_, ?_, ?_, ?_⟩ (sh_code hc (i := 55) rfl) fun s' e1 e2 e3 e4 e5 e6 => ?_
  all_goals try rs [hF.rsp, hF.rbp, hF.r15]
  · exact hF.r14
  · exact hF.pres
  · refine hok s' e1 e2 e3 e4 (by rw [e5]; rs; exact hF.r14) ?_
    rw [e6]; rs [hr10]
    simp only [BinOp.eval]
    rfl

/-- The first limb (index 30): `(A[0] << s) | c`, then the loop (`.L`) or, for `n = 1`, `.T`. -/
theorem sh_first (TA TO : TieredArray) (hTA : G.tab.dom64 TA = true) (hTO : G.tab.dom64 TO = true)
    (qa ob n sh c : Word) (m0 : Mem) (R14 : UInt64)
    (hqa : qa.toNat + n.toNat ≤ G.s (G.tab.pos64 TA)) (hoa : ob.toNat + n.toNat ≤ G.s (G.tab.pos64 TO))
    (hn1 : 1 ≤ n.toNat) (s : MachineData) (hF : MrFr G d s) (hm : MemRel G m0 s.dmem)
    (hrsi : s.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat))
    (hrdi : s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat))
    (hr9 : s.regs.r9 = n) (hr10 : s.regs.r10 = sh) (hr11 : s.regs.r11 = c) (hr14 : s.regs.r14 = R14)
    (hL : ∀ s', MrFr G d s' →
      MemRel G (wRows (shlStep TA TO qa ob sh (63 - sh)) (1 : Word).toNat m0 0 c).1 s'.dmem →
      (wRows (shlStep TA TO qa ob sh (63 - sh)) (1 : Word).toNat m0 0 c).2 = (s'.regs.rdx >>> 1) >>> (63 - sh) →
      s'.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat) →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s'.regs.r13 = 1 → s'.regs.r9 = n → s'.regs.r10 = sh → s'.regs.rcx = sh → s'.regs.r14 = R14 →
      (1 : Word).toNat < n.toNat → Ev Q s' (at_ (kf + 40)))
    (hT : ∀ s', MrFr G d s' → MemRel G (wRows (shlStep TA TO qa ob sh (63 - sh)) n.toNat m0 0 c).1 s'.dmem →
      (wRows (shlStep TA TO qa ob sh (63 - sh)) n.toNat m0 0 c).2 = (s'.regs.rdx >>> 1) >>> (63 - sh) →
      s'.regs.r10 = sh → Ev Q s' (at_ (kf + 49))) :
    Ev Q s (at_ (kf + 30)) := by
  have hpA := G.tab.pos64_lt hTA
  have hpO := G.tab.pos64_lt hTO
  have heA := hG.end64 _ hpA
  have heO := hG.end64 _ hpO
  have hszA := hm.size64 TA hTA
  have hszO := hm.size64 TO hTO
  generalize hBA : G.b (G.tab.pos64 TA) = BA at *
  generalize hBO : G.b (G.tab.pos64 TO) = BO at *
  have hq0 : (qa + 0).toNat = qa.toNat := by simp
  have ho0 : (ob + 0).toNat = ob.toNat := by simp
  have hinA : (qa + 0).toNat < (m0.arr64 TA).size := by rw [hq0, hszA]; omega
  have hinO : (ob + 0).toNat < (m0.arr64 TO).size := by rw [ho0, hszO]; omega
  have haA : s.regs.rsi.toBitVec + (0 : Word).toBitVec * 8 = A (BA + 8 * (qa + 0).toNat) := by
    rw [hrsi, addr_idx BA qa.toNat 0 (by simp; omega), hq0]; simp
  have haO : s.regs.rdi.toBitVec + (0 : Word).toBitVec * 8 = A (BO + 8 * (ob + 0).toNat) := by
    rw [hrdi, addr_idx BO ob.toNat 0 (by simp; omega), ho0]; simp
  have hrA : rdW s.dmem (A (BA + 8 * (qa + 0).toNat)) = some (m0.arr64 TA)[(qa + 0).toNat] := by
    have := hm.get64 TA hTA _ hinA; rw [hBA] at this; exact this
  have hrO : rdW s.dmem (A (BO + 8 * (ob + 0).toNat)) = some (m0.arr64 TO)[(ob + 0).toNat] := by
    have := hm.get64 TO hTO _ hinO; rw [hBO] at this; exact this
  obtain ⟨x0, hx0⟩ : ∃ x, (m0.arr64 TA)[(qa + 0).toNat]'hinA = x := ⟨_, rfl⟩
  rw [hx0] at hrA
  have hx0' : (m0.arr64 TA)[(qa + 0).toNat]! = x0 := by simp only [getElem!_pos, hinA]; exact hx0
  have hrow1 : wRows (shlStep TA TO qa ob sh (63 - sh)) (1 : Word).toNat m0 0 c =
      (m0.set64 TO (ob + 0) ((x0 <<< sh) ||| c), (x0 >>> 1) >>> (63 - sh)) := by
    simp only [UInt64.toNat_one, wRows, shlStep, hx0']
  have hm' := MemRel.store64 hG hm hTO hinO ((x0 <<< sh) ||| c)
  rw [hBO] at hm'
  have hpres := hF.pres.trans (Pres.store64 hG (top := d.regs.rsp.toNat) (d := s.dmem) hTO
    (j := (ob + 0).toNat) (by omega) ((x0 <<< sh) ||| c).toBitVec)
  rw [hBO] at hpres
  refine ev_movRI (sh_code hc (i := 30) rfl) ?_
  refine ev_movRR (sh_code hc (i := 31) rfl) ?_
  refine ev_ldX (sh_code hc (i := 32) rfl) (v := x0) (by rs; rw [haA]; exact hrA) ?_
  refine ev_movRR (sh_code hc (i := 33) rfl) ?_
  refine ev_shlCl (sh_code hc (i := 34) rfl) fun st1 => ?_
  refine ev_aluOp (op := .or) (v := c) rfl (sh_code hc (i := 35) rfl) (Or.inr (Or.inr ⟨.r11, rfl, by rs [hr11]⟩))
    fun st2 => ?_
  refine ev_stX (sh_code hc (i := 36) rfl) (by rs; rw [haO, hrO]; rfl) ?_
  refine ev_addRI (sh_code hc (i := 37) rfl) fun st3 => ?_
  refine ev_cmpRO (sh_code hc (i := 38) rfl) (v := n) (Or.inr (Or.inr ⟨.r9, rfl, by rs [hr9]⟩)) ?_
  rw [hrow1] at hL
  have haO' : (UInt64.ofNat (BO + 8 * ob.toNat)).toBitVec + (0 : Word).toBitVec * 8 = A (BO + 8 * (ob + 0).toNat) := by
    have := haO; rw [hrdi] at this; exact this
  have hval : (BinOp.or.eval (UInt64.ofBitVec x0.toBitVec <<< sh) c).toBitVec = ((x0 <<< sh) ||| c).toBitVec := rfl
  refine ev_jcc (sh_code hc (i := 39) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_true', decide_eq_false_iff_not] at hcc
    rs at hcc
    have hn : n.toNat = 1 := by
      have e : n.toBitVec.toNat = n.toNat := rfl
      have e1 : ((0 : Word).toBitVec + (Int64.ofInt 1).toBitVec).toNat = 1 := rfl
      rw [e, e1] at hcc; omega
    refine ev_lbl (Code.label hc (i := 49) rfl) ?_
    rw [hn, ← UInt64.toNat_one, hrow1] at hT
    refine hT _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hr10, hr11, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haO]; exact hpres
    · rw [haO]; exact hm'
    all_goals rfl
  · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_false', decide_eq_true_eq] at hcc
    rs at hcc
    have hlt : (1 : Word).toNat < n.toNat := by
      have e : n.toBitVec.toNat = n.toNat := rfl
      have e1 : ((0 : Word).toBitVec + (Int64.ofInt 1).toBitVec).toNat = 1 := rfl
      rw [e, e1] at hcc; simpa using hcc
    refine hL _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrsi, hrdi, hr9, hr10, hr11, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haO', hval]; exact hpres
    · rw [haO', hval]; exact hm'
    all_goals try rfl
    exact hlt

end

/-- **The `shl_n` body meets the compiler's per-function contract.** -/
theorem shlAsm_sim [Host] (p : Prog) (G : L.Compiler.Layout) (hG : G.Ok)
    (hspec : ShlSpec p) (fd : FunDecl) (hnp : fd.nparams = 5) (hnr : Stmt.nret fd.body = 1)
    (hdom : G.tab.dom64 (tier1 0) = true)
    (hoffL : SmallOff (G.tab.len64 (0 : ArrId))) (hoffB : SmallOff (G.tab.base64 (0 : ArrId)))
    (kf : Nat) (hc : Code (shlAsm G.tab) kf) (sk : NTree) (n : Nat) :
    FnSimAt p G sk n "shl_n" fd kf := by
  intro vs σ d ra Q hlen hra hargs hlo8 hhi h15 hmem h14 hok herr habrt hexh
  have hlo : G.lo ≤ d.regs.rsp.toNat := by omega
  rw [hnp] at hlen
  obtain ⟨o, oa, nn, sh, c, rfl⟩ : ∃ o oa nn sh c, vs = [o, oa, nn, sh, c] := by
    match vs, hlen with
    | [o, oa, nn, sh, c], _ => exact ⟨o, oa, nn, sh, c, rfl⟩
  have hA := hargs.1 (by simp [argRegs])
  have hrdi : d.regs.rdi = o := UInt64.toBitVec_inj.mp (hA 0 (by simp))
  have hr8 : d.regs.r8 = oa := UInt64.toBitVec_inj.mp (hA 1 (by simp))
  have hr9 : d.regs.r9 = nn := UInt64.toBitVec_inj.mp (hA 2 (by simp))
  have hr10 : d.regs.r10 = sh := UInt64.toBitVec_inj.mp (hA 3 (by simp))
  have hr11 : d.regs.r11 = c := UInt64.toBitVec_inj.mp (hA 4 (by simp))
  have hn0 : 0 < n := by omega
  have hh := hG.hi_le
  refine ev_label (sh_code hc (i := 0) rfl) ?_
  refine ev_cmpRO (sh_code hc (i := 1) rfl) (v := 63) (Or.inl rfl) ?_
  refine ev_jcc (sh_code hc (i := 2) rfl) (fun _ => hexh _ ⟨rfl, Pres.refl _ _⟩) (fun hca => ?_)
  have hs : sh < 64 := by
    simp only [CondCode.interp, cmpFlags_cf, cmpFlags_zf, Bool.and_eq_false_iff, Bool.not_eq_false',
      decide_eq_true_eq, beq_iff_eq] at hca
    rs [hr10] at hca
    rw [UInt64.lt_iff_toNat_lt]
    rcases hca with h | h
    · have : (63 : Word).toBitVec.toNat = 63 := rfl
      have e : sh.toBitVec.toNat = sh.toNat := rfl
      simp only [this, e] at h; simp; omega
    · have := UInt64.toBitVec_inj.mp h; subst this; decide
  refine ev_cmpRO (sh_code hc (i := 3) rfl) (v := 0) (Or.inl rfl) ?_
  refine ev_jcc (sh_code hc (i := 4) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · -- `n = 0`: return the carry
    simp only [CondCode.interp, cmpFlags_zf, beq_iff_eq] at hcc
    rs [hr9] at hcc
    have hn0' : nn = 0 := UInt64.toBitVec_inj.mp hcc
    subst hn0'
    refine ev_lbl (Code.label hc (i := 56) rfl) ?_
    refine ev_label (sh_code hc (i := 56) rfl) ?_
    refine ev_movRR (sh_code hc (i := 57) rfl) ?_
    refine frame_ret hG hra hlo hhi ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.refl _ _⟩ (sh_code hc (i := 58) rfl)
      fun s' e1 e2 e3 e4 e5 e6 => ?_
    have hrun := hspec σ o oa 0 sh c n (by simp; omega) (Or.inl rfl)
    simp only [UInt64.toNat_zero, wRows] at hrun
    refine hok [c] σ s' (by rw [hrun]) (by rw [e1]; exact hmem) rfl e2 e3 e4
      (by rw [e5]; rs; exact Nat.le_refl _) ?_ (by rw [e1]; exact Pres.refl _ _)
    rw [hnr]; exact resOut_zero' (by rw [e6]; rs [hr11])
  simp only [CondCode.interp, cmpFlags_zf, beq_eq_false_iff_ne] at hcc
  rs [hr9] at hcc
  have hnz : nn ≠ 0 := fun h => hcc (by rw [h])
  refine ev_movRI (sh_code hc (i := 5) rfl) ?_
  refine ev_movRR (sh_code hc (i := 6) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (sh_code hc (i := 7) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (sh_code hc (i := 8) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (sh_code hc (i := 9) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_movRR (sh_code hc (i := 10) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (sh_code hc (i := 11) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (sh_code hc (i := 12) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (sh_code hc (i := 13) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_gen (fun s1 => s1.regs.rcx = (o >>> 40) &&& 1 ∧ s1.regs.rdi = o &&& idxMask ∧
      s1.regs.rdx = (oa >>> 40) &&& 1 ∧ s1.regs.r8 = oa &&& idxMask ∧ s1.regs.r9 = nn ∧
      s1.regs.r10 = sh ∧ s1.regs.r11 = c ∧
      s1.regs.r14 = d.regs.r14 ∧ s1.regs.r15 = d.regs.r15 ∧
      s1.regs.rsp = d.regs.rsp ∧ s1.regs.rbp = d.regs.rbp ∧ s1.dmem = d.dmem)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rs [hrdi, hr8, hr9, hr10, hr11, BinOp.eval]
        all_goals rfl)
    fun s1 ⟨g1, g2, g3, g4, g7, g5, g8, g9, g10, g11, g12, g13⟩ => ?_
  have hTA := G.tab.dom64_tierA hdom (oa >>> 40)
  have hTO := G.tab.dom64_tierA hdom (o >>> 40)
  have heA := hG.end64 _ (G.tab.pos64_lt hTA)
  have heO := hG.end64 _ (G.tab.pos64_lt hTO)
  have hm1 : MemRel G σ.mem s1.dmem := by rw [g13]; exact hmem
  have h15' : s1.regs.r15.toNat = G.T := by rw [g10]; exact h15
  have hdA := pool_desc hm1 hdom (oa >>> 40) (r := .rdx) (by rs [g3]) h15'
  have hdO := pool_desc hm1 hdom (o >>> 40) (r := .rcx) (by rs [g1]) h15'
  have hszA := hmem.size64 _ hTA
  have hszO := hmem.size64 _ hTO
  generalize hSA : G.s (G.tab.pos64 (tierA 0 (oa >>> 40))) = SA at *
  generalize hSO : G.s (G.tab.pos64 (tierA 0 (o >>> 40))) = SO at *
  generalize hBA : G.b (G.tab.pos64 (tierA 0 (oa >>> 40))) = BA at *
  generalize hBO : G.b (G.tab.pos64 (tierA 0 (o >>> 40))) = BO at *
  have hSAn : (UInt64.ofNat SA).toNat = SA := L.toNat_ofNat_of_lt (by omega)
  have hSOn : (UInt64.ofNat SO).toNat = SO := L.toNat_ofNat_of_lt (by omega)
  have hsub : ∀ (S : Nat) (w : Word), S < 2 ^ 64 → w.toNat ≤ S →
      ((UInt64.ofNat S).toBitVec - w.toBitVec).toNat = S - w.toNat := by
    intro S w h1 h2
    rw [BitVec.toNat_sub, UInt64.toNat_toBitVec, show (UInt64.ofNat S).toBitVec.toNat = S from
      L.toNat_ofNat_of_lt h1]
    have := w.toNat_lt; omega
  have hX : ∀ s', s'.regs.rbp = d.regs.rbp → s'.dmem = s1.dmem → Ev Q s' (label exhaustedL) :=
    fun s' e1 e2 => hexh _ ⟨e1, by rw [e2, g13]; exact Pres.refl _ _⟩
  -- the window of `a`
  refine ev_movRMt (sh_code hc (i := 14) rfl) hoffL (v := UInt64.ofNat SA) hdA.1 ?_
  refine ev_subRR (sh_code hc (i := 15) rfl) fun st hcf => ?_
  rs [g4, hSAn] at hcf
  refine ev_jcc (sh_code hc (i := 16) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSAn] at hcc
  refine ev_cmpRO (sh_code hc (i := 17) rfl) (v := nn) (Or.inr (Or.inr ⟨.r9, rfl, by rs [g7]⟩)) ?_
  refine ev_jcc (sh_code hc (i := 18) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc2 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc2
  rs [g4] at hcc2
  rw [hsub SA _ (by omega) (by omega)] at hcc2
  simp only [UInt64.toNat_toBitVec] at hcc2
  have hqa : (oa &&& idxMask).toNat + nn.toNat ≤ SA := by omega
  refine ev_movRMt (sh_code hc (i := 19) rfl) hoffB (v := UInt64.ofNat BA) (by rs; exact hdA.2) ?_
  refine ev_leaX (sh_code hc (i := 20) rfl) ?_
  -- the output window
  refine ev_movRMt (sh_code hc (i := 21) rfl) hoffL (v := UInt64.ofNat SO) (by rs; exact hdO.1) ?_
  refine ev_subRR (sh_code hc (i := 22) rfl) fun st hcf => ?_
  rs [g2, hSOn] at hcf
  refine ev_jcc (sh_code hc (i := 23) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc5 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSOn] at hcc5
  refine ev_cmpRO (sh_code hc (i := 24) rfl) (v := nn) (Or.inr (Or.inr ⟨.r9, rfl, by rs [g7]⟩)) ?_
  refine ev_jcc (sh_code hc (i := 25) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc6 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc6
  rs [g2] at hcc6
  rw [hsub SO _ (by omega) (by omega)] at hcc6
  simp only [UInt64.toNat_toBitVec] at hcc6
  have hoa : (o &&& idxMask).toNat + nn.toNat ≤ SO := by omega
  refine ev_movRMt (sh_code hc (i := 26) rfl) hoffB (v := UInt64.ofNat BO) (by rs; exact hdO.2) ?_
  refine ev_leaX (sh_code hc (i := 27) rfl) ?_
  -- the fuel
  refine ev_subRR (sh_code hc (i := 28) rfl) fun st hcf => ?_
  rs [g7, g9] at hcf
  refine ev_jcc (sh_code hc (i := 29) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc7 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec] at hcc7
  have hl14 : nn.toNat ≤ d.regs.r14.toNat := by omega
  have hnF : nn.toNat < n := by omega
  have hrun := hspec σ o oa nn sh c n hnF (Or.inr ⟨by rw [hszA]; exact hqa, by rw [hszO]; exact hoa,
    by rw [hszA]; omega, by rw [hszO]; omega⟩)
  simp only [] at hrun
  rw [← hSA] at hqa
  rw [← hSO] at hoa
  -- the tail
  have hT : ∀ s', MrFr G d s' →
      MemRel G (wRows (shlStep (tierA 0 (oa >>> 40)) (tierA 0 (o >>> 40)) (oa &&& idxMask) (o &&& idxMask) sh (63 - sh)) nn.toNat σ.mem 0 c).1 s'.dmem →
      (wRows (shlStep (tierA 0 (oa >>> 40)) (tierA 0 (o >>> 40)) (oa &&& idxMask) (o &&& idxMask) sh (63 - sh)) nn.toNat σ.mem 0 c).2 =
        (s'.regs.rdx >>> 1) >>> (63 - sh) →
      s'.regs.r10 = sh → Ev Q s' (at_ (kf + 49)) := by
    intro s' fr hm' hcy h10
    refine sh_tail hG hc hra hlo hhi s' fr sh h10 fun s'' e1 e2 e3 e4 e5 e6 => ?_
    refine hok _ _ s'' hrun (by rw [e1]; exact hm') rfl e2 e3 e4 e5 ?_ (by rw [e1]; exact fr.pres)
    rw [hnr]; exact resOut_zero' (by rw [e6, hcy])
  have hn1 : 1 ≤ nn.toNat := by
    have := L.toNat_ne_zero_of_ne _ hnz; omega
  refine sh_first (d := d) hG hc _ _ hTA hTO (oa &&& idxMask) (o &&& idxMask) nn sh c σ.mem
    (d.regs.r14 - nn) hqa hoa hn1 _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun s' fr hm' hcy h1 h2 h3 h4 h5 h6 h7 hlt => sh_loop hG hc _ _ hTA hTO _ _ nn sh hs (d.regs.r14 - nn)
      σ.mem c hqa hoa hT (nn.toNat - 1) s' 1 (by simp only [UInt64.toNat_one]; omega) fr hm' hcy h1 h2 h3 h4 h5
      h6 h7 hlt) hT
  all_goals try rs [g1, g2, g3, g4, g5, g7, g8, g9, g10, g11, g12, g13]
  · show (d.regs.r14 - nn).toNat ≤ _
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hl14)]; omega
  · exact Pres.refl _ _
  · exact hmem
  · apply UInt64.toBitVec_inj.mp
    rw [hBA]
    have := addr_idx BA 0 (oa &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  · apply UInt64.toBitVec_inj.mp
    rw [hBO]
    have := addr_idx BO 0 (o &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  all_goals rfl

end L.AsmEsc
