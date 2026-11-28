module

public import ConAguaX86.AsmEsc.BitAsm
public import ConAguaX86.AsmEsc.BitL
import Kraken.X64.Registers

@[expose] public section

/-!
# The bitwise and copy templates meet the compiler's contract

`bitAsm_sim`, `copyAsm_sim`: the per-function contract (`FnSimAt`) of the templates of
`BitAsm.lean`, for any L function whose run is the model (`BitSpec`, `CopySpec`, `BitL.lean`).
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

section
variable [Host] {kf : Nat} {tab : Tab} {f : FnName} {op : BinOp}

theorem b_code (hc : Code (bitAsm tab f op) kf) {i : Nat} {x : Directive}
    (hi : (bitAsm tab f op)[i]? = some x) : Host.prog[kf + i]? = some x := Code.get hc hi

end

section
variable [Host] {G : L.Compiler.Layout} (hG : G.Ok) {kf : Nat} {f : FnName} {op : BinOp}
  (hop : op = .and ∨ op = .or ∨ op = .xor) (hc : Code (bitAsm G.tab f op) kf)
  {d : MachineData} {Q : MachineState → Prop}
include hG hop hc

/-- One step of the loop (`.L`) at index `j < n`: the next step or, after the last, `.Z`. -/
theorem b_step (TA TB TO : TieredArray) (hTA : G.tab.dom64 TA = true) (hTB : G.tab.dom64 TB = true)
    (hTO : G.tab.dom64 TO = true) (qa qb ob n : Word) (R14 : UInt64) (m0 : Mem)
    (hqa : qa.toNat + n.toNat ≤ G.s (G.tab.pos64 TA)) (hqb : qb.toNat + n.toNat ≤ G.s (G.tab.pos64 TB))
    (hoa : ob.toNat + n.toNat ≤ G.s (G.tab.pos64 TO))
    (s : MachineData) (j : Word) (hF : MrFr G d s)
    (hm : MemRel G (g0Rows (bitStep op TA TB TO qa qb ob) j.toNat m0 0) s.dmem)
    (hrsi : s.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat))
    (hrbx : s.regs.rbx = UInt64.ofNat (G.b (G.tab.pos64 TB) + 8 * qb.toNat))
    (hrdi : s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat))
    (hr13 : s.regs.r13 = j) (hr10 : s.regs.r10 = n) (hr14 : s.regs.r14 = R14) (hj : j.toNat < n.toNat)
    (hnext : ∀ s', MrFr G d s' → MemRel G (g0Rows (bitStep op TA TB TO qa qb ob) (j + 1).toNat m0 0) s'.dmem →
      s'.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat) →
      s'.regs.rbx = UInt64.ofNat (G.b (G.tab.pos64 TB) + 8 * qb.toNat) →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s'.regs.r13 = j + 1 → s'.regs.r10 = n → s'.regs.r14 = R14 →
      (j + 1).toNat < n.toNat → Ev Q s' (at_ (kf + 40)))
    (hE : ∀ s', MrFr G d s' → MemRel G (g0Rows (bitStep op TA TB TO qa qb ob) n.toNat m0 0) s'.dmem →
      Ev Q s' (at_ (kf + 47))) :
    Ev Q s (at_ (kf + 40)) := by
  have hpA := G.tab.pos64_lt hTA
  have hpB := G.tab.pos64_lt hTB
  have hpO := G.tab.pos64_lt hTO
  have heA := hG.end64 _ hpA
  have heB := hG.end64 _ hpB
  have heO := hG.end64 _ hpO
  generalize hMc : g0Rows (bitStep op TA TB TO qa qb ob) j.toNat m0 0 = M at hm
  have hszA := hm.size64 TA hTA
  have hszB := hm.size64 TB hTB
  have hszO := hm.size64 TO hTO
  generalize hBA : G.b (G.tab.pos64 TA) = BA at *
  generalize hBB : G.b (G.tab.pos64 TB) = BB at *
  generalize hBO : G.b (G.tab.pos64 TO) = BO at *
  have hqj : (qa + j).toNat = qa.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hbj : (qb + j).toNat = qb.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hoj : (ob + j).toNat = ob.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hinA : (qa + j).toNat < (M.arr64 TA).size := by rw [hqj, hszA]; omega
  have hinB : (qb + j).toNat < (M.arr64 TB).size := by rw [hbj, hszB]; omega
  have hinO : (ob + j).toNat < (M.arr64 TO).size := by rw [hoj, hszO]; omega
  have haA : s.regs.rsi.toBitVec + s.regs.r13.toBitVec * 8 = A (BA + 8 * (qa + j).toNat) := by
    rw [hrsi, hr13, addr_idx BA qa.toNat j (by omega), hqj]
  have haB : s.regs.rbx.toBitVec + s.regs.r13.toBitVec * 8 = A (BB + 8 * (qb + j).toNat) := by
    rw [hrbx, hr13, addr_idx BB qb.toNat j (by omega), hbj]
  have haO : s.regs.rdi.toBitVec + s.regs.r13.toBitVec * 8 = A (BO + 8 * (ob + j).toNat) := by
    rw [hrdi, hr13, addr_idx BO ob.toNat j (by omega), hoj]
  have hrA : rdW s.dmem (A (BA + 8 * (qa + j).toNat)) = some (M.arr64 TA)[(qa + j).toNat] := by
    have := hm.get64 TA hTA (qa + j).toNat hinA; rw [hBA] at this; exact this
  have hrB : rdW s.dmem (A (BB + 8 * (qb + j).toNat)) = some (M.arr64 TB)[(qb + j).toNat] := by
    have := hm.get64 TB hTB (qb + j).toNat hinB; rw [hBB] at this; exact this
  have hrO : rdW s.dmem (A (BO + 8 * (ob + j).toNat)) = some (M.arr64 TO)[(ob + j).toNat] := by
    have := hm.get64 TO hTO (ob + j).toNat hinO; rw [hBO] at this; exact this
  refine ev_label (b_code hc (i := 40) rfl) ?_
  refine ev_ldX (b_code hc (i := 41) rfl) (v := (M.arr64 TA)[(qa + j).toNat]) (by rs; rw [haA]; exact hrA) ?_
  refine ev_bitOpS hop (b_code hc (i := 42) rfl) (v := (M.arr64 TB)[(qb + j).toNat]) (by rs; rw [haB]; exact hrB)
    fun st1 => ?_
  refine ev_stX (b_code hc (i := 43) rfl) (by rs; rw [haO, hrO]; rfl) ?_
  refine ev_addRI (b_code hc (i := 44) rfl) fun st2 => ?_
  refine ev_cmpRO (b_code hc (i := 45) rfl) (v := n) (Or.inr (Or.inr ⟨.r10, rfl, by rs [hr10]⟩)) ?_
  have hj1 : (j + 1).toNat = j.toNat + 1 := L.toNat_add_one_of_lt (by omega)
  have hval : op.eval (M.arr64 TA)[(qa + j).toNat] (M.arr64 TB)[(qb + j).toNat] =
      op.eval (UInt64.ofBitVec (M.arr64 TA)[(qa + j).toNat].toBitVec) (M.arr64 TB)[(qb + j).toNat] := rfl
  have hrow : g0Rows (bitStep op TA TB TO qa qb ob) (j + 1).toNat m0 0 =
      M.set64 TO (ob + j) (op.eval (M.arr64 TA)[(qa + j).toNat] (M.arr64 TB)[(qb + j).toNat]) := by
    rw [hj1, g0Rows_succ, hMc, UInt64.zero_add, L.ofNat_toNat]
    simp only [bitStep, getElem!_pos, hinA, hinB]
  rw [hrow] at hnext
  have hm' := MemRel.store64 hG hm hTO hinO (op.eval (M.arr64 TA)[(qa + j).toNat] (M.arr64 TB)[(qb + j).toNat])
  rw [hBO] at hm'
  have hpres := hF.pres.trans (Pres.store64 hG (top := d.regs.rsp.toNat) (d := s.dmem) hTO
    (j := (ob + j).toNat) (by omega) (op.eval (M.arr64 TA)[(qa + j).toNat] (M.arr64 TB)[(qb + j).toNat]).toBitVec)
  rw [hBO] at hpres
  have haO' : (UInt64.ofNat (BO + 8 * ob.toNat)).toBitVec + j.toBitVec * 8 = A (BO + 8 * (ob + j).toNat) := by
    have := haO; rw [hrdi, hr13] at this; exact this
  refine ev_jcc (b_code hc (i := 46) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · refine ev_lbl (Code.label hc (i := 40) rfl) ?_
    refine hnext _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrsi, hrbx, hrdi, hr13, hr10, hr14]
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
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrsi, hrbx, hrdi, hr13, hr10, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haO']; exact hpres
    · rw [haO']; exact hm'

/-- The loop from `.L`, by induction on the limbs left. -/
theorem b_loop (TA TB TO : TieredArray) (hTA : G.tab.dom64 TA = true) (hTB : G.tab.dom64 TB = true)
    (hTO : G.tab.dom64 TO = true) (qa qb ob n : Word) (R14 : UInt64) (m0 : Mem)
    (hqa : qa.toNat + n.toNat ≤ G.s (G.tab.pos64 TA)) (hqb : qb.toNat + n.toNat ≤ G.s (G.tab.pos64 TB))
    (hoa : ob.toNat + n.toNat ≤ G.s (G.tab.pos64 TO))
    (hE : ∀ s', MrFr G d s' → MemRel G (g0Rows (bitStep op TA TB TO qa qb ob) n.toNat m0 0) s'.dmem →
      Ev Q s' (at_ (kf + 47))) :
    ∀ (r : Nat) (s : MachineData) (j : Word), n.toNat = j.toNat + r → MrFr G d s →
      MemRel G (g0Rows (bitStep op TA TB TO qa qb ob) j.toNat m0 0) s.dmem →
      s.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat) →
      s.regs.rbx = UInt64.ofNat (G.b (G.tab.pos64 TB) + 8 * qb.toNat) →
      s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s.regs.r13 = j → s.regs.r10 = n → s.regs.r14 = R14 → j.toNat < n.toNat → Ev Q s (at_ (kf + 40)) := by
  intro r
  induction r with
  | zero => intro s j hr _ _ _ _ _ _ _ _ hj; omega
  | succ r ih =>
    intro s j hr hF hm h1 h2 h3 h4 h5 h6 hj
    refine b_step hG hop hc TA TB TO hTA hTB hTO qa qb ob n R14 m0 hqa hqb hoa s j hF hm h1 h2 h3 h4 h5 h6 hj
      ?_ hE
    intro s' g1 g2 g3 g4 g5 g6 g7 g8 g9
    have := n.toNat_lt
    exact ih s' (j + 1) (by rw [L.toNat_add_one_of_lt (by omega)]; omega) g1 g2 g3 g4 g5 g6 g7 g8 g9

omit hop in
/-- `.Z`: the result `0`, the return. -/
theorem b_exit {ra : Word} (hra : rdW d.dmem (A d.regs.rsp.toNat) = some ra) (hlo : G.lo ≤ d.regs.rsp.toNat)
    (hhi : d.regs.rsp.toNat + 8 ≤ G.hi) (s : MachineData) (hF : MrFr G d s)
    (hok : ∀ s', s'.dmem = s.dmem → s'.regs.rsp.toNat = d.regs.rsp.toNat + 8 →
      s'.regs.rbp = d.regs.rbp → s'.regs.r15 = d.regs.r15 → s'.regs.r14.toNat ≤ d.regs.r14.toNat →
      s'.regs.rax = 0 → Ev Q s' (Int64.ofBitVec ra.toBitVec)) :
    Ev Q s (at_ (kf + 47)) := by
  refine ev_label (b_code hc (i := 47) rfl) ?_
  refine ev_movRI (b_code hc (i := 48) rfl) ?_
  refine frame_ret hG hra hlo hhi ⟨?_, ?_, ?_, ?_, ?_⟩ (b_code hc (i := 49) rfl) fun s' e1 e2 e3 e4 e5 e6 => ?_
  all_goals try rs [hF.rsp, hF.rbp, hF.r15]
  · exact hF.r14
  · exact hF.pres
  · exact hok s' e1 e2 e3 e4 (by rw [e5]; rs; exact hF.r14) (by rw [e6]; rs)

end

/-- **The bitwise template meets the compiler's per-function contract**, for any L function `f`
with four parameters and one result whose run is the model (`BitSpec`), in any table where
`POOL` (0) is a tiered word array with small descriptor offsets, at every fuel. -/
theorem bitAsm_sim [Host] (p : Prog) (G : L.Compiler.Layout) (hG : G.Ok) (f : FnName) (op : BinOp)
    (hop : op = .and ∨ op = .or ∨ op = .xor)
    (fd : FunDecl) (hspec : BitSpec p f op) (hnp : fd.nparams = 4) (hnr : Stmt.nret fd.body = 1)
    (hdom : G.tab.dom64 (tier1 0) = true)
    (hoffL : SmallOff (G.tab.len64 (0 : ArrId))) (hoffB : SmallOff (G.tab.base64 (0 : ArrId)))
    (kf : Nat) (hc : Code (bitAsm G.tab f op) kf) (sk : NTree) (n : Nat) :
    FnSimAt p G sk n f fd kf := by
  intro vs σ d ra Q hlen hra hargs hlo8 hhi h15 hmem h14 hok herr habrt hexh
  have hlo : G.lo ≤ d.regs.rsp.toNat := by omega
  rw [hnp] at hlen
  obtain ⟨o, oa, ob, nn, rfl⟩ : ∃ o oa ob nn, vs = [o, oa, ob, nn] := by
    match vs, hlen with
    | [o, oa, ob, nn], _ => exact ⟨o, oa, ob, nn, rfl⟩
  have hA := hargs.1 (by simp [argRegs])
  have hrdi : d.regs.rdi = o := UInt64.toBitVec_inj.mp (hA 0 (by simp))
  have hr8 : d.regs.r8 = oa := UInt64.toBitVec_inj.mp (hA 1 (by simp))
  have hr9 : d.regs.r9 = ob := UInt64.toBitVec_inj.mp (hA 2 (by simp))
  have hr10 : d.regs.r10 = nn := UInt64.toBitVec_inj.mp (hA 3 (by simp))
  have hn0 : 0 < n := by omega
  have hh := hG.hi_le
  have hfin : ∀ (M : Mem), (invoke p (exec p n) f [o, oa, ob, nn]).run σ = .ok ([0], { σ with mem := M }) →
      ∀ s, MrFr G d s → MemRel G M s.dmem → Ev Q s (at_ (kf + 47)) := by
    intro M hrun s hF hm
    refine b_exit hG hc hra hlo hhi s hF fun s' e1 e2 e3 e4 e5 e6 => ?_
    refine hok _ _ s' hrun (by rw [e1]; exact hm) rfl e2 e3 e4 e5 ?_ (by rw [e1]; exact hF.pres)
    rw [hnr]; exact resOut_zero' e6
  refine ev_label (b_code hc (i := 0) rfl) ?_
  refine ev_cmpRO (b_code hc (i := 1) rfl) (v := 0) (Or.inl rfl) ?_
  refine ev_jcc (b_code hc (i := 2) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · simp only [CondCode.interp, cmpFlags_zf, beq_iff_eq] at hcc
    rs [hr10] at hcc
    have hn0' : nn = 0 := UInt64.toBitVec_inj.mp hcc
    subst hn0'
    have hrun := hspec σ o oa ob 0 n (by simp; omega) (Or.inl rfl)
    simp only [UInt64.toNat_zero, g0Rows] at hrun
    refine ev_lbl (Code.label hc (i := 47) rfl) ?_
    exact hfin σ.mem hrun _ ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.refl _ _⟩ hmem
  simp only [CondCode.interp, cmpFlags_zf, beq_eq_false_iff_ne] at hcc
  rs [hr10] at hcc
  have hnz : nn ≠ 0 := fun h => hcc (by rw [h])
  refine ev_movRI (b_code hc (i := 3) rfl) ?_
  refine ev_movRR (b_code hc (i := 4) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (b_code hc (i := 5) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (b_code hc (i := 6) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (b_code hc (i := 7) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_movRR (b_code hc (i := 8) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (b_code hc (i := 9) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (b_code hc (i := 10) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (b_code hc (i := 11) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_movRR (b_code hc (i := 12) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (b_code hc (i := 13) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (b_code hc (i := 14) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (b_code hc (i := 15) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_gen (fun s1 => s1.regs.rcx = (o >>> 40) &&& 1 ∧ s1.regs.rdi = o &&& idxMask ∧
      s1.regs.rdx = (oa >>> 40) &&& 1 ∧ s1.regs.r8 = oa &&& idxMask ∧
      s1.regs.r12 = (ob >>> 40) &&& 1 ∧ s1.regs.r9 = ob &&& idxMask ∧ s1.regs.r10 = nn ∧
      s1.regs.r14 = d.regs.r14 ∧ s1.regs.r15 = d.regs.r15 ∧
      s1.regs.rsp = d.regs.rsp ∧ s1.regs.rbp = d.regs.rbp ∧ s1.dmem = d.dmem)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rs [hrdi, hr8, hr9, hr10, BinOp.eval]
        all_goals rfl)
    fun s1 ⟨g1, g2, g3, g4, g5, g6, g7, g9, g10, g11, g12, g13⟩ => ?_
  have hTA := G.tab.dom64_tierA hdom (oa >>> 40)
  have hTB := G.tab.dom64_tierA hdom (ob >>> 40)
  have hTO := G.tab.dom64_tierA hdom (o >>> 40)
  have heA := hG.end64 _ (G.tab.pos64_lt hTA)
  have heB := hG.end64 _ (G.tab.pos64_lt hTB)
  have heO := hG.end64 _ (G.tab.pos64_lt hTO)
  have hm1 : MemRel G σ.mem s1.dmem := by rw [g13]; exact hmem
  have h15' : s1.regs.r15.toNat = G.T := by rw [g10]; exact h15
  have hdA := pool_desc hm1 hdom (oa >>> 40) (r := .rdx) (by rs [g3]) h15'
  have hdB := pool_desc hm1 hdom (ob >>> 40) (r := .r12) (by rs [g5]) h15'
  have hdO := pool_desc hm1 hdom (o >>> 40) (r := .rcx) (by rs [g1]) h15'
  have hszA := hmem.size64 _ hTA
  have hszB := hmem.size64 _ hTB
  have hszO := hmem.size64 _ hTO
  generalize hSA : G.s (G.tab.pos64 (tierA 0 (oa >>> 40))) = SA at *
  generalize hSB : G.s (G.tab.pos64 (tierA 0 (ob >>> 40))) = SB at *
  generalize hSO : G.s (G.tab.pos64 (tierA 0 (o >>> 40))) = SO at *
  generalize hBA : G.b (G.tab.pos64 (tierA 0 (oa >>> 40))) = BA at *
  generalize hBB : G.b (G.tab.pos64 (tierA 0 (ob >>> 40))) = BB at *
  generalize hBO : G.b (G.tab.pos64 (tierA 0 (o >>> 40))) = BO at *
  have hSAn : (UInt64.ofNat SA).toNat = SA := L.toNat_ofNat_of_lt (by omega)
  have hSBn : (UInt64.ofNat SB).toNat = SB := L.toNat_ofNat_of_lt (by omega)
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
  refine ev_movRMt (b_code hc (i := 16) rfl) hoffL (v := UInt64.ofNat SA) hdA.1 ?_
  refine ev_subRR (b_code hc (i := 17) rfl) fun st hcf => ?_
  rs [g4, hSAn] at hcf
  refine ev_jcc (b_code hc (i := 18) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSAn] at hcc
  refine ev_cmpRO (b_code hc (i := 19) rfl) (v := nn) (Or.inr (Or.inr ⟨.r10, rfl, by rs [g7]⟩)) ?_
  refine ev_jcc (b_code hc (i := 20) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc2 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc2
  rs [g4] at hcc2
  rw [hsub SA _ (by omega) (by omega)] at hcc2
  simp only [UInt64.toNat_toBitVec] at hcc2
  have hqa : (oa &&& idxMask).toNat + nn.toNat ≤ SA := by omega
  refine ev_movRMt (b_code hc (i := 21) rfl) hoffB (v := UInt64.ofNat BA) (by rs; exact hdA.2) ?_
  refine ev_leaX (b_code hc (i := 22) rfl) ?_
  -- the window of `b`
  refine ev_movRMt (b_code hc (i := 23) rfl) hoffL (v := UInt64.ofNat SB) (by rs; exact hdB.1) ?_
  refine ev_subRR (b_code hc (i := 24) rfl) fun st hcf => ?_
  rs [g6, hSBn] at hcf
  refine ev_jcc (b_code hc (i := 25) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc3 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSBn] at hcc3
  refine ev_cmpRO (b_code hc (i := 26) rfl) (v := nn) (Or.inr (Or.inr ⟨.r10, rfl, by rs [g7]⟩)) ?_
  refine ev_jcc (b_code hc (i := 27) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc4 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc4
  rs [g6] at hcc4
  rw [hsub SB _ (by omega) (by omega)] at hcc4
  simp only [UInt64.toNat_toBitVec] at hcc4
  have hqb : (ob &&& idxMask).toNat + nn.toNat ≤ SB := by omega
  refine ev_movRMt (b_code hc (i := 28) rfl) hoffB (v := UInt64.ofNat BB) (by rs; exact hdB.2) ?_
  refine ev_leaX (b_code hc (i := 29) rfl) ?_
  -- the output window
  refine ev_movRMt (b_code hc (i := 30) rfl) hoffL (v := UInt64.ofNat SO) (by rs; exact hdO.1) ?_
  refine ev_subRR (b_code hc (i := 31) rfl) fun st hcf => ?_
  rs [g2, hSOn] at hcf
  refine ev_jcc (b_code hc (i := 32) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc5 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSOn] at hcc5
  refine ev_cmpRO (b_code hc (i := 33) rfl) (v := nn) (Or.inr (Or.inr ⟨.r10, rfl, by rs [g7]⟩)) ?_
  refine ev_jcc (b_code hc (i := 34) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc6 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc6
  rs [g2] at hcc6
  rw [hsub SO _ (by omega) (by omega)] at hcc6
  simp only [UInt64.toNat_toBitVec] at hcc6
  have hoa : (o &&& idxMask).toNat + nn.toNat ≤ SO := by omega
  refine ev_movRMt (b_code hc (i := 35) rfl) hoffB (v := UInt64.ofNat BO) (by rs; exact hdO.2) ?_
  refine ev_leaX (b_code hc (i := 36) rfl) ?_
  -- the fuel
  refine ev_subRR (b_code hc (i := 37) rfl) fun st hcf => ?_
  rs [g7, g9] at hcf
  refine ev_jcc (b_code hc (i := 38) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc7 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec] at hcc7
  refine ev_movRI (b_code hc (i := 39) rfl) ?_
  have hl14 : nn.toNat ≤ d.regs.r14.toNat := by omega
  have hnF : nn.toNat < n := by omega
  have hrun := hspec σ o oa ob nn n hnF (Or.inr ⟨by rw [hszA]; exact hqa, by rw [hszB]; exact hqb,
    by rw [hszO]; exact hoa, by rw [hszA]; omega, by rw [hszB]; omega, by rw [hszO]; omega⟩)
  rw [← hSA] at hqa
  rw [← hSB] at hqb
  rw [← hSO] at hoa
  refine b_loop (d := d) hG hop hc _ _ _ hTA hTB hTO (oa &&& idxMask) (ob &&& idxMask) (o &&& idxMask) nn
    (d.regs.r14 - nn) σ.mem hqa hqb hoa (fun s' fr hm' => hfin _ hrun s' fr hm') nn.toNat _ 0 (by simp)
    ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by have := L.toNat_ne_zero_of_ne _ hnz; simp only [UInt64.toNat_zero]; omega)
  all_goals try rs [g1, g2, g3, g4, g5, g6, g7, g9, g10, g11, g12, g13]
  · show (d.regs.r14 - nn).toNat ≤ _
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hl14)]; omega
  · exact Pres.refl _ _
  · simpa [g0Rows] using hmem
  · apply UInt64.toBitVec_inj.mp
    rw [hBA]
    have := addr_idx BA 0 (oa &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  · apply UInt64.toBitVec_inj.mp
    rw [hBB]
    have := addr_idx BB 0 (ob &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  · apply UInt64.toBitVec_inj.mp
    rw [hBO]
    have := addr_idx BO 0 (o &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  · rfl



/-! ## The copy -/

section
variable [Host] {kf : Nat} {tab : Tab} {f : FnName}

theorem cp_code (hc : Code (copyAsm tab f) kf) {i : Nat} {x : Directive}
    (hi : (copyAsm tab f)[i]? = some x) : Host.prog[kf + i]? = some x := Code.get hc hi

end

section
variable [Host] {G : L.Compiler.Layout} (hG : G.Ok) {kf : Nat} {f : FnName}
  (hc : Code (copyAsm G.tab f) kf) {d : MachineData} {Q : MachineState → Prop}
include hG hc

/-- One step of the copy loop (`.L`) at index `j < n`. -/
theorem cp_step (TA TO : TieredArray) (hTA : G.tab.dom64 TA = true) (hTO : G.tab.dom64 TO = true)
    (qa ob n : Word) (R14 : UInt64) (m0 : Mem)
    (hqa : qa.toNat + n.toNat ≤ G.s (G.tab.pos64 TA)) (hoa : ob.toNat + n.toNat ≤ G.s (G.tab.pos64 TO))
    (s : MachineData) (j : Word) (hF : MrFr G d s)
    (hm : MemRel G (g0Rows (copyStep TA TO qa ob) j.toNat m0 0) s.dmem)
    (hrsi : s.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat))
    (hrdi : s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat))
    (hr13 : s.regs.r13 = j) (hr9 : s.regs.r9 = n) (hr14 : s.regs.r14 = R14) (hj : j.toNat < n.toNat)
    (hnext : ∀ s', MrFr G d s' → MemRel G (g0Rows (copyStep TA TO qa ob) (j + 1).toNat m0 0) s'.dmem →
      s'.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat) →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s'.regs.r13 = j + 1 → s'.regs.r9 = n → s'.regs.r14 = R14 →
      (j + 1).toNat < n.toNat → Ev Q s' (at_ (kf + 29)))
    (hE : ∀ s', MrFr G d s' → MemRel G (g0Rows (copyStep TA TO qa ob) n.toNat m0 0) s'.dmem →
      Ev Q s' (at_ (kf + 35))) :
    Ev Q s (at_ (kf + 29)) := by
  have hpA := G.tab.pos64_lt hTA
  have hpO := G.tab.pos64_lt hTO
  have heA := hG.end64 _ hpA
  have heO := hG.end64 _ hpO
  generalize hMc : g0Rows (copyStep TA TO qa ob) j.toNat m0 0 = M at hm
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
  refine ev_label (cp_code hc (i := 29) rfl) ?_
  refine ev_ldX (cp_code hc (i := 30) rfl) (v := (M.arr64 TA)[(qa + j).toNat]) (by rs; rw [haA]; exact hrA) ?_
  refine ev_stX (cp_code hc (i := 31) rfl) (by rs; rw [haO, hrO]; rfl) ?_
  refine ev_addRI (cp_code hc (i := 32) rfl) fun st2 => ?_
  refine ev_cmpRO (cp_code hc (i := 33) rfl) (v := n) (Or.inr (Or.inr ⟨.r9, rfl, by rs [hr9]⟩)) ?_
  have hj1 : (j + 1).toNat = j.toNat + 1 := L.toNat_add_one_of_lt (by omega)
  have hrow : g0Rows (copyStep TA TO qa ob) (j + 1).toNat m0 0 =
      M.set64 TO (ob + j) (M.arr64 TA)[(qa + j).toNat] := by
    rw [hj1, g0Rows_succ, hMc, UInt64.zero_add, L.ofNat_toNat]
    simp only [copyStep, getElem!_pos, hinA]
  rw [hrow] at hnext
  have hm' := MemRel.store64 hG hm hTO hinO (M.arr64 TA)[(qa + j).toNat]
  rw [hBO] at hm'
  have hpres := hF.pres.trans (Pres.store64 hG (top := d.regs.rsp.toNat) (d := s.dmem) hTO
    (j := (ob + j).toNat) (by omega) (M.arr64 TA)[(qa + j).toNat].toBitVec)
  rw [hBO] at hpres
  have haO' : (UInt64.ofNat (BO + 8 * ob.toNat)).toBitVec + j.toBitVec * 8 = A (BO + 8 * (ob + j).toNat) := by
    have := haO; rw [hrdi, hr13] at this; exact this
  refine ev_jcc (cp_code hc (i := 34) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · refine ev_lbl (Code.label hc (i := 29) rfl) ?_
    refine hnext _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrsi, hrdi, hr13, hr9, hr14]
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
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrsi, hrdi, hr13, hr9, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haO']; exact hpres
    · rw [haO']; exact hm'

/-- The copy loop from `.L`, by induction on the limbs left. -/
theorem cp_loop (TA TO : TieredArray) (hTA : G.tab.dom64 TA = true) (hTO : G.tab.dom64 TO = true)
    (qa ob n : Word) (R14 : UInt64) (m0 : Mem)
    (hqa : qa.toNat + n.toNat ≤ G.s (G.tab.pos64 TA)) (hoa : ob.toNat + n.toNat ≤ G.s (G.tab.pos64 TO))
    (hE : ∀ s', MrFr G d s' → MemRel G (g0Rows (copyStep TA TO qa ob) n.toNat m0 0) s'.dmem →
      Ev Q s' (at_ (kf + 35))) :
    ∀ (r : Nat) (s : MachineData) (j : Word), n.toNat = j.toNat + r → MrFr G d s →
      MemRel G (g0Rows (copyStep TA TO qa ob) j.toNat m0 0) s.dmem →
      s.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat) →
      s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s.regs.r13 = j → s.regs.r9 = n → s.regs.r14 = R14 → j.toNat < n.toNat → Ev Q s (at_ (kf + 29)) := by
  intro r
  induction r with
  | zero => intro s j hr _ _ _ _ _ _ _ hj; omega
  | succ r ih =>
    intro s j hr hF hm h1 h3 h4 h5 h6 hj
    refine cp_step hG hc TA TO hTA hTO qa ob n R14 m0 hqa hoa s j hF hm h1 h3 h4 h5 h6 hj ?_ hE
    intro s' g1 g2 g3 g4 g5 g6 g7 g8
    have := n.toNat_lt
    exact ih s' (j + 1) (by rw [L.toNat_add_one_of_lt (by omega)]; omega) g1 g2 g3 g4 g5 g6 g7 g8

/-- The copy's `.Z`: the result `0`, the return. -/
theorem cp_exit {ra : Word} (hra : rdW d.dmem (A d.regs.rsp.toNat) = some ra) (hlo : G.lo ≤ d.regs.rsp.toNat)
    (hhi : d.regs.rsp.toNat + 8 ≤ G.hi) (s : MachineData) (hF : MrFr G d s)
    (hok : ∀ s', s'.dmem = s.dmem → s'.regs.rsp.toNat = d.regs.rsp.toNat + 8 →
      s'.regs.rbp = d.regs.rbp → s'.regs.r15 = d.regs.r15 → s'.regs.r14.toNat ≤ d.regs.r14.toNat →
      s'.regs.rax = 0 → Ev Q s' (Int64.ofBitVec ra.toBitVec)) :
    Ev Q s (at_ (kf + 35)) := by
  refine ev_label (cp_code hc (i := 35) rfl) ?_
  refine ev_movRI (cp_code hc (i := 36) rfl) ?_
  refine frame_ret hG hra hlo hhi ⟨?_, ?_, ?_, ?_, ?_⟩ (cp_code hc (i := 37) rfl) fun s' e1 e2 e3 e4 e5 e6 => ?_
  all_goals try rs [hF.rsp, hF.rbp, hF.r15]
  · exact hF.r14
  · exact hF.pres
  · exact hok s' e1 e2 e3 e4 (by rw [e5]; rs; exact hF.r14) (by rw [e6]; rs)

end

/-- **The copy template meets the compiler's per-function contract**, for any L function `f` with
three parameters and one result whose run is the model (`CopySpec`). -/
theorem copyAsm_sim [Host] (p : Prog) (G : L.Compiler.Layout) (hG : G.Ok) (f : FnName)
    (fd : FunDecl) (hspec : CopySpec p f) (hnp : fd.nparams = 3) (hnr : Stmt.nret fd.body = 1)
    (hdom : G.tab.dom64 (tier1 0) = true)
    (hoffL : SmallOff (G.tab.len64 (0 : ArrId))) (hoffB : SmallOff (G.tab.base64 (0 : ArrId)))
    (kf : Nat) (hc : Code (copyAsm G.tab f) kf) (sk : NTree) (n : Nat) :
    FnSimAt p G sk n f fd kf := by
  intro vs σ d ra Q hlen hra hargs hlo8 hhi h15 hmem h14 hok herr habrt hexh
  have hlo : G.lo ≤ d.regs.rsp.toNat := by omega
  rw [hnp] at hlen
  obtain ⟨o, oa, nn, rfl⟩ : ∃ o oa nn, vs = [o, oa, nn] := by
    match vs, hlen with
    | [o, oa, nn], _ => exact ⟨o, oa, nn, rfl⟩
  have hA := hargs.1 (by simp [argRegs])
  have hrdi : d.regs.rdi = o := UInt64.toBitVec_inj.mp (hA 0 (by simp))
  have hr8 : d.regs.r8 = oa := UInt64.toBitVec_inj.mp (hA 1 (by simp))
  have hr9 : d.regs.r9 = nn := UInt64.toBitVec_inj.mp (hA 2 (by simp))
  have hn0 : 0 < n := by omega
  have hh := hG.hi_le
  have hfin : ∀ (M : Mem), (invoke p (exec p n) f [o, oa, nn]).run σ = .ok ([0], { σ with mem := M }) →
      ∀ s, MrFr G d s → MemRel G M s.dmem → Ev Q s (at_ (kf + 35)) := by
    intro M hrun s hF hm
    refine cp_exit hG hc hra hlo hhi s hF fun s' e1 e2 e3 e4 e5 e6 => ?_
    refine hok _ _ s' hrun (by rw [e1]; exact hm) rfl e2 e3 e4 e5 ?_ (by rw [e1]; exact hF.pres)
    rw [hnr]; exact resOut_zero' e6
  refine ev_label (cp_code hc (i := 0) rfl) ?_
  refine ev_cmpRO (cp_code hc (i := 1) rfl) (v := 0) (Or.inl rfl) ?_
  refine ev_jcc (cp_code hc (i := 2) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · simp only [CondCode.interp, cmpFlags_zf, beq_iff_eq] at hcc
    rs [hr9] at hcc
    have hn0' : nn = 0 := UInt64.toBitVec_inj.mp hcc
    subst hn0'
    have hrun := hspec σ o oa 0 n (by simp; omega) (Or.inl rfl)
    simp only [UInt64.toNat_zero, g0Rows] at hrun
    refine ev_lbl (Code.label hc (i := 35) rfl) ?_
    exact hfin σ.mem hrun _ ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.refl _ _⟩ hmem
  simp only [CondCode.interp, cmpFlags_zf, beq_eq_false_iff_ne] at hcc
  rs [hr9] at hcc
  have hnz : nn ≠ 0 := fun h => hcc (by rw [h])
  refine ev_movRI (cp_code hc (i := 3) rfl) ?_
  refine ev_movRR (cp_code hc (i := 4) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (cp_code hc (i := 5) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (cp_code hc (i := 6) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (cp_code hc (i := 7) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_movRR (cp_code hc (i := 8) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (cp_code hc (i := 9) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (cp_code hc (i := 10) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (cp_code hc (i := 11) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_gen (fun s1 => s1.regs.rcx = (o >>> 40) &&& 1 ∧ s1.regs.rdi = o &&& idxMask ∧
      s1.regs.rdx = (oa >>> 40) &&& 1 ∧ s1.regs.r8 = oa &&& idxMask ∧ s1.regs.r9 = nn ∧
      s1.regs.r14 = d.regs.r14 ∧ s1.regs.r15 = d.regs.r15 ∧
      s1.regs.rsp = d.regs.rsp ∧ s1.regs.rbp = d.regs.rbp ∧ s1.dmem = d.dmem)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rs [hrdi, hr8, hr9, BinOp.eval]
        all_goals rfl)
    fun s1 ⟨g1, g2, g3, g4, g7, g9, g10, g11, g12, g13⟩ => ?_
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
  refine ev_movRMt (cp_code hc (i := 12) rfl) hoffL (v := UInt64.ofNat SA) hdA.1 ?_
  refine ev_subRR (cp_code hc (i := 13) rfl) fun st hcf => ?_
  rs [g4, hSAn] at hcf
  refine ev_jcc (cp_code hc (i := 14) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSAn] at hcc
  refine ev_cmpRO (cp_code hc (i := 15) rfl) (v := nn) (Or.inr (Or.inr ⟨.r9, rfl, by rs [g7]⟩)) ?_
  refine ev_jcc (cp_code hc (i := 16) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc2 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc2
  rs [g4] at hcc2
  rw [hsub SA _ (by omega) (by omega)] at hcc2
  simp only [UInt64.toNat_toBitVec] at hcc2
  have hqa : (oa &&& idxMask).toNat + nn.toNat ≤ SA := by omega
  refine ev_movRMt (cp_code hc (i := 17) rfl) hoffB (v := UInt64.ofNat BA) (by rs; exact hdA.2) ?_
  refine ev_leaX (cp_code hc (i := 18) rfl) ?_
  -- the output window
  refine ev_movRMt (cp_code hc (i := 19) rfl) hoffL (v := UInt64.ofNat SO) (by rs; exact hdO.1) ?_
  refine ev_subRR (cp_code hc (i := 20) rfl) fun st hcf => ?_
  rs [g2, hSOn] at hcf
  refine ev_jcc (cp_code hc (i := 21) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc5 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSOn] at hcc5
  refine ev_cmpRO (cp_code hc (i := 22) rfl) (v := nn) (Or.inr (Or.inr ⟨.r9, rfl, by rs [g7]⟩)) ?_
  refine ev_jcc (cp_code hc (i := 23) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc6 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc6
  rs [g2] at hcc6
  rw [hsub SO _ (by omega) (by omega)] at hcc6
  simp only [UInt64.toNat_toBitVec] at hcc6
  have hoa : (o &&& idxMask).toNat + nn.toNat ≤ SO := by omega
  refine ev_movRMt (cp_code hc (i := 24) rfl) hoffB (v := UInt64.ofNat BO) (by rs; exact hdO.2) ?_
  refine ev_leaX (cp_code hc (i := 25) rfl) ?_
  -- the fuel
  refine ev_subRR (cp_code hc (i := 26) rfl) fun st hcf => ?_
  rs [g7, g9] at hcf
  refine ev_jcc (cp_code hc (i := 27) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc7 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec] at hcc7
  refine ev_movRI (cp_code hc (i := 28) rfl) ?_
  have hl14 : nn.toNat ≤ d.regs.r14.toNat := by omega
  have hnF : nn.toNat < n := by omega
  have hrun := hspec σ o oa nn n hnF (Or.inr ⟨by rw [hszA]; exact hqa, by rw [hszO]; exact hoa,
    by rw [hszA]; omega, by rw [hszO]; omega⟩)
  rw [← hSA] at hqa
  rw [← hSO] at hoa
  refine cp_loop (d := d) hG hc _ _ hTA hTO (oa &&& idxMask) (o &&& idxMask) nn
    (d.regs.r14 - nn) σ.mem hqa hoa (fun s' fr hm' => hfin _ hrun s' fr hm') nn.toNat _ 0 (by simp)
    ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_
    (by have := L.toNat_ne_zero_of_ne _ hnz; simp only [UInt64.toNat_zero]; omega)
  all_goals try rs [g1, g2, g3, g4, g7, g9, g10, g11, g12, g13]
  · show (d.regs.r14 - nn).toNat ≤ _
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hl14)]; omega
  · exact Pres.refl _ _
  · simpa [g0Rows] using hmem
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
  · rfl

end L.AsmEsc
