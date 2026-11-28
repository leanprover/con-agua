module

public import ConAguaX86.AsmEsc.Chain2
public import ConAguaX86.AsmEsc.NatMadL
import Kraken.X64.Registers

@[expose] public section

/-!
# Hand-written `nat_mad` and its simulation contract

`natMadAsm tab` is a hand-written body for `nat_mad(o, n, w, y)` (`L.Front.natMad`, the decimal
reader's multiply-add): `R := R · w + y` in place on the `n` limbs at `o`, returning the carry.
`n = 0` returns `y` at once. Otherwise, up front: the window inside its tier and below `2^40` (so
that the tagged address `o + i` keeps `o`'s tier, as L's per-limb decode reads it) and fuel for the
row, else `ca_exhausted`. The row is 9 instructions per limb: load, `mul`, `add`/`adc` of the carry,
store. `natMadAsm_sim` proves the per-function contract (`FnSimAt`) against `natMad_run`
(`NatMadL.lean`).

Registers: `rdi o`, `r8 n`, `r9 w`, `r10 y` (the carry); in the row `rdi` the address of `R[0]`,
`r13` the index, `rcx` zero.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler L.Front

/-- A local label of the hand-written `nat_mad`. -/
abbrev nmL (m : String) : Label := ".Lasm_nat_mad_" ++ m

/-- The hand-written `nat_mad`, for the table `tab` (the descriptor offsets of `POOL` = 0). -/
def natMadAsm (tab : Tab) : Program :=
  [ .label (fnL "nat_mad"),                                            -- 0
    i64 (.cmp (.reg (rr .r8)) (.imm (.int64 (0 : Word).toInt64))),     -- 1
    jccL .z (nmL "Z"),                                                 -- 2  n = 0
    movRI .rax idxMask,                                                -- 3
    movRR .rcx .rdi,                                                   -- 4
    i64 (.shr (.reg (rr .rcx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 5
    i64 (.and (.reg (rr .rcx)) (.imm (.int64 (1 : Word).toInt64))),    -- 6  tier bit
    i64 (.and (.reg (rr .rdi)) (oR .rax)),                             -- 7  ob
    movRR .r11 .rax,                                                   -- 8
    i64 (.sub (.reg (rr .r11)) (oR .rdi)),                             -- 9
    i64 (.cmp (.reg (rr .r11)) (oR .r8)),                              -- 10
    jccL .c exhaustedL,                                                -- 11 ob + n ≥ 2^40
    movRM .rax (tdesc .rcx (tab.len64 (0 : ArrId))),                   -- 12
    i64 (.sub (.reg (rr .rax)) (oR .rdi)),                             -- 13
    jccL .c exhaustedL,                                                -- 14
    i64 (.cmp (.reg (rr .rax)) (oR .r8)),                              -- 15
    jccL .c exhaustedL,                                                -- 16 len - ob < n
    movRM .rcx (tdesc .rcx (tab.base64 (0 : ArrId))),                  -- 17
    i64 (.lea (rr .rdi) (mbi .rcx .rdi .W64)),                         -- 18 rdi := &R[0]
    i64 (.sub (.reg (rr .r14)) (oR .r8)),                              -- 19
    jccL .c exhaustedL,                                                -- 20 fuel < n
    movRI .r13 0,                                                      -- 21 i := 0
    movRI .rcx 0,                                                      -- 22
    .label (nmL "L"),                                                  -- 23
    movRM .rax (mbi .rdi .r13 .W64),                                   -- 24 x
    i64 (.mul (.reg (rr .r9))),                                        -- 25 rdx:rax := x * w
    i64 (.add (.reg (rr .rax)) (oR .r10)),                             -- 26 lo := + y
    i64 (.adc (.reg (rr .rdx)) (oR .rcx)),                             -- 27
    movMR (mbi .rdi .r13 .W64) .rax,                                   -- 28
    movRR .r10 .rdx,                                                   -- 29 y := the carry
    i64 (.add (.reg (rr .r13)) (oI 1)),                                -- 30
    i64 (.cmp (.reg (rr .r13)) (oR .r8)),                              -- 31
    jccL .c (nmL "L"),                                                 -- 32
    .label (nmL "Z"),                                                  -- 33
    movRR .rax .r10,                                                   -- 34
    i64 .ret ]                                                         -- 35

section
variable [Host] {kf : Nat} {tab : Tab}

theorem nm_code (hc : Code (natMadAsm tab) kf) {i : Nat} {x : Directive}
    (hi : (natMadAsm tab)[i]? = some x) : Host.prog[kf + i]? = some x := Code.get hc hi

end

section
variable [Host] {G : L.Compiler.Layout} (hG : G.Ok) {kf : Nat} (hc : Code (natMadAsm G.tab) kf)
  {d : MachineData} {Q : MachineState → Prop}
include hG hc

/-- One step of the row (`.L`), at index `j < n`: the next step (`hnext`) or, after the last,
`.Z` (`hT`). -/
theorem nm_row_step (TR : TieredArray) (hTR : G.tab.dom64 TR = true)
    (rb w n : Word) (R14 : UInt64) (m0 : Mem) (y0 : Word)
    (hqa : rb.toNat + n.toNat ≤ G.s (G.tab.pos64 TR))
    (s : MachineData) (j : Word) (hF : MrFr G d s)
    (hm : MemRel G (nmRows TR rb w j.toNat m0 0 y0).1 s.dmem)
    (hrdi : s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TR) + 8 * rb.toNat))
    (hr8 : s.regs.r8 = n) (hr9 : s.regs.r9 = w) (hr13 : s.regs.r13 = j)
    (hr10 : s.regs.r10 = (nmRows TR rb w j.toNat m0 0 y0).2) (hrcx : s.regs.rcx = 0)
    (hr14 : s.regs.r14 = R14) (hj : j.toNat < n.toNat)
    (hnext : ∀ s', MrFr G d s' → MemRel G (nmRows TR rb w (j + 1).toNat m0 0 y0).1 s'.dmem →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TR) + 8 * rb.toNat) →
      s'.regs.r8 = n → s'.regs.r9 = w → s'.regs.r13 = j + 1 →
      s'.regs.r10 = (nmRows TR rb w (j + 1).toNat m0 0 y0).2 → s'.regs.rcx = 0 →
      s'.regs.r14 = R14 → (j + 1).toNat < n.toNat → Ev Q s' (at_ (kf + 23)))
    (hT : ∀ s', MrFr G d s' → MemRel G (nmRows TR rb w n.toNat m0 0 y0).1 s'.dmem →
      s'.regs.r10 = (nmRows TR rb w n.toNat m0 0 y0).2 → Ev Q s' (at_ (kf + 33))) :
    Ev Q s (at_ (kf + 23)) := by
  have hpA := G.tab.pos64_lt hTR
  have heA := hG.end64 _ hpA
  generalize hMc : nmRows TR rb w j.toNat m0 0 y0 = Mc at hm hr10
  obtain ⟨M, c⟩ := Mc
  simp only at hm hr10
  have hszA := hm.size64 TR hTR
  generalize hBA : G.b (G.tab.pos64 TR) = BA at *
  have hqj : (rb + j).toNat = rb.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hinA : (rb + j).toNat < (M.arr64 TR).size := by rw [hqj, hszA]; omega
  have haA : s.regs.rdi.toBitVec + s.regs.r13.toBitVec * 8 = A (BA + 8 * (rb + j).toNat) := by
    rw [hrdi, hr13, addr_idx BA rb.toNat j (by omega), hqj]
  have hrA : rdW s.dmem (A (BA + 8 * (rb + j).toNat)) = some (M.arr64 TR)[(rb + j).toNat] := by
    have := hm.get64 TR hTR (rb + j).toNat hinA; rw [hBA] at this; exact this
  refine ev_label (nm_code hc (i := 23) rfl) ?_
  refine ev_ldX (nm_code hc (i := 24) rfl) (v := (M.arr64 TR)[(rb + j).toNat]) (by rs; rw [haA]; exact hrA) ?_
  refine ev_mulR (nm_code hc (i := 25) rfl) fun st1 => ?_
  refine ev_addRR (nm_code hc (i := 26) rfl) fun st2 hcf2 => ?_
  refine ev_adcRR (nm_code hc (i := 27) rfl) fun st3 => ?_
  refine ev_stX (nm_code hc (i := 28) rfl) (by rs; rw [haA, hrA]; rfl) ?_
  refine ev_movRR (nm_code hc (i := 29) rfl) ?_
  refine ev_addRI (nm_code hc (i := 30) rfl) fun st6 => ?_
  refine ev_cmpRO (nm_code hc (i := 31) rfl) (v := n) (Or.inr (Or.inr ⟨.r8, rfl, by rs [hr8]⟩)) ?_
  have hj1 : (j + 1).toNat = j.toNat + 1 := L.toNat_add_one_of_lt (by omega)
  have hrow : nmRows TR rb w (j + 1).toNat m0 0 y0 = nmStep TR rb w M j c := by
    rw [hj1, nmRows_succ, hMc, UInt64.zero_add, L.ofNat_toNat]
  have hstep : nmStep TR rb w M j c =
      (M.set64 TR (rb + j) ((M.arr64 TR)[(rb + j).toNat] * w + c),
       BinOp.mulhi.eval (M.arr64 TR)[(rb + j).toNat] w +
         Cmp.evalW .ult ((M.arr64 TR)[(rb + j).toNat] * w + c) c) := by
    simp only [nmStep, getElem!_pos, hinA]
  rw [hrow, hstep] at hnext
  have hm' := MemRel.store64 hG hm hTR hinA ((M.arr64 TR)[(rb + j).toNat] * w + c)
  rw [hBA] at hm'
  have hpres := hF.pres.trans (Pres.store64 hG (top := d.regs.rsp.toNat) (d := s.dmem) hTR
    (j := (rb + j).toNat) (by omega) ((M.arr64 TR)[(rb + j).toNat] * w + c).toBitVec)
  rw [hBA] at hpres
  rs [hr9, hr10, hr13, hrcx] at hcf2
  have haA' : (UInt64.ofNat (BA + 8 * rb.toNat)).toBitVec + j.toBitVec * 8 = A (BA + 8 * (rb + j).toNat) := by
    have := haA; rw [hrdi, hr13] at this; exact this
  have hval : ((M.arr64 TR)[(rb + j).toNat] * w).toBitVec + c.toBitVec =
      ((M.arr64 TR)[(rb + j).toNat] * w + c).toBitVec := rfl
  refine ev_jcc (nm_code hc (i := 32) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · refine ev_lbl (Code.label hc (i := 23) rfl) ?_
    refine hnext _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrdi, hr8, hr9, hr10, hr13, hrcx, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haA', hval]; exact hpres
    · rw [haA', hval]; exact hm'
    · rfl
    · rw [hcf2]
      exact adc_word _ _ _
    · simp only [CondCode.interp, cmpFlags_cf, decide_eq_true_eq] at hcc
      rs [hr13] at hcc
      exact hcc
    all_goals done
  · simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc
    rs [hr13] at hcc
    have e1 : (j + 1).toNat = (j.toBitVec + (Int64.ofInt 1).toBitVec).toNat := rfl
    have e2 : n.toNat = n.toBitVec.toNat := rfl
    have hla : j + 1 = n := UInt64.toNat_inj.mp (by omega)
    rw [← hla] at hT
    rw [hrow, hstep] at hT
    refine hT _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrdi, hr8, hr9, hr10, hr13, hrcx, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haA', hval]; exact hpres
    · rw [haA', hval]; exact hm'
    · rw [hcf2]
      exact adc_word _ _ _
    all_goals done

/-- The row from `.L`, by induction on the steps left. -/
theorem nm_row (TR : TieredArray) (hTR : G.tab.dom64 TR = true)
    (rb w n : Word) (R14 : UInt64) (m0 : Mem) (y0 : Word)
    (hqa : rb.toNat + n.toNat ≤ G.s (G.tab.pos64 TR))
    (hT : ∀ s', MrFr G d s' → MemRel G (nmRows TR rb w n.toNat m0 0 y0).1 s'.dmem →
      s'.regs.r10 = (nmRows TR rb w n.toNat m0 0 y0).2 → Ev Q s' (at_ (kf + 33))) :
    ∀ (r : Nat) (s : MachineData) (j : Word), n.toNat = j.toNat + r → MrFr G d s →
      MemRel G (nmRows TR rb w j.toNat m0 0 y0).1 s.dmem →
      s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TR) + 8 * rb.toNat) →
      s.regs.r8 = n → s.regs.r9 = w → s.regs.r13 = j →
      s.regs.r10 = (nmRows TR rb w j.toNat m0 0 y0).2 → s.regs.rcx = 0 →
      s.regs.r14 = R14 → j.toNat < n.toNat → Ev Q s (at_ (kf + 23)) := by
  intro r
  induction r with
  | zero => intro s j hr _ _ _ _ _ _ _ _ _ hj; omega
  | succ r ih =>
    intro s j hr hF hm h1 h2 h3 h4 h5 h6 h7 hj
    refine nm_row_step hG hc TR hTR rb w n R14 m0 y0 hqa s j hF hm h1 h2 h3 h4 h5 h6 h7 hj ?_ hT
    intro s' g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
    have := n.toNat_lt
    exact ih s' (j + 1) (by rw [L.toNat_add_one_of_lt (by omega)]; omega) g1 g2 g3 g4 g5 g6 g7 g8 g9 g10

/-- `.Z`: the carry, the return. -/
theorem nm_tail {ra : Word} (hra : rdW d.dmem (A d.regs.rsp.toNat) = some ra) (hlo : G.lo ≤ d.regs.rsp.toNat)
    (hhi : d.regs.rsp.toNat + 8 ≤ G.hi) (s : MachineData) (M : Mem) (c : Word) (hF : MrFr G d s)
    (hm : MemRel G M s.dmem) (hr10 : s.regs.r10 = c)
    (hok : ∀ s', MemRel G M s'.dmem → s'.regs.rsp.toNat = d.regs.rsp.toNat + 8 →
      s'.regs.rbp = d.regs.rbp → s'.regs.r15 = d.regs.r15 → s'.regs.r14.toNat ≤ d.regs.r14.toNat →
      s'.regs.rax = c → Pres G d.regs.rsp.toNat d.dmem s'.dmem → Ev Q s' (Int64.ofBitVec ra.toBitVec)) :
    Ev Q s (at_ (kf + 33)) := by
  refine ev_label (nm_code hc (i := 33) rfl) ?_
  refine ev_movRR (nm_code hc (i := 34) rfl) ?_
  refine frame_ret hG hra hlo hhi ⟨?_, ?_, ?_, ?_, ?_⟩ (nm_code hc (i := 35) rfl) fun s' e1 e2 e3 e4 e5 e6 => ?_
  all_goals try rs [hF.rsp, hF.rbp, hF.r15]
  · exact hF.r14
  · exact hF.pres
  · refine hok s' (by rw [e1]; exact hm) e2 e3 e4 (by rw [e5]; rs; exact hF.r14) (by rw [e6]; rs [hr10])
      (by rw [e1]; exact hF.pres)

end

/-- **The hand-written `nat_mad` meets the compiler's per-function contract**, for any table in
which `POOL` (0) is a tiered word array with small descriptor offsets, at every fuel. -/
theorem natMadAsm_sim [Host] (p : Prog) (G : L.Compiler.Layout) (hG : G.Ok)
    (hp : p.lookup "nat_mad" = some natMad) (hdom : G.tab.dom64 (tier1 0) = true)
    (hoffL : SmallOff (G.tab.len64 (0 : ArrId))) (hoffB : SmallOff (G.tab.base64 (0 : ArrId)))
    (kf : Nat) (hc : Code (natMadAsm G.tab) kf) (sk : NTree) (n : Nat) :
    FnSimAt p G sk n "nat_mad" natMad kf := by
  intro vs σ d ra Q hlen hra hargs hlo8 hhi h15 hmem h14 hok herr habrt hexh
  have hlo : G.lo ≤ d.regs.rsp.toNat := by omega
  rw [natMad_nparams] at hlen
  obtain ⟨o, nn, w, y, rfl⟩ : ∃ o nn w y, vs = [o, nn, w, y] := by
    match vs, hlen with
    | [o, nn, w, y], _ => exact ⟨o, nn, w, y, rfl⟩
  have hA := hargs.1 (by simp [argRegs])
  have hrdi : d.regs.rdi = o := UInt64.toBitVec_inj.mp (hA 0 (by simp))
  have hr8 : d.regs.r8 = nn := UInt64.toBitVec_inj.mp (hA 1 (by simp))
  have hr9 : d.regs.r9 = w := UInt64.toBitVec_inj.mp (hA 2 (by simp))
  have hr10 : d.regs.r10 = y := UInt64.toBitVec_inj.mp (hA 3 (by simp))
  have hh := hG.hi_le
  have hnr : Stmt.nret natMad.body = 1 := by rw [natMad_body]; rfl
  have hfin : ∀ (M : Mem) (c : Word), (invoke p (exec p n) "nat_mad" [o, nn, w, y]).run σ =
      .ok ([c], { σ with mem := M }) → ∀ s, MrFr G d s → MemRel G M s.dmem → s.regs.r10 = c →
      Ev Q s (at_ (kf + 33)) := by
    intro M c hrun s hF hm hc10
    refine nm_tail hG hc hra hlo hhi s M c hF hm hc10 fun s' e1 e2 e3 e4 e5 e6 e7 => ?_
    refine hok _ _ s' hrun e1 rfl e2 e3 e4 e5 ?_ e7
    rw [hnr]; exact resOut_zero' e6
  refine ev_label (nm_code hc (i := 0) rfl) ?_
  refine ev_cmpRO (nm_code hc (i := 1) rfl) (v := 0) (Or.inl rfl) ?_
  refine ev_jcc (nm_code hc (i := 2) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · simp only [CondCode.interp, cmpFlags_zf, beq_iff_eq] at hcc
    rs [hr8] at hcc
    have hn0 : nn = 0 := UInt64.toBitVec_inj.mp hcc
    subst hn0
    have hrun := natMad_run p hp σ o 0 w y n (by simp; omega) (Or.inl rfl)
    simp only [UInt64.toNat_zero, nmRows] at hrun
    refine ev_lbl (Code.label hc (i := 33) rfl) ?_
    refine hfin σ.mem y (by rw [hrun]) _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_
    all_goals try rs [hr10]
    · exact Nat.le_refl _
    · exact Pres.refl _ _
    · exact hmem
  simp only [CondCode.interp, cmpFlags_zf, beq_eq_false_iff_ne] at hcc
  rs [hr8] at hcc
  have hnz : nn ≠ 0 := fun h => hcc (by rw [h])
  refine ev_movRI (nm_code hc (i := 3) rfl) ?_
  refine ev_movRR (nm_code hc (i := 4) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (nm_code hc (i := 5) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (nm_code hc (i := 6) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (nm_code hc (i := 7) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_gen (fun s1 => s1.regs.rcx = (o >>> 40) &&& 1 ∧ s1.regs.rdi = o &&& idxMask ∧
      s1.regs.rax = idxMask ∧ s1.regs.r8 = nn ∧ s1.regs.r9 = w ∧ s1.regs.r10 = y ∧
      s1.regs.r14 = d.regs.r14 ∧ s1.regs.r15 = d.regs.r15 ∧
      s1.regs.rsp = d.regs.rsp ∧ s1.regs.rbp = d.regs.rbp ∧ s1.dmem = d.dmem)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rs [hrdi, hr8, hr9, hr10, BinOp.eval]
        all_goals rfl)
    fun s1 ⟨g1, g2, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ => ?_
  have hTR := G.tab.dom64_tierA hdom (o >>> 40)
  have heA := hG.end64 _ (G.tab.pos64_lt hTR)
  have hm1 : MemRel G σ.mem s1.dmem := by rw [g13]; exact hmem
  have h15' : s1.regs.r15.toNat = G.T := by rw [g10]; exact h15
  have hdA := pool_desc hm1 hdom (o >>> 40) (r := .rcx) (by rs [g1]) h15'
  have hszA := hmem.size64 _ hTR
  generalize hSA : G.s (G.tab.pos64 (tierA 0 (o >>> 40))) = SA at *
  generalize hBA : G.b (G.tab.pos64 (tierA 0 (o >>> 40))) = BA at *
  have hSAn : (UInt64.ofNat SA).toNat = SA := L.toNat_ofNat_of_lt (by omega)
  have hsub : ∀ (S : Nat) (w : Word), S < 2 ^ 64 → w.toNat ≤ S →
      ((UInt64.ofNat S).toBitVec - w.toBitVec).toNat = S - w.toNat := by
    intro S w h1 h2
    rw [BitVec.toNat_sub, UInt64.toNat_toBitVec, show (UInt64.ofNat S).toBitVec.toNat = S from
      L.toNat_ofNat_of_lt h1]
    have := w.toNat_lt; omega
  have hrb : (o &&& idxMask).toNat < 2 ^ 40 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hmask : (idxMask : Word).toNat = 2 ^ 40 - 1 := rfl
  have hX : ∀ s', s'.regs.rbp = d.regs.rbp → s'.dmem = s1.dmem → Ev Q s' (label exhaustedL) :=
    fun s' e1 e2 => hexh _ ⟨e1, by rw [e2, g13]; exact Pres.refl _ _⟩
  -- the indices stay below `2^40`
  refine ev_movRR (nm_code hc (i := 8) rfl) ?_
  refine ev_subRR (nm_code hc (i := 9) rfl) fun _ _ => ?_
  refine ev_cmpRO (nm_code hc (i := 10) rfl) (v := nn) (Or.inr (Or.inr ⟨.r8, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (nm_code hc (i := 11) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc1 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc1
  rs [g2, g5] at hcc1
  rw [BitVec.toNat_sub] at hcc1
  simp only [UInt64.toNat_toBitVec, hmask] at hcc1
  have hr40 : (o &&& idxMask).toNat + nn.toNat < 2 ^ 40 := by omega
  -- the window
  refine ev_movRMt (nm_code hc (i := 12) rfl) hoffL (v := UInt64.ofNat SA) (by rs; exact hdA.1) ?_
  refine ev_subRR (nm_code hc (i := 13) rfl) fun st hcf => ?_
  rs [g2, hSAn] at hcf
  refine ev_jcc (nm_code hc (i := 14) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc3 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSAn] at hcc3
  refine ev_cmpRO (nm_code hc (i := 15) rfl) (v := nn) (Or.inr (Or.inr ⟨.r8, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (nm_code hc (i := 16) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc4 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc4
  rs [g2] at hcc4
  rw [hsub SA _ (by omega) (by omega)] at hcc4
  simp only [UInt64.toNat_toBitVec] at hcc4
  have hqa : (o &&& idxMask).toNat + nn.toNat ≤ SA := by omega
  refine ev_movRMt (nm_code hc (i := 17) rfl) hoffB (v := UInt64.ofNat BA) (by rs; exact hdA.2) ?_
  refine ev_leaX (nm_code hc (i := 18) rfl) ?_
  -- the fuel
  refine ev_subRR (nm_code hc (i := 19) rfl) fun st hcf => ?_
  rs [g6, g9] at hcf
  refine ev_jcc (nm_code hc (i := 20) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc7 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec] at hcc7
  refine ev_movRI (nm_code hc (i := 21) rfl) ?_
  refine ev_movRI (nm_code hc (i := 22) rfl) ?_
  have hl14 : nn.toNat ≤ d.regs.r14.toNat := by omega
  have hnF : nn.toNat < n := by omega
  have hrun := natMad_run p hp σ o nn w y n hnF (Or.inr ⟨hr40, by rw [hszA]; exact hqa⟩)
  simp only [] at hrun
  rw [← hSA] at hqa
  have hrdi0 : (UInt64.ofNat BA).toBitVec + (o &&& idxMask).toBitVec * 8 =
      (UInt64.ofNat (BA + 8 * (o &&& idxMask).toNat)).toBitVec := by
    have := addr_idx BA 0 (o &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  refine nm_row (d := d) hG hc _ hTR (o &&& idxMask) w nn (d.regs.r14 - nn) σ.mem y (by omega)
    (fun s' fr hm' h10 => hfin _ _ hrun s' fr hm' h10) nn.toNat _ 0 (by simp) ⟨?_, ?_, ?_, ?_, ?_⟩
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by have := L.toNat_ne_zero_of_ne _ hnz; simp only [UInt64.toNat_zero]; omega)
  all_goals try rs [g1, g2, g5, g6, g7, g8, g9, g10, g11, g12, g13]
  · show (d.regs.r14 - nn).toNat ≤ _; rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hl14)]; omega
  · exact Pres.refl _ _
  · simpa [nmRows] using hmem
  · apply UInt64.toBitVec_inj.mp; rw [hBA]; exact hrdi0
  · simp [nmRows]
  · rfl

end L.AsmEsc
