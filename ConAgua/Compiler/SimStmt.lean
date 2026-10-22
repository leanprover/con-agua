module

public import ConAgua.Compiler.RunEq

@[expose] public section

/-!
# Statements

`SimS p G run P s`: from any state related to `σ` (with the fuel counter satisfying `P`), the
code of `s` reaches the exit that `run s σ` names: the end of the code (normal), the `break`
target, the return label (with the results in the result registers), `ca_error` (an error other than running out
of fuel), or `ca_exhausted` (always allowed). The exits are continuations (`Conts`).
-/

namespace L.Compiler

open L

attribute [local simp] Reg64s.set64_rax Reg64s.set64_rcx Reg64s.set64_rdx Reg64s.set64_rsi
  Reg64s.set64_rsp Reg64s.set64_r14

/-- `d'` has every byte of `d`, and the same bytes outside the stack below `top`, outside the
arrays, the result area and the global variables. -/
structure Pres (G : Layout) (top : Nat) (d d' : DataMem) : Prop where
  grows : ∀ y, (d.get? y).isSome → (d'.get? y).isSome
  same : ∀ x < 2 ^ 64, ¬ (G.lo ≤ x ∧ x < top) → ¬ G.InArr x → ¬ G.InRes x → ¬ G.InGlob x →
    d'.get? (A x) = d.get? (A x)

namespace Pres
variable {G : Layout}

theorem refl (top : Nat) (d : DataMem) : Pres G top d d := ⟨fun _ h => h, fun _ _ _ _ _ _ => rfl⟩

theorem trans {top : Nat} {d d' d'' : DataMem} (h : Pres G top d d') (h' : Pres G top d' d'') :
    Pres G top d d'' :=
  ⟨fun y hy => h'.grows y (h.grows y hy), fun x hx h1 h2 h3 h4 => by
    rw [h'.same x hx h1 h2 h3 h4, h.same x hx h1 h2 h3 h4]⟩

theorem mono {top top' : Nat} {d d' : DataMem} (h : Pres G top d d') (ht : top ≤ top') :
    Pres G top' d d' :=
  ⟨h.grows, fun x hx h1 h2 h3 h4 => h.same x hx (fun ⟨a, b⟩ => h1 ⟨a, by omega⟩) h2 h3 h4⟩

theorem of_only {a b top : Nat} {d d' : DataMem} (h : Only a b d d') (ha : G.lo ≤ a) (hb : b ≤ top) :
    Pres G top d d' :=
  ⟨h.grows, fun x hx h1 _ _ _ => h.same x hx (by omega)⟩

/-- A change inside the result area. -/
theorem of_res {a b top : Nat} {d d' : DataMem} (h : Only a b d d') (hab : ∀ x, a ≤ x → x < b → G.InRes x) :
    Pres G top d d' :=
  ⟨h.grows, fun x hx _ _ h3 _ => h.same x hx (Classical.byContradiction fun hc => h3 (hab x (by omega) (by omega)))⟩

/-- A change inside the global variables. -/
theorem of_glob {a b top : Nat} {d d' : DataMem} (h : Only a b d d') (hab : ∀ x, a ≤ x → x < b → G.InGlob x) :
    Pres G top d d' :=
  ⟨h.grows, fun x hx _ _ _ h4 => h.same x hx (Classical.byContradiction fun hc => h4 (hab x (by omega) (by omega)))⟩

end Pres

theorem u64_sub_one_toNat {x : UInt64} (h : 0 < x.toNat) : (x - 1).toNat = x.toNat - 1 := by
  rw [UInt64.toNat_sub_of_le]
  · rfl
  · rw [UInt64.le_iff_toNat_le]; simp; omega

/-- The current function's frame ends here. -/
abbrev top (d : MachineData) (F : Nat) : Nat := d.regs.rsp.toNat + 8 * F

/-- What a statement keeps: the frame, `rbp`, `r15`; the fuel counter only goes down. -/
structure SPost (G : Layout) (F : Nat) (d d' : MachineData) : Prop where
  rsp : d'.regs.rsp = d.regs.rsp
  rbp : d'.regs.rbp = d.regs.rbp
  r15 : d'.regs.r15 = d.regs.r15
  r14 : d'.regs.r14.toNat ≤ d.regs.r14.toNat
  mem : Pres G (top d F) d.dmem d'.dmem

/-- What a statement keeps when it leaves through `ca_error` or `ca_exhausted`. -/
structure GPost (G : Layout) (top : Nat) (d d' : MachineData) : Prop where
  rbp : d'.regs.rbp = d.regs.rbp
  mem : Pres G top d.dmem d'.dmem

namespace SPost
variable {G : Layout} {F : Nat}

theorem refl (d : MachineData) : SPost G F d d := ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.refl _ _⟩

theorem trans {d d' d'' : MachineData} (h : SPost G F d d') (h' : SPost G F d' d'') : SPost G F d d'' :=
  ⟨h'.rsp.trans h.rsp, h'.rbp.trans h.rbp, h'.r15.trans h.r15, Nat.le_trans h'.r14 h.r14,
    h.mem.trans (by have := h'.mem; simp only [top, h.rsp] at this; exact this)⟩

theorem gpost {d d' : MachineData} (h : SPost G F d d') : GPost G (top d F) d d' := ⟨h.rbp, h.mem⟩

theorem trans_g {d d' d'' : MachineData} (h : SPost G F d d') (h' : GPost G (top d' F) d' d'') :
    GPost G (top d F) d d'' :=
  ⟨h'.rbp.trans h.rbp, h.mem.trans (by have := h'.mem; simp only [top, h.rsp] at this; exact this)⟩

end SPost

theorem EPost.spost {G : Layout} {nl F t : Nat} {d d' : MachineData} (h : EPost nl F t d d')
    (hlo : G.lo ≤ d.regs.rsp.toNat) : SPost G F d d' :=
  ⟨h.rsp, h.rbp, h.r15, by rw [h.r14]; exact Nat.le_refl _, Pres.of_only h.mem (by omega) (Nat.le_refl _)⟩

/-- The exits of a statement whose run is `R`, for code that ends at `kend`. -/
structure Conts [Host] (G : Layout) (ctx : Ctx) (F : Nat) (d : MachineData) (R : Except Err (Sig × St))
    (kend : Nat) (Q : MachineState → Prop) : Prop where
  normal : ∀ σ' d', R = .ok (.normal, σ') → Inv G ctx.nl F σ' d' → SPost G F d d' → Ev Q d' (at_ kend)
  brk : ∀ σ' d', R = .ok (.brk, σ') → Inv G ctx.nl F σ' d' → SPost G F d d' → Ev Q d' (label ctx.brk)
  ret : ∀ vs σ' d', R = .ok (.ret vs, σ') → Inv G ctx.nl F σ' d' → SPost G F d d' →
    ResOut G vs d' → Ev Q d' (label ctx.retL)
  err : ∀ d', (∃ e, R = .error e ∧ e ≠ .outOfFuel) → GPost G (top d F) d d' → Ev Q d' (label errorL)
  exh : ∀ d', GPost G (top d F) d d' → Ev Q d' (label exhaustedL)

/-- The simulation of a statement `s`, for a run function `run` and a condition `P` on the fuel
counter. -/
def SimS [Host] (p : Prog) (G : Layout) (run : Stmt → St → Except Err (Sig × St)) (P : Nat → Prop)
    (s : Stmt) : Prop :=
  ∀ (ctx : Ctx) (F : Nat) (path : Path) (k : Nat), ctx.tab = G.tab → 8 * F + 8 < maxOff →
    Code (compileS ctx path s) k → Stmt.wf p ctx.nl G.tab s = true → ctx.nl + tempsS s ≤ F →
    ∀ (σ : St) (d : MachineData) (Q : MachineState → Prop), Inv G ctx.nl F σ d → P d.regs.r14.toNat →
    Conts G ctx F d (run s σ) (k + (compileS ctx path s).length) Q → Ev Q d (at_ k)

/-- `exec p n` on statement `s` from state `σ`. -/
def execRun (p : Prog) (n : Nat) (s : Stmt) (σ : St) : Except Err (Sig × St) := (exec p n s).run σ

/-- Statements under `step p (exec p n)`, with at most `n` units of machine fuel. -/
abbrev StepSim [Host] (p : Prog) (G : Layout) (n : Nat) : Prop :=
  ∀ s, SimS p G (stepRun p (exec p n)) (· ≤ n) s

/-- Statements under `exec p n`, with fewer than `n` units of machine fuel. -/
abbrev ExecSim [Host] (p : Prog) (G : Layout) (n : Nat) : Prop :=
  ∀ s, SimS p G (execRun p n) (· < n) s

theorem execSim_zero [Host] (p : Prog) (G : Layout) : ExecSim p G 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP _ => absurd hP (Nat.not_lt_zero _)

theorem execSim_succ [Host] {p : Prog} {G : Layout} {n : Nat} (h : StepSim p G n) : ExecSim p G (n + 1) :=
  fun s ctx F path k hT hF hc hwf htmp σ d Q hI hP hK =>
    h s ctx F path k hT hF hc hwf htmp σ d Q hI (Nat.lt_succ_iff.mp hP) hK


theorem SPost.store {G : Layout} {F : Nat} {d : MachineData} {a : Nat} {v : BitVec 64}
    (hlo : G.lo ≤ a) (ha : a + 8 ≤ top d F) (hov : top d F ≤ 2 ^ 64) :
    SPost G F d { d with dmem := wrW d.dmem (A a) v } :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.of_only (Only.wrW (by omega)) hlo ha⟩

theorem SPost.regs {G : Layout} {F : Nat} {d : MachineData} {R : Reg64s} {st : StatusFlags}
    (h1 : R.rsp = d.regs.rsp) (h2 : R.rbp = d.regs.rbp) (h3 : R.r15 = d.regs.r15)
    (h4 : R.r14.toNat ≤ d.regs.r14.toNat) :
    SPost G F d { d with regs := R, status := st } := ⟨h1, h2, h3, h4, Pres.refl _ _⟩

section
variable {G : Layout} (hG : G.Ok)
include hG

theorem Inv.setLoc {nl F : Nat} {σ : St} {d : MachineData} (hI : Inv G nl F σ d) {x : Nat} (hx : x < nl)
    (v : Word) :
    Inv G nl F (σ.setLoc x v) { d with dmem := wrW d.dmem (A (d.regs.rsp.toNat + 8 * x)) v.toBitVec } where
  r15 := hI.r15
  lo8 := hI.lo8
  hi := hI.hi
  nlF := hI.nlF
  frame := fun y hy => by
    have := hI.hi; have := hG.hi_le; have := hI.nlF
    by_cases hxy : y = x
    · subst hxy; simp [St.setLoc, rdW_wrW_same]
    · simp only [St.setLoc, hxy, ite_false]
      rw [rdW_wrW_A (by omega) (by omega) (by omega)]
      exact hI.frame y hy
  mem := hI.mem.only hG (Only.wrW (by have := hI.hi; have := hG.hi_le; have := hI.nlF; omega))
    fun z h1 h2 => ⟨by have := hI.lo; omega, by have := hI.hi; have := hI.nlF; omega⟩

end

section
variable [Host] {G : Layout} (hG : G.Ok) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
  (p : Prog) (K : Stmt → M Sig) (P : Nat → Prop)
include hG hTab

omit hG hTab in
theorem sim_skip : SimS p G (stepRun p K) P .skip := by
  intro ctx F path k hT hF hc hwf htmp σ d Q hI hP hK
  exact ev_congr (hK.normal σ d (step_skip_run p K σ) hI (SPost.refl d)) (by simp [compileS])

omit hG hTab in
theorem sim_brk : SimS p G (stepRun p K) P .brk := by
  intro ctx F path k hT hF hc hwf htmp σ d Q hI hP hK
  simp only [compileS] at hc
  exact ev_jmp hc.head (hK.brk σ d (step_brk_run p K σ) hI (SPost.refl d))

omit hG hTab in
theorem sim_abort : SimS p G (stepRun p K) P .abort := by
  intro ctx F path k hT hF hc hwf htmp σ d Q hI hP hK
  simp only [compileS] at hc
  exact ev_jmp hc.head (hK.err d ⟨.abort, step_abort_run p K σ, by simp⟩ (SPost.refl d).gpost)

theorem sim_set (x : Var) (e : Expr) : SimS p G (stepRun p K) P (.set x e) := by
  intro ctx F path k hT hF hc hwf htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  simp only [compileS] at hc hK
  simp only [tempsS] at htmp
  have hF' := hF; simp only [maxOff] at hF'
  refine sim_expr hG ctx hT hTab F hF e 0 k hc.left hwf.2 (by omega) σ d Q hI ?_ ?_
  · intro v s1 hv hrax hE1
    have hI1 := hI.only hG (hE1.mem.mono (by omega) (Nat.le_refl _)) hE1.rsp hE1.r15
    have hx := hwf.1
    have := hI.nlF
    refine ev_movMR hc.right.head ⟨by lomega, by lomega⟩ ?_ ?_
    · rw [slot_addr _ x _ (by omega)]; exact hI1.mapped (by lomega)
    rw [slot_addr _ x _ (by omega)]
    have hv' : s1.regs.get64 .rax = v.toBitVec := by simp [hrax]
    rw [hv']
    refine ev_congr (hK.normal (σ.setLoc x v) _ ?_ (hI1.setLoc hG hx v) ?_) ?_
    · simp [step_set_run, hv]; rfl
    · refine (hE1.spost hI.lo).trans (SPost.store ?_ ?_ ?_)
      · have := hI1.lo; omega
      · have := hI.hi; simp only [top, hE1.rsp]; lomega
      · have := hI.hi; have := hG.hi_le; simp only [top, hE1.rsp]; omega
    · simp; omega
  · intro s1 herr hE1
    obtain ⟨y, hy⟩ := herr
    refine hK.err s1 ⟨y, by simp [step_set_run, hy]; rfl, by rw [evalP_error hy]; simp⟩ (hE1.spost hI.lo).gpost

omit hG hTab in
theorem sim_seq (hPm : ∀ a b, a ≤ b → P b → P a) (s t : Stmt)
    (hs : SimS p G (stepRun p K) P s) (ht : SimS p G (stepRun p K) P t) :
    SimS p G (stepRun p K) P (.seq s t) := by
  intro ctx F path k hT hF hc hwf htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true] at hwf
  simp only [compileS] at hc hK
  simp only [tempsS] at htmp
  refine hs ctx F _ k hT hF hc.left hwf.1 (by omega) σ d Q hI hP ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro σ1 d1 hr1 hI1 hS1
    refine ht ctx F _ _ hT hF hc.right hwf.2 (by omega) σ1 d1 Q hI1 (hPm _ _ hS1.r14 hP) ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro σ2 d2 hr2 hI2 hS2
      refine ev_congr (hK.normal σ2 d2 (by rw [step_seq_run, hr1]; exact hr2) hI2 (hS1.trans hS2)) ?_
      simp only [List.length_append]; omega
    · intro σ2 d2 hr2 hI2 hS2
      exact hK.brk σ2 d2 (by rw [step_seq_run, hr1]; exact hr2) hI2 (hS1.trans hS2)
    · intro v σ2 d2 hr2 hI2 hS2 hv
      exact hK.ret v σ2 d2 (by rw [step_seq_run, hr1]; exact hr2) hI2 (hS1.trans hS2) hv
    · intro d2 ⟨e, hr2, hne⟩ hG2
      exact hK.err d2 ⟨e, by rw [step_seq_run, hr1]; exact hr2, hne⟩ (hS1.trans_g hG2)
    · intro d2 hG2
      exact hK.exh d2 (hS1.trans_g hG2)
  · intro σ1 d1 hr1 hI1 hS1
    exact hK.brk σ1 d1 (by rw [step_seq_run, hr1]) hI1 hS1
  · intro v σ1 d1 hr1 hI1 hS1 hv
    exact hK.ret v σ1 d1 (by rw [step_seq_run, hr1]) hI1 hS1 hv
  · intro d1 ⟨e, hr1, hne⟩ hG1
    exact hK.err d1 ⟨e, by rw [step_seq_run, hr1], hne⟩ hG1
  · intro d1 hG1
    exact hK.exh d1 hG1

theorem sim_ite (c : Cond) (s t : Stmt)
    (hs : SimS p G (stepRun p K) P s) (ht : SimS p G (stepRun p K) P t) :
    SimS p G (stepRun p K) P (.ite c s t) := by
  intro ctx F path k hT hF hc hwf htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true] at hwf
  simp only [compileS, List.append_assoc, List.cons_append, List.nil_append] at hc hK
  simp only [tempsS] at htmp
  have hc1 := hc.right
  have hc2 := hc1.right
  have hE := Code.label (i := 1) hc2 rfl
  have hc3 := hc2.tail.tail
  have hX := Code.label (i := 0) hc3.right rfl
  refine sim_cond hG ctx hT hTab F hF c _ false _ 0 k hc.left hwf.1.1 (by omega) σ d Q hI ?_ ?_ ?_
  · -- the condition is false: the else branch
    intro d1 hc1v hE1
    have hI1 := hI.only hG (hE1.mem.mono (by omega) (Nat.le_refl _)) hE1.rsp hE1.r15
    have hS1 := hE1.spost (G := G) hI.lo
    rw [hE]
    refine ev_label hc2.tail.head ?_
    refine ht ctx F _ _ hT hF hc3.left hwf.2 (by omega) σ d1 Q hI1 (by rw [hE1.r14]; exact hP)
      ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro σ2 d2 hr2 hI2 hS2
      refine ev_label hc3.right.head ?_
      refine ev_congr (hK.normal σ2 d2 (by rw [step_ite_run, hc1v]; exact hr2) hI2 (hS1.trans hS2)) ?_
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro σ2 d2 hr2 hI2 hS2
      exact hK.brk σ2 d2 (by rw [step_ite_run, hc1v]; exact hr2) hI2 (hS1.trans hS2)
    · intro v σ2 d2 hr2 hI2 hS2 hv
      exact hK.ret v σ2 d2 (by rw [step_ite_run, hc1v]; exact hr2) hI2 (hS1.trans hS2) hv
    · intro d2 ⟨e, hr2, hne⟩ hG2
      exact hK.err d2 ⟨e, by rw [step_ite_run, hc1v]; exact hr2, hne⟩ (hS1.trans_g hG2)
    · intro d2 hG2
      exact hK.exh d2 (hS1.trans_g hG2)
  · -- the condition is true: the then branch
    intro d1 hc1v hE1
    have hI1 := hI.only hG (hE1.mem.mono (by omega) (Nat.le_refl _)) hE1.rsp hE1.r15
    have hS1 := hE1.spost (G := G) hI.lo
    refine hs ctx F _ _ hT hF hc1.left hwf.1.2 (by omega) σ d1 Q hI1 (by rw [hE1.r14]; exact hP)
      ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro σ2 d2 hr2 hI2 hS2
      refine ev_jmp hc2.head ?_
      rw [hX]
      refine ev_label hc3.right.head ?_
      refine ev_congr (hK.normal σ2 d2 (by rw [step_ite_run, hc1v]; exact hr2) hI2 (hS1.trans hS2)) ?_
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro σ2 d2 hr2 hI2 hS2
      exact hK.brk σ2 d2 (by rw [step_ite_run, hc1v]; exact hr2) hI2 (hS1.trans hS2)
    · intro v σ2 d2 hr2 hI2 hS2 hv
      exact hK.ret v σ2 d2 (by rw [step_ite_run, hc1v]; exact hr2) hI2 (hS1.trans hS2) hv
    · intro d2 ⟨e, hr2, hne⟩ hG2
      exact hK.err d2 ⟨e, by rw [step_ite_run, hc1v]; exact hr2, hne⟩ (hS1.trans_g hG2)
    · intro d2 hG2
      exact hK.exh d2 (hS1.trans_g hG2)
  · intro d1 ⟨e, he⟩ hE1
    exact hK.err d1 ⟨e, by rw [step_ite_run, he], by rw [evalCP_error he]; simp⟩
      (hE1.spost (G := G) hI.lo).gpost

omit [Host] hG hTab in
theorem Inv.of_regs {nl F : Nat} {σ : St} {d d' : MachineData} (hI : Inv G nl F σ d)
    (hd : d'.dmem = d.dmem) (hsp : d'.regs.rsp = d.regs.rsp) (h15 : d'.regs.r15 = d.regs.r15) :
    Inv G nl F σ d' :=
  ⟨h15 ▸ hI.r15, hsp ▸ hI.lo8, hsp ▸ hI.hi, hI.nlF, fun x hx => hsp ▸ hd ▸ hI.frame x hx, hd ▸ hI.mem⟩

theorem sim_while (n : Nat) (hE : ExecSim p G n) (c : Cond) (s : Stmt)
    (hs : SimS p G (stepRun p (exec p n)) (· ≤ n) s) :
    SimS p G (stepRun p (exec p n)) (· ≤ n) (.while c s) := by
  intro ctx F path k hT hF hc hwf htmp σ d Q hI hP hK
  have hc0 := hc
  simp only [Stmt.wf, Bool.and_eq_true] at hwf
  simp only [compileS, burnFuel, List.append_assoc, List.cons_append, List.nil_append,
    List.singleton_append] at hc hK
  simp only [tempsS] at htmp
  have hH := Code.label (i := 0) hc rfl
  have hc1 := hc.tail
  have hc2 := hc1.right
  have hc3 := hc2.right
  have hX := Code.label (i := 3) hc3 rfl
  refine ev_label hc.head ?_
  refine sim_cond hG ctx hT hTab F hF c _ false _ 0 _ hc1.left hwf.1 (by omega) σ d Q hI ?_ ?_ ?_
  · -- the condition is false: leave the loop
    intro d1 hcv hE1
    have hI1 := hI.only hG (hE1.mem.mono (by omega) (Nat.le_refl _)) hE1.rsp hE1.r15
    rw [hX]
    refine ev_label hc3.tail.tail.tail.head ?_
    refine ev_congr (hK.normal σ d1 (by rw [step_while_run, hcv]) hI1 (hE1.spost hI.lo)) ?_
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · -- the condition is true: the body
    intro d1 hcv hE1
    have hI1 := hI.only hG (hE1.mem.mono (by omega) (Nat.le_refl _)) hE1.rsp hE1.r15
    have hS1 := hE1.spost (G := G) hI.lo
    refine hs { ctx with brk := ctx.lbl path "X" } F _ _ hT hF hc2.left hwf.2 (by simp; omega) σ d1 Q
      hI1 (by rw [hE1.r14]; exact hP) ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- the body ends normally: burn fuel and go round
      intro σ1 d2 hr1 hI2 hS2
      have hS12 := hS1.trans hS2
      refine ev_sub1 hc3.head fun st hst => ?_
      refine ev_jcc hc3.tail.head (fun hcc => ?_) (fun hcc => ?_)
      · exact hK.exh _ (hS12.trans_g ⟨by simp, Pres.refl _ _⟩)
      · simp only [CondCode.interp] at hcc
        rw [hst] at hcc
        have h0 : d2.regs.r14 ≠ 0 := by
          intro h; simp [h] at hcc
        have hpos : 0 < d2.regs.r14.toNat := by
          rcases Nat.eq_zero_or_pos d2.regs.r14.toNat with h | h
          · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) h0
          · exact h
        refine ev_jmp hc3.tail.tail.head ?_
        rw [hH]
        have hS3 : SPost G F d2 { d2 with regs := d2.regs.set64 .r14 (d2.regs.get64 .r14 - 1), status := st } :=
          SPost.regs (by simp) (by simp) (by simp) (by simp [Reg64s.set64_r14, u64_sub_one_toNat hpos])
        have hS13 := hS12.trans hS3
        refine hE (.while c s) ctx F path k hT hF hc0 (by simp [Stmt.wf, hwf.1, hwf.2]) (by simp only [tempsS]; omega) σ1 _ Q
          (hI2.of_regs rfl (by simp) (by simp)) ?_ ⟨?_, ?_, ?_, ?_, ?_⟩
        · show _ < n
          have := hS12.r14
          simp [Reg64s.set64_r14, u64_sub_one_toNat hpos]
          omega
        · intro σ2 d4 hr2 hI4 hS4
          refine ev_congr (hK.normal σ2 d4 (by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]; exact hr2)
            hI4 (hS13.trans hS4)) ?_
          simp [compileS, burnFuel]
        · intro σ2 d4 hr2 hI4 hS4
          exact hK.brk σ2 d4 (by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]; exact hr2) hI4 (hS13.trans hS4)
        · intro v σ2 d4 hr2 hI4 hS4 hv
          exact hK.ret v σ2 d4 (by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]; exact hr2) hI4 (hS13.trans hS4) hv
        · intro d4 ⟨e, hr2, hne⟩ hG4
          exact hK.err d4 ⟨e, by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]; exact hr2, hne⟩ (hS13.trans_g hG4)
        · intro d4 hG4
          exact hK.exh d4 (hS13.trans_g hG4)
    · -- `break`: leave the loop
      intro σ1 d2 hr1 hI2 hS2
      show Ev Q d2 (label (ctx.lbl path "X"))
      rw [hX]
      refine ev_label hc3.tail.tail.tail.head ?_
      refine ev_congr (hK.normal σ1 d2 (by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]) hI2 (hS1.trans hS2)) ?_
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro v σ1 d2 hr1 hI2 hS2 hv
      exact hK.ret v σ1 d2 (by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1]) hI2 (hS1.trans hS2) hv
    · intro d2 ⟨e, hr1, hne⟩ hG2
      exact hK.err d2 ⟨e, by rw [step_while_run, hcv]; simp only [Bool.not_false, hr1], hne⟩ (hS1.trans_g hG2)
    · intro d2 hG2
      exact hK.exh d2 (hS1.trans_g hG2)
  · intro d1 ⟨e, he⟩ hE1
    exact hK.err d1 ⟨e, by rw [step_while_run, he], by rw [evalCP_error he]; simp⟩
      (hE1.spost (G := G) hI.lo).gpost

end

end L.Compiler
