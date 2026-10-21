module

public import ConAgua.Compiler.Rel

@[expose] public section

/-!
# Expressions and conditions

`evalE` never changes the state, so its run is a pure function `evalP` of the state.
`sim_expr`: the code of `e` leaves `evalP σ e` in `rax`, or jumps to `ca_error` exactly when
`evalP σ e` fails; it changes only the temporaries from `t` on.
-/

namespace L.Compiler

open L

/-- `evalE`, without the state. -/
def evalP (σ : St) : Expr → Except Err Word
  | .const w => .ok w
  | .var x => .ok (σ.loc x)
  | .bin op a b => do
    let x ← evalP σ a
    let y ← evalP σ b
    return op.eval x y
  | .ld8 a i => do
    let j ← evalP σ i
    if h : j.toNat < (σ.mem.arr8 a).size then .ok (σ.mem.arr8 a)[j.toNat].toUInt64 else .error .oob
  | .ld64 a i => do
    let j ← evalP σ i
    if h : j.toNat < (σ.mem.arr64 a).size then .ok (σ.mem.arr64 a)[j.toNat] else .error .oob
  | .len8 a => .ok (σ.mem.len8 a)
  | .len64 a => .ok (σ.mem.len64 a)

theorem evalE_run (σ : St) (e : Expr) : (evalE e).run σ = (evalP σ e).map (·, σ) := by
  induction e with
  | const => rfl
  | var => rfl
  | bin op a b iha ihb =>
    simp only [evalE, evalP, StateT.run_bind] at *
    rw [iha]
    cases evalP σ a <;> simp [Except.map, bind, Except.bind, ihb]
    · cases evalP σ b <;> rfl
  | ld8 a i ih =>
    simp only [evalE, evalP, StateT.run_bind, ih]
    cases evalP σ i with
    | error => rfl
    | ok j =>
      simp only [Except.map, bind, Except.bind, L.ld8, pure]
      by_cases hj : j.toNat < (σ.mem.arr8 a).size
      · simp [StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, hj, StateT.pure]; rfl
      · simp [StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, hj]; rfl
  | ld64 a i ih =>
    simp only [evalE, evalP, StateT.run_bind, ih]
    cases evalP σ i with
    | error => rfl
    | ok j =>
      simp only [Except.map, bind, Except.bind, L.ld64, pure]
      by_cases hj : j.toNat < (σ.mem.arr64 a).size
      · simp [StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, hj, StateT.pure]; rfl
      · simp [StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, hj]; rfl
  | len8 => rfl
  | len64 => rfl


/-! ## Evaluating an expression on the machine -/

/-- What evaluating an expression with temporaries from `t` may change: `rax`, `rcx`, `rdx`,
the flags and the temporaries `t, t+1, …` of the frame. -/
structure EPost (nl F t : Nat) (s s' : MachineData) : Prop where
  rsp : s'.regs.rsp = s.regs.rsp
  rbp : s'.regs.rbp = s.regs.rbp
  r14 : s'.regs.r14 = s.regs.r14
  r15 : s'.regs.r15 = s.regs.r15
  rsi : s'.regs.rsi = s.regs.rsi
  mem : Only (s.regs.rsp.toNat + 8 * (nl + t)) (s.regs.rsp.toNat + 8 * F) s.dmem s'.dmem

theorem EPost.refl (nl F t : Nat) (s : MachineData) : EPost nl F t s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, Only.refl _ _ _⟩

theorem EPost.trans {nl F t t' : Nat} {s s' s'' : MachineData} (h : EPost nl F t s s')
    (h' : EPost nl F t' s' s'') (ht : t ≤ t') : EPost nl F t s s'' := by
  have hm := h'.mem
  rw [h.rsp] at hm
  exact ⟨h'.rsp.trans h.rsp, h'.rbp.trans h.rbp, h'.r14.trans h.r14, h'.r15.trans h.r15,
    h'.rsi.trans h.rsi, h.mem.trans hm (by omega) (Nat.le_refl _)⟩

/-- The registers of an expression step: only `rax`, `rcx`, `rdx` and the flags change. -/
theorem EPost.regs {nl F t : Nat} {s : MachineData} {r : Reg64} (hr : r = .rax ∨ r = .rcx ∨ r = .rdx)
    (v : BitVec 64) (st : StatusFlags) :
    EPost nl F t s { s with regs := s.regs.set64 r v, status := st } := by
  rcases hr with rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, Only.refl _ _ _⟩

theorem EPost.regs' {nl F t : Nat} {s : MachineData} {r : Reg64} (hr : r = .rax ∨ r = .rcx ∨ r = .rdx)
    (v : BitVec 64) : EPost nl F t s { s with regs := s.regs.set64 r v } :=
  EPost.regs (st := s.status) hr v

theorem EPost.flags {nl F t : Nat} {s : MachineData} (st : StatusFlags) :
    EPost nl F t s { s with status := st } :=
  ⟨rfl, rfl, rfl, rfl, rfl, Only.refl _ _ _⟩


theorem EPost.store {nl F t j : Nat} {s : MachineData} {v : BitVec 64} (hj : nl + t ≤ j) (hjF : j + 1 ≤ F)
    (hov : s.regs.rsp.toNat + 8 * F ≤ 2 ^ 64) :
    EPost nl F t s { s with dmem := wrW s.dmem (A (s.regs.rsp.toNat + 8 * j)) v } :=
  ⟨rfl, rfl, rfl, rfl, rfl, (Only.wrW (by omega)).mono (by omega) (by omega)⟩

theorem EPost.of_eq {nl F t : Nat} {s s' s'' : MachineData} (h : EPost nl F t s s')
    (hd : s''.dmem = s'.dmem) (h1 : s''.regs.rsp = s'.regs.rsp) (h2 : s''.regs.rbp = s'.regs.rbp)
    (h3 : s''.regs.r14 = s'.regs.r14) (h4 : s''.regs.r15 = s'.regs.r15) (h5 : s''.regs.rsi = s'.regs.rsi) :
    EPost nl F t s s'' :=
  ⟨h1.trans h.rsp, h2.trans h.rbp, h3.trans h.r14, h4.trans h.r15, h5.trans h.rsi, hd ▸ h.mem⟩

theorem slot_addr (s : MachineData) (j : Nat) (off : Int) (h : off = 8 * (j : Int)) :
    A ((s.regs.get64 .rsp).toNat + off.toNat) = A (s.regs.rsp.toNat + 8 * j) := by
  subst h; simp only [Reg64s.get64_rsp, UInt64.toNat_toBitVec]; congr 1; (try omega)

theorem Inv.mapped {G : Layout} {nl F : Nat} {σ : St} {s : MachineData} (hI : Inv G nl F σ s) {j : Nat}
    (hj : j ≤ F) : (rdW s.dmem (A (s.regs.rsp.toNat + 8 * j))).isSome :=
  isSome_rdW fun i hi => by
    rw [A_add]
    exact hI.mem.stack _ ⟨by have := hI.lo; omega, by have := hI.hi; omega⟩

theorem toNat_eight_mul (x : Nat) : (8 * (x : Int)).toNat = 8 * x := by omega

/-- `omega`, after unfolding L's `Nat` synonyms (see docs/gaps/omega-nat-synonym-hyp.lean). -/
macro "lomega" : tactic => `(tactic| (try simp only [L.Var, L.ArrId] at *) <;> omega)

attribute [local simp] Reg64s.set64_rax Reg64s.set64_rcx Reg64s.set64_rdx Reg64s.set64_rsi
  Reg64s.set64_rsp Reg64s.set64_r14

section
variable [Host] {G : Layout} (hG : G.Ok)
include hG

theorem sim_expr (ctx : Ctx) (hT : ctx.tab = G.tab) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) < maxOff)
    (F : Nat) (hF : 8 * F + 8 < maxOff) :
    ∀ (e : Expr) (t k : Nat), Code (compileE ctx e t) k → Expr.wf ctx.nl G.tab e = true →
    ctx.nl + t + tempsE e ≤ F →
    ∀ (σ : St) (s : MachineData) (Q : MachineState → Prop), Inv G ctx.nl F σ s →
    (∀ v s', evalP σ e = .ok v → s'.regs.rax = v → EPost ctx.nl F t s s' →
      Ev Q s' (at_ (k + (compileE ctx e t).length))) →
    (∀ s', (∃ x, evalP σ e = .error x) → EPost ctx.nl F t s s' → Ev Q s' (label errorL)) →
    Ev Q s (at_ k) := by
  simp only [maxOff] at hF hTab
  intro e
  induction e with
  | const w =>
    intro t k hc _ _ σ s Q hI hok _
    exact ev_movRI hc.head (hok w _ rfl (by simp) (EPost.regs' (by simp) _))
  | var x =>
    intro t k hc hwf _ σ s Q hI hok _
    simp only [Expr.wf, decide_eq_true_eq] at hwf
    have := hI.nlF
    refine ev_movRM hc.head ⟨by lomega, by lomega⟩ (v := σ.loc x) ?_
      (hok _ _ rfl (by simp) (EPost.regs' (by simp) _))
    rw [Reg64s.get64_rsp, UInt64.toNat_toBitVec, toNat_eight_mul]; exact hI.frame x hwf
  | len8 a =>
    intro t k hc hwf _ σ s Q hI hok _
    simp only [Expr.wf, decide_eq_true_eq] at hwf
    refine ev_movRM hc.head ⟨by simp [Tab.len8]; lomega, by simp [hT, Tab.len8]; lomega⟩
      (v := UInt64.ofNat (G.s8 a)) ?_
      (hok _ _ rfl ?_ (EPost.regs' (by simp) _))
    · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.len8 a hwf
    · simp [evalP, Mem.len8, hI.mem.size8 a hwf]
  | len64 a =>
    intro t k hc hwf _ σ s Q hI hok _
    simp only [Expr.wf, decide_eq_true_eq] at hwf
    refine ev_movRM hc.head ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩
      (v := UInt64.ofNat (G.s64 a)) ?_
      (hok _ _ rfl ?_ (EPost.regs' (by simp) _))
    · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.len64 a hwf
    · simp [evalP, Mem.len64, hI.mem.size64 a hwf]
  | bin op a b iha ihb =>
    intro t k hc hwf htmp σ s Q hI hok herr
    simp only [Expr.wf, Bool.and_eq_true] at hwf
    simp only [tempsE] at htmp
    simp only [compileE, List.append_assoc, List.singleton_append] at hc hok
    have hc1 := hc.right
    have hsp := hI.hi
    have hhi := hG.hi_le
    refine iha t k hc.left hwf.1 (by omega) σ s Q hI ?_ ?_
    · intro va s1 hva hrax1 hE1
      have hI1 : Inv G ctx.nl F σ s1 :=
        hI.only hG (hE1.mem.mono (by omega) (Nat.le_refl _)) hE1.rsp hE1.r15
      have hoff : SmallOff (8 * ((ctx.nl : Int) + (t : Int))) := ⟨by omega, by omega⟩
      refine ev_movMR hc1.head hoff ?_ ?_
      · rw [slot_addr _ (ctx.nl + t) _ (by omega)]; exact hI1.mapped (by omega)
      rw [slot_addr _ (ctx.nl + t) _ (by omega)]
      have hE2 := hE1.trans (EPost.store (v := s1.regs.get64 .rax) (j := ctx.nl + t) (s := s1)
        (by omega) (by omega) (by rw [hE1.rsp]; omega)) (Nat.le_refl _)
      have hI2 := hI.only hG (hE2.mem.mono (by omega) (Nat.le_refl _)) hE2.rsp hE2.r15
      have hc2 := hc1.tail
      refine ihb (t + 1) _ hc2.left hwf.2 (by omega) σ _ Q hI2 ?_ ?_
      · intro vb s3 hvb hrax3 hE3
        have h1rsp := congrArg UInt64.toNat hE1.rsp
        have h2rsp := congrArg UInt64.toNat hE2.rsp
        have h3rsp := congrArg UInt64.toNat hE3.rsp
        have hcR := hc2.right
        refine ev_movRR hcR.head ?_
        refine ev_movRM hcR.tail.head hoff (v := va) ?_ ?_
        · rw [slot_addr _ (ctx.nl + t) _ (by omega)]
          simp only [Reg64s.set64_rcx]
          rw [hE3.rsp, hE3.mem.rdW_eq (by omega) (by omega)]
          simp only [hE1.rsp, rdW_wrW_same, Reg64s.get64_rax, hrax1, UInt64.ofBitVec_toBitVec]
        refine ev_bin hcR.tail.tail.head fun st => ?_
        refine ev_congr (hok (op.eval va vb) _ ?_ (by simp [hrax3]) ?_) ?_
        · simp [evalP, hva, hvb]; rfl
        · exact (hE2.trans hE3 (by omega)).of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp)
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · intro s3 herrb hE3
        refine herr s3 ?_ (hE2.trans hE3 (by omega))
        obtain ⟨x, hx⟩ := herrb
        exact ⟨x, by simp [evalP, hva, hx]; rfl⟩
    · intro s1 herra hE1
      refine herr s1 ?_ hE1
      obtain ⟨x, hx⟩ := herra
      exact ⟨x, by simp [evalP, hx]; rfl⟩
  | ld8 a i ih =>
    intro t k hc hwf htmp σ s Q hI hok herr
    simp only [Expr.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    simp only [tempsE] at htmp
    simp only [compileE] at hc hok
    have hcR := hc.right
    refine ih t k hc.left hwf.2 (by omega) σ s Q hI ?_ ?_
    · intro j s1 hj hrax1 hE1
      have hI1 : Inv G ctx.nl F σ s1 :=
        hI.only hG (hE1.mem.mono (by omega) (Nat.le_refl _)) hE1.rsp hE1.r15
      have hsz := hI1.mem.size8 a hwf.1
      have hend := hG.end8 a hwf.1
      refine ev_cmpRM hcR.head ⟨by simp [Tab.len8]; lomega, by simp [hT, Tab.len8]; lomega⟩
        (v := UInt64.ofNat (G.s8 a)) ?_ ?_
      · rw [hI1.r15, hT]; exact hI1.mem.len8 a hwf.1
      refine ev_jcc hcR.tail.head (fun hcc => ?_) (fun hcc => ?_)
      · refine herr _ ⟨.oob, ?_⟩ ((hE1.trans (EPost.flags _) (Nat.le_refl _)))
        simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_true', decide_eq_false_iff_not,
          UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' (show G.s8 a < UInt64.size by
            simp [UInt64.size]; omega), hrax1] at hcc
        simp only [evalP, hj, bind, Except.bind]
        rw [dite_eq_right (by rw [hsz]; exact hcc)]
      · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_false', decide_eq_true_eq,
          UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' (show G.s8 a < UInt64.size by
            simp [UInt64.size]; omega), hrax1] at hcc
        refine ev_movRM hcR.tail.tail.head ⟨by simp [Tab.base8]; lomega, by simp [hT, Tab.base8]; lomega⟩
          (v := UInt64.ofNat (G.b8 a)) ?_ ?_
        · simp only [Reg64s.get64_r15, UInt64.toNat_toBitVec]
          rw [hI1.r15, hT]; exact hI1.mem.base8 a hwf.1
        refine ev_movzx hcR.tail.tail.tail.head (b := (σ.mem.arr8 a)[j.toNat]'(by omega)) ?_ ?_
        · simp only [Reg64s.set64_rcx, hrax1]
          have := hI1.mem.get8 a hwf.1 j.toNat (by omega)
          rw [← this]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp [A]
          (try omega)
        refine ev_congr (hok ((σ.mem.arr8 a)[j.toNat]'(by omega)).toUInt64 _ ?_ (by simp) ?_) ?_
        · simp only [evalP, hj, bind, Except.bind]
          rw [dite_eq_left (by omega)]
        · exact hE1.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp)
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro s1 herra hE1
      refine herr s1 ?_ hE1
      obtain ⟨x, hx⟩ := herra
      exact ⟨x, by simp [evalP, hx]; rfl⟩
  | ld64 a i ih =>
    intro t k hc hwf htmp σ s Q hI hok herr
    simp only [Expr.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    simp only [tempsE] at htmp
    simp only [compileE] at hc hok
    have hcR := hc.right
    refine ih t k hc.left hwf.2 (by omega) σ s Q hI ?_ ?_
    · intro j s1 hj hrax1 hE1
      have hI1 : Inv G ctx.nl F σ s1 :=
        hI.only hG (hE1.mem.mono (by omega) (Nat.le_refl _)) hE1.rsp hE1.r15
      have hsz := hI1.mem.size64 a hwf.1
      have hend := hG.end64 a hwf.1
      have hlt : G.s64 a < UInt64.size := by simp [UInt64.size]; omega
      refine ev_cmpRM hcR.head ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩
        (v := UInt64.ofNat (G.s64 a)) ?_ ?_
      · rw [hI1.r15, hT]; exact hI1.mem.len64 a hwf.1
      refine ev_jcc hcR.tail.head (fun hcc => ?_) (fun hcc => ?_)
      · refine herr _ ⟨.oob, ?_⟩ ((hE1.trans (EPost.flags _) (Nat.le_refl _)))
        simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_true', decide_eq_false_iff_not,
          UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' hlt, hrax1] at hcc
        simp only [evalP, hj, bind, Except.bind]
        rw [dite_eq_right (by rw [hsz]; exact hcc)]
      · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_false', decide_eq_true_eq,
          UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' hlt, hrax1] at hcc
        refine ev_movRM hcR.tail.tail.head ⟨by simp [Tab.base64]; lomega, by simp [hT, Tab.base64]; lomega⟩
          (v := UInt64.ofNat (G.b64 a)) ?_ ?_
        · simp only [Reg64s.get64_r15, UInt64.toNat_toBitVec]
          rw [hI1.r15, hT]; exact hI1.mem.base64 a hwf.1
        refine ev_ld64 hcR.tail.tail.tail.head (v := (σ.mem.arr64 a)[j.toNat]'(by omega)) ?_ ?_
        · simp only [Reg64s.set64_rcx, hrax1]
          have := hI1.mem.get64 a hwf.1 j.toNat (by omega)
          rw [← this]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp [A]
          (try omega)
        refine ev_congr (hok ((σ.mem.arr64 a)[j.toNat]'(by omega)) _ ?_ (by simp) ?_) ?_
        · simp only [evalP, hj, bind, Except.bind]
          rw [dite_eq_left (by omega)]
        · exact hE1.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp)
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro s1 herra hE1
      refine herr s1 ?_ hE1
      obtain ⟨x, hx⟩ := herra
      exact ⟨x, by simp [evalP, hx]; rfl⟩

end

end L.Compiler
