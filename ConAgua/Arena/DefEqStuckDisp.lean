import ConAgua.Arena.DefEqStuckApp

/-!
# `defeq_stuck` refines `defeqStuck` (lane `defeq`, helper `defeq-top`)

The dispatcher: both views (`e_view`), then the arms by the tags in the twin's match order
(`stuck_str`, the free variables, the constants, `stuck_app`, `eta_cert` on either side, else
`stuck_irrel`). The twin's match, one run lemma per arm (`ds_*`), the fallthrough by cases on
both views (`ds_irrel`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- The tag word of a view (`e_view`'s first result). -/
def tagV : ENodeView → Word
  | .bvar _ => 0 | .fvar _ _ => 1 | .sort _ => 2 | .const _ _ => 3 | .app _ _ => 4
  | .lam _ _ => 5 | .forallE _ _ => 6 | .letE _ _ _ => 7 | .lit _ => 8 | .proj _ _ _ => 9

theorem viewR_tag {r : List Word} {v : ENodeView} (h : L.Ind.ViewR r v) : r.headD 0 = tagV v := by
  cases v <;> first | exact h.1 | exact h

/-! ## The twin's arms -/

/-- `defeqStuck`'s λ arms: η on the λ's side, else the fallback. -/
def lamArmT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b t bd x : EIdx) :
    AM Bool := do
  if ← etaCert mode r fe depth t bd x then pure true else stuckIrrel r fe depth a b

section dsRuns
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx)
  (st : AState)

theorem ds_strL (l : ConLeche.Literal) (fo x : EIdx) (hva : st.store.view a = some (.lit l))
    (hvb : st.store.view b = some (.app fo x)) :
    (defeqStuck mode r fe depth a b).run st = (stuckStrT r fe depth a b false l fo).run st := by
  simp only [defeqStuck, StateT.run_bind, view_run _ _ _ hva, view_run _ _ _ hvb, except_ok_bind]
  cases l <;> rfl

theorem ds_strR (l : ConLeche.Literal) (fo x : EIdx) (hva : st.store.view a = some (.app fo x))
    (hvb : st.store.view b = some (.lit l)) :
    (defeqStuck mode r fe depth a b).run st = (stuckStrT r fe depth a b true l fo).run st := by
  simp only [defeqStuck, StateT.run_bind, view_run _ _ _ hva, view_run _ _ _ hvb, except_ok_bind]
  cases l <;> rfl

theorem ds_fvar (i j : Nat) (t u : EIdx) (hva : st.store.view a = some (.fvar i t))
    (hvb : st.store.view b = some (.fvar j u)) :
    (defeqStuck mode r fe depth a b).run st =
      (if i == j then pure true else stuckIrrel r fe depth a b).run st := by
  simp only [defeqStuck, StateT.run_bind, view_run _ _ _ hva, view_run _ _ _ hvb, except_ok_bind]

theorem ds_const (n n' : NIdx) (us us' : LsIdx) (hva : st.store.view a = some (.const n us))
    (hvb : st.store.view b = some (.const n' us')) :
    (defeqStuck mode r fe depth a b).run st =
      (if n = n' then (do
          if ← liftFueled "level comparison" (← lvlsEq? us us') then pure true
          else stuckIrrel r fe depth a b)
        else stuckIrrel r fe depth a b).run st := by
  simp only [defeqStuck, StateT.run_bind, view_run _ _ _ hva, view_run _ _ _ hvb, except_ok_bind]

theorem ds_app (f x g y : EIdx) (hva : st.store.view a = some (.app f x))
    (hvb : st.store.view b = some (.app g y)) :
    (defeqStuck mode r fe depth a b).run st = (stuckAppT r fe depth a b).run st := by
  simp only [defeqStuck, StateT.run_bind, view_run _ _ _ hva, view_run _ _ _ hvb, except_ok_bind]
  rfl

theorem ds_lamL (t bd : EIdx) (vb : ENodeView) (hva : st.store.view a = some (.lam t bd))
    (hvb : st.store.view b = some vb) :
    (defeqStuck mode r fe depth a b).run st = (lamArmT mode r fe depth a b t bd b).run st := by
  simp only [defeqStuck, StateT.run_bind, view_run _ _ _ hva, view_run _ _ _ hvb, except_ok_bind]
  cases vb <;> rfl

theorem ds_lamR (t bd : EIdx) (va : ENodeView) (hva : st.store.view a = some va)
    (hvb : st.store.view b = some (.lam t bd)) (h5 : tagV va ≠ 5) :
    (defeqStuck mode r fe depth a b).run st = (lamArmT mode r fe depth a b t bd a).run st := by
  simp only [defeqStuck, StateT.run_bind, view_run _ _ _ hva, view_run _ _ _ hvb, except_ok_bind]
  cases va <;> first | rfl | (exact absurd rfl h5)

theorem ds_irrel (va vb : ENodeView) (hva : st.store.view a = some va)
    (hvb : st.store.view b = some vb)
    (h1 : ¬ (tagV va = 8 ∧ tagV vb = 4)) (h2 : ¬ (tagV va = 4 ∧ tagV vb = 8))
    (h3 : ¬ (tagV va = 1 ∧ tagV vb = 1)) (h4 : ¬ (tagV va = 3 ∧ tagV vb = 3))
    (h5 : ¬ (tagV va = 4 ∧ tagV vb = 4)) (h6 : tagV va ≠ 5) (h7 : tagV vb ≠ 5) :
    (defeqStuck mode r fe depth a b).run st = (stuckIrrel r fe depth a b).run st := by
  simp only [defeqStuck, StateT.run_bind, view_run _ _ _ hva, view_run _ _ _ hvb, except_ok_bind]
  cases va <;> cases vb <;> first | rfl | (simp [tagV] at h1 h2 h3 h4 h5 h6 h7)

end dsRuns

/-! ## The model of `defeq_stuck` -/

section dsK
variable (p : Prog) (n : Nat) (mode vis d a b : Word)

def dsLv (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then none
    else if r.headD 0 ≠ 1 then some (1, m)
    else call1W p n "stuck_irrel" [mode, vis, d, a, b] m

def dsEta (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then some (1, m) else call1W p n "stuck_irrel" [mode, vis, d, a, b] m

/-- **The model of `stuck_rest`**: the free-variable, constant and λ arms, the fallback. -/
def drK (ga a1 a2 gb b1 b2 : Word) (m : Mem) : Option (Word × Mem) :=
  if ga = 1 ∧ gb = 1 then
    (if a1 = b1 then some (1, m) else call1W p n "stuck_irrel" [mode, vis, d, a, b] m)
  else if ga = 3 ∧ gb = 3 then
    (if a1 = b1 then dsLv p n mode vis d a b (callW p n "lvls_eq_c" [a2, b2] m)
     else call1W p n "stuck_irrel" [mode, vis, d, a, b] m)
  else if ga = 5 then dsEta p n mode vis d a b (callW p n "eta_cert" [mode, vis, d, a1, a2, b] m)
  else if gb = 5 then dsEta p n mode vis d a b (callW p n "eta_cert" [mode, vis, d, b1, b2, a] m)
  else call1W p n "stuck_irrel" [mode, vis, d, a, b] m

/-- The arms by the two views' words. -/
def dsArm (ga a1 a2 gb b1 b2 : Word) (m : Mem) : Option (Word × Mem) :=
  if ga = 8 ∧ gb = 4 then call1W p n "stuck_str" [mode, vis, d, a, b, 0, a, b1] m
  else if ga = 4 ∧ gb = 8 then call1W p n "stuck_str" [mode, vis, d, a, b, 1, b, a1] m
  else if ga = 4 ∧ gb = 4 then call1W p n "stuck_app" [mode, vis, d, a, b] m
  else call1W p n "stuck_rest" [mode, vis, d, a, b, ga, a1, a2, gb, b1, b2] m

/-- **The model of `defeq_stuck`.** -/
def dsK (m : Mem) : Option (Word × Mem) :=
  match callW p n "e_view" [a] m with
  | none => none
  | some (ra, m₁) =>
    match callW p n "e_view" [b] m₁ with
    | none => none
    | some (rb, m₂) => dsArm p n mode vis d a b (ra.headD 0) (ra.tail.headD 0) (ra.tail.tail.headD 0)
        (rb.headD 0) (rb.tail.headD 0) (rb.tail.tail.headD 0) m₂

end dsK

theorem stuckRest_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St)
    (mode vis d a b ga a1 a2 gb b1 b2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "stuck_rest" [mode, vis, d, a, b, ga, a1, a2, gb, b1, b2]
    ⦃fun r s' => LocEq s' s₀ ∧ drK p n mode vis d a b ga a1 a2 gb b1 b2 s₀.mem =
      some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.stuckRest]
  simp only [callFn, stuckRestL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "stuck_irrel",
      callW_spec p n "lvls_eq_c", callW_spec p n "eta_cert"] <;>
  simp_all [drK, dsLv, dsEta, call1W, LocEq, St.setLocs_cons, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

theorem defeqStuck_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_stuck" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ dsK p n mode vis d a b s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.defeqStuck]
  simp only [callFn, defeqStuckL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "e_view",
      callW_spec p n "stuck_str", callW_spec p n "stuck_app", callW_spec p n "stuck_rest"] <;>
  simp_all [dsK, dsArm, call1W, LocEq, St.setLocs_cons, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

/-! ## Leaves at any fuel -/

theorem etaCert_at (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d ty1 body1 b : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      HW ty1 → HW body1 → HW b →
      CoreSpec p n "eta_cert" [mode, vis, d, ty1, body1, b]
        (etaCert (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty1) (decE body1)
          (decE b)) decBool s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, t, bd, b, hF, hn, hs, h1, h2, h3 =>
      etaCert_refines p hq hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d t bd b
        (by omega) (by omega) hs h1 h2 h3

theorem stuckApp_at (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d a b : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      HW a → HW b →
      CoreSpec p n "stuck_app" [mode, vis, d, a, b]
        (stuckAppT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
        s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, b, hF, hn, hs, h1, h2 =>
      stuckApp_refines p hq hi hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b
        (by omega) (by omega) hs h1 h2

theorem stuckStr_at (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d a b side lt fo : Word) (l : ConLeche.Literal), n ≤ F → n ≤ 2 ^ 62 →
      SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b → HW lt → HW fo → lt >>> 28 = 8 →
      a₀.store.view (decE lt) = some (.lit l) →
      CoreSpec p n "stuck_str" [mode, vis, d, a, b, side, lt, fo]
        (stuckStrT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (side != 0) l
          (decE fo)) decBool s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, b, side, lt, fo, l, hF, hn, hs, h1, h2, h3,
      h4, h5, h6 =>
      stuckStr_refines p hq hi hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b side lt fo
        l (by omega) (by omega) hs h1 h2 h3 h4 h5 h6

/-! ## `stuck_rest` -/

/-- The words `e_view` answers for a view, as `stuck_rest` uses them. -/
def ViewW (g w1 w2 : Word) : ENodeView → Prop
  | .fvar i _ => g = 1 ∧ w1.toNat = i
  | .const nm us => g = 3 ∧ HW w1 ∧ decI w1 = nm ∧ HW w2 ∧ decI w2 = us
  | .lam t bd => g = 5 ∧ HW w1 ∧ decE w1 = t ∧ HW w2 ∧ decE w2 = bd
  | v => g = tagV v

theorem ViewW.tag {g w1 w2 : Word} {v : ENodeView} (h : ViewW g w1 w2 v) : g = tagV v := by
  cases v <;> first | exact h.1 | exact h

theorem viewW_of {r : List Word} {v : ENodeView} (h : L.Ind.ViewR r v) :
    ViewW (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) v := by
  cases v <;> simp only [L.Ind.ViewR, getD1, getD2] at h <;>
    first
    | exact ⟨h.1, h.2.1⟩
    | exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    | exact h.1
    | exact h

theorem tagV_fvar {v : ENodeView} (h : tagV v = 1) : ∃ i t, v = .fvar i t := by
  cases v <;> simp [tagV] at h ⊢
theorem tagV_const {v : ENodeView} (h : tagV v = 3) : ∃ nm us, v = .const nm us := by
  cases v <;> simp [tagV] at h ⊢
theorem tagV_lam {v : ENodeView} (h : tagV v = 5) : ∃ t bd, v = .lam t bd := by
  cases v <;> simp [tagV] at h ⊢

/-- **`stuck_rest` refines `defeqStuck`** past its string-literal and application arms. -/
@[refines_part ConRon.Arena.defeqStuck "the free-variable, constant and λ arms"]
theorem stuckRest_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b ga a1 a2 gb b1 b2 : Word) (va vb : ENodeView) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (hva : a₀.store.view (decE a) = some va) (hvb : a₀.store.view (decE b) = some vb)
    (hwa : ViewW ga a1 a2 va) (hwb : ViewW gb b1 b2 vb)
    (h1 : ¬ (ga = 8 ∧ gb = 4)) (h2 : ¬ (ga = 4 ∧ gb = 8)) (h3 : ¬ (ga = 4 ∧ gb = 4)) :
    CoreSpec p (n + 1) "stuck_rest" [mode, vis, d, a, b, ga, a1, a2, gb, b1, b2]
      (defeqStuck (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
      decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (stuckRest_spec p hq n s₀ mode vis d a b ga a1 a2 gb b1 b2)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hirr : ∀ (st : AState) (m : Mem) (M' : ModeMaps), CoreS dn m st vis fe M' eb →
      call1W p n "stuck_irrel" [mode, vis, d, a, b] m = some (r.headD 0, s'.mem) →
      CoreRef (stuckIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) st decBool
        dn m vis fe M' eb r s'.mem := fun st m M' hS' hc' =>
    CoreSpec.of_call1W (s₀ := ⟨m, Locals.init []⟩)
      (stuckIrrel_at p hq hi hc n hk F _ st dn vis fe M' eb mode d a b hF hn
        ⟨hS', hs.mode4, hs.eb_mode⟩ ha hb) (fun r r' h => by simp only [decBool, h]) hc'
  have hta := hwa.tag
  have htb := hwb.tag
  simp only [drK] at hW
  -- the free variables
  by_cases hf : ga = 1 ∧ gb = 1
  · rw [ite_eq_left hf] at hW
    obtain ⟨i, t, rfl⟩ := tagV_fvar (hta ▸ hf.1)
    obtain ⟨j, u, rfl⟩ := tagV_fvar (htb ▸ hf.2)
    refine coreRef_congr (ds_fvar _ _ fe _ _ _ a₀ i j t u hva hvb) ?_
    have hij : (i == j) = decide (a1 = b1) := by
      rw [← hwa.2, ← hwb.2]
      by_cases e : a1 = b1
      · simp [e]
      · have : a1.toNat ≠ b1.toNat := fun e' => e (UInt64.toNat_inj.mp e')
        simp [e, this]
    rw [hij]
    by_cases e : a1 = b1
    · simp only [e, ↓reduceIte, decide_true] at hW ⊢
      exact coreRef_true hS hW
    · simp only [e, ↓reduceIte, decide_false, Bool.false_eq_true] at hW ⊢
      exact hirr a₀ s.mem M hS hW
  rw [ite_eq_right hf] at hW
  -- the constants
  by_cases hcn : ga = 3 ∧ gb = 3
  · rw [ite_eq_left hcn] at hW
    obtain ⟨nm, us, rfl⟩ := tagV_const (hta ▸ hcn.1)
    obtain ⟨nm', us', rfl⟩ := tagV_const (htb ▸ hcn.2)
    obtain ⟨-, hw1, hd1, hw2, hd2⟩ := hwa
    obtain ⟨-, hw1', hd1', hw2', hd2'⟩ := hwb
    refine coreRef_congr (ds_const _ _ fe _ _ _ a₀ nm nm' us us' hva hvb) ?_
    rw [← hd1, ← hd1', ← hd2, ← hd2']
    by_cases e : a1 = b1
    · rw [ite_eq_left e] at hW
      rw [ite_eq_left (by rw [e])]
      obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
      have h₁ := CoreSpec.of_callW (hc.lvlsEqC n s a₀ dn vis fe M eb a2 b2 hS hw2 hw2'
        (by rw [hd2]; exact (hc.den _ _ _ _ _ _ _ hS).constLs _ _ _ hva)
        (by rw [hd2']; exact (hc.den _ _ _ _ _ _ _ hS).constLs _ _ _ hvb)) hc1
      refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
      simp only [dsLv] at hW1
      have z0 : ¬ r₁.headD 0 = 0 := fun z0 => by simp only [z0, ↓reduceIte] at hW1; cases hW1
      simp only [z0, ↓reduceIte] at hW1
      by_cases z1 : r₁.headD 0 = 1
      · simp only [z1, ne_eq, not_true_eq_false, ↓reduceIte] at hW1
        have : decO (r₁.headD 0) = some false := by unfold decO; rw [ite_eq_right z0, ite_eq_left z1]
        rw [this]
        exact hirr _ m₁ M₁ hS₁ hW1
      · simp only [z1, ne_eq, not_false_eq_true, ↓reduceIte] at hW1
        have : decO (r₁.headD 0) = some true := by unfold decO; rw [ite_eq_right z0, ite_eq_right z1]
        rw [this]
        exact coreRef_true hS₁ hW1
    · rw [ite_eq_right e] at hW
      rw [ite_eq_right (fun h => e (decI_inj hw1 hw1' h))]
      exact hirr a₀ s.mem M hS hW
  rw [ite_eq_right hcn] at hW
  have hlam : ∀ (t bd : EIdx) (w1 w2 x : Word) (T : AM Bool),
      HW w1 → decE w1 = t → HW w2 → decE w2 = bd → HW x →
      T.run a₀ = (lamArmT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
        (decE a) (decE b) t bd (decE x)).run a₀ →
      dsEta p n mode vis d a b (callW p n "eta_cert" [mode, vis, d, w1, w2, x] s.mem) =
        some (r.headD 0, s'.mem) →
      CoreRef T a₀ decBool dn s.mem vis fe M eb r s'.mem := by
    intro t bd w1 w2 x T hw1 hd1 hw2 hd2 hx hT hW
    refine coreRef_congr hT ?_
    unfold lamArmT
    obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
    have h₁ := CoreSpec.of_callW (etaCert_at p hq hc n hk F s a₀ dn vis fe M eb mode d w1 w2 x hF hn hs
      hw1 hw2 hx) hc1
    rw [hd1, hd2] at h₁
    refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
    simp only [dsEta] at hW1
    by_cases e0 : r₁.headD 0 ≠ 0
    · simp only [e0, ne_eq, not_false_eq_true, ↓reduceIte] at hW1
      rw [decBool_true_of e0]; exact coreRef_true hS₁ hW1
    · simp only [e0, ↓reduceIte] at hW1
      rw [decBool_false_of (by simpa using e0)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hirr _ m₁ M₁ hS₁ hW1
  by_cases hl : ga = 5
  · rw [ite_eq_left hl] at hW
    obtain ⟨t, bd, rfl⟩ := tagV_lam (hta ▸ hl)
    obtain ⟨-, hw1, hd1, hw2, hd2⟩ := hwa
    exact hlam t bd a1 a2 b _ hw1 hd1 hw2 hd2 hb
      (ds_lamL _ _ fe _ _ _ a₀ t bd vb hva hvb) hW
  rw [ite_eq_right hl] at hW
  by_cases hl' : gb = 5
  · rw [ite_eq_left hl'] at hW
    obtain ⟨t, bd, rfl⟩ := tagV_lam (htb ▸ hl')
    obtain ⟨-, hw1, hd1, hw2, hd2⟩ := hwb
    exact hlam t bd b1 b2 a _ hw1 hd1 hw2 hd2 ha
      (ds_lamR _ _ fe _ _ _ a₀ t bd va hva hvb (by rw [← hta]; exact hl)) hW
  rw [ite_eq_right hl'] at hW
  refine coreRef_congr (ds_irrel _ _ fe _ _ _ a₀ va vb hva hvb (by rw [← hta, ← htb]; exact h1)
    (by rw [← hta, ← htb]; exact h2) (by rw [← hta, ← htb]; exact hf)
    (by rw [← hta, ← htb]; exact hcn) (by rw [← hta, ← htb]; exact h3) (by rw [← hta]; exact hl)
    (by rw [← htb]; exact hl')) ?_
  exact hirr a₀ s.mem M hS hW

theorem stuckRest_at (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d a b ga a1 a2 gb b1 b2 : Word) (va vb : ENodeView), n ≤ F → n ≤ 2 ^ 62 →
      SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
      a₀.store.view (decE a) = some va → a₀.store.view (decE b) = some vb →
      ViewW ga a1 a2 va → ViewW gb b1 b2 vb →
      ¬ (ga = 8 ∧ gb = 4) → ¬ (ga = 4 ∧ gb = 8) → ¬ (ga = 4 ∧ gb = 4) →
      CoreSpec p n "stuck_rest" [mode, vis, d, a, b, ga, a1, a2, gb, b1, b2]
        (defeqStuck (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
        decBool s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, b, ga, a1, a2, gb, b1, b2, va, vb, hF, hn,
      hs, ha, hb, hva, hvb, hwa, hwb, h1, h2, h3 =>
      stuckRest_refines p hq hi hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b ga a1 a2
        gb b1 b2 va vb (by omega) (by omega) hs ha hb hva hvb hwa hwb h1 h2 h3

theorem tagV_lit {v : ENodeView} (h : tagV v = 8) : ∃ l, v = .lit l := by
  cases v <;> simp [tagV] at h ⊢
theorem tagV_app {v : ENodeView} (h : tagV v = 4) : ∃ f x, v = .app f x := by
  cases v <;> simp [tagV] at h ⊢

/-- **`defeq_stuck` refines `defeqStuck`** at the knot. -/
@[refines ConRon.Arena.defeqStuck]
theorem defeqStuck_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "defeq_stuck" [mode, vis, d, a, b]
      (defeqStuck (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
      decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqStuck_spec p hq n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold dsK at hW
  cases hca : callW p n "e_view" [a] s.mem with
  | none => rw [hca] at hW; cases hW
  | some q =>
  obtain ⟨ra, m₁⟩ := q
  rw [hca] at hW; dsimp only at hW
  obtain ⟨t₁, ht₁, hts₁, hne₁, hra⟩ := triple_of_callW (L.Ind.eView_spec p hq.eview n s a) hca
  have hm₁ : m₁ = s.mem := by rw [← ht₁, hts₁]
  subst hm₁
  cases hcb : callW p n "e_view" [b] s.mem with
  | none => rw [hcb] at hW; cases hW
  | some q =>
  obtain ⟨rb, m₂⟩ := q
  rw [hcb] at hW; dsimp only at hW
  obtain ⟨t₂, ht₂, hts₂, hne₂, hrb⟩ := triple_of_callW (L.Ind.eView_spec p hq.eview n ⟨s.mem, Locals.init []⟩ b) hcb
  have hm₂ : m₂ = s.mem := by rw [← ht₂, hts₂]
  subst hm₂
  have hne₁' : L.Ind.eViewW s.mem a ≠ [] := hra ▸ hne₁
  have hne₂' : L.Ind.eViewW s.mem b ≠ [] := hrb ▸ hne₂
  have hhda := eViewW_head s.mem a hne₁'
  have hhdb := eViewW_head s.mem b hne₂'
  rw [← hra] at hhda
  rw [← hrb] at hhdb
  obtain ⟨va, hva, hvra⟩ := L.Ind.eViewW_ok s.mem a₀ hS.arena.1 a hne₁'
  obtain ⟨vb, hvb, hvrb⟩ := L.Ind.eViewW_ok s.mem a₀ hS.arena.1 b hne₂'
  rw [← hra] at hvra
  rw [← hrb] at hvrb
  have hta := viewR_tag hvra
  have htb := viewR_tag hvrb
  have hsl : SlotPre ⟨s.mem, Locals.init []⟩ a₀ dn vis fe M eb mode := ⟨hS, hs.mode4, hs.eb_mode⟩
  have fin : ∀ {T : AM Bool} {f : FnName} {vs : List Word},
      CoreSpec p n f vs T decBool ⟨s.mem, Locals.init []⟩ a₀ dn vis fe M eb →
      call1W p n f vs s.mem = some (r.headD 0, s'.mem) →
      CoreRef T a₀ decBool dn s.mem vis fe M eb r s'.mem :=
    fun hsp h => CoreSpec.of_call1W hsp (fun r r' h => by simp only [decBool, h]) h
  simp only [dsArm] at hW
  by_cases c1 : ra.headD 0 = 8 ∧ rb.headD 0 = 4
  · rw [ite_eq_left c1] at hW
    obtain ⟨l, rfl⟩ := tagV_lit (hta ▸ c1.1)
    obtain ⟨fo, x, rfl⟩ := tagV_app (htb ▸ c1.2)
    obtain ⟨-, hfw, hfo, -, -⟩ := hvrb
    rw [getD1] at hfw hfo
    refine coreRef_congr (ds_strL _ _ fe _ _ _ a₀ l fo x hva hvb) ?_
    have h := fin (stuckStr_at p hq hi hc n hk F _ a₀ dn vis fe M eb mode d a b 0 a
      (rb.tail.headD 0) l hF hn hsl ha hb ha hfw (by rw [← hhda]; exact c1.1) hva) hW
    rw [hfo] at h
    simpa using h
  rw [ite_eq_right c1] at hW
  by_cases c2 : ra.headD 0 = 4 ∧ rb.headD 0 = 8
  · rw [ite_eq_left c2] at hW
    obtain ⟨fo, x, rfl⟩ := tagV_app (hta ▸ c2.1)
    obtain ⟨l, rfl⟩ := tagV_lit (htb ▸ c2.2)
    obtain ⟨-, hfw, hfo, -, -⟩ := hvra
    rw [getD1] at hfw hfo
    refine coreRef_congr (ds_strR _ _ fe _ _ _ a₀ l fo x hva hvb) ?_
    have h := fin (stuckStr_at p hq hi hc n hk F _ a₀ dn vis fe M eb mode d a b 1 b
      (ra.tail.headD 0) l hF hn hsl ha hb hb hfw (by rw [← hhdb]; exact c2.2) hvb) hW
    rw [hfo] at h
    simpa using h
  rw [ite_eq_right c2] at hW
  by_cases c3 : ra.headD 0 = 4 ∧ rb.headD 0 = 4
  · rw [ite_eq_left c3] at hW
    obtain ⟨f, x, rfl⟩ := tagV_app (hta ▸ c3.1)
    obtain ⟨g, y, rfl⟩ := tagV_app (htb ▸ c3.2)
    refine coreRef_congr (ds_app _ _ fe _ _ _ a₀ f x g y hva hvb) ?_
    exact fin (stuckApp_at p hq hi hc n hk F _ a₀ dn vis fe M eb mode d a b hF hn hsl ha hb) hW
  rw [ite_eq_right c3] at hW
  exact fin (stuckRest_at p hq hi hc n hk F _ a₀ dn vis fe M eb mode d a b _ _ _ _ _ _ va vb hF hn
    hsl ha hb hva hvb (viewW_of hvra) (viewW_of hvrb) c1 c2 c3) hW

end L.Arena
