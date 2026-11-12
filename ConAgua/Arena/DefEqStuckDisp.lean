module

public import ConAgua.Arena.DefEqStuckApp
import ConAgua.Arena.InferBodyDisp
import ConAgua.Arena.DefEqStuckEta
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import ConAgua.Arena.DefEqStuckStr
public import ConAgua.Arena.IndView
import all ConAgua.Arena.DefEq
import ConAgua.L.WordOff

@[expose] public section

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
  cases v <;> simp only [L.Ind.ViewR, L.getD_one, L.getD_two] at h <;>
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

/-- **`stuck_rest`'s model, both outcomes** (generated; `lvls_eq_c` lifted, `eta_cert` and
`stuck_irrel` by their unified models). -/
l_model drE_spec (p : Prog) (hf : p.lookup "stuck_rest" = some stuckRestL)
    (hi : p.lookup "stuck_irrel" = some stuckIrrelL)
    (hcp : CertProg p)
    (he : p.lookup "eta_cert" = some etaCertL)
    (heb : p.lookup "eta_cert_body" = some etaCertBodyL) (het : p.lookup "eta_cert_ty" = some etaCertTyL)
  fns [hf ↦ drE list]
  specs [callW_spec p n "lvls_eq_c", ecE_spec p he heb het n, siE_spec p hi hcp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem ite_ite_neg {α : Type} {c d : Prop} [Decidable c] [Decidable d] {x y : α} (h : ¬ (c ∧ d)) :
    (if c then (if d then x else y) else y) = y := by
  by_cases hc : c
  · rw [ite_eq_left hc, ite_eq_right (fun hd => h ⟨hc, hd⟩)]
  · rw [ite_eq_right hc]

/-- **`stuck_rest` refines `defeqStuck`, both outcomes**, past its string-literal and application
arms: the errors are `eta_cert`'s, `stuck_irrel`'s and the level comparison's decline (out of
level fuel, as the twin's `liftFueled`). -/
theorem dr_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b ga a1 a2 gb b1 b2 : Word) (va vb : ENodeView) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (hva : a₀.store.view (decE a) = some va) (hvb : a₀.store.view (decE b) = some vb)
    (hwa : ViewW ga a1 a2 va) (hwb : ViewW gb b1 b2 vb)
    (h1 : ¬ (ga = 8 ∧ gb = 4)) (h2 : ¬ (ga = 4 ∧ gb = 8)) (h3 : ¬ (ga = 4 ∧ gb = 4)) :
    RefE (StuckG p n) (drE p (n + 1) s₀.mem mode vis d a b ga a1 a2 gb b1 b2)
      (defeqStuck (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hirr : ∀ (st : AState) (m : Mem) (M' : ModeMaps), CoreS dn m st vis fe M' eb →
      RefE (StuckG p n) (drE.k_stuck_irrel p (siE p n m mode vis d a b))
        (stuckIrrel (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) st
        (CorePost decBool dn m vis fe M' eb ResH) := fun st m M' hS' =>
    si_tail hq hi hc (fun _ => rfl) (fun _ => rfl) n hk F hF hn m st dn vis fe M' eb mode d a b hS'
      hs.mode4 hs.eb_mode ha hb
  have hta := hwa.tag
  have htb := hwb.tag
  simp only [drE]
  -- the free variables
  by_cases hf : ga = 1 ∧ gb = 1
  · rw [ite_eq_left hf.1, ite_eq_left hf.2]
    obtain ⟨i, t, rfl⟩ := tagV_fvar (hta ▸ hf.1)
    obtain ⟨j, u, rfl⟩ := tagV_fvar (htb ▸ hf.2)
    refine RefE.of_run_eq (ds_fvar _ _ fe _ _ _ a₀ i j t u hva hvb) ?_
    by_cases e : a1 = b1
    · rw [ite_eq_left e, show (i == j) = true by simp [← hwa.2, ← hwb.2, e]]
      exact RefE.ret rfl (CorePost.ret hS rfl L.Arena.hw1)
    · rw [ite_eq_right e, show (i == j) = false by
        simpa [← hwa.2, ← hwb.2] using fun h => e (UInt64.toNat_inj.mp h)]
      exact hirr a₀ s₀.mem M hS
  rw [ite_ite_neg hf]
  simp only [drE.j1]
  -- the constants
  by_cases hcn : ga = 3 ∧ gb = 3
  · rw [ite_eq_left hcn.1, ite_eq_left hcn.2]
    obtain ⟨nm, us, rfl⟩ := tagV_const (hta ▸ hcn.1)
    obtain ⟨nm', us', rfl⟩ := tagV_const (htb ▸ hcn.2)
    obtain ⟨-, hw1, hd1, hw2, hd2⟩ := hwa
    obtain ⟨-, hw1', hd1', hw2', hd2'⟩ := hwb
    refine RefE.of_run_eq (ds_const _ _ fe _ _ _ a₀ nm nm' us us' hva hvb) ?_
    rw [← hd1, ← hd1', ← hd2, ← hd2']
    by_cases e : a1 = b1
    · rw [ite_eq_left e, ite_eq_left (by rw [e])]
      refine RefE.bind_callW (fun _ => rfl) (hc.lvlsEqC n s₀ a₀ dn vis fe M eb a2 b2 hS
        hw2 hw2' (by rw [hd2]; exact (hc.den _ _ _ _ _ _ _ hS).constLs _ _ _ hva)
        (by rw [hd2']; exact (hc.den _ _ _ _ _ _ _ hS).constLs _ _ _ hvb))
        fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
      dsimp only [drE.k_lvls_eq_c]
      -- the decline: `lvls_eq_c` ran out of fuel, the twin's `liftFueled` fails
      refine RefE.guardOpt rfl (fun z0 => ite_eq_left z0) (fun h => by unfold decO at h; grind)
        fun v hv z0 => ?_
      by_cases z1 : r₁.headD 0 = 1
      · rw [decO, ite_eq_right z0, ite_eq_left z1] at hv; cases hv
        rw [ite_eq_right (fun h => h z1)]
        exact hirr _ m₁ M₁ hS₁
      · rw [decO, ite_eq_right z0, ite_eq_right z1] at hv; cases hv
        rw [ite_eq_left z1]
        exact RefE.ret rfl (CorePost.ret hS₁ rfl L.Arena.hw1)
    · rw [ite_eq_right e]
      rw [ite_eq_right (fun h => e (decI_inj hw1 hw1' h))]
      exact hirr a₀ s₀.mem M hS
  rw [ite_ite_neg hcn]
  simp only [drE.j2]
  have hlam : ∀ (t bd : EIdx) (w1 w2 x : Word) (T : AM Bool),
      HW w1 → decE w1 = t → HW w2 → decE w2 = bd → HW x →
      T.run a₀ = (lamArmT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat
        (decE a) (decE b) t bd (decE x)).run a₀ →
      RefE (StuckG p n) (drE.k_eta_cert p n mode vis d a b (ecE p n s₀.mem mode vis d w1 w2 x)) T a₀
        (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
    intro t bd w1 w2 x T hw1 hd1 hw2 hd2 hx hT
    refine RefE.of_run_eq hT ?_
    unfold lamArmT
    cases n with
    | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
    | succ k =>
    subst hd1 hd2
    refine RefE.bind_coreE (w := id) (fun _ => rfl) (fun hG => hG.knot.mono (by omega))
      (ec_ref p hq hc k (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d w1 w2 x (by omega)
        (by omega) hs hw1 hw2 hx)
      (fun r₁ m₁ _ _ M₁ hS₁ _ => ?_)
    simp only [drE.k_eta_cert]
    by_cases e0 : r₁.headD 0 ≠ 0
    · rw [ite_eq_left e0, L.Arena.decBool_true_of e0]; exact RefE.ret rfl (CorePost.ret hS₁ rfl L.Arena.hw1)
    · rw [ite_eq_right e0, L.Arena.decBool_false_of (by simpa using e0)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hirr _ m₁ M₁ hS₁
  by_cases hl : ga = 5
  · rw [ite_eq_left hl]
    obtain ⟨t, bd, rfl⟩ := tagV_lam (hta ▸ hl)
    obtain ⟨-, hw1, hd1, hw2, hd2⟩ := hwa
    exact hlam t bd a1 a2 b _ hw1 hd1 hw2 hd2 hb (ds_lamL _ _ fe _ _ _ a₀ t bd vb hva hvb)
  rw [ite_eq_right hl]
  by_cases hl' : gb = 5
  · rw [ite_eq_left hl']
    obtain ⟨t, bd, rfl⟩ := tagV_lam (htb ▸ hl')
    obtain ⟨-, hw1, hd1, hw2, hd2⟩ := hwb
    exact hlam t bd b1 b2 a _ hw1 hd1 hw2 hd2 ha
      (ds_lamR _ _ fe _ _ _ a₀ t bd va hva hvb (by rw [← hta]; exact hl))
  rw [ite_eq_right hl']
  refine RefE.of_run_eq (ds_irrel _ _ fe _ _ _ a₀ va vb hva hvb (by rw [← hta, ← htb]; exact h1)
    (by rw [← hta, ← htb]; exact h2) (by rw [← hta, ← htb]; exact hf)
    (by rw [← hta, ← htb]; exact hcn) (by rw [← hta, ← htb]; exact h3) (by rw [← hta]; exact hl)
    (by rw [← htb]; exact hl')) ?_
  exact hirr a₀ s₀.mem M hS

theorem tagV_lit {v : ENodeView} (h : tagV v = 8) : ∃ l, v = .lit l := by
  cases v <;> simp [tagV] at h ⊢
theorem tagV_app {v : ENodeView} (h : tagV v = 4) : ∃ f x, v = .app f x := by
  cases v <;> simp [tagV] at h ⊢

/-- **`defeq_stuck`'s model, both outcomes** (generated; `e_view` lifted, the arms by their unified
models). -/
l_model dsE_spec (p : Prog) (hf : p.lookup "defeq_stuck" = some defeqStuckL)
    (hstr : p.lookup "stuck_str" = some stuckStrL) (hsa : p.lookup "stuck_app" = some stuckAppL)
    (hac : p.lookup "stuck_app_cong" = some stuckAppCongL) (hdr : p.lookup "stuck_rest" = some stuckRestL)
    (hi : p.lookup "stuck_irrel" = some stuckIrrelL)
    (hcp : CertProg p)
    (he : p.lookup "eta_cert" = some etaCertL)
    (heb : p.lookup "eta_cert_body" = some etaCertBodyL) (het : p.lookup "eta_cert_ty" = some etaCertTyL)
  fns [hf ↦ dsE list]
  specs [callW_spec p n "e_view", strE_spec p hstr hi hcp n,
    saE_spec p hsa hac hi hcp n, drE_spec p hdr hi hcp he heb het n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`defeq_stuck` refines `defeqStuck`, both outcomes**: the errors are the arms'. -/
theorem ds_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (StuckG p n) (dsE p (n + 1) s₀.mem mode vis d a b)
      (defeqStuck (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  simp only [dsE]
  cases n with
  | zero =>
    exact RefE.onlySim (Q := fun _ _ => False) (fun _ => rfl)
      (fun _ _ h => by rw [callW_zero] at h; cases h) fun _ _ h => h.elim
  | succ k =>
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => triple_of_callW (L.Ind.eView_spec p hq.eview (k + 1)
    ⟨s₀.mem, Locals.init []⟩ a) h) fun ra m₁ ⟨_, ht, hts, hne, hra⟩ => ?_
  obtain rfl : m₁ = s₀.mem := by rw [← ht, hts]
  obtain ⟨va, hva, hvra⟩ := L.Ind.eViewW_ok s₀.mem a₀ hS.arena.base a (hra ▸ hne)
  have hhda := eViewW_head s₀.mem a (hra ▸ hne)
  rw [← hra] at hvra hhda
  dsimp only [dsE.k_e_view]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => triple_of_callW (L.Ind.eView_spec p hq.eview (k + 1)
    ⟨s₀.mem, Locals.init []⟩ b) h) fun rb m₂ ⟨_, ht, hts, hne, hrb⟩ => ?_
  obtain rfl : m₂ = s₀.mem := by rw [← ht, hts]
  obtain ⟨vb, hvb, hvrb⟩ := L.Ind.eViewW_ok s₀.mem a₀ hS.arena.base b (hrb ▸ hne)
  have hhdb := eViewW_head s₀.mem b (hrb ▸ hne)
  rw [← hrb] at hvrb hhdb
  dsimp only [dsE.k_e_view_2]
  have hta := viewR_tag hvra
  have htb := viewR_tag hvrb
  by_cases c1 : ra.headD 0 = 8 ∧ rb.headD 0 = 4
  · rw [ite_eq_left c1.1, ite_eq_left c1.2]
    obtain ⟨l, rfl⟩ := tagV_lit (hta ▸ c1.1)
    obtain ⟨fo, x, rfl⟩ := tagV_app (htb ▸ c1.2)
    obtain ⟨-, hfw, hfo, -, -⟩ := hvrb
    rw [L.getD_one] at hfw hfo
    refine RefE.of_run_eq (ds_strL _ _ fe _ _ _ a₀ l fo x hva hvb) ?_
    have H := str_ref p hq hi hc k (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d
      a b 0 a (rb.tail.headD 0) l (by omega) (by omega) hs ha hb ha hfw (hhda ▸ c1.1) hva
    rw [hfo, show ((0 : Word) != 0) = false from rfl] at H
    exact RefE.tail_relist1 (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (by omega)) H
  rw [ite_ite_neg c1]
  simp only [dsE.j1]
  by_cases c2 : ra.headD 0 = 4 ∧ rb.headD 0 = 8
  · rw [ite_eq_left c2.1, ite_eq_left c2.2]
    obtain ⟨fo, x, rfl⟩ := tagV_app (hta ▸ c2.1)
    obtain ⟨l, rfl⟩ := tagV_lit (htb ▸ c2.2)
    obtain ⟨-, hfw, hfo, -, -⟩ := hvra
    rw [L.getD_one] at hfw hfo
    refine RefE.of_run_eq (ds_strR _ _ fe _ _ _ a₀ l fo x hva hvb) ?_
    have H := str_ref p hq hi hc k (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d
      a b 1 b (ra.tail.headD 0) l (by omega) (by omega) hs ha hb hb hfw (hhdb ▸ c2.2) hvb
    rw [hfo, show ((1 : Word) != 0) = true from rfl] at H
    exact RefE.tail_relist1 (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (by omega)) H
  by_cases c3 : ra.headD 0 = 4 ∧ rb.headD 0 = 4
  · rw [ite_eq_left c3.1, ite_eq_right (fun h => c2 ⟨c3.1, h⟩), ite_eq_left c3.2]
    obtain ⟨f, x, rfl⟩ := tagV_app (hta ▸ c3.1)
    obtain ⟨g, y, rfl⟩ := tagV_app (htb ▸ c3.2)
    refine RefE.of_run_eq (ds_app _ _ fe _ _ _ a₀ f x g y hva hvb) ?_
    exact RefE.tail_relist1 (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (by omega))
      (sa_ref p hq hi hc k (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b
        (by omega) (by omega) hs ha hb)
  generalize hJ : dsE.j2 p (k + 1) mode vis d a b (ra.headD 0) (ra.tail.headD 0) (ra.tail.tail.headD 0)
    (rb.headD 0) (rb.tail.headD 0) (rb.tail.tail.headD 0) s₀.mem = J2
  have e3 : ∀ x y : Except Err (List Word × Mem), (if ra.headD 0 = 4 then
      (if rb.headD 0 = 8 then x else if rb.headD 0 = 4 then y else J2) else J2) = J2 := by
    intro x y
    by_cases g : ra.headD 0 = 4
    · rw [ite_eq_left g, ite_eq_right (fun h => c2 ⟨g, h⟩), ite_eq_right (fun h => c3 ⟨g, h⟩)]
    · rw [ite_eq_right g]
  rw [e3, ← hJ]
  simp only [dsE.j2]
  exact RefE.tail_relist1 (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (by omega))
    (dr_ref p hq hi hc k (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b _ _ _
      _ _ _ va vb (by omega) (by omega) hs ha hb hva hvb (viewW_of hvra) (viewW_of hvrb) c1 c2 c3)

/-- **`defeq_stuck` refines `defeqStuck`** at the knot (`ds_ref`'s ok half). -/
@[refines ConRon.Arena.defeqStuck]
theorem defeqStuck_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "defeq_stuck" [mode, vis, d, a, b]
      (defeqStuck (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b))
      decBool s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (dsE_spec p hq.defeqStuck hq.stuckStr hq.stuckApp hq.stuckAppCong hq.stuckRest
    hq.stuckIrrel hq.toCertProg
    hq.etaCert hq.etaCertBody hq.etaCertTy (n + 1) s₀ mode vis d a b)
    (ds_ref p hq hi hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb)

end L.Arena

