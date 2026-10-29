import ConAgua.Arena.DefEqStuckStr

/-!
# `stuck_app_cong`, `stuck_app` refine `defeqStuck`'s application arm (lane `defeq`, helper `defeq-top`)

The arm is the congruence `appCongT` (both spines, the heads, then the arguments pairwise),
then `stuckIrrel` on a failure (`stuckAppT_eq`, by the monad laws).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin -/

/-- **`defeqStuck`'s application arm**, copied. -/
def stuckAppT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) : AM Bool := do
  let aa ← getAppArgs coreWalkFuel a
  let bb ← getAppArgs coreWalkFuel b
  if aa.length = bb.length then do
    let fa ← getAppFn coreWalkFuel a
    let fb ← getAppFn coreWalkFuel b
    if ← r.defeq depth fa fb then do
      if ← defEqList r fe depth aa bb then pure true
      else stuckIrrel r fe depth a b
    else stuckIrrel r fe depth a b
  else stuckIrrel r fe depth a b

/-- The arm's congruence (`stuck_app_cong`). -/
def appCongT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) : AM Bool := do
  let aa ← getAppArgs coreWalkFuel a
  let bb ← getAppArgs coreWalkFuel b
  if aa.length = bb.length then do
    let fa ← getAppFn coreWalkFuel a
    let fb ← getAppFn coreWalkFuel b
    if ← r.defeq depth fa fb then defEqList r fe depth aa bb else pure false
  else pure false

theorem stuckAppT_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    stuckAppT r fe depth a b =
      (appCongT r fe depth a b >>= fun ok => if ok then pure true else stuckIrrel r fe depth a b) := by
  simp only [stuckAppT, appCongT, bind_assoc]
  congr 1; funext aa; congr 1; funext bb
  by_cases h : aa.length = bb.length
  · simp only [h, ↓reduceIte, bind_assoc]
    congr 1; funext fa; congr 1; funext fb; congr 1; funext x
    cases x <;> simp
  · simp [h]

/-! ## The model of `stuck_app_cong` -/

/-- **`stuck_app_cong`'s model, both outcomes** (generated; the spines' callees lifted, the `defeq`
slot and `defeq_lst` through their runs). -/
l_model acE_spec (p : Prog) (hf : p.lookup "stuck_app_cong" = some stuckAppCongL)
  fns [hf ↦ acE list]
  specs [callW_spec p n "get_app_args", callW_spec p n "get_app_fn"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## The refinements -/

section congRuns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) (st : AState) (aa bb : List EIdx)
  (h1 : (getAppArgs coreWalkFuel a).run st = .ok (aa, st))
  (h2 : (getAppArgs coreWalkFuel b).run st = .ok (bb, st))
include h1 h2

theorem appCongT_ne (h : ¬ aa.length = bb.length) :
    (appCongT r fe depth a b).run st = .ok (false, st) := by
  simp only [appCongT, StateT.run_bind, h1, h2, except_ok_bind, h, ↓reduceIte]
  rfl

theorem appCongT_eq (h : aa.length = bb.length) (fa fb : EIdx)
    (h3 : (getAppFn coreWalkFuel a).run st = .ok (fa, st))
    (h4 : (getAppFn coreWalkFuel b).run st = .ok (fb, st)) :
    (appCongT r fe depth a b).run st =
      (r.defeq depth fa fb >>= fun x => if x then defEqList r fe depth aa bb else pure false).run st := by
  simp only [appCongT, StateT.run_bind, h1, h2, except_ok_bind, h, ↓reduceIte, h3, h4]

end congRuns

/-- **`stuck_app_cong` refines `appCongT`, both outcomes** (the top put back): the errors are the
`defeq` slot's and `defeq_lst`'s. -/
theorem ac_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (StuckG p n) (acE p (n + 1) s₀.mem mode vis d a b)
      (appCongT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hspn := hS.spn
  -- a leaf: the answer `x` at `m`, after a run that grew the stack; the top put back
  have leaf : ∀ (x : Word) (m : Mem) (T : AM Bool) (a y a') (M' : ModeMaps), T.run a = .ok (y, a') →
      CoreS dn m a' vis fe M' eb → KeptAll M M' eb → StackGrew s₀.mem m → y = decBool [x] → HW x →
      RefE (StuckG p n) (acE.j1 p (rdW (s₀.mem.arr64 CTL) 136) x m) T a
        (CorePost decBool dn s₀.mem vis fe M eb ResH) :=
    fun x m T a y a' M' hrun hS' hK hG hy hx =>
      RefE.ret hrun (GrowPost.restore (r := [x]) ⟨⟨M', hS', hK, hG⟩, hy, hx⟩ [x] rfl hx)
  simp only [acE]
  rcases c1 : callW p n "get_app_args" [a] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, acE.k_get_app_args.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [acE.k_get_app_args]
  cases n with
  | zero => rw [callW_zero] at c1; cases c1
  | succ k =>
  obtain ⟨hf1, hg1, hr10, htop1, aa, hargs1, hsp1⟩ := getAppArgs_callW hq.leaf.core.spine hS ha c1
  have hS₁ := hS.frame_stk hf1 (by simp) (by simp)
  rcases c2 : callW p (k + 1) "get_app_args" [b] m₁ with _ | ⟨r₂, m₂⟩
  · rw [liftE_none, acE.k_get_app_args_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [acE.k_get_app_args_2]
  obtain ⟨hf2, hg2, hr20, htop2, bb, hargs2, hsp2⟩ := getAppArgs_callW hq.leaf.core.spine hS₁ hb c2
  have hS₂ := hS₁.frame_stk hf2 (by simp) (by simp)
  have hla : aa.length = (r₁.tail.headD 0).toNat := by simpa using hsp1.size
  have hlb : bb.length = (r₂.tail.headD 0).toNat := by simpa using hsp2.size
  have hspn₁ : (m₁.arr64 SPN).size < 2 ^ 63 := hg1.size ▸ hspn
  have hspn₂ : (m₂.arr64 SPN).size < 2 ^ 63 := hg2.size ▸ hspn₁
  rcases (Classical.em (r₁.tail.headD 0 = r₂.tail.headD 0)).symm with heq | heq
  · rw [ite_eq_right heq]
    have hne : ¬ aa.length = bb.length := by
      rw [hla, hlb]; exact fun e => heq (UInt64.toNat_inj.mp e)
    exact leaf 0 m₂ _ a₀ false a₀ M (appCongT_ne _ fe _ _ _ a₀ aa bb hargs1 hargs2 hne) hS₂
      (KeptAll.refl _ _) (hg1.trans hg2) rfl hw0
  rw [ite_eq_left heq]
  have heq' : aa.length = bb.length := by rw [hla, hlb, heq]
  rcases c3 : callW p (k + 1) "get_app_fn" [a] m₂ with _ | ⟨r₃, m₃⟩
  · rw [liftE_none, acE.k_get_app_fn.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [acE.k_get_app_fn]
  obtain ⟨hm3, hh3, hgaf3⟩ := getAppFn_callW hq.leaf hS₂.arena.base ha c3
  subst hm3
  rcases c4 : callW p (k + 1) "get_app_fn" [b] m₃ with _ | ⟨r₄, m₄⟩
  · rw [liftE_none, acE.k_get_app_fn_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [acE.k_get_app_fn_2]
  obtain ⟨hm4, hh4, hgaf4⟩ := getAppFn_callW hq.leaf hS₂.arena.base hb c4
  subst hm4
  refine RefE.of_run_eq (appCongT_eq _ fe _ _ _ a₀ aa bb hargs1 hargs2 heq' _ _ hgaf3 hgaf4) ?_
  rcases c5 : callE p (k + 1) "defeq" [mode, vis, d, r₃.headD 0, r₄.headD 0] m₄ with e | ⟨r₅, m₅⟩
  · exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₄, Locals.init []⟩)
      ((hG.knot (k + 1) (Nat.le_refl _)).defeq F _ a₀ dn vis fe M eb mode d (r₃.headD 0) (r₄.headD 0)
        hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ hh3 hh4) c5
  have h₅ := CoreSpec.of_callW (s₀ := ⟨m₄, Locals.init []⟩)
    ((hk (k + 1) (Nat.le_refl _)).defeq F _ a₀ dn vis fe M eb mode d (r₃.headD 0) (r₄.headD 0) hF hn
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ hh3 hh4) (callW_of_callE c5)
  obtain ⟨M₅, hS₅, hK₅, hst₅⟩ := h₅.2.1
  refine RefE.bind_right (by rw [AM.run_of_ok _ _ h₅.1, h₅.2.2.1]) ?_
  simp only [acE.k_defeq]
  by_cases h0 : r₅.headD 0 = 0
  · rw [ite_eq_right (fun h => h h0), decBool_false_of h0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact leaf _ m₅ _ _ false _ M₅ rfl hS₅ hK₅ ((hg1.trans hg2).trans hst₅.toGrew)
      (decBool_false_of (r := [r₅.headD 0]) h0).symm h₅.2.2.2
  rw [ite_eq_left h0, decBool_true_of h0]
  simp only [↓reduceIte]
  -- the spines below the top
  have hb1 := hsp1.bound
  have hb2 := hsp2.bound
  have e1 : (spTop m₁).toNat = (r₁.headD 0).toNat + (r₁.tail.headD 0).toNat := by
    rw [htop1, ← hr10, addW_toNat (by omega)]
  have e2 : (spTop m₄).toNat = (r₂.headD 0).toNat + (r₂.tail.headD 0).toNat := by
    rw [htop2, ← hr20, addW_toNat (by have := hg1.size; omega)]
  have hle12 : (spTop m₁).toNat ≤ (spTop m₄).toNat := UInt64.le_iff_toNat_le.mp hg2.1
  have h5top : spTop m₅ = spTop m₄ := hst₅.1
  have hA : SpineR m₅ (r₁.headD 0) (r₁.tail.headD 0) aa.toArray :=
    (hsp1.grew hg2 (by omega) hspn₁).keep hst₅.size hst₅.below (by omega) hspn₂
  have hB : SpineR m₅ (r₂.headD 0) (r₂.tail.headD 0) bb.toArray :=
    hsp2.keep hst₅.size hst₅.below (by omega) hspn₂
  rcases c6 : callE p (k + 1) "defeq_lst"
      [mode, vis, d, r₁.headD 0, r₁.tail.headD 0, r₂.headD 0, r₂.tail.headD 0] m₅ with e | ⟨r₆, m₆⟩
  · exact fun hG => CoreSpecE.of_callE (s₀ := ⟨m₅, Locals.init []⟩)
      (hG.lst k (hk.mono (by omega)) (hG.knot.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₅
        eb mode d (r₁.headD 0) (r₁.tail.headD 0) (r₂.headD 0) (r₂.tail.headD 0) aa.toArray bb.toArray
        ⟨hS₅, hs.mode4, hs.eb_mode⟩ hA hB (by rw [h5top]; omega) (by rw [h5top]; omega)) c6
  have h₆ := CoreSpec.of_callW (s₀ := ⟨m₅, Locals.init []⟩)
    (defeqLst_at p hc (k + 1) hk F hF hn ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode d (r₁.headD 0)
      (r₁.tail.headD 0) (r₂.headD 0) (r₂.tail.headD 0) aa.toArray bb.toArray
      ⟨hS₅, hs.mode4, hs.eb_mode⟩ hA hB (by rw [h5top]; omega) (by rw [h5top]; omega))
    (callW_of_callE c6)
  obtain ⟨M₆, hS₆, hK₆, hst₆⟩ := h₆.2.1
  simp only [acE.k_defeq_lst]
  exact leaf _ m₆ _ _ _ _ M₆ (AM.run_of_ok _ _ h₆.1) hS₆ (hK₅.trans hK₆)
    (((hg1.trans hg2).trans hst₅.toGrew).trans hst₆.toGrew) h₆.2.2.1 h₆.2.2.2

/-- **`stuck_app_cong` refines `appCongT`** at the knot (`ac_ref`'s ok half). -/
@[refines_part ConRon.Arena.defeqStuck "the application arm's congruence (appCongT)"]
theorem appCong_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "stuck_app_cong" [mode, vis, d, a, b]
      (appCongT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (acE_spec p hq.stuckAppCong (n + 1) s₀ mode vis d a b)
    (ac_ref p hq hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb)

/-- **`stuck_app`'s model, both outcomes** (generated; `stuck_app_cong` and `stuck_irrel` by their
unified models). -/
l_model saE_spec (p : Prog) (hf : p.lookup "stuck_app" = some stuckAppL)
    (hac : p.lookup "stuck_app_cong" = some stuckAppCongL)
    (hi : p.lookup "stuck_irrel" = some stuckIrrelL)
    (hc : p.lookup "struct_eta_cert" = some structEtaCertL)
    (hw : p.lookup "struct_eta_cert_with" = some structEtaCertWithL)
    (hb : p.lookup "struct_eta_cert_wtb" = some structEtaCertWtbL)
    (hg : p.lookup "struct_eta_cert_go" = some structEtaCertGoL)
    (ht : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL)
    (hu : p.lookup "struct_unit_cert" = some structUnitCertL)
    (hh : p.lookup "struct_unit_head" = some structUnitHeadL)
    (hut : p.lookup "struct_unit_tail" = some structUnitTailL)
  fns [hf ↦ saE list]
  specs [acE_spec p hac n, siE_spec p hi hc hw hb hg ht hu hh hut n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`stuck_app` refines `defeqStuck`'s application arm (`stuckAppT`), both outcomes**: the errors
are the congruence's and `stuck_irrel`'s. -/
theorem sa_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (StuckG p n) (saE p (n + 1) s₀.mem mode vis d a b)
      (stuckAppT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  rw [stuckAppT_eq]
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ k =>
  simp only [saE]
  refine RefE.bind_coreE (w := id) (fun _ => rfl) (fun hG => hG.mono (by omega))
    (ac_ref p hq hc k (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b (by omega)
      (by omega) hs ha hb)
    (fun r₁ m₁ _ _ M₁ hS₁ _ => ?_)
  simp only [saE.k_stuck_app_cong]
  by_cases h0 : r₁.headD 0 ≠ 0
  · rw [ite_eq_left h0, decBool_true_of h0]; exact RefE.ret rfl (CorePost.ret hS₁ rfl hw1)
  rw [ite_eq_right h0, decBool_false_of (by simpa using h0)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact si_tail hq hi hc (fun _ => rfl) (fun _ => rfl) (k + 1) hk F hF hn m₁ _ dn vis fe M₁ eb mode d
    a b hS₁ hs.mode4 hs.eb_mode ha hb

/-- **`stuck_app` refines `defeqStuck`'s application arm** at the knot (`sa_ref`'s ok half). -/
@[refines_part ConRon.Arena.defeqStuck "the application arm (stuckAppT)"]
theorem stuckApp_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "stuck_app" [mode, vis, d, a, b]
      (stuckAppT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (saE_spec p hq.stuckApp hq.stuckAppCong hq.stuckIrrel hq.setCert hq.setWith hq.setWtb
    hq.setGo hq.setTail hq.sunit hq.suHead hq.suTail (n + 1) s₀ mode vis d a b)
    (sa_ref p hq hi hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb)

end L.Arena
