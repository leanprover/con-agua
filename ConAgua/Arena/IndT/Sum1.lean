import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndSumSpec.StructProjArgP

/-!
# `whnfTelescope` under `StageC` (lane `indstaget`)

`whnf_telescope`'s model at `realCall p`, from `StageC` and con-ron's preconditions of
`whnfTelescope_spec` (the type denotes and is scoped at the depth `i`), its twin side transcribed
from that spec's proof: `whnf` (`whnfC_rsim`: the answer denotes, scoped), the view
(`denote_forallE_inv`), `internE` of the binder's variable (`internE_run`: a `PStep`),
`instantiate1Fast` (`instantiate1Fast_run`: a `PStep` by `PStep.of_caches`, the instantiated body
denotes), the recursion one level deeper (`WScoped.instantiate1`), the cons (L only).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `whnf_telescope`'s model reads. -/
structure WtProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  view : p.lookup "e_view" = some eView
  ff : p.lookup "fvar_find" = some fvarFind
  fp : p.lookup "fvar_push" = some fvarPush
  ifv : p.lookup "intern_fvar" = some internFVar
  wt : p.lookup "whnf_telescope" = some whnfTelescopeL
  i1 : I1Prog p

/-- **The model of `whnf_telescope`, both outcomes**: `whnf_top` and `e_view` through their runs,
`intern_fvar`, `instantiate1_fast` and `sl_cons` (outside the verdict closure) through their
`Option` models, the recursion through the model itself. -/
l_model wtE_spec (p : Prog) (hP : WtProg p)
  fns [hP.wt ↦ wtE]
  specs [internFVar_spec p hP.ff hP.fp hP.ifv n, i1F_spec p hP.i1 n,
    slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `whnf_telescope`'s error arms assume: the no-verdict callees closed, `whnf_top`'s claim
(`WhnfTopE`, from the error knot). -/
structure WtG (p : Prog) : Prop where
  nv : closedNV p _root_.L.Checker.nvFns = true
  whnf : WhnfTopE p

/-- What `whnf_telescope` gives besides the twin's telescope `x` (from `m`): the binders' domains
as an `IW` slice, the sort as a word, the stage relation, growth, the walk memos. -/
structure WtPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (b : List Word × Mem) (a' : AState) (x : List EIdx × LIdx) : Prop where
  stage : StageC dn vis fe env b.2 a'
  grow : IWGrow m b.2
  doms : decHL b.2 (b.1.headD 0).toNat (b.1.tail.headD 0).toNat = some x.1
  top : (b.1.headD 0).toNat + (b.1.tail.headD 0).toNat ≤ iwTop b.2
  sort32 : (b.1.tail.tail.headD 0).toNat < 2 ^ 32
  sort : decI (b.1.tail.tail.headD 0) = x.2
  abs : AbsOK b.2

/-- The arms of `wtArm` the L guards leave (not a sort at `0`, not a `∀` at `n + 1`) are the
twin's `.invalid` failures. -/
theorem wtArm_fail (fe : IFEnv) (i : Nat) {vv : ENodeView} {v : List Word} {n : Word}
    (hVR : ViewR v vv) (h1 : ¬ (v.headD 0 = 2 ∧ n = 0)) (h2 : ¬ (v.headD 0 = 6 ∧ n ≠ 0)) :
    ∃ msg, wtArm V fe i vv n.toNat = ConRon.Arena.fail (.invalid msg) := by
  by_cases hn : n = 0
  · subst hn
    cases vv with
    | sort u => exact absurd ⟨hVR.1, rfl⟩ h1
    | _ => exact ⟨_, rfl⟩
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (fun h0 => hn (UInt64.toNat_inj.mp (by simpa using h0)))
    rw [hk]
    cases vv with
    | forallE ty b => exact absurd ⟨hVR.1, hn⟩ h2
    | _ => exact ⟨_, rfl⟩

section sims
variable {p : Prog} (hq : KnotStageProg p) (hP : WtProg p) {dn : NIdx → Option ConLeche.Name}
  {vis : Word} {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq hP henv in
/-- **`whnf_telescope` refines `whnfTelescope .verified`, both outcomes**, under `StageC` (twin
side: con-ron's `whnfTelescope_spec`'s proof): `whnf` (`whnfC_rsim`; its error by `WhnfTopE`),
the view, `internE` of the binder's variable (`internE_run`: a `PStep`), `instantiate1Fast`
(`instantiate1Fast_run`), the recursion one level deeper (`WScoped.instantiate1`), the cons (L
only); every arm the guards leave is the twin's `.invalid`. -/
theorem wt_ref (k : Nat) (hk : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (i n e : Word) {eP : ConLeche.Expr},
    StageC dn vis fe env m a → AbsOK m → H e → i.toNat + n.toNat < 2 ^ 64 →
    denoteE a.store (decI e) = some eP → ConLeche.Expr.WScoped i.toNat eP →
    RefE (WtG p) (wtE p k m vis i n e) (whnfTelescope V fe i.toNat n.toNat (decI e)) a
      (fun v x a' => WtPost dn vis fe env m v a' x) := by
  induction k with
  | zero =>
    intro m a i n e eP _ _ _ _ _ _
    rw [wtE.eq_1]; exact RefE.of_cls0 rfl
  | succ k ih =>
  intro m a i n e eP hC hA he hin hdP hwsP
  rw [wtE.arm1, whnfTelescope_eq]
  refine RefE.bindCall (fun _ => wtE.k_whnf_top.none ..) (fun hG e1 h1 => hG.whnf k (by omega) hC.stageT i e he _ h1)
    (whnfC_rsim hq henv k (by omega) hC hA i e he hdP hwsP)
    fun r1 m1 e' a1 _ hrun1 ⟨hC1, hg1, ⟨he'32, he'eq⟩, hA1, hcs1, wP, hwP, hwsw⟩ => ?_
  dsimp only at hC1 hg1 he'32 he'eq hA1
  rw [wtE.k_whnf_top.arm1]
  have hS1 := hC1.stage
  rw [← he'eq] at hwP ⊢
  generalize hw : r1.headD 0 = w at he'32 hwP
  -- the view
  rcases h2 : callE p k "e_view" [w] m1 with e2 | ⟨r2, m2⟩
  · rw [wtE.k_e_view.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  obtain ⟨s2, hs2, hl2, hne2, hr2⟩ := triple_of_callE (eView_spec p hP.view k ⟨m1, Locals.init []⟩ w) h2
  have hm2 : m2 = m1 := by rw [← hs2, hl2]
  subst hm2
  generalize hvv : eViewW m2 w = v at hr2
  subst hr2
  obtain ⟨vv, hview, hVR⟩ := eViewW_ok m2 a1 hS1.check.arena.base w (hvv ▸ hne2)
  rw [hvv] at hVR
  have hrv : (view (decI w)).run a1 = .ok (vv, a1) := by
    rw [← decE_eq]; exact view_run _ _ _ hview
  refine RefE.bind_right hrv ?_
  by_cases hs : r2.headD 0 = 2 ∧ n = 0
  · rw [wtE.k_e_view.arm1 _ _ _ _ _ _ _ hs]
    cases vv with
    | sort u =>
      obtain ⟨-, hu32, hu⟩ := hVR
      rw [hs.2]
      exact RefE.ret rfl ⟨hC1, hg1, by simp [decHL, hslice?], by simp,
        by simpa [List.getD] using hu32, by simpa [List.getD] using hu, hA1⟩
    | _ => simp [ViewR] at hVR <;> (try omega) <;> (have := hs.1; simp_all)
  by_cases hp' : ¬ (r2.headD 0 = 6 ∧ n ≠ 0)
  · rw [wtE.k_e_view.abort1 _ _ _ _ _ _ _ hs hp']
    obtain ⟨msg, hm⟩ := wtArm_fail fe i.toNat hVR hs hp'
    rw [hm]
    exact fun _ => ErrClaim.fail _ _ rfl
  have hp : r2.headD 0 = 6 ∧ n ≠ 0 := Decidable.not_not.mp hp'
  rw [wtE.k_e_view.arm2 _ _ _ _ _ _ _ hs hp]
  cases vv with
  | forallE ty body =>
    obtain ⟨domP, bodyP, rfl, hd, hbd⟩ :=
      ConRon.Bridge.denote_forallE_inv hC1.check.state.wf hview hwP
    have hwsdb : ConLeche.Expr.WScoped i.toNat domP ∧ ConLeche.Expr.WScoped i.toNat bodyP := by
      simp only [ConLeche.Expr.WScoped] at hwsw; exact hwsw
    obtain ⟨hwsd, hwsb⟩ := hwsdb
    obtain ⟨-, hx32, hxe, hy32, hye⟩ := hVR
    have hx1 : r2.getD 1 0 = r2.tail.headD 0 := by
      cases r2 with | nil => rfl | cons _ t => cases t <;> rfl
    have hy1 : r2.getD 2 0 = r2.tail.tail.headD 0 := by
      cases r2 with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ u => cases u <;> rfl
    rw [hx1] at hx32 hxe
    rw [hy1] at hy32 hye
    generalize r2.tail.headD 0 = x at hx32 hxe ⊢
    generalize r2.tail.tail.headD 0 = y at hy32 hye ⊢
    have hn1 : 1 ≤ n.toNat := by
      rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hp.2
      · omega
    have hnm : (n - 1).toNat = n.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hn1))]; simp
    have hiS : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hns : n.toNat = (n.toNat - 1) + 1 := by omega
    rw [hns]
    simp only [wtArm]
    -- `intern_fvar`
    refine RefE.bindLift (fun _ => wtE.k_intern_fvar.none ..) fun fv m3 h3 => ?_
    obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 i x hx32 h3
    have hrun2' : (internE (.fvar i.toNat ty)).run a1 = .ok (decE fv, a2) := by
      rw [← hxe]; exact hrun2
    refine ⟨_, _, hrun2', ?_⟩
    refine RefE.ofArms (fun h => wtE.k_intern_fvar.abort1 (hc1 := h) ..)
      (fun h => wtE.k_intern_fvar.arm1 (hc1 := h) ..) (RefE.abort0 rfl fun hfv => ?_)
    have hfv32 : fv.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ fv.toNat := hfv; omega
    obtain ⟨p2, hfvd⟩ := ConRon.Bridge.Inductives.internE_run hC1.check.state
      (ConRon.Bridge.viewOK_fvar (by rw [hd]; rfl)) hrun2'
    have hfv' : denoteE a2.store (decE fv) = some (.fvar i.toNat domP) := by
      rw [hfvd]; simp [denoteEView, ConRon.Bridge.denote_ext hd p2.ext]
    have hA2 := fvinternW_afr h3 hA1
    have hC2 : StageC dn vis fe env m3 a2 := hC1.of_pstep hS2 hA2 p2
    -- `instantiate1_fast`
    refine RefE.bindLift (fun _ => wtE.k_instantiate1_fast.none ..) fun rb m4 h4 => ?_
    obtain ⟨b', a3, hrun3, hS3, hg3, hb32, hbeq⟩ :=
      i1F_ok dn vis fe y fv 0 hy32 m3 m4 a2 rb h4 hS2
    rw [CWF_eq, show (0 : Word).toNat = 0 from rfl, ← decE_eq y, hye, ← decE_eq fv] at hrun3
    refine ⟨_, _, hrun3, ?_⟩
    rw [wtE.k_instantiate1_fast.arm1]
    have hb2 : denoteE a2.store body = some bodyP := ConRon.Bridge.denote_ext hbd p2.ext
    obtain ⟨i1, i2, i4, i5, -, i7⟩ := ConRon.Bridge.ExprOps.instantiate1Fast_run hC2.check.state hfv'
      (by rw [hb2]; rfl) hrun3
    have p3 : PStep a2 a3 := PStep.of_caches i1 i2 i4 i5
    have hop : denoteE a3.store b' = some (bodyP.instantiate1 (.fvar i.toNat domP) 0) := i7 _ hb2
    have hA3 := i1F_afr h4 hA2
    have hC3 : StageC dn vis fe env m4 a3 := hC2.of_pstep hS3 hA3 p3
    -- the recursion
    have hR := ih (by omega) m4 a3 (i + 1) (n - 1) (rb.headD 0) hC3 hA3 hb32 (by omega)
      (by rw [hbeq]; exact hop) (by rw [hiS]; exact ConLeche.Expr.WScoped.instantiate1 hwsd 0 hwsb)
    rw [hiS, hnm, hbeq] at hR
    refine RefE.bindE (fun _ => wtE.k_whnf_telescope.none ..) id hR fun ⟨rr, m5⟩ ⟨bs, s'⟩ a4 _ hR4 => ?_
    rw [wtE.k_whnf_telescope.arm1]
    -- `sl_cons` (L only)
    refine RefE.onlySim (fun _ => wtE.k_sl_cons.none ..) (fun _ _ h => h) fun ro m6 h6 => ?_
    rw [wtE.k_sl_cons.arm1]
    obtain ⟨hS6, hg6, hd6, ht6⟩ := consW_stage h6 hR4.stage.stage hR4.top hx32 hR4.doms
    have hA6 := consW_afr h6 hR4.abs
    exact RefE.ret rfl ⟨hR4.stage.of_pstep hS6 hA6 (PStep.refl hR4.stage.check.state),
      (((hg1.trans hg2).trans hg3).trans hR4.grow).trans hg6,
      by rw [← hxe, decE_eq]; exact hd6, Nat.le_of_eq ht6, hR4.sort32, hR4.sort, hA6⟩
  | _ => simp [ViewR] at hVR <;> (try omega) <;> (have := hp.1; simp_all)

include hq hP henv in
/-- **`whnf_telescope` refines `whnfTelescope .verified`** under `StageC` (`wt_ref`'s ok half; the
type's denotation and scoping as con-ron's `whnfTelescope_spec` asks): the binders' domains as an
`IW` slice, the sort as a word. -/
@[refines ConRon.Arena.whnfTelescope]
theorem whnfTelescope_refinesC (k : Nat)
    (hk : k ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (i n e : Word)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem) (he : H e)
    (hin : i.toNat + n.toNat < 2 ^ 64) {eP : ConLeche.Expr}
    (hdP : denoteE a₀.store (decI e) = some eP) (hwsP : ConLeche.Expr.WScoped i.toNat eP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "whnf_telescope" [vis, i, n, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (whnfTelescope V fe i.toNat n.toNat (decI e)) a₀ ∧
      WtPost dn vis fe env s₀.mem (r, s'.mem) (AM.st (whnfTelescope V fe i.toNat n.toNat (decI e)) a₀)
        (AM.res (whnfTelescope V fe i.toNat n.toNat (decI e)) a₀); ⊤⦄ :=
  triple_post (RefE.triple (wtE_spec p hP k s₀ vis i n e)
      (wt_ref hq hP henv k hk _ a₀ i n e hC hA he hin hdP hwsP)) fun _ _ ⟨hl, _, _, hrun, hR⟩ => by
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
    exact ⟨hl, hok, by rw [hst, hres]; exact hR⟩

end sims

end L.Ind
