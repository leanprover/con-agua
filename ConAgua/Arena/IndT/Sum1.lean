import ConAgua.Arena.IndT.Lift

/-!
# `whnfTelescope` under `StageC` (lane `indstaget`)

`whnf_telescope`'s model at `realCall p`, from `StageC` and con-ron's preconditions of
`whnfTelescope_spec` (the type denotes and is scoped at the depth `i`), its twin side transcribed
from that spec's proof: `whnf` (`whnfC_rsim`: the answer denotes, scoped), the view
(`denote_forallE_inv`), `internE` of the binder's variable (`internE_run`: a `PStep`),
`instantiate1Fast` (`instantiate1Fast_run`: a `PStep` by `PStep.of_caches`, the instantiated body
denotes), the recursion one level deeper (`WScoped.instantiate1`), the cons (L only).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

/-- `whnf_telescope`'s post: the binders' domains as an `IW` slice, the sort as a word. -/
def WtPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (b : List Word × Mem) (a' : AState) (x : List EIdx × LIdx) : Prop :=
  StageC dn vis fe env b.2 a' ∧ IWGrow m b.2 ∧
    decHL b.2 (b.1.headD 0).toNat (b.1.tail.headD 0).toNat = some x.1 ∧
    (b.1.headD 0).toNat + (b.1.tail.headD 0).toNat ≤ iwTop b.2 ∧
    (b.1.tail.tail.headD 0).toNat < 2 ^ 32 ∧ decI (b.1.tail.tail.headD 0) = x.2 ∧ AbsOK b.2

include hq henv in
/-- **`whnf_telescope` under `StageC`** (twin side: con-ron's `whnfTelescope_spec`'s proof). -/
theorem wtW_simC (k : Nat) (hk : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (i n e : Word) {eP : ConLeche.Expr},
    StageC dn vis fe env m a → AbsOK m → H e → i.toNat + n.toNat < 2 ^ 64 →
    denoteE a.store (decI e) = some eP → ConLeche.Expr.WScoped i.toNat eP →
    RSim (wtW (realCall p) k m vis i n e) (whnfTelescope V fe i.toNat n.toNat (decI e)) a
      (WtPost dn vis fe env m) := by
  induction k with
  | zero => intros; intro b hb; simp [wtW] at hb
  | succ k ih =>
    intro m a i n e eP hC hA he hin hdP hwsP
    intro ⟨r, m'⟩ h
    rw [wtW_succ] at h
    rcases h1 : realCall p k "whnf_top" [vis, i, e] m with _ | ⟨r1, m1⟩
    · rw [h1] at h; simp [wtK1] at h
    rw [h1, wtK1_some] at h
    obtain ⟨e', a1, hrun1, hC1, hg1, ⟨he'32, he'eq⟩, hA1, hcs1, wP, hwP, hwsw⟩ :=
      whnfC_rsim hq henv k (by omega) hC hA i e he hdP hwsP _ h1
    dsimp only at hC1 hg1 he'32 he'eq hA1
    have hS1 := hC1.stage
    rw [whnfTelescope_eq, StateT.run_bind, hrun1]
    simp only [bind, Except.bind]
    rw [← he'eq] at hwP ⊢
    generalize hw : r1.headD 0 = w at h he'32 hwP
    generalize hv : eViewW m1 w = v at h
    by_cases hs : v.headD 0 = 2 ∧ n = 0
    · rw [wtK2_sort (realCall p) k m1 vis i n v hs.1 hs.2] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hne : v ≠ [] := fun h0 => by rw [h0] at hs; simp at hs
      obtain ⟨vv, hview, hVR⟩ := eViewW_ok m1 a1 hS1.1.arena.1 w (hv ▸ hne)
      rw [hv] at hVR
      have hb : ∀ {β : Type} (f : ENodeView → AM β),
          (StateT.bind (view (decI w)) f).run a1 = (f vv).run a1 := by
        intro β f
        show (view (decI w) >>= f).run a1 = _
        rw [StateT.run_bind, ← decE_eq, view_run _ _ _ hview]; rfl
      rw [hb]
      cases vv with
      | sort u =>
        obtain ⟨-, hu32, hu⟩ := hVR
        rw [hs.2]
        refine ⟨([], u), a1, rfl, hC1, hg1, by simp [decHL, hslice?], by simp, ?_, ?_, hA1⟩
        · simpa [List.getD] using hu32
        · simpa [List.getD] using hu
      | _ => simp [ViewR] at hVR <;> (try omega) <;> (have := hs.1; simp_all)
    by_cases hp : v.headD 0 = 6 ∧ n ≠ 0
    · rw [wtK2_pi (realCall p) k m1 vis i n v hp.1 hp.2] at h
      have hne : v ≠ [] := fun h0 => by rw [h0] at hp; simp at hp
      obtain ⟨vv, hview, hVR⟩ := eViewW_ok m1 a1 hS1.1.arena.1 w (hv ▸ hne)
      rw [hv] at hVR
      have hb : ∀ {β : Type} (f : ENodeView → AM β),
          (StateT.bind (view (decI w)) f).run a1 = (f vv).run a1 := by
        intro β f
        show (view (decI w) >>= f).run a1 = _
        rw [StateT.run_bind, ← decE_eq, view_run _ _ _ hview]; rfl
      rw [hb]
      cases vv with
      | forallE ty body =>
        obtain ⟨domP, bodyP, rfl, hd, hbd⟩ :=
          ConRon.Bridge.denote_forallE_inv hC1.check.state.wf hview hwP
        have hwsdb : ConLeche.Expr.WScoped i.toNat domP ∧ ConLeche.Expr.WScoped i.toNat bodyP := by
          simp only [ConLeche.Expr.WScoped] at hwsw; exact hwsw
        obtain ⟨hwsd, hwsb⟩ := hwsdb
        obtain ⟨-, hx32, hxe, hy32, hye⟩ := hVR
        have hx1 : v.getD 1 0 = v.tail.headD 0 := by cases v with | nil => rfl | cons _ t => cases t <;> rfl
        have hy1 : v.getD 2 0 = v.tail.tail.headD 0 := by
          cases v with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ u => cases u <;> rfl
        rw [hx1] at hx32 hxe
        rw [hy1] at hy32 hye
        generalize v.tail.headD 0 = x at h hx32 hxe
        generalize v.tail.tail.headD 0 = y at h hy32 hye
        have hn1 : 1 ≤ n.toNat := by
          rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
          · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hp.2
          · omega
        have hnm : (n - 1).toNat = n.toNat - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hn1))]; simp
        have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
        have hns : n.toNat = (n.toNat - 1) + 1 := by omega
        rw [hns]
        simp only [wtArm]
        rcases h2 : fvinternW m1 i x with _ | ⟨fv, m2⟩
        · rw [h2] at h; simp [wtK3] at h
        rw [h2] at h
        by_cases hfv : 4294967296 ≤ fv
        · rw [wtK3_big (realCall p) k m2 vis i n x y fv hfv] at h; cases h
        rw [wtK3_ok (realCall p) k m2 vis i n x y fv hfv] at h
        have hfv32 : fv.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ fv.toNat := hfv; omega
        obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 i x hx32 h2
        have hrun2' : (internE (.fvar i.toNat ty)).run a1 = .ok (decE fv, a2) := by
          rw [← hxe]; exact hrun2
        obtain ⟨p2, hfv⟩ := ConRon.Bridge.Inductives.internE_run hC1.check.state
          (ConRon.Bridge.viewOK_fvar (by rw [hd]; rfl)) hrun2'
        have hfv' : denoteE a2.store (decE fv) = some (.fvar i.toNat domP) := by
          rw [hfv]; simp [denoteEView, ConRon.Bridge.denote_ext hd p2.ext]
        have hA2 := fvinternW_afr h2 hA1
        have hC2 : StageC dn vis fe env m2 a2 := hC1.of_pstep hS2 hA2 p2
        rcases h3 : i1F m2 [CWF, y, fv, 0] with _ | ⟨rb, m3⟩
        · rw [h3] at h; simp [wtK4] at h
        rw [h3, wtK4_some] at h
        obtain ⟨b', a3, hrun3, hS3, hg3, hb32, hbeq⟩ :=
          i1F_ok dn vis fe y fv 0 hy32 m2 m3 a2 rb h3 hS2
        rw [CWF_eq, show (0 : Word).toNat = 0 from rfl, ← decE_eq y, hye, ← decE_eq fv] at hrun3
        have hb2 : denoteE a2.store body = some bodyP := ConRon.Bridge.denote_ext hbd p2.ext
        obtain ⟨i1, i2, i4, i5, -, i7⟩ := ConRon.Bridge.ExprOps.instantiate1Fast_run hC2.check.state hfv'
          (by rw [hb2]; rfl) hrun3
        have p3 : PStep a2 a3 := PStep.of_caches i1 i2 i4 i5
        have hop : denoteE a3.store b' = some (bodyP.instantiate1 (.fvar i.toNat domP) 0) := i7 _ hb2
        have hA3 := i1F_afr h3 hA2
        have hC3 : StageC dn vis fe env m3 a3 := hC2.of_pstep hS3 hA3 p3
        rcases h4 : wtW (realCall p) k m3 vis (i + 1) (n - 1) (rb.headD 0) with _ | ⟨rr, m4⟩
        · rw [h4] at h; simp [wtK5] at h
        rw [h4, wtK5_some] at h
        obtain ⟨⟨bs, s'⟩, a4, hrun4, hC4, hg4, hd4, ht4, hs32, hseq, hA4⟩ :=
          ih (by omega) m3 a3 (i + 1) (n - 1) (rb.headD 0) hC3 hA3 hb32 (by omega)
            (by rw [hbeq]; exact hop) (by rw [hi1]; exact ConLeche.Expr.WScoped.instantiate1 hwsd 0 hwsb)
            _ h4
        dsimp only at hC4 hg4 hd4 ht4 hs32 hseq hA4
        rcases h5 : consW k m4 x (rr.headD 0) (rr.tail.headD 0) with _ | ⟨ro, m5⟩
        · rw [h5] at h; simp [wtK6] at h
        rw [h5, wtK6_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hS5, hg5, hd5, ht5⟩ := consW_stage h5 hC4.stage ht4 hx32 hd4
        have hA5 := consW_afr h5 hA4
        refine ⟨(ty :: bs, s'), a4, ?_, hC4.of_pstep hS5 hA5 (PStep.refl hC4.check.state),
          (((hg1.trans hg2).trans hg3).trans hg4).trans hg5,
          by rw [← hxe, decE_eq]; exact hd5, Nat.le_of_eq ht5, hs32, hseq, hA5⟩
        simp only [StateT.run_bind, StateT.run_pure]
        rw [hrun2']
        simp only [bind, Except.bind]
        rw [hrun3]
        simp only
        rw [hi1, hnm, hbeq] at hrun4
        rw [hrun4]
        rfl
      | _ => simp [ViewR] at hVR <;> (try omega) <;> (have := hp.1; simp_all)
    · rw [wtK2_none (realCall p) k m1 vis i n v hs hp] at h; cases h

include hq henv in
/-- **`whnf_telescope` refines `whnfTelescope .verified`** under `StageC` (the knot's `whnf`; the
type's denotation and scoping as con-ron's `whnfTelescope_spec` asks): the binders' domains as an
`IW` slice, the sort as a word. -/
@[refines ConRon.Arena.whnfTelescope]
theorem whnfTelescope_refinesC (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hv : p.lookup "e_view" = some eView)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hp : p.lookup "whnf_telescope" = some whnfTelescopeL) (hi1 : I1Prog p) (k : Nat)
    (hk : k ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (i n e : Word)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem) (he : H e)
    (hin : i.toNat + n.toNat < 2 ^ 64) {eP : ConLeche.Expr}
    (hdP : denoteE a₀.store (decI e) = some eP) (hwsP : ConLeche.Expr.WScoped i.toNat eP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "whnf_telescope" [vis, i, n, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (whnfTelescope V fe i.toNat n.toNat (decI e)) a₀ ∧
      WtPost dn vis fe env s₀.mem (r, s'.mem) (AM.st (whnfTelescope V fe i.toNat n.toNat (decI e)) a₀)
        (AM.res (whnfTelescope V fe i.toNat n.toNat (decI e)) a₀); ⊤⦄ :=
  triple_post (wtW_spec p ha hc hsc hv hff hfp hif hp hi1 (realCall p) (realCall_spec p) k s₀ vis i n e)
    fun _ _ ⟨hl, hw⟩ =>
      let h := (wtW_simC hq henv k hk _ a₀ i n e hC hA he hin hdP hwsP).am hw
      ⟨hl, h.1, h.2⟩

end sims

end L.Ind
