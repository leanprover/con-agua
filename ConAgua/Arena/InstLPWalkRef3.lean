import ConAgua.Arena.InstLPWalkRef2
import ConAgua.Arena.InstLPWalkLet
import ConAgua.Arena.InstLPLevel2
import ConAgua.Arena.InstLPWalkArms
import ConAgua.Arena.InstLPWalkGo
import ConAgua.Census.Attr

/-!
# The `instLP` walk refines `instLPGo`: the dispatcher, by induction on the L fuel

`lp_go` at `n + 1`: the counter (`fu = 0` aborts, the twin fails), the cut-off on the
level-parameter bit (`der_b`'s third result is `exprLPW`, `derLW_ok`: the twin's `lpOfData`), the
scratch check, then by the tag: the leaves `bvar`, `lit` return `h`; `sort` and `const` substitute
their level (list) behind the level memos (`SlMemoOK`, `SlsMemoOK`, helper `whnf4-ilp-lev`) and
re-intern; the six compound arms (`InstLPWalkRef.lean`, `InstLPWalkRef2.lean`) at `fu - 1`.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem ilw_beqI {k : IdxKind} {x y : Word} (hx : HW x) (hy : HW y) :
    ((decI x : Idx k) == decI y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · have : (decI x : Idx k) ≠ decI y := fun e => h (by
      rw [← (word_decI _ x hx).mpr rfl, ← (word_decI _ y hy).mpr rfl, e])
    simp [h, this]

section steps
variable {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
  {M : ModeMaps} {eb : Word}
variable {p : Prog} (hp : ILWMkProg p) (n : Nat)
include hp

theorem ilw_internSort (y : Word) (rs : List Word) (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a)
    (hy : HW y) (hdy : ∃ l, denoteL a.store.ls (decI y) = some l)
    (hc : callW p n "intern_sort" [y] m = some (rs, m')) :
    ILWStep (internE (.sort (decI y))) a dn m m' vis fe M eb (rs.headD 0) := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (internSort_spec p hp.sof hp.sop hp.soi n ⟨m, Locals.init []⟩ y) hc
  obtain ⟨hok, hA, hres, hw⟩ := internSort_core hS y hy rs hm hdy
  obtain ⟨hM', hg⟩ := hM.of_internE hok (sointernW_frame _ _ _ _ hm)
  exact ⟨_, by rw [AM.run_of_ok _ _ hok, hres]; rfl, hA, hM', hg, hw⟩

theorem ilw_internConst (c y : Word) (rs : List Word) (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a)
    (hcw : HW c) (hy : HW y) (hdy : ∃ ls, denoteLs a.store.lss (decI y) = some ls)
    (hc : callW p n "intern_const" [c, y] m = some (rs, m')) :
    ILWStep (internE (.const (decI c) (decI y))) a dn m m' vis fe M eb (rs.headD 0) := by
  obtain ⟨hok, hD, hres, hf, hw⟩ :=
    callW_internConst p hp.cof hp.cop hp.coi n ⟨m, Locals.init []⟩ a hS.arena c y hcw hy rs m' hc
  have hrun := AM.run_of_ok _ _ hok
  have hS' := hS.of_const hD (Keeps.run (keeps_cpl_internConst _ _) hrun) hf hrun hdy
  obtain ⟨hM', hg⟩ := hM.of_internE hok hf
  exact ⟨_, by rw [hrun, hres]; rfl, ⟨M, hS', KeptAll.refl _ _, StackKept.of_const_frame hf⟩, hM', hg, hw⟩

end steps

end L.Arena

namespace L.Arena

theorem lpW_zero_iff (d : UInt64) : lpW d = 0 ↔ lpOfData d = false := by
  unfold lpW b2w; cases lpOfData d <;> simp

/-- **The dispatcher at `n + 1`** from the walk at `n`. -/
theorem ilwGo_succ {p : Prog} (hp : ILWAllProg p) (n : Nat) (ih : ∀ k, k ≤ n → ILWGoOK p k) :
    ILWGoOK p (n + 1) := by
  intro m m' a dn vis fe M eb h ko kc vo vc fu ks us vs rs hS hM hE hh hc
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lpGo_spec p hp.lev.ilw n _ h ko kc vo vc fu) hc
  rw [hs'] at hW
  change ilwGoW p n m h ko kc vo vc fu = some (rs.headD 0, m') at hW
  unfold ilwGoW at hW
  by_cases hfu : fu = 0
  · simp [hfu] at hW
  simp only [hfu, ↓reduceIte] at hW
  generalize rs.headD 0 = r at hW ⊢
  rcases h1 : callW p n "der_b" [h] m with _ | ⟨d, m₁⟩ <;> rw [h1] at hW
  · simp [ilwGoK] at hW
  rw [ilwGoK_some] at hW
  obtain ⟨s1, hs1, -, hm1, -, -, hlp⟩ :=
    triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (derB_spec p hp.mkp.spine.derb n _ h) h1
  have hm₁ : m₁ = m := hs1.symm.trans hm1
  subst hm₁
  rw [ctrW_toNat fu hfu, instLPGo_succ]
  have hd := derLW_ok m₁ a hS.arena.1 hS.arena.2 h hh
  rw [hlp] at hW
  -- the cut-off
  by_cases h0 : exprLPW m₁ h = 0
  · simp only [h0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    rw [hd, lpW_zero_iff] at h0
    exact ILWStep.refl (by
      rw [StateT.run_bind, derivedE_run]
      simp only [except_ok_bind, h0, Bool.not_false, ↓reduceIte]; rfl) hS hM hh
  simp only [h0, ↓reduceIte] at hW
  have hlp' : lpOfData (a.store.derived (decE h)) = true := by
    rw [hd, lpW_zero_iff] at h0; simpa using h0
  have hR := hS.arena.1
  -- the twin's walk past the cut-off, at the node's view
  have hrun : ∀ (v : ENodeView), a.store.view (decE h) = some v → ∀ T : AM EIdx,
      (match v with
        | .bvar _ => pure (decE h)
        | .lit _ => pure (decE h)
        | .sort u => do
          let hl ← substLMemoAt ks vs u
          internRebuiltSort (decE h) (hl == u) hl
        | .const c ws => do
          let ws' ← substLsMemoAt ks vs ws
          internRebuiltConst (decE h) (ws' == ws) c ws'
        | .fvar i ty => instLPArmFVar ks vs (fu - 1).toNat (decE h) i ty
        | .app f x => instLPArmApp ks vs (fu - 1).toNat (decE h) f x
        | .lam ty b => instLPArmLam ks vs (fu - 1).toNat (decE h) ty b
        | .forallE ty b => instLPArmForallE ks vs (fu - 1).toNat (decE h) ty b
        | .letE ty x b => instLPArmLet ks vs (fu - 1).toNat (decE h) ty x b
        | .proj c i x => instLPArmProj ks vs (fu - 1).toNat (decE h) c i x : AM EIdx).run a = T.run a →
      ILWStep T a dn m₁ m' vis fe M eb r →
      ILWStep (do
        let der ← derivedE (decE h)
        if !(lpOfData der) then pure (decE h)
        else
          match ← view (decE h) with
          | .bvar _ => pure (decE h)
          | .lit _ => pure (decE h)
          | .sort u => do
            let hl ← substLMemoAt ks vs u
            internRebuiltSort (decE h) (hl == u) hl
          | .const c ws => do
            let ws' ← substLsMemoAt ks vs ws
            internRebuiltConst (decE h) (ws' == ws) c ws'
          | .fvar i ty => instLPArmFVar ks vs (fu - 1).toNat (decE h) i ty
          | .app f x => instLPArmApp ks vs (fu - 1).toNat (decE h) f x
          | .lam ty b => instLPArmLam ks vs (fu - 1).toNat (decE h) ty b
          | .forallE ty b => instLPArmForallE ks vs (fu - 1).toNat (decE h) ty b
          | .letE ty x b => instLPArmLet ks vs (fu - 1).toNat (decE h) ty x b
          | .proj c i x => instLPArmProj ks vs (fu - 1).toNat (decE h) c i x) a dn m₁ m' vis fe M eb r := by
    intro v hv T hT hst
    refine ILWStep.congr ?_ hst
    rw [StateT.run_bind, derivedE_run]
    simp only [except_ok_bind, hlp', Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      view_run _ _ _ hv]
    exact hT
  have vok : ∀ c, ¬ tcnt m₁ c (tierW h) ≤ idxW h →
      ¬ (tierW h ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0) → viewOK m₁ h c := fun c hc hs => ⟨hs, by simpa using hc⟩
  by_cases hs : tierW h ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0
  · rw [ilwDispW_sc p n m₁ h ko kc vo vc fu hs] at hW; cases hW
  -- an arm call at `n` (the arm's own fuel `k + 1 = n`)
  have armK : ∀ (f : FnName) (rs2 : List Word) (m₂ : Mem),
      callW p n f [h, ko, kc, vo, vc, fu - 1] m₁ = some (rs2, m₂) → ∃ k, n = k + 1 := by
    intro f rs2 m₂ h2
    cases n with
    | zero => rw [callW_zero] at h2; cases h2
    | succ k => exact ⟨k, rfl⟩
  by_cases g0 : h >>> 28 = 0
  · rw [ilwDispW_bvar p n m₁ h ko kc vo vc fu hs g0] at hW
    by_cases hc0 : tcnt m₁ BVAR (tierW h) ≤ idxW h
    · simp [hc0] at hW
    simp only [hc0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact hrun _ (view_bvar m₁ a hR h hh (vok BVAR hc0 hs) g0) _ rfl (ILWStep.refl rfl hS hM hh)
  by_cases g8 : h >>> 28 = 8
  · rw [ilwDispW_lit p n m₁ h ko kc vo vc fu hs g8] at hW
    by_cases hc0 : tcnt m₁ LIT (tierW h) ≤ idxW h
    · simp [hc0] at hW
    simp only [hc0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    obtain ⟨l, hv⟩ := view_lit m₁ a hR h hh (vok LIT hc0 hs) g8
    exact hrun _ hv _ rfl (ILWStep.refl rfl hS hM hh)
  by_cases g2 : h >>> 28 = 2
  · rw [ilwDispW_sort p n m₁ h ko kc vo vc fu hs g2] at hW
    by_cases hc0 : tcnt m₁ SORT (tierW h) ≤ idxW h
    · simp [hc0] at hW
    simp only [hc0, ↓reduceIte] at hW
    obtain ⟨hv, hx⟩ := L.Ind.view_sort_f m₁ a hR h hh (vok SORT hc0 hs) g2
    generalize tfld m₁ SORT (tierW h) (idxW h) 0 = x at hW hv hx
    refine hrun _ hv _ rfl ?_
    rcases h2 : callW p n "sl_memo" [x, ko, kc, vo, vc] m₁ with _ | ⟨ys, m₂⟩ <;> simp only [h2, ilwSortK, reduceCtorEq] at hW
    obtain ⟨a₂, r2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hM₂, hg₂, hy, hdy⟩ :=
      slMemo_ok p hp.lev n m₁ m₂ a dn vis fe M eb x ko kc vo vc ks us vs ys hS hM hE hx
        (hS.den.sort _ _ hv) h2
    by_cases same : ys.headD 0 = x
    · simp only [same, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl⟩ := hW
      refine ⟨a₂, ?_, ⟨M₂, hS₂, hK₂, hSt₂⟩, hM₂, hg₂, hh⟩
      simp only [StateT.run_bind, r2, except_ok_bind, same, beq_self_eq_true,
        internRebuiltSort, ↓reduceIte]; rfl
    simp only [same, ↓reduceIte] at hW
    rcases h3 : callW p n "intern_sort" [ys.headD 0] m₂ with _ | ⟨zs, m₃⟩ <;> simp only [h3, ilwChk, reduceCtorEq] at hW
    by_cases hb : 4294967296 ≤ zs.headD 0
    · rw [ite_eq_left hb] at hW; cases hW
    rw [ite_eq_right hb] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hz : HW (zs.headD 0) := by
      unfold HW; have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hb); simpa using this
    obtain ⟨a₃, r3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hM₃, hg₃, -⟩ :=
      ilw_internSort hp.mkp n (ys.headD 0) zs hS₂ hM₂ hy hdy h3
    refine ⟨a₃, ?_, ⟨M₃, hS₃, hK₂.trans hK₃, hSt₂.trans hSt₃⟩, hM₃, hg₂.trans hg₃, hz⟩
    simp only [StateT.run_bind, r2, except_ok_bind, ilw_beqI hy hx, same, decide_false,
      internRebuiltSort, Bool.false_eq_true, ↓reduceIte, internSortE]
    exact r3
  by_cases g3 : h >>> 28 = 3
  · rw [ilwDispW_const p n m₁ h ko kc vo vc fu hs g3] at hW
    by_cases hc0 : tcnt m₁ CONST (tierW h) ≤ idxW h
    · simp [hc0] at hW
    simp only [hc0, ↓reduceIte] at hW
    obtain ⟨hv, hcw, hx⟩ := L.Ind.view_const_f m₁ a hR h hh (vok CONST hc0 hs) g3
    generalize tfld m₁ CONST (tierW h) (idxW h) 0 = cw at hW hv hcw
    generalize tfld m₁ CONST (tierW h) (idxW h) 1 = x at hW hv hx
    refine hrun _ hv _ rfl ?_
    rcases h2 : callW p n "sls_memo" [x, ko, kc, vo, vc] m₁ with _ | ⟨ys, m₂⟩ <;> simp only [h2, ilwConstK, reduceCtorEq] at hW
    obtain ⟨a₂, r2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hM₂, hg₂, hy, hdy⟩ :=
      slsMemo_ok p hp.lev n m₁ m₂ a dn vis fe M eb x ko kc vo vc ks us vs ys hS hM hE hx
        (hS.den.constLs _ _ _ hv) h2
    by_cases same : ys.headD 0 = x
    · simp only [same, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl⟩ := hW
      refine ⟨a₂, ?_, ⟨M₂, hS₂, hK₂, hSt₂⟩, hM₂, hg₂, hh⟩
      simp only [StateT.run_bind, r2, except_ok_bind, same, beq_self_eq_true,
        internRebuiltConst, ↓reduceIte]; rfl
    simp only [same, ↓reduceIte] at hW
    rcases h3 : callW p n "intern_const" [cw, ys.headD 0] m₂ with _ | ⟨zs, m₃⟩ <;> simp only [h3, ilwChk, reduceCtorEq] at hW
    by_cases hb : 4294967296 ≤ zs.headD 0
    · rw [ite_eq_left hb] at hW; cases hW
    rw [ite_eq_right hb] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hz : HW (zs.headD 0) := by
      unfold HW; have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hb); simpa using this
    obtain ⟨a₃, r3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hM₃, hg₃, -⟩ :=
      ilw_internConst hp.mkp n cw (ys.headD 0) zs hS₂ hM₂ hcw hy hdy h3
    refine ⟨a₃, ?_, ⟨M₃, hS₃, hK₂.trans hK₃, hSt₂.trans hSt₃⟩, hM₃, hg₂.trans hg₃, hz⟩
    simp only [StateT.run_bind, r2, except_ok_bind, ilw_beqI hy hx, same, decide_false,
      internRebuiltConst, Bool.false_eq_true, ↓reduceIte, internConstE]
    exact r3
  -- the compound arms
  have arm : ∀ (g : Word) (c : TRec) (fn : FnName), h >>> 28 = g →
      ilwDispW p n m₁ h ko kc vo vc fu =
        (if tcnt m₁ c (tierW h) ≤ idxW h then none
         else ilwHd (callW p n fn [h, ko, kc, vo, vc, fu - 1] m₁)) →
      ∃ k rs2, n = k + 1 ∧ viewOK m₁ h c ∧
        callW (p) (k + 1) fn [h, ko, kc, vo, vc, fu - 1] m₁ = some (rs2, m') ∧ r = rs2.headD 0 := by
    intro g c fn _ he
    rw [he] at hW
    by_cases hc0 : tcnt m₁ c (tierW h) ≤ idxW h
    · simp [hc0] at hW
    simp only [hc0, ↓reduceIte] at hW
    rcases h2 : callW p n fn [h, ko, kc, vo, vc, fu - 1] m₁ with _ | ⟨rs2, m₂⟩ <;> simp only [h2, ilwHd, reduceCtorEq] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨k, rfl⟩ := armK fn rs2 m₂ h2
    exact ⟨k, rs2, rfl, vok c hc0 hs, h2, rfl⟩
  by_cases g1 : h >>> 28 = 1
  · obtain ⟨k, rs2, rfl, hvk, h2, rfl⟩ := arm 1 FVAR "lp_fvar" g1 (ilwDispW_fvar p n m₁ h ko kc vo vc fu hs g1)
    obtain ⟨hv, hty⟩ := view_fvar_idx m₁ a hR h hh hvk g1
    obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
      (lpFVar_spec p hp.lev.ilw k _ h ko kc vo vc (fu - 1)) h2
    rw [hs2] at hW2
    exact hrun _ hv _ rfl (ilw_fvarArm hp.mkp (ih k (by omega)) hS hM hE hh hty hW2)
  by_cases g4 : h >>> 28 = 4
  · obtain ⟨k, rs2, rfl, hvk, h2, rfl⟩ := arm 4 APP "lp_app" g4 (ilwDispW_app p n m₁ h ko kc vo vc fu hs g4)
    obtain ⟨hv, hf, ha⟩ := view_app m₁ a hR h hh hvk g4
    obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
      (lpApp_spec p hp.lev.ilw k _ h ko kc vo vc (fu - 1)) h2
    rw [hs2] at hW2
    refine hrun _ hv _ (by dsimp only; rw [instLPArmApp_eq]) (ilw_binArm hp.mkp (ih k (by omega)) APP "mk_app" ENodeView.app ?_ hS hM hE hh hf ha hW2)
    intro m m' a M x y rs hS hM hx hy hc hw
    exact ilw_mkApp p hp.mkp k x y rs hS hM hc
  by_cases g5 : h >>> 28 = 5
  · obtain ⟨k, rs2, rfl, hvk, h2, rfl⟩ := arm 5 LAM "lp_lam" g5 (ilwDispW_lam p n m₁ h ko kc vo vc fu hs g5)
    obtain ⟨hv, hf, ha⟩ := view_lam m₁ a hR h hh hvk g5
    obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
      (lpLam_spec p hp.lev.ilw k _ h ko kc vo vc (fu - 1)) h2
    rw [hs2] at hW2
    refine hrun _ hv _ (by dsimp only; rw [instLPArmLam_eq]) (ilw_binArm hp.mkp (ih k (by omega)) LAM "mk_lam" ENodeView.lam ?_ hS hM hE hh hf ha hW2)
    intro m m' a M x y rs hS hM hx hy hc hw
    exact ilw_mkLam p hp.mkp k x y rs hS hM hc hw
  by_cases g6 : h >>> 28 = 6
  · obtain ⟨k, rs2, rfl, hvk, h2, rfl⟩ := arm 6 FORALL "lp_forall" g6 (ilwDispW_forall p n m₁ h ko kc vo vc fu hs g6)
    obtain ⟨hv, hf, ha⟩ := view_forall m₁ a hR h hh hvk g6
    obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
      (lpForall_spec p hp.lev.ilw k _ h ko kc vo vc (fu - 1)) h2
    rw [hs2] at hW2
    refine hrun _ hv _ (by dsimp only; rw [instLPArmForallE_eq]) (ilw_binArm hp.mkp (ih k (by omega)) FORALL "mk_forall" ENodeView.forallE ?_ hS hM hE hh hf ha hW2)
    intro m m' a M x y rs hS hM hx hy hc hw
    exact ilw_mkForall p hp.mkp k x y rs hS hM hc hw
  by_cases g7 : h >>> 28 = 7
  · obtain ⟨k, rs2, rfl, hvk, h2, rfl⟩ := arm 7 LET "lp_let" g7 (ilwDispW_let p n m₁ h ko kc vo vc fu hs g7)
    obtain ⟨hv, hf, ha, hb⟩ := view_let m₁ a hR h hh hvk g7
    obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
      (lpLet_spec p hp.lev.ilw k _ h ko kc vo vc (fu - 1)) h2
    rw [hs2] at hW2
    exact hrun _ hv _ rfl (ilw_letArm hp.mkp (ih k (by omega)) hp.lev.ilw (fun j _ => ih j (by omega)) hS hM hE hh hf ha hb hW2)
  by_cases g9 : h >>> 28 = 9
  · obtain ⟨k, rs2, rfl, hvk, h2, rfl⟩ := arm 9 PROJ "lp_proj" g9 (ilwDispW_proj p n m₁ h ko kc vo vc fu hs g9)
    obtain ⟨hv, -, he⟩ := view_proj m₁ a hR h hh hvk g9
    obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
      (lpProj_spec p hp.lev.ilw k _ h ko kc vo vc (fu - 1)) h2
    rw [hs2] at hW2
    exact hrun _ hv _ rfl (ilw_projArm hp.mkp (ih k (by omega)) hS hM hE hh he hW2)
  rw [ilwDispW_other p n m₁ h ko kc vo vc fu hs g0 g1 g2 g3 g4 g5 g6 g7 g8 g9] at hW
  cases hW

/-- **`lp_go` refines `instLPGo`** at every L fuel. -/
@[refines ConRon.Arena.instLPGo]
theorem ilwGo_ok {p : Prog} (hp : ILWAllProg p) (n : Nat) : ILWGoOK p n := by
  suffices h : ∀ n k, k ≤ n → ILWGoOK p k from h n n (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro k hk m m' a dn vis fe M eb h ko kc vo vc fu ks us vs rs _ _ _ _ hc
    obtain rfl : k = 0 := by omega
    rw [callW_zero] at hc; cases hc
  | succ n ih =>
    intro k hk
    rcases Nat.lt_or_eq_of_le hk with hlt | rfl
    · exact ih k (by omega)
    · exact ilwGo_succ hp n ih

end L.Arena
