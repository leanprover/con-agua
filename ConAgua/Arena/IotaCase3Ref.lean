module

public import ConAgua.Arena.FormerNZRef
public import ConAgua.Arena.WhnfIotaRefine4
import ConAgua.Arena.WhnfIotaRefine6
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# Case 3 of the ι split: `ctor_family`, `iota_case3_at`

`ctor_family(vis, cq)` (the constructor's family, read through the tagged record reads) by its
model `cfamW` and the run lemma `cfam_ok`; `iota_case3_at(mode, vis, isK, cq, us)` by its unified
model `ic3E` and `ic3_ref` (both outcomes: the errors are `former_never_zero_at`'s, `fnza_ref`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `ctor_family(vis, cq)` -/

/-- Model of `ctor_family`, its callees through their runs. -/
def cfamW (p : Prog) (n : Nat) (m : Mem) (vis cq : Word) : Option (List Word × Mem) :=
  match callW p n "pi_result" [erRd m (cq + 4)] m with
  | none => none
  | some (r₁, m₁) =>
    match callW p n "get_app_fn" [r₁.headD 0] m₁ with
    | none => none
    | some (r₂, m₂) =>
      if tagW (r₂.headD 0) ≠ 3 then some ([0, 0], m₂)
      else match callW p n "const_name_of" [r₂.headD 0] m₂ with
        | none => none
        | some (r₃, m₃) =>
          match callW p n "env_find" [r₃.headD 0, vis] m₃ with
          | none => none
          | some (r₄, m₄) =>
            if r₄.headD 0 = 0 then some ([0, 0], m₄)
            else if erRd m₄ (r₄.tail.headD 0) ≠ 3 then some ([0, 0], m₄)
            else some ([1, r₄.tail.headD 0], m₄)

theorem ctorFamily_spec (p : Prog) (hp : p.lookup "ctor_family" = some ctorFamilyL) (n : Nat)
    (s₀ : St) (vis cq : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ctor_family" [vis, cq]
    ⦃fun r s' => LocEq s' s₀ ∧ cfamW p n s₀.mem vis cq = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ctorFamilyL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld,
      evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE,
      callW_spec p n "pi_result", callW_spec p n "get_app_fn", callW_spec p n "const_name_of",
      callW_spec p n "env_find"] <;>
    finish [cfamW]

/-- An inductive record by its kind word `3`. -/
theorem decCI_ind_rd {R : Nat → Option Word} {rd : Word → Word} {q : Word}
    {ci : IConstantInfo} (hR : RdOK R rd) (h : decCI R q.toNat = some ci) :
    (rd q = 3 → ∃ cv caps, ci = .indInfo cv caps) ∧ (rd q ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) := by
  have := decCI_split hR h
  exact ⟨fun h3 => by obtain ⟨cv, caps, e, -⟩ := this.2.2.1 h3; exact ⟨cv, caps, e⟩, this.2.2.2.1⟩

/-- **`ctor_family` as a run**: the memory unchanged; the twin's family, a found one decoding at the
returned record. -/
theorem cfam_ok (p : Prog) (hp : IotaProg' p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m : Mem}
    {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    {cq : Word} {cvj : IConstantVal} {np nf : Nat}
    (hci : decCI (erecP m) cq.toNat = some (.ctorInfo cvj np nf)) {r : List Word} {m' : Mem}
    (h : cfamW p n m vis cq = some (r, m')) :
    m' = m ∧ ∃ res, (ctorFamily fe cvj).run a = .ok (res, a) ∧ (r.headD 0 = 0 → res = none) ∧
      (r.headD 0 ≠ 0 → ∃ cvT caps, res = some (cvT, caps) ∧
        decCI (erecP m) (r.tail.headD 0).toNat = some (.indInfo cvT caps) ∧
        ∃ T, fe.find? T = some (.indInfo cvT caps)) := by
  have hR := hS.arena.base
  have h4 : erRd m cq = 4 := Classical.byContradiction fun h =>
    (decCI_ctorR (erRdOK m) hci).2 h _ _ _ rfl
  obtain ⟨_, _, _, e4, hcv⟩ := (decCI_split (erRdOK m) hci).2.2.2.2.1 h4
  cases e4
  obtain ⟨-, -, hty, hty32⟩ := decCV_rd (erRdOK m) hcv
  unfold cfamW at h
  rcases c1 : callW p n "pi_result" [erRd m (cq + 4)] m with _ | ⟨r₁, m₁⟩ <;>
    simp only [c1, reduceCtorEq] at h
  obtain ⟨t₁, ht₁, hm₁, -, hw1, hpi⟩ := triple_of_callW
    (piResult_refines' p hp.spine.pires n ⟨m, Locals.init []⟩ a hR _ hty32) c1
  have e1 : m = m₁ := hm₁.symm.trans ht₁
  subst e1
  rcases c2 : callW p n "get_app_fn" [r₁.headD 0] m with _ | ⟨r₂, m₂⟩ <;>
    simp only [c2, reduceCtorEq] at h
  obtain ⟨t₂, ht₂, hm₂, -, hw2, hga⟩ := triple_of_callW
    (getAppFn_refines' p hp.spine.fn n ⟨m, Locals.init []⟩ a hR _ hw1) c2
  have e2 : m = m₂ := hm₂.symm.trans ht₂
  subst e2
  have hpi' : (piResult coreWalkFuel cvj.type).run a = .ok (decE (r₁.headD 0), a) := by
    rw [hty]; exact hpi
  have hv' : ∀ x, (viewConstName x).run a = .ok (a.store.viewConstName x, a) := fun _ => rfl
  by_cases h3 : tagW (r₂.headD 0) ≠ 3
  · simp only [h3, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ht : ((decE (r₂.headD 0)).tag == ETag.const) = false := by
      cases hb : ((decE (r₂.headD 0)).tag == ETag.const)
      · rfl
      · exact absurd ((decE_tag_eq _ hw2 3 (by decide)).mp (beq_iff_eq.mp hb)) h3
    refine ⟨rfl, none, ?_, fun _ => rfl, fun h0 => absurd rfl h0⟩
    simp only [ctorFamily, StateT.run_bind, hpi', except_ok_bind, hga, ht, Bool.false_eq_true,
      ↓reduceIte]; rfl
  rw [ite_eq_right h3] at h
  have h3' : tagW (r₂.headD 0) = 3 := by simpa using h3
  rcases c3 : callW p n "const_name_of" [r₂.headD 0] m with _ | ⟨r₃, m₃⟩ <;>
    simp only [c3, reduceCtorEq] at h
  cases n with
  | zero => exact absurd c3 (by rw [callW_zero]; simp)
  | succ n =>
  obtain ⟨t₃, ht₃, -, hm₃, hcno⟩ := triple_of_callW
    (constNameOf_spec p hp.constNameOf n ⟨m, Locals.init []⟩ _) c3
  have e3 : m = m₃ := hm₃.symm.trans ht₃
  subst e3
  unfold cnoW at hcno
  obtain ⟨hv1, hcno⟩ := of_ite_none hcno
  obtain ⟨hv2, hcno⟩ := of_ite_none hcno
  have hvn := viewConstName_f m a hR _ hw2 ⟨hv1, UInt64.not_le.mp hv2⟩ h3'
  rw [Option.some.inj hcno] at hvn
  obtain ⟨-, hn32, -⟩ := view_const_f m a hR _ hw2 ⟨hv1, UInt64.not_le.mp hv2⟩ h3'
  rw [Option.some.inj hcno] at hn32
  rcases c4 : callW p (n + 1) "env_find" [r₃.headD 0, vis] m with _ | ⟨r₄, m₄⟩ <;>
    simp only [c4, reduceCtorEq] at h
  obtain ⟨t₄, ht₄, hm₄, -, hfind, hdec⟩ := triple_of_callW
    (envFind_refines p hp.envrow hp.baserow hp.envfind (n + 1) ⟨m, Locals.init []⟩ vis _ hS.env
      hn32) c4
  have e4 : m = m₄ := hm₄.symm.trans ht₄
  subst e4
  have htag : ((decE (r₂.headD 0)).tag == ETag.const) = true := by
    exact beq_iff_eq.mpr ((decE_tag_eq _ hw2 3 (by decide)).mpr h3')
  have hfam : (ctorFamily fe cvj).run a = (match fe.find? (decI (r₃.headD 0)) with
      | some (.indInfo cvT caps) => pure (some (cvT, caps))
      | _ => pure none : AM (Option (IConstantVal × IIndCaps))).run a := by
    simp only [ctorFamily, StateT.run_bind, hpi', except_ok_bind, hga, htag, ↓reduceIte, hv', hvn]
    rcases fe.find? (decI (r₃.headD 0)) with _ | ci
    · rfl
    · cases ci <;> rfl
  by_cases h0 : r₄.headD 0 = 0
  · simp only [h0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hnone : fe.find? (decI (r₃.headD 0)) = none := by rw [hfind]; simp only [envFound, h0, ↓reduceIte]
    refine ⟨rfl, none, by rw [hfam]; simp only [hnone]; rfl, fun _ => rfl, fun h0 => absurd rfl h0⟩
  rw [ite_eq_right h0] at h
  obtain ⟨ci, hci4⟩ := hdec h0
  have hf' : fe.find? (decI (r₃.headD 0)) = some ci := by
    rw [hfind]; simp only [envFound, h0, ↓reduceIte]; exact hci4
  have hk := decCI_ind_rd (erRdOK m) hci4
  by_cases k3 : erRd m (r₄.tail.headD 0) ≠ 3
  · rw [ite_eq_left k3] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, none, ?_, fun _ => rfl, fun h0 => absurd rfl h0⟩
    rw [hfam]; simp only [hf']
    cases ci <;> first | exact absurd rfl (hk.2 k3 _ _) | rfl
  rw [ite_eq_right k3] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨cvT, caps, rfl⟩ := hk.1 (Classical.not_not.mp k3)
  refine ⟨rfl, some (cvT, caps), by rw [hfam]; simp only [hf']; rfl, fun h => by simp at h,
    fun _ => ⟨cvT, caps, rfl, hci4, _, hf'⟩⟩

/-! ## `iota_case3_at(mode, vis, isK, cq, us)` -/

/-- **`iota_case3_at`'s unified model** (`former_never_zero_at` through its unified model, the
other callees lifted). -/
l_model ic3E_spec (p : Prog) (hf : p.lookup "iota_case3_at" = some iotaCase3AtL)
  (hz : p.lookup "former_never_zero_at" = some formerNeverZeroAtL)
  (hs : p.lookup "former_sort_loop" = some formerSortLoopL)
  fns [hf ↦ ic3E list]
  specs [callW_spec p n "ctor_family", callW_spec p n "ls_node", fnzaE_spec p hz hs n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem decBool_ite0 (r : List Word) :
    decBool [if r.headD 0 = 0 then 1 else 0] = !decBool r := by
  by_cases h : r.headD 0 = 0
  · rw [ite_eq_left h, decBool_f_m2c h]; rfl
  · rw [ite_eq_right h, decBool_t_m2c h]; rfl

/-- **`iota_case3_at` refines `iotaCase3At`, both outcomes**: the errors are
`former_never_zero_at`'s (the `whnf` slot's, `fnza_ref`). -/
theorem ic3_ref (p : Prog) (hp : IotaProg4 p) (hz : FnzaProg p) (n F : Nat) (hk : KnotUpTo p n)
    (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (m : Mem) (a : AState)
    (M : ModeMaps) (isK cq us : Word) (cvj : IConstantVal) (np nf : Nat)
    (hS : CoreS dn m a vis fe M eb) (hci : decCI (erecP m) cq.toNat = some (.ctorInfo cvj np nf))
    (hus : HW us) :
    RefE (KnotUpToE p n) (ic3E p (n + 1) m mode vis isK cq us)
      (iotaCase3At (coreKnot (decMode mode) (decEager mode) fe id F) fe (isK != 0) cvj (decI us)) a
      (CorePost decBool dn m vis fe M eb ResH) := by
  have hR := hS.arena.base
  by_cases hK : isK ≠ 0
  · rw [ic3E.arm1 _ _ _ _ _ _ _ _ hK]
    have hK' : (isK != 0) = true := by simpa using hK
    unfold iotaCase3At; rw [ite_eq_left hK']
    exact RefE.ret rfl (CorePost.ret hS rfl (by unfold ResH HW; decide))
  have hK0 : isK = 0 := Classical.not_not.mp hK
  rw [ic3E.arm2 _ _ _ _ _ _ _ _ hK0]
  have hK' : (isK != 0) = false := by rw [hK0]; rfl
  unfold iotaCase3At; rw [hK', ite_eq_right (by simp)]
  cases n with
  | zero => rw [callW_zero, liftE_none, ic3E.k_ctor_family.none]; exact RefE.of_cls0 (by simp)
  | succ k =>
  rcases c1 : callW p (k + 1) "ctor_family" [vis, cq] m with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, ic3E.k_ctor_family.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨t₁, ht₁, -, hW⟩ := triple_of_callW
    (ctorFamily_spec p hp.ctorFamily k ⟨m, Locals.init []⟩ vis cq) c1
  obtain ⟨e1, res, hrun1, hnone, hsome⟩ := cfam_ok p hp.toIotaProg' hS hci hW
  have em : m = m₁ := e1.symm.trans ht₁
  subst em
  refine RefE.bind_right hrun1 ?_
  by_cases f0 : r₁.headD 0 = 0
  · rw [ic3E.k_ctor_family.arm1 _ _ _ _ _ _ _ f0, hnone f0]
    exact RefE.ret rfl (CorePost.ret hS rfl (by unfold ResH HW; decide))
  rw [ic3E.k_ctor_family.eq_2, ite_eq_right f0]
  obtain ⟨cvT, caps, rfl, hciT, T, hfT⟩ := hsome f0
  obtain ⟨-, hlen, -, -⟩ := decCV_rd (erRdOK m) (decCI_ind_cv' hciT)
  dsimp only
  -- the comparand levels' length
  rcases c2 : callW p (k + 1) "ls_node" [us] m with _ | ⟨r₂, m₂⟩
  · rw [liftE_none, ic3E.k_ls_node.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨t₂, ht₂, hts, hne, hr2⟩ := triple_of_callW (lsNode_spec p hp.lvl.lsnode (k + 1) ⟨m, Locals.init []⟩ us) c2
  have e2 : m = m₂ := by rw [← ht₂, hts]
  subst e2
  have hne' : lsNodeW m us ≠ [] := by rw [← hr2]; exact hne
  obtain ⟨o, l, hol⟩ : ∃ o l, r₂ = [o, l] := by
    rcases lsNodeW_cases m us with h | ⟨o, l, h⟩
    · exact absurd h hne'
    · exact ⟨o, l, hr2.trans h⟩
  have hvl := lsNodeW_viewLen hR hus (hr2.symm.trans hol)
  subst hol
  refine RefE.bind_right (by rw [viewLsLen_run, hvl]) ?_
  dsimp only
  have hlen' : (erRd m (r₁.tail.headD 0 + 3)).toNat = cvT.levelParams.length := hlen.symm
  by_cases hl : erRd m (r₁.tail.headD 0 + 3) ≠ l
  · rw [ic3E.k_ls_node.arm1 _ _ _ _ _ _ _ _ _ (by simpa using hl)]
    have hb : (cvT.levelParams.length == l.toNat) = false := by
      rw [← hlen']; simpa using fun e => hl (UInt64.toNat_inj.mp e)
    rw [hb, ite_eq_right (by simp)]
    exact RefE.ret rfl (CorePost.ret hS rfl (by unfold ResH HW; decide))
  rw [ic3E.k_ls_node.arm2 _ _ _ _ _ _ _ _ _ (by simpa using hl)]
  have hb : (cvT.levelParams.length == l.toNat) = true := by
    rw [← hlen', Classical.not_not.mp hl]; simp
  rw [hb, ite_eq_left rfl]
  -- `former_never_zero_at`
  have hks : ∃ ks, cvT.levelParams.mapM (denoteN a.store.ns) = some ks := hS.den.constLps T _ hfT
  have hlsd : ∃ ls, denoteLs a.store.lss (decI us) = some ls :=
    hS.den.lsAll _ (by obtain ⟨ids, e, -⟩ := lsNodeW_view hR hus hne'; rw [e]; rfl)
  have hf := fnza_ref p hz k F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode hm4 hebm
    m a M _ us cvT caps hS hciT hks hus hlsd
  refine RefE.bind_coreE (w := id) (fun _ => ic3E.k_former_never_zero_at.none ..)
    (fun (hG : KnotUpToE p (k + 1)) => hG.mono (Nat.le_succ _)) hf
    fun r4 m4 _ _ M4 hS4 _ => ?_
  rw [ic3E.k_former_never_zero_at.eq_2]
  exact RefE.ret rfl (CorePost.ret hS4 (decBool_ite0 r4).symm (by
    show HW (if r4.headD 0 = 0 then (1 : Word) else 0); unfold HW; split <;> decide))

end L.Arena
