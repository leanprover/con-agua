module

public import ConAgua.Arena.FormerNZRef
public import ConAgua.Arena.WhnfIotaRefine4
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# Case 3 of the ι split: `ctor_family`, `iota_case3_at`

`ctor_family(vis, T)` (the family stored at a constructor's `induct`: one lookup) by its generated
model `cfamW` and the run lemma `cfam_ok`; `iota_case3_at(mode, vis, isK, T, us)` by its unified
model `ic3E` and `ic3_ref` (both outcomes: the errors are `former_never_zero_at`'s, `fnza_ref`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `ctor_family(vis, T)` -/

/-- **`ctor_family`'s model**: one `env_find`, the record's kind. -/
l_model ctorFamily_spec (p : Prog) (hp : p.lookup "ctor_family" = some ctorFamilyL)
  fns [hp ↦ cfamW list]
  specs [callW_spec p n "env_find"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- An inductive record by its kind word `3`. -/
theorem decCI_ind_rd {R : Nat → Option Word} {rd : Word → Word} {q : Word}
    {ci : IConstantInfo} (hR : RdOK R rd) (h : decCI R q.toNat = some ci) :
    (rd q = 3 → ∃ cv caps, ci = .indInfo cv caps) ∧ (rd q ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) := by
  have := decCI_split hR h
  exact ⟨fun h3 => by obtain ⟨cv, caps, e, -⟩ := this.2.2.1 h3; exact ⟨cv, caps, e⟩, this.2.2.2.1⟩

/-- **`ctor_family` as a run**: the memory unchanged; the twin's family at the handle `T`, a found
one decoding at the returned record. -/
theorem cfam_ok (p : Prog) (hp : IotaProg' p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m : Mem}
    {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    {T : Word} (hT : HW T) {r : List Word} {m' : Mem}
    (h : cfamW p n m vis T = some (r, m')) :
    m' = m ∧ (r.headD 0 = 0 → ctorFamily fe (decI T) = none) ∧
      (r.headD 0 ≠ 0 → ∃ cvT caps, ctorFamily fe (decI T) = some (cvT, caps) ∧
        decCI (erecP m) (r.tail.headD 0).toNat = some (.indInfo cvT caps) ∧
        fe.find? (decI T) = some (.indInfo cvT caps)) := by
  cases n with
  | zero => simp [cfamW] at h
  | succ n =>
  simp only [cfamW] at h
  rcases c4 : callW p n "env_find" [T, vis] m with _ | ⟨r₄, m₄⟩
  · rw [c4] at h; simp [cfamW.k_env_find] at h
  rw [c4] at h
  obtain ⟨t₄, ht₄, hm₄, -, hfind, hdec⟩ := triple_of_callW
    (envFind_refines p hp.envrow hp.baserow hp.envfind n ⟨m, Locals.init []⟩ vis _ hS.env hT) c4
  have e4 : m = m₄ := hm₄.symm.trans ht₄
  subst e4
  by_cases h0 : r₄.headD 0 = 0
  · rw [cfamW.k_env_find.arm1 _ _ _ h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hnone : fe.find? (decI T) = none := by rw [hfind]; simp only [envFound, h0, ↓reduceIte]
    exact ⟨rfl, fun _ => by simp only [ctorFamily, hnone], fun h0 => absurd rfl h0⟩
  obtain ⟨ci, hci4⟩ := hdec h0
  have hf' : fe.find? (decI T) = some ci := by
    rw [hfind]; simp only [envFound, h0, ↓reduceIte]; exact hci4
  have hk := decCI_ind_rd (erRdOK m) hci4
  by_cases k3 : erRd m (r₄.tail.headD 0) ≠ 3
  · rw [cfamW.k_env_find.arm2 _ _ _ h0 (by simpa [erRd] using k3)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, fun _ => ?_, fun h0 => absurd rfl h0⟩
    simp only [ctorFamily, hf']
    cases ci <;> first | exact absurd rfl (hk.2 k3 _ _) | rfl
  rw [cfamW.k_env_find.arm3 _ _ _ h0 (by simpa [erRd] using k3)] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨cvT, caps, rfl⟩ := hk.1 (Classical.not_not.mp k3)
  exact ⟨rfl, fun h => by simp at h, fun _ => ⟨cvT, caps, by simp only [ctorFamily, hf'], hci4, hf'⟩⟩

/-! ## `iota_case3_at(mode, vis, isK, T, us)` -/

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
  · rw [ite_eq_left h, L.Arena.decBool_false_of h]; rfl
  · rw [ite_eq_right h, L.Arena.decBool_true_of h]; rfl

/-- **`iota_case3_at` refines `iotaCase3At`, both outcomes**: the errors are
`former_never_zero_at`'s (the `whnf` slot's, `fnza_ref`). -/
theorem ic3_ref (p : Prog) (hp : IotaProg4 p) (hz : FnzaProg p) (n F : Nat) (hk : KnotUpTo p n)
    (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (m : Mem) (a : AState)
    (M : ModeMaps) (isK T us : Word)
    (hS : CoreS dn m a vis fe M eb) (hT : HW T) (hus : HW us) :
    RefE (KnotUpToE p n) (ic3E p (n + 1) m mode vis isK T us)
      (iotaCase3At (coreKnot (decMode mode) (decEager mode) fe id F) fe (isK != 0) (decI T) (decI us)) a
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
  rcases c1 : callW p (k + 1) "ctor_family" [vis, T] m with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, ic3E.k_ctor_family.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨t₁, ht₁, -, hW⟩ := triple_of_callW
    (ctorFamily_spec p hp.ctorFamily (k + 1) ⟨m, Locals.init []⟩ vis T) c1
  obtain ⟨e1, hnone, hsome⟩ := cfam_ok p hp.toIotaProg' hS hT hW
  have em : m = m₁ := e1.symm.trans ht₁
  subst em
  by_cases f0 : r₁.headD 0 = 0
  · rw [ic3E.k_ctor_family.arm1 _ _ _ _ _ _ _ f0, hnone f0]
    exact RefE.ret rfl (CorePost.ret hS rfl (by unfold ResH HW; decide))
  rw [ic3E.k_ctor_family.eq_2, ite_eq_right f0]
  obtain ⟨cvT, caps, hfam, hciT, hfT⟩ := hsome f0
  rw [hfam]
  obtain ⟨-, hlen, -, -⟩ := decCV_rd (erRdOK m) (L.Arena.decCI_ind_cv hciT)
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
  · rw [ic3E.k_ls_node.arm1 _ _ _ _ _ _ _ _ _ (by simpa [erRd] using hl)]
    have hb : (cvT.levelParams.length == l.toNat) = false := by
      rw [← hlen']; simpa using fun e => hl (UInt64.toNat_inj.mp e)
    rw [hb, ite_eq_right (by simp)]
    exact RefE.ret rfl (CorePost.ret hS rfl (by unfold ResH HW; decide))
  rw [ic3E.k_ls_node.arm2 _ _ _ _ _ _ _ _ _ (by simpa [erRd] using hl)]
  have hb : (cvT.levelParams.length == l.toNat) = true := by
    rw [← hlen', Classical.not_not.mp hl]; simp
  rw [hb, ite_eq_left rfl]
  -- `former_never_zero_at`
  have hks : ∃ ks, cvT.levelParams.mapM (denoteN a.store.ns) = some ks := hS.den.constLps (decI T) _ hfT
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
