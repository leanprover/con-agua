import ConAgua.Arena.IndT.Install1
import ConAgua.Arena.IndSumSpec12

/-!
# `checkStructFieldSortsI` under `StageC` (lane `indstaget`)

`check_struct_field_sorts_i`'s model at `realCall p`, from `StageC` and con-ron's preconditions of
`checkStructFieldSortsI_spec` (the opened fields denote; each inferred field type scoped at its
depth), its twin side transcribed from that spec's proof: `fvarTypeD` (`fvarTypeD_run`: the state
unchanged), `inferTypeCore` (`inferC_rsim`), `ensureSortCore` (`ensureSortC_rsim`), the universe
bound `sfbT` (`sfbT_cstep`: `readLevelM_pstep` twice, or the zero pin and `lvlEq?_spec`), the
write (twin side none), the recursion at the extended store.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

open ConRon.Bridge ConRon.Bridge.Inductives in
/-- **The twin's universe bound for one field is a core step** (con-ron's
`checkStructFieldSortsI_spec`, its middle: `readLevelM_pstep` twice; or nothing; or the zero pin
and `lvlEq?_spec`). -/
theorem sfbT_cstep {env : ConLeche.Env} {fe : IFEnv} {isProp large : Bool} {s : LIdx}
    {idxArgs : List EIdx} {fv : EIdx} {u : LIdx} {a a' : AState} (hok : CheckOK V env fe a)
    (h : (sfbT isProp large s idxArgs fv u).run a = .ok ((), a')) : CoreStep V env fe a a' := by
  have h' : sfbT isProp large s idxArgs fv u a = .ok ((), a') := h
  unfold sfbT at h'
  cases isProp with
  | false =>
    simp only [Bool.not_false, ite_true] at h'
    obtain ⟨lu, s5, k5, z5⟩ := AM.bind_ok h'
    have c5 : CoreStep V env fe a s5 := (readLevelM_pstep hok.state k5).toCore hok
    obtain ⟨ls, s6, k6, z6⟩ := AM.bind_ok z5
    have c6 : CoreStep V env fe s5 s6 := (readLevelM_pstep c5.ok.state k6).toCore c5.ok
    obtain ⟨b, s7, k7, z7⟩ := AM.bind_ok z6
    cases hleq : ConLeche.Level.leq lu ls with
    | none =>
      rw [hleq] at k7; simp only [ConRon.Arena.liftFueled] at k7
      exact absurd k7 (fun h => AM.fail_ok h)
    | some bb =>
    rw [hleq] at k7; simp only [ConRon.Arena.liftFueled] at k7
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k7
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ite_false, Bool.not_false, ite_true] at z7
      first
        | exact absurd z7 (fun h => AM.fail_ok h)
        | (obtain ⟨_, _, k, _⟩ := AM.bind_ok z7; exact absurd k (fun h => AM.fail_ok h))
    | true =>
      simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false] at z7
      obtain ⟨-, rfl⟩ := AM.pure_ok z7
      exact c5.trans c6
  | true =>
    cases large with
    | false =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h'
      obtain ⟨-, rfl⟩ := AM.pure_ok h'
      exact CoreStep.refl hok
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at h'
      obtain ⟨z, s5, k5, z5⟩ := AM.bind_ok h'
      obtain ⟨hs5, -⟩ := zeroLevel_run hok.pins k5
      rw [hs5] at z5
      obtain ⟨vv, s6, k6, z6⟩ := AM.bind_ok z5
      obtain ⟨hok6, hst6, hp6, -⟩ :=
        AM.of_run (P := fun t => t = a) rfl k6 (Core.lvlEq?_spec a u z hok)
      have c6 : CoreStep V env fe a s6 := ⟨hok6, by rw [hst6]; exact Ext.refl _, hp6⟩
      split at z6
      · first
          | (obtain ⟨-, rfl⟩ := AM.pure_ok z6; exact c6)
          | exact absurd z6 (fun h => AM.fail_ok h)
          | (obtain ⟨_, _, k, _⟩ := AM.bind_ok z6; exact absurd k (fun h => AM.fail_ok h))
      · first
          | (obtain ⟨-, rfl⟩ := AM.pure_ok z6; exact c6)
          | exact absurd z6 (fun h => AM.fail_ok h)
          | (obtain ⟨_, _, k, _⟩ := AM.bind_ok z6; exact absurd k (fun h => AM.fail_ok h))

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`check_struct_field_sorts_i_go` under `StageC`** (twin side: con-ron's
`checkStructFieldSortsI_spec`'s proof). -/
theorem csfW_okC (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (isProp large s nP fo fl io il res j : Word) (m0 : Mem) (k : Nat)
      (acc : List LIdx) (fvs idxArgs : List EIdx) (fvsP : List ConLeche.Expr),
    StageC dn vis fe env m a → AbsOK m → IWGrow m0 m → iwTop m0 ≤ res.toNat →
    res.toNat + j.toNat + k ≤ iwTop m →
    decHL m (res.toNat + j.toNat) k = some acc →
    decHL m0 fo.toNat fl.toNat = some fvs → fo.toNat + fl.toNat ≤ iwTop m0 →
    decHL m0 io.toNat il.toNat = some idxArgs → io.toNat + il.toNat ≤ iwTop m0 →
    H s → nP.toNat + j.toNat < 2 ^ 64 →
    Frontend.denoteEList a.store fvs = some fvsP →
    (∀ i, i < j.toNat → ∀ x, fvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD) →
    Sim (csfW (realCall p) n m vis isProp large s nP fo fl io il res j)
      (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs j.toNat) a
      (fun _ xs m' a' => StageC dn vis fe env m' a' ∧ IWGrow m0 m' ∧
        decHL m' res.toNat (j.toNat + k) = some (xs ++ acc) ∧ res.toNat + j.toNat + k ≤ iwTop m' ∧
        AbsOK m') := by
  induction n with
  | zero => intros; exact Sim.of_none
  | succ n ih =>
  intro m a isProp large s nP fo fl io il res j m0 k acc fvs idxArgs fvsP hC hA hg0 hr0 hroom hacc
    hfvs hfb hidx hib hs hnj hfP hws
  have hS := hC.stage
  by_cases hj : j = 0
  · subst hj
    rw [csfW_zero (realCall p) n m vis isProp large s nP fo fl io il res 0 rfl]
    simp only [UInt64.toNat_zero, Nat.add_zero, Nat.zero_add] at hacc hroom ⊢
    simp only [checkStructFieldSortsI]
    exact Sim.ret ⟨hC, hg0, by simpa using hacc, hroom, hA⟩
  obtain ⟨J, hjJ⟩ : ∃ J, j.toNat = J + 1 :=
    ⟨j.toNat - 1, by have : j.toNat ≠ 0 := fun e => hj (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hJ : (j - 1).toNat = J := by rw [sumToNat_pred hj]; omega
  by_cases hl : fl ≤ j - 1
  · rw [csfW_oob (realCall p) n m vis isProp large s nP fo fl io il res j hj hl]; exact Sim.of_none
  rw [csfW_step (realCall p) n m vis isProp large s nP fo fl io il res j hj hl]
  have hJl : J < fl.toNat := by
    have : ¬ fl.toNat ≤ (j - 1).toNat := fun e => hl (UInt64.le_iff_toNat_le.mpr e)
    omega
  have hT := hS.lt64 (x := iwTop m) (Nat.le_refl _)
  have hgT := hg0.1
  -- the field
  have hfvs' : decHL m fo.toNat fl.toNat = some fvs := by rw [decHL_grow hg0 hfb]; exact hfvs
  obtain ⟨w, hw, hwl, hwd⟩ := decHL_get' hfvs' J hJl (by omega)
  have efo : fo + (j - 1) = UInt64.ofNat (fo.toNat + J) := by
    apply UInt64.toNat_inj.mp; rw [sum_toNat_add (by omega), hJ]; simp; omega
  rw [efo, hw]
  rw [hjJ, checkStructFieldSortsI_succ]
  have hget : fvs[J]? = some (decI w) := by
    rw [List.getElem?_eq_getElem (by rw [decHL_length m hfvs']; exact hJl), hwd]
  obtain ⟨aP, haP, hda⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? fvs fvsP hfP J (decI w) hget
  have hwsa := hws J (by omega) aP haP
  refine Sim.bind_twin (x := decI w) (a₁ := a) (by rw [hget]; rfl) ?_
  have hdep : (nP + (j - 1)).toNat = nP.toNat + J := by rw [sum_toNat_add (by omega), hJ]
  refine Sim.bindK (K := csfK1 _ (realCall p) n vis isProp large s nP io il w res j) rfl (fun _ _ => rfl)
    (Sim.withFr (F := AbsOK) (Sim.withRunC (sumSim_of_relW (ftdF_ok dn vis fe w hwl) hS))
      (fun _ _ e => ftdF_afr e hA)) fun rt t m1 a1 hQ => ?_
  obtain ⟨⟨⟨hS1, hg1, ht1, ht⟩, hrun1⟩, hA1⟩ := hQ
  obtain ⟨ha1, htd⟩ := ConRon.Bridge.Inductives.fvarTypeD_run hC.check.state hda hrun1
  rw [ha1] at hS1 ⊢
  have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  rw [csfK1_some]
  have hdt : denoteE a.store (decI (rt.headD 0)) = some aP.fvarTypeD := by rw [ht]; exact htd
  have h2 := inferC_rsim hq henv n (by omega) hC1 hA1 (nP + (j - 1)) (rt.headD 0) ht1 hdt
    (by rw [hdep]; exact hwsa)
  rw [hdep, ht] at h2
  refine Sim.bindK (K := csfK2 _ (realCall p) n vis isProp large s nP io il w res j) rfl (fun _ _ => rfl)
    (RSim.toSim h2) fun ry ty m2 a2 hQ => ?_
  obtain ⟨hC2, hg2, ⟨hy1, hy⟩, hA2, c2, tyP, htyP, hwty⟩ := hQ
  dsimp only at hC2 hg2 hy1 hy hA2
  rw [csfK2_some]
  have h3 := ensureSortC_rsim hq henv n (by omega) hC2 hA2 (nP + (j - 1)) (ry.headD 0) hy1
    (by rw [hy]; exact htyP) (by rw [hdep]; exact hwty)
  rw [hdep, hy] at h3
  refine Sim.bindK (K := csfK3 _ n isProp large s io il w res j) rfl (fun _ _ => rfl)
    (RSim.toSim h3) fun ru u m3 a3 hQ => ?_
  obtain ⟨hC3, hg3, ⟨hu1, hu⟩, hA3, c3, -⟩ := hQ
  dsimp only at hC3 hg3 hu1 hu hA3
  rw [csfK3_some]
  have hg03 := ((hg0.trans hg1).trans hg2).trans hg3
  have hidx3 : decHL m3 io.toNat il.toNat = some idxArgs := by rw [decHL_grow hg03 hib]; exact hidx
  have h4 := cfbW_ok n m3 a3 isProp large s io il w (ru.headD 0) idxArgs hC3.stage hu1 hs hwl hidx3
    (by have := hg03.1; omega)
  rw [hu] at h4
  refine Sim.bindK (K := csfK4 _ res j (ru.headD 0)) rfl (fun _ _ => rfl)
    (Sim.withFr (F := AbsOK) (Sim.withRunC h4) (fun _ _ e => cfbW_afr _ _ _ _ _ _ _ _ _ _ _ e hA3))
    fun _ _ m4 a4 hQ => ?_
  obtain ⟨⟨⟨hS4, hg4⟩, hrun4⟩, hA4⟩ := hQ
  have c4 := sfbT_cstep hC3.check hrun4
  have hC4 : StageC dn vis fe env m4 a4 := hC3.of_check hS4 hA4 c4.ok c4.ext
  rw [csfK4_some]
  -- the write
  have hg14 := ((hg1.trans hg2).trans hg3).trans hg4
  have hres1 : (res + (j - 1)).toNat = res.toNat + J := by rw [sum_toNat_add (by omega), hJ]
  have hsz4 : res.toNat + J < (m4.arr64 IW).size := by
    obtain ⟨h1, -, -, -, -⟩ := hS4.2; have := hg14.1; omega
  have hacc4 : decHL m4 (res.toNat + J + 1) k = some acc := by
    rw [decHL_grow hg14 (by omega)]; rw [show res.toNat + J + 1 = res.toNat + j.toNat by omega]; exact hacc
  have hacc' := sumDecHL_write_front m4 _ k _ (ru.headD 0) acc hres1 hsz4 hu1 hacc4
  rw [hu] at hacc'
  have htop' : iwTop (m4.set64 IW (res + (j - 1)) (ru.headD 0)) = iwTop m4 := by
    simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hAw := set64IW_afr m4 (res + (j - 1)) (ru.headD 0) hA4
  have hCw : StageC dn vis fe env (m4.set64 IW (res + (j - 1)) (ru.headD 0)) a4 :=
    hC4.of_pstep (hS4.set_iw _ _) hAw (PStep.refl hC4.check.state)
  have hx14 := c2.ext.trans (c3.ext.trans c4.ext)
  have h5 := ih (by omega) (m4.set64 IW (res + (j - 1)) (ru.headD 0)) a4 isProp large s nP fo fl io il
    res (j - 1) m0 (k + 1) (u :: acc) fvs idxArgs fvsP hCw hAw
    ((hg03.trans hg4).set_iw _ _ (by omega)) hr0 (by rw [htop', hJ]; have := hg14.1; omega)
    (by rw [hJ]; exact hacc') hfvs hfb hidx hib hs (by omega)
    (ConRon.Bridge.denoteEList_ext hx14 _ _ hfP) (fun i hi => hws i (by omega))
  rw [hJ] at h5
  refine Sim.bindK (K := csfK5) rfl (fun _ _ => rfl) h5 fun _ xs m5 a5 hQ => ?_
  obtain ⟨hC5, hg5, hd5, ht5, hA5⟩ := hQ
  refine Sim.ret ⟨hC5, hg5, ?_, by omega, hA5⟩
  rw [show J + 1 + k = J + (k + 1) by omega, hd5]; simp

include hq henv in
/-- **`check_struct_field_sorts_i` under `StageC`**: the allocation (L only), then `csfW_okC`. -/
theorem fsortsW_okC (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem)
    (a : AState) (isProp large s nP fo fl io il nW : Word) (fvs idxArgs : List EIdx)
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hfvs : decHL m fo.toNat fl.toNat = some fvs)
    (hfb : fo.toNat + fl.toNat ≤ iwTop m) (hidx : decHL m io.toNat il.toNat = some idxArgs)
    (hib : io.toNat + il.toNat ≤ iwTop m) (hs : H s) (hnj : nP.toNat + nW.toNat < 2 ^ 64)
    {fvsP : List ConLeche.Expr} (hfP : Frontend.denoteEList a.store fvs = some fvsP)
    (hws : ∀ i, i < nW.toNat → ∀ x, fvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD) :
    Sim (fsortsW (realCall p) n m vis isProp large s nP fo fl io il nW)
      (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs nW.toNat) a
      (fun r xs m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ AbsOK m') := by
  unfold fsortsW
  cases hal : allocW m nW with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨res, m1⟩ := y
  rw [fsortsK1_some]
  obtain ⟨hS1, hg1, hrt, ht1⟩ := allocW_stage hal hC.stage
  have hA1 := allocW_afr hal hA
  have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  refine sumSim_map (K := fsortsK2 res nW) rfl (fun _ _ => rfl)
    (csfW_okC hq henv n hn m1 a isProp large s nP fo fl io il res nW m 0 [] fvs idxArgs fvsP hC1 hA1 hg1
      (by omega) (by omega) (by simp [decHL, hslice?]) hfvs hfb hidx hib hs hnj hfP hws)
    fun _ xs m' a' hQ => ?_
  obtain ⟨hC', hg', hd', ht', hA'⟩ := hQ
  exact ⟨hC', hg', by simpa using hd', by simpa using ht', hA'⟩

include hq henv in
/-- **`check_struct_field_sorts_i` refines `checkStructFieldSortsI .verified`** under `StageC` (the
knot's `infer_type_core`, `ensure_sort_core`; the fields' denotations and scoping as con-ron's
`checkStructFieldSortsI_spec` asks): the sorts in a fresh `IW` slice. -/
@[refines ConRon.Arena.checkStructFieldSortsI]
theorem checkStructFieldSortsI_refinesC (hg : p.lookup "sl_get" = some slGet)
    (hpw : p.lookup "pin_word" = some pinWordL)
    (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
    (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
    (hgo : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL)
    (hia : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL) (hftd : FtdF p)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (isProp large s nP fo fl io il nW : Word)
    (fvs idxArgs : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hfvs : decHL s₀.mem fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem)
    (hidx : decHL s₀.mem io.toNat il.toNat = some idxArgs) (hib : io.toNat + il.toNat ≤ iwTop s₀.mem)
    (hs : H s) (hnj : nP.toNat + nW.toNat < 2 ^ 64) {fvsP : List ConLeche.Expr}
    (hfP : Frontend.denoteEList a₀.store fvs = some fvsP)
    (hws : ∀ i, i < nW.toNat → ∀ x, fvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_struct_field_sorts_i"
      [vis, isProp, large, s, nP, fo, fl, io, il, nW]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs
        nW.toNat) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (checkStructFieldSortsI V fe (isProp != 0) (large != 0)
        (decI s) nP.toNat fvs idxArgs nW.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs
          idxArgs nW.toNat) a₀) ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (fsortsW_spec p hg hpw het hc hb hgo hia hp hftd (realCall p) (realCall_spec p) n
    s₀ vis isProp large s nP fo fl io il nW) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hok, hC', hg', hd, -, hA'⟩ :=
    (fsortsW_okC hq henv n hn _ a₀ isProp large s nP fo fl io il nW fvs idxArgs hC hA hfvs hfb hidx hib
      hs hnj hfP hws).run hm
  exact ⟨hl, hok, hC', hg', hd, hA'⟩

end sims

end L.Ind
