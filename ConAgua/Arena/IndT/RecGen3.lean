import ConAgua.Arena.DeclValT
import ConAgua.Arena.RecGenSpec7
import ConAgua.Arena.IndT.Base

/-!
# `classConstOk` under `StageT` (lane `indstaget`)

`class_const_ok`'s model `ccoW` at `realCall p`: `install_header`'s guards under `StageT`
(`ihW_okT`; on success they leave the same state as `classConstOk`'s own guards, which differ in
the error messages only: `classConstOk_of_ih`), then the knot's `infer_type_core` and
`ensure_sort_core` (`Base.lean`).
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem failAM_run {α : Type} (e : CheckError) (s : AState) :
    (fail e : AM α).run s = .error e := rfl

theorem exc_error_bind {α β : Type} (e : CheckError) (f : α → Except CheckError β) :
    (Except.error e >>= f) = .error e := rfl

theorem classConstOk_of_ih (mode : ConLeche.CheckMode) {fe : IFEnv} {cv : IConstantVal}
    {a a' : AState} (h : (installHeader fe cv).run a = .ok ((), a')) :
    (ConRon.Arena.classConstOk mode fe cv).run a = (do
        let stype ← inferTypeCore mode fe checkFuel 0 cv.type
        let _u ← ensureSortCore mode fe checkFuel 0 stype).run a' := by
  unfold installHeader at h
  unfold ConRon.Arena.classConstOk
  by_cases h1 : (fe.find? cv.name).isSome = true
  · simp [h1, failAM_run, StateT.run_bind, exc_error_bind] at h
  simp only [h1, if_false, Bool.false_eq_true, StateT.run_bind] at h ⊢
  cases h2 : reservedBasisNames.run a with
  | error e => simp [h2, exc_error_bind] at h
  | ok p2 =>
  obtain ⟨b2, a2⟩ := p2
  simp only [h2, exc_ok_bind'] at h ⊢
  by_cases c2 : b2.contains cv.name = true
  · simp only [c2, ↓reduceIte, failAM_run, StateT.run_bind, exc_error_bind, reduceCtorEq] at h
  simp only [c2, if_false, Bool.false_eq_true, StateT.run_bind] at h ⊢
  cases h3 : (NIdx.isProjFnShape cv.name).run a2 with
  | error e => simp [h3, exc_error_bind] at h
  | ok p3 =>
  obtain ⟨b3, a3⟩ := p3
  simp only [h3, exc_ok_bind'] at h ⊢
  by_cases c3 : b3 = true
  · simp only [c3, ↓reduceIte, failAM_run, StateT.run_bind, exc_error_bind, reduceCtorEq] at h
  simp only [c3, if_false, Bool.false_eq_true, StateT.run_bind] at h ⊢
  cases c4 : nameNodup cv.levelParams
  · simp only [c4, Bool.false_eq_true, ↓reduceIte, failAM_run, StateT.run_bind, exc_error_bind,
      reduceCtorEq, not_false_eq_true] at h
  simp only [c4, ↓reduceIte, not_true_eq_false, StateT.run_bind] at h ⊢
  cases h5 : (looseBVarsBoundedFast coreWalkFuel 0 cv.type).run a3 with
  | error e => simp [h5, exc_error_bind] at h
  | ok p5 =>
  obtain ⟨b5, a5⟩ := p5
  simp only [h5, exc_ok_bind'] at h ⊢
  cases b5
  · simp only [Bool.false_eq_true, ↓reduceIte, failAM_run, StateT.run_bind, exc_error_bind,
      reduceCtorEq, not_false_eq_true] at h
  simp only [↓reduceIte, not_true_eq_false, StateT.run_bind] at h ⊢
  cases h6 : (hasFvarFast coreWalkFuel cv.type).run a5 with
  | error e => simp [h6, exc_error_bind] at h
  | ok p6 =>
  obtain ⟨b6, a6⟩ := p6
  simp only [h6, exc_ok_bind'] at h ⊢
  cases b6 with
  | true => simp only [↓reduceIte, failAM_run, StateT.run_bind, exc_error_bind, reduceCtorEq] at h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind] at h ⊢
  cases h7 : (allLevelParamsDefined cv.levelParams cv.type).run a6 with
  | error e => simp [h7, exc_error_bind] at h
  | ok p7 =>
  obtain ⟨b7, a7⟩ := p7
  simp only [h7, exc_ok_bind'] at h ⊢
  cases b7
  · simp only [Bool.false_eq_true, ↓reduceIte, failAM_run, StateT.run_bind, exc_error_bind,
      reduceCtorEq, not_false_eq_true] at h
  simp only [↓reduceIte, not_true_eq_false, StateT.run_bind] at h ⊢
  cases h8 : (constsResolveFFast fe cv.type).run a7 with
  | error e => simp [h8, exc_error_bind] at h
  | ok p8 =>
  obtain ⟨b8, a8⟩ := p8
  simp only [h8, exc_ok_bind'] at h ⊢
  cases b8
  · simp only [Bool.false_eq_true, ↓reduceIte, failAM_run, StateT.run_bind, exc_error_bind,
      reduceCtorEq, not_false_eq_true] at h
    exfalso
    cases hs : (strLitSupported fe).run a8 with
    | error e => simp [hs, exc_error_bind] at h
    | ok q =>
      simp only [hs, exc_ok_bind'] at h
      cases hu : (unresolvedConstsErrorL q.1 "type" cv.type).run q.2 <;>
        simp [hu, exc_error_bind, exc_ok_bind'] at h
  simp only [↓reduceIte, not_true_eq_false, StateT.run_bind] at h ⊢
  have : a8 = a' := by cases h; rfl
  subst this
  rfl

section sims
variable {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) (hCrk : CrKeep p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv}

local notation "V" => ConLeche.CheckMode.verified

include hq hApd hCrk in
/-- **`class_const_ok` under `StageT`**: `install_header`'s guards (`ihW_okT`, the same guards as
`classConstOk`'s, `classConstOk_of_ih`), then the knot's `infer_type_core` and
`ensure_sort_core`. -/
theorem ccoW_simT (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (q : Word)
    (cv : IConstantVal) (hS : StageT dn vis fe m a) (hq' : decCV (erecP m) q.toNat = some cv)
    (hqb : q.toNat + 3 < 2 ^ 64) (hA : AbsOK m)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) :
    RSim (ccoW (realCall p) n m vis q) (ConRon.Arena.classConstOk V fe cv) a
      (fun b a' x => KPT dn vis fe m decUnit b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [ccoW_eq]
  rintro b hb
  obtain ⟨⟨r1, m1⟩, h1, hb⟩ := of_K hb rfl
  obtain ⟨a1, hrun, hS1, hg1, -, hA1⟩ := ihW_okT hApd hCrk.crf h1 hS hq' hqb hlps hA.crMemo.crOK
  have hq1 : decCV (erA m1) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt hg1) hq'
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hq1
  have et : rdW (m1.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hwt
  have hA1 : AbsOK m1 := hA1 hA
  have hr : RSim (ccoK1 (realCall p) n vis q (some (r1, m1)))
      (do let stype ← inferTypeCore V fe checkFuel 0 cv.type
          let _u ← ensureSortCore V fe checkFuel 0 stype) a1
      (fun b a' x => KPT dn vis fe m decUnit b a' x ∧ AbsOK b.2) := by
    rw [ccoK1_some, et, hty]
    have hi := RSim.coreAbs hq.closed (by decide) hA1 (inferT_rsim hq n (by omega) hS1 0 wt hwtl)
    rw [show (0 : Word).toNat = 0 from rfl] at hi
    refine RSim.bind (K := ccoK2 (realCall p) n vis) rfl hi ?_
    rintro ⟨r2, m2⟩ st a2 - ⟨⟨hS2, hg2, hb2, rfl⟩, hA2⟩
    dsimp only at hS2 hg2 hb2 hA2
    rw [ccoK2_some]
    have he := RSim.coreAbs hq.closed (by decide) hA2
      (ensureSortT_rsim hq n (by omega) hS2 0 (r2.headD 0) hb2)
    rw [show (0 : Word).toNat = 0 from rfl] at he
    refine RSim.bind (K := ccoK3) rfl he ?_
    rintro ⟨r3, m3⟩ u a3 - ⟨⟨hS3, hg3, -⟩, hA3⟩
    rw [ccoK3_some]
    exact RSim.pure_some ⟨⟨hS3, (hg1.trans hg2).trans hg3, trivial⟩, hA3⟩
  obtain ⟨x, a', hr', hQ⟩ := hr b hb
  exact ⟨x, a', by rw [classConstOk_of_ih V hrun]; exact hr', hQ⟩

include hq hApd hCrk in
/-- **`class_const_ok` refines `classConstOk`** under `StageT` (the guards are `install_header`'s,
then the knot's `infer_type_core` and `ensure_sort_core`). -/
@[refines ConRon.Arena.classConstOk]
theorem classConstOk_refinesT (h : IhProg p)
    (hh : p.lookup "class_const_ok_header" = some classConstOkHeader)
    (hc : p.lookup "class_const_ok" = some classConstOkL) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (q : Word) (cv : IConstantVal) (hS : StageT dn vis fe s₀.mem a₀)
    (hq' : decCV (erecP s₀.mem) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hA : AbsOK s₀.mem) (hlps : ∃ ks, cv.levelParams.mapM (denoteN a₀.store.ns) = some ks) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_const_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classConstOk V fe cv) a₀ ∧
      KPT dn vis fe s₀.mem decUnit (r, s'.mem) (AM.st (ConRon.Arena.classConstOk V fe cv) a₀)
        (AM.res (ConRon.Arena.classConstOk V fe cv) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classConstOk_spec p h hh hc (realCall p) (realCall_spec p) n s₀ vis q)
    fun _ _ ⟨hl, hw⟩ =>
      let h := (ccoW_simT hq hApd hCrk n hn _ a₀ q cv hS hq' hqb hA hlps).am hw
      ⟨hl, h.1, h.2.1, h.2.2⟩

end sims

end L.Ind
