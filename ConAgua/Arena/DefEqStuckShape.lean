module

public import ConAgua.Arena.DefEqStuck
import ConAgua.Arena.InferBodySpine
public import ConAgua.Arena.WhnfIotaRefine
import ConAgua.Arena.IndView
import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.WhnfCoreRefine
import ConRon.Bridge.Grind
import all ConAgua.Arena.DefEq

@[expose] public section

/-!
# `eta_ctor_shape` refines `etaCtorShape` (lane `defeq`, helper `defeq-top`)

Reads only: `get_app_fn`, the head's `const` record, `env_find`, the constructor record's counts,
`get_app_args` (its slice dropped: the top put back). Shared helpers for the structure-η side:
`envFind_callW` (a run of `env_find`), `decCI_ctorF` (a constructor record's counts),
`getAppArgs_callW`, `CoreS.restoreTop` (the relation after the top is put back).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Shared helpers -/

-- RS2B ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **A run of `env_find`**: the memory unchanged, the twin's `find?` decoded, a hit decodes. -/
theorem envFind_callW {p : Prog} (hp : WhnfCoreProg p) {n : Nat}
    {m m' : Mem} {vis : Word} {fe : IFEnv} (hE : EnvR m vis fe) {k : Word} (hk : HW k)
    {r : List Word} (hc : callW p n "env_find" [k, vis] m = some (r, m')) :
    m' = m ∧ fe.find? (decI k) = envFound m (r.headD 0) (r.tail.headD 0) ∧
      (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP m) (r.tail.headD 0).toNat = some ci) := by
  sorry

-- RS2E

-- RS2B ronsync2 stage 2: commented out (statement at the old twin/L)
/-- A found record decodes to the twin's constant. -/
theorem find_of_found {m : Mem} {fe : IFEnv} {k : Word}
    {r : List Word} (hfind : fe.find? (decI k) = envFound m (r.headD 0) (r.tail.headD 0))
    (h0 : r.headD 0 ≠ 0) {ci : IConstantInfo}
    (hci : decCI (erecP m) (r.tail.headD 0).toNat = some ci) : fe.find? (decI k) = some ci := by
  rw [hfind]; simp only [envFound, h0, ↓reduceIte]; exact hci
-- RS2E

/-- **A constructor record's counts**: kind word `4`, parameters at `q + 5`, fields at `q + 6`. -/
theorem decCI_ctorF {a b : Array Word} {q : Word}
    {ci : IConstantInfo} (h : decCI (aread a) q.toNat = some ci) (hab : ArrExt (aread a) (aread b))
    (hsz : b.size < 2 ^ 63) :
    (rdW b q = 4 → ∃ cv, ci = .ctorInfo cv (rdW b (q + 5)).toNat (rdW b (q + 6)).toNat) ∧
    (rdW b q ≠ 4 → ∀ cv np nf, ci ≠ .ctorInfo cv np nf) := by
  sorry

/-- **A run of `get_app_args`** from `CoreS`: the twin's arguments as a slice at the old top. -/
theorem getAppArgs_callW {p : Prog} (hp : SpineProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn m a vis fe M eb) {e : Word} (he : HW e) {r : List Word}
    (hc : callW p n "get_app_args" [e] m = some (r, m')) :
    MemFrame [SPN] [136] m m' ∧ StackGrew m m' ∧ r.headD 0 = spTop m ∧
      spTop m' = spTop m + r.tail.headD 0 ∧
      ∃ xs, (getAppArgs coreWalkFuel (decE e)).run a = .ok (xs, a) ∧
        SpineR m' (r.headD 0) (r.tail.headD 0) xs.toArray := by
  obtain ⟨t, ht, -, h1, h2, h3, h4, h5⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (getAppArgs_refines p hp n ⟨m, Locals.init []⟩ a hS.arena.base e he hS.spn) hc
  subst ht
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **The top put back** after a run that only pushed (`MemFrame [SPN] [136]`, `StackGrew`). -/
theorem CoreS.restoreTop {dn : NIdx → Option ConLeche.Name} {m m₁ : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (hf : MemFrame [SPN] [136] m m₁) (hg : StackGrew m m₁)
    (h136 : (136 : Word).toNat < (m₁.arr64 CTL).size) :
    CoreS dn (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) a vis fe M eb ∧
      StackKept m (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) := by
  have hS₁ := hS.frame_stk hf (by simp) (by simp)
  have hS₂ := hS₁.frame_stk (MemFrame.setCtl m₁ 136 (rdW (m.arr64 CTL) 136)) (by simp) (by simp)
  exact ⟨hS₂, StackKept.restoreG hg h136⟩

/-- `restoreTop` without the bound: out of bounds the store is a no-op and the top reads `0` on
both sides (the frame keeps `CTL`'s size). -/
theorem CoreS.restoreTop' {dn : NIdx → Option ConLeche.Name} {m m₁ : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (hf : MemFrame [SPN] [136] m m₁) (hg : StackGrew m m₁) :
    CoreS dn (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) a vis fe M eb ∧
      StackKept m (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) := by
  by_cases h136 : (136 : Word).toNat < (m₁.arr64 CTL).size
  · exact hS.restoreTop hf hg h136
  have hfs := MemFrame.setCtl m₁ 136 (rdW (m.arr64 CTL) 136)
  refine ⟨(hS.frame_stk hf (by simp) (by simp)).frame_stk hfs (by simp) (by simp), ?_, ?_,
    fun i hi => ?_, hg.bstk.trans (BKept.of_frame hfs (by decide) (by decide)),
    hg.pool.trans (PoolGrew.of_frame hfs (by decide) (by decide))⟩
  · have hm : ¬ (136 : Word).toNat < (m.arr64 CTL).size := by rw [← hf.size CTL]; exact h136
    rw [spTop, spTop, rdW_set64, ite_eq_right (fun h => h136 h.2.2)]
    simp only [rdW, Array.getElem?_eq_none (Nat.le_of_not_lt h136), Array.getElem?_eq_none (Nat.le_of_not_lt hm)]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact hg.size
  · simp only [spW]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact hg.below i hi

/-! ## `eta_ctor_shape` -/

section ecs
variable (p : Prog) (n : Nat) (vis a : Word)

/-- After `get_app_args`: the top put back, the count test. -/
def ecsK3 (top q : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if (136 : Word).toNat < (m.arr64 CTL).size then
      if r.tail.headD 0 < rdW ((m.set64 CTL 136 top).arr64 EREC) (q + 6) then
        some (0, m.set64 CTL 136 top)
      else some (if r.tail.headD 0 - rdW ((m.set64 CTL 136 top).arr64 EREC) (q + 6) =
          rdW ((m.set64 CTL 136 top).arr64 EREC) (q + 5) then 1 else 0, m.set64 CTL 136 top)
    else none

/-- After `env_find`: a constructor record, then the arguments. -/
def ecsK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, m)
    else if rdW (m.arr64 EREC) (r.tail.headD 0) ≠ 4 then some (0, m)
    else ecsK3 (rdW (m.arr64 CTL) 136) (r.tail.headD 0) (callW p n "get_app_args" [a] m)

/-- **The model of `eta_ctor_shape`** past `get_app_fn`'s run. -/
def ecsK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if tagW (r.headD 0) ≠ 3 then some (0, m)
    else if tierW (r.headD 0) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m CONST (tierW (r.headD 0)) ≤ idxW (r.headD 0) then none
    else ecsK2 p n a (callW p n "env_find"
      [tfld m CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0, vis] m)

end ecs

theorem etaCtorShape_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (vis a : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "eta_ctor_shape" [vis, a]
    ⦃fun r s' => LocEq s' s₀ ∧ ecsK1 p n vis a (callW p n "get_app_fn" [a] s₀.mem) =
      some (r.headD 0, s'.mem); ⊤⦄ := by
  sorry

/-! ### The twin's runs, by case -/

theorem etaCtorShape_run_nonconst (fe : IFEnv) (e : EIdx) (a : AState) (hh : EIdx)
    (hgaf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = false) :
    (etaCtorShape fe e).run a = .ok (false, a) := by
  simp only [etaCtorShape, StateT.run_bind, hgaf, except_ok_bind, ht, Bool.false_eq_true,
    ↓reduceIte]
  rfl

theorem etaCtorShape_run_other (fe : IFEnv) (e : EIdx) (a : AState) (hh : EIdx) (c : NIdx)
    (us : LsIdx) (hgaf : (getAppFn coreWalkFuel e).run a = .ok (hh, a))
    (ht : (hh.tag == ETag.const) = true) (hv : a.store.view hh = some (.const c us))
    (hf : ∀ cv np nf, fe.find? c ≠ some (.ctorInfo cv np nf)) :
    (etaCtorShape fe e).run a = .ok (false, a) := by
  simp only [etaCtorShape, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte,
    view_run _ _ _ hv]
  rcases hc : fe.find? c with _ | ⟨_ | _ | _ | _ | ⟨cv, np, nf⟩ | _ | _⟩ <;> try rfl
  all_goals exact absurd hc (hf cv np nf)

theorem etaCtorShape_run_ctor (fe : IFEnv) (e : EIdx) (a : AState) (hh : EIdx) (c : NIdx)
    (us : LsIdx) (hgaf : (getAppFn coreWalkFuel e).run a = .ok (hh, a))
    (ht : (hh.tag == ETag.const) = true) (hv : a.store.view hh = some (.const c us))
    (cv : IConstantVal) (np nf : Nat) (hf : fe.find? c = some (.ctorInfo cv np nf))
    (xs : List EIdx) (hargs : (getAppArgs coreWalkFuel e).run a = .ok (xs, a)) :
    (etaCtorShape fe e).run a = .ok (xs.length == np + nf, a) := by
  simp only [etaCtorShape, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte,
    view_run _ _ _ hv, hf, hargs]
  rfl

/-- The L count test is the twin's: `an - nf = np` on words, past `an < nf`. -/
theorem count_test (an npw nfw : Word) (k : Nat) (hk : k = an.toNat) :
    (if an < nfw then (0 : Word) else if an - nfw = npw then 1 else 0) =
      (if (k == npw.toNat + nfw.toNat) = true then 1 else 0) := by
  subst hk
  by_cases h1 : an < nfw
  · have h1' : an.toNat < nfw.toNat := UInt64.lt_iff_toNat_lt.mp h1
    have : (an.toNat == npw.toNat + nfw.toNat) = false := by simp; omega
    simp only [h1, ↓reduceIte, this]; rfl
  · have h1' : nfw.toNat ≤ an.toNat :=
      Nat.not_lt.mp (fun h => h1 (UInt64.lt_iff_toNat_lt.mpr h))
    have hs : (an - nfw).toNat = an.toNat - nfw.toNat := UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr h1')
    simp only [h1, ↓reduceIte]
    by_cases h2 : an - nfw = npw
    · have : (an.toNat == npw.toNat + nfw.toNat) = true := by
        simp; rw [← h2, hs]; omega
      simp only [h2, ↓reduceIte, this]
    · have : (an.toNat == npw.toNat + nfw.toNat) = false := by
        simp; intro e; apply h2; apply UInt64.toNat_inj.mp; rw [hs]; omega
      simp only [h2, ↓reduceIte, this]; rfl

/-- **`eta_ctor_shape` refines `etaCtorShape`.** -/
@[refines ConRon.Arena.etaCtorShape]
theorem etaCtorShape_refines (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb e : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) :
    CoreSpec p (n + 1) "eta_ctor_shape" [vis, e] (etaCtorShape fe (decE e)) decBool s₀ a₀ dn vis
      fe MM eb := by
  sorry

end L.Arena
