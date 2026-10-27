import ConAgua.Arena.WhnfBase
import ConAgua.Front.Preserve
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# `WhnfSpine`'s L code and the proofs behind its refinements

The L code for the eight spine functions (`WhnfSpine.lean`'s docstring has the table), each
loop's own `lblk`, a word-level model per loop, and the lemmas that connect the model to the
twin (`ConRon.Arena.getAppFn`, …) under `ArenaR`/`ArenaD`. `WhnfSpine.lean` states the eight
`@[refines]` theorems against these.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `get_app_fn(e)`: chase `.app` nodes' `f` child, counting down a 64-bit fuel word -/

def getAppFnLoop : Stmt := lblk (e, f, t, x) {
  while e >> 28 == 4 {
    if f == 0 { abort };
    f -= 1;
    t := ⟦e⟧.tier;
    x := ⟦e⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if APP⟨t⟩.count <= x { abort };
    e := APP⟨t, x⟩.f
  }
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1281-1290 ConRon.Arena.getAppFn -/
@[l_impl ConRon.Arena.getAppFn]
def getAppFnL : FunDecl := lfn (e) locals (f, t, x) {
  f := 4000000000;
  ⟪getAppFnLoop⟫;
  if f == 0 { abort };
  return e
}

/-- **The model of the `get_app_fn` loop**: from `(e, f)`, the final `(e, f)` or `none` where the
L code aborts. Terminates because `f` strictly decreases (checked `≠ 0` before each decrement). -/
def gafLoopW (m : Mem) (e f : Word) : Option (Word × Word) :=
  if e >>> 28 = 4 then
    if f = 0 then none
    else if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m APP (tierW e) ≤ idxW e then none
    else gafLoopW m (tfld m APP (tierW e) (idxW e) 0) (f - 1)
  else some (e, f)
termination_by f.toNat
decreasing_by
  have hf0 : f ≠ 0 := by assumption
  have hlt : (f - 1).toNat < f.toNat := by
    have hp : 0 < f.toNat := by
      have : f.toNat ≠ 0 := fun h => hf0 (UInt64.toNat_inj.mp (by simpa using h))
      omega
    rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
    simp; omega
  exact hlt

theorem gafLoopW_done (m : Mem) (e f : Word) (h : e >>> 28 ≠ 4) : gafLoopW m e f = some (e, f) := by
  rw [gafLoopW]; simp [h]

theorem gafLoopW_step (m : Mem) (e f e' : Word) (h : e >>> 28 = 4) (hf : f ≠ 0)
    (hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hv2 : ¬ tcnt m APP (tierW e) ≤ idxW e)
    (he' : e' = tfld m APP (tierW e) (idxW e) 0) :
    gafLoopW m e f = gafLoopW m e' (f - 1) := by
  subst he'; rw [gafLoopW]
  simp only [h, ↓reduceIte, hf, hv2, hv1]

grind_pattern [arena_grind] gafLoopW_done => gafLoopW m e f
grind_pattern [arena_grind] gafLoopW_step => gafLoopW m e f, gafLoopW m e' (f - 1)

section gafLoop
variable (p : Prog)

theorem getAppFnLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n getAppFnLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      gafLoopW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (s'.loc 0, s'.loc 1); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := getAppFnLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih, evalE_tld, tld, evalE_cnt,
        tcntM, evalE_tierE, evalE_idxE] <;> finish [tierW, idxW]

theorem getAppFnLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) getAppFnLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      gafLoopW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (s'.loc 0, s'.loc 1); ⊤⦄ :=
  Triple.step_exec (getAppFnLoop_spec p (n + 1) s₀)

end gafLoop

/-- **The model of `get_app_fn`.** -/
def gafW (m : Mem) (e : Word) : Option Word :=
  match gafLoopW m e 4000000000 with
  | none => none
  | some (e', f') => if f' = 0 then none else some e'

theorem getAppFnL_spec (p : Prog) (hp : p.lookup "get_app_fn" = some getAppFnL) (n : Nat)
    (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "get_app_fn" [e]
    ⦃fun r s' => s' = s₀ ∧ gafW s₀.mem e = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, getAppFnL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, getAppFnLoop_step_spec p n] <;>
      finish [gafW]

/-! ## `get_app_fn` refines `getAppFn` -/

/-- A handle word's tag, compared with a small numeral: `decE_tag` plus the numeral's own bound. -/
theorem decE_tag_eq (e : Word) (hh : e.toNat < 2 ^ 32) (k : Nat) (hk : k < 16) :
    ((decE e).tag = UInt32.ofNat k) ↔ e >>> 28 = UInt64.ofNat k := by
  rw [decE_tag e hh]
  have e1 : (e >>> 28).toNat < 2 ^ 32 := by
    have := e.toNat_lt
    simp [UInt64.toNat_shiftRight]
    omega
  constructor
  · intro h
    have h1 := congrArg UInt32.toNat h
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt e1,
      UInt32.toNat_ofNat_of_lt' (by omega : k < 2 ^ 32)] at h1
    apply UInt64.toNat_inj.mp
    rw [h1, UInt64.toNat_ofNat_of_lt' (by omega : k < 2 ^ 64)]
  · intro h
    rw [h]
    apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, UInt64.toNat_ofNat_of_lt' (by omega : k < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : k < 2 ^ 32), UInt32.toNat_ofNat_of_lt' (by omega : k < 2 ^ 32)]

theorem viewApp_run' (h : EIdx) (a : AState) :
    (viewApp h).run a = .ok (a.store.viewApp h, a) := rfl

theorem decE_tag_app (e : Word) (hh : e.toNat < 2 ^ 32) : ((decE e).tag = ETag.app) ↔ e >>> 28 = 4 :=
  decE_tag_eq e hh 4 (by decide)

theorem decE_tag_forall (e : Word) (hh : e.toNat < 2 ^ 32) :
    ((decE e).tag = ETag.forallE) ↔ e >>> 28 = 6 := decE_tag_eq e hh 6 (by decide)

/-- **The loop's model refines `getAppFn`**: whenever `gafLoopW` from `(e, f)` succeeds with
`(e', f')` and `f'` is nonzero (the surrounding function's own post-loop check), the twin's
walk at fuel `f.toNat` from `e` succeeds and lands on `e'`, in the SAME arena state (the walk
reads only). -/
theorem gafLoopW_ok (m : Mem) (a : AState) (hR : ArenaR m a) :
    ∀ (N : Nat) (e f e' f' : Word), f.toNat ≤ N → e.toNat < 2 ^ 32 → gafLoopW m e f = some (e', f') →
      f' ≠ 0 → (getAppFn f.toNat (decE e)).run a = .ok (decE e', a) ∧ e'.toNat < 2 ^ 32 := by
  intro N
  induction N with
  | zero =>
    intro e f e' f' hfN he hL hf'
    have hf0 : f = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst hf0
    have hc : ¬ e >>> 28 = 4 := fun hc => by rw [gafLoopW] at hL; simp [hc] at hL
    · rw [gafLoopW_done m e 0 hc] at hL
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      exact absurd rfl hf'
  | succ N ih =>
    intro e f e' f' hfN he hL hf'
    by_cases hc : e >>> 28 = 4
    · have hf0 : f ≠ 0 := by
        intro hf0; rw [hf0, gafLoopW] at hL; simp [hc] at hL
      have hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
        rw [gafLoopW] at hL
        simp only [hc, ↓reduceIte, hf0] at hL
        have hv : ¬ ((tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) := fun hv => by simp [hv] at hL
        · exact hv
      have hv2 : ¬ tcnt m APP (tierW e) ≤ idxW e := by
        rw [gafLoopW] at hL
        simp only [hc, ↓reduceIte, hf0, hv1] at hL
        have hv : ¬ tcnt m APP (tierW e) ≤ idxW e := fun hv => by simp [hv] at hL
        · exact hv
      have hL' : gafLoopW m (tfld m APP (tierW e) (idxW e) 0) (f - 1) = some (e', f') := by
        rw [← gafLoopW_step m e f _ hc hf0 hv1 hv2 rfl]; exact hL
      have hf0' : f.toNat ≠ 0 := fun h => hf0 (UInt64.toNat_inj.mp (by simpa using h))
      have hfm1 : (f - 1).toNat = f.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp
      have hfm1N : (f - 1).toNat ≤ N := by rw [hfm1]; omega
      have hcnt : idxW e < tcnt m APP (tierW e) := UInt64.not_le.mp hv2
      have hva := viewApp_ok m a hR e he ⟨hv1, hcnt⟩
      have h1 : (tfld m APP (tierW e) (idxW e) 0).toNat < 2 ^ 32 :=
        (view_app m a hR e he ⟨hv1, hcnt⟩ hc).2.1
      obtain ⟨ihr, ihb⟩ := ih _ (f - 1) e' f' hfm1N h1 hL' hf'
      have heq : getAppFn f.toNat (decE e) = getAppFn ((f.toNat - 1) + 1) (decE e) := by
        congr 1; omega
      refine ⟨?_, ihb⟩
      rw [heq, getAppFn, (decE_tag_app e he).mpr hc]
      rw [show (f.toNat - 1) = (f - 1).toNat from hfm1.symm]
      simp [viewApp_run' _ a, hva, except_ok_bind]
      rw [ihr]
    · rw [gafLoopW_done m e f hc] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (fun h => hf' (UInt64.toNat_inj.mp (by simpa using h)))
      refine ⟨?_, he⟩
      rw [hk, getAppFn]
      have htag : (decE e).tag ≠ ETag.app := fun h => hc ((decE_tag_app e he).mp h)
      simp [htag]
      rfl

/-- **`get_app_fn` refines `getAppFn coreWalkFuel`.** The helper behind
`WhnfSpine.lean`'s `getAppFn_refines`. -/
theorem getAppFn_refines' (p : Prog) (hp : p.lookup "get_app_fn" = some getAppFnL) (n : Nat)
    (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (e : Word) (he : HW e) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "get_app_fn" [e]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ HW (r.headD 0) ∧
      (getAppFn coreWalkFuel (decE e)).run a₀ = .ok (decE (r.headD 0), a₀); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hs', hgaf⟩ := M.of_run (P := fun s => s = s₀) hs hrun (getAppFnL_spec p hp n s₀ e)
  unfold gafW at hgaf
  rcases hL : gafLoopW s₀.mem e 4000000000 with _ | ⟨e', f'⟩
  · rw [hL] at hgaf; simp at hgaf
  · rw [hL] at hgaf
    have hf0 : ¬ f' = 0 := fun hf0 => by simp [hf0] at hgaf
    · simp only [hf0, ↓reduceIte] at hgaf
      have he' : e' = r.headD 0 := Option.some.inj hgaf
      have hN : (4000000000 : Word).toNat ≤ (4000000000 : Word).toNat := Nat.le_refl _
      obtain ⟨hrun', hbd⟩ := gafLoopW_ok s₀.mem a₀ hR _ e 4000000000 e' f' hN he hL hf0
      have hfuel : (4000000000 : Word).toNat = coreWalkFuel := by
        simp [UInt64.toNat_ofNat, coreWalkFuel]
      rw [hfuel] at hrun'
      refine ⟨by rw [hs'], by rw [LocEq, hs'], ?_, ?_⟩
      · rw [← he']; exact hbd
      · rw [← he']; exact hrun'

/-! ## `pi_result(e)`: chase `∀`-telescope bodies, counting down a 64-bit fuel word

Same shape as `get_app_fn`, chasing tag `6` (`forallE`) off `FAREC`'s second word instead of
tag `4` off `AREC`'s first. -/

def piResultLoop : Stmt := lblk (e, f, t, x) {
  while e >> 28 == 6 {
    if f == 0 { abort };
    f -= 1;
    t := ⟦e⟧.tier;
    x := ⟦e⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if FORALL⟨t⟩.count <= x { abort };
    e := FORALL⟨t, x⟩.b
  }
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1357-1367 ConRon.Arena.piResult -/
@[l_impl ConRon.Arena.piResult]
def piResultL : FunDecl := lfn (e) locals (f, t, x) {
  f := 4000000000;
  ⟪piResultLoop⟫;
  if f == 0 { abort };
  return e
}

/-- **The model of the `pi_result` loop.** -/
def priLoopW (m : Mem) (e f : Word) : Option (Word × Word) :=
  if e >>> 28 = 6 then
    if f = 0 then none
    else if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m FORALL (tierW e) ≤ idxW e then none
    else priLoopW m (tfld m FORALL (tierW e) (idxW e) 1) (f - 1)
  else some (e, f)
termination_by f.toNat
decreasing_by
  have hf0 : f ≠ 0 := by assumption
  have hlt : (f - 1).toNat < f.toNat := by
    have hp : 0 < f.toNat := by
      have : f.toNat ≠ 0 := fun h => hf0 (UInt64.toNat_inj.mp (by simpa using h))
      omega
    rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
    simp; omega
  exact hlt

theorem priLoopW_done (m : Mem) (e f : Word) (h : e >>> 28 ≠ 6) : priLoopW m e f = some (e, f) := by
  rw [priLoopW]; simp [h]

theorem priLoopW_step (m : Mem) (e f e' : Word) (h : e >>> 28 = 6) (hf : f ≠ 0)
    (hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hv2 : ¬ tcnt m FORALL (tierW e) ≤ idxW e)
    (he' : e' = tfld m FORALL (tierW e) (idxW e) 1) :
    priLoopW m e f = priLoopW m e' (f - 1) := by
  subst he'; rw [priLoopW]
  simp only [h, ↓reduceIte, hf, hv2, hv1]

grind_pattern [arena_grind] priLoopW_done => priLoopW m e f
grind_pattern [arena_grind] priLoopW_step => priLoopW m e f, priLoopW m e' (f - 1)

section priLoop
variable (p : Prog)

theorem piResultLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n piResultLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      priLoopW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (s'.loc 0, s'.loc 1); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := piResultLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih, evalE_tld, tld, evalE_cnt,
        tcntM, evalE_tierE, evalE_idxE] <;> finish [tierW, idxW]

theorem piResultLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) piResultLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      priLoopW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (s'.loc 0, s'.loc 1); ⊤⦄ :=
  Triple.step_exec (piResultLoop_spec p (n + 1) s₀)

end priLoop

/-- **The model of `pi_result`.** -/
def priW (m : Mem) (e : Word) : Option Word :=
  match priLoopW m e 4000000000 with
  | none => none
  | some (e', f') => if f' = 0 then none else some e'

theorem piResultL_spec (p : Prog) (hp : p.lookup "pi_result" = some piResultL) (n : Nat)
    (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "pi_result" [e]
    ⦃fun r s' => s' = s₀ ∧ priW s₀.mem e = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, piResultL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, piResultLoop_step_spec p n] <;>
      finish [priW]

theorem viewBind_run' (h : EIdx) (a : AState) :
    (viewBind h).run a = .ok (a.store.viewBind h, a) := rfl

/-- **The loop's model refines `piResult`** (the twin-fuel correspondence, as `gafLoopW_ok`). -/
theorem priLoopW_ok (m : Mem) (a : AState) (hR : ArenaR m a) :
    ∀ (N : Nat) (e f e' f' : Word), f.toNat ≤ N → e.toNat < 2 ^ 32 → priLoopW m e f = some (e', f') →
      f' ≠ 0 → (piResult f.toNat (decE e)).run a = .ok (decE e', a) ∧ e'.toNat < 2 ^ 32 := by
  intro N
  induction N with
  | zero =>
    intro e f e' f' hfN he hL hf'
    have hf0 : f = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst hf0
    have hc : ¬ e >>> 28 = 6 := fun hc => by rw [priLoopW] at hL; simp [hc] at hL
    · rw [priLoopW_done m e 0 hc] at hL
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      exact absurd rfl hf'
  | succ N ih =>
    intro e f e' f' hfN he hL hf'
    by_cases hc : e >>> 28 = 6
    · have hf0 : f ≠ 0 := by
        intro hf0; rw [hf0, priLoopW] at hL; simp [hc] at hL
      have hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
        rw [priLoopW] at hL
        simp only [hc, ↓reduceIte, hf0] at hL
        have hv : ¬ ((tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) := fun hv => by simp [hv] at hL
        · exact hv
      have hv2 : ¬ tcnt m FORALL (tierW e) ≤ idxW e := by
        rw [priLoopW] at hL
        simp only [hc, ↓reduceIte, hf0, hv1] at hL
        have hv : ¬ tcnt m FORALL (tierW e) ≤ idxW e := fun hv => by simp [hv] at hL
        · exact hv
      have hL' : priLoopW m (tfld m FORALL (tierW e) (idxW e) 1) (f - 1) =
          some (e', f') := by
        rw [← priLoopW_step m e f _ hc hf0 hv1 hv2 rfl]; exact hL
      have hf0' : f.toNat ≠ 0 := fun h => hf0 (UInt64.toNat_inj.mp (by simpa using h))
      have hfm1 : (f - 1).toNat = f.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp
      have hfm1N : (f - 1).toNat ≤ N := by rw [hfm1]; omega
      have hcnt : idxW e < tcnt m FORALL (tierW e) := UInt64.not_le.mp hv2
      have hvb := viewBind_forall m a hR e he ⟨hv1, hcnt⟩ hc
      have h1 : (tfld m FORALL (tierW e) (idxW e) 1).toNat < 2 ^ 32 :=
        (view_forall m a hR e he ⟨hv1, hcnt⟩ hc).2.2
      obtain ⟨ihr, ihb⟩ := ih _ (f - 1) e' f' hfm1N h1 hL' hf'
      have heq : piResult f.toNat (decE e) = piResult ((f.toNat - 1) + 1) (decE e) := by
        congr 1; omega
      refine ⟨?_, ihb⟩
      rw [heq, piResult, (decE_tag_forall e he).mpr hc]
      rw [show (f.toNat - 1) = (f - 1).toNat from hfm1.symm]
      simp [viewBind_run' _ a, hvb, except_ok_bind]
      exact ihr
    · rw [priLoopW_done m e f hc] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (fun h => hf' (UInt64.toNat_inj.mp (by simpa using h)))
      refine ⟨?_, he⟩
      rw [hk, piResult]
      have htag : (decE e).tag ≠ ETag.forallE := fun h => hc ((decE_tag_forall e he).mp h)
      simp [htag]
      rfl

/-- **`pi_result` refines `piResult coreWalkFuel`.** The helper behind `WhnfSpine.lean`'s
`piResult_refines`. -/
theorem piResult_refines' (p : Prog) (hp : p.lookup "pi_result" = some piResultL) (n : Nat)
    (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (e : Word) (he : HW e) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "pi_result" [e]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ HW (r.headD 0) ∧
      (piResult coreWalkFuel (decE e)).run a₀ = .ok (decE (r.headD 0), a₀); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hs', hpi⟩ := M.of_run (P := fun s => s = s₀) hs hrun (piResultL_spec p hp n s₀ e)
  unfold priW at hpi
  rcases hL : priLoopW s₀.mem e 4000000000 with _ | ⟨e', f'⟩
  · rw [hL] at hpi; simp at hpi
  · rw [hL] at hpi
    have hf0 : ¬ f' = 0 := fun hf0 => by simp [hf0] at hpi
    · simp only [hf0, ↓reduceIte] at hpi
      have he' : e' = r.headD 0 := Option.some.inj hpi
      have hN : (4000000000 : Word).toNat ≤ (4000000000 : Word).toNat := Nat.le_refl _
      obtain ⟨hrun', hbd⟩ := priLoopW_ok s₀.mem a₀ hR _ e 4000000000 e' f' hN he hL hf0
      have hfuel : (4000000000 : Word).toNat = coreWalkFuel := by
        simp [UInt64.toNat_ofNat, coreWalkFuel]
      rw [hfuel] at hrun'
      refine ⟨by rw [hs'], by rw [LocEq, hs'], ?_, ?_⟩
      · rw [← he']; exact hbd
      · rw [← he']; exact hrun'

/-! ## `peel_pis(k, e)`: peel `k` syntactic `∀` binders, or fail (`(0, 0)`) at the first non-`∀`

Structural on `k`: no twin fuel, an explicit `return (0, 0)` inside the loop at the first
non-`∀`, the trailing `return (1, e)` at `k = 0`. -/

def peelPisLoop : Stmt := lblk (k, e, t, x) {
  while k != 0 {
    if e >> 28 != 6 { return (0, 0) };
    t := ⟦e⟧.tier;
    x := ⟦e⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if FORALL⟨t⟩.count <= x { abort };
    e := FORALL⟨t, x⟩.b;
    k -= 1
  }
}

/-- con-ron: ConRon/Arena/PropRead.lean:45-57 ConRon.Arena.peelPis -/
@[l_impl ConRon.Arena.peelPis]
def peelPisL : FunDecl := lfn (k, e) locals (t, x) {
  ⟪peelPisLoop⟫;
  return (1, e)
}

/-- **The model of `peel_pis`** (the whole function, the trailing `return (1, e)` baked into the
`k = 0` base case): `(flag, value)`, `none` where the L code aborts. -/
def peelPisW (m : Mem) (k e : Word) : Option (Word × Word) :=
  if k = 0 then some (1, e)
  else if e >>> 28 ≠ 6 then some (0, 0)
  else if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m FORALL (tierW e) ≤ idxW e then none
  else peelPisW m (k - 1) (tfld m FORALL (tierW e) (idxW e) 1)
termination_by k.toNat
decreasing_by
  have hk0 : k ≠ 0 := by assumption
  have hlt : (k - 1).toNat < k.toNat := by
    have hp : 0 < k.toNat := by
      have : k.toNat ≠ 0 := fun h => hk0 (UInt64.toNat_inj.mp (by simpa using h))
      omega
    rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
    simp; omega
  exact hlt

theorem peelPisW_zero (m : Mem) (e : Word) : peelPisW m 0 e = some (1, e) := by
  rw [peelPisW]; simp

theorem peelPisW_miss (m : Mem) (k e : Word) (hk : k ≠ 0) (h : e >>> 28 ≠ 6) :
    peelPisW m k e = some (0, 0) := by
  rw [peelPisW]; simp [hk, h]

theorem peelPisW_step (m : Mem) (k e e' : Word) (hk : k ≠ 0) (h : e >>> 28 = 6)
    (hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hv2 : ¬ tcnt m FORALL (tierW e) ≤ idxW e)
    (he' : e' = tfld m FORALL (tierW e) (idxW e) 1) :
    peelPisW m k e = peelPisW m (k - 1) e' := by
  subst he'; rw [peelPisW]
  simp [hk, ↓reduceIte, h, hv2, hv1]

grind_pattern [arena_grind] peelPisW_zero => peelPisW m 0 e
grind_pattern [arena_grind] peelPisW_miss => peelPisW m k e
grind_pattern [arena_grind] peelPisW_step => peelPisW m k e, peelPisW m (k - 1) e'

section peelLoop
variable (p : Prog)

theorem peelPisLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n peelPisLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      (r = .normal → peelPisW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (1, s'.loc 1)) ∧
      (r = .ret [0, 0] → peelPisW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (0, 0)) ∧
      (∀ v, r = .ret v → v = [0, 0]); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := peelPisLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih, evalE_tld, tld, evalE_cnt,
        tcntM, evalE_tierE, evalE_idxE] <;> finish [tierW, idxW]

theorem peelPisLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) peelPisLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      (r = .normal → peelPisW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (1, s'.loc 1)) ∧
      (r = .ret [0, 0] → peelPisW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (0, 0)) ∧
      (∀ v, r = .ret v → v = [0, 0]); ⊤⦄ :=
  Triple.step_exec (peelPisLoop_spec p (n + 1) s₀)

end peelLoop

theorem peelPisL_spec (p : Prog) (hp : p.lookup "peel_pis" = some peelPisL) (n : Nat) (s₀ : St)
    (k e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "peel_pis" [k, e]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ peelPisW s₀.mem k e = some (r.headD 0, r.tail.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, peelPisL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLocs, peelPisLoop_step_spec p n] <;> finish [peelPisW]

/-- **The model of `peel_pis` refines `peelPis`**: by induction on (a bound on) `k.toNat`, as
`gafLoopW_ok`. -/
theorem peelPisW_ok (m : Mem) (a : AState) (hR : ArenaR m a) :
    ∀ (N : Nat) (k e flag val : Word), k.toNat ≤ N → e.toNat < 2 ^ 32 →
      peelPisW m k e = some (flag, val) →
      (peelPis k.toNat (decE e)).run a = .ok (decOpt flag val, a) ∧
        (flag ≠ 0 → val.toNat < 2 ^ 32) ∧ (flag = 0 → val = 0) := by
  intro N
  induction N with
  | zero =>
    intro k e flag val hkN he hL
    have hk0 : k = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst hk0
    rw [peelPisW_zero] at hL
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    refine ⟨?_, fun _ => he, fun h => absurd h (by decide)⟩
    simp [peelPis, decOpt]
    rfl
  | succ N ih =>
    intro k e flag val hkN he hL
    by_cases hk0 : k = 0
    · subst hk0
      rw [peelPisW_zero] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      refine ⟨?_, fun _ => he, fun h => absurd h (by decide)⟩
      simp [peelPis, decOpt]
      rfl
    · have hk0' : k.toNat ≠ 0 := fun h => hk0 (UInt64.toNat_inj.mp (by simpa using h))
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0'
      by_cases hc : e >>> 28 = 6
      · have hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
          rw [peelPisW] at hL
          simp only [hk0, ↓reduceIte, hc] at hL
          have hv : ¬ ((tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) := fun hv => by simp [hv] at hL
          · exact hv
        have hv2 : ¬ tcnt m FORALL (tierW e) ≤ idxW e := by
          rw [peelPisW] at hL
          simp only [hk0, ↓reduceIte, hc, hv1] at hL
          have hv : ¬ tcnt m FORALL (tierW e) ≤ idxW e := fun hv => by simp [hv] at hL
          · exact hv
        have hL' : peelPisW m (k - 1) (tfld m FORALL (tierW e) (idxW e) 1) =
            some (flag, val) := by
          rw [← peelPisW_step m k e _ hk0 hc hv1 hv2 rfl]; exact hL
        have hkm1 : (k - 1).toNat = k.toNat - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp
        have hkm1N : (k - 1).toNat ≤ N := by rw [hkm1]; omega
        have hcnt : idxW e < tcnt m FORALL (tierW e) := UInt64.not_le.mp hv2
        have hvb := viewBind_forall m a hR e he ⟨hv1, hcnt⟩ hc
        have h1 : (tfld m FORALL (tierW e) (idxW e) 1).toNat < 2 ^ 32 :=
          (view_forall m a hR e he ⟨hv1, hcnt⟩ hc).2.2
        obtain ⟨ihr, ihb, ih0⟩ := ih _ _ flag val hkm1N h1 hL'
        refine ⟨?_, ihb, ih0⟩
        rw [hj, peelPis, (decE_tag_forall e he).mpr hc]
        rw [show j = (k - 1).toNat from by rw [hkm1]; omega]
        simp [viewBind_run' _ a, hvb, except_ok_bind]
        exact ihr
      · rw [peelPisW_miss m k e hk0 hc] at hL
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
        refine ⟨?_, fun h => absurd rfl h, fun _ => rfl⟩
        rw [hj, peelPis]
        have htag : (decE e).tag ≠ ETag.forallE := fun h => hc ((decE_tag_forall e he).mp h)
        simp [htag, decOpt]
        rfl

/-- **`peel_pis` refines `peelPis`.** The helper behind `WhnfSpine.lean`'s `peelPis_refines`. -/
theorem peelPis_refines' (p : Prog) (hp : p.lookup "peel_pis" = some peelPisL) (n : Nat)
    (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (k e : Word) (he : HW e) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "peel_pis" [k, e]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ HW (r.tail.headD 0) ∧
      (peelPis k.toNat (decE e)).run a₀ = .ok (decOpt (r.headD 0) (r.tail.headD 0), a₀); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hs', -, hL⟩ := M.of_run (P := fun s => s = s₀) hs hrun (peelPisL_spec p hp n s₀ k e)
  have hN : k.toNat ≤ k.toNat := Nat.le_refl _
  obtain ⟨hrun', hbd, hz⟩ := peelPisW_ok s₀.mem a₀ hR _ k e _ _ hN he hL
  by_cases hflag : r.headD 0 = 0
  · refine ⟨by rw [hs'], by rw [LocEq, hs'], ?_, hrun'⟩
    rw [hz hflag]; simp [HW]
  · exact ⟨by rw [hs'], by rw [LocEq, hs'], hbd hflag, hrun'⟩

/-! ## `mk_app_n(f, o, n)` / `mk_app_n_from(f, o, n, i)`: fold `mk_app` over a stack slice

Both are the same loop (`mk_app_n` just starts it at `i = 0`); `mkAppNFromW` is the Mem-level
fold (a callee, `mk_app`, chained through the slice `SPN[o .. o + n)`), and `mkAppNFromW_ok`
connects it to the twin's `mkAppNFrom` under `ArenaD`, by induction on (a bound on) `n - i`. No
twin fuel: `mkAppW`'s own success already gives the handle bounds `mk_app_ok` needs
(`or_shr32`), so the induction carries no separate `HW` bookkeeping. -/

def mkAppNFromLoop : Stmt := lblk (f, o, n, i) {
  while i < n {
    f := call mk_app(f, SPN.u64[o + i]);
    i += 1
  }
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1305-1311 ConRon.Arena.mkAppN -/
@[l_impl ConRon.Arena.mkAppN]
def mkAppNL : FunDecl := lfn (f, o, n) locals (i) {
  i := 0;
  ⟪mkAppNFromLoop⟫;
  return f
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1313-1323 ConRon.Arena.mkAppNFrom -/
@[l_impl ConRon.Arena.mkAppNFrom]
def mkAppNFromL : FunDecl := lfn (f, o, n, i) locals () {
  ⟪mkAppNFromLoop⟫;
  return f
}

/-- **The model of the `mk_app_n_from` loop**, structural on a step bound (the caller always
supplies `n.toNat - i.toNat`, enough): the final accumulator and memory, `none` where the L
code aborts (`mk_app` fails). -/
def mkAppNFromW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, m, f, _, _, _ => some (f, m)
  | K + 1, m, f, o, n, i =>
    if i < n then
      match mkAppW m f (spW m (o + i)) with
      | none => none
      | some (f', m') => mkAppNFromW K m' f' o n (i + 1)
    else some (f, m)

theorem mkAppNFromW_done (m : Mem) (f o n i : Word) (h : ¬ i < n) :
    mkAppNFromW (n.toNat - i.toNat) m f o n i = some (f, m) := by
  cases hK : n.toNat - i.toNat with
  | zero => rw [mkAppNFromW]
  | succ k => rw [mkAppNFromW]; simp [h]

theorem mkAppNFromW_step (m m' : Mem) (f o n i f' : Word) (h : i < n)
    (hmk : mkAppW m f (spW m (o + i)) = some (f', m')) :
    mkAppNFromW (n.toNat - i.toNat) m f o n i =
      mkAppNFromW (n.toNat - (i + 1).toNat) m' f' o n (i + 1) := by
  have h1 : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add]; simp
    have := n.toNat_lt
    have : i.toNat < n.toNat := h
    omega
  have hK : n.toNat - i.toNat = (n.toNat - (i + 1).toNat) + 1 := by
    have : i.toNat < n.toNat := h
    omega
  rw [hK, mkAppNFromW]
  simp [h, hmk]

grind_pattern [arena_grind] mkAppNFromW_done => mkAppNFromW (n.toNat - i.toNat) m f o n i
grind_pattern [arena_grind] mkAppNFromW_step =>
  mkAppNFromW (n.toNat - i.toNat) m f o n i, mkAppNFromW (n.toNat - (i + 1).toNat) m' f' o n (i + 1)

section mkAppLoop
variable (p : Prog) (hpd : p.lookup "der_b" = some derB) (hpf : p.lookup "app_find" = some appFind)
  (hpp : p.lookup "app_push" = some appPush) (hpi : p.lookup "intern_app" = some internApp)
  (hp : p.lookup "mk_app" = some mkApp)
include hpd hpf hpp hpi hp

theorem mkAppNFromLoop_spec (n' : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n' mkAppNFromLoop
    ⦃fun r s' => r = .normal ∧
      mkAppNFromW ((s₀.loc 2).toNat - (s₀.loc 3).toNat) s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)
        (s₀.loc 3) = some (s'.loc 0, s'.mem); ⊤⦄ := by
  induction n' generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n' ih =>
    rw [exec, step_while (w := mkAppNFromLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        mkApp_spec p hpd hpf hpp hpi hp n', ih] <;> finish [mkAppNFromW, spW]

theorem mkAppNFromLoop_step_spec (n' : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n') mkAppNFromLoop
    ⦃fun r s' => r = .normal ∧
      mkAppNFromW ((s₀.loc 2).toNat - (s₀.loc 3).toNat) s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)
        (s₀.loc 3) = some (s'.loc 0, s'.mem); ⊤⦄ :=
  Triple.step_exec (mkAppNFromLoop_spec p hpd hpf hpp hpi hp (n' + 1) s₀)

end mkAppLoop

theorem mkAppNFromL_spec (p : Prog) (hpd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "app_find" = some appFind) (hpp : p.lookup "app_push" = some appPush)
    (hpi : p.lookup "intern_app" = some internApp) (hp : p.lookup "mk_app" = some mkApp)
    (hpn : p.lookup "mk_app_n_from" = some mkAppNFromL) (n' : Nat) (s₀ : St) (f o n i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n') "mk_app_n_from" [f, o, n, i]
    ⦃fun r s' => LocEq s' s₀ ∧ mkAppNFromW (n.toNat - i.toNat) s₀.mem f o n i = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpn]
  simp only [callFn, mkAppNFromL]
  cases n' with
  | zero => vcgen [exec] <;> grind
  | succ n' =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs,
        mkAppNFromLoop_step_spec p hpd hpf hpp hpi hp n'] <;> finish

theorem mkAppNL_spec (p : Prog) (hpd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "app_find" = some appFind) (hpp : p.lookup "app_push" = some appPush)
    (hpi : p.lookup "intern_app" = some internApp) (hp : p.lookup "mk_app" = some mkApp)
    (hpn : p.lookup "mk_app_n" = some mkAppNL) (n' : Nat) (s₀ : St) (f o n : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n') "mk_app_n" [f, o, n]
    ⦃fun r s' => LocEq s' s₀ ∧ mkAppNFromW n.toNat s₀.mem f o n 0 = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpn]
  simp only [callFn, mkAppNL]
  cases n' with
  | zero => vcgen [exec] <;> grind
  | succ n' =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc,
        mkAppNFromLoop_step_spec p hpd hpf hpp hpi hp n'] <;> finish

/-- **What `mk_app` changes** (the app tables and their derived-range cache): the `Grows`
conjunct a `mk_*` constructor usually posts is the Nat-limb pool's (`Pool.lean`), which `mk_app`
never touches; this is what is available instead (`mkAppN_refines`/`mkAppNFrom_refines` post it
in `Grows`'s place). -/
theorem mkAppW_frame (m m' : Mem) (f a r : Word) (hI : mkAppW m f a = some (r, m')) :
    MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] m m' := by
  unfold mkAppW at hI; split at hI
  · cases hI
  exact (mkK_frame appCS_wf (by decide) hI).mono
    (by simp [ConsSch.wset, appCS, AREC, ASLOT, ADER]) (by simp [appCS])

/-- A slice of the stack survives a writer that leaves `SPN` alone. -/
theorem SpineR.frame {m m' : Mem} {o n : Word} {xs : Array EIdx} (hx : SpineR m o n xs)
    {A : List ArrId} {C : List Word} (hf : MemFrame A C m m') (hA : SPN ∉ A) : SpineR m' o n xs where
  size := hx.size
  bound := by rw [hf.2.2.1 SPN]; exact hx.bound
  lt := fun i hi => by rw [spW, hf.1 SPN hA (by decide)]; exact hx.lt i hi
  get := fun i hi => by rw [hx.get i hi, spW, spW, hf.1 SPN hA (by decide)]

/-- **`mkAppNFrom` from `0` is `mkAppN`** over the whole array (con-leche's standing
`List`-as-cursor deviation, §3.4): by induction on a bound on `xs.size - i`. -/
theorem mkAppNFrom_eq_mkAppN' : ∀ (N : Nat) (f : EIdx) (xs : Array EIdx) (i : Nat),
    xs.size - i ≤ N → i ≤ xs.size → mkAppNFrom f xs i = mkAppN f (xs.toList.drop i) := by
  intro N
  induction N with
  | zero =>
    intro f xs i hN hi
    have hi' : i = xs.size := by omega
    subst hi'
    rw [mkAppNFrom.eq_def]
    simp only [Nat.lt_irrefl, dite_false]
    rw [show List.drop xs.size xs.toList = [] from
      by rw [← Array.length_toList]; exact List.drop_length]; rfl
  | succ N ih =>
    intro f xs i hN hi
    by_cases hc : i < xs.size
    · rw [mkAppNFrom.eq_def]
      simp only [hc, dite_true]
      have hget : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hc)]
        simp
      rw [hget, mkAppN]
      congr 1
      funext g
      exact ih g xs (i + 1) (by omega) (by omega)
    · have hi' : i = xs.size := by omega
      subst hi'
      rw [mkAppNFrom.eq_def]
      simp only [Nat.lt_irrefl, dite_false]
      rw [show List.drop xs.size xs.toList = [] from
        by rw [← Array.length_toList]; exact List.drop_length]; rfl

theorem mkAppNFrom_eq_mkAppN (f : EIdx) (xs : Array EIdx) :
    mkAppNFrom f xs 0 = mkAppN f xs.toList :=
  mkAppNFrom_eq_mkAppN' xs.size f xs 0 (by omega) (by omega)

/-- **The model of the `mk_app_n_from` loop refines `mkAppNFrom`** under `ArenaD`: by induction
on the step bound `K`, `mkApp_ok` and `mkAppW_frame` at every step (no twin fuel: `mkApp_ok`'s
own success already gives the handle bounds it needs). -/
theorem mkAppNFromW_ok : ∀ (K : Nat) (m : Mem) (a : AState) (f o n i : Word) (xs : Array EIdx),
    K = n.toNat - i.toNat → i.toNat ≤ n.toNat → ArenaD m a → SpineR m o n xs →
    ∀ r m', mkAppNFromW K m f o n i = some (r, m') →
      AM.ok (mkAppNFrom (decE f) xs i.toNat) a ∧
      ArenaD m' (AM.st (mkAppNFrom (decE f) xs i.toNat) a) ∧
      AM.res (mkAppNFrom (decE f) xs i.toNat) a = decE r := by
  intro K
  induction K with
  | zero =>
    intro m a f o n i xs hK hin0 hD hx r m' hL
    have hin : i.toNat = n.toNat := by omega
    have hxs : i.toNat = xs.size := by rw [hin, ← hx.size]
    have hne : ¬ i.toNat < xs.size := by omega
    rw [mkAppNFromW] at hL
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    rw [mkAppNFrom.eq_def]
    simp [hne, AM.ok_pure, AM.st_pure, AM.res_pure]
    exact hD
  | succ K ih =>
    intro m a f o n i xs hK hin0 hD hx r m' hL
    have hin : i.toNat < n.toNat := by omega
    have hiw : i < n := hin
    rw [mkAppNFromW] at hL
    simp only [hiw, ↓reduceIte] at hL
    rcases hmk : mkAppW m f (spW m (o + i)) with _ | ⟨f₁, m₁⟩ <;> simp only [hmk, reduceCtorEq] at hL
    have hxsize : xs.size = n.toNat := hx.size
    have hilt : i.toNat < xs.size := by omega
    have hxi : xs[i.toNat] = decE (spW m (o + i)) := by
      have h := hx.get i.toNat hilt
      rwa [show (i.toNat).toUInt64 = UInt64.ofNat i.toNat from rfl, UInt64.ofNat_toNat] at h
    obtain ⟨hok, hArenaD, hres⟩ := mkApp_ok m a hD f (spW m (o + i)) f₁ m₁ hmk
    have hfr := mkAppW_frame m m₁ f (spW m (o + i)) f₁ hmk
    have hx' : SpineR m₁ o n xs := hx.frame hfr (by decide)
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add]; simp
      have := n.toNat_lt
      omega
    have hK' : K = n.toNat - (i + 1).toNat := by omega
    have hin0' : (i + 1).toNat ≤ n.toNat := by omega
    have hunfold : mkAppNFrom (decE f) xs i.toNat =
        internAppE (decE f) xs[i.toNat] >>= fun g => mkAppNFrom g xs (i.toNat + 1) := by
      rw [mkAppNFrom.eq_def]; simp [hilt]
    have hintern : internAppE (decE f) xs[i.toNat] =
        internE (.app (decE f) (decE (spW m (o + i)))) := by rw [hxi]; rfl
    rw [hunfold, hintern]
    obtain ⟨ihok, ihD, ihres⟩ :=
      ih m₁ (AM.st (internE (.app (decE f) (decE (spW m (o + i))))) a) f₁ o n (i + 1) xs hK'
        hin0' hArenaD hx' r m' hL
    rw [hi1] at ihok ihD ihres
    refine ⟨?_, ?_, ?_⟩
    · rw [AM.ok_bind, hres]; exact ⟨hok, ihok⟩
    · have hok' : AM.ok (internE (.app (decE f) (decE (spW m (o + i)))) >>=
          fun g => mkAppNFrom g xs (i.toNat + 1)) a := by
        rw [AM.ok_bind, hres]; exact ⟨hok, ihok⟩
      rw [AM.st_bind _ _ _ hok', hres]; exact ihD
    · rw [AM.res_bind _ _ _ hok, hres]; exact ihres

/-- **The `mk_app_n_from` loop only touches the `app` tables and their derived-range cache**:
by induction on `K`, chaining `mkAppW_frame` at each step. -/
theorem mkAppNFromW_frame : ∀ (K : Nat) (m m' : Mem) (f o n i r : Word),
    mkAppNFromW K m f o n i = some (r, m') → MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] m m' := by
  intro K
  induction K with
  | zero =>
    intro m m' f o n i r hL
    rw [mkAppNFromW] at hL
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    exact MemFrame.refl _ _ _
  | succ K ih =>
    intro m m' f o n i r hL
    rw [mkAppNFromW] at hL
    by_cases hc : i < n
    · simp only [hc, ↓reduceIte] at hL
      rcases hmk : mkAppW m f (spW m (o + i)) with _ | ⟨f₁, m₁⟩ <;> simp only [hmk, reduceCtorEq] at hL
      exact (mkAppW_frame m m₁ f (spW m (o + i)) f₁ hmk).trans (ih m₁ m' f₁ o n (i + 1) r hL)
    · simp only [hc, ↓reduceIte] at hL
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      exact MemFrame.refl _ _ _

/-- **`mk_app_n_from` refines `mkAppNFrom`.** The helper behind `WhnfSpine.lean`'s
`mkAppNFrom_refines` (see its docstring for the two statement changes). -/
theorem mkAppNFrom_refines' (p : Prog) (hpn : p.lookup "mk_app_n_from" = some mkAppNFromL)
    (hpd : p.lookup "der_b" = some derB) (hpf : p.lookup "app_find" = some appFind)
    (hpp : p.lookup "app_push" = some appPush) (hpi : p.lookup "intern_app" = some internApp)
    (hp : p.lookup "mk_app" = some mkApp) (n : Nat) (s₀ : St) (a₀ : AState)
    (hD : ArenaD s₀.mem a₀) (f o k i : Word) (xs : Array EIdx) (hx : SpineR s₀.mem o k xs)
    (hik : i.toNat ≤ k.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_app_n_from" [f, o, k, i]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (mkAppNFrom (decE f) xs i.toNat) a₀ ∧
      ArenaD s'.mem (AM.st (mkAppNFrom (decE f) xs i.toNat) a₀) ∧
      AM.res (mkAppNFrom (decE f) xs i.toNat) a₀ = decE (r.headD 0) ∧
      MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] s₀.mem s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hL⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (mkAppNFromL_spec p hpd hpf hpp hpi hp hpn n s₀ f o k i)
  obtain ⟨hok, hArenaD, hres⟩ := mkAppNFromW_ok (k.toNat - i.toNat) s₀.mem a₀ f o k i xs rfl hik
    hD hx (r.headD 0) s'.mem hL
  exact ⟨hloc, hok, hArenaD, hres, mkAppNFromW_frame (k.toNat - i.toNat) s₀.mem s'.mem f o k i
    (r.headD 0) hL⟩

/-- **`mk_app_n` refines `mkAppN`.** The helper behind `WhnfSpine.lean`'s `mkAppN_refines`. -/
theorem mkAppN_refines' (p : Prog) (hpn : p.lookup "mk_app_n" = some mkAppNL)
    (hpd : p.lookup "der_b" = some derB) (hpf : p.lookup "app_find" = some appFind)
    (hpp : p.lookup "app_push" = some appPush) (hpi : p.lookup "intern_app" = some internApp)
    (hp : p.lookup "mk_app" = some mkApp) (n : Nat) (s₀ : St) (a₀ : AState)
    (hD : ArenaD s₀.mem a₀) (f o k : Word) (xs : Array EIdx) (hx : SpineR s₀.mem o k xs) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_app_n" [f, o, k]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (mkAppN (decE f) xs.toList) a₀ ∧
      ArenaD s'.mem (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
      AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧
      MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] s₀.mem s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hL⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (mkAppNL_spec p hpd hpf hpp hpi hp hpn n s₀ f o k)
  have h0 : (0 : Word).toNat = 0 := rfl
  obtain ⟨hok, hArenaD, hres⟩ := mkAppNFromW_ok k.toNat s₀.mem a₀ f o k 0 xs (by rw [h0]; omega)
    (by rw [h0]; omega) hD hx (r.headD 0) s'.mem hL
  rw [h0, mkAppNFrom_eq_mkAppN] at hok hArenaD hres
  exact ⟨hloc, hok, hArenaD, hres, mkAppNFromW_frame k.toNat s₀.mem s'.mem f o k 0 (r.headD 0) hL⟩

end L.Arena
