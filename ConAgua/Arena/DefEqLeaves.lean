import ConAgua.Arena.DefEq
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.IndPartsSpec3

/-!
# Refinements of `DefEq.lean`'s small leaves

`WhnfCoreRefine.lean`'s pattern, one function at a time: a word model of the L function (its
callees through their runs, `callW`; the pin readers, which read and change nothing, as reads of
`PINS`), its spec by `vcgen` + `finish` with arm lemmas, then the refinement: the callees' specs
applied to the runs, the twin's run computed arm by arm.

* Node fields under `ArenaR`: `view_app` (`View.lean`), `view_const_f` (`IndView.lean`).
* Pins: `pin_at(i)` returns `PINS[1 + i]`, `pin_word(k)` returns `PINS[k]` (`pinAt_rd`,
  `pinWord_rd`); under `PinsFull` the twin's readers return the same words (`pinAt_run`,
  `pinEmptyLevels_run`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The program -/

/-- The `p.lookup` facts the leaves need. -/
structure DefEqLeafProg (p : Prog) : Prop where
  core : WhnfCoreProg p
  pinat : p.lookup "pin_at" = some pinAtL
  pinword : p.lookup "pin_word" = some pinWordL
  bt : p.lookup "is_bool_true" = some isBoolTrueL
  hproj : p.lookup "head_is_proj" = some headIsProjL
  ion : p.lookup "io_neutral" = some ioNeutralL
  eager : p.lookup "is_eager_reduce" = some isEagerReduceL
  natzero : p.lookup "is_nat_zero" = some isNatZeroL

/-! ## Shared lemmas -/

theorem decE_tag_beq (e : Word) (hh : e.toNat < 2 ^ 32) (k : Nat) (hk : k < 16) :
    ((decE e).tag == UInt32.ofNat k) = decide (e >>> 28 = UInt64.ofNat k) := by
  have := decE_tag_eq e hh k hk
  by_cases h : e >>> 28 = UInt64.ofNat k
  · simp [h, this.mpr h]
  · have h2 : ¬ (decE e).tag = UInt32.ofNat k := fun h' => h (this.mp h')
    simp [h, h2]

/-- `pin_at(i)` reads `PINS[1 + i]` and changes nothing. -/
theorem pinAt_rd (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_at" [i]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ i < 51 ∧
      r.headD 0 = rdW (s₀.mem.arr64 PINS) (1 + i); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pinAtL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [rdW]

/-- `pin_word(k)` reads `PINS[k]` and changes nothing. -/
theorem pinWord_rd (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_word" [k]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r.headD 0 = rdW (s₀.mem.arr64 PINS) k; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pinWordL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [rdW]

theorem pinW_rdW (m : Mem) (k : Nat) (w : Word) (hk : w.toNat = k) :
    pinW m k = rdW (m.arr64 PINS) w := by
  simp only [pinW, rdW, hk]

/-- A twin run that keeps the state, as a `CoreRef` (the memory unchanged). -/
theorem coreRef_pure {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {r : List Word} {v : α} (hS : CoreS dn m a₀ vis fe M eb) (hrun : T.run a₀ = .ok (v, a₀))
    (hv : v = dec r) (hr : ResH r) : CoreRef T a₀ dec dn m vis fe M eb r m := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok, ?_, by rw [hres, hv], hr⟩
  rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩

theorem resH_bool (c : Prop) [Decidable c] : ResH [if c then 1 else 0] := by
  unfold ResH HW; split <;> decide

theorem decBool_ite (c : Prop) [Decidable c] : decBool [if c then 1 else 0] = decide c := by
  unfold decBool; split <;> simp_all

theorem decBool_of {c : Prop} [Decidable c] {r : List Word} (hr : (if c then 1 else 0) = r.headD 0) :
    decBool r = decide c := by
  unfold decBool; rw [← hr]
  by_cases hc : c <;> simp only [hc, ↓reduceIte, decide_true, decide_false] <;> decide

theorem decBool_of' {c : Prop} [Decidable c] {r : List Word} (hr : (if c then 0 else 1) = r.headD 0) :
    decBool r = !decide c := by
  unfold decBool; rw [← hr]
  by_cases hc : c <;> simp only [hc, ↓reduceIte, decide_true, decide_false] <;> decide

theorem hw0 : HW 0 := by unfold HW; decide
theorem hw1 : HW 1 := by unfold HW; decide

theorem resH_of {c : Prop} [Decidable c] {r : List Word} {x y : Word} (hx : HW x) (hy : HW y)
    (hr : (if c then x else y) = r.headD 0) : ResH r := by
  unfold ResH; rw [← hr]; split <;> assumption

/-! ## `is_bool_true` -/

/-- The model of `is_bool_true` (`none` where it aborts). -/
def isBoolTrueW (m : Mem) (h : Word) : Option Word :=
  if h >>> 28 ≠ 3 then some 0
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h then none
  else if rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1) ≠ rdW (m.arr64 PINS) 52 then some 0
  else some (if rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2) = rdW (m.arr64 PINS) (1 + 30) then 1
    else 0)

theorem isBoolTrue_spec (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "is_bool_true" [h]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ isBoolTrueW s₀.mem h = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp.bt]
  simp only [callFn, isBoolTrueL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      pinAt_rd p hp.pinat n, pinWord_rd p hp.pinword n] <;>
    finish [isBoolTrueW, tierW, idxW, rdW]

theorem decI_bne {k : IdxKind} (v w : Word) (hv : v.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32) :
    ((decI v : Idx k) != decI w) = !decide (v = w) := by
  simp only [bne, decI_beq v w hv hw]

theorem tag_const : ETag.const = UInt32.ofNat 3 := rfl

theorem tag_beq_const (h : Word) (hh : HW h) :
    ((decE h).tag == ETag.const) = decide (h >>> 28 = 3) := by
  rw [tag_const, decE_tag_beq h hh 3 (by decide)]; rfl

theorem isBoolTrue_run (m : Mem) (a : AState) (hR : ArenaR m a) (hP : PinsFull m a.pins)
    (h : Word) (hh : HW h) (w : Word) (hW : isBoolTrueW m h = some w) :
    (isBoolTrue (decE h)).run a = .ok (w != 0, a) := by
  unfold isBoolTrueW at hW
  rcases (Classical.em (h >>> 28 = 3)).symm with h3 | h3
  · simp only [ne_eq, h3, not_false_eq_true, ↓reduceIte, Option.some.injEq] at hW
    subst hW
    simp only [isBoolTrue, tag_beq_const h hh, h3, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [h3, hs] at hW
  by_cases hc : rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h
  · simp [h3, hs, hc] at hW
  obtain ⟨hv, hn, hu⟩ := L.Ind.view_const_f m a hR h hh ⟨hs, by simpa using hc⟩ h3
  have hel := hP.lv_lt.1
  rw [pinW_rdW m 52 52 rfl] at hel
  have hbt := hP.names_lt 30 (by decide)
  rw [pinW_rdW m (1 + 30) (1 + 30) rfl] at hbt
  simp only [h3, hs, hc, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  simp only [isBoolTrue, tag_beq_const h hh, h3, decide_true, ↓reduceIte,
    StateT.run_bind, view_run _ _ _ hv, except_ok_bind, emptyLevels, pinEmptyLevels_run hP,
    pinW_rdW m 52 52 rfl, boolTrueName, pinBoolTrue, PIN_BOOL_TRUE]
  by_cases hus : rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1) = rdW (m.arr64 PINS) 52
  · simp only [hus, not_true_eq_false, ↓reduceIte, Option.some.injEq] at hW
    subst hW
    rw [decI_bne _ _ hu hel]
    simp only [bne, hus, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, pinAt_run hP 30 (by decide), pinW_rdW m (1 + 30) (1 + 30) rfl, except_ok_bind,
      StateT.run_pure]
    rw [decI_beq _ _ hn hbt]
    split <;> (rename_i hx; simp only [hx, decide_true, decide_false]; rfl)
  · simp only [hus, not_false_eq_true, ↓reduceIte, Option.some.injEq] at hW
    subst hW
    rw [decI_bne _ _ hu hel]
    simp only [bne, hus, decide_false, Bool.not_false, ↓reduceIte]
    rfl

/-- **`is_bool_true` refines `isBoolTrue`.** -/
@[refines ConRon.Arena.isBoolTrue]
theorem isBoolTrue_refines (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb h : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (hh : HW h) :
    CoreSpec p (n + 1) "is_bool_true" [h] (isBoolTrue (decE h)) decBool s₀ a₀ dn vis fe MM eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hm, hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (isBoolTrue_spec p hp n s₀ h)
  subst hs0
  refine ⟨hloc, ?_⟩
  rw [hm]
  have hrun' := isBoolTrue_run _ _ hS.arena.1 hS.pins h hh _ hW
  refine coreRef_pure hS hrun' rfl ?_
  unfold isBoolTrueW at hW
  unfold ResH HW
  repeat' split at hW
  all_goals simp only [reduceCtorEq, Option.some.injEq] at hW
  all_goals (rw [← hW]; decide)

/-! ## `get_app_fn` runs -/

/-- **A run of `get_app_fn`**: the memory unchanged, the twin's `getAppFn` at the result. -/
theorem getAppFn_callW {p : Prog} (hp : DefEqLeafProg p) {n : Nat} {m m' : Mem} {a : AState}
    (hR : ArenaR m a) {e : Word} (he : HW e) {r : List Word}
    (hc : callW p n "get_app_fn" [e] m = some (r, m')) :
    m' = m ∧ HW (r.headD 0) ∧
      (getAppFn coreWalkFuel (decE e)).run a = .ok (decE (r.headD 0), a) := by
  obtain ⟨t, ht, hm, -, hh, hrun⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (getAppFn_refines p hp.core.spine n ⟨m, Locals.init []⟩ a hR e he) hc
  exact ⟨ht ▸ hm, hh, hrun⟩

theorem tag_beq_w (h : Word) (hh : HW h) (k : Nat) (hk : k < 16) (t : UInt32) (ht : t = UInt32.ofNat k)
    (w : Word) (hw : UInt64.ofNat k = w) : ((decE h).tag == t) = decide (h >>> 28 = w) := by
  rw [ht, decE_tag_beq h hh k hk, hw]

/-! ## `head_is_proj` -/

def headIsProjW (p : Prog) (n : Nat) (m : Mem) (e : Word) : Option (Word × Mem) :=
  match callW p n "get_app_fn" [e] m with
  | none => none
  | some (r, m₁) => some (if r.headD 0 >>> 28 = 9 then 1 else 0, m₁)

theorem headIsProjW_eq (p : Prog) (n : Nat) (m m₁ : Mem) (e : Word) (r : List Word)
    (h : callW p n "get_app_fn" [e] m = some (r, m₁)) :
    headIsProjW p n m e = some (if r.headD 0 >>> 28 = 9 then 1 else 0, m₁) := by
  simp only [headIsProjW, h]

theorem headIsProj_spec (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "head_is_proj" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ headIsProjW p n s₀.mem e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.hproj]
  simp only [callFn, headIsProjL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "get_app_fn"] <;>
    finish [headIsProjW_eq]

/-- **`head_is_proj` refines `headIsProj`.** -/
@[refines ConRon.Arena.headIsProj]
theorem headIsProj_refines (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb e : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) :
    CoreSpec p (n + 1) "head_is_proj" [e] (headIsProj (decE e)) decBool s₀ a₀ dn vis fe MM eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (headIsProj_spec p hp n s₀ e)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc : callW p n "get_app_fn" [e] s.mem with
  | none => simp [headIsProjW, hc] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [headIsProjW_eq p n _ _ e r₁ hc, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  obtain ⟨rfl, hh, hgaf⟩ := getAppFn_callW hp hS.arena.1 he hc
  rw [← hm]
  refine coreRef_pure hS (v := decide (r₁.headD 0 >>> 28 = 9)) ?_ ?_ ?_
  · simp only [headIsProj, StateT.run_bind, hgaf, except_ok_bind]
    rw [tag_beq_w _ hh 9 (by decide) ETag.proj rfl 9 rfl]; rfl
  · exact (decBool_of hr).symm
  · exact resH_of hw1 hw0 hr

/-! ## `io_neutral` -/

def ioNeutralW (p : Prog) (n : Nat) (m : Mem) (e : Word) : Option (Word × Mem) :=
  match callW p n "get_app_fn" [e] m with
  | none => none
  | some (r, m₁) =>
    some (if r.headD 0 >>> 28 = 5 ∨ r.headD 0 >>> 28 = 7 ∨ r.headD 0 >>> 28 = 0 then 0 else 1, m₁)

theorem ioNeutralW_eq (p : Prog) (n : Nat) (m m₁ : Mem) (e : Word) (r : List Word)
    (h : callW p n "get_app_fn" [e] m = some (r, m₁)) :
    ioNeutralW p n m e = some (if r.headD 0 >>> 28 = 5 ∨ r.headD 0 >>> 28 = 7 ∨ r.headD 0 >>> 28 = 0
      then 0 else 1, m₁) := by
  simp only [ioNeutralW, h]

theorem ioNeutral_spec (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "io_neutral" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ ioNeutralW p n s₀.mem e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ion]
  simp only [callFn, ioNeutralL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "get_app_fn"] <;>
    finish [ioNeutralW_eq]

/-- **`io_neutral` refines `ioNeutral`.** -/
@[refines ConRon.Arena.ioNeutral]
theorem ioNeutral_refines (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb e : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) :
    CoreSpec p (n + 1) "io_neutral" [e] (ioNeutral (decE e)) decBool s₀ a₀ dn vis fe MM eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (ioNeutral_spec p hp n s₀ e)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc : callW p n "get_app_fn" [e] s.mem with
  | none => simp [ioNeutralW, hc] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [ioNeutralW_eq p n _ _ e r₁ hc, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  obtain ⟨rfl, hh, hgaf⟩ := getAppFn_callW hp hS.arena.1 he hc
  rw [← hm]
  refine coreRef_pure hS (v := !decide (r₁.headD 0 >>> 28 = 5 ∨ r₁.headD 0 >>> 28 = 7 ∨
    r₁.headD 0 >>> 28 = 0)) ?_ ?_ ?_
  · simp only [ioNeutral, StateT.run_bind, hgaf, except_ok_bind]
    rw [tag_beq_w _ hh 5 (by decide) ETag.lam rfl 5 rfl, tag_beq_w _ hh 7 (by decide) ETag.letE rfl 7 rfl,
      tag_beq_w _ hh 0 (by decide) ETag.bvar rfl 0 rfl]
    by_cases h5 : r₁.headD 0 >>> 28 = 5 <;> by_cases h7 : r₁.headD 0 >>> 28 = 7 <;>
      by_cases h0 : r₁.headD 0 >>> 28 = 0 <;>
      simp only [h5, h7, h0, decide_true, decide_false, ↓reduceIte, Bool.not_true, Bool.not_false,
        true_or, or_true, or_false] <;> rfl
  · exact (decBool_of' hr).symm
  · exact resH_of hw0 hw1 hr

/-! ## `is_eager_reduce` -/

/-- The scratch-tier and count checks of a view (`none`: the L code aborts). -/
def viewChk (m : Mem) (h c : Word) : Prop :=
  ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) ∧ ¬ rdW (m.arr64 CTL) (c + tierW h) ≤ idxW h

instance (m : Mem) (h c : Word) : Decidable (viewChk m h c) := by unfold viewChk; infer_instance

theorem viewChk_ok {m : Mem} {h c : Word} (hc : viewChk m h c) : viewOK m h c :=
  ⟨hc.1, by have := hc.2; simpa using this⟩

/-- `is_eager_reduce`'s last stage: the head `g` of `eagerReduce _ _`. -/
def eagerG (m : Mem) (g : Word) : Option Word :=
  if g >>> 28 ≠ 3 then some 0
  else if tierW g ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (18 + tierW g) ≤ idxW g then none
  else some (if rdW (m.arr64 CREC) (idxW g * 4 + tierW g * 2) = rdW (m.arr64 PINS) (1 + 50) then 1
    else 0)

def eagerF (m : Mem) (f : Word) : Option Word :=
  if f >>> 28 ≠ 4 then some 0
  else if tierW f ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (4 + tierW f) ≤ idxW f then none
  else eagerG m (rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2))

/-- The model of `is_eager_reduce`. -/
def isEagerReduceW (m : Mem) (h : Word) : Option Word :=
  if h >>> 28 ≠ 4 then some 0
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h then none
  else eagerF m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2))

section eagerArms
variable (m : Mem) (h : Word)

theorem eagerG_tag (h3 : ¬ h >>> 28 = 3) : eagerG m h = some 0 := by simp [eagerG, h3]
theorem eagerG_go (h3 : h >>> 28 = 3) (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hc : ¬ rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h) :
    eagerG m h = some (if rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2) = rdW (m.arr64 PINS) (1 + 50)
      then 1 else 0) := by
  simp only [eagerG, h3, hs, hc, ne_eq, not_true_eq_false, ↓reduceIte]
theorem eagerF_tag (h4 : ¬ h >>> 28 = 4) : eagerF m h = some 0 := by simp [eagerF, h4]
theorem eagerF_go (h4 : h >>> 28 = 4) (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hc : ¬ rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h) :
    eagerF m h = eagerG m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) := by
  simp only [eagerF, h4, hs, hc, ne_eq, not_true_eq_false, ↓reduceIte]
theorem eagerW_tag (h4 : ¬ h >>> 28 = 4) : isEagerReduceW m h = some 0 := by
  simp [isEagerReduceW, h4]
theorem eagerW_go (h4 : h >>> 28 = 4) (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hc : ¬ rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h) :
    isEagerReduceW m h = eagerF m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) := by
  simp only [isEagerReduceW, h4, hs, hc, ne_eq, not_true_eq_false, ↓reduceIte]

end eagerArms

set_option maxHeartbeats 2000000 in
theorem isEagerReduce_spec (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "is_eager_reduce" [h]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ isEagerReduceW s₀.mem h = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp.eager]
  simp only [callFn, isEagerReduceL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      pinAt_rd p hp.pinat n] <;>
    finish [eagerW_tag, eagerW_go, eagerF_tag, eagerF_go, eagerG_tag, eagerG_go, tierW, idxW]

theorem tag_beq_app (h : Word) (hh : HW h) :
    ((decE h).tag == ETag.app) = decide (h >>> 28 = 4) := tag_beq_w h hh 4 (by decide) _ rfl 4 rfl

theorem isEagerReduce_run (m : Mem) (a : AState) (hR : ArenaR m a) (hP : PinsFull m a.pins)
    (h : Word) (hh : HW h) (w : Word) (hW : isEagerReduceW m h = some w) :
    (isEagerReduce (decE h)).run a = .ok (w != 0, a) := by
  unfold isEagerReduceW at hW
  rcases (Classical.em (h >>> 28 = 4)).symm with h4 | h4
  · simp only [ne_eq, h4, not_false_eq_true, ↓reduceIte, Option.some.injEq] at hW
    subst hW
    simp only [isEagerReduce, tag_beq_app h hh, h4, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [h4, hs] at hW
  by_cases hc : rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h
  · simp [h4, hs, hc] at hW
  simp only [h4, hs, hc, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  have hvo : viewOK m h 4 := ⟨hs, by simpa using hc⟩
  obtain ⟨-, hf, -⟩ := view_app m a hR h hh hvo h4
  simp only [isEagerReduce, tag_beq_app h hh, h4, decide_true, ↓reduceIte, StateT.run_bind,
    viewApp_run', viewApp_ok m a hR h hh hvo, except_ok_bind]
  generalize rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2) = f at hf hW ⊢
  unfold eagerF at hW
  rcases (Classical.em (f >>> 28 = 4)).symm with f4 | f4
  · simp only [ne_eq, f4, not_false_eq_true, ↓reduceIte, Option.some.injEq] at hW
    subst hW
    simp only [tag_beq_app f hf, f4, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  by_cases fs : tierW f ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [f4, fs] at hW
  by_cases fc : rdW (m.arr64 CTL) (4 + tierW f) ≤ idxW f
  · simp [f4, fs, fc] at hW
  simp only [f4, fs, fc, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  have fvo : viewOK m f 4 := ⟨fs, by simpa using fc⟩
  obtain ⟨-, hg, -⟩ := view_app m a hR f hf fvo f4
  simp only [tag_beq_app f hf, f4, decide_true, ↓reduceIte, StateT.run_bind,
    viewApp_run', viewApp_ok m a hR f hf fvo, except_ok_bind]
  generalize rdW (m.arr64 AREC) (idxW f * 4 + tierW f * 2) = g at hg hW ⊢
  unfold eagerG at hW
  rcases (Classical.em (g >>> 28 = 3)).symm with g3 | g3
  · simp only [ne_eq, g3, not_false_eq_true, ↓reduceIte, Option.some.injEq] at hW
    subst hW
    simp only [tag_beq_const g hg, g3, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  by_cases gs : tierW g ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [g3, gs] at hW
  by_cases gc : rdW (m.arr64 CTL) (18 + tierW g) ≤ idxW g
  · simp [g3, gs, gc] at hW
  simp only [g3, gs, gc, ne_eq, not_true_eq_false, ↓reduceIte, Option.some.injEq] at hW
  have gvo : viewOK m g 18 := ⟨gs, by simpa using gc⟩
  obtain ⟨-, hn, -⟩ := L.Ind.view_const_f m a hR g hg gvo g3
  have her := hP.names_lt 50 (by decide)
  rw [pinW_rdW m (1 + 50) (1 + 50) rfl] at her
  subst hW
  simp only [tag_beq_const g hg, g3, decide_true, ↓reduceIte, StateT.run_bind, L.Ind.viewConst_run',
    L.Ind.viewConst_ok m a hR g hg gvo, except_ok_bind, eagerReduceName, pinEagerReduce,
    PIN_EAGER_REDUCE, pinAt_run hP 50 (by decide), pinW_rdW m (1 + 50) (1 + 50) rfl,
    StateT.run_pure]
  rw [decI_beq _ _ hn her]
  split <;> (rename_i hx; simp only [hx, decide_true, decide_false]; rfl)

/-- **`is_eager_reduce` refines `isEagerReduce`.** -/
@[refines ConRon.Arena.isEagerReduce]
theorem isEagerReduce_refines (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb h : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (hh : HW h) :
    CoreSpec p (n + 1) "is_eager_reduce" [h] (isEagerReduce (decE h)) decBool s₀ a₀ dn vis fe MM eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hm, hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (isEagerReduce_spec p hp n s₀ h)
  subst hs0
  refine ⟨hloc, ?_⟩
  rw [hm]
  have hrun' := isEagerReduce_run _ _ hS.arena.1 hS.pins h hh _ hW
  refine coreRef_pure hS hrun' rfl ?_
  unfold isEagerReduceW eagerF eagerG at hW
  unfold ResH HW
  repeat' split at hW
  all_goals simp only [reduceCtorEq, Option.some.injEq] at hW
  all_goals (rw [← hW]; decide)

/-! ## Literal nodes -/

theorem pv_eq_zero_iff (p : Array Word) (o l : Nat) (hn : Norm p o l) : pv p o l = 0 ↔ l = 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos l with hl | hl
    · exact hl
    · have := pv_ge p o l hl hn
      have : 0 < wt (l - 1) := Nat.two_pow_pos _
      omega
  · intro h; subst h; rfl

/-- **A `lit` node past the view checks**: kind word `0` is a `natVal` whose value is `0` iff the
length word is; another kind word is a `strVal`. -/
theorem view_lit_nat (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : HW h)
    (hv : viewOK m h 2) (hg : h >>> 28 = 8) :
    (rdW (m.arr64 REC) (idxW h * 8 + tierW h * 4) = 0 →
      ∃ N, a.store.view (decE h) = some (.lit (.natVal N)) ∧
        (N = 0 ↔ rdW (m.arr64 REC) (idxW h * 8 + tierW h * 4 + 2) = 0)) ∧
    (rdW (m.arr64 REC) (idxW h * 8 + tierW h * 4) ≠ 0 →
      ∃ s, a.store.view (decE h) = some (.lit (.strVal s))) := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h litSch RecRel litH (·.lits) _ hR.lit.2 hv.2
  have hview : ∀ l, k = ⟨l⟩ → a.store.view (decE h) = some (.lit l) := by
    intro l hl
    rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk, hl]
    rfl
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · simp only [RecRel_natVal, NatRec] at hkr
    obtain ⟨h0, -, hn, hpv, -⟩ := hkr
    refine ⟨fun _ => ⟨N, hview _ rfl, ?_⟩, fun hc => absurd h0 hc⟩
    rw [← hpv, pv_eq_zero_iff _ _ _ hn]
    constructor
    · intro e; exact UInt64.toNat_inj.mp (by simpa using e)
    · intro e; rw [e]; rfl
  · simp only [RecRel_strVal, StrRec] at hkr
    exact ⟨fun hc => absurd (hkr.1.symm.trans hc) (by decide), fun _ => ⟨s, hview _ rfl⟩⟩

theorem tag_beq_lit (h : Word) (hh : HW h) :
    ((decE h).tag == ETag.lit) = decide (h >>> 28 = 8) := tag_beq_w h hh 8 (by decide) _ rfl 8 rfl

/-! ## `is_nat_zero` -/

/-- The model of `is_nat_zero`. -/
def isNatZeroW (m : Mem) (e : Word) : Option Word :=
  if e >>> 28 = 8 then
    if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (2 + tierW e) ≤ idxW e then none
    else if rdW (m.arr64 REC) (idxW e * 8 + tierW e * 4) ≠ 0 then some 0
    else some (if rdW (m.arr64 REC) (idxW e * 8 + tierW e * 4 + 2) = 0 then 1 else 0)
  else if e >>> 28 = 3 then
    if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (18 + tierW e) ≤ idxW e then none
    else some (if rdW (m.arr64 CREC) (idxW e * 4 + tierW e * 2) = rdW (m.arr64 PINS) (1 + 2) ∧
      rdW (m.arr64 CREC) (idxW e * 4 + tierW e * 2 + 1) = rdW (m.arr64 PINS) 52 then 1 else 0)
  else some 0

theorem isNatZero_spec (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "is_nat_zero" [e]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ isNatZeroW s₀.mem e = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp.natzero]
  simp only [callFn, isNatZeroL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      pinAt_rd p hp.pinat n, pinWord_rd p hp.pinword n] <;>
    finish [isNatZeroW, tierW, idxW]

theorem isNatZero_run (m : Mem) (a : AState) (hR : ArenaR m a) (hP : PinsFull m a.pins)
    (e : Word) (he : HW e) (w : Word) (hW : isNatZeroW m e = some w) :
    (isNatZero (decE e)).run a = .ok (w != 0, a) := by
  unfold isNatZeroW at hW
  by_cases h8 : e >>> 28 = 8
  · simp only [h8, ↓reduceIte] at hW
    by_cases hs : tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
    · simp [hs] at hW
    by_cases hc : rdW (m.arr64 CTL) (2 + tierW e) ≤ idxW e
    · simp [hs, hc] at hW
    simp only [hs, hc, ↓reduceIte] at hW
    have hvo : viewOK m e 2 := ⟨hs, by simpa using hc⟩
    obtain ⟨hnat, hstr⟩ := view_lit_nat m a hR e he hvo h8
    simp only [isNatZero, tag_beq_lit e he, h8, decide_true, ↓reduceIte, StateT.run_bind]
    by_cases hk : rdW (m.arr64 REC) (idxW e * 8 + tierW e * 4) = 0
    · obtain ⟨N, hv, hN⟩ := hnat hk
      simp only [hk, ne_eq, not_true_eq_false, ↓reduceIte, Option.some.injEq] at hW
      subst hW
      simp only [view_run _ _ _ hv, except_ok_bind]
      by_cases hl : rdW (m.arr64 REC) (idxW e * 8 + tierW e * 4 + 2) = 0
      · simp only [hl, ↓reduceIte, hN.mpr hl] <;> rfl
      · have : N ≠ 0 := fun h => hl (hN.mp h)
        simp only [hl, ↓reduceIte]
        show Except.ok (N == 0, a) = _
        simp [this]
    · obtain ⟨s, hv⟩ := hstr hk
      simp only [hk, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq] at hW
      subst hW
      simp only [view_run _ _ _ hv, except_ok_bind]
      rfl
  have ht8 : ((decE e).tag == ETag.lit) = false := by rw [tag_beq_lit e he]; simp [h8]
  rcases (Classical.em (e >>> 28 = 3)).symm with h3 | h3
  · simp only [h8, ↓reduceIte] at hW
    simp only [h3, ↓reduceIte, Option.some.injEq] at hW
    subst hW
    simp only [isNatZero, ht8, tag_beq_const e he, h3, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  simp only [h8, ↓reduceIte] at hW
  simp only [h3, ↓reduceIte] at hW
  by_cases hs : tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hW
  by_cases hc : rdW (m.arr64 CTL) (18 + tierW e) ≤ idxW e
  · simp [hs, hc] at hW
  simp only [hs, hc, ↓reduceIte, Option.some.injEq] at hW
  subst hW
  have hvo : viewOK m e 18 := ⟨hs, by simpa using hc⟩
  obtain ⟨hv, hn, hu⟩ := L.Ind.view_const_f m a hR e he hvo h3
  have hel := hP.lv_lt.1
  rw [pinW_rdW m 52 52 rfl] at hel
  have hnz := hP.names_lt 2 (by decide)
  rw [pinW_rdW m (1 + 2) (1 + 2) rfl] at hnz
  simp only [isNatZero, ht8, tag_beq_const e he, h3, decide_true, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind, view_run _ _ _ hv, except_ok_bind, emptyLevels, pinEmptyLevels_run hP,
    pinNatZero, PIN_NAT_ZERO, pinAt_run hP 2 (by decide), StateT.run_pure,
    pinW_rdW m 52 52 rfl, pinW_rdW m (1 + 2) (1 + 2) rfl]
  rw [decI_beq _ _ hn hnz, decI_beq _ _ hu hel]
  by_cases h1 : rdW (m.arr64 CREC) (idxW e * 4 + tierW e * 2) = rdW (m.arr64 PINS) (1 + 2) <;>
  by_cases h2 : rdW (m.arr64 CREC) (idxW e * 4 + tierW e * 2 + 1) = rdW (m.arr64 PINS) 52 <;>
  simp only [h1, h2, decide_true, decide_false, Bool.and_true, Bool.and_false, and_true, and_false,
    ↓reduceIte] <;> rfl

/-- **`is_nat_zero` refines `isNatZero`.** -/
@[refines ConRon.Arena.isNatZero]
theorem isNatZero_refines (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb e : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) :
    CoreSpec p (n + 1) "is_nat_zero" [e] (isNatZero (decE e)) decBool s₀ a₀ dn vis fe MM eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hm, hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (isNatZero_spec p hp n s₀ e)
  subst hs0
  refine ⟨hloc, ?_⟩
  rw [hm]
  have hrun' := isNatZero_run _ _ hS.arena.1 hS.pins e he _ hW
  refine coreRef_pure hS hrun' rfl ?_
  unfold isNatZeroW at hW
  unfold ResH HW
  repeat' split at hW
  all_goals simp only [reduceCtorEq, Option.some.injEq] at hW
  all_goals (rw [← hW]; decide)

end L.Arena
