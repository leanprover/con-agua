import ConAgua.Arena.DefEq
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.IndPartsSpec3
import ConAgua.Arena.DefEqGrindAttr

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
  hhint : p.lookup "head_hint" = some headHintL
  hlt : p.lookup "hint_lt" = some hintLtL
  ufh : p.lookup "unfoldable_head" = some unfoldableHeadL

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

/-! ## Definition records -/

/-- A `(kind, height)` hint word pair (`decHint`'s layout; kinds past `2` read as `regular`). -/
def decHintW (k h : Word) : ConLeche.ReducibilityHint :=
  if k = 0 then .opaque else if k = 1 then .abbrev else .regular h.toNat

/-- A `head_hint` result. -/
def decHintR (r : List Word) : ConLeche.ReducibilityHint := decHintW (r.headD 0) (r.tail.headD 0)

theorem mapM_length {β : Type} {f : Nat → Option β} :
    ∀ {l : List Nat} {r : List β}, l.mapM f = some r → r.length = l.length
  | [], r, h => by simp at h; subst h; rfl
  | x :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, -, ys, hys, rfl⟩ := h
    simp [mapM_length hys]

/-- Word `q + k` of an extension, read off the decoded array. -/
theorem rdW_ext {a b : Array Word} (hab : ArrExt a b) (hsz : b.size < 2 ^ 63) {q : Word} {k : Nat}
    (hk : k < 16) {w : Word} (ha : a[q.toNat + k]? = some w) : rdW b (q + UInt64.ofNat k) = w := by
  have hb := hab _ _ ha
  have hlt : q.toNat + k < b.size := by
    rcases Nat.lt_or_ge (q.toNat + k) b.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at hb
  have : (q + UInt64.ofNat k).toNat = q.toNat + k := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']; rw [Nat.mod_eq_of_lt (a := k) (by omega)]; omega
  simp only [rdW, this, hb, Option.getD_some]

/-- The kind word of a decoded constant record says whether it is a definition; a definition's
level-parameter count is word `q + 3`, its hint words `q + 6`, `q + 7`. -/
theorem decCI_defn {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI a dn q.toNat = some ci) (hab : ArrExt a b)
    (hsz : b.size < 2 ^ 63) :
    (rdW b q = 1 → ∃ cv v, ci = .defnInfo cv v (decHintW (rdW b (q + 6)) (rdW b (q + 7))) ∧
      cv.levelParams.length = (rdW b (q + 3)).toNat ∧ (rdW b (q + 6)).toNat ≤ 2) ∧
    (rdW b q ≠ 1 → ∀ cv v hint, ci ≠ .defnInfo cv v hint) := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  have hrd : rdW b q = w := by
    have := rdW_ext hab hsz (k := 0) (by decide) (by simpa using hq); simpa using this
  rw [hrd]
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  constructor
  · intro hw; subst hw
    simp only [show UInt64.toNat 1 = 1 from rfl, Option.bind_eq_some_iff] at h
    obtain ⟨cv, hcv, v, -, hint, hhint, hc⟩ := h
    cases hc
    refine ⟨cv, v, ?_, ?_, ?_⟩
    · simp only [decHint, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hhint
      obtain ⟨k, ⟨wk, hwk, rfl⟩, hk⟩ := hhint
      have h6 : rdW b (q + 6) = wk := rdW_ext hab hsz (k := 6) (by decide) hwk
      rw [h6]
      rcases hkk : wk.toNat with _ | _ | _ | k
      · rw [hkk] at hk; cases hk
        have : wk = 0 := UInt64.toNat_inj.mp (by simpa using hkk)
        simp [decHintW, this]
      · rw [hkk] at hk; cases hk
        have : wk = 1 := UInt64.toNat_inj.mp (by simpa using hkk)
        simp [decHintW, this]
      · rw [hkk] at hk
        simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at hk
        obtain ⟨hh, ⟨wh, hwh, rfl⟩, rfl⟩ := hk
        have h7 : rdW b (q + 7) = wh := rdW_ext hab hsz (k := 7) (by decide)
          (by simpa [Nat.add_assoc] using hwh)
        have h0 : wk ≠ 0 := fun e => by subst e; simp at hkk
        have h1 : wk ≠ 1 := fun e => by subst e; simp at hkk
        simp [decHintW, h0, h1, h7]
      · rw [hkk] at hk; simp at hk
    · simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcv
      obtain ⟨nm, -, ls, hls, ty, -, hc⟩ := hcv
      cases hc
      simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hls
      obtain ⟨o, -, c, ⟨wc, hwc, rfl⟩, hs⟩ := hls
      have h3 : rdW b (q + 3) = wc := rdW_ext hab hsz (k := 3) (by decide)
        (by simpa [Nat.add_assoc] using hwc)
      rw [h3]
      simp only [hslice?] at hs
      rw [mapM_length hs, List.length_range]
    · simp only [decHint, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hhint
      obtain ⟨k, ⟨wk, hwk, rfl⟩, hk⟩ := hhint
      have h6 : rdW b (q + 6) = wk := rdW_ext hab hsz (k := 6) (by decide) hwk
      rw [h6]
      rcases hkk : wk.toNat with _ | _ | _ | k
      · omega
      · omega
      · omega
      · rw [hkk] at hk; simp at hk
  · intro hw cv v hint hc
    subst hc
    have hne : w.toNat ≠ 1 := fun e => hw (UInt64.toNat_inj.mp (by rw [e]; rfl))
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h hne; simp [Option.bind_eq_some_iff] at h hne)

/-! ## `head_hint` -/

/-- After `env_find`: the hint words of a definition, else `(0, 0)` (opaque). -/
def hhEnv (q : Option (List Word × Mem)) : Option (Word × Word × Mem) :=
  match q with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, 0, m)
    else if rdW (m.arr64 EREC) (r.tail.headD 0) ≠ 1 then some (0, 0, m)
    else some (rdW (m.arr64 EREC) (r.tail.headD 0 + 6), rdW (m.arr64 EREC) (r.tail.headD 0 + 7), m)

/-- After `get_app_fn`: the head `hh`. -/
def hhHead (p : Prog) (n : Nat) (m : Mem) (vis hh : Word) : Option (Word × Word × Mem) :=
  if hh >>> 28 ≠ 3 then some (0, 0, m)
  else if tierW hh ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (18 + tierW hh) ≤ idxW hh then none
  else hhEnv (callW p n "env_find" [rdW (m.arr64 CREC) (idxW hh * 4 + tierW hh * 2), vis] m)

/-- The model of `head_hint`. -/
def headHintW (p : Prog) (n : Nat) (m : Mem) (vis e : Word) : Option (Word × Word × Mem) :=
  match callW p n "get_app_fn" [e] m with
  | none => none
  | some (r, m₁) => hhHead p n m₁ vis (r.headD 0)

section hhArms
variable (p : Prog) (n : Nat) (m m₁ : Mem) (vis e hh : Word) (r : List Word)
  (q : Option (List Word × Mem))

theorem headHintW_eq (h : callW p n "get_app_fn" [e] m = some (r, m₁)) :
    headHintW p n m vis e = hhHead p n m₁ vis (r.headD 0) := by simp only [headHintW, h]
theorem hhHead_tag (h3 : ¬ hh >>> 28 = 3) : hhHead p n m vis hh = some (0, 0, m) := by
  simp [hhHead, h3]
theorem hhHead_go (h3 : hh >>> 28 = 3) (hs : ¬ (tierW hh ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hc : ¬ rdW (m.arr64 CTL) (18 + tierW hh) ≤ idxW hh) :
    hhHead p n m vis hh =
      hhEnv (callW p n "env_find" [rdW (m.arr64 CREC) (idxW hh * 4 + tierW hh * 2), vis] m) := by
  simp only [hhHead, h3, hs, hc, ne_eq, not_true_eq_false, ↓reduceIte]
theorem hhEnv_zero (h : q = some (r, m)) (h0 : r.headD 0 = 0) : hhEnv q = some (0, 0, m) := by
  subst h; simp only [hhEnv, h0, ↓reduceIte]
theorem hhEnv_kind (h : q = some (r, m)) (h0 : ¬ r.headD 0 = 0)
    (h1 : ¬ rdW (m.arr64 EREC) (r.tail.headD 0) = 1) : hhEnv q = some (0, 0, m) := by
  subst h; simp only [hhEnv, h0, h1, ne_eq, ↓reduceIte] <;> simp
theorem hhEnv_defn (h : q = some (r, m)) (h0 : ¬ r.headD 0 = 0)
    (h1 : rdW (m.arr64 EREC) (r.tail.headD 0) = 1) :
    hhEnv q = some (rdW (m.arr64 EREC) (r.tail.headD 0 + 6), rdW (m.arr64 EREC) (r.tail.headD 0 + 7),
      m) := by
  subst h; simp only [hhEnv, h0, h1, ne_eq, ↓reduceIte] <;> simp

end hhArms

grind_pattern [defeq_grind] headHintW_eq => headHintW p n m vis e, (r, m₁)
grind_pattern [defeq_grind] hhHead_tag => hhHead p n m vis hh
grind_pattern [defeq_grind] hhHead_go => hhHead p n m vis hh
grind_pattern [defeq_grind] hhEnv_zero => hhEnv q, (r, m)
grind_pattern [defeq_grind] hhEnv_kind => hhEnv q, (r, m)
grind_pattern [defeq_grind] hhEnv_defn => hhEnv q, (r, m)

theorem headHint_spec (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (vis e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "head_hint" [vis, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      headHintW p n s₀.mem vis e = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.hhint]
  simp only [callFn, headHintL]
  sym only [lang_grind, arena_grind, defeq_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "get_app_fn", callW_spec p n "env_find"] <;>
    finish [tierW, idxW]

/-- The hint the twin reads off a lookup. -/
def hintOf : Option IConstantInfo → ConLeche.ReducibilityHint
  | some (.defnInfo _ _ hint) => hint
  | _ => .opaque

theorem hintOf_none (o : Option IConstantInfo) (h : ∀ cv v hint, o ≠ some (.defnInfo cv v hint)) :
    hintOf o = .opaque := by
  rcases o with _ | ⟨_ | ⟨cv, v, hint⟩ | _ | _ | _ | _ | _⟩ <;> try rfl
  exact absurd rfl (h cv v hint)

theorem headHint_run_nonconst (fe : IFEnv) (e : EIdx) (a : AState) (hh : EIdx)
    (hgaf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = false) :
    (headHint fe e).run a = .ok (.opaque, a) := by
  simp only [headHint, StateT.run_bind, hgaf, except_ok_bind, ht, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem headHint_run_const (fe : IFEnv) (e : EIdx) (a : AState) (hh : EIdx) (c : NIdx) (us : LsIdx)
    (hgaf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = true)
    (hv : a.store.view hh = some (.const c us)) :
    (headHint fe e).run a = .ok (hintOf (fe.find? c), a) := by
  simp only [headHint, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv]
  rcases fe.find? c with _ | ⟨_ | ⟨cv, v, hint⟩ | _ | _ | _ | _ | _⟩ <;> rfl

theorem decHintR_zero : decHintR [0, 0] = .opaque := rfl

/-- **`head_hint` refines `headHint`.** -/
@[refines ConRon.Arena.headHint]
theorem headHint_refines (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb e : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) :
    CoreSpec p (n + 1) "head_hint" [vis, e] (headHint fe (decE e)) decHintR s₀ a₀ dn vis fe MM eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (headHint_spec p hp n s₀ vis e)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc : callW p n "get_app_fn" [e] s.mem with
  | none => simp [headHintW, hc] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [headHintW_eq p n _ _ vis e r₁ hc] at hW
  obtain ⟨rfl, hh, hgaf⟩ := getAppFn_callW hp hS.arena.1 he hc
  have hR := hS.arena.1
  generalize r₁.headD 0 = h at hh hgaf hW
  have hres : ∀ x y : Word, some (x, y, s.mem) = some (r.headD 0, r.tail.headD 0, s'.mem) →
      HW x → ∀ v, (headHint fe (decE e)).run a₀ = .ok (v, a₀) → v = decHintW x y →
      CoreRef (headHint fe (decE e)) a₀ decHintR dn s.mem vis fe MM eb r s'.mem := by
    intro x y hxy hx v hv hvx
    simp only [Option.some.injEq, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    rw [← h3]
    refine coreRef_pure hS hv ?_ ?_
    · rw [hvx, decHintR, ← h1, ← h2]
    · unfold ResH; rw [← h1]; exact hx
  rcases (Classical.em (h >>> 28 = 3)).symm with h3 | h3
  · rw [hhHead_tag p n _ vis h h3] at hW
    exact hres 0 0 hW hw0 _
      (headHint_run_nonconst fe _ a₀ _ hgaf (by rw [tag_beq_const _ hh]; simp [h3])) rfl
  by_cases hs : tierW h ≠ 0 ∧ rdW (s.mem.arr64 CTL) 1 = 0
  · simp [hhHead, h3, hs] at hW
  by_cases hcc : rdW (s.mem.arr64 CTL) (18 + tierW h) ≤ idxW h
  · simp [hhHead, h3, hs, hcc] at hW
  rw [hhHead_go p n _ vis h h3 hs hcc] at hW
  have hvo : viewOK s.mem h 18 := ⟨hs, by simpa using hcc⟩
  obtain ⟨hv, hnw, -⟩ := L.Ind.view_const_f s.mem a₀ hR h hh hvo h3
  have hrun1 := headHint_run_const fe _ a₀ _ _ _ hgaf (by rw [tag_beq_const _ hh]; simp [h3]) hv
  generalize rdW (s.mem.arr64 CREC) (idxW h * 4 + tierW h * 2) = k at hnw hW hrun1
  cases hc2 : callW p n "env_find" [k, vis] s.mem with
  | none => simp [hhEnv, hc2] at hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  obtain ⟨t₂, ht₂, hm₂, -, hfind⟩ := triple_of_callW
    (envFind_refines p hp.core.envix hp.core.envrow hp.core.envfind n s vis k hS.env hnw) hc2
  obtain ⟨t₂', ht₂', hm₂', -, hfound⟩ := triple_of_callW
    (envFind_found p hp.core.envix hp.core.envrow hp.core.envfind n s vis k hnw) hc2
  rw [ht₂] at hm₂
  subst hm₂
  by_cases h0 : r₂.headD 0 = 0
  · rw [hhEnv_zero (h := hc2) (h0 := h0)] at hW
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [decFound, h0, ↓reduceIte]
    rw [hnone] at hrun1
    exact hres 0 0 hW hw0 _ hrun1 rfl
  obtain ⟨htag, hrow, hq⟩ := hfound h0
  obtain ⟨ci, hci⟩ := hS.env.found_some k hnw htag hrow
  have hfind' : fe.find? (decI k) = some ci := by
    rw [hfind]; simp only [decFound, h0, ↓reduceIte, hq]; exact hci
  rw [← hq] at hci
  have hdefn := decCI_defn hci (erecP_ext _) hS.erec
  rw [hfind'] at hrun1
  by_cases h1 : rdW (s.mem.arr64 EREC) (r₂.tail.headD 0) = 1
  · rw [hhEnv_defn (h := hc2) (h0 := h0) (h1 := h1)] at hW
    obtain ⟨cv, v, rfl, -, hk6⟩ := hdefn.1 h1
    exact hres _ _ hW (by unfold HW; omega) _ hrun1 rfl
  · rw [hhEnv_kind (h := hc2) (h0 := h0) (h1 := h1)] at hW
    rw [hintOf_none _ (fun cv v hint e => hdefn.2 h1 cv v hint (Option.some.inj e))] at hrun1
    exact hres 0 0 hW hw0 _ hrun1 rfl

/-! ## `hint_lt` -/

/-- The model of `hint_lt`: a pure word function. -/
def hintLtW (k1 h1 k2 h2 : Word) : Word :=
  if k2 = 0 then 0 else if k1 = 1 then 0 else if k1 = 0 then 1 else if k2 = 1 then 1
  else if h1 < h2 then 1 else 0

theorem hintLt_spec (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (k1 h1 k2 h2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "hint_lt" [k1, h1, k2, h2]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r.headD 0 = hintLtW k1 h1 k2 h2; ⊤⦄ := by
  rw [invoke_eq _ hp.hlt]
  simp only [callFn, hintLtL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
    finish [hintLtW]

theorem ite_bne (c : Prop) [Decidable c] : ((if c then (1 : Word) else 0) != 0) = decide c := by
  by_cases hc : c <;> simp [hc]

/-- `hint_lt`'s word function is `ReducibilityHint.lt` on the decoded hints. -/
theorem hintLtW_lt (k1 h1 k2 h2 : Word) :
    (hintLtW k1 h1 k2 h2 != 0) = (decHintW k1 h1).lt (decHintW k2 h2) := by
  unfold hintLtW decHintW
  by_cases a2 : k2 = 0 <;> by_cases a1 : k1 = 1 <;> by_cases b1 : k1 = 0 <;> by_cases b2 : k2 = 1 <;>
    simp_all [ConLeche.ReducibilityHint.lt] <;>
  simp only [ite_bne, UInt64.lt_iff_toNat_lt]

/-- **`hint_lt` refines `ReducibilityHint.lt`** on the decoded hints (a pure function: the memory
and the locals unchanged). -/
@[refines ConLeche.ReducibilityHint.lt]
theorem hintLt_refines (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (k1 h1 k2 h2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "hint_lt" [k1, h1, k2, h2]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      decBool r = (decHintW k1 h1).lt (decHintW k2 h2) ∧ ResH r; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hm, hloc, hr⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (hintLt_spec p hp n s₀ k1 h1 k2 h2)
  refine ⟨hm, hloc, by rw [decBool, hr, hintLtW_lt], ?_⟩
  unfold ResH; rw [hr]; unfold hintLtW
  repeat' split
  all_goals first | exact hw0 | exact hw1

/-! ## Level-list lengths -/

/-- **`ls_node`'s length word is the twin's `viewLen`** (when `ls_node` returns). -/
theorem lsNodeW_viewLen {m : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : HW h)
    (hne : lsNodeW m h ≠ []) :
    a.store.lss.viewLen (decI h) = some ((lsNodeW m h).tail.headD 0).toNat := by
  unfold lsNodeW at hne ⊢
  by_cases g0 : h >>> 28 ≠ 0
  · simp [g0] at hne
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [g0, hs] at hne
  by_cases hc : rdW (m.arr64 CTL) (40 + tierW h) ≤ idxW h
  · simp [g0, hs, hc] at hne
  simp only [g0, hs, hc, ↓reduceIte, List.tail_cons, List.headD_cons]
  have hi : idxW h < cntW lsSch m (tierW h) := by simpa [cntW, lsSch] using hc
  obtain ⟨x, hx, hrel⟩ := storeR_node lsSch LsRecRel lshash m _ _ _ hR.ls (tierW h) (tierW_le h)
    (idxW h) hi
  have hlen : x.us.length = (lsL m (tierW h) (idxW h)).toNat := by
    have := sliceL_length (m.arr64 POOL) (lsO m (tierW h) (idxW h)).toNat
      (lsL m (tierW h) (idxW h)).toNat
    rw [hrel.2.1] at this; simpa [lsWords] using this
  have hpers : (decI h : LsIdx).isPersistent = (tierW h == 0) := by
    rw [isPersistent_decI h hh]; rfl
  have htag : ((decI h : LsIdx).tag == LsTag.list) = true := by
    rw [decLs_tag0 h hh]; simpa using g0
  have hfl := hR.ls.2.1
  unfold LsStore.viewLen LsStore.persGetLen
  rw [hpers]
  by_cases ht : tierW h = 0
  · simp only [ht, ↓reduceIte] at hx
    simp only [ht, beq_self_eq_true, ↓reduceIte, LsTables.getLen, htag, Tbl.node?, decLs_idx, hx,
      Option.map_some, hlen]
  · simp only [ht, ↓reduceIte] at hx
    have hon : a.store.lss.scratchOn = true := by
      rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hs ⟨ht, h1⟩
    simp only [ht, beq_iff_eq, ↓reduceIte, hon, LsTables.getLen, htag, Tbl.node?, decLs_idx, hx,
      Option.map_some, hlen]

/-! ## `unfoldable_head`

The model binds each callee's run (`Option.bind` on the run, the continuation a named function of
the run's pair): no hypotheses for `grind` to instantiate. -/

/-- After `ls_node`: the list's length against the count at `EREC[q]` (read after the call). -/
def ufLsF (q : Word) (x : List Word × Mem) : Option (Word × Mem) :=
  some (if x.1.tail.headD 0 = rdW (x.2.arr64 EREC) q then 1 else 0, x.2)

/-- After `env_find`: a definition whose level-parameter count is the length of the list of the
head `hh` (read after the call, as the L code does). -/
def ufEnvF (p : Prog) (n : Nat) (hh : Word) (x : List Word × Mem) : Option (Word × Mem) :=
  if x.1.headD 0 = 0 then some (0, x.2)
  else if rdW (x.2.arr64 EREC) (x.1.tail.headD 0) ≠ 1 then some (0, x.2)
  else (callW p n "ls_node" [rdW (x.2.arr64 CREC) (idxW hh * 4 + tierW hh * 2 + 1)] x.2).bind
    (ufLsF (x.1.tail.headD 0 + 3))

/-- After `get_app_fn`: the head. -/
def ufHeadF (p : Prog) (n : Nat) (vis : Word) (x : List Word × Mem) : Option (Word × Mem) :=
  if x.1.headD 0 >>> 28 ≠ 3 then some (0, x.2)
  else if tierW (x.1.headD 0) ≠ 0 ∧ rdW (x.2.arr64 CTL) 1 = 0 then none
  else if rdW (x.2.arr64 CTL) (18 + tierW (x.1.headD 0)) ≤ idxW (x.1.headD 0) then none
  else (callW p n "env_find" [rdW (x.2.arr64 CREC) (idxW (x.1.headD 0) * 4 + tierW (x.1.headD 0) * 2),
      vis] x.2).bind (ufEnvF p n (x.1.headD 0))

/-- The model of `unfoldable_head`. -/
def unfoldableHeadW (p : Prog) (n : Nat) (m : Mem) (vis e : Word) : Option (Word × Mem) :=
  (callW p n "get_app_fn" [e] m).bind (ufHeadF p n vis)

theorem unfoldableHead_spec (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (vis e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "unfoldable_head" [vis, e]
    ⦃fun r s' => LocEq s' s₀ ∧ unfoldableHeadW p n s₀.mem vis e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ufh]
  simp only [callFn, unfoldableHeadL]
  sym only [lang_grind, arena_grind, defeq_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "ls_node"] <;>
    finish [unfoldableHeadW, ufHeadF, ufEnvF, ufLsF, Option.bind_some, tierW, idxW]

theorem toNat_beq (a b : Word) : (a.toNat == b.toNat) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · have : a.toNat ≠ b.toNat := fun e => h (UInt64.toNat_inj.mp e)
    simp [h, this]

theorem unfoldableHead_run_nonconst (fe : IFEnv) (e : EIdx) (a : AState) (hh : EIdx)
    (hgaf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = false) :
    (unfoldableHead fe e).run a = .ok (false, a) := by
  simp only [unfoldableHead, StateT.run_bind, hgaf, except_ok_bind, ht, Bool.false_eq_true,
    ↓reduceIte]
  rfl

theorem unfoldableHead_run_other (fe : IFEnv) (e : EIdx) (a : AState) (hh : EIdx) (c : NIdx)
    (us : LsIdx) (hgaf : (getAppFn coreWalkFuel e).run a = .ok (hh, a))
    (ht : (hh.tag == ETag.const) = true) (hv : a.store.view hh = some (.const c us))
    (hf : ∀ cv v hint, fe.find? c ≠ some (.defnInfo cv v hint)) :
    (unfoldableHead fe e).run a = .ok (false, a) := by
  simp only [unfoldableHead, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte,
    view_run _ _ _ hv]
  rcases hc : fe.find? c with _ | ⟨_ | ⟨cv, v, hint⟩ | _ | _ | _ | _ | _⟩ <;> try rfl
  all_goals exact absurd hc (hf cv v hint)

theorem unfoldableHead_run_defn (fe : IFEnv) (e : EIdx) (a : AState) (hh : EIdx) (c : NIdx)
    (us : LsIdx) (hgaf : (getAppFn coreWalkFuel e).run a = .ok (hh, a))
    (ht : (hh.tag == ETag.const) = true) (hv : a.store.view hh = some (.const c us))
    (cv : IConstantVal) (v : EIdx) (hint : ConLeche.ReducibilityHint)
    (hf : fe.find? c = some (.defnInfo cv v hint)) (k : Nat) (hl : a.store.lss.viewLen us = some k) :
    (unfoldableHead fe e).run a = .ok (k == cv.levelParams.length, a) := by
  simp only [unfoldableHead, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte,
    view_run _ _ _ hv, hf]
  simp [viewLsLen, StateT.run, hl, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure,
    get, getThe, MonadStateOf.get, StateT.get]

/-- **`unfoldable_head` refines `unfoldableHead`.** -/
@[refines ConRon.Arena.unfoldableHead]
theorem unfoldableHead_refines (p : Prog) (hp : DefEqLeafProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb e : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) :
    CoreSpec p (n + 1) "unfoldable_head" [vis, e] (unfoldableHead fe (decE e)) decBool s₀ a₀ dn vis
      fe MM eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (unfoldableHead_spec p hp n s₀ vis e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hR := hS.arena.1
  have hres : ∀ x : Word, some (x, s.mem) = some (r.headD 0, s'.mem) → HW x → ∀ v,
      (unfoldableHead fe (decE e)).run a₀ = .ok (v, a₀) → v = (x != 0) →
      CoreRef (unfoldableHead fe (decE e)) a₀ decBool dn s.mem vis fe MM eb r s'.mem := by
    intro x hxy hx v hv hvx
    simp only [Option.some.injEq, Prod.mk.injEq] at hxy
    obtain ⟨h1, h3⟩ := hxy
    rw [← h3]
    refine coreRef_pure hS hv ?_ ?_
    · rw [hvx, decBool, ← h1]
    · unfold ResH; rw [← h1]; exact hx
  unfold unfoldableHeadW at hW
  cases hc : callW p n "get_app_fn" [e] s.mem with
  | none => simp [hc] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc, Option.bind_some] at hW
  obtain ⟨rfl, hh, hgaf⟩ := getAppFn_callW hp hS.arena.1 he hc
  unfold ufHeadF at hW
  simp only at hW
  generalize r₁.headD 0 = h at hh hgaf hW
  rcases (Classical.em (h >>> 28 = 3)).symm with h3 | h3
  · simp only [ne_eq, h3, not_false_eq_true, ↓reduceIte] at hW
    exact hres 0 hW hw0 _
      (unfoldableHead_run_nonconst fe _ a₀ _ hgaf (by rw [tag_beq_const _ hh]; simp [h3])) rfl
  by_cases hs : tierW h ≠ 0 ∧ rdW (s.mem.arr64 CTL) 1 = 0
  · simp [h3, hs] at hW
  by_cases hcc : rdW (s.mem.arr64 CTL) (18 + tierW h) ≤ idxW h
  · simp [h3, hs, hcc] at hW
  simp only [h3, hs, hcc, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  have hvo : viewOK s.mem h 18 := ⟨hs, by simpa using hcc⟩
  obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s.mem a₀ hR h hh hvo h3
  have hct : ((decE h).tag == ETag.const) = true := by rw [tag_beq_const _ hh]; simp [h3]
  generalize rdW (s.mem.arr64 CREC) (idxW h * 4 + tierW h * 2) = k at hnw hW hv
  cases hc2 : callW p n "env_find" [k, vis] s.mem with
  | none => simp [hc2] at hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2, Option.bind_some] at hW
  obtain ⟨t₂, ht₂, hm₂, -, hfind⟩ := triple_of_callW
    (envFind_refines p hp.core.envix hp.core.envrow hp.core.envfind n s vis k hS.env hnw) hc2
  obtain ⟨t₂', ht₂', hm₂', -, hfound⟩ := triple_of_callW
    (envFind_found p hp.core.envix hp.core.envrow hp.core.envfind n s vis k hnw) hc2
  rw [ht₂] at hm₂
  subst hm₂
  unfold ufEnvF at hW
  simp only at hW
  by_cases h0 : r₂.headD 0 = 0
  · simp only [h0, ↓reduceIte] at hW
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [decFound, h0, ↓reduceIte]
    exact hres 0 hW hw0 _ (unfoldableHead_run_other fe _ a₀ _ _ _ hgaf hct hv
      (fun cv v hint e => by rw [hnone] at e; cases e)) rfl
  obtain ⟨htag, hrow, hq⟩ := hfound h0
  obtain ⟨ci, hci⟩ := hS.env.found_some k hnw htag hrow
  have hfind' : fe.find? (decI k) = some ci := by
    rw [hfind]; simp only [decFound, h0, ↓reduceIte, hq]; exact hci
  rw [← hq] at hci
  have hdefn := decCI_defn hci (erecP_ext _) hS.erec
  rcases (Classical.em (rdW (s.mem.arr64 EREC) (r₂.tail.headD 0) = 1)).symm with h1 | h1
  · simp only [h0, h1, ne_eq, not_false_eq_true, ↓reduceIte] at hW
    exact hres 0 hW hw0 _ (unfoldableHead_run_other fe _ a₀ _ _ _ hgaf hct hv
      (fun cv v hint e => hdefn.2 h1 cv v hint (by rw [hfind'] at e; exact Option.some.inj e))) rfl
  simp only [h0, h1, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  obtain ⟨cv, v, hci_eq, hlen, -⟩ := hdefn.1 h1
  cases hc3 : callW p n "ls_node" [rdW (s.mem.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1)] s.mem with
  | none => simp [hc3] at hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [hc3, Option.bind_some] at hW
  obtain ⟨t₃, ht₃, heq, hne, hr₃⟩ := triple_of_callW
    (lsNode_spec p hp.core.lsn n s (rdW (s.mem.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1))) hc3
  have hm₃ : m₃ = s.mem := by rw [← ht₃, heq]
  subst hm₃
  rw [hr₃] at hne
  have hvl := lsNodeW_viewLen hR huw hne
  rw [← hr₃] at hvl
  unfold ufLsF at hW
  simp only at hW
  have hrun := unfoldableHead_run_defn fe _ a₀ _ _ _ hgaf hct hv cv v _ (by rw [hfind', hci_eq]) _ hvl
  refine hres _ hW (by split <;> first | exact hw0 | exact hw1) _ hrun ?_
  rw [hlen, ite_bne, toNat_beq]

end L.Arena
