import ConAgua.Arena.DefEq
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.IndView

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

end L.Arena
