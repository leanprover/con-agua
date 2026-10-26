import ConAgua.Arena.StrLitCv
import ConAgua.Arena.DefEqMidQuick

/-!
# The string-support declaration tests under `CoreS` (helper `defeq2-str`)

`string_ty_ok`/`char_ty_ok`, `list_ty_ok` (and the shared pieces: `str_param_sort`, the `∀`-type
comparison tail `faEqW`/`faEqT`), each as a `callW` run refining its twin at the decoded record.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace L.Arena

/-- A refinement post from the twin's run and the relation after it. -/
theorem cref_run {α : Type} [Inhabited α] {T : AM α} {a a' : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} {v : α}
    (hrun : T.run a = .ok (v, a')) (hA : CoreAfter dn m m' a' vis fe M eb) (hv : v = dec r)
    (hok : ok r) : CoreRef T a dec dn m vis fe M eb r m' ok := by
  obtain ⟨h1, h2, h3⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨h1, by rw [h2]; exact hA, by rw [h3, hv], hok⟩

theorem coreAfter_refl {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) :
    CoreAfter dn m m a vis fe M eb := ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩

theorem resH_ite01 (c : Prop) [Decidable c] : ResH [if c then 1 else 0] := by
  unfold ResH HW; split <;> decide

/-! ## The `∀`-type comparison tail -/

/-- The twins' tail: `ty` is `∀ (_ : X), Y`. -/
def faEqT (ty X Y : EIdx) : AM Bool :=
  if ty.tag == ETag.forallE then do
    match ← view ty with
    | .forallE d b => pure (d == X && b == Y)
    | _ => pure false
  else pure false

/-- The L code's tail: the tag test, `e_view`, the comparison. -/
def faEqW (p : Prog) (n : Nat) (m : Mem) (ty X Y : Word) : Option (Word × Mem) :=
  if ty >>> 28 ≠ 6 then some (0, m)
  else match callW p n "e_view" [ty] m with
    | none => none
    | some (g, m₁) =>
      some (if g.tail.headD 0 = X ∧ g.tail.tail.headD 0 = Y then 1 else 0, m₁)

theorem faEqW_ok {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat} {m m' : Mem}
    {a : AState} (hR : ArenaR m a) {ty X Y w : Word} (hty : HW ty) (hX : HW X) (hY : HW Y)
    (h : faEqW p n m ty X Y = some (w, m')) :
    (faEqT (decI ty) (decE X) (decE Y)).run a = .ok (w != 0, a) ∧ m' = m ∧ ResH [w] := by
  unfold faEqW at h
  by_cases g6 : ty >>> 28 ≠ 6
  · rw [if_pos g6] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ht : ((decI ty : EIdx).tag == ETag.forallE) = false := by
      cases hb : ((decI ty : EIdx).tag == ETag.forallE)
      · rfl
      · exact absurd ((decE_tag_forall ty hty).mp (beq_iff_eq.mp hb)) g6
    refine ⟨?_, rfl, by unfold ResH HW; decide⟩
    simp only [faEqT, ht]; rfl
  rw [if_neg g6] at h
  have g6' : ty >>> 28 = 6 := by simpa using g6
  cases hc : callW p n "e_view" [ty] m with
  | none => rw [hc] at h; cases h
  | some q =>
  obtain ⟨g, m₁⟩ := q
  rw [hc] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨rfl, v, hv, hvr, hg⟩ := eView_callW_view hp hR hc
  obtain ⟨rfl, h1, h2⟩ := viewR_forall hvr (by rw [hg, g6'])
  have ht : ((decI ty : EIdx).tag == ETag.forallE) = true :=
    beq_iff_eq.mpr ((decE_tag_forall ty hty).mpr g6')
  refine ⟨?_, rfl, resH_ite01 _⟩
  rw [decE_eq] at hv
  simp only [faEqT, ht, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  show Except.ok _ = _
  congr 1
  simp only [Prod.mk.injEq, and_true]
  rw [decE_eq, decE_eq, decE_eq, decE_eq, decI_beq _ _ h1 hX, decI_beq _ _ h2 hY]
  have e : ((if g.tail.headD 0 = X ∧ g.tail.tail.headD 0 = Y then (1 : Word) else 0) != 0) =
      (decide (g.tail.headD 0 = X) && decide (g.tail.tail.headD 0 = Y)) := by
    by_cases c1 : g.tail.headD 0 = X <;> by_cases c2 : g.tail.tail.headD 0 = Y
    · rw [if_pos ⟨c1, c2⟩, decide_eq_true c1, decide_eq_true c2]; rfl
    · rw [if_neg (fun h => c2 h.2), decide_eq_true c1, decide_eq_false c2]; rfl
    · rw [if_neg (fun h => c1 h.1), decide_eq_false c1]; rfl
    · rw [if_neg (fun h => c1 h.1), decide_eq_false c1]; rfl
  rw [e]

/-! ## `string_ty_ok`, `char_ty_ok` -/

/-- The model of `string_ty_ok` (and `char_ty_ok`). -/
def sTyW (p : Prog) (n : Nat) (m : Mem) (found q : Word) : Option (Word × Mem) :=
  if found = 0 then some (0, m)
  else match callW p n "str_cv" [q] m with
    | none => none
    | some (c, m₁) =>
      match callW p n "pin_word" [54] m₁ with
      | none => none
      | some (s, m₂) =>
        some (if c.tail.headD 0 = 0 ∧ c.tail.tail.headD 0 = s.headD 0 then 1 else 0, m₂)

theorem sTy_spec (p : Prog) (f : FnName) (hp : p.lookup f = some stringTyOkL) (n : Nat) (s₀ : St)
    (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) f [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ sTyW p n s₀.mem found q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, stringTyOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "str_cv", callW_spec p n "pin_word"] <;>
    finish [sTyW]

theorem charTyOk_eq : charTyOk = stringTyOk := by
  funext x; cases x <;> rfl

section calls
variable (p : Prog) (hp : StrLitProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
  {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
include hp

/-- **`string_ty_ok` (at any name bound to its body) refines `stringTyOk`.** -/
theorem sTy_call (f : FnName) (hf : p.lookup f = some stringTyOkL)
    (hS : CoreS dn m a vis fe M eb) {found q : Word}
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP m) dn q.toNat = some ci)
    (h : callW p n f [found, q] m = some (r, m')) :
    CoreRef (stringTyOk (decFound dn m found q)) a decBool dn m vis fe M eb r m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (sTy_spec p f hf n _ found q) h
  unfold sTyW at hW
  by_cases hf0 : found = 0
  · rw [if_pos hf0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    simp only [decFound, hf0, ↓reduceIte]
    exact cref_run (v := false) rfl (coreAfter_refl hS) (by rw [decBool, ← hr]; rfl)
      (by unfold ResH HW; rw [← hr]; decide)
  rw [if_neg hf0] at hW
  obtain ⟨ci, hci⟩ := hdec hf0
  have hdf : decFound dn m found q = some ci := by simp only [decFound, hf0, ↓reduceIte, hci]
  rw [hdf]
  cases h1 : callW p n "str_cv" [q] m with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨c, m₁⟩ := q₁
  rw [h1] at hW; dsimp only at hW
  obtain ⟨hm₁, -, hlen, hty, hhw⟩ := cv_call p hp hS hci h1
  subst m₁
  generalize hcv : ci.toConstantVal = cv at hlen hty
  cases h2 : callW p n "pin_word" [54] m with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨s, m₂⟩ := q₂
  rw [h2] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [← hm]
  obtain ⟨hm21, -, hs⟩ := callW_pinWord p hp.pinWord n m 54 s m₂ h2
  rw [hm21]
  have hs' : s.headD 0 = pinW m 54 := hs
  have hpw : HW (pinW m 54) := hS.pins.lv_lt.2.2
  have hrun' : (stringTyOk (some ci)).run a =
      .ok (cv.levelParams.isEmpty && cv.type == decI (pinW m 54), a) := by
    simp only [stringTyOk, hcv, StateT.run_bind, except_ok_bind, sortOne,
      pinSortOne_run hS.pins]; rfl
  refine cref_run hrun' (coreAfter_refl hS) ?_ (by unfold ResH; rw [← hr]; exact resH_ite01 _)
  have hb : decBool r = decide (c.tail.headD 0 = 0 ∧ c.tail.tail.headD 0 = s.headD 0) := by
    unfold decBool; rw [← hr]; split <;> simp_all
  rw [hb, hty, decI_beq _ _ hhw hpw, ← hs']
  have : cv.levelParams.isEmpty = decide (c.tail.headD 0 = 0) := by
    rcases hl : cv.levelParams with _ | ⟨x, xs⟩
    · rw [hl] at hlen; simp only [List.length_nil] at hlen
      simp only [List.isEmpty_nil]
      exact (decide_eq_true (UInt64.toNat_inj.mp (by rw [← hlen]; rfl))).symm
    · rw [hl] at hlen; simp only [List.length_cons] at hlen
      simp only [List.isEmpty_cons]
      refine (decide_eq_false fun h0 => ?_).symm
      rw [h0] at hlen; simp at hlen
  rw [this]
  by_cases c1 : c.tail.headD 0 = 0 <;> by_cases c2 : c.tail.tail.headD 0 = s.headD 0 <;> simp [c1, c2]

/-- **`string_ty_ok` refines `stringTyOk`.** -/
@[refines ConRon.Arena.stringTyOk]
theorem stringTyOk_call (hS : CoreS dn m a vis fe M eb) {found q : Word}
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP m) dn q.toNat = some ci)
    (h : callW p n "string_ty_ok" [found, q] m = some (r, m')) :
    CoreRef (stringTyOk (decFound dn m found q)) a decBool dn m vis fe M eb r m' :=
  sTy_call p hp "string_ty_ok" hp.stringTyOk hS hdec h

/-- **`char_ty_ok` refines `charTyOk`.** -/
@[refines ConRon.Arena.charTyOk]
theorem charTyOk_call (hS : CoreS dn m a vis fe M eb) {found q : Word}
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP m) dn q.toNat = some ci)
    (h : callW p n "char_ty_ok" [found, q] m = some (r, m')) :
    CoreRef (charTyOk (decFound dn m found q)) a decBool dn m vis fe M eb r m' := by
  rw [charTyOk_eq]; exact sTy_call p hp "char_ty_ok" hp.charTyOk hS hdec h

end calls

end L.Arena
