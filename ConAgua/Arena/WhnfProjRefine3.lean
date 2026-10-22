import ConAgua.Arena.WhnfProjRefine2
import ConAgua.Arena.DeclLvlStage
import ConAgua.Arena.Knot

/-!
# `fire_ok` refines `IProjEntry.fireOk` under `CoreS` (lane `whnf3`, helper `whnf3-proj`)

The table's `structSort` against the pinned zero level by the cached `lvl_eq_c`; at `some true`
the field's guard level through `field_sort_zero` (`FieldSortZeroOK`, lane `defeq`'s stub
statement, a hypothesis here). `lvl_eq_c` needs both levels to read back: **`ProjSortDen`**, a
named hypothesis (as `CoreS.lvl_den`: an invariant of the twin's store that `CoreS` does not
carry). The record pool is unchanged across `lvl_eq_c` by its write set from the text
(`lvlText_closed`, lane `decls3`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-- **A projection table's sort level and the pinned zero level read back** (assumed; the twin's
store is well formed and the environment loader interned the table's levels). -/
def ProjSortDen : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb q : Word) (tbl : IProjTable), CoreS dn m a vis fe M eb →
    decTbl (m.arr64 EREC) q.toNat = some tbl →
    (∃ l, denoteL a.store.ls tbl.structSort = some l) ∧
      (∃ l, denoteL a.store.ls a.pins.zeroLevel = some l)

/-- The lookups `fire_ok` needs. -/
structure FireProg (p : Prog) : Prop where
  fireOk : p.lookup "fire_ok" = some fireOkL
  pinw : p.lookup "pin_word" = some pinWordL
  lvl : LvlCacheProg p
  lvlText : ∀ f ∈ lvlFns, p.lookup f = cvgProg.lookup f

/-! ## The word model -/

/-- The guard word of field `i` (`0`, the `default` handle, past the list). -/
def foFs (m : Mem) (q i : Word) : Word :=
  if i < rdW (m.arr64 EREC) (q + 12) then rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (q + 11) + i) else 0

/-- The model of `fire_ok`. -/
def foW (p : Prog) (n : Nat) (m : Mem) (q i us : Word) : Option (Word × Mem) :=
  match callW p n "pin_word" [53] m with
  | none => none
  | some (z, m₁) =>
    match callW p n "lvl_eq_c" [rdW (m₁.arr64 EREC) (q + 8), z.headD 0] m₁ with
    | none => none
    | some (o, m₂) =>
      if o.headD 0 < 2 then some (1, m₂)
      else match callW p n "field_sort_zero" [rdW (m₂.arr64 EREC) (q + 3),
          rdW (m₂.arr64 EREC) (q + 4), us, foFs m₂ q i] m₂ with
        | none => none
        | some (r, m₃) => some (r.headD 0, m₃)

theorem fireOk_spec (p : Prog) (hp : FireProg p) (n : Nat) (s₀ : St) (q i us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "fire_ok" [q, i, us]
    ⦃fun r s' => LocEq s' s₀ ∧ foW p n s₀.mem q i us = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.fireOk]
  simp only [callFn, fireOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_word", callW_spec p n "lvl_eq_c", callW_spec p n "field_sort_zero"] <;>
    finish [foW, foFs]

/-! ## The table record's parts -/

theorem decTbl_parts {a : Array Word} {q : Nat} {tbl : IProjTable} (h : decTbl a q = some tbl) :
    hd? a (q + 8) = some tbl.structSort ∧ hlist? a (q + 3) = some tbl.levelParams ∧
      hlist? a (q + 11) = some tbl.guards := by
  simp only [decTbl, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, _, _, _, l3, h3, _, _, _, _, _, _, s8, h8, _, _, g, hg, _, _, rfl⟩ := h
  exact ⟨h8, h3, hg⟩

theorem hlist?_slice' {k : IdxKind} {a : Array Word} {i : Nat} {l : List (Idx k)}
    (h : hlist? a i = some l) :
    ∃ o c : Word, a[i]? = some o ∧ a[i+1]? = some c ∧ hslice? a o.toNat c.toNat = some l := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, c, hc, hs⟩ := h
  simp only [nat?, Option.map_eq_some_iff] at ho hc
  obtain ⟨wo, hwo, rfl⟩ := ho
  obtain ⟨wc, hwc, rfl⟩ := hc
  exact ⟨wo, wc, hwo, hwc, hs⟩

theorem except_ok_bind' {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

/-! ## The twin's run -/

theorem fireOk_run (e : IProjEntry) (us : LsIdx) (a a₂ : AState) (z : LIdx) (o : Option Bool)
    (hz : zeroLevel.run a = .ok (z, a)) (hl : (lvlEq? e.structSort z).run a = .ok (o, a₂)) :
    (e.fireOk us).run a =
      if o = some true then (fieldSortZeroT e.levelParams us e.fieldSort).run a₂ else .ok (true, a₂) := by
  simp only [IProjEntry.fireOk, StateT.run_bind, hz, except_ok_bind', hl]
  by_cases ho : o = some true
  · subst ho; simp only [ite_true, fieldSortZeroT, StateT.run_bind]; rfl
  · simp only [ho, ite_false]
    have : (!(o == some true)) = true := by cases o with
      | none => rfl
      | some b => cases b <;> simp_all
    simp only [this, ite_true]; rfl

end L.Arena
