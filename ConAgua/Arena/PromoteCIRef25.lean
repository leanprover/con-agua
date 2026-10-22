import ConAgua.Arena.PromoteCIRef24

/-!
# The constants list as a recursion on positions; the environment relation after a promotion
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The first `j` constants (positions `j - 1, …, 0`, newest first), decoded. -/
def cdec (dn : NIdx → Option ConLeche.Name) (A E : Array Word) : Nat → Option (List IConstantInfo)
  | 0 => some []
  | j + 1 => (nat? E j).bind fun p => (decCI A dn p).bind fun x =>
      (cdec dn A E j).bind fun xs => some (x :: xs)

theorem envConsts_eq (dn : NIdx → Option ConLeche.Name) (m : Mem) :
    envConsts dn m = cdec dn (erecP m) (m.arr64 ECON) (envLen m) := by
  unfold envConsts
  generalize envLen m = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.mapM_cons, ih]
    simp [cdec, Option.bind_eq_bind, Option.bind_assoc]

theorem cdec_mono {dn : NIdx → Option ConLeche.Name} {A A' E E' : Array Word} (hA : ArrExt A A') :
    ∀ (j : Nat) (B : List IConstantInfo), (∀ i, i < j → E'[i]? = E[i]?) →
    cdec dn A E j = some B → cdec dn A' E' j = some B
  | 0, B, _, h => h
  | j + 1, B, hE, h => by
    simp only [cdec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h ⊢
    obtain ⟨p, hp, x, hx, xs, hxs, rfl⟩ := h
    refine ⟨p, ?_, x, hA.decCI hx, xs, cdec_mono hA j xs (fun i hi => hE i (by omega)) hxs, rfl⟩
    obtain ⟨w, hw, rfl⟩ := nat?_get hp
    simp [L.Arena.nat?, hE j (by omega), hw]

theorem cdec_join {dn : NIdx → Option ConLeche.Name} {A E : Array Word} :
    ∀ (L : List IConstantInfo) (j : Nat) (B : List IConstantInfo),
    ConstsAt dn A E (j + L.length - 1) L → cdec dn A E j = some B →
    cdec dn A E (j + L.length) = some (L ++ B)
  | [], j, B, _, h => by simpa using h
  | ci :: L, j, B, ⟨⟨ptr, hp, hd⟩, hrest⟩, h => by
    have ih := cdec_join L j B (by
      have : j + (ci :: L).length - 1 - 1 = j + L.length - 1 := by simp only [List.length_cons]; omega
      rw [← this]; exact hrest) h
    have e : j + (ci :: L).length = (j + L.length) + 1 := by simp only [List.length_cons]; omega
    rw [e]
    simp only [cdec, Option.bind_eq_bind, ih, Option.bind_some]
    have e2 : j + (ci :: L).length - 1 = j + L.length := by simp only [List.length_cons]; omega
    rw [e2] at hp
    simp [nat?, hp, hd]

theorem cdec_split {dn : NIdx → Option ConLeche.Name} {A E : Array Word} :
    ∀ (c j : Nat) (cs : List IConstantInfo), cdec dn A E (j + c) = some cs →
    ∃ L B, cs = L ++ B ∧ L.length = c ∧ ConstsAt dn A E (j + c - 1) L ∧ cdec dn A E j = some B
  | 0, j, cs, h => ⟨[], cs, by simpa using h.symm ▸ rfl, rfl, trivial, by simpa using h⟩
  | c + 1, j, cs, h => by
    have e : j + (c + 1) = (j + c) + 1 := by omega
    rw [e] at h
    simp only [cdec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨p, hp, x, hx, xs, hxs, rfl⟩ := h
    obtain ⟨L, B, hxsL, hL, hC, hB⟩ := cdec_split c j xs hxs
    obtain ⟨w, hw, rfl⟩ := nat?_get hp
    refine ⟨x :: L, B, by simp [hxsL], by simp [hL], ?_, hB⟩
    refine ⟨⟨w, hw, hx⟩, ?_⟩
    have : j + (c + 1) - 1 - 1 = j + c - 1 := by omega
    rw [this]; exact hC

end L.Arena
