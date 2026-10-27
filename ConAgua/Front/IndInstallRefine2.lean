import ConAgua.Front.IndInstallRefine
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `install_ind_d` refines `installIndD`, II: the type and constructor records

`typeW_twin`, `ctorRW_twin`: `ind_type`/`ind_ctor` allocate a record above `DLP`'s top and write
it; it decodes (`decCI`) as the twin's `indInfo`/`ctorInfo` constant in any pool that agrees with
the memory from the record on (`RecAt`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec CVRec RuleRec)
open ConAgua.Front.FieldsLink
open L.Front.Fields (listN itemsN)


namespace L.Front.Ind

/-- The value of a twin computation that runs `.ok` (else `default`). -/
def resOf {α : Type} [Inhabited α] (x : AM α) (a : AState) : α :=
  match x.run a with
  | .ok (c, _) => c
  | .error _ => default

theorem resOf_eq {α : Type} [Inhabited α] {x : AM α} {a a' : AState} {c : α}
    (h : x.run a = .ok (c, a')) : resOf x a = c := by
  simp [resOf, h]

/-- **The constant record at `q`** decodes as `ci` in every pool that holds `m`'s words from `q`
to the top. -/
def RecAt (m : Mem) (q : Nat) (ci : IConstantInfo) : Prop :=
  ∀ P, AgreesFrom P m q → decCI P (fun _ => none) q = some ci

theorem RecAt.keep {m m' : Mem} {q : Nat} {ci : IConstantInfo} (h : RecAt m q ci)
    (ht : topN m DLP ≤ topN m' DLP) (hk : ∀ i, q ≤ i → i ≤ topN m DLP → wd m' DLP i = wd m DLP i) :
    RecAt m' q ci :=
  fun P hP => h P (fun i h1 h2 => by rw [hP i h1 (Nat.le_trans h2 ht), hk i h1 h2])

theorem wd_set_ne (m : Mem) (A : ArrId) (i v : Word) (j : Nat) (h : i.toNat ≠ j) :
    wd (m.set64 A i v) A j = wd m A j := by
  rw [wd_setA]; simp [h]

theorem wd_set_eq (m : Mem) (A : ArrId) (i v : Word) (j : Nat) (h : i.toNat = j)
    (hs : j < (m.arr64 A).size) : wd (m.set64 A i v) A j = v := by
  rw [wd_setA]; simp [h, hs]

theorem range_map_eq {α β : Type} (l : List α) (f : Nat → β) (g : α → β)
    (h : ∀ j (hj : j < l.length), f j = g l[j]) : (List.range l.length).map f = l.map g := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]; exact h j h1

/-- A pool agreeing with `m` from `q` holds word `i` (in range). -/
theorem AgreesFrom.get {P : Array Word} {m : Mem} {q : Nat} (h : AgreesFrom P m q) {i : Nat}
    (h1 : q ≤ i) (h2 : i ≤ topN m DLP) : P[i]? = some (wd m DLP i) := h i h1 h2

/-! ## The capabilities -/

/-- `ind_caps`' fifteen words decode as the default capabilities. -/
theorem capsM_dec (m : Mem) (q : Word) (hs : q.toNat + 15 ≤ (m.arr64 DLP).size) (hq : q.toNat + 15 < 2 ^ 64)
    (P : Array Word) (dn : NIdx → Option ConLeche.Name)
    (h : ∀ k, k < 15 → P[q.toNat + k]? = some (wd (capsM m q) DLP (q.toNat + k))) :
    decCaps P dn q.toNat = some {} := by
  have h0 := h 0 (by decide)
  simp only [Nat.add_zero] at h0
  have v0 : wd (capsM m q) DLP q.toNat = 0 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ q.toNat (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ q.toNat (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ q.toNat (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 11) _ q.toNat (by rw [widx2 q 11 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 10) _ q.toNat (by rw [widx2 q 10 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 9) _ q.toNat (by rw [widx2 q 9 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 8) _ q.toNat (by rw [widx2 q 8 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 7) _ q.toNat (by rw [widx2 q 7 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 6) _ q.toNat (by rw [widx2 q 6 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 5) _ q.toNat (by rw [widx2 q 5 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 4) _ q.toNat (by rw [widx2 q 4 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 3) _ q.toNat (by rw [widx2 q 3 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 2) _ q.toNat (by rw [widx2 q 2 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 1) _ q.toNat (by rw [widx2 q 1 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP q _ q.toNat rfl]; omega
  rw [v0] at h0
  have h1 := h 1 (by decide)
  have v1 : wd (capsM m q) DLP (q.toNat + 1) = 0 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ (q.toNat + 1) (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ (q.toNat + 1) (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ (q.toNat + 1) (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 11) _ (q.toNat + 1) (by rw [widx2 q 11 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 10) _ (q.toNat + 1) (by rw [widx2 q 10 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 9) _ (q.toNat + 1) (by rw [widx2 q 9 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 8) _ (q.toNat + 1) (by rw [widx2 q 8 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 7) _ (q.toNat + 1) (by rw [widx2 q 7 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 6) _ (q.toNat + 1) (by rw [widx2 q 6 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 5) _ (q.toNat + 1) (by rw [widx2 q 5 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 4) _ (q.toNat + 1) (by rw [widx2 q 4 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 3) _ (q.toNat + 1) (by rw [widx2 q 3 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 2) _ (q.toNat + 1) (by rw [widx2 q 2 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP (q + 1) _ (q.toNat + 1) (by rw [widx2 q 1 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v1] at h1
  have h2 := h 2 (by decide)
  have v2 : wd (capsM m q) DLP (q.toNat + 2) = 0 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ (q.toNat + 2) (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ (q.toNat + 2) (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ (q.toNat + 2) (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 11) _ (q.toNat + 2) (by rw [widx2 q 11 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 10) _ (q.toNat + 2) (by rw [widx2 q 10 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 9) _ (q.toNat + 2) (by rw [widx2 q 9 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 8) _ (q.toNat + 2) (by rw [widx2 q 8 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 7) _ (q.toNat + 2) (by rw [widx2 q 7 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 6) _ (q.toNat + 2) (by rw [widx2 q 6 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 5) _ (q.toNat + 2) (by rw [widx2 q 5 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 4) _ (q.toNat + 2) (by rw [widx2 q 4 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 3) _ (q.toNat + 2) (by rw [widx2 q 3 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP (q + 2) _ (q.toNat + 2) (by rw [widx2 q 2 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v2] at h2
  have h3 := h 3 (by decide)
  have v3 : wd (capsM m q) DLP (q.toNat + 3) = 0 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ (q.toNat + 3) (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ (q.toNat + 3) (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ (q.toNat + 3) (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 11) _ (q.toNat + 3) (by rw [widx2 q 11 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 10) _ (q.toNat + 3) (by rw [widx2 q 10 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 9) _ (q.toNat + 3) (by rw [widx2 q 9 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 8) _ (q.toNat + 3) (by rw [widx2 q 8 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 7) _ (q.toNat + 3) (by rw [widx2 q 7 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 6) _ (q.toNat + 3) (by rw [widx2 q 6 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 5) _ (q.toNat + 3) (by rw [widx2 q 5 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 4) _ (q.toNat + 3) (by rw [widx2 q 4 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP (q + 3) _ (q.toNat + 3) (by rw [widx2 q 3 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v3] at h3
  have h4 := h 4 (by decide)
  have v4 : wd (capsM m q) DLP (q.toNat + 4) = 0 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ (q.toNat + 4) (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ (q.toNat + 4) (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ (q.toNat + 4) (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 11) _ (q.toNat + 4) (by rw [widx2 q 11 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 10) _ (q.toNat + 4) (by rw [widx2 q 10 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 9) _ (q.toNat + 4) (by rw [widx2 q 9 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 8) _ (q.toNat + 4) (by rw [widx2 q 8 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 7) _ (q.toNat + 4) (by rw [widx2 q 7 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 6) _ (q.toNat + 4) (by rw [widx2 q 6 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 5) _ (q.toNat + 4) (by rw [widx2 q 5 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP (q + 4) _ (q.toNat + 4) (by rw [widx2 q 4 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v4] at h4
  have h5 := h 5 (by decide)
  have v5 : wd (capsM m q) DLP (q.toNat + 5) = 0 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ (q.toNat + 5) (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ (q.toNat + 5) (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ (q.toNat + 5) (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 11) _ (q.toNat + 5) (by rw [widx2 q 11 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 10) _ (q.toNat + 5) (by rw [widx2 q 10 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 9) _ (q.toNat + 5) (by rw [widx2 q 9 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 8) _ (q.toNat + 5) (by rw [widx2 q 8 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 7) _ (q.toNat + 5) (by rw [widx2 q 7 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 6) _ (q.toNat + 5) (by rw [widx2 q 6 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP (q + 5) _ (q.toNat + 5) (by rw [widx2 q 5 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v5] at h5
  have h6 := h 6 (by decide)
  have v6 : wd (capsM m q) DLP (q.toNat + 6) = 0 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ (q.toNat + 6) (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ (q.toNat + 6) (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ (q.toNat + 6) (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 11) _ (q.toNat + 6) (by rw [widx2 q 11 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 10) _ (q.toNat + 6) (by rw [widx2 q 10 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 9) _ (q.toNat + 6) (by rw [widx2 q 9 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 8) _ (q.toNat + 6) (by rw [widx2 q 8 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 7) _ (q.toNat + 6) (by rw [widx2 q 7 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP (q + 6) _ (q.toNat + 6) (by rw [widx2 q 6 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v6] at h6
  have h7 := h 7 (by decide)
  have v7 : wd (capsM m q) DLP (q.toNat + 7) = 1 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ (q.toNat + 7) (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ (q.toNat + 7) (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ (q.toNat + 7) (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 11) _ (q.toNat + 7) (by rw [widx2 q 11 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 10) _ (q.toNat + 7) (by rw [widx2 q 10 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 9) _ (q.toNat + 7) (by rw [widx2 q 9 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 8) _ (q.toNat + 7) (by rw [widx2 q 8 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP (q + 7) _ (q.toNat + 7) (by rw [widx2 q 7 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v7] at h7
  have h8 := h 8 (by decide)
  have v8 : wd (capsM m q) DLP (q.toNat + 8) = 0 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ (q.toNat + 8) (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ (q.toNat + 8) (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ (q.toNat + 8) (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 11) _ (q.toNat + 8) (by rw [widx2 q 11 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 10) _ (q.toNat + 8) (by rw [widx2 q 10 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 9) _ (q.toNat + 8) (by rw [widx2 q 9 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP (q + 8) _ (q.toNat + 8) (by rw [widx2 q 8 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v8] at h8
  have h9 := h 9 (by decide)
  have v9 : wd (capsM m q) DLP (q.toNat + 9) = 0 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ (q.toNat + 9) (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ (q.toNat + 9) (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ (q.toNat + 9) (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 11) _ (q.toNat + 9) (by rw [widx2 q 11 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 10) _ (q.toNat + 9) (by rw [widx2 q 10 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP (q + 9) _ (q.toNat + 9) (by rw [widx2 q 9 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v9] at h9
  have h10 := h 10 (by decide)
  have v10 : wd (capsM m q) DLP (q.toNat + 10) = 0 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ (q.toNat + 10) (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ (q.toNat + 10) (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ (q.toNat + 10) (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 11) _ (q.toNat + 10) (by rw [widx2 q 11 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP (q + 10) _ (q.toNat + 10) (by rw [widx2 q 10 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v10] at h10
  have h11 := h 11 (by decide)
  have v11 : wd (capsM m q) DLP (q.toNat + 11) = 0 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ (q.toNat + 11) (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ (q.toNat + 11) (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ (q.toNat + 11) (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP (q + 11) _ (q.toNat + 11) (by rw [widx2 q 11 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v11] at h11
  have h12 := h 12 (by decide)
  have v12 : wd (capsM m q) DLP (q.toNat + 12) = 0 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ (q.toNat + 12) (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ (q.toNat + 12) (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP (q + 12) _ (q.toNat + 12) (by rw [widx2 q 12 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v12] at h12
  have h13 := h 13 (by decide)
  have v13 : wd (capsM m q) DLP (q.toNat + 13) = 0 := by
    unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ (q.toNat + 13) (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_eq _ DLP (q + 13) _ (q.toNat + 13) (by rw [widx2 q 13 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v13] at h13
  have h14 := h 14 (by decide)
  have v14 : wd (capsM m q) DLP (q.toNat + 14) = 0 := by
    unfold capsM; rw [wd_set_eq _ DLP (q + 14) _ (q.toNat + 14) (by rw [widx2 q 14 (by simp; omega)]; rfl)]; simp only [size_set64]; omega
  rw [v14] at h14
  simp [decCaps, bool?, hd?, nat?, decPW, hlist?, hslice?, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  rfl

/-- `ind_caps` writes only its fifteen words. -/
theorem capsM_out (m : Mem) (q : Word) (hq : q.toNat + 15 < 2 ^ 64) (j : Nat)
    (hj : j < q.toNat ∨ q.toNat + 15 ≤ j) : wd (capsM m q) DLP j = wd m DLP j := by
  unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ j (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ j (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ j (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 11) _ j (by rw [widx2 q 11 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 10) _ j (by rw [widx2 q 10 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 9) _ j (by rw [widx2 q 9 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 8) _ j (by rw [widx2 q 8 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 7) _ j (by rw [widx2 q 7 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 6) _ j (by rw [widx2 q 6 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 5) _ j (by rw [widx2 q 5 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 4) _ j (by rw [widx2 q 4 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 3) _ j (by rw [widx2 q 3 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 2) _ j (by rw [widx2 q 2 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 1) _ j (by rw [widx2 q 1 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP q _ j (by omega)]

theorem capsM_frame (m : Mem) (q : Word) : MemFrame [DLP] [] m (capsM m q) := by
  unfold capsM
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  exact MemFrame.set64 _ DLP (by decide) _ _

theorem capsM_size (m : Mem) (q : Word) : ((capsM m q).arr64 DLP).size = (m.arr64 DLP).size :=
  (capsM_frame m q).2.2.1 DLP

/-! ## The type and constructor records -/

/-- The twin's constant of a type record (`installIndD`'s `types`). -/
def tyT (st : StateD) (t : IndTypeRec) : AM IConstantInfo := do
  pure (IConstantInfo.indInfo (← parseCVD st t.cv) {})

/-- The twin's constant of a constructor record (`installIndD`'s `ctors`). -/
def ctT (st : StateD) (c : IndCtorRec) : AM IConstantInfo := do
  pure (IConstantInfo.ctorInfo (← parseCVD st c.cv) c.numParams c.numFields)

theorem rdW_wdI (m : Mem) (A : ArrId) (t w : Word) (h : t.toNat + w.toNat < 2 ^ 64) :
    rdW (m.arr64 A) (t + w) = wd m A (t.toNat + w.toNat) := by
  simp only [rdW, wd, widx2 t w h]

/-- **`ind_type` against the twin's type constant.** -/
theorem typeW_twin {b : ByteArray} {m m' : Mem} {st : StateD} (a : AState) (hD : LkR m st)
    {t q : Word} {ty : IndTypeRec} (hF : CVF b m t.toNat ty.cv) (ht : t.toNat + 3 < 2 ^ 63)
    (h : typeW b.data m t = some (q, m')) :
    (tyT st ty).run a = .ok (resOf (tyT st ty) a, a) ∧ PExt m m' ∧ q.toNat = topN m DLP + 1 ∧
      LkR m' st ∧ RecAt m' q.toNat (resOf (tyT st ty) a) := by
  have hps := hD.psize
  have hpt := hD.ptop
  unfold typeW at h
  rcases h1 : allocW m DLP 20 with _ | ⟨q1, m₁⟩ <;> rw [h1] at h
  · cases h
  simp only [allocK] at h
  obtain ⟨P1, P2, P3, P4, P5⟩ := allocP_facts hD.psize hD.ptop h1
  simp only [show (20 : Word).toNat = 20 from rfl] at P3 P4
  have hifr : m₁.arr64 IFR = m.arr64 IFR := P1.other IFR (by decide) (by decide)
  have hsm1 : (m₁.arr64 DLP).size = (m.arr64 DLP).size := P1.size DLP
  cases h2 : cvW b.data (m₁.set64 DLP q1 3) (q1 + 1) (rdW (m₁.arr64 IFR) t) (rdW (m₁.arr64 IFR) (t + 1))
      (rdW (m₁.arr64 IFR) (t + 2)) with
  | none => rw [h2] at h; cases h
  | some m₂ =>
  rw [h2] at h; simp only [mK, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have Pq : PExt m (m₁.set64 DLP q1 3) := P1.set q1 3 (by omega) (by omega)
  have hs1 : ((m₁.set64 DLP q1 3).arr64 DLP).size = (m.arr64 DLP).size := Pq.size DLP
  have ht1 : topN (m₁.set64 DLP q1 3) DLP = topN m DLP + 20 := by
    rw [← P3]; unfold topN; rw [wd_set_ne _ _ _ _ _ (by omega)]
  have hL1 : LkR (m₁.set64 DLP q1 3) st := hD.frame Pq.frame (by rw [ht1, hs1]; omega)
  obtain ⟨n0, l0, y0⟩ := hF
  have r0 : rdW (m₁.arr64 IFR) t = wd m IFR t.toNat := by rw [hifr]; rfl
  have r1 : rdW (m₁.arr64 IFR) (t + 1) = wd m IFR (t.toNat + 1) := by
    rw [hifr, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  have r2 : rdW (m₁.arr64 IFR) (t + 2) = wd m IFR (t.toNat + 2) := by
    rw [hifr, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  rw [r0, r1, r2] at h2
  have hq1 : (q1 + 1).toNat = q1.toNat + 1 := widx2 _ _ (by simp; omega)
  obtain ⟨cvp, C1, C2, C3, C3', C4, C5, C6⟩ :=
    cvW_facts a hL1 n0.1 y0.1 l0 (by omega) (by rw [hq1, ht1]; omega) h2
  have hrun : (tyT st ty).run a = .ok (.indInfo cvp {}, a) := by
    unfold tyT; rw [run_bind _ _ a _ C1]; rfl
  rw [resOf_eq hrun]
  have hs2 : (m₂.arr64 DLP).size = (m.arr64 DLP).size := by rw [C2.2.2.1 DLP, hs1]
  have ht2 : topN m₂ DLP = topN m DLP + 20 + ty.cv.levelParams.length := by rw [C3, ht1]
  have hq5 : (q1 + 5).toNat = q1.toNat + 5 := widx2 _ _ (by simp; omega)
  have hc0 : ∀ i, (i < q1.toNat + 5 ∨ q1.toNat + 20 ≤ i) → wd (capsM m₂ (q1 + 5)) DLP i = wd m₂ DLP i :=
    fun i hi => capsM_out _ _ (by omega) i (by omega)
  have ht3 : topN (capsM m₂ (q1 + 5)) DLP = topN m₂ DLP := by
    unfold topN; rw [hc0 0 (by omega)]
  refine ⟨hrun, ⟨Pq.frame.trans (C2.trans (capsM_frame _ _)), by rw [ht3, ht2]; omega,
    fun i h1 h2 => ?_⟩, P2, ?_, ?_⟩
  · rw [hc0 i (by omega), C4 i h1 (by omega), Pq.keep i h1 h2]
  · exact hD.frame (Pq.frame.trans (C2.trans (capsM_frame _ _)))
      (by rw [ht3, capsM_size]; exact C3')
  · intro P hP
    have g0 : P[q1.toNat]? = some 3 := by
      rw [hP.get (Nat.le_refl _) (by rw [ht3, ht2]; omega), hc0 _ (by omega),
        C4 _ (by omega) (by omega), wd_set_eq _ _ _ _ _ rfl (by omega)]
    have gcv : decCV P (q1.toNat + 1) = some cvp := by
      rw [← hq1]
      exact C6 P (fun i hi => by
        rw [hP.get (by omega) (by rw [ht3, ht2]; omega), hc0 i (by omega)])
    have gcaps : decCaps P (fun _ => none) (q1.toNat + 5) = some {} := by
      rw [← hq5]
      exact capsM_dec m₂ (q1 + 5) (by rw [hs2]; omega) (by omega) P _
        (fun k hk => hP.get (by omega) (by rw [ht3, ht2]; omega))
    simp [decCI, nat?, g0, gcv, gcaps]

/-- **`ind_ctor` against the twin's constructor constant.** -/
theorem ctorRW_twin {b : ByteArray} {m m' : Mem} {st : StateD} (a : AState) (hD : LkR m st)
    {c q : Word} {ct : IndCtorRec} (hF : CtF b m c.toNat ct) (hc : c.toNat + 6 < 2 ^ 63)
    (h : ctorRW b.data m c = some (q, m')) :
    (ctT st ct).run a = .ok (resOf (ctT st ct) a, a) ∧ PExt m m' ∧ q.toNat = topN m DLP + 1 ∧
      LkR m' st ∧ RecAt m' q.toNat (resOf (ctT st ct) a) := by
  have hps := hD.psize
  have hpt := hD.ptop
  unfold ctorRW at h
  rcases h1 : allocW m DLP 7 with _ | ⟨q1, m₁⟩ <;> rw [h1] at h
  · cases h
  simp only [allocK] at h
  obtain ⟨P1, P2, P3, P4, P5⟩ := allocP_facts hD.psize hD.ptop h1
  simp only [show (7 : Word).toNat = 7 from rfl] at P3 P4
  have hifr : m₁.arr64 IFR = m.arr64 IFR := P1.other IFR (by decide) (by decide)
  have hsm1 : (m₁.arr64 DLP).size = (m.arr64 DLP).size := P1.size DLP
  cases h2 : cvW b.data (m₁.set64 DLP q1 4) (q1 + 1) (rdW (m₁.arr64 IFR) c) (rdW (m₁.arr64 IFR) (c + 1))
      (rdW (m₁.arr64 IFR) (c + 2)) with
  | none => rw [h2] at h; cases h
  | some m₂ =>
  rw [h2] at h; simp only [mK, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have Pq : PExt m (m₁.set64 DLP q1 4) := P1.set q1 4 (by omega) (by omega)
  have hs1 : ((m₁.set64 DLP q1 4).arr64 DLP).size = (m.arr64 DLP).size := Pq.size DLP
  have ht1 : topN (m₁.set64 DLP q1 4) DLP = topN m DLP + 7 := by
    rw [← P3]; unfold topN; rw [wd_set_ne _ _ _ _ _ (by omega)]
  have hL1 : LkR (m₁.set64 DLP q1 4) st := hD.frame Pq.frame (by rw [ht1, hs1]; omega)
  obtain ⟨⟨n0, l0, y0⟩, f0, p0, -, -⟩ := hF
  have r0 : rdW (m₁.arr64 IFR) c = wd m IFR c.toNat := by rw [hifr]; rfl
  have r1 : rdW (m₁.arr64 IFR) (c + 1) = wd m IFR (c.toNat + 1) := by
    rw [hifr, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  have r2 : rdW (m₁.arr64 IFR) (c + 2) = wd m IFR (c.toNat + 2) := by
    rw [hifr, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  rw [r0, r1, r2] at h2
  have hq1 : (q1 + 1).toNat = q1.toNat + 1 := widx2 _ _ (by simp; omega)
  obtain ⟨cvp, C1, C2, C3, C3', C4, C5, C6⟩ :=
    cvW_facts a hL1 n0.1 y0.1 l0 (by omega) (by rw [hq1, ht1]; omega) h2
  have hrun : (ctT st ct).run a = .ok (.ctorInfo cvp ct.numParams ct.numFields, a) := by
    unfold ctT; rw [run_bind _ _ a _ C1]; rfl
  rw [resOf_eq hrun]
  have hs2 : (m₂.arr64 DLP).size = (m.arr64 DLP).size := by rw [C2.2.2.1 DLP, hs1]
  have ht2 : topN m₂ DLP = topN m DLP + 7 + ct.cv.levelParams.length := by rw [C3, ht1]
  have hifr2 : m₂.arr64 IFR = m.arr64 IFR := by rw [C2.1 IFR (by decide) (by decide), Pq.other IFR (by decide) (by decide)]
  have hq5 : (q1 + 5).toNat = q1.toNat + 5 := widx2 _ _ (by simp; omega)
  have hq6 : (q1 + 6).toNat = q1.toNat + 6 := widx2 _ _ (by simp; omega)
  have w5 : rdW (m₂.arr64 IFR) (c + 5) = wd m IFR (c.toNat + 5) := by
    rw [hifr2, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  have w4 : rdW (m₂.arr64 IFR) (c + 4) = wd m IFR (c.toNat + 4) := by
    rw [hifr2, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  rw [w5, w4]
  have hc0 : ∀ i, (i ≠ q1.toNat + 5 ∧ i ≠ q1.toNat + 6) →
      wd ((m₂.set64 DLP (q1 + 5) (wd m IFR (c.toNat + 5))).set64 DLP (q1 + 6) (wd m IFR (c.toNat + 4))) DLP i =
        wd m₂ DLP i := fun i hi => by
    rw [wd_set_ne _ _ _ _ _ (by omega), wd_set_ne _ _ _ _ _ (by omega)]
  have hsz : (((m₂.set64 DLP (q1 + 5) (wd m IFR (c.toNat + 5))).set64 DLP (q1 + 6)
      (wd m IFR (c.toNat + 4))).arr64 DLP).size = (m.arr64 DLP).size := by simp only [size_set64]; exact hs2
  have hfr : MemFrame [DLP] [] m₂ ((m₂.set64 DLP (q1 + 5) (wd m IFR (c.toNat + 5))).set64 DLP (q1 + 6)
      (wd m IFR (c.toNat + 4))) :=
    (MemFrame.set64 _ DLP (by decide) _ _).trans (MemFrame.set64 _ DLP (by decide) _ _)
  have ht3 : topN ((m₂.set64 DLP (q1 + 5) (wd m IFR (c.toNat + 5))).set64 DLP (q1 + 6)
      (wd m IFR (c.toNat + 4))) DLP = topN m₂ DLP := by
    unfold topN; rw [hc0 0 (by omega)]
  refine ⟨hrun, ⟨Pq.frame.trans (C2.trans hfr), by rw [ht3, ht2]; omega,
    fun i h1 h2 => ?_⟩, P2, ?_, ?_⟩
  · rw [hc0 i (by omega), C4 i h1 (by omega), Pq.keep i h1 h2]
  · exact hD.frame (Pq.frame.trans (C2.trans hfr)) (by rw [ht3, hsz, ← hs2]; exact C3')
  · intro P hP
    have g0 : P[q1.toNat]? = some 4 := by
      rw [hP.get (Nat.le_refl _) (by rw [ht3, ht2]; omega), hc0 _ (by omega),
        C4 _ (by omega) (by omega), wd_set_eq _ _ _ _ _ rfl (by omega)]
    have gcv : decCV P (q1.toNat + 1) = some cvp := by
      rw [← hq1]
      exact C6 P (fun i hi => by
        rw [hP.get (by omega) (by rw [ht3, ht2]; omega), hc0 i (by omega)])
    have g5 : P[q1.toNat + 5]? = some (wd m IFR (c.toNat + 5)) := by
      rw [hP.get (by omega) (by rw [ht3, ht2]; omega), wd_set_ne _ _ _ _ _ (by omega),
        wd_set_eq _ _ _ _ _ hq5 (by omega)]
    have g6 : P[q1.toNat + 6]? = some (wd m IFR (c.toNat + 4)) := by
      rw [hP.get (by omega) (by rw [ht3, ht2]; omega),
        wd_set_eq _ _ _ _ _ hq6 (by simp only [size_set64]; omega)]
    simp [decCI, nat?, g0, gcv, g5, g6, p0.1, f0.1]

end L.Front.Ind
