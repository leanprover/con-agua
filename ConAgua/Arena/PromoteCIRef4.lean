import ConAgua.Arena.PromoteCIRef3

/-!
# The stores as relations on the pool
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem wr1_rel {n : Nat} {d a : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 1 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr1" [d, a] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 1 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a := by
  have h := wr1_call p hp hc
  have e : ∀ (o : Nat), o < 1 → (([0] : List Nat).contains o = true ∨ True) → True := fun _ _ _ => trivial
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_nat d _ (by simp; omega) (by simp) h
  refine ⟨h1, h2, fun i hi => h3 i ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, show (((0 : Word)).toNat = 0) from rfl, show (((1 : Word)).toNat = 1) from rfl, show (((2 : Word)).toNat = 2) from rfl, show (((3 : Word)).toNat = 3) from rfl, show (((4 : Word)).toNat = 4) from rfl, show (((6 : Word)).toNat = 6) from rfl, show (((8 : Word)).toNat = 8) from rfl, show (((9 : Word)).toNat = 9) from rfl, show (((10 : Word)).toNat = 10) from rfl, show (((11 : Word)).toNat = 11) from rfl, show (((13 : Word)).toNat = 13) from rfl]
    omega
  · simpa using h5

theorem wr2_rel {n : Nat} {d a b : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 2 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr2" [d, a, b] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 2 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some b := by
  have h := wr2_call p hp hc
  have e : ∀ (o : Nat), o < 2 → (([0, 1] : List Nat).contains o = true ∨ True) → True := fun _ _ _ => trivial
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_nat d _ (by simp; omega) (by simp) h
  refine ⟨h1, h2, fun i hi => h3 i ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, show (((0 : Word)).toNat = 0) from rfl, show (((1 : Word)).toNat = 1) from rfl, show (((2 : Word)).toNat = 2) from rfl, show (((3 : Word)).toNat = 3) from rfl, show (((4 : Word)).toNat = 4) from rfl, show (((6 : Word)).toNat = 6) from rfl, show (((8 : Word)).toNat = 8) from rfl, show (((9 : Word)).toNat = 9) from rfl, show (((10 : Word)).toNat = 10) from rfl, show (((11 : Word)).toNat = 11) from rfl, show (((13 : Word)).toNat = 13) from rfl]
    omega
  · simpa using h5

theorem wr3_rel {n : Nat} {d a b c : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 3 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr3" [d, a, b, c] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 3 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some b ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some c := by
  have h := wr3_call p hp hc
  have e : ∀ (o : Nat), o < 3 → (([0, 1, 2] : List Nat).contains o = true ∨ True) → True := fun _ _ _ => trivial
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_nat d _ (by simp; omega) (by simp) h
  refine ⟨h1, h2, fun i hi => h3 i ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, show (((0 : Word)).toNat = 0) from rfl, show (((1 : Word)).toNat = 1) from rfl, show (((2 : Word)).toNat = 2) from rfl, show (((3 : Word)).toNat = 3) from rfl, show (((4 : Word)).toNat = 4) from rfl, show (((6 : Word)).toNat = 6) from rfl, show (((8 : Word)).toNat = 8) from rfl, show (((9 : Word)).toNat = 9) from rfl, show (((10 : Word)).toNat = 10) from rfl, show (((11 : Word)).toNat = 11) from rfl, show (((13 : Word)).toNat = 13) from rfl]
    omega
  · simpa using h5

theorem wr4_rel {n : Nat} {d a b c e : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 4 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr4" [d, a, b, c, e] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 4 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some b ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some c ∧
    (m'.arr64 EREC)[d.toNat + 3]? = some e := by
  have h := wr4_call p hp hc
  have e : ∀ (o : Nat), o < 4 → (([0, 1, 2, 3] : List Nat).contains o = true ∨ True) → True := fun _ _ _ => trivial
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_nat d _ (by simp; omega) (by simp) h
  refine ⟨h1, h2, fun i hi => h3 i ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, show (((0 : Word)).toNat = 0) from rfl, show (((1 : Word)).toNat = 1) from rfl, show (((2 : Word)).toNat = 2) from rfl, show (((3 : Word)).toNat = 3) from rfl, show (((4 : Word)).toNat = 4) from rfl, show (((6 : Word)).toNat = 6) from rfl, show (((8 : Word)).toNat = 8) from rfl, show (((9 : Word)).toNat = 9) from rfl, show (((10 : Word)).toNat = 10) from rfl, show (((11 : Word)).toNat = 11) from rfl, show (((13 : Word)).toNat = 13) from rfl]
    omega
  · simpa using h5

theorem wr5_rel {n : Nat} {d a b c e g : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 5 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr5" [d, a, b, c, e, g] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 5 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some b ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some c ∧
    (m'.arr64 EREC)[d.toNat + 3]? = some e ∧
    (m'.arr64 EREC)[d.toNat + 4]? = some g := by
  have h := wr5_call p hp hc
  have e : ∀ (o : Nat), o < 5 → (([0, 1, 2, 3, 4] : List Nat).contains o = true ∨ True) → True := fun _ _ _ => trivial
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_nat d _ (by simp; omega) (by simp) h
  refine ⟨h1, h2, fun i hi => h3 i ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, show (((0 : Word)).toNat = 0) from rfl, show (((1 : Word)).toNat = 1) from rfl, show (((2 : Word)).toNat = 2) from rfl, show (((3 : Word)).toNat = 3) from rfl, show (((4 : Word)).toNat = 4) from rfl, show (((6 : Word)).toNat = 6) from rfl, show (((8 : Word)).toNat = 8) from rfl, show (((9 : Word)).toNat = 9) from rfl, show (((10 : Word)).toNat = 10) from rfl, show (((11 : Word)).toNat = 11) from rfl, show (((13 : Word)).toNat = 13) from rfl]
    omega
  · simpa using h5

theorem capsWr_rel {n : Nat} {d c a k : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 14 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "caps_wr" [d, c, a, k] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 14 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some c ∧
    (m'.arr64 EREC)[d.toNat + 10]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 13]? = some k := by
  have h := capsWr_call p hp hc
  have e : ∀ (o : Nat), o < 14 → (([1, 10, 13] : List Nat).contains o = true ∨ True) → True := fun _ _ _ => trivial
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_nat d _ (by simp; omega) (by simp) h
  refine ⟨h1, h2, fun i hi => h3 i ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, show (((0 : Word)).toNat = 0) from rfl, show (((1 : Word)).toNat = 1) from rfl, show (((2 : Word)).toNat = 2) from rfl, show (((3 : Word)).toNat = 3) from rfl, show (((4 : Word)).toNat = 4) from rfl, show (((6 : Word)).toNat = 6) from rfl, show (((8 : Word)).toNat = 8) from rfl, show (((9 : Word)).toNat = 9) from rfl, show (((10 : Word)).toNat = 10) from rfl, show (((11 : Word)).toNat = 11) from rfl, show (((13 : Word)).toNat = 13) from rfl]
    omega
  · simpa using h5

theorem projWr_rel {n : Nat} {d tn sn lp c ss bs gs : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 12 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "proj_wr" [d, tn, sn, lp, c, ss, bs, gs] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 12 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some tn ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some sn ∧
    (m'.arr64 EREC)[d.toNat + 3]? = some lp ∧
    (m'.arr64 EREC)[d.toNat + 6]? = some c ∧
    (m'.arr64 EREC)[d.toNat + 8]? = some ss ∧
    (m'.arr64 EREC)[d.toNat + 9]? = some bs ∧
    (m'.arr64 EREC)[d.toNat + 11]? = some gs := by
  have h := projWr_call p hp hc
  have e : ∀ (o : Nat), o < 12 → (([1, 2, 3, 6, 8, 9, 11] : List Nat).contains o = true ∨ True) → True := fun _ _ _ => trivial
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_nat d _ (by simp; omega) (by simp) h
  refine ⟨h1, h2, fun i hi => h3 i ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, show (((0 : Word)).toNat = 0) from rfl, show (((1 : Word)).toNat = 1) from rfl, show (((2 : Word)).toNat = 2) from rfl, show (((3 : Word)).toNat = 3) from rfl, show (((4 : Word)).toNat = 4) from rfl, show (((6 : Word)).toNat = 6) from rfl, show (((8 : Word)).toNat = 8) from rfl, show (((9 : Word)).toNat = 9) from rfl, show (((10 : Word)).toNat = 10) from rfl, show (((11 : Word)).toNat = 11) from rfl, show (((13 : Word)).toNat = 13) from rfl]
    omega
  · simpa using h5

end rel

end L.Arena
