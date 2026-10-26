import ConAgua.Arena.PromoteCIRef3

/-!
# The stores as relations on the pool
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- **A store of the words `ps` at offsets below `N` from `d`**, as a relation on the pool. -/
theorem wr_core {N : Nat} {d : Word} {ps : List (Word × Word)} {m m' : Mem}
    (hbd : d.toNat + N ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hN : ∀ q ∈ ps, q.1.toNat < N) (hnd : (ps.map (fun q => q.1.toNat)).Nodup)
    (h : stP d m ps = some m') :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + N ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (∀ q ∈ ps, (m'.arr64 EREC)[d.toNat + q.1.toNat]? = some q.2) := by
  obtain ⟨h1, h2, h3, -, h5⟩ := stP_nat d ps (fun q hq => by have := hN q hq; omega) hnd h
  exact ⟨h1, h2, fun i hi => h3 i fun q hq => by have := hN q hq; omega, h5⟩

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem wr1_rel {n : Nat} {d a : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 1 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr1" [d, a] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 1 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a := by
  obtain ⟨h1, h2, h3, h5⟩ := wr_core hbd hsz
    (by simp only [List.forall_mem_cons]; decide) (by simp) (wr1_call p hp hc)
  exact ⟨h1, h2, h3, by simpa using h5⟩

theorem wr2_rel {n : Nat} {d a b : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 2 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr2" [d, a, b] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 2 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some b := by
  obtain ⟨h1, h2, h3, h5⟩ := wr_core hbd hsz
    (by simp only [List.forall_mem_cons]; decide) (by simp) (wr2_call p hp hc)
  exact ⟨h1, h2, h3, by simpa using h5⟩

theorem wr3_rel {n : Nat} {d a b c : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 3 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr3" [d, a, b, c] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 3 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some b ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some c := by
  obtain ⟨h1, h2, h3, h5⟩ := wr_core hbd hsz
    (by simp only [List.forall_mem_cons]; decide) (by simp) (wr3_call p hp hc)
  exact ⟨h1, h2, h3, by simpa using h5⟩

theorem wr4_rel {n : Nat} {d a b c e : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 4 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr4" [d, a, b, c, e] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 4 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some b ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some c ∧
    (m'.arr64 EREC)[d.toNat + 3]? = some e := by
  obtain ⟨h1, h2, h3, h5⟩ := wr_core hbd hsz
    (by simp only [List.forall_mem_cons]; decide) (by simp) (wr4_call p hp hc)
  exact ⟨h1, h2, h3, by simpa using h5⟩

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
  obtain ⟨h1, h2, h3, h5⟩ := wr_core hbd hsz
    (by simp only [List.forall_mem_cons]; decide) (by simp) (wr5_call p hp hc)
  exact ⟨h1, h2, h3, by simpa using h5⟩

end rel

end L.Arena
