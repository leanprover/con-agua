import ConAgua.Arena.IndInstallSpec13

/-!
# Refinements of `IndInstall`, part 14 (lane `indproofs2`, helper `install`): `consBlockInds`

`ind_info_rec` (the `.indInfo` record: the constant's four words, the capability record's 15, all
read before the allocation and written at once, `wrER`), `env_push` (lane `decls2`'s), by recursion
as the twin's.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `ind_info_rec` -/

/-- The record's words, read in the memory before the allocation. -/
def iirWs (m : Mem) (cv caps : Word) : List Word :=
  [3, rdW (m.arr64 EREC) cv, rdW (m.arr64 EREC) (cv + 1), rdW (m.arr64 EREC) (cv + 2), rdW (m.arr64 EREC) (cv + 3), rdW (m.arr64 IW) caps, rdW (m.arr64 IW) (caps + 1), rdW (m.arr64 IW) (caps + 2), rdW (m.arr64 IW) (caps + 3), rdW (m.arr64 IW) (caps + 4), rdW (m.arr64 IW) (caps + 5), rdW (m.arr64 IW) (caps + 6), rdW (m.arr64 IW) (caps + 7), rdW (m.arr64 IW) (caps + 8), rdW (m.arr64 IW) (caps + 9), rdW (m.arr64 IW) (caps + 10), rdW (m.arr64 IW) (caps + 11), rdW (m.arr64 IW) (caps + 12), rdW (m.arr64 IW) (caps + 13), rdW (m.arr64 IW) (caps + 14)]

theorem erPut5_spec (p : Prog) (hp : p.lookup "er_put5" = some erPut5) (n : Nat) (s₀ : St)
    (d x0 x1 x2 x3 x4 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "er_put5" [d, x0, x1, x2, x3, x4]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = wrER s₀.mem d [x0, x1, x2, x3, x4]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erPut5]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
    finish [wrER, UInt64.add_assoc]

theorem wrER_append : ∀ (xs ys : List Word) (m : Mem) (q : Word),
    wrER m q (xs ++ ys) = wrER (wrER m q xs) (q + UInt64.ofNat xs.length) ys
  | [], ys, m, q => by simp [wrER]
  | x :: xs, ys, m, q => by
    simp only [List.cons_append, wrER]
    rw [wrER_append xs ys]
    congr 1
    simp only [List.length_cons]
    rw [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm (UInt64.ofNat xs.length)]; rfl

/-- The model of `ind_info_rec(cv, caps)`. -/
def iirW (m : Mem) (cv caps : Word) : Option (Word × Mem) :=
  match erAllocW m 20 with
  | none => none
  | some (q, m1) => some (q, wrER m1 q (iirWs m cv caps))

/-- The four writes, one continuation each. -/
def iirK5 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m5) => some ([q], m5)
def iirK4 (p : Prog) (n : Nat) (caps q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m4) => iirK5 q (callW p n "er_put5" [q + 15, rdW (m4.arr64 IW) (caps + 10),
      rdW (m4.arr64 IW) (caps + 11), rdW (m4.arr64 IW) (caps + 12), rdW (m4.arr64 IW) (caps + 13),
      rdW (m4.arr64 IW) (caps + 14)] m4)
def iirK3 (p : Prog) (n : Nat) (caps q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m3) => iirK4 p n caps q (callW p n "er_put5" [q + 10, rdW (m3.arr64 IW) (caps + 5),
      rdW (m3.arr64 IW) (caps + 6), rdW (m3.arr64 IW) (caps + 7), rdW (m3.arr64 IW) (caps + 8),
      rdW (m3.arr64 IW) (caps + 9)] m3)
def iirK2 (p : Prog) (n : Nat) (caps q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => iirK3 p n caps q (callW p n "er_put5" [q + 5, rdW (m2.arr64 IW) caps,
      rdW (m2.arr64 IW) (caps + 1), rdW (m2.arr64 IW) (caps + 2), rdW (m2.arr64 IW) (caps + 3),
      rdW (m2.arr64 IW) (caps + 4)] m2)
/-- After the allocation: the four writes. -/
def iirK (p : Prog) (n : Nat) (cv caps : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m1) => iirK2 p n caps q (callW p n "er_put5" [q, 3, rdW (m1.arr64 EREC) cv,
      rdW (m1.arr64 EREC) (cv + 1), rdW (m1.arr64 EREC) (cv + 2), rdW (m1.arr64 EREC) (cv + 3)] m1)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (cv caps q : Word) (r : List Word)
theorem iirK5_some : iirK5 q (some (r, m)) = some ([q], m) := rfl
theorem iirK4_some : iirK4 p n caps q (some (r, m)) = iirK5 q (callW p n "er_put5" [q + 15,
    rdW (m.arr64 IW) (caps + 10), rdW (m.arr64 IW) (caps + 11), rdW (m.arr64 IW) (caps + 12),
    rdW (m.arr64 IW) (caps + 13), rdW (m.arr64 IW) (caps + 14)] m) := rfl
theorem iirK3_some : iirK3 p n caps q (some (r, m)) = iirK4 p n caps q (callW p n "er_put5" [q + 10,
    rdW (m.arr64 IW) (caps + 5), rdW (m.arr64 IW) (caps + 6), rdW (m.arr64 IW) (caps + 7),
    rdW (m.arr64 IW) (caps + 8), rdW (m.arr64 IW) (caps + 9)] m) := rfl
theorem iirK2_some : iirK2 p n caps q (some (r, m)) = iirK3 p n caps q (callW p n "er_put5" [q + 5,
    rdW (m.arr64 IW) caps, rdW (m.arr64 IW) (caps + 1), rdW (m.arr64 IW) (caps + 2),
    rdW (m.arr64 IW) (caps + 3), rdW (m.arr64 IW) (caps + 4)] m) := rfl
theorem iirK_some : iirK p n cv caps (some (q, m)) = iirK2 p n caps q (callW p n "er_put5" [q, 3,
    rdW (m.arr64 EREC) cv, rdW (m.arr64 EREC) (cv + 1), rdW (m.arr64 EREC) (cv + 2),
    rdW (m.arr64 EREC) (cv + 3)] m) := rfl
end arms
attribute [ind_grind] iirK5_some iirK4_some iirK3_some iirK2_some iirK_some

theorem iir_specK (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hp : p.lookup "ind_info_rec" = some indInfoRec) (n : Nat) (s₀ : St) (cv caps : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ind_info_rec" [cv, caps]
    ⦃fun r s' => LocEq s' s₀ ∧ iirK p n cv caps (erAllocW s₀.mem 20) = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, indInfoRec]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      erecAlloc_specW p ha n, callW_spec p n "er_put5"] <;>
    finish (gen := 40) (instances := 20000) [rdW_eq]

end L.Ind
