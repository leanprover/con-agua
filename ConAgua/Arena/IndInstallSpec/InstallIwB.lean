import ConAgua.Arena.IndInstallSpec.InstallCvDecB
import ConAgua.Arena.IndSumSpec.SumProg

/-!
# InstallIwB

`installIwB`, `decPLB`, `decCNSB`, `iwA_truncM_size_le`, `decCNSB_bound`, `CtorsProg`.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A `bool?` word of a record decoded below the tops, read at its word address. -/
theorem installIwB {m : Mem} {w : Word} {k : Nat} {b : Bool} (h : iwB (truncM m) (w.toNat + k) = some b)
    (hsz : (m.arr64 IW).size < 2 ^ 64) : (rdW (m.arr64 IW) (w + UInt64.ofNat k) != 0) = b := by
  simp only [iwB, bool?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨hi, hx'⟩ := truncM_iw_get hx
  simp only [iwA] at hx'
  have hlt : w.toNat + k < (m.arr64 IW).size := (Array.getElem?_eq_some_iff.mp hx').1
  have hk : k < 2 ^ 64 := by omega
  have hwk : w.toNat + k < 2 ^ 64 := by omega
  have he : (w + UInt64.ofNat k).toNat = w.toNat + k := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hk]; exact Nat.mod_eq_of_lt hwk
  rw [rdW_of_get? he.symm hx']

/-! ## Member slices with their bound

A member's constructor slice `(o, l)` decoded below the tops says nothing about `o` when `l = 0`;
the positivity walk (`CssAt`) wants `o + l ≤ iwTop` for every member. `decPLB` carries the bound in
the decoding (below the tops the pool's size is its top), so it survives `sl_cons` and growth. -/

/-- A pointer slice whose end lies within the pool. -/
def decPLB {α : Type} (m : Mem) (f : Nat → Option α) (o l : Nat) : Option (List α) :=
  if o + l ≤ (iwA m).size then decPL m f o l else none

/-- A member's constructors with their slice's bound. -/
def decCNSB (m : Mem) (q : Nat) : Option (List (IConstantVal × Nat)) :=
  decAt m (fun o l => decPLB m (decCN m) o l) q

/-- Below the tops, the pool's size is at most its top. -/
theorem iwA_truncM_size_le (m : Mem) : (iwA (truncM m)).size ≤ iwTop m := by
  apply Nat.le_of_not_lt
  intro h
  have := truncM_iw_get? m (iwTop m)
  rw [ite_eq_right (Nat.lt_irrefl _)] at this
  rw [Array.getElem?_eq_getElem h] at this
  cases this

/-- A `[off, len]` member record decoded with its bound: the bound. -/
theorem decCNSB_bound {m : Mem} {q : Nat} {cs : List (IConstantVal × Nat)}
    (h : DecB (fun m => decCNSB m q) m cs) :
    ∃ o l, iwN (truncM m) q = some o ∧ iwN (truncM m) (q + 1) = some l ∧ o + l ≤ iwTop m ∧
      decPL (truncM m) (decCN (truncM m)) o l = some cs := by
  have h' : decCNSB (truncM m) q = some cs := h
  simp only [decCNSB, decAt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h'
  obtain ⟨o, ho, l, hl, hd⟩ := h'
  simp only [decPLB] at hd
  split at hd
  · rename_i hb
    exact ⟨o, l, ho, hl, Nat.le_trans hb (iwA_truncM_size_le m), hd⟩
  · cases hd

/-- The lookups of `check_block_ctors`. -/
structure CtorsProg (p : Prog) : Prop extends CstProg p where
  rec2 : p.lookup "rec2" = some rec2
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  one : p.lookup "check_block_ctors_one" = some checkBlockCtorsOne
  go : p.lookup "check_block_ctors_go" = some checkBlockCtorsGo
  ctors : p.lookup "check_block_ctors" = some checkBlockCtors
  sum : SumProg p

end L.Ind

end
