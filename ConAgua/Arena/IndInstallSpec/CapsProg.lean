module

public import ConAgua.Arena.DeclRec
public import ConAgua.Arena.WhnfIota
public import ConAgua.Arena.WhnfSpineRefine
public import ConAgua.Arena.LevelZero
public import ConAgua.Arena.LevelHeap

@[expose] public section

/-!
# CapsProg

`CapsProg`, `ShapeSrc`, `CapsAt`, `CapsAt.grow`, `ConsIndsProg`.
-/

section

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups `member_never_zero` reaches. -/
structure MnzProg (p : Prog) : Prop where
  mnz : p.lookup "member_never_zero" = some memberNeverZero
  fz : p.lookup "former_z" = some formerZL
  fr : p.lookup "former_res_sort" = some formerResSortL
  pr : p.lookup "pi_result" = some piResultL
  node : p.lookup "lv_node" = some lvNode
  push : p.lookup "lh_push" = some lhPush
  zero : p.lookup "lv_zero" = some lvZero

/-- The lookups of `block_caps_at`. -/
structure CapsProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  rec5 : p.lookup "rec5" = some rec5
  namesCopy : p.lookup "member_names_copy" = some memberNamesCopy
  names : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  erAlloc : p.lookup "erec_alloc" = some erecAlloc
  erCopyGo : p.lookup "block_caps_at_er_copy_go" = some blockCapsAtErCopyGo
  erCopy : p.lookup "block_caps_at_er_copy" = some blockCapsAtErCopy
  erPut : p.lookup "erec_put" = some erecPut
  ctorNames : p.lookup "block_caps_ctor_names" = some blockCapsCtorNames
  fin : p.lookup "block_caps_fin" = some blockCapsFin
  head : p.lookup "block_caps_head" = some blockCapsHead
  one : p.lookup "block_caps_one" = some blockCapsOne
  caps : p.lookup "block_caps_at" = some blockCapsAt
  mnz : MnzProg p

/-- The members' slice of a shape record lies below the top. -/
def ShapeSrc (m : Mem) (q : Word) : Prop :=
  ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l ≤ iwTop m

/-! ## The capability record's decoding -/

/-- **`IIndCaps` at `IW[q‥q+15)`**, decoded in every array that holds those words (at any `e`) and
extends the record pool in use, both tiers (where `cons_block_inds` copies them). -/
def CapsAt (m : Mem) (q : Nat) (c : IIndCaps) : Prop :=
  q + 15 ≤ iwTop m ∧ ∀ (a : Nat → Option Word) (e : Nat), (∀ i < 15, a (e + i) = iwA m (q + i)) →
    ArrExt (erA m) a → decCaps a e = some c

theorem CapsAt.grow {m m' : Mem} {q : Nat} {c : IIndCaps}
    (h : CapsAt m q c) (hg : IWGrow m m') : CapsAt m' q c := by
  refine ⟨Nat.le_trans h.1 hg.iw, fun a e h1 h2 => h.2 a e (fun i hi => ?_) (fun i v hv => h2 i v (hg.ext i v hv))⟩
  rw [h1 i hi]; simp only [iwA, aread]; rw [hg.iwGet _ (by have := h.1; omega)]

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `cons_block_inds`. -/
structure ConsIndsProg (p : Prog) : Prop extends CapsProg p where
  recP : RecProg p
  iir : p.lookup "ind_info_rec" = some indInfoRec
  put5 : p.lookup "er_put5" = some erPut5
  cbi : p.lookup "cons_block_inds" = some consBlockInds

end L.Ind

end

end
