module

public import ConAgua.Arena.IndDeclConstsRecs
public import ConAgua.Arena.IndInstallSpec.BlockRawRec
public import ConAgua.Arena.IndCopy2
import ConAgua.Arena.IndPosSpec.RootHoles
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndRealNames
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndDeclConsts

@[expose] public section

/-!
# A declaration's constants: a block's (lane `ronsync2`, stage 3)

`block_constants(p)` refines con-ron's `blockConstants` (`Arena/Install.lean`): `block_is_rec`
(`blockIsRec_refines`), the formers (`bfW_ok`), the constructors (`bctW_ok`), the recursors
(`brsW_ok`), appended (`sl_append`, `appendW_ci`) into an `IW` slice of `EREC` constant records.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `block_constants`. -/
structure BlockProg (p : Prog) : Prop extends RecsProg p where
  ma : MaProg p
  memberNamesCopy : p.lookup "member_names_copy" = some memberNamesCopy
  pdma : p.lookup "pi_doms_mention_any" = some piDomsMentionAny
  birm : p.lookup "block_is_rec_member" = some blockIsRecMember
  birg : p.lookup "block_is_rec_go" = some blockIsRecGo
  bir : p.lookup "block_is_rec" = some blockIsRec
  slAppend : p.lookup "sl_append" = some slAppend
  bk : p.lookup "block_constants" = some blockConstants

/-- Two `EREC` constant-record slices appended (`sl_append`). -/
theorem appendW_ci {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {o1 l1 o2 l2 : Word}
    {r : List Word} {xs ys : List IConstantInfo}
    (h : appendW n m o1 l1 o2 l2 = some (r, m')) (hS : StageR vis fe m a)
    (hb1 : o1.toNat + l1.toNat ≤ iwTop m) (hb2 : o2.toNat + l2.toNat ≤ iwTop m)
    (hx : decPL m (decCI (erecP m)) o1.toNat l1.toNat = some xs)
    (hy : decPL m (decCI (erecP m)) o2.toNat l2.toNat = some ys) :
    decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some (xs ++ ys) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' ∧ StageR vis fe m' a ∧ IWGrow m m' := by
  obtain ⟨hS', hg, h0, h1, htop, hc1, hc2⟩ := appendW_stage h hS hb1 hb2
  have hlx := decPL_length m hx
  have hly := decPL_length m hy
  refine ⟨?_, by omega, hS', hg⟩
  rw [h0, h1, ← hlx, ← hly, ← List.length_append]
  apply decPL_of_get
  intro j hj
  simp only [List.length_append] at hj
  by_cases hj1 : j < xs.length
  · obtain ⟨v, x, hv, hfx, hgx⟩ := decPL_get _ _ _ hx j (by omega)
    refine ⟨v, ?_, ?_⟩
    · simp only [iwN, nat?, iwA, aread_apply] at hv ⊢
      rw [hc1 j (by omega)]; exact hv
    · rw [List.getElem_append_left hj1]
      rw [List.getElem?_eq_getElem hj1] at hgx
      rw [Option.some.inj hgx]; exact hg.ext.decCI hfx
  · obtain ⟨v, x, hv, hfx, hgx⟩ := decPL_get _ _ _ hy (j - xs.length) (by omega)
    refine ⟨v, ?_, ?_⟩
    · simp only [iwN, nat?, iwA, aread_apply] at hv ⊢
      rw [show iwTop m + j = iwTop m + l1.toNat + (j - xs.length) by omega, hc2 _ (by omega)]; exact hv
    · rw [List.getElem_append_right (by omega)]
      rw [List.getElem?_eq_getElem (by omega)] at hgx
      rw [Option.some.inj hgx]; exact hg.ext.decCI hfx

end L.Ind

end
