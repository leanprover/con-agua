module

public import ConAgua.Arena.RecGenSpec.ClassFeR
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
public import ConAgua.Arena.IndInstallSpec.TabsProg
public import ConAgua.Arena.IndRealBle
public import ConAgua.Arena.RecCheckSpec.RpLook
public import ConAgua.Arena.RecGenSpec.ClassRecTysOk
public import ConAgua.Arena.RecGenSpec.DecB
public import ConAgua.Arena.RecGenSpec.DecCIIndCv
public import ConAgua.Arena.RecGenSpec.DecCNWords
public import ConAgua.Arena.RecGenSpec.Rec3TmdWDecB
public import ConAgua.Arena.IndInstallSpec.SelProg
public import ConAgua.Arena.IndInstallSpec.InstallCvDecB

@[expose] public section

/-!
# GrcProg

`decIS`, `idxTail`, `idxOneAM`, `installIdx_cons`, `installIdxTail`, `IdxProg` and the lemmas only they use.
-/

section

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A pointer to `[off, len]` of level handles. -/
def decIS (m : Mem) (rp : Nat) : Option (List LIdx) := decAt m (decHL m) rp

/-- The index binders' slice: the telescope's tail past `nP`, `(0, 0)` when empty. -/
def idxTail (nP o l : Word) : Word × Word := if nP < l then (o + nP, l - nP) else (0, 0)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- One member's index sorts, as the twin computes them. -/
def idxOneAM (fe : IFEnv) (bs : BlockShape) (ms : MemberShape) (cvTa : IConstantVal) : AM (List LIdx) := do
  let tq ← unwrapOr (← openPisAtFvarsF (bs.nP + ms.nIdx) cvTa.type 0)
    (.internal "direct rec: type former telescope")
  checkStructFieldSortsI V fe true false bs.resSort bs.nP (tq.1.drop bs.nP) [] ms.nIdx
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem installIdx_cons (fe : IFEnv) (bs : BlockShape) (ms : MemberShape) (rest : List MemberShape)
    (cvTa : IConstantVal) (cvTas : List IConstantVal) :
    ConRon.Arena.checkBlockIdxSorts V fe bs (ms :: rest) (cvTa :: cvTas) =
      (idxOneAM fe bs ms cvTa >>= fun is =>
        ConRon.Arena.checkBlockIdxSorts V fe bs rest cvTas >>= fun rs => pure (is :: rs)) := by
  simp only [ConRon.Arena.checkBlockIdxSorts, idxOneAM, bind_assoc]
-/

/-- A handle slice whose tail past `k` is taken: `idxTail`'s slice. -/
theorem installIdxTail {m : Mem} {o l : Word} {xs : List EIdx} {k : Word}
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    decHL m (idxTail k o l).1.toNat (idxTail k o l).2.toNat = some (xs.drop k.toNat) ∧
      (idxTail k o l).1.toNat + (idxTail k o l).2.toNat ≤ iwTop m := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hlen := decHL_length m hd
  unfold idxTail
  split
  · rename_i hk
    have hk' : k.toNat < l.toNat := hk
    have e1 : (o + k).toNat = o.toNat + k.toNat := by rw [UInt64.toNat_add]; omega
    have e2 : (l - k).toNat = l.toNat - k.toNat := UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]; omega)
    rw [e1, e2]
    exact ⟨decHL_drop k.toNat hd (by omega), by omega⟩
  · rename_i hk
    have hk' : ¬ k.toNat < l.toNat := hk
    have : xs.drop k.toNat = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]
    exact ⟨by simp [decHL, hslice?], by simp⟩

/-- The lookups of `check_block_idx_sorts`. -/
structure IdxProg (p : Prog) : Prop extends CstProg p where
  rec2 : p.lookup "rec2" = some rec2
  idx : p.lookup "check_block_idx_sorts" = some checkBlockIdxSorts
  sum : SumProg p

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
local notation "V" => ConLeche.CheckMode.verified

-- ==== S41A.lean
/-! ## The program bundle -/

/-- The lookups of `gen_rec_check` and its callees. -/
structure GrcProg (p : Prog) : Prop where
  rp : RpLook p
  cpy : p.lookup "iw_copy" = some iwCopy
  ia : p.lookup "iw_alloc" = some iwAlloc
  slc : p.lookup "sl_cons" = some slCons
  csr : p.lookup "class_stream_recs" = some classStreamRecsL
  anm : p.lookup "gen_rec_check_any_no_member" = some genRecCheckAnyNoMember
  gft : p.lookup "gen_rec_check_former_tys" = some genRecCheckFormerTys
  cns : CnsProg p
  ccs : CcsProg p
  csm : p.lookup "class_slot_is_minor" = some classSlotIsMinor
  gmo : p.lookup "gen_rec_check_minor_ok" = some genRecCheckMinorOk
  gftc : p.lookup "gen_rec_check_former_tys_c" = some genRecCheckFormerTysC
  sel : SelProg p
  pb : PbProg p
  rts : RtsProg p
  cfr : CfrProg p
  flush : FlushProg p
  crr : CrrProg p
  ers : p.lookup "env_row_set" = some envRowSetL
  ept : p.lookup "env_pop_temp" = some envPopTempL
  gpa : p.lookup "gen_rec_check_pop_all" = some genRecCheckPopAll
  prep : p.lookup "gen_rec_check_prep" = some genRecCheckPrep
  grc : p.lookup "gen_rec_check" = some genRecCheckL
  ble : BleProg p
  opf : OpfF p

-- ==== S41J.lean

/-! ## `check_block_rec` -/

end L.Ind

end

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups of `check_block_tail`. -/
structure TailProg (p : Prog) : Prop where
  idx : IdxProg p
  recp : RecProg p
  hci : p.lookup "ctor_info_rec" = some ctorInfoRecL
  hcs : p.lookup "cons_sum_ctors" = some consSumCtorsL
  hcbc : p.lookup "cons_block_ctors" = some consBlockCtors
  flush : FlushProg p
  nf : p.lookup "nest_field_kind_flat" = some nestFieldKindFlat
  ni : p.lookup "nest_kinds_flat_inner" = some nestKindsFlatInner
  nm : p.lookup "nest_kinds_flat_mid" = some nestKindsFlatMid
  nk : p.lookup "nest_kinds_flat" = some nestKindsFlat
  ng : p.lookup "block_nested_bit_go" = some blockNestedBitGo
  nb : p.lookup "block_nested_bit" = some blockNestedBit
  crec : p.lookup "check_block_rec" = some checkBlockRec
  tabs : TabsProg p
  tail : p.lookup "check_block_tail" = some checkBlockTail

end L.Ind

end
