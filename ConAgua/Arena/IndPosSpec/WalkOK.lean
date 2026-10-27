import ConAgua.Arena.IndPosSpec.BvbWMfr
import ConAgua.Arena.IndPosSpec.NbPosW
import ConAgua.Arena.IndPosSpec.PosBindT
import ConAgua.Arena.IndPosSpec.KlB
import ConAgua.Arena.IndPosSpec.WCtx

/-!
# WalkOK

`NewOK`, `CtorsCtx`, `WalkOK`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section stmts
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

def NewOK (cR : CallM) (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (NS : NestState) (r : List Word),
    nbNewW cR n m vis ctx fu po pl kb nn us dO dL nPc cty ns = some (r, m') → StageR dn vis fe m a →
    WCtx dn vis fe m ctx po pl c prog → H nn → H us →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds → dO.toNat + dL.toNat ≤ iwTop m →
    H cty → NSB m ns NS → PosMR m → AbsOK m →
    ∃ x a', (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a =
        .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decNFK (r.headD 0) = some x.1 ∧ NSB m' (r.tail.headD 0) x.2 ∧ PosMR m' ∧ AbsOK m'

/-- The facts every constructor walk of a frame shares. -/
structure CtorsCtx (m : Mem) (us dO dL no nl hO hL : Word) (ds : List EIdx) (names : List NIdx)
    (holes : List EIdx) : Prop where
  hus : H us
  hds : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds
  hdsb : dO.toNat + dL.toNat ≤ iwTop m
  hnames : decHL m no.toNat nl.toNat = some names
  hnamesb : no.toNat + nl.toNat ≤ iwTop m
  hnn : dL.toNat + names.length < 2 ^ 64
  hholes : decHL m hO.toNat hL.toNat = some holes
  hholesb : hO.toNat + hL.toNat ≤ iwTop m

def WalkOK (cR : CallM) (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx root fu po pl hi nF crest ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (r : List Word),
    nbWalkW cR n m vis ctx root fu po pl hi nF crest ns = some (r, m') → StageR dn vis fe m a →
    WCtx dn vis fe m ctx po pl c prog → H crest → NSB m ns NS → PosMR m → AbsOK m →
    ∃ ks nds cur ns2 closed a', (∀ {β : Type} (K : List NestFieldKind → List EIdx → EIdx → NestState → EIdx → AM β),
        (walkK V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat nF.toNat (decI crest) NS K).run a =
          (K ks nds cur ns2 closed).run a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ KlB m' (r.headD 0).toNat (r.tail.headD 0).toNat ks ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ ks.length = nF.toNat ∧
      H (r.tail.tail.headD 0) ∧ decI (r.tail.tail.headD 0) = cur ∧
      H (r.tail.tail.tail.headD 0) ∧ decI (r.tail.tail.tail.headD 0) = closed ∧
      NSB m' (r.tail.tail.tail.tail.headD 0) ns2 ∧ PosMR m' ∧ AbsOK m'

end stmts

end L.Ind

end
