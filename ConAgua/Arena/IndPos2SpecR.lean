import ConAgua.Arena.IndPos2SpecQ

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the relational side's
statements — each function of the block, its model at exec fuel `n`, simulated by the twin. -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section stmts
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

def PosOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl dep kb e ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (r : List Word),
    nbPosW n m vis ctx fu po pl dep kb e ns = some (r, m') → StageR dn vis fe m a →
    WCtx dn vis fe m ctx po pl c prog → H e → NSB m ns NS →
    ∃ x a', (nestPos V fe c fu.toNat prog dep.toNat kb.toNat (decI e) NS).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decNFK (r.headD 0) = some x.1 ∧
      H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2.1 ∧ NSB m' (r.tail.tail.headD 0) x.2.2

def BindOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl dep kb w ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (r : List Word),
    nbBindW n m vis ctx fu po pl dep kb w ns = some (r, m') → StageR dn vis fe m a →
    WCtx dn vis fe m ctx po pl c prog → H w → w >>> 28 = 6 → NSB m ns NS →
    ∃ x a', (posBindT V fe c fu.toNat prog dep.toNat kb.toNat (c.hiAt prog.length) (decI w) NS).run a =
        .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decNFK (r.headD 0) = some x.1 ∧
      H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2.1 ∧ NSB m' (r.tail.tail.headD 0) x.2.2

def AppOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl kb hi w ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (r : List Word),
    nbAppW n m vis ctx fu po pl kb hi w ns = some (r, m') → StageR dn vis fe m a →
    WCtx dn vis fe m ctx po pl c prog → hi.toNat = c.hiAt prog.length → H w → NSB m ns NS →
    ∃ x a', (posAppT V fe c fu.toNat prog kb.toNat hi.toNat (decI w) NS).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decNFK (r.headD 0) = some x.1 ∧ x.2.1 = decI w ∧
      NSB m' (r.tail.headD 0) x.2.2

def ContOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl kb nn us aO aL ns : Word) (c : NestCtx) (prog : List NestHole)
    (args : List EIdx) (NS : NestState) (r : List Word),
    nbContW n m vis ctx fu po pl kb nn us aO aL ns = some (r, m') → StageR dn vis fe m a →
    WCtx dn vis fe m ctx po pl c prog → H nn → H us → decHL m aO.toNat aL.toNat = some args →
    aO.toNat + aL.toNat ≤ iwTop m → NSB m ns NS →
    ∃ x a', (nestCont V fe c fu.toNat prog kb.toNat (decI nn) (decI us) args NS).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decNFK (r.headD 0) = some x.1 ∧ NSB m' (r.tail.headD 0) x.2

def KeyOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (NS : NestState) (r : List Word),
    nbKeyW n m vis ctx fu po pl kb nn us dO dL nPc cty ns = some (r, m') → StageR dn vis fe m a →
    WCtx dn vis fe m ctx po pl c prog → H nn → H us →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds → dO.toNat + dL.toNat ≤ iwTop m →
    H cty → NSB m ns NS →
    ∃ x a', (nestContKey V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a =
        .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decNFK (r.headD 0) = some x.1 ∧ NSB m' (r.tail.headD 0) x.2

def NewOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (NS : NestState) (r : List Word),
    nbNewW n m vis ctx fu po pl kb nn us dO dL nPc cty ns = some (r, m') → StageR dn vis fe m a →
    WCtx dn vis fe m ctx po pl c prog → H nn → H us →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds → dO.toNat + dL.toNat ≤ iwTop m →
    H cty → NSB m ns NS →
    ∃ x a', (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a =
        .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decNFK (r.headD 0) = some x.1 ∧ NSB m' (r.tail.headD 0) x.2

def FrameOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl hi us dO dL nPc gO gL ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (grp : List (NIdx × EIdx)) (NS : NestState) (r : List Word),
    nbFrameW n m vis ctx fu po pl hi us dO dL nPc gO gL ns = some (r, m') → StageR dn vis fe m a →
    WCtx dn vis fe m ctx po pl c prog → hi.toNat = c.hiAt prog.length → H us →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds → dO.toNat + dL.toNat ≤ iwTop m →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp → NSB m ns NS →
    ∃ x a', (nestFrame V fe c fu.toNat prog hi.toNat (decI us) ds nPc.toNat grp NS).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ NSB m' (r.headD 0) x

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

def CtorsOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (names : List NIdx) (holes : List EIdx)
    (cs : List (IConstantVal × Nat)) (NS : NestState) (outs : List (List NestFieldKind × EIdx)) (r : List Word),
    nbCtorsW n m vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL = some (r, m') →
    StageR dn vis fe m a → WCtx dn vis fe m ctx po pl c prog → CtorsCtx m us dO dL no nl hO hL ds names holes →
    cL.toNat = cs.length → cO.toNat + cs.length ≤ iwTop m → CsAt m cO.toNat cs (· < iwTop m) → NSB m ns NS →
    OutsB m oO.toNat oL.toNat outs → oO.toNat + oL.toNat ≤ iwTop m →
    ∃ x a', (nestCtors V fe c (decide (root ≠ 0)) fu.toNat prog hi.toNat (decI us) ds names holes cs NS outs).run a =
        .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ OutsB m' (r.headD 0).toNat (r.tail.headD 0).toNat x.1 ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ NSB m' (r.tail.tail.headD 0) x.2

def OneOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx root fu po pl hi us dO dL no nl hO hL cv nF ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (names : List NIdx) (holes : List EIdx) (cvv : IConstantVal)
    (NS : NestState) (r : List Word),
    nbOneW n m vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns = some (r, m') →
    StageR dn vis fe m a → WCtx dn vis fe m ctx po pl c prog → CtorsCtx m us dO dL no nl hO hL ds names holes →
    decCVp m cv.toNat = some cvv → cv.toNat + 3 < 2 ^ 64 → NSB m ns NS →
    ∃ ks closed NS3 a', (∀ {β : Type} (K : List NestFieldKind × EIdx → NestState → AM β),
        (oneK V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat (decI us) ds names holes cvv nF.toNat NS K).run a =
          (K (ks, closed) NS3).run a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ KlB m' (r.headD 0).toNat (r.tail.headD 0).toNat ks ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ H (r.tail.tail.headD 0) ∧
      decI (r.tail.tail.headD 0) = closed ∧ NSB m' (r.tail.tail.tail.headD 0) NS3

def WalkOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx root fu po pl hi nF crest ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (r : List Word),
    nbWalkW n m vis ctx root fu po pl hi nF crest ns = some (r, m') → StageR dn vis fe m a →
    WCtx dn vis fe m ctx po pl c prog → H crest → NSB m ns NS →
    ∃ ks nds cur ns2 closed a', (∀ {β : Type} (K : List NestFieldKind → List EIdx → EIdx → NestState → EIdx → AM β),
        (walkK V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat nF.toNat (decI crest) NS K).run a =
          (K ks nds cur ns2 closed).run a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ KlB m' (r.headD 0).toNat (r.tail.headD 0).toNat ks ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ ks.length = nF.toNat ∧
      H (r.tail.tail.headD 0) ∧ decI (r.tail.tail.headD 0) = cur ∧
      H (r.tail.tail.tail.headD 0) ∧ decI (r.tail.tail.tail.headD 0) = closed ∧
      NSB m' (r.tail.tail.tail.tail.headD 0) ns2

def FieldsOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl base nF j cur ns kO kL dO dL : Word) (c : NestCtx)
    (prog : List NestHole) (NS : NestState) (ks : List NestFieldKind) (nds : List EIdx) (r : List Word),
    nbFieldsW n m vis ctx fu po pl base nF j cur ns kO kL dO dL = some (r, m') → StageR dn vis fe m a →
    WCtx dn vis fe m ctx po pl c prog → H cur → NSB m ns NS →
    KlB m kO.toNat kL.toNat ks → kO.toNat + kL.toNat ≤ iwTop m →
    decHL m dO.toNat dL.toNat = some nds → dO.toNat + dL.toNat ≤ iwTop m →
    ∃ x a', (nestFields V fe c fu.toNat prog base.toNat nF.toNat j.toNat (decI cur) NS ks nds).run a =
        .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      KlB m' (r.headD 0).toNat (r.tail.headD 0).toNat x.1 ∧ (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧
      decHL m' (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat = some x.2.1 ∧
      (r.tail.tail.headD 0).toNat + (r.tail.tail.tail.headD 0).toNat ≤ iwTop m' ∧
      H (r.tail.tail.tail.tail.headD 0) ∧ decI (r.tail.tail.tail.tail.headD 0) = x.2.2.1 ∧
      NSB m' (r.tail.tail.tail.tail.tail.headD 0) x.2.2.2 ∧
      x.1.length = ks.length + nF.toNat ∧ x.2.1.length = nds.length + nF.toNat ∧
      (nF.toNat = 0 ∨ base.toNat + j.toNat + nF.toNat < 2 ^ 64)

/-- The block's relational facts at exec fuel `n`. -/
def NbOK (n : Nat) : Prop :=
  PosOK dn vis fe n ∧ BindOK dn vis fe n ∧ AppOK dn vis fe n ∧ ContOK dn vis fe n ∧ KeyOK dn vis fe n ∧
    NewOK dn vis fe n ∧ FrameOK dn vis fe n ∧ CtorsOK dn vis fe n ∧ OneOK dn vis fe n ∧ WalkOK dn vis fe n ∧
    FieldsOK dn vis fe n

end stmts

end L.Ind
