import ConRon.Bridge.Inductives.Positivity
import ConAgua.Arena.TwinStep
import ConAgua.Arena.IndPosSpec.OneK
import ConAgua.Arena.IndPosSpec.WalkOK

/-!
# The positivity walk under `StageC`: the statements (lane `indstaget`, helper `indstaget-pos`)

The `StageC` companions of `IndPos2SpecR`'s predicates: each function of the `nestPos` block, its
model at `realCall p` and exec fuel `n`, simulated by the twin from `StageC` (the stage relation
with con-ron's `CheckOK`) and con-ron's preconditions of the twin op (`Bridge/Inductives/
Positivity.lean`: the context, the frame stack, the inputs and the walk's state denoting, the
inputs well scoped). The posts add `StageC` and the twin's `CoreStep` to the `StageR` ones; for the
two continuation-shaped fragments (`oneK`, `walkK`, no con-ron spec of their own) and the two arms
of `nestPos` (`posBindT`, `posAppT`) they also give the denotations the caller's next step needs.
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (dCtx dProg dState dCtors dOut dGrp kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section stmts
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)

/-- `nest_pos` under `StageC`. -/
def PosOKC (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl dep kb e ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (r : List Word) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole)
    (eP : ConLeche.Expr) (nsP : ConLeche.NestState),
    nbPosW (realCall p) n m vis ctx fu po pl dep kb e ns = some (r, m') → StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H e → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI e) = some eP → dState a.store NS = some nsP →
    ConLeche.Expr.WScoped dep.toNat eP →
    ∃ x a', (nestPos V fe c fu.toNat prog dep.toNat kb.toNat (decI e) NS).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decNFK (r.headD 0) = some x.1 ∧
      H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2.1 ∧ NSB m' (r.tail.tail.headD 0) x.2.2 ∧
      PosMR m' ∧ AbsOK m' ∧ ConRon.Bridge.CoreStep V env fe a a'

/-- `nest_pos_bind` under `StageC` (the reduct `w`, a `Π`, denoting `wP`). -/
def BindOKC (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl dep kb w ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (r : List Word) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole)
    (wP : ConLeche.Expr) (nsP : ConLeche.NestState),
    nbBindW (realCall p) n m vis ctx fu po pl dep kb w ns = some (r, m') → StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H w → w >>> 28 = 6 → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI w) = some wP → dState a.store NS = some nsP →
    ConLeche.Expr.WScoped dep.toNat wP →
    ∃ x a', (posBindT V fe c fu.toNat prog dep.toNat kb.toNat (c.hiAt prog.length) (decI w) NS).run a =
        .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decNFK (r.headD 0) = some x.1 ∧
      H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2.1 ∧ NSB m' (r.tail.tail.headD 0) x.2.2 ∧
      PosMR m' ∧ AbsOK m' ∧ ConRon.Bridge.CoreStep V env fe a a'

/-- `nest_pos_app` under `StageC` (the reduct `w` denoting `wP`, well scoped at some depth). -/
def AppOKC (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl kb hi w ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (r : List Word) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole)
    (wP : ConLeche.Expr) (nsP : ConLeche.NestState) (dep : Nat),
    nbAppW (realCall p) n m vis ctx fu po pl kb hi w ns = some (r, m') → StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → hi.toNat = c.hiAt prog.length → H w → NSB m ns NS → PosMR m →
    AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI w) = some wP → dState a.store NS = some nsP → ConLeche.Expr.WScoped dep wP →
    ∃ x a', (posAppT V fe c fu.toNat prog kb.toNat hi.toNat (decI w) NS).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decNFK (r.headD 0) = some x.1 ∧ x.2.1 = decI w ∧
      NSB m' (r.tail.headD 0) x.2.2 ∧ PosMR m' ∧ AbsOK m' ∧ ConRon.Bridge.CoreStep V env fe a a'

/-- `nest_cont` under `StageC`. -/
def ContOKC (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl kb nn us aO aL ns : Word) (c : NestCtx)
    (prog : List NestHole) (args : List EIdx) (NS : NestState) (r : List Word)
    (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (nP : ConLeche.Name)
    (usP : List ConLeche.Level) (argsP : List ConLeche.Expr) (nsP : ConLeche.NestState) (dep : Nat),
    nbContW (realCall p) n m vis ctx fu po pl kb nn us aO aL ns = some (r, m') →
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H nn → H us → decHL m aO.toNat aL.toNat = some args →
    aO.toNat + aL.toNat ≤ iwTop m → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteN a.store.ns (decI nn) = some nP → denoteLs a.store.lss (decI us) = some usP →
    Frontend.denoteEList a.store args = some argsP → dState a.store NS = some nsP →
    (∀ x ∈ argsP, ConLeche.Expr.WScoped dep x) →
    ∃ x a', (nestCont V fe c fu.toNat prog kb.toNat (decI nn) (decI us) args NS).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decNFK (r.headD 0) = some x.1 ∧
      NSB m' (r.tail.headD 0) x.2 ∧ PosMR m' ∧ AbsOK m' ∧ ConRon.Bridge.CoreStep V env fe a a'

/-- `nest_cont_key` under `StageC`. -/
def KeyOKC (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (NS : NestState) (r : List Word)
    (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (nP : ConLeche.Name)
    (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (ctyP : ConLeche.Expr)
    (nsP : ConLeche.NestState),
    nbKeyW (realCall p) n m vis ctx fu po pl kb nn us dO dL nPc cty ns = some (r, m') →
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H nn → H us →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds → dO.toNat + dL.toNat ≤ iwTop m →
    H cty → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteN a.store.ns (decI nn) = some nP → denoteLs a.store.lss (decI us) = some usP →
    Frontend.denoteEList a.store ds = some dsP → denoteE a.store (decI cty) = some ctyP →
    dState a.store NS = some nsP →
    (∀ d ∈ dsP, ConLeche.Expr.WScoped (ctxP.hiAt progP.length) d) →
    (∀ d, (∀ y ∈ dsP, ConLeche.Expr.WScoped d y) → ConLeche.Expr.WScoped d ctyP) →
    ∃ x a', (nestContKey V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a =
        .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decNFK (r.headD 0) = some x.1 ∧
      NSB m' (r.tail.headD 0) x.2 ∧ PosMR m' ∧ AbsOK m' ∧ ConRon.Bridge.CoreStep V env fe a a'

/-- `nest_cont_new` under `StageC`. -/
def NewOKC (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (NS : NestState) (r : List Word)
    (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (nP : ConLeche.Name)
    (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (ctyP : ConLeche.Expr)
    (nsP : ConLeche.NestState),
    nbNewW (realCall p) n m vis ctx fu po pl kb nn us dO dL nPc cty ns = some (r, m') →
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H nn → H us →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds → dO.toNat + dL.toNat ≤ iwTop m →
    H cty → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteN a.store.ns (decI nn) = some nP → denoteLs a.store.lss (decI us) = some usP →
    Frontend.denoteEList a.store ds = some dsP → denoteE a.store (decI cty) = some ctyP →
    dState a.store NS = some nsP →
    (∀ d ∈ dsP, ConLeche.Expr.WScoped (ctxP.hiAt progP.length) d) →
    (∀ d, (∀ y ∈ dsP, ConLeche.Expr.WScoped d y) → ConLeche.Expr.WScoped d ctyP) →
    ∃ x a', (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a =
        .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decNFK (r.headD 0) = some x.1 ∧
      NSB m' (r.tail.headD 0) x.2 ∧ PosMR m' ∧ AbsOK m' ∧ ConRon.Bridge.CoreStep V env fe a a'

/-- `nest_frame` under `StageC`. -/
def FrameOKC (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl hi us dO dL nPc gO gL ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (grp : List (NIdx × EIdx)) (NS : NestState) (r : List Word)
    (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (usP : List ConLeche.Level)
    (dsP : List ConLeche.Expr) (grpP : List (ConLeche.Name × ConLeche.Expr)) (nsP : ConLeche.NestState),
    nbFrameW (realCall p) n m vis ctx fu po pl hi us dO dL nPc gO gL ns = some (r, m') →
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → hi.toNat = c.hiAt prog.length → H us →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds → dO.toNat + dL.toNat ≤ iwTop m →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp → NSB m ns NS →
    PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteLs a.store.lss (decI us) = some usP → Frontend.denoteEList a.store ds = some dsP →
    dGrp a.store grp = some grpP → dState a.store NS = some nsP →
    (∀ d ∈ dsP, ConLeche.Expr.WScoped hi.toNat d) → (∀ x ∈ grpP, ConLeche.Expr.WScoped hi.toNat x.2) →
    ∃ x a', (nestFrame V fe c fu.toNat prog hi.toNat (decI us) ds nPc.toNat grp NS).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ NSB m' (r.headD 0) x ∧ PosMR m' ∧ AbsOK m' ∧
      ConRon.Bridge.CoreStep V env fe a a'

/-- The twin-side facts every constructor walk of a frame shares (con-ron's `nestCtors_spec`'s). -/
structure CtorsPre (st : EStore) (us : LsIdx) (ds : List EIdx) (names : List NIdx) (holes : List EIdx)
    (hi : Nat) (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (namesP : List ConLeche.Name)
    (holesP : List ConLeche.Expr) : Prop where
  hus : denoteLs st.lss us = some usP
  hds : Frontend.denoteEList st ds = some dsP
  hnames : Frontend.denoteNList st.ns names = some namesP
  hholes : Frontend.denoteEList st holes = some holesP
  wds : ∀ d ∈ dsP, ConLeche.Expr.WScoped hi d
  wholes : ∀ x ∈ holesP, ConLeche.Expr.WScoped hi x
  hlen : namesP.length ≤ holesP.length

/-- `nest_ctors` under `StageC`. -/
def CtorsOKC (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL : Word)
    (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (names : List NIdx) (holes : List EIdx)
    (cs : List (IConstantVal × Nat)) (NS : NestState) (outs : List (List NestFieldKind × EIdx))
    (r : List Word) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (usP : List ConLeche.Level)
    (dsP : List ConLeche.Expr) (namesP : List ConLeche.Name) (holesP : List ConLeche.Expr)
    (csP : List (ConLeche.ConstantVal × Nat)) (nsP : ConLeche.NestState)
    (outsP : List (List ConLeche.NestFieldKind × ConLeche.Expr)),
    nbCtorsW (realCall p) n m vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL = some (r, m') →
    StageC dn vis fe env m a → WCtx dn vis fe m ctx po pl c prog →
    CtorsCtx m us dO dL no nl hO hL ds names holes →
    cL.toNat = cs.length → cO.toNat + cs.length ≤ iwTop m → CsAt m cO.toNat cs (· < iwTop m) → NSB m ns NS →
    OutsB m oO.toNat oL.toNat outs → oO.toNat + oL.toNat ≤ iwTop m → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    CtorsPre a.store (decI us) ds names holes hi.toNat usP dsP namesP holesP →
    dCtors a.store cs = some csP → (∀ x ∈ csP, x.1.type.hasFvar = false) →
    dState a.store NS = some nsP → outs.mapM (dOut a.store) = some outsP →
    ∃ x a', (nestCtors V fe c (decide (root ≠ 0)) fu.toNat prog hi.toNat (decI us) ds names holes cs NS
        outs).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ OutsB m' (r.headD 0).toNat (r.tail.headD 0).toNat x.1 ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ NSB m' (r.tail.tail.headD 0) x.2 ∧
      PosMR m' ∧ AbsOK m' ∧ ConRon.Bridge.CoreStep V env fe a a'

/-- `nest_ctors_one` under `StageC`: the continuation's inputs denote (the walked out record, the
state with the constructor's normal form pushed). -/
def OneOKC (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx root fu po pl hi us dO dL no nl hO hL cv nF ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (names : List NIdx) (holes : List EIdx) (cvv : IConstantVal)
    (NS : NestState) (r : List Word) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole)
    (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (namesP : List ConLeche.Name)
    (holesP : List ConLeche.Expr) (cvP : ConLeche.ConstantVal) (nsP : ConLeche.NestState),
    nbOneW (realCall p) n m vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns = some (r, m') →
    StageC dn vis fe env m a → WCtx dn vis fe m ctx po pl c prog →
    CtorsCtx m us dO dL no nl hO hL ds names holes →
    decCV (erecP m) cv.toNat = some cvv → cv.toNat + 3 < 2 ^ 64 → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    CtorsPre a.store (decI us) ds names holes hi.toNat usP dsP namesP holesP →
    Frontend.denoteCV a.store cvv = some cvP → cvP.type.hasFvar = false →
    dState a.store NS = some nsP →
    ∃ ks closed NS3 a', (∀ {β : Type} (K : List NestFieldKind × EIdx → NestState → AM β),
        (oneK V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat (decI us) ds names holes cvv nF.toNat NS K).run a =
          (K (ks, closed) NS3).run a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ KlB m' (r.headD 0).toNat (r.tail.headD 0).toNat ks ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ H (r.tail.tail.headD 0) ∧
      decI (r.tail.tail.headD 0) = closed ∧ NSB m' (r.tail.tail.tail.headD 0) NS3 ∧ PosMR m' ∧ AbsOK m' ∧
      ConRon.Bridge.CoreStep V env fe a a' ∧
      (∃ oP, dOut a'.store (ks, closed) = some oP ∧ ConLeche.Expr.WScoped hi.toNat oP.2) ∧
      (∃ nsP3, dState a'.store NS3 = some nsP3)

/-- `nest_ctors_walk` under `StageC`: the walked fields, the result and the closed telescope
denote (con-ron's `nestFields_spec` and `closeTelescope_spec` on the run). -/
def WalkOKC (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx root fu po pl hi nF crest ns : Word) (c : NestCtx)
    (prog : List NestHole) (NS : NestState) (r : List Word) (ctxP : ConLeche.NestCtx)
    (progP : List ConLeche.NestHole) (crestP : ConLeche.Expr) (nsP : ConLeche.NestState),
    nbWalkW (realCall p) n m vis ctx root fu po pl hi nF crest ns = some (r, m') →
    StageC dn vis fe env m a → WCtx dn vis fe m ctx po pl c prog → H crest → NSB m ns NS → PosMR m →
    AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI crest) = some crestP → dState a.store NS = some nsP →
    ConLeche.Expr.WScoped hi.toNat crestP →
    ∃ ks nds cur ns2 closed a', (∀ {β : Type}
        (K : List NestFieldKind → List EIdx → EIdx → NestState → EIdx → AM β),
        (walkK V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat nF.toNat (decI crest) NS K).run a =
          (K ks nds cur ns2 closed).run a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ KlB m' (r.headD 0).toNat (r.tail.headD 0).toNat ks ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ ks.length = nF.toNat ∧
      H (r.tail.tail.headD 0) ∧ decI (r.tail.tail.headD 0) = cur ∧
      H (r.tail.tail.tail.headD 0) ∧ decI (r.tail.tail.tail.headD 0) = closed ∧
      NSB m' (r.tail.tail.tail.tail.headD 0) ns2 ∧ PosMR m' ∧ AbsOK m' ∧
      ConRon.Bridge.CoreStep V env fe a a' ∧
      ∃ ndsP curP nsP2, Frontend.denoteEList a'.store nds = some ndsP ∧ denoteE a'.store cur = some curP ∧
        dState a'.store ns2 = some nsP2 ∧
        denoteE a'.store closed = some (ConLeche.closeTelescope ndsP hi.toNat curP) ∧
        (∀ (i : Nat) (nd : ConLeche.Expr), ndsP[i]? = some nd → ConLeche.Expr.WScoped (hi.toNat + i) nd) ∧
        ConLeche.Expr.WScoped (hi.toNat + ndsP.length) curP

/-- `nest_fields` under `StageC`. -/
def FieldsOKC (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx fu po pl base nF j cur ns kO kL dO dL : Word) (c : NestCtx)
    (prog : List NestHole) (NS : NestState) (ks : List NestFieldKind) (nds : List EIdx) (r : List Word)
    (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (curP : ConLeche.Expr)
    (nsP : ConLeche.NestState) (ndsP : List ConLeche.Expr),
    nbFieldsW (realCall p) n m vis ctx fu po pl base nF j cur ns kO kL dO dL = some (r, m') →
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H cur → NSB m ns NS →
    KlB m kO.toNat kL.toNat ks → kO.toNat + kL.toNat ≤ iwTop m →
    decHL m dO.toNat dL.toNat = some nds → dO.toNat + dL.toNat ≤ iwTop m → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI cur) = some curP → dState a.store NS = some nsP →
    Frontend.denoteEList a.store nds = some ndsP →
    ConLeche.Expr.WScoped (base.toNat + j.toNat) curP →
    ∃ x a', (nestFields V fe c fu.toNat prog base.toNat nF.toNat j.toNat (decI cur) NS ks nds).run a =
        .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
      KlB m' (r.headD 0).toNat (r.tail.headD 0).toNat x.1 ∧ (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧
      decHL m' (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat = some x.2.1 ∧
      (r.tail.tail.headD 0).toNat + (r.tail.tail.tail.headD 0).toNat ≤ iwTop m' ∧
      H (r.tail.tail.tail.tail.headD 0) ∧ decI (r.tail.tail.tail.tail.headD 0) = x.2.2.1 ∧
      NSB m' (r.tail.tail.tail.tail.tail.headD 0) x.2.2.2 ∧
      x.1.length = ks.length + nF.toNat ∧ x.2.1.length = nds.length + nF.toNat ∧
      (nF.toNat = 0 ∨ base.toNat + j.toNat + nF.toNat < 2 ^ 64) ∧ PosMR m' ∧ AbsOK m' ∧
      ConRon.Bridge.CoreStep V env fe a a'

/-- The block's `StageC` facts at exec fuel `n`. -/
def NbOKC (n : Nat) : Prop :=
  PosOKC p dn vis fe env n ∧ BindOKC p dn vis fe env n ∧ AppOKC p dn vis fe env n ∧
    ContOKC p dn vis fe env n ∧ KeyOKC p dn vis fe env n ∧ NewOKC p dn vis fe env n ∧
    FrameOKC p dn vis fe env n ∧ CtorsOKC p dn vis fe env n ∧ OneOKC p dn vis fe env n ∧
    WalkOKC p dn vis fe env n ∧ FieldsOKC p dn vis fe env n

end stmts

end L.Ind
