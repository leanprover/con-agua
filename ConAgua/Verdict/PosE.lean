import ConAgua.Verdict.IndE
import ConAgua.Arena.IndT.PosDefs

/-!
# The positivity walk's error claims: the statements (lane `verdicts-b`, helper `ia2`)

The error halves of `PosDefs.lean`'s `*OKC` predicates, in `callE` form: at L fuel `n`, a failing
call of the block's function from the `*OKC`'s hypotheses claims the twin computation fails with
that class. `NbOKE n` is the block's conjunction (`nest_cont_new` is `IndE.lean`'s `NewOKE`;
`nest_cont_key`'s `callE` form `KeyOKEc` comes from `IndE.lean`'s model-form `KeyOKE`). The
continuation-shaped fragments (`nest_ctors_one`, `nest_ctors_walk`) claim the twin's fragment
fails for every continuation `K` (the L function's errors all lie before `K`).

The leaves' claims shared between the steps: `NitE` (`nest_inst_type`), `WhnfTopE` (`whnf_top`
under `StageT`, a core stub).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (dCtx dProg dState dCtors dOut dGrp dKey kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`whnf_top`'s error claim under `StageT`** (a core stub, like `CoreStubsE`'s fields). -/
def WhnfTopE (p : Prog) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, StageT dn vis fe m a → ∀ (dep t : Word), H t →
    ∀ e, callE p n "whnf_top" [vis, dep, t] m = .error e →
      ErrClaim (whnf V fe checkFuel dep.toNat (decI t)) a e

section stmts
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)

/-- **`nest_inst_type`'s error claim** (every fuel), from the facts `nitW_ok` and `nitLe_realC`
take. -/
def NitE : Prop :=
  ∀ (k : Nat) (m : Mem) (a : AState) (ctx hi key : Word) (HI : Nat) (c : NestCtx) (kk : NestKey)
    (ctxP : ConLeche.NestCtx) (keyP : ConLeche.NestKey),
    StageC dn vis fe env m a → AbsOK m → hi.toNat = HI → UCtx dn vis fe m ctx c →
    decNK m key.toNat = some kk → NKIn m key.toNat (· < iwTop m) → NKSl m key → PosMR m →
    dCtx a.store env.find? c = some ctxP → dKey a.store kk = some keyP →
    ∀ e, callE p k "nest_inst_type" [vis, ctx, hi, key] m = .error e →
      ErrClaim (ConRon.Arena.nestInstType fe c HI kk) a e

/-- `nest_pos`'s error claim at L fuel `n` (`PosOKC`'s hypotheses). -/
def PosOKE (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx fu po pl dep kb e ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole)
    (eP : ConLeche.Expr) (nsP : ConLeche.NestState),
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H e → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI e) = some eP → dState a.store NS = some nsP →
    ConLeche.Expr.WScoped dep.toNat eP →
    ∀ er, callE p n "nest_pos" [vis, ctx, fu, po, pl, dep, kb, e, ns] m = .error er →
      ErrClaim (nestPos V fe c fu.toNat prog dep.toNat kb.toNat (decI e) NS) a er

/-- `nest_pos_bind`'s error claim at L fuel `n`. -/
def BindOKE (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx fu po pl dep kb w ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole)
    (wP : ConLeche.Expr) (nsP : ConLeche.NestState),
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H w → w >>> 28 = 6 → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI w) = some wP → dState a.store NS = some nsP →
    ConLeche.Expr.WScoped dep.toNat wP →
    ∀ er, callE p n "nest_pos_bind" [vis, ctx, fu, po, pl, dep, kb, w, ns] m = .error er →
      ErrClaim (posBindT V fe c fu.toNat prog dep.toNat kb.toNat (c.hiAt prog.length) (decI w) NS) a er

/-- `nest_pos_app`'s error claim at L fuel `n`. -/
def AppOKE (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx fu po pl kb hi w ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole)
    (wP : ConLeche.Expr) (nsP : ConLeche.NestState) (dep : Nat),
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → hi.toNat = c.hiAt prog.length → H w → NSB m ns NS → PosMR m →
    AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI w) = some wP → dState a.store NS = some nsP → ConLeche.Expr.WScoped dep wP →
    ∀ er, callE p n "nest_pos_app" [vis, ctx, fu, po, pl, kb, hi, w, ns] m = .error er →
      ErrClaim (posAppT V fe c fu.toNat prog kb.toNat hi.toNat (decI w) NS) a er

/-- `nest_cont`'s error claim at L fuel `n`. -/
def ContOKE (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx fu po pl kb nn us aO aL ns : Word) (c : NestCtx)
    (prog : List NestHole) (args : List EIdx) (NS : NestState)
    (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (nP : ConLeche.Name)
    (usP : List ConLeche.Level) (argsP : List ConLeche.Expr) (nsP : ConLeche.NestState) (dep : Nat),
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H nn → H us → decHL m aO.toNat aL.toNat = some args →
    aO.toNat + aL.toNat ≤ iwTop m → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteN a.store.ns (decI nn) = some nP → denoteLs a.store.lss (decI us) = some usP →
    Frontend.denoteEList a.store args = some argsP → dState a.store NS = some nsP →
    (∀ x ∈ argsP, ConLeche.Expr.WScoped dep x) →
    ∀ er, callE p n "nest_cont" [vis, ctx, fu, po, pl, kb, nn, us, aO, aL, ns] m = .error er →
      ErrClaim (nestCont V fe c fu.toNat prog kb.toNat (decI nn) (decI us) args NS) a er

/-- `nest_cont_key`'s error claim at L fuel `n`, in `callE` form (`KeyOKE` is the model form). -/
def KeyOKEc (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (NS : NestState)
    (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (nP : ConLeche.Name)
    (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (ctyP : ConLeche.Expr)
    (nsP : ConLeche.NestState),
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
    ∀ e, callE p n "nest_cont_key" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns] m = .error e →
      ErrClaim (nestContKey V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS) a e

/-- `nest_frame`'s error claim at L fuel `n`. -/
def FrameOKE (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx fu po pl hi us dO dL nPc gO gL ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (grp : List (NIdx × EIdx)) (NS : NestState)
    (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (usP : List ConLeche.Level)
    (dsP : List ConLeche.Expr) (grpP : List (ConLeche.Name × ConLeche.Expr)) (nsP : ConLeche.NestState),
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → hi.toNat = c.hiAt prog.length → H us →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds → dO.toNat + dL.toNat ≤ iwTop m →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp → NSB m ns NS →
    PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteLs a.store.lss (decI us) = some usP → Frontend.denoteEList a.store ds = some dsP →
    dGrp a.store grp = some grpP → dState a.store NS = some nsP →
    (∀ d ∈ dsP, ConLeche.Expr.WScoped hi.toNat d) → (∀ x ∈ grpP, ConLeche.Expr.WScoped hi.toNat x.2) →
    ∀ e, callE p n "nest_frame" [vis, ctx, fu, po, pl, hi, us, dO, dL, nPc, gO, gL, ns] m = .error e →
      ErrClaim (nestFrame V fe c fu.toNat prog hi.toNat (decI us) ds nPc.toNat grp NS) a e

/-- `nest_ctors`'s error claim at L fuel `n`. -/
def CtorsOKE (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL : Word)
    (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (names : List NIdx) (holes : List EIdx)
    (cs : List (IConstantVal × Nat)) (NS : NestState) (outs : List (List NestFieldKind × EIdx))
    (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (usP : List ConLeche.Level)
    (dsP : List ConLeche.Expr) (namesP : List ConLeche.Name) (holesP : List ConLeche.Expr)
    (csP : List (ConLeche.ConstantVal × Nat)) (nsP : ConLeche.NestState)
    (outsP : List (List ConLeche.NestFieldKind × ConLeche.Expr)),
    StageC dn vis fe env m a → WCtx dn vis fe m ctx po pl c prog →
    CtorsCtx m us dO dL no nl hO hL ds names holes →
    cL.toNat = cs.length → cO.toNat + cs.length ≤ iwTop m → CsAt m cO.toNat cs (· < iwTop m) → NSB m ns NS →
    OutsB m oO.toNat oL.toNat outs → oO.toNat + oL.toNat ≤ iwTop m → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    CtorsPre a.store (decI us) ds names holes hi.toNat usP dsP namesP holesP →
    dCtors a.store cs = some csP → (∀ x ∈ csP, x.1.type.hasFvar = false) →
    dState a.store NS = some nsP → outs.mapM (dOut a.store) = some outsP →
    ∀ e, callE p n "nest_ctors" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cO, cL, ns,
        oO, oL] m = .error e →
      ErrClaim (nestCtors V fe c (decide (root ≠ 0)) fu.toNat prog hi.toNat (decI us) ds names holes cs NS
        outs) a e

/-- `nest_ctors_one`'s error claim at L fuel `n`: the fragment `oneK` fails, whatever its
continuation. -/
def OneOKE (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx root fu po pl hi us dO dL no nl hO hL cv nF ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (names : List NIdx) (holes : List EIdx) (cvv : IConstantVal)
    (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole)
    (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (namesP : List ConLeche.Name)
    (holesP : List ConLeche.Expr) (cvP : ConLeche.ConstantVal) (nsP : ConLeche.NestState),
    StageC dn vis fe env m a → WCtx dn vis fe m ctx po pl c prog →
    CtorsCtx m us dO dL no nl hO hL ds names holes →
    decCV (erecP m) cv.toNat = some cvv → cv.toNat + 3 < 2 ^ 64 → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    CtorsPre a.store (decI us) ds names holes hi.toNat usP dsP namesP holesP →
    Frontend.denoteCV a.store cvv = some cvP → cvP.type.hasFvar = false →
    dState a.store NS = some nsP →
    ∀ e, callE p n "nest_ctors_one" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cv, nF, ns]
        m = .error e →
      ∀ {β : Type} (K : List NestFieldKind × EIdx → NestState → AM β),
        ErrClaim (oneK V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat (decI us) ds names holes cvv nF.toNat NS K)
          a e

/-- `nest_ctors_walk`'s error claim at L fuel `n`: the fragment `walkK` fails, whatever its
continuation. -/
def WalkOKE (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx root fu po pl hi nF crest ns : Word) (c : NestCtx)
    (prog : List NestHole) (NS : NestState) (ctxP : ConLeche.NestCtx)
    (progP : List ConLeche.NestHole) (crestP : ConLeche.Expr) (nsP : ConLeche.NestState),
    StageC dn vis fe env m a → WCtx dn vis fe m ctx po pl c prog → H crest → NSB m ns NS → PosMR m →
    AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI crest) = some crestP → dState a.store NS = some nsP →
    ConLeche.Expr.WScoped hi.toNat crestP →
    ∀ e, callE p n "nest_ctors_walk" [vis, ctx, root, fu, po, pl, hi, nF, crest, ns] m = .error e →
      ∀ {β : Type} (K : List NestFieldKind → List EIdx → EIdx → NestState → EIdx → AM β),
        ErrClaim (walkK V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat nF.toNat (decI crest) NS K) a e

/-- `nest_fields`'s error claim at L fuel `n`. -/
def FieldsOKE (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx fu po pl base nF j cur ns kO kL dO dL : Word) (c : NestCtx)
    (prog : List NestHole) (NS : NestState) (ks : List NestFieldKind) (nds : List EIdx)
    (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (curP : ConLeche.Expr)
    (nsP : ConLeche.NestState) (ndsP : List ConLeche.Expr),
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H cur → NSB m ns NS →
    KlB m kO.toNat kL.toNat ks → kO.toNat + kL.toNat ≤ iwTop m →
    decHL m dO.toNat dL.toNat = some nds → dO.toNat + dL.toNat ≤ iwTop m → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI cur) = some curP → dState a.store NS = some nsP →
    Frontend.denoteEList a.store nds = some ndsP →
    ConLeche.Expr.WScoped (base.toNat + j.toNat) curP →
    ∀ e, callE p n "nest_fields" [vis, ctx, fu, po, pl, base, nF, j, cur, ns, kO, kL, dO, dL] m = .error e →
      ErrClaim (nestFields V fe c fu.toNat prog base.toNat nF.toNat j.toNat (decI cur) NS ks nds) a e

/-- **The block's error claims at L fuel `n`.** -/
def NbOKE (n : Nat) : Prop :=
  PosOKE p dn vis fe env n ∧ BindOKE p dn vis fe env n ∧ AppOKE p dn vis fe env n ∧
    ContOKE p dn vis fe env n ∧ KeyOKEc p dn vis fe env n ∧ NewOKE p dn vis fe env n ∧
    FrameOKE p dn vis fe env n ∧ CtorsOKE p dn vis fe env n ∧ OneOKE p dn vis fe env n ∧
    WalkOKE p dn vis fe env n ∧ FieldsOKE p dn vis fe env n

end stmts

end L.Ind
