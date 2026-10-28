import ConAgua.Verdict.PosE3Fm
import ConAgua.Arena.IndPosSpec.BvbWMfr
import ConAgua.Arena.Verdict
import ConAgua.Arena.IndPosSpec.KlB
import ConAgua.Arena.IndPosSpec.WCtx
import ConAgua.Arena.IndPosSpec.OneK
import ConAgua.Arena.IndPosSpec.WalkOK
import ConAgua.Verdict.IndE
import ConAgua.Verdict.VCtx
import ConAgua.Verdict.PosE2M
import ConAgua.Verdict.PosE3Cm
import ConAgua.Arena.IndT.PosDefs

/-!
# The positivity walk: one refinement per function, the statements

The `nestPos` block's eleven functions, each refined by its model for both outcomes (`RefE`) at L
fuel `n`, from `StageC` (the stage relation with con-ron's `CheckOK`) and con-ron's preconditions of
the twin op (`Bridge/Inductives/Positivity.lean`: the context, the frame stack, the inputs and the
walk's state denoting, the inputs well scoped): `NbRef n`. The posts add `StageC` and the twin's
`CoreStep`; for the two continuation-shaped fragments (`oneK`, `walkK`, refined without their
continuation as `oneT`, `walkT`) and the two arms of `nestPos` (`posBindT`, `posAppT`) they also
give the denotations the caller's next step needs. The error halves assume `NbG p`.

The leaf claim shared between the steps: `WhnfTopE` (`whnf_top` under `StageT`, a core stub).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (dCtx dProg dState dCtors dOut dGrp dKey kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified



/-! ## The block, one refinement per function for both outcomes -/

/-- **What the block's error claims assume about the program**: the no-verdict closure, the core
stubs' claims, `whnf_top`'s claim under `StageT`. -/
structure NbG (p : Prog) : Prop where
  nv : closedNV p _root_.L.Checker.nvFns = true
  core : CoreStubsE p
  whnf : WhnfTopE p

section twin
variable (mode : ConLeche.CheckMode) (fe : IFEnv) (ctx : NestCtx) (fuel : Nat) (prog : List NestHole)

/-- `walkK`, its continuation's inputs as its result. -/
def walkT (root : Bool) (hi nF : Nat) (crest : EIdx) (ns : NestState) :
    AM (List NestFieldKind × List EIdx × EIdx × NestState × EIdx) :=
  walkK mode fe ctx fuel prog root hi nF crest ns fun ks nds cur ns2 closed => pure (ks, nds, cur, ns2, closed)

theorem walkK_split {β : Type} (root : Bool) (hi nF : Nat) (crest : EIdx) (ns : NestState)
    (K : List NestFieldKind → List EIdx → EIdx → NestState → EIdx → AM β) :
    walkK mode fe ctx fuel prog root hi nF crest ns K =
      walkT mode fe ctx fuel prog root hi nF crest ns >>= fun x => K x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  unfold walkT walkK
  cases root <;> simp only [Bool.false_eq_true, dite_false, dite_true, bind_assoc, pure_bind]

theorem walkK_bind {β γ : Type} (root : Bool) (hi nF : Nat) (crest : EIdx) (ns : NestState)
    (K : List NestFieldKind → List EIdx → EIdx → NestState → EIdx → AM β) (f : β → AM γ) :
    walkK mode fe ctx fuel prog root hi nF crest ns K >>= f =
      walkK mode fe ctx fuel prog root hi nF crest ns fun ks nds cur ns2 closed => K ks nds cur ns2 closed >>= f := by
  rw [walkK_split, walkK_split, bind_assoc]

/-- `oneK`, its continuation's inputs as its result. -/
def oneT (root : Bool) (hi : Nat) (us : LsIdx) (ds : List EIdx) (names : List NIdx) (holes : List EIdx)
    (cv : IConstantVal) (nF : Nat) (ns : NestState) : AM ((List NestFieldKind × EIdx) × NestState) :=
  oneK mode fe ctx fuel prog root hi us ds names holes cv nF ns fun o ns3 => pure (o, ns3)

theorem oneK_split {β : Type} (root : Bool) (hi : Nat) (us : LsIdx) (ds : List EIdx) (names : List NIdx)
    (holes : List EIdx) (cv : IConstantVal) (nF : Nat) (ns : NestState)
    (K : List NestFieldKind × EIdx → NestState → AM β) :
    oneK mode fe ctx fuel prog root hi us ds names holes cv nF ns K =
      oneT mode fe ctx fuel prog root hi us ds names holes cv nF ns >>= fun x => K x.1 x.2 := by
  unfold oneT oneK roK
  simp only [bind_assoc, pure_bind, ite_bind', fail_bindAM]
  split
  · rfl
  · congr 1; funext cty
    congr 1; funext x
    cases x
    · simp only [fail_bindAM]
    · simp only [bind_assoc, walkK_bind, ite_bind', fail_bindAM, pure_bind]

end twin

section posts
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (a : AState)
  (m : Mem)

/-- What `nest_pos` and `nest_pos_bind` give besides the twin's `(kind, normal form, state)`. -/
structure PosPost (r : List Word) (m' : Mem) (x : NestFieldKind × EIdx × NestState) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  kind : decNFK (r.headD 0) = some x.1
  hnf : H (r.tail.headD 0)
  nf : decI (r.tail.headD 0) = x.2.1
  ns : NSB m' (r.tail.tail.headD 0) x.2.2
  pos : PosMR m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

/-- What `nest_pos_app` (on `w`) gives besides the twin's `(kind, w, state)`. -/
structure AppPost (w : Word) (r : List Word) (m' : Mem) (x : NestFieldKind × EIdx × NestState) (a' : AState) :
    Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  kind : decNFK (r.headD 0) = some x.1
  nf : x.2.1 = decI w
  ns : NSB m' (r.tail.headD 0) x.2.2
  pos : PosMR m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

/-- What `nest_cont`, `nest_cont_key` and `nest_cont_new` give besides the twin's `(kind, state)`. -/
structure KindPost (r : List Word) (m' : Mem) (x : NestFieldKind × NestState) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  kind : decNFK (r.headD 0) = some x.1
  ns : NSB m' (r.tail.headD 0) x.2
  pos : PosMR m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

/-- What `nest_frame` gives besides the twin's state. -/
structure FramePost (r : List Word) (m' : Mem) (x : NestState) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  ns : NSB m' (r.headD 0) x
  pos : PosMR m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

/-- What `nest_ctors` gives besides the twin's `(outs, state)`. -/
structure CtorsPost (r : List Word) (m' : Mem) (x : List (List NestFieldKind × EIdx) × NestState) (a' : AState) :
    Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  outs : OutsB m' (r.headD 0).toNat (r.tail.headD 0).toNat x.1
  outsb : (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m'
  ns : NSB m' (r.tail.tail.headD 0) x.2
  pos : PosMR m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

/-- What `nest_ctors_one` gives besides the twin's `((kinds, closed), state)`: the continuation's
inputs denote. -/
structure OnePost (hi : Word) (r : List Word) (m' : Mem) (x : (List NestFieldKind × EIdx) × NestState)
    (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  kinds : KlB m' (r.headD 0).toNat (r.tail.headD 0).toNat x.1.1
  kindsb : (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m'
  hcl : H (r.tail.tail.headD 0)
  cl : decI (r.tail.tail.headD 0) = x.1.2
  ns : NSB m' (r.tail.tail.tail.headD 0) x.2
  pos : PosMR m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'
  out : ∃ oP, dOut a'.store x.1 = some oP ∧ ConLeche.Expr.WScoped hi.toNat oP.2
  st : ∃ nsP3, dState a'.store x.2 = some nsP3

/-- What `nest_ctors_walk` gives besides the twin's `(kinds, domains, result, state, closed)`: they
denote (con-ron's `nestFields_spec` and `closeTelescope_spec` on the run). -/
structure WalkPost (hi nF : Word) (r : List Word) (m' : Mem)
    (x : List NestFieldKind × List EIdx × EIdx × NestState × EIdx) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  kinds : KlB m' (r.headD 0).toNat (r.tail.headD 0).toNat x.1
  kindsb : (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m'
  klen : x.1.length = nF.toNat
  hcur : H (r.tail.tail.headD 0)
  cur : decI (r.tail.tail.headD 0) = x.2.2.1
  hcl : H (r.tail.tail.tail.headD 0)
  cl : decI (r.tail.tail.tail.headD 0) = x.2.2.2.2
  ns : NSB m' (r.tail.tail.tail.tail.headD 0) x.2.2.2.1
  pos : PosMR m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'
  den : ∃ ndsP curP nsP2, Frontend.denoteEList a'.store x.2.1 = some ndsP ∧ denoteE a'.store x.2.2.1 = some curP ∧
    dState a'.store x.2.2.2.1 = some nsP2 ∧
    denoteE a'.store x.2.2.2.2 = some (ConLeche.closeTelescope ndsP hi.toNat curP) ∧
    (∀ (i : Nat) (nd : ConLeche.Expr), ndsP[i]? = some nd → ConLeche.Expr.WScoped (hi.toNat + i) nd) ∧
    ConLeche.Expr.WScoped (hi.toNat + ndsP.length) curP

/-- What `nest_fields` gives besides the twin's `(kinds, domains, result, state)`. -/
structure FieldsPost (base nF j : Word) (ks : List NestFieldKind) (nds : List EIdx) (r : List Word) (m' : Mem)
    (x : List NestFieldKind × List EIdx × EIdx × NestState) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  kinds : KlB m' (r.headD 0).toNat (r.tail.headD 0).toNat x.1
  kindsb : (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m'
  doms : decHL m' (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat = some x.2.1
  domsb : (r.tail.tail.headD 0).toNat + (r.tail.tail.tail.headD 0).toNat ≤ iwTop m'
  hcur : H (r.tail.tail.tail.tail.headD 0)
  cur : decI (r.tail.tail.tail.tail.headD 0) = x.2.2.1
  ns : NSB m' (r.tail.tail.tail.tail.tail.headD 0) x.2.2.2
  kindsl : x.1.length = ks.length + nF.toNat
  domsl : x.2.1.length = nds.length + nF.toNat
  nfb : nF.toNat = 0 ∨ base.toNat + j.toNat + nF.toNat < 2 ^ 64
  pos : PosMR m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

end posts

section refs
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)

/-- **`nest_pos` refines `nestPos`, both outcomes**, at L fuel `n`. -/
def PosRef (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx fu po pl dep kb e ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole)
    (eP : ConLeche.Expr) (nsP : ConLeche.NestState),
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H e → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI e) = some eP → dState a.store NS = some nsP →
    ConLeche.Expr.WScoped dep.toNat eP →
    RefE (NbG p) (npE p n m vis ctx fu po pl dep kb e ns)
      (nestPos V fe c fu.toNat prog dep.toNat kb.toNat (decI e) NS) a
      (fun v x a' => PosPost dn vis fe env a m v.1 v.2 x a')

/-- **`nest_pos_bind` refines `posBindT`, both outcomes.** -/
def BindRef (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx fu po pl dep kb w ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole)
    (wP : ConLeche.Expr) (nsP : ConLeche.NestState),
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H w → w >>> 28 = 6 → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI w) = some wP → dState a.store NS = some nsP →
    ConLeche.Expr.WScoped dep.toNat wP →
    RefE (NbG p) (npbE p n m vis ctx fu po pl dep kb w ns)
      (posBindT V fe c fu.toNat prog dep.toNat kb.toNat (c.hiAt prog.length) (decI w) NS) a
      (fun v x a' => PosPost dn vis fe env a m v.1 v.2 x a')

/-- **`nest_pos_app` refines `posAppT`, both outcomes.** -/
def AppRef (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx fu po pl kb hi w ns : Word) (c : NestCtx) (prog : List NestHole)
    (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole)
    (wP : ConLeche.Expr) (nsP : ConLeche.NestState) (dep : Nat),
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → hi.toNat = c.hiAt prog.length → H w → NSB m ns NS → PosMR m →
    AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI w) = some wP → dState a.store NS = some nsP → ConLeche.Expr.WScoped dep wP →
    RefE (NbG p) (npaE p n m vis ctx fu po pl kb hi w ns)
      (posAppT V fe c fu.toNat prog kb.toNat hi.toNat (decI w) NS) a
      (fun v x a' => AppPost dn vis fe env a m w v.1 v.2 x a')

/-- **`nest_cont` refines `nestCont`, both outcomes.** -/
def ContRef (n : Nat) : Prop :=
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
    RefE (NbG p) (ncE p n m vis ctx fu po pl kb nn us aO aL ns)
      (nestCont V fe c fu.toNat prog kb.toNat (decI nn) (decI us) args NS) a
      (fun v x a' => KindPost dn vis fe env a m v.1 v.2 x a')

/-- **`nest_cont_key` refines `nestContKey`, both outcomes.** -/
def KeyRef (n : Nat) : Prop :=
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
    RefE (NbG p) (nckE p n m vis ctx fu po pl kb nn us dO dL nPc cty ns)
      (nestContKey V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS) a
      (fun v x a' => KindPost dn vis fe env a m v.1 v.2 x a')

/-- **`nest_cont_new` refines `nestContNew`, both outcomes.** -/
def NewRef (n : Nat) : Prop :=
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
    RefE (NbG p) (nnewE p n m vis ctx fu po pl kb nn us dO dL nPc cty ns)
      (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS) a
      (fun v x a' => KindPost dn vis fe env a m v.1 v.2 x a')

/-- **`nest_frame` refines `nestFrame`, both outcomes.** -/
def FrameRef (n : Nat) : Prop :=
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
    RefE (NbG p) (nfrE p n m vis ctx fu po pl hi us dO dL nPc gO gL ns)
      (nestFrame V fe c fu.toNat prog hi.toNat (decI us) ds nPc.toNat grp NS) a
      (fun v x a' => FramePost dn vis fe env a m v.1 v.2 x a')

/-- **`nest_ctors` refines `nestCtors`, both outcomes.** -/
def CtorsRef (n : Nat) : Prop :=
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
    RefE (NbG p) (nctE p n m vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL)
      (nestCtors V fe c (decide (root ≠ 0)) fu.toNat prog hi.toNat (decI us) ds names holes cs NS outs) a
      (fun v x a' => CtorsPost dn vis fe env a m v.1 v.2 x a')

/-- **`nest_ctors_one` refines `oneT` (`oneK` without its continuation), both outcomes.** -/
def OneRef (n : Nat) : Prop :=
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
    RefE (NbG p) (noE p n m vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns)
      (oneT V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat (decI us) ds names holes cvv nF.toNat NS) a
      (fun v x a' => OnePost dn vis fe env a m hi v.1 v.2 x a')

/-- **`nest_ctors_walk` refines `walkT` (`walkK` without its continuation), both outcomes.** -/
def WalkRef (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx root fu po pl hi nF crest ns : Word) (c : NestCtx)
    (prog : List NestHole) (NS : NestState) (ctxP : ConLeche.NestCtx)
    (progP : List ConLeche.NestHole) (crestP : ConLeche.Expr) (nsP : ConLeche.NestState),
    StageC dn vis fe env m a → WCtx dn vis fe m ctx po pl c prog → H crest → NSB m ns NS → PosMR m →
    AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteE a.store (decI crest) = some crestP → dState a.store NS = some nsP →
    ConLeche.Expr.WScoped hi.toNat crestP →
    RefE (NbG p) (nwE p n m vis ctx root fu po pl hi nF crest ns)
      (walkT V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat nF.toNat (decI crest) NS) a
      (fun v x a' => WalkPost dn vis fe env a m hi nF v.1 v.2 x a')

/-- **`nest_fields` refines `nestFields`, both outcomes.** -/
def FieldsRef (n : Nat) : Prop :=
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
    RefE (NbG p) (nfE p n m vis ctx fu po pl base nF j cur ns kO kL dO dL)
      (nestFields V fe c fu.toNat prog base.toNat nF.toNat j.toNat (decI cur) NS ks nds) a
      (fun v x a' => FieldsPost dn vis fe env a m base nF j ks nds v.1 v.2 x a')

/-- **The block's refinements at L fuel `n`.** -/
structure NbRef (n : Nat) : Prop where
  pos : PosRef p dn vis fe env n
  bind : BindRef p dn vis fe env n
  app : AppRef p dn vis fe env n
  cont : ContRef p dn vis fe env n
  key : KeyRef p dn vis fe env n
  new : NewRef p dn vis fe env n
  frame : FrameRef p dn vis fe env n
  ctors : CtorsRef p dn vis fe env n
  one : OneRef p dn vis fe env n
  walk : WalkRef p dn vis fe env n
  fields : FieldsRef p dn vis fe env n

end refs

end L.Ind
