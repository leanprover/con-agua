import ConAgua.Arena.IndPos2SpecM

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the twin's block in pieces,
one per L function, each taking the rest of the twin's code as a continuation (so that every
piece is the twin's text, and the twin's functions are their pieces by `rfl`). -/


noncomputable section

open ConRon.Arena
open ConLeche (CheckMode)

namespace L.Ind

section pieces
variable (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) (fuel : Nat) (prog : List NestHole)

/-- The `Π` branch of `nestPos` (`nest_pos_bind`). -/
def posBindT (dep kb hi : Nat) (w : EIdx) (ns : NestState) : AM (NestFieldKind × EIdx × NestState) := do
  match ← viewBind w with
  | none => failDanglingE
  | some (a, b) =>
    if ← ConRon.Arena.nestOcc ctx.names ctx.nP hi a then
      fail (.invalid "nested positivity: non positive occurrence of the datatypes being declared")
    else do
      let fv ← internFVarE dep a
      let b2 ← instantiate1Fast coreWalkFuel b fv 0
      let (k, nb, ns2) ← ConRon.Arena.nestPos mode fe ctx fuel prog (dep + 1) (kb + 1) b2 ns
      let nb2 ← abstract1Fast coreWalkFuel nb dep 0
      let r ← internForallEE a nb2
      pure (k, r, ns2)

/-- The application branch of `nestPos` (`nest_pos_app`). -/
def posAppT (kb hi : Nat) (w : EIdx) (ns : NestState) : AM (NestFieldKind × EIdx × NestState) := do
  let args ← getAppArgs coreWalkFuel w
  let hd ← getAppFn coreWalkFuel w
  match ← view hd with
  | .fvar i _ => pfK fe ctx prog kb hi i args (fun k => pure (k, w, ns))
  | .const n us =>
    if ctx.names.contains n then fail nestNonValid
    else do
      let (k, ns2) ← ConRon.Arena.nestCont mode fe ctx fuel prog kb n us args ns
      pure (k, w, ns2)
  | _ => fail nestNonValid

theorem nestPos_succ (dep kb : Nat) (e : EIdx) (ns : NestState) :
    ConRon.Arena.nestPos mode fe ctx (fuel + 1) prog dep kb e ns = (do
      let w ← whnf mode fe checkFuel dep e
      if !(← ConRon.Arena.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) w) then
        if ← ConRon.Arena.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) e then pure (.ordinary, w, ns)
        else pure (.ordinary, e, ns)
      else if w.tag == ETag.forallE then posBindT mode fe ctx fuel prog dep kb (ctx.hiAt prog.length) w ns
      else posAppT mode fe ctx fuel prog kb (ctx.hiAt prog.length) w ns) := by
  rw [ConRon.Arena.nestPos]; rfl


/-- The walk of one constructor's fields (`nest_ctors_walk`), the rest to `K`. -/
def walkK {β : Type} (root : Bool) (hi nF : Nat) (crest : EIdx) (ns : NestState)
    (K : List NestFieldKind → List EIdx → EIdx → NestState → EIdx → AM β) : AM β := do
  let (ks, nds, cur, ns2) ←
    if _h : root = true then do
      let fuelC ← ConRon.Arena.whnfWalkFuel crest
      ConRon.Arena.nestFields mode fe ctx fuelC prog hi nF 0 crest ns [] []
    else ConRon.Arena.nestFields mode fe ctx fuel prog hi nF 0 crest ns [] []
  let closed ← ConRon.Arena.closeTelescope nds hi cur
  K ks nds cur ns2 closed

/-- One constructor of `nestCtors` (`nest_ctors_one`), the rest to `K`. -/
def oneK {β : Type} (root : Bool) (hi : Nat) (us : LsIdx) (ds : List EIdx) (names : List NIdx)
    (holes : List EIdx) (cv : IConstantVal) (nF : Nat) (ns : NestState)
    (K : List NestFieldKind × EIdx → NestState → AM β) : AM β :=
  if !nameNodup cv.levelParams then
    fail (.invalid "nested positivity: invalid nested inductive datatype, its constructor has a duplicate universe level parameter (official: duplicate universe level parameter)")
  else do
    let cty ← instLPFast coreWalkFuel cv.levelParams us cv.type
    match ← ConRon.Arena.nestCrest names us ds holes cty with
    | none => fail (.invalid "nested positivity: invalid nested inductive datatype, its constructor type does not bind the parameters (official: ill-formed constructor)")
    | some crest => do
      let ty ← inferTypeCore mode fe checkFuel hi crest
      let _ ← ensureSortCore mode fe checkFuel hi ty
      walkK mode fe ctx fuel prog root hi nF crest ns fun ks _nds cur ns2 closed => do
        let u4 ← (List.range nF).anyM (u4F ks closed)
        if u4 then
          fail (.invalid "nested positivity: non valid occurrence of the datatypes being declared (a later field or the result depends on a recursive or nested field)")
        else do
          roK ctx hi cur fun resOk =>
            if !resOk then
              fail (.invalid "nested positivity: invalid return type — a constructor's result index mentions the block")
            else do
              let nf ← ConRon.Arena.nestCtorNf ctx prog us ds cv closed
              let ns3 := { ns2 with ctorNfs := ns2.ctorNfs.push nf }
              K (ks, closed) ns3

theorem nestCtors_cons (root : Bool) (hi : Nat) (us : LsIdx) (ds : List EIdx) (names : List NIdx)
    (holes : List EIdx) (cv : IConstantVal) (nF : Nat) (cs : List (IConstantVal × Nat)) (ns : NestState)
    (outs : List (List NestFieldKind × EIdx)) :
    ConRon.Arena.nestCtors mode fe ctx root fuel prog hi us ds names holes ((cv, nF) :: cs) ns outs =
      oneK mode fe ctx fuel prog root hi us ds names holes cv nF ns (fun o ns3 =>
        ConRon.Arena.nestCtors mode fe ctx root fuel prog hi us ds names holes cs ns3 (outs ++ [o])) := by
  rw [ConRon.Arena.nestCtors]; rfl

end pieces

end L.Ind
