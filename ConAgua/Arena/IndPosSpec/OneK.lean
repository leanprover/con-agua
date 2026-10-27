import ConAgua.Arena.IndPosSpec.PfLook
import ConAgua.Arena.IndPosSpec.PosBindT

/-!
# OneK

`posAppT`, `nestPos_succ`, `oneK`, `nestCtors_cons`.
-/

noncomputable section

open ConRon.Arena
open ConLeche (CheckMode)

namespace L.Ind

section pieces
variable (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) (fuel : Nat) (prog : List NestHole)

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

end
