import ConAgua.Arena.DefEqKnot

/-!
# The whnf family's census-tagged refinements, through the knot (lane `knotwire`)

Lane `whnf` stated each refinement of the whnf family over callee bundles (`WhnfCallees`,
`CoreCallees`, `IotaCallees`, `ProjCallees`, `SupKeep`) and tagged a copy that instantiated them
with `sorry`'d stubs (`whnfCallees_stub`, `coreCallees_stub`, `iotaCallees_stub`,
`supKeep_twin`). `DefEqKnot.lean` builds every bundle from real proofs under `KnotAllProg p`
(program lookups only), so the tagged statements are restated here over `KnotAllProg p` and the
stubs are gone. Each statement is the old one with its program hypotheses (`WhnfCoreProg`,
`IotaProg'`, `M2CProg'`, `WhnfDeltaProg'`, the write-set fact `hcl`) replaced by `KnotAllProg p`;
names and tags are unchanged.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section tagged
variable {p : Prog} (hq : KnotAllProg p)

/-! ## `whnf_core` (`WhnfCoreLoop`, `WhnfCoreProj`, `WhnfCoreAppLoop`) -/

include hq in
/-- **`whnf_core_step` refines `whnfCoreStep`.** -/
@[refines ConRon.Arena.whnfCoreStep]
theorem whnfCoreStep_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode cheap d e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (he : HW e) :
    CoreSpec p (n + 1) "whnf_core_step" [mode, cheap, vis, d, e]
      (whnfCoreStep (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e)) decStep s₀ a₀ dn vis fe MM eb ResW :=
  whnfCoreStep_refines' p hq.core (KnotAllProg.whnfC hq) (KnotAllProg.coreC hq) supKeep_of n hk F
    hF hn s₀ a₀ dn vis fe MM eb mode cheap d e hs he

include hq in
/-- **`whnf_core_loop` refines `whnfCoreLoop` at every twin loop fuel `K ≥ n`.** -/
@[refines ConRon.Arena.whnfCoreLoop]
theorem whnfCoreLoop_refines (n : Nat) (hk : KnotUpTo p n) (F K : Nat) (hF : n ≤ F) (hK : n ≤ K)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode cheap d e : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpec p (n + 1) "whnf_core_loop" [mode, cheap, vis, d, e]
      (whnfCoreLoop (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat K
        (decE e)) decH s₀ a₀ dn vis fe MM eb :=
  whnfCoreLoop_refines' p hq.core (KnotAllProg.whnfC hq) (KnotAllProg.coreC hq) supKeep_of n hk F K
    hF hK hn s₀ a₀ dn vis fe MM eb mode cheap d e hs he

include hq in
/-- **`whnf_core_loop` refines `whnfCoreBody`** (the loop at `whnfCoreLoopFuel = 2^62`). -/
@[refines ConRon.Arena.whnfCoreBody]
theorem whnfCoreBody_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode cheap d e : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpec p (n + 1) "whnf_core_loop" [mode, cheap, vis, d, e]
      (whnfCoreBody (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e)) decH s₀ a₀ dn vis fe MM eb :=
  whnfCoreBody_refines' p hq.core (KnotAllProg.whnfC hq) (KnotAllProg.coreC hq) supKeep_of n hk F
    hF hn s₀ a₀ dn vis fe MM eb mode cheap d e hs he

include hq in
/-- **`whnf_core_step_proj` refines `whnfCoreStepProj`.** -/
@[refines ConRon.Arena.whnfCoreStepProj]
theorem whnfCoreStepProj_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode cheap d e sn i pe : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) (hsn : HW sn) (hpe : HW pe) :
    CoreSpec p (n + 1) "whnf_core_step_proj" [mode, cheap, vis, d, e, sn, i, pe]
      (whnfCoreStepProj (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e) (decI sn) i.toNat (decE pe)) decStep s₀ a₀ dn vis fe MM eb ResW :=
  whnfCoreStepProj_refines' p hq.core (KnotAllProg.whnfC hq).strLitSupported
    (KnotAllProg.whnfC hq).strLitCtor (KnotAllProg.projC hq) hq.core.lsn (erecKept_of hq.hcl) n hk
    F hF hn s₀ a₀ dn vis fe MM eb mode cheap d e sn i pe hs he hsn hpe (supKeep_of fe)

include hq in
/-- **`reduce_proj_core` refines `reduceProjCore`.** -/
@[refines ConRon.Arena.reduceProjCore]
theorem reduceProjCore_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d sn i c : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hsn : HW sn) (hc' : HW c) :
    CoreSpec p (n + 1) "reduce_proj_core" [mode, vis, d, sn, i, c]
      (reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE c)) decOptR s₀ a₀ dn vis fe MM eb ResW :=
  KnotAllProg.reduceProjCore hq n hk F hF hn s₀ a₀ dn vis fe MM eb mode d sn i c hs hsn hc'

include hq in
/-- **`proj_lit_to_ctor` refines `projLitToCtor`.** -/
@[refines ConRon.Arena.projLitToCtor]
theorem projLitToCtor_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d h : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hh : HW h) :
    CoreSpec p (n + 1) "proj_lit_to_ctor" [mode, vis, d, h]
      (projLitToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE h)) decH s₀ a₀ dn vis fe
      MM eb :=
  projLitToCtor_refines' p hq.core (KnotAllProg.whnfC hq).strLitSupported
    (KnotAllProg.whnfC hq).strLitCtor n hk F hF hn s₀ a₀ dn vis fe MM eb mode d h hs hh
    (supKeep_of fe)

include hq in
/-- **`whnf_app` refines `whnfApp`**: `vargs` the slice `(vo, vn)` at the top of the stack, the
spine's arguments and nodes the slices `(ao, an)`, `(ao + an, an)` below it. -/
@[refines ConRon.Arena.whnfApp]
theorem whnfApp_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d v hd vo vn same ao an i : Word)
    (vargs args nodes : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hv : HW v)
    (hhd : HW hd) (hva : SpineR s₀.mem vo vn vargs) (htop : spTop s₀.mem = vo + vn)
    (har : SpineR s₀.mem ao an args) (hno : SpineR s₀.mem (ao + an) an nodes)
    (hlo : ao.toNat + an.toNat + an.toNat ≤ vo.toNat) :
    CoreSpec p (n + 1) "whnf_app" [mode, vis, d, v, hd, vo, vn, same, ao, an, i]
      (whnfApp (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v) (decE hd) vargs
        (same != 0) args nodes i.toNat) decStep s₀ a₀ dn vis fe MM eb ResW :=
  whnfApp_refines' p hq.core (KnotAllProg.whnfC hq) (KnotAllProg.coreC hq) n hk F hF hn s₀ a₀ dn vis
    fe MM eb mode d v hd vo vn same ao an i vargs args nodes hs hv hhd hva htop har hno hlo

/-! ## δ (`WhnfDeltaRefine4`) -/

include hq in
@[refines ConRon.Arena.constValAt]
theorem constValAt_refines (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb nm po pl value us : Word) (lps : List NIdx)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hnm : HW nm) (hv : HW value) (hu : HW us)
    (hlps : hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps) :
    CoreSpec p n "const_val_at" [nm, po, pl, value, us]
      (constValAt (decI nm) lps (decE value) (decI us)) decH s₀ a₀ dn vis fe MM eb :=
  constValAt_refines' p hq.delta.toWhnfDeltaProg n s₀ a₀ dn vis fe MM eb nm po pl value us lps hC
    hnm hv hu hq.instLP hlps

include hq in
@[refines ConRon.Arena.unfoldDefinition]
theorem unfoldDefinition_refines (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb e : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) :
    CoreSpec p n "unfold_definition" [vis, e] (unfoldDefinition fe (decE e)) decOptR s₀ a₀ dn vis fe
      MM eb ResW :=
  KnotAllProg.unfold hq n s₀ a₀ dn vis fe MM eb e hC he

include hq in
@[refines ConRon.Arena.whnfStep]
theorem whnfStep_refines (n : Nat) : WhnfStepSpec' p n :=
  whnfStep_refines' p hq.delta hq.instLP n (fun k _ => reduceNat_refines p hq.delta k)

/-! ## ι (`WhnfIotaRefine*`, `WhnfIotaRecRefine3`, `WhnfM2CRefine5`) -/

include hq in
@[refines ConRon.Arena.constTyAt]
theorem constTyAt_refines : ConstTyAtOK p := KnotAllProg.constTy hq

include hq in
@[refines ConRon.Arena.ruleRhsAt]
theorem ruleRhsAt_refines : RuleRhsAtOK p := ruleRhsAt_refines' p hq.body.iota hq.instLP

include hq in
@[refines ConRon.Arena.instSpinePins]
theorem instSpinePins_refines :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb po pl us ao an rP pvo pvc : Word) (lps : List NIdx) (args pins : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW us →
    hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps → SpineR s₀.mem ao an args →
    SpineR s₀.mem pvo pvc pins → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    pvo.toNat + pvc.toNat ≤ (spTop s₀.mem).toNat →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "inst_spine_pins" [po, pl, us, ao, an, rP, pvo, pvc]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (instSpinePins lps (decI us) args.toList rP.toNat pins.toList) a₀ ∧
      CoreAfterG dn s₀.mem s'.mem
        (AM.st (instSpinePins lps (decI us) args.toList rP.toNat pins.toList) a₀) vis fe MM eb ∧
      ∃ xs, AM.res (instSpinePins lps (decI us) args.toList rP.toNat pins.toList) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄ :=
  instSpinePins_refines' p hq.body.iota (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq)
    (ErecKeptInst.of_closed hq.hcl)

include hq in
@[refines ConRon.Arena.recFireArgs]
theorem recFireArgs_refines :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb fireKind pvo pvc po pc us ao an rP ctorParams : Word) (rl : IRecRule)
    (lps : List NIdx) (args : Array EIdx), CoreS dn s₀.mem a₀ vis fe MM eb → HW us →
    hslice? (s₀.mem.arr64 EREC) po.toNat pc.toNat = some lps → SpineR s₀.mem ao an args →
    (fireKind = 1 → ∃ lvls pins, rl.fire = .nested lvls pins ∧ SpineR s₀.mem pvo pvc pins.toArray) →
    (fireKind ≠ 1 → rl.fire = .plain) → rl.ctorParams = ctorParams.toNat →
    ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    (fireKind = 1 → pvo.toNat + pvc.toNat ≤ (spTop s₀.mem).toNat) →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_fire_args" [fireKind, pvo, pvc, po, pc, us, ao, an, rP, ctorParams]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (recFireArgs rl lps (decI us) args.toList rP.toNat) a₀ ∧
      CoreAfterG dn s₀.mem s'.mem (AM.st (recFireArgs rl lps (decI us) args.toList rP.toNat) a₀) vis
        fe MM eb ∧
      ∃ xs, AM.res (recFireArgs rl lps (decI us) args.toList rP.toNat) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄ :=
  recFireArgs_refines' p hq.body.iota (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq)
    (ErecKeptInst.of_closed hq.hcl)

include hq in
@[refines ConRon.Arena.andRescueSlots]
theorem andRescueSlots_refines : AndRescueSlotsOK p :=
  andRescueSlots_refines' p hq.body.iota (KnotAllProg.projC hq)

include hq in
@[refines ConRon.Arena.fabScopeOk]
theorem fabScopeOk_refines : FabScopeOkOK p :=
  fabScopeOk_refines' p hq.body.iota (KnotAllProg.iotaC hq)

include hq in
@[refines ConRon.Arena.litMajorToCtor]
theorem litMajorToCtor_refines :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
    eb = (mode >>> 1) &&& 1 → HW h →
    CoreSpec p (n + 1) "lit_major_to_ctor" [mode, vis, d, h]
      (litMajorToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE h)) decH s₀ a₀ dn vis fe MM
      eb :=
  litMajorToCtor_refines' p hq.body.iota (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq) supKeep_of

include hq in
@[refines ConRon.Arena.majorToCtor]
theorem majorToCtor_refines : MajorToCtorOK p :=
  majorToCtor_refines' p hq.m2c (KnotAllProg.iotaC hq) (KnotAllProg.proofIrrel hq)
    (ErecKeptKnot.of_closed hq.hcl) (KnotAllProg.projC hq)

include hq in
@[refines ConRon.Arena.prepareMajor]
theorem prepareMajor_refines :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec ro rc major : Word) (rules : List IRecRule),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW major →
    decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules →
    CoreSpec p (n + 1) "prepare_major" [mode, vis, d, rec, ro, rc, major]
      (prepareMajor (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI rec) rules
        (decE major)) decH s₀ a₀ dn vis fe MM eb :=
  prepareMajor_refines' p hq.m2c.toIotaProg4 (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq) supKeep_of
    (majorToCtor_refines hq) (ErecKeptKnot.of_closed hq.hcl)

include hq in
/-- **`iota_rec_at` refines `iotaRecAt`** (the statement is `WhnfCore.lean`'s `IotaRecAtOK`, what
`whnf_app` assumes). -/
@[refines ConRon.Arena.iotaRecAt]
theorem iotaRecAt_refines (n : Nat) (hk : KnotUpTo p n) : IotaRecAtOK p (n + 1) :=
  KnotAllProg.iota hq n hk

end tagged

end L.Arena
