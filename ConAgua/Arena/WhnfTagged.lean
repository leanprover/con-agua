import ConAgua.Arena.CoreWalks
import ConAgua.Arena.WhnfIotaRefine5
import ConAgua.Census.Attr

/-!
# The census-tagged statements whose stubs the verified walks discharge (lane `whnf2`)

The primed theorems take the callee specs they use as hypotheses (`InstListOK`,
`IotaInst1OK`); here they are instantiated with the walks' real refinements under `CoreS`
(`CoreWalks.lean`), given the walks' programs (`CoreWalkProg`). A theorem moves here when every
stub it used is discharged; the others keep instantiating the stub bundles where they are.
-/

open ConRon.Arena

namespace L.Arena

variable (p : Prog)

/-- **`beta_peel` refines `betaPeel t #[a] args i`.** -/
@[refines ConRon.Arena.betaPeel]
theorem betaPeel_refines (hp : WhnfCoreProg p) (hw : CoreWalkProg p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb t a ao an i : Word) (args : Array EIdx) (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (ht : HW t)
    (ha : HW a) (har : SpineR s₀.mem ao an args) (hlo : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpec p (n + 1) "beta_peel" [t, a, ao, an, i]
      (betaPeel (decE t) #[decE a] args i.toNat) decStep s₀ a₀ dn vis fe MM eb ResW :=
  betaPeel_refines' p hp hw.instListOK n s₀ a₀ dn vis fe MM eb t a ao an i args hS ht ha har hlo

/-- **`pi_residual` refines `piResidual`.** -/
@[refines ConRon.Arena.piResidual]
theorem piResidual_refinesT (hp : IotaProg' p) (hw : CoreWalkProg p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb e ao an : Word) (args : Array EIdx), CoreS dn s₀.mem a₀ vis fe MM eb →
    HW e → SpineR s₀.mem ao an args → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p n "pi_residual" [e, ao, an] (piResidual (decE e) args.toList) decOptR s₀ a₀ dn vis fe
      MM eb ResW :=
  piResidual_refines p hp hw.iotaInst1OK

/-- **`inst_spine` refines `instSpine coreWalkFuel`.** -/
@[refines ConRon.Arena.instSpine]
theorem instSpine_refines (hp : IotaProg' p) (hw : CoreWalkProg p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb ao an t e : Word) (args : Array EIdx), CoreS dn s₀.mem a₀ vis fe MM eb →
    HW e → SpineR s₀.mem ao an args → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    an.toNat ≤ t.toNat + 1 →
    CoreSpec p n "inst_spine" [ao, an, t, e] (instSpine coreWalkFuel args.toList t.toNat (decE e))
      decH s₀ a₀ dn vis fe MM eb :=
  instSpine_refines' p hp hw.iotaInst1OK

/-- **`iota_index_ok` refines `iotaIndexOk`** (the knot one level down as `KnotUpTo`). -/
@[refines ConRon.Arena.iotaIndexOk]
theorem iotaIndexOk_refines (hp : IotaProg' p) (hw : CoreWalkProg p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d mI rP cnP tyCtor mo mn xo xn : Word) (margs idx : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW tyCtor →
    SpineR s₀.mem mo mn margs → SpineR s₀.mem xo xn idx →
    mo.toNat + mn.toNat ≤ (spTop s₀.mem).toNat → xo.toNat + xn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p (n + 1) "iota_index_ok" [mode, vis, d, mI, rP, cnP, tyCtor, mo, mn, xo, xn]
      (iotaIndexOk (coreKnot (decMode mode) fe id F) fe d.toNat mI.toNat rP.toNat cnP.toNat
        (decE tyCtor) margs.toList idx.toList) decBool s₀ a₀ dn vis fe MM eb :=
  iotaIndexOk_refines' p hp hw.iotaInst1OK

/-- **`iota_certs_full_aux` refines `iotaCertsFullAux`.** -/
@[refines ConRon.Arena.iotaCertsFullAux]
theorem iotaCertsFullAux_refines (hp : IotaProg4 p) (hw : CoreWalkProg p) (n : Nat) :
    ICFSpec p "iota_certs_full_aux" (fun _ _ _ => True) n :=
  iotaCertsFullAux_refines' p hp hw.instListOK n

/-- **`iota_certs_full` refines `iotaCertsFull`.** -/
@[refines ConRon.Arena.iotaCertsFull]
theorem iotaCertsFull_refines (hp : IotaProg4 p) (hw : CoreWalkProg p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h ao an : Word) (args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW h →
    SpineR s₀.mem ao an args → ao + an = spTop s₀.mem →
    CoreSpec p (n + 1) "iota_certs_full" [mode, vis, d, h, ao, an]
      (iotaCertsFull (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) args.toList) decBool s₀
      a₀ dn vis fe MM eb :=
  iotaCertsFull_refines' p hp hw.instListOK

end L.Arena
