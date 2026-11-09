module

public import ConRon.Bridge.Checker.DeclVal
public import ConRon.Bridge.Checker.TypePins
public import ConAgua.Arena.DeclDivModSpec.BoolCtorTyped
import ConAgua.Arena.DeclDivModSpec.CertDivModEqs
import ConAgua.Arena.DeclDivModSpec.CertTwoEqs
public import ConAgua.Arena.DeclDivModSpec.SubstConst0List
public import ConAgua.Arena.CrOKFrame
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.StageC
public import ConRon.Bridge.Checker.DivMod
import all ConRon.Bridge.Checker.DivMod
import ConAgua.Arena.DeclNatGate
import ConAgua.Arena.IndInstallSpec.DomsW
public import ConAgua.Arena.LeafFns
public import ConAgua.Arena.TwinStep

@[expose] public section

/-!
# The `Nat.div`-family pin gate under `StageC`, part 1: the guards (lane `loopt3`, `loopt3-div`)

`div_mod_pin_guard` (`pgC`) and `div_mod_cert_guard` (`cgC`) under `StageC`: their leaves by their
`StageR` refinements (`DeclDivModSpec/`), the leaves' write set and con-ron's step lemmas
(`StageC.of_core`), the walks the stubs stand for by their `StageT` refinements (`IndRealWalkT.lean`, `apdF_okT`,
`crfF_okT` with `consts_resolve_ffast`'s memo threaded: `CrKeep`, `CrOKFrame.lean`)
and con-ron's `RunsC` lemmas (`lbbF_runsC`, `hasFvarF_runsC`, `alpd0_runsC`, `crF_runsC`). The twin
side follows con-ron's `divModPinGuard_run` and `divModCertGuard_run` (`Bridge/Checker/DivMod.lean`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Ind

open L.Arena
open L.Rom (PinSetsR PinSetR)
open ConRon.Bridge (CheckOK StepOK PinsDenote PinSetDenote CoreStep)

local notation "V" => ConLeche.CheckMode.verified

section helpers
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

/-- **`StageC` across a leaf whose twin op is a `CoreStep`** (`StageC.of_leaf` for twin ops that
read through the walks' memos: con-ron gives `CheckOK` after rather than `IStepS`). -/
theorem StageC.of_core {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR vis fe m' a') (hf : MemFrame leafA leafC m m') (hc : CoreStep env fe a a') :
    StageC dn vis fe env m' a' := by
  sorry


/-- `CallRef.bindL` with `consts_resolve_ffast`'s memo carried across the leaf (`CrKeep.call`). -/
theorem CallRef.bindLC {α β : Type} {p : Prog} {f : FnName} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : CallRef p f args pre op post) (hcl : LeafClosed p) (hf : f ∈ leafFns) (hkp : CrKeep p)
    (hfi : f ∈ imFns) {n : Nat} {m : Mem} {a : AState} (hpre : pre m a) (hCr : L.Stubs.CrOK m)
    {K : List Word → Mem → Option β} {res : β} (hw : ntBW (callW p n f args m) K = some res) :
    ∃ r1 m1 x a1, op.run a = .ok (x, a1) ∧ post m m1 a1 r1 x ∧ MemFrame leafA leafC m m1 ∧
      L.Stubs.CrOK m1 ∧ K r1 m1 = some res := by
  sorry

/-- A twin op running as a `CoreStep`, from a `RunsC` fact. -/
theorem runsC_step {m : AM Bool} {a a' : AState} {b x : Bool}
    (h : ConRon.Bridge.RunsC env fe m a b) (hr : m.run a = .ok (x, a')) :
    CoreStep env fe a a' ∧ x = b := by
  sorry


end helpers

/-! ## `ground_guards` -/

section gg
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`ground_guards` under `StageC`** (con-ron's `pinGuardWalk_run`): the four walks by their
`StageT` contracts and con-ron's `RunsC` lemmas. -/
theorem ggC (hD : DmProg6 p) (hkp : CrKeep p) {pe : Word} {P : ConLeche.Expr} {k : Nat}
    {m m' : Mem} {a : AState} {r : List Word}
    (hcall : callW p k "ground_guards" [vis, pe] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hl1 : H pe) (hpd : denoteE a.store (decI pe) = some P)
    (hCr : L.Stubs.CrOK m) :
    ∃ x a', (groundGuards fe (decI pe)).run a = .ok (x, a') ∧ StageC dn vis fe env m' a' ∧
      CoreStep env fe a a' ∧ IWGrow m m' ∧ decW0B m' r x ∧
      x = (P.looseBVarsBounded 0 && (!P.hasFvar && (P.allLevelParamsDefined [] &&
        P.constsResolve env))) := by
  sorry


end gg

/-! ## `type_pin_guard`, `type_pins_guard` -/

section tpg
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`type_pin_guard` under `StageC`** (con-ron's `typePinGuard_spec`): the lookup, the stored
type by `tps_ref` and con-ron's `typePinStored_spec`, the walks by their `StageT` contracts and
con-ron's `RunsC` lemmas. -/
theorem tpgC (hD : DmProg6 p) (hcl : LeafClosed p) (hkp : CrKeep p) {nw ty : Word}
    {nm : ConLeche.Name} {T : ConLeche.Expr} {k : Nat} {m m' : Mem} {a : AState} {r : List Word}
    (hcall : callW p k "type_pin_guard" [vis, nw, ty] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hn1 : H nw) (hl1 : H ty)
    (hn : denoteN a.store.ns (decI nw) = some nm) (ht : denoteE a.store (decI ty) = some T)
    (hCr : L.Stubs.CrOK m) :
    ∃ x a', (typePinGuard fe (decI nw) (decI ty)).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ CoreStep env fe a a' ∧ IWGrow m m' ∧ decW0B m' r x := by
  sorry


/-- **`type_pins_guard` under `StageC`** (con-ron's `typePinsGuard_spec`): `tpgC` on each pair of
the `EREC` slice. -/
theorem tpsgC (hD : DmProg6 p) (hcl : LeafClosed p) (hkp : CrKeep p) :
    ∀ (tps : List (NIdx × EIdx)) (tpsP : List (ConLeche.Name × ConLeche.Expr)) (o l : Word)
      (k : Nat) (m : Mem) (a : AState) (res : List Word) (m' : Mem),
      StageC dn vis fe env m a → L.Stubs.CrOK m → L.Rom.TPinsR m o l tps →
      ConRon.Bridge.TypePinsDenote a.store tps tpsP →
      callW p k "type_pins_guard" [vis, o, l] m = some (res, m') →
      ∃ x a', (typePinsGuard fe tps).run a = .ok (x, a') ∧ StageC dn vis fe env m' a' ∧
        CoreStep env fe a a' ∧ IWGrow m m' ∧ decW0B m' res x := by
  sorry


end tpg

/-! ## `div_mod_pin_guard` -/

section pg
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`div_mod_pin_guard` under `StageC`** (con-ron's `divModPinGuard_run`): the pin and the
type pins by their `StageR` refinements and con-ron's choice lemmas, the guards by `ggC` and
`tpsgC`. -/
theorem pgC (hD : DmProg6 p) (hcl : LeafClosed p) (hkp : CrKeep p) {ps c : Word} {ip : INatOpPinSet}
    {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name} {k : Nat} {m m' : Mem} {a : AState}
    {r : List Word} (hcall : callW p k "div_mod_pin_guard" [ps, vis, c] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hc : H c) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hCr : L.Stubs.CrOK m) :
    ∃ x a', (divModPinGuard ip fe (decI c)).run a = .ok (x, a') ∧ StageC dn vis fe env m' a' ∧
      CoreStep env fe a a' ∧ IWGrow m m' ∧ decW0B m' r x ∧
      x = ConLeche.divModPinGuard psP env nm := by
  sorry


end pg

/-! ## `div_mod_cert_guard` -/

section cg
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`consts_resolve_all` under `StageT`** (`cra_ref`'s, `consts_resolve_ffast` by `crfF_okT`
with its memo `CrOK` threaded). -/
theorem cra_refT (hD : DmProg5 p) (hkp : CrKeep p) :
    ∀ (hyps : List EIdx) (o l : Word) (k : Nat) (m : Mem) (a : AState) (res : List Word) (m' : Mem),
      StageT dn vis fe m a → L.Stubs.CrOK m → decHL m o.toNat l.toNat = some hyps →
      o.toNat + l.toNat ≤ iwTop m →
      callW p k "consts_resolve_all" [vis, o, l] m = some (res, m') →
      ∃ x a', (constsResolveAll fe hyps).run a = .ok (x, a') ∧
        KeepPostT dn vis fe decW0B m m' a' res x ∧ L.Stubs.CrOK m' := by
  sorry

/-- **`div_mod_cert_guard` under `StageC`** (`cg_ref`'s; con-ron's `divModCertGuard_run`): the
substitutions and `consts_resolve_all` by `StageC.of_core`, the walks by their `StageT` contracts. -/
theorem cgC (hD : DmProg5 p) (hcl : LeafClosed p) (hkp : CrKeep p) (hs0 : SubstC0 p vis fe)
    (hsA : SubstCAll p vis fe) {c annVal ho hl eqE proof : Word} {hyps : List EIdx}
    {nm : ConLeche.Name} {v ex px : ConLeche.Expr} {hx : List ConLeche.Expr} {k : Nat} {m m' : Mem}
    {a : AState} {r : List Word}
    (hcall : callW p k "div_mod_cert_guard" [vis, c, annVal, ho, hl, eqE, proof] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hc : H c) (hann : H annVal) (heq : H eqE) (hpr : H proof)
    (hd : decHL m ho.toNat hl.toNat = some hyps) (hb : ho.toNat + hl.toNat ≤ iwTop m)
    (hn : denoteN a.store.ns (decI c) = some nm) (hv : denoteE a.store (decE annVal) = some v)
    (hh : Frontend.denoteEList a.store hyps = some hx) (he : denoteE a.store (decE eqE) = some ex)
    (hpf : denoteE a.store (decE proof) = some px) (hCr : L.Stubs.CrOK m) :
    ∃ x a', (divModCertGuard fe (decI c) (decE annVal) hyps (decE eqE) (decE proof)).run a =
        .ok (x, a') ∧ StageC dn vis fe env m' a' ∧ CoreStep env fe a a' ∧ IWGrow m m' ∧
      decW0B m' r x ∧ x = ConLeche.divModCertGuard env nm v hx ex px := by
  sorry


end cg

/-! ## `div_mod_certs_guard_go`, `div_mod_certs_guard` -/

section cgs
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`div_mod_certs_guard_go` under `StageC`** (`cggo_ref`'s; con-ron's `divModCertsGuardGo_run`). -/
theorem cggoC (hD : DmProg6 p) (hcl : LeafClosed p) (hkp : CrKeep p) (hs0 : SubstC0 p vis fe)
    (hsA : SubstCAll p vis fe) (c annVal : Word) (hc : H c) (hann : H annVal)
    {nm : ConLeche.Name} {v : ConLeche.Expr} :
    ∀ (ss : List (List EIdx × EIdx)) (xs : List (List ConLeche.Expr × ConLeche.Expr))
      (proofs : List EIdx) (ps : List ConLeche.Expr) (so sl po pl : Word) (k : Nat) (m : Mem)
      (a : AState) (res : List Word) (m' : Mem), StageC dn vis fe env m a → L.Stubs.CrOK m →
      StmtL m so.toNat sl.toNat ss → decHL m po.toNat pl.toNat = some proofs →
      po.toNat + pl.toNat ≤ iwTop m → denoteN a.store.ns (decI c) = some nm →
      denoteE a.store (decE annVal) = some v → ConRon.Bridge.StmtsDenote a.store ss xs →
      Frontend.denoteEList a.store proofs = some ps →
      callW p k "div_mod_certs_guard_go" [vis, c, annVal, so, sl, po, pl] m = some (res, m') →
      ∃ x a', (divModCertsGuardGo fe (decI c) (decE annVal) ss proofs).run a = .ok (x, a') ∧
        StageC dn vis fe env m' a' ∧ CoreStep env fe a a' ∧ IWGrow m m' ∧ decW0B m' res x := by
  sorry


/-- **`div_mod_certs_guard` under `StageC`** (`cgs_ref`'s; con-ron's `divModCertsGuard_run`). -/
theorem cgsC (hD : DmProg6 p) (hcl : LeafClosed p) (hkp : CrKeep p) (hs0 : SubstC0 p vis fe)
    (hsA : SubstCAll p vis fe) {ps c annVal : Word} {ip : INatOpPinSet}
    {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name} {v : ConLeche.Expr} {k : Nat} {m m' : Mem}
    {a : AState} {r : List Word}
    (hcall : callW p k "div_mod_certs_guard" [ps, vis, c, annVal] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hc : H c) (hann : H annVal) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE annVal) = some v) (hCr : L.Stubs.CrOK m) :
    ∃ x a', (divModCertsGuard ip fe (decI c) (decE annVal)).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ CoreStep env fe a a' ∧ IWGrow m m' ∧ decW0B m' r x := by
  sorry


end cgs

end L.Ind
