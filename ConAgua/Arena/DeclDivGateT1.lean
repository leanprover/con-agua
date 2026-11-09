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
import ConAgua.Arena.DeclNatGateT
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
    StageC dn vis fe env m' a' :=
  ⟨hS, hc.ok,
    ⟨by rw [hf.size]; exact h.mem.erec, by rw [hf.size]; exact h.mem.spn,
      by rw [hf.size]; exact h.mem.bstk,
      h.mem.memos.frame hf leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp,
      fun k x e => hc.ext.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    by simp only [pinW, hf.arr PINS leafA_pins (by decide)]; exact h.flag⟩


/-- `CallRef.bindL` with `consts_resolve_ffast`'s memo carried across the leaf (`CrKeep.call`). -/
theorem CallRef.bindLC {α β : Type} {p : Prog} {f : FnName} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : CallRef p f args pre op post) (hcl : LeafClosed p) (hf : f ∈ leafFns) (hkp : CrKeep p)
    (hfi : f ∈ imFns) {n : Nat} {m : Mem} {a : AState} (hpre : pre m a) (hCr : L.Stubs.CrOK m)
    {K : List Word → Mem → Option β} {res : β} (hw : ntBW (callW p n f args m) K = some res) :
    ∃ r1 m1 x a1, op.run a = .ok (x, a1) ∧ post m m1 a1 r1 x ∧ MemFrame leafA leafC m m1 ∧
      L.Stubs.CrOK m1 ∧ K r1 m1 = some res := by
  cases hc : callW p n f args m with
  | none => rw [hc] at hw; simp at hw
  | some q =>
    obtain ⟨r1, m1⟩ := q
    rw [hc, bW_some] at hw
    obtain ⟨x, a1, hr, hp⟩ := h n m a r1 m1 hpre hc
    exact ⟨r1, m1, x, a1, hr, hp, callW_leafFrame hcl hf hc, hkp.call hfi hc hCr, hw⟩

/-- A twin op running as a `CoreStep`, from a `RunsC` fact. -/
theorem runsC_step {m : AM Bool} {a a' : AState} {b x : Bool}
    (h : ConRon.Bridge.RunsC env fe m a b) (hr : m.run a = .ok (x, a')) :
    CoreStep env fe a a' ∧ x = b :=
  h x a' hr


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
  cases k with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ k =>
  have hw := callW_model (M := fun mq => dmPgW p (k + 1) mq ps vis c)
    (pg_specW p hD.lDivModPinGuard (k + 1) · ps vis c) hcall
  rw [dmPgW.arm1] at hw
  have fin : ∀ x a', (divModPinGuard ip fe (decI c)).run a = .ok (x, a') →
      CoreStep env fe a a' ∧ x = ConLeche.divModPinGuard psP env nm := fun x a' hr => by
    obtain ⟨h1, h2, h3, h4⟩ := ConRon.Bridge.divModPinGuard_run hC.check hps hn hr
    exact ⟨⟨h1, h2, h3⟩, h4⟩
  -- the pin
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1, hx1⟩, hf1, hCr1, hw⟩ :=
    (divModDeclPin_ref hD.toDmProg5.toDmProg2.toDmProg1 ps c ip).bindLC hcl
      (leaf_mem _ (by decide)) hkp (im_mem _ rfl) ⟨hC.stage, hc, hP⟩ hCr hw
  obtain ⟨e1, hpd⟩ := ConRon.Bridge.divModDeclPin_run hC.check.state hC.check.pins hps hn hrun1
  rw [e1] at hrun1 hS1
  have hC1 := StageC.of_core hC hS1 hf1 (CoreStep.refl hC.check)
  rw [← hx1] at hpd
  have hrun1' : (divModDeclPin ip (decI c)).run a = .ok (decI (r1.headD 0), a) := by
    rw [hx1]; exact hrun1
  -- the ground guards
  replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
  obtain ⟨x2, a2, hrun2, hC2, c2, hg2, hd2, -⟩ := ggC hD hkp h2 hC1 hl1 hpd hCr1
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
  by_cases z2 : r2.headD 0 = 0
  · rw [ite_eq_left z2] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx2 := decW0B_false hd2 z2
    have hrun : (divModPinGuard ip fe (decI c)).run a = .ok (false, a2) := by
      simp only [divModPinGuard, StateT.run_bind, hrun1', exc_ok_bind', hrun2, hx2,
        Bool.false_eq_true, ite_false]
      rfl
    obtain ⟨cs, hx⟩ := fin _ _ hrun
    exact ⟨false, a2, hrun, hC2, cs, hg1.trans hg2, decW0B_of_false _, hx⟩
  rw [ite_eq_right z2] at hw
  have hx2 := decW0B_true hd2 z2
  -- the type pins
  have hP2 := PinSetR.grow hP (hg1.trans hg2)
  have hps2 := (ConRon.Bridge.PinsDenote.mono c2.ext [ip] [psP] ⟨hps, trivial⟩).1
  have hn2 := ConRon.Bridge.denoteN_ext hn c2.ext
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hd3⟩, hf3, hCr3, hw⟩ :=
    (divModTypePins_ref hD.toDmProg5.toDmProg2.toDmProg1 ps c ip).bindLC hcl
      (leaf_mem _ (by decide)) hkp (im_mem _ rfl) ⟨hC2.stage, hc, hP2⟩ hCr2 hw
  obtain ⟨e3, htd⟩ := ConRon.Bridge.divModTypePins_run hC2.check.state hC2.check.pins hps2 hn2 hrun3
  rw [e3] at hrun3 hS3
  have hC3 := StageC.of_core hC2 hS3 hf3 (CoreStep.refl hC2.check)
  replace hw := ntBW_some hw; obtain ⟨r4, m4, h4, hw⟩ := hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨x4, a4, hrun4, hC4, c4, hg4, hd4⟩ := tpsgC hD hcl hkp x3 _ _ _ k m3 a2 r4 m4 hC3 hCr3
    hd3 htd h4
  have hrun : (divModPinGuard ip fe (decI c)).run a = .ok (x4, a4) := by
    simp only [divModPinGuard, StateT.run_bind, hrun1', exc_ok_bind', hrun2, hx2, ite_true, hrun3]
    exact hrun4
  obtain ⟨cs, hx⟩ := fin _ _ hrun
  exact ⟨x4, a4, hrun, hC4, cs, hg1.trans (hg2.trans (hg3.trans hg4)), hd4, hx⟩

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
  intro ss
  induction ss with
  | nil =>
    intro xs proofs ps so sl po pl k m a res m' hC _ hs hd hb hn hv hsd hpr hc'
    have hsl : sl = 0 := UInt64.toNat_inj.mp (by have := hs.2.1; simpa using this)
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hw := callW_model (M := fun mq => cggoW p (k + 1) mq vis c annVal so sl po pl)
      (cggo_specW p hD.lCertsGuardGo (k + 1) · vis c annVal so sl po pl) hc'
    simp only [cggoW.eq_2, hsl, true_or, ite_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨true, a, by cases proofs <;> rfl, hC, CoreStep.refl hC.check, IWGrow.refl _,
      by simp [decW0B]⟩
  | cons st ss ih =>
    rcases st with ⟨hy, eqq⟩
    intro xs proofs ps so sl po pl k m a res m' hC hCr hs hd hb hn hv hsd hpr hc'
    cases xs with
    | nil => exact hsd.elim
    | cons xq xrest =>
    obtain ⟨hx, ex⟩ := xq
    obtain ⟨hsd1, hsd2, hsd3⟩ := hsd
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hw := callW_model (M := fun mq => cggoW p (k + 1) mq vis c annVal so sl po pl)
      (cggo_specW p hD.lCertsGuardGo (k + 1) · vis c annVal so sl po pl) hc'
    rw [cggoW.eq_2] at hw
    have hS := hC.stage
    cases proofs with
    | nil =>
      have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := decHL_length m hd; simp at this ⊢; omega)
      simp only [hpl, or_true, ite_true, Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨true, a, rfl, hC, CoreStep.refl hC.check, IWGrow.refl _, by simp [decW0B]⟩
    | cons pf pfs =>
    obtain ⟨px, pxs, hpx, hpxs, rfl⟩ := ConRon.Bridge.denoteEList_cons hpr
    obtain ⟨hsl0, q, hq, hstm, hrest⟩ := StmtL.cons hS.iw hs
    obtain ⟨hpl0, hpwlt, hpf, hdrest⟩ := decHL_cons_iw hS.iw.iwSize hd
    subst hpf
    obtain ⟨ho, hl, e, hr3, hbd, hdh, he, hst2⟩ := hstm
    obtain ⟨hp3, h0, h1, h2⟩ := hr3
    have hst2' : eqq = decE e := hst2
    subst hst2'
    rw [ite_eq_right (by simp [hsl0, hpl0])] at hw
    have hsz := hS.iw.iwSize
    have hI1 := hS.iw.iw
    have r0 : rdW (m.arr64 IW) so = q := hq
    have rq1 : rdW (m.arr64 IW) q = ho := rdW_iw_of h0 rfl
    have rq2 : rdW (m.arr64 IW) (q + 1) = hl :=
      rdW_iw_of h1 (word_add_one (by omega))
    have rq3 : rdW (m.arr64 IW) (q + 2) = e :=
      rdW_iw_of h2 (word_add_two (by omega))
    rw [r0, rq1, rq2, rq3] at hw
    replace hw := ntBW_some hw; obtain ⟨r1, m1, h1', hw⟩ := hw
    obtain ⟨x1, a1, hrun1, hC1, c1, hg1, hd1, -⟩ :=
      cgC hD.toDmProg5 hcl hkp hs0 hsA h1' hC hc hann he hpwlt hdh hbd hn hv hsd1 hsd2 hpx hCr
    have hrun1' : (divModCertGuard fe (decI c) (decE annVal) hy (decE e)
        (decI (rdW (m.arr64 IW) po))).run a = .ok (x1, a1) := hrun1
    have hlpos : 0 < pl.toNat :=
      Nat.pos_of_ne_zero (fun e' => hpl0 (UInt64.toNat_inj.mp (by simpa using e')))
    have hpo1 : (po + 1).toNat = po.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hpl1 : (pl - 1).toNat = pl.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    by_cases z1 : r1.headD 0 = 0
    · rw [ite_eq_left z1] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx1 := decW0B_false hd1 z1
      refine ⟨false, a1, ?_, hC1, c1, hg1, decW0B_of_false _⟩
      simp only [divModCertsGuardGo, StateT.run_bind, hrun1', exc_ok_bind', hx1,
        Bool.false_eq_true, ite_false]
      rfl
    rw [ite_eq_right z1] at hw
    have hx1 := decW0B_true hd1 z1
    replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hdr1 : decHL m1 (po + 1).toNat (pl - 1).toNat = some pfs := by
      rw [decHL_grow hg1 (by rw [hpo1, hpl1]; omega)]; exact hdrest
    obtain ⟨x2, a2, hrun2, hC2, c2, hg2, hd2⟩ := ih xrest pfs pxs (so + 1) (sl - 1) (po + 1) (pl - 1)
      k m1 a1 r2 m2 hC1 (hkp.call (im_mem _ rfl) h1' hCr) (hrest.grow hg1) hdr1 (by rw [hpo1, hpl1]; have := hg1.iw; omega)
      (ConRon.Bridge.denoteN_ext hn c1.ext) (ConRon.Bridge.denote_ext hv c1.ext)
      (ConRon.Bridge.StmtsDenote.mono c1.ext _ _ hsd3)
      (ConRon.Bridge.denoteEList_ext c1.ext _ _ hpxs) h2
    refine ⟨x2, a2, ?_, hC2, c1.trans c2, hg1.trans hg2, hd2⟩
    simp only [divModCertsGuardGo, StateT.run_bind, hrun1', exc_ok_bind', hx1, ite_true]
    exact hrun2

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
  cases k with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ k =>
  have hw := callW_model (M := fun mq => cgsW p (k + 1) mq ps vis c annVal)
    (cgs_specW p hD.lCertsGuard (k + 1) · ps vis c annVal) hcall
  rw [cgsW.arm1] at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hd1⟩, hf1, hCr1, hw⟩ :=
    (divModCertStmts_ref hD.toDmProg5.toDmProg2 c).bindLC hcl (leaf_mem _ (by decide)) hkp
      (im_mem _ rfl) ⟨hC.stage, hc⟩ hCr hw
  obtain ⟨hi1, hsd⟩ := ConRon.Bridge.divModCertStmts_run hC.check.state hC.check.pins hn hrun1
  have c1 := ConRon.Bridge.CoreStep.of_istep hC.check hi1
  have hC1 := StageC.of_core hC hS1 hf1 c1
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hd2⟩, hf2, hCr2, hw⟩ :=
    (divModCertProofs_ref hD.toDmProg5.toDmProg2.toDmProg1 ps c ip).bindLC hcl
      (leaf_mem _ (by decide)) hkp (im_mem _ rfl) ⟨hS1, hc, PinSetR.grow hP hg1⟩ hCr1 hw
  have hps1 := (ConRon.Bridge.PinsDenote.mono c1.ext [ip] [psP] ⟨hps, trivial⟩).1
  have hn1 := ConRon.Bridge.denoteN_ext hn c1.ext
  obtain ⟨e2, hpr⟩ := ConRon.Bridge.divModCertProofs_run hC1.check.state hC1.check.pins hps1 hn1 hrun2
  rw [e2] at hrun2 hS2
  have hC2 := StageC.of_core hC1 hS2 hf2 (CoreStep.refl hC1.check)
  cases h3 : callW p k "div_mod_certs_guard_go" [vis, c, annVal, r1.headD 0, r1.tail.headD 0,
      r2.headD 0, r2.tail.headD 0] m2 with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  simp only [decStmtL, ntGetD0, ntGetD1] at hd1
  unfold decRL at hd2
  simp only [Nat.zero_add, ntGetD0, ntGetD1] at hd2
  obtain ⟨x3, a3, hrun3, hC3, c3, hg3, hd3⟩ := cggoC hD hcl hkp hs0 hsA c annVal hc hann x1 _ x2 _
    (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) k m2 a1 r3 m3 hC2 hCr2
    (hd1.grow hg2) hd2.1 hd2.2 hn1 (ConRon.Bridge.denote_ext hv c1.ext) hsd hpr h3
  refine ⟨x3, a3, ?_, hC3, c1.trans c3, hg1.trans (hg2.trans hg3), hd3⟩
  simp only [divModCertsGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2]
  exact hrun3

end cgs

end L.Ind
