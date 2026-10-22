import ConAgua.Arena.DeclArmOpaque
import ConAgua.Arena.DeclPins

/-!
# The definition arm `check_decl_defn(i, vis)` (lane `decls3`)

`checkDecl`'s `.defnDecl` arm: the constant check, the definition check (the push), then two
gates at the extended environment `fe2` and the pre-insertion one `fe2.restrictTo fe.visibleBelow`:
the structural-`Nat` gate (`defn_nat_gate`, the twin's lines 104-119: `natGateT`) and the
`Nat.div`-family pin gate (`defn_div_gate`, lines 123-124: `divGateT`). The arm is proved at the
loop's relation through the gates' specs, stated here as hypotheses (`NatGateSpec`,
`DivGateSpec`) for helpers `decls3-nat` and `decls3-divmod` to discharge. The pin gate reads the
pin variants `rom_pin_sets()` lists, so its spec takes lane `romload`'s `PinSetsR m pins`, which
the arm carries from its entry to the gate (`PinSetsR.grow`: the records are below `EREC`'s top
and `CTL[150]`, `CTL[151]` are not written by the arm's text).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Ind
open L.Rom (PinSetsR PinSetR SliceR HdrR)
open L.Front (DECL DLP DeclsR DeclAt CVAt dw)

local notation "V" => ConLeche.CheckMode.verified

/-! ## The twin's two gates -/

/-- The structural-`Nat` gate (`checkDecl`'s lines 104-119), at the extended environment `fe2`
and the pre-insertion one `feR`. -/
def natGateT (feR fe2 : IFEnv) (c : NIdx) : AM Unit := do
  if (← natOpNames).contains c then do
    let g ← natOpGuard fe2 c
    let deps ← natOpDeps c
    unless g && (← natOpStoredOkAll fe2 deps) do
      fail (.notImplemented
        "nonstandard structural Nat operation environment")
    match fe2.find? c with
    | some (.defnInfo _ value' _) => do
      let eqs ← natOpEquations 0 c
      let ok ← certifyNatEqs V feR (← substConst0Pairs c value' eqs)
      unless ok do
        fail (.notImplemented
          "nonstandard structural Nat operation")
    | _ => fail (.internal
        "structural Nat operation not stored")

/-- The `Nat.div`-family pin gate (`checkDecl`'s lines 123-124). -/
def divGateT (pins : List INatOpPinSet) (feR fe2 : IFEnv) (c : NIdx) : AM Unit := do
  if (← natDivModNames).contains c then
    checkDivModPin V pins feR fe2 c

/-- **The arm is the two checks, then the two gates** (the twin's `do` block, its join points
distributed over the gates' branches). -/
theorem checkDecl_defn_eq (pins : List INatOpPinSet) (fe : IFEnv) (cv : IConstantVal) (v : EIdx)
    (h : ConLeche.ReducibilityHint) :
    checkDecl V pins fe (.defnDecl cv v h) = (do
      checkConstantVal V fe cv
      let fe2 ← checkDefnVal V fe cv v h
      natGateT (fe2.restrictTo fe.visibleBelow) fe2 cv.name
      divGateT pins (fe2.restrictTo fe.visibleBelow) fe2 cv.name
      pure fe2) := by
  simp only [checkDecl, natGateT, divGateT, bind_assoc]
  congr 1; funext _; congr 1; funext fe2; congr 1; funext x
  split
  · rw [bind_assoc]
    congr 1; funext g
    rw [bind_assoc]; congr 1; funext deps
    rw [bind_assoc]; congr 1; funext b
    cases hf : fe2.find? cv.name with
    | none => split <;> simp [fail_bindAM] <;> try (congr 1; funext u; congr 1; funext y; split <;> simp [fail_bindAM])
    | some ci =>
      cases ci
      case defnInfo cv' val hint =>
        split
        · simp only [bind_assoc]
          congr 1; funext eqs; congr 1; funext l; congr 1; funext ok
          split <;> simp [fail_bindAM] <;> try (congr 1; funext u; congr 1; funext y; split <;> simp [fail_bindAM])
        · simp only [bind_assoc]
          congr 1; funext u
          congr 1; funext eqs; congr 1; funext l; congr 1; funext ok
          split <;> simp [fail_bindAM] <;> try (congr 1; funext u; congr 1; funext y; split <;> simp [fail_bindAM])
      all_goals (split <;> simp [fail_bindAM] <;> try (congr 1; funext u; congr 1; funext y; split <;> simp [fail_bindAM]))
  · simp only [pure_bind, bind_assoc]
    congr 1; funext y
    split <;> simp

/-! ## The gates' specs (hypotheses) -/

/-- `defn_nat_gate(vis, w, n)` refines `natGateT` at the extended view `w`. -/
def NatGateSpec (p : Prog) (pins : List INatOpPinSet) : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (vis w : Word) (fe2 : IFEnv) (n : Word),
    n.toNat < 2 ^ 32 →
    RefAM p "defn_nat_gate" [vis, w, n] (fun m a => StageR dn w fe2 m a ∧ PinSetsR m pins)
      (natGateT (fe2.restrictTo vis.toNat) fe2 (decI n))
      (fun m m' a r x => KeepPost dn w fe2 decUnit m m' a r x ∧ PinSetsR m' pins ∧
        MemFrame stepA stepC m m')

/-- `defn_div_gate(vis, w, n)` refines `divGateT pins` at the extended view `w`, the variant list
in memory being `pins`. -/
def DivGateSpec (p : Prog) (pins : List INatOpPinSet) : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (vis w : Word) (fe2 : IFEnv) (n : Word),
    n.toNat < 2 ^ 32 →
    RefAM p "defn_div_gate" [vis, w, n] (fun m a => StageR dn w fe2 m a ∧ PinSetsR m pins)
      (divGateT pins (fe2.restrictTo vis.toNat) fe2 (decI n))
      (fun m m' a r x => KeepPost dn w fe2 decUnit m m' a r x ∧ PinSetsR m' pins ∧
        MemFrame stepA stepC m m')

/-! ## The model -/

section model
variable (p : Prog)

/-- After the pin gate: the extended view. -/
def cdfK5 (w : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m5) => some ([w], m5)

/-- After the structural gate. -/
def cdfK4 (n : Nat) (vis w nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m4) => cdfK5 w (callW p n "defn_div_gate" [vis, w, nm] m4)

/-- After `check_defn_val`. -/
def cdfK3 (n : Nat) (vis nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => cdfK4 p n vis (r3.headD 0) nm (callW p n "defn_nat_gate" [vis, r3.headD 0, nm] m3)

/-- After `check_constant_val`. -/
def cdfK2 (n : Nat) (vis q nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => cdfK3 p n vis nm (callW p n "check_defn_val" [vis, q] m2)

/-- After `erec_ci`. -/
def cdfK1 (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    cdfK2 p n vis (r1.headD 0) (rdW (m1.arr64 EREC) (r1.headD 0 + 1))
      (callW p n "check_constant_val" [vis, r1.headD 0 + 1] m1)

/-- **The model of `check_decl_defn(i, vis)`.** -/
def cdfW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, i, vis => cdfK1 p n vis (callW p n "erec_ci" [i, 1] m)

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (i vis q nm w : Word) (r1 r2 r3 r4 r5 : List Word)
theorem cdfW_step : cdfW p (n + 1) m i vis = cdfK1 p n vis (callW p n "erec_ci" [i, 1] m) := rfl
theorem cdfK1_some : cdfK1 p n vis (some (r1, m1)) =
    cdfK2 p n vis (r1.headD 0) (rdW (m1.arr64 EREC) (r1.headD 0 + 1))
      (callW p n "check_constant_val" [vis, r1.headD 0 + 1] m1) := rfl
theorem cdfK2_some : cdfK2 p n vis q nm (some (r2, m2)) =
    cdfK3 p n vis nm (callW p n "check_defn_val" [vis, q] m2) := rfl
theorem cdfK3_some : cdfK3 p n vis nm (some (r3, m3)) =
    cdfK4 p n vis (r3.headD 0) nm (callW p n "defn_nat_gate" [vis, r3.headD 0, nm] m3) := rfl
theorem cdfK4_some : cdfK4 p n vis w nm (some (r4, m4)) =
    cdfK5 w (callW p n "defn_div_gate" [vis, w, nm] m4) := rfl
theorem cdfK5_some : cdfK5 w (some (r5, m5)) = some ([w], m5) := rfl
end arms

grind_pattern [ind_grind] cdfW_step => cdfW p (n + 1) m i vis
grind_pattern [ind_grind] cdfK1_some => cdfK1 p n vis (some (r1, m1))
grind_pattern [ind_grind] cdfK2_some => cdfK2 p n vis q nm (some (r2, m2))
grind_pattern [ind_grind] cdfK3_some => cdfK3 p n vis nm (some (r3, m3))
grind_pattern [ind_grind] cdfK4_some => cdfK4 p n vis w nm (some (r4, m4))
grind_pattern [ind_grind] cdfK5_some => cdfK5 w (some (r5, m5))

set_option maxHeartbeats 1600000 in
theorem cdf_specW (hp : p.lookup "check_decl_defn" = some checkDeclDefn) (n : Nat) (s₀ : St)
    (i vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl_defn" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ cdfW p n s₀.mem i vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDeclDefn]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "erec_ci",
        callW_spec p n "check_constant_val", callW_spec p n "check_defn_val",
        callW_spec p n "defn_nat_gate", callW_spec p n "defn_div_gate"] <;>
      finish (gen := 20) [rdW_eq]

end model

/-- The definition arm's program facts: its text, and the two gates' specs. -/
structure DefnProg (p : Prog) (pins : List INatOpPinSet) : Prop where
  df : p.lookup "check_decl_defn" = some checkDeclDefn
  nat : NatGateSpec p pins
  div : DivGateSpec p pins

/-- A frame of the step's write set keeps the variant list. -/
theorem PinSetsR.step {m m' : Mem} {ips : List INatOpPinSet} (h : PinSetsR m ips)
    (hg : IWGrow m m') (hf : MemFrame stepA stepC m m') : PinSetsR m' ips :=
  PinSetsR.grow h (IWGrow.recGrow hg) (hf.2.1 _ step_pins.1) (hf.2.1 _ step_pins.2)

/-- **The definition arm at the stage relation.** -/
theorem cdfW_ok {p : Prog} (hA : ArmProg p) (hV : ValProg p) {pins : List INatOpPinSet}
    (hG : DefnProg p pins) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {a : AState} {n : Nat} {m m' : Mem} {i : Word} {r : List Word} {ds : Array IDeclaration}
    {cv : IConstantVal} {v : EIdx} {hh : ConLeche.ReducibilityHint}
    (h : cdfW p n m i vis = some (r, m')) (hS : StageR dn vis fe m a) (hPS : PinSetsR m pins)
    (hD : DeclsR (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .defnDecl cv v hh) :
    ∃ fe' a', (checkDecl V pins fe (.defnDecl cv v hh)).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ IWGrow m m' ∧ MemFrame stepA stepC m m' := by
  have hfr : ∀ {k : Nat} {f : FnName} {args : List Word} {mx my : Mem} {rx : List Word}, f ∈ armFns →
      callW p k f args mx = some (rx, my) → MemFrame stepA stepC mx my := by
    intro k f args mx my rx hf hc
    obtain ⟨s', hs', hfr', -⟩ := triple_of_callW (s₀ := ⟨mx, Locals.init []⟩)
      (invoke_memFrame hA.closed k hf args ⟨mx, Locals.init []⟩) hc
    rw [← hs']; exact hfr'
  cases n with
  | zero => simp [cdfW] at h
  | succ n =>
  rw [cdfW_step] at h
  -- `erec_ci`
  cases h1 : callW p n "erec_ci" [i, 1] m with
  | none => rw [h1] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, cdfK1_some] at h
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erecCi_specW p hV.rcp n ⟨m, Locals.init []⟩ i 1) h1
  rw [hs1] at hW1
  obtain ⟨hS1, hg1, hci1, hcv1, -, htop1⟩ :=
    erecCiW_ok (ci := .defnInfo cv v hh) hW1 hS hD hi (by rw [hd]; rfl)
  have hf1 := hfr (by decide) h1
  have hPS1 := PinSetsR.step hPS hg1 hf1
  rw [hd] at hcv1
  simp only [stepCV] at hcv1
  generalize hq : r1.headD 0 = q at h hci1 hcv1 htop1
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.2.2.1; have := hS1.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCI_name hci1
  have hname : cv.name = decI wn := hname0
  rw [rdW_of_get? hq1.symm (erecP_get hwn)] at h
  -- `check_constant_val`
  cases h2 : callW p n "check_constant_val" [vis, q + 1] m1 with
  | none => rw [h2] at h; cases h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, cdfK2_some] at h
  obtain ⟨s2, hs2, -, hok2, hS2, hg2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (checkConstantVal_refines p hV n ⟨m1, Locals.init []⟩ a dn fe vis (q + 1) cv hS1
      (by rw [hq1]; exact hcv1) (by omega)) h2
  subst hs2
  have hf2 := hfr (by decide) h2
  have hPS2 := PinSetsR.step hPS1 hg2 hf2
  have hrun2 := AM.run_of_ok _ _ hok2
  generalize AM.st (checkConstantVal V fe cv) a = a2 at hrun2 hS2
  -- `check_defn_val`
  cases h3 : callW p n "check_defn_val" [vis, q] s2.mem with
  | none => rw [h3] at h; cases h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, cdfK3_some] at h
  have hx2 : ArrExt (erecP m1) (erecP s2.mem) := IWGrow.erecPExt hg2
  obtain ⟨s3, hs3, -, hok3, hS3, hg3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (checkDefnVal_refines p hV n ⟨s2.mem, Locals.init []⟩ a2 dn fe vis q cv v hh hS2
      (ArrExt.decCI hx2 hci1)) h3
  subst hs3
  have hf3 := hfr (by decide) h3
  have hPS3 := PinSetsR.step hPS2 hg3 hf3
  have hrun3 := AM.run_of_ok _ _ hok3
  generalize AM.st (checkDefnVal V fe cv v hh) a2 = a3 at hrun3 hS3
  generalize hw : r3.headD 0 = w at h hS3
  -- the structural gate
  cases h4 : callW p n "defn_nat_gate" [vis, w, wn] s3.mem with
  | none => rw [h4] at h; cases h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, cdfK4_some] at h
  obtain ⟨s4, hs4, -, hok4, ⟨hS4, hg4, -⟩, hPS4, hf4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (hG.nat dn vis w _ wn hwnl n ⟨s3.mem, Locals.init []⟩ a3 ⟨hS3, hPS3⟩) h4
  subst hs4
  have hrun4 := AM.run_of_ok _ _ hok4
  -- the pin gate
  cases h5 : callW p n "defn_div_gate" [vis, w, wn] s4.mem with
  | none => rw [h5] at h; cases h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, cdfK5_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s5, hs5, -, hok5, ⟨hS5, hg5, -⟩, -, hf5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (hG.div dn vis w _ wn hwnl n ⟨s4.mem, Locals.init []⟩ _ ⟨hS4, hPS4⟩) h5
  subst hs5
  have hrun5 := AM.run_of_ok _ _ hok5
  have hvis : fe.visibleBelow = vis.toNat := hS.1.env.vis
  refine ⟨_, _, ?_, by simpa using hS5, hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5))),
    hf1.trans (hf2.trans (hf3.trans (hf4.trans hf5)))⟩
  rw [checkDecl_defn_eq]
  simp only [StateT.run_bind, hrun2, exc_ok_bind', hrun3, hvis, hname]
  erw [hrun4, exc_ok_bind', hrun5]
  rfl

/-- **`check_decl_defn` refines `checkDecl`'s `.defnDecl` arm** at the loop's relation, the variant
list in memory being `pins` (through the gates' specs, `DefnProg`). -/
theorem checkDeclDefn_loop' {p : Prog} (hA : ArmProg p) (hV : ValProg p)
    (pins : List INatOpPinSet) (hG : DefnProg p pins) (dn : NIdx → Option ConLeche.Name)
    (ds : Array IDeclaration) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (i : Word) (cv : IConstantVal) (v : EIdx) (hh : ConLeche.ReducibilityHint), i.toNat < ds.size →
      ds[i.toNat]? = some (.defnDecl cv v hh) → LoopR pins dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl_defn" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDecl V pins fe (.defnDecl cv v hh)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (checkDecl V pins fe (.defnDecl cv v hh)) a₀) (r.headD 0)
        (AM.res (checkDecl V pins fe (.defnDecl cv v hh)) a₀) pend ds; ⊤⦄ := by
  intro n s₀ a₀ vis fe pend i cv v hh hi hd hR
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun (cdf_specW p hG.df n s₀ i vis)
  subst hs
  have hd' : ds[i.toNat] = .defnDecl cv v hh := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨fe', a', hrun', hS', hg', hf⟩ :=
    cdfW_ok hA hV hG hW ⟨hR.check, hR.iw⟩ hR.pinsets hR.decls hi hd'
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok, ?_⟩
  rw [hst, hres]
  exact hR.of_step hS' hf (IWGrow.erecPExt hg')

end L.Arena
