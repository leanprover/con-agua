import ConAgua.Arena.DeclArmOpaque
import ConAgua.Rom.PinSets

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
      (fun m m' a r x => KeepPost dn w fe2 decUnit m m' a r x ∧ PinSetsR m' pins)

/-- `defn_div_gate(vis, w, n)` refines `divGateT pins` at the extended view `w`, the variant list
in memory being `pins`. -/
def DivGateSpec (p : Prog) (pins : List INatOpPinSet) : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (vis w : Word) (fe2 : IFEnv) (n : Word),
    n.toNat < 2 ^ 32 →
    RefAM p "defn_div_gate" [vis, w, n] (fun m a => StageR dn w fe2 m a ∧ PinSetsR m pins)
      (divGateT pins (fe2.restrictTo vis.toNat) fe2 (decI n))
      (fun m m' a r x => KeepPost dn w fe2 decUnit m m' a r x ∧ PinSetsR m' pins)

/-! ## The variant list across a growing record pool -/

theorem rdW_keep {a a' : Array Word} {T : Nat} (h : ∀ i < T, a'[i]? = a[i]?) {x : Word}
    (hx : x.toNat < T) : rdW a' x = rdW a x := by
  simp only [rdW, h _ hx]

theorem SliceR.grow {m m' : Mem} {o l : Word} {hs : List EIdx} (h : SliceR m o l hs)
    (hg : IWGrow m m') : SliceR m' o l hs := by
  obtain ⟨hb, hl, hw⟩ := h
  obtain ⟨-, het, -, hek⟩ := hg
  have het' : erecTop m ≤ erecTop m' := het
  have e0 : erTop m = erecTop m := rfl
  refine ⟨by omega, hl, fun i hi => ?_⟩
  have hlt : (o + UInt64.ofNat i).toNat < erecTop m := by
    have : (rdW (m.arr64 CTL) 129).toNat < 2 ^ 64 := UInt64.toNat_lt_size _
    have : erecTop m < 2 ^ 64 := this
    rw [toNat_add_small o i (by omega)]; omega
  rw [rdW_keep hek hlt]; exact hw i hi

theorem PinSetR.grow {m m' : Mem} {r : Word} {ip : INatOpPinSet} (h : PinSetR m r ip)
    (hg : IWGrow m m') : PinSetR m' r ip := by
  obtain ⟨hb, hs, hh⟩ := h
  have het : erecTop m ≤ erecTop m' := hg.2.1
  have hek := hg.2.2.2
  have e0 : erTop m = erecTop m := rfl
  have htop : erecTop m < 2 ^ 64 := UInt64.toNat_lt_size _
  refine ⟨by omega, SliceR.grow hs hg, fun j hj => ?_⟩
  have e8 : (r + 8 + 2 * UInt64.ofNat j).toNat = r.toNat + 8 + 2 * j := by
    have : (2 * UInt64.ofNat j).toNat = 2 * j := by
      rw [UInt64.toNat_mul, UInt64.toNat_ofNat']; simp; omega
    rw [UInt64.toNat_add, UInt64.toNat_add, this]; simp; omega
  have e9 : (r + 9 + 2 * UInt64.ofNat j).toNat = r.toNat + 9 + 2 * j := by
    have : (2 * UInt64.ofNat j).toNat = 2 * j := by
      rw [UInt64.toNat_mul, UInt64.toNat_ofNat']; simp; omega
    rw [UInt64.toNat_add, UInt64.toNat_add, this]; simp; omega
  have h8 : rdW (m'.arr64 EREC) (r + 8 + 2 * UInt64.ofNat j) =
      rdW (m.arr64 EREC) (r + 8 + 2 * UInt64.ofNat j) := rdW_keep hek (by rw [e8]; omega)
  have h9 : rdW (m'.arr64 EREC) (r + 9 + 2 * UInt64.ofNat j) =
      rdW (m.arr64 EREC) (r + 9 + 2 * UInt64.ofNat j) := rdW_keep hek (by rw [e9]; omega)
  have := SliceR.grow (hh j hj) hg
  unfold HdrR at this ⊢
  rw [h8, h9]; exact this

/-- **The variant list survives a run that grows the pools and leaves `CTL[150]`, `CTL[151]`.** -/
theorem PinSetsR.grow {m m' : Mem} {ips : List INatOpPinSet} (h : PinSetsR m ips)
    (hg : IWGrow m m') (h150 : rdW (m'.arr64 CTL) 150 = rdW (m.arr64 CTL) 150)
    (h151 : rdW (m'.arr64 CTL) 151 = rdW (m.arr64 CTL) 151) : PinSetsR m' ips := by
  obtain ⟨hc, hb, hr⟩ := h
  have het : erecTop m ≤ erecTop m' := hg.2.1
  have hek := hg.2.2.2
  have e0 : erTop m = erecTop m := rfl
  have htop : erecTop m < 2 ^ 64 := UInt64.toNat_lt_size _
  refine ⟨by rw [h151]; exact hc, by rw [h150]; omega, fun k hk => ?_⟩
  have ek : (rdW (m.arr64 CTL) 150 + UInt64.ofNat k).toNat = (rdW (m.arr64 CTL) 150).toNat + k :=
    toNat_add_small _ k (by omega)
  rw [h150, rdW_keep hek (by rw [ek]; omega)]
  exact PinSetR.grow (hr k hk) hg

end L.Arena
