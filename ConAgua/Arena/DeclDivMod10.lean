import ConAgua.Arena.DeclDivMod9
import ConAgua.Arena.DeclArmDefn
import ConAgua.Rom.PinReadSpec

/-!
# The `Nat.div` family's pin gate: `defn_div_gate` (lane `decls3`, `decls3-divmod`)

Part 10: `rom_pin_sets()` (the variant records at `CTL[150]`, `CTL[151]` copied into `IW`: `PinsIW`),
then `defn_div_gate(vis, w, n)` as `DivGateSpec` of `DeclArmDefn.lean`.
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetsR PinSetR)

namespace L.Ind

open L.Arena

/-- The words `er_to_iw` leaves: the copy at the old top. -/
theorem erToIwW_words {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : erToIwW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hE : (m.arr64 EREC).size < 2 ^ 64)
    (hsrc : o.toNat + l.toNat ≤ (m.arr64 EREC).size) :
    ∀ i < l.toNat, (m'.arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + i]? = (m.arr64 EREC)[o.toNat + i]? := by
  simp only [erToIwW] at h
  cases hal : allocW m l with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  cases hcp : erCopyW (n - 1) m1 q o l with
  | none => simp [hcp] at h
  | some m2 =>
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq hm1
  have hIW := allocMem_IW m l
  have hEE : (allocMem m l).arr64 EREC = m.arr64 EREC := by
    simp only [allocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  obtain ⟨hA, hS, hW, hG⟩ := erCopyW_get (n - 1) _ _ _ _ _ hcp (by rw [hEE]; exact hsrc)
    (by rw [hEE]; exact hE) (by rw [hIW]; exact hroom) (by rw [hIW]; exact hsz)
  rw [hEE] at hG
  intro i hi
  rw [hG, if_pos (by omega)]
  congr 1; omega

section divgate
variable {dn : NIdx → Option ConLeche.Name} {p : Prog}

structure DmProg10 (p : Prog) : Prop extends DmProg9 p where
  lRomPinSets : p.lookup "rom_pin_sets" = some L.Rom.romPinSetsL
  lDefnDivGate : p.lookup "defn_div_gate" = some defnDivGate

theorem romPinSets_spec' (hD : DmProg10 p) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_pin_sets" []
    ⦃fun res s' => LocEq s' s₀ ∧ L.Rom.romPinSetsW (n + 1) s₀.mem = some (res, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hD.lRomPinSets]
  simp only [callFn, L.Rom.romPinSetsL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      erToIw_specW2 p hD.lIwAlloc hD.lErCopy hD.lErToIw n] <;>
    finish

/-- **`rom_pin_sets()` under the stage relation**: the variant records, as an `IW` slice. -/
theorem romPinSets_ref (hD : DmProg10 p) {vis : Word} {fe : IFEnv} {ips : List INatOpPinSet}
    {n : Nat} {m m' : Mem} {a : AState} {r : List Word}
    (hS : StageR dn vis fe m a) (hP : PinSetsR m ips)
    (hc : callW p n "rom_pin_sets" [] m = some (r, m')) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ PinSetsR m' ips ∧
      PinsIW m' (r.headD 0).toNat (r.tail.headD 0).toNat ips := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ k =>
  obtain ⟨s', rfl, -, hmod⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (romPinSets_spec' hD k _) hc
  have hmod' : erToIwW k m (rdW (m.arr64 CTL) 150) (rdW (m.arr64 CTL) 151) = some (r, s'.mem) := hmod
  obtain ⟨hlen, hbd, hrec⟩ := hP
  obtain ⟨hI1, hE1, hsz, hEs, hct⟩ := hS.2
  have hEtop : erecTop m ≤ (m.arr64 EREC).size := hE1
  have hsrc : (rdW (m.arr64 CTL) 150).toNat + (rdW (m.arr64 CTL) 151).toNat ≤ (m.arr64 EREC).size := by
    omega
  obtain ⟨hr, hd, hg, hfr, -, htop⟩ := erToIwW_dec (k := IdxKind.expr) hmod' hsz hct hEs hsrc
  obtain ⟨-, -, -, hS', hg', htop'⟩ := L.Arena.erToIwW_stage hmod' hS (Or.inr hsrc)
  have hw := erToIwW_words hmod' hsz hct hEs hsrc
  have hP' : PinSetsR s'.mem ips :=
    PinSetsR.grow ⟨hlen, hbd, hrec⟩ (IWGrow.recGrow hg) (hfr.2.1 150 (by simp)) (hfr.2.1 151 (by simp))
  refine ⟨hS', hg, hP', ?_⟩
  rw [hr]
  simp only [List.headD_cons, List.tail_cons]
  have ht : iwTop s'.mem = (rdW (m.arr64 CTL) 200).toNat + (rdW (m.arr64 CTL) 151).toNat := htop.symm
  refine ⟨by omega, hlen, fun j hj => ?_⟩
  have hjl : j < (rdW (m.arr64 CTL) 151).toNat := by omega
  have hoj : (rdW (m.arr64 CTL) 150 + UInt64.ofNat j).toNat = (rdW (m.arr64 CTL) 150).toNat + j := by
    have := (rdW (m.arr64 CTL) 150).toNat_lt
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hlt : (rdW (m.arr64 CTL) 150).toNat + j < (m.arr64 EREC).size := by omega
  refine ⟨rdW (m.arr64 EREC) (rdW (m.arr64 CTL) 150 + UInt64.ofNat j), ?_, PinSetR.grow (hrec j hj) hg⟩
  have e1 : (iwA s'.mem)[(rdW (m.arr64 CTL) 200).toNat + j]? = (m.arr64 EREC)[(rdW (m.arr64 CTL) 150).toNat + j]? := hw j hjl
  have e2 : rdW (m.arr64 EREC) (rdW (m.arr64 CTL) 150 + UInt64.ofNat j) = (m.arr64 EREC)[(rdW (m.arr64 CTL) 150).toNat + j] := by
    rw [rdW_eq _ _ ((rdW (m.arr64 CTL) 150).toNat + j) hoj.symm hlt]
  rw [e1, e2]
  exact Array.getElem?_eq_getElem hlt

/-! ## `defn_div_gate` -/

def dgW (p : Prog) (n : Nat) (m : Mem) (vs w nm : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "nat_div_mod_names" [] m) fun r1 m1 =>
  ntBW (callW p n "sl_contains" [r1.headD 0, r1.tail.headD 0, nm] m1) fun r2 m2 =>
  if r2.headD 0 ≠ 0 then
    ntBW (callW p n "rom_pin_sets" [] m2) fun r3 m3 =>
    ntBW (callW p n "check_div_mod_pin" [r3.headD 0, r3.tail.headD 0, vs, w, nm] m3) fun r4 m4 =>
      some ([0], m4)
  else some ([0], m2)

set_option maxHeartbeats 1600000 in
theorem dg_specW (p : Prog) (hp : p.lookup "defn_div_gate" = some defnDivGate) (n : Nat) (s₀ : St)
    (vs w nm : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defn_div_gate" [vs, w, nm]
    ⦃fun r s' => LocEq s' s₀ ∧ dgW p n s₀.mem vs w nm = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, defnDivGate]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_div_mod_names", callW_spec p n "sl_contains",
      callW_spec p n "rom_pin_sets", callW_spec p n "check_div_mod_pin"] <;>
    finish (gen := 30) (instances := 10000) [dgW, ntBW]

/-- The gate and its callees. -/
def dgFns : List FnName :=
  ["defn_div_gate", "nat_div_mod_names", "sl_contains", "rom_pin_sets", "check_div_mod_pin"]

/-- `DivGateSpec` of `DeclArmDefn.lean` with the one hypothesis it lacks: `dn` is injective
(`DnInj`, what `div_mod_env_guard`'s `find_is` needs); the substitution walks' refinements (helper
`decls3-nat`) and the gate text's write set (`closedA`, by `decide +kernel` on the program) are
hypotheses of the theorem below. -/
def DivGateSpecD (p : Prog) (pins : List INatOpPinSet) : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name), DnInj dn → ∀ (vis w : Word) (fe2 : IFEnv) (n : Word),
    n.toNat < 2 ^ 32 →
    RefAM p "defn_div_gate" [vis, w, n] (fun m a => StageR dn w fe2 m a ∧ PinSetsR m pins)
      (divGateT pins (fe2.restrictTo vis.toNat) fe2 (decI n))
      (fun m m' a r x => KeepPost dn w fe2 decUnit m m' a r x ∧ PinSetsR m' pins ∧
        MemFrame stepA stepC m m')

theorem divGateSpecD (hD : DmProg10 p) (pins : List INatOpPinSet)
    (hs0 : ∀ dn vis fe, SubstC0 p dn vis fe) (hsA : ∀ dn vis fe, SubstCAll p dn vis fe)
    (hCl : StepIn p dgFns) : DivGateSpecD p pins := by
  intro dn hdn vis w fe2 n hn
  refine CallRef.refAM (fun k m a res m' ⟨hS, hP⟩ hcall => ?_)
  cases k with
  | zero => rw [callW_zero] at hcall; exact absurd hcall (by simp)
  | succ k =>
  have hw := callW_model (M := fun mq => dgW p k mq vis w n)
    (dg_specW p hD.lDefnDivGate k · vis w n) hcall
  unfold dgW at hw
  have hfrOf : ∀ {k : Nat} {f : FnName} {args : List Word} {mx my : Mem} {rx : List Word},
      f ∈ dgFns → callW p k f args mx = some (rx, my) → MemFrame stepA stepC mx my := by
    intro k f args mx my rx hf hc
    obtain ⟨s', hs', hfr', -⟩ := triple_of_callW (s₀ := ⟨mx, Locals.init []⟩)
      (hCl.memFrame k hf args ⟨mx, Locals.init []⟩) hc
    rw [← hs']; exact hfr'
  have hfr : MemFrame stepA stepC m m' := hfrOf (by simp [dgFns]) hcall
  have hN : NatGateProg p := hD.toDmProg9.toDmProg8.toDmProg7.toDmProg6.toDmProg5.toDmProg2.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg
  suffices H : ∃ x a', (divGateT pins (fe2.restrictTo vis.toNat) fe2 (decI n)).run a = .ok (x, a') ∧
      KeepPost dn w fe2 decUnit m m' a' res x by
    obtain ⟨x, a', hr, hK⟩ := H
    exact ⟨x, a', hr, hK, PinSetsR.step hP hK.2.1 hfr, hfr⟩
  cases h1 : callW p k "nat_div_mod_names" [] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨x1, a1, hrun1, hS1, hg1, hd1⟩ := natDivModNames_ref hN (vis := w) (fe := fe2) (dn := dn) k m a r1 m1 hS h1
  have hP1 := PinSetsR.step hP hg1 (hfrOf (by simp [dgFns]) h1)
  unfold decRL at hd1
  simp only [Nat.zero_add, ntGetD0, ntGetD1] at hd1
  cases h2 : callW p k "sl_contains" [r1.headD 0, r1.tail.headD 0, n] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := slContains_ref hN.lSlContains (vis := w) (fe := fe2) (dn := dn)
    (r1.headD 0) (r1.tail.headD 0) n x1 (by exact_mod_cast hn) k m1 a1 r2 m2 ⟨hS1, hd1.1⟩ h2
  have hP2 := PinSetsR.step hP1 hg2 (hfrOf (by simp [dgFns]) h2)
  have hrun2' : (pure (x1.contains (decI n)) : AM Bool).run a1 = .ok (x2, a2) := hrun2
  obtain ⟨hx2e, hxa⟩ := pure_run_eq hrun2'
  subst hxa
  have hG2 : IWGrow m m2 := hg1.trans hg2
  by_cases z2 : r2.headD 0 ≠ 0
  · rw [if_pos z2] at hw
    have hx2 := decW0B_true hd2 z2
    have hx2' : x1.contains (decI n) = true := by rw [← hx2e]; exact hx2
    cases h3 : callW p k "rom_pin_sets" [] m2 with
    | none => rw [h3] at hw; simp at hw
    | some q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, bW_some] at hw
    obtain ⟨hS3, hg3, hP3, hI3⟩ := romPinSets_ref hD hS2 hP2 h3
    cases h4 : callW p k "check_div_mod_pin" [r3.headD 0, r3.tail.headD 0, vis, w, n] m3 with
    | none => rw [h4] at hw; simp at hw
    | some q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨x4, a4, hrun4, hS4, hg4, -⟩ := cp_ref hD.toDmProg9 hdn (hs0 dn vis _) (hsA dn vis _)
      (r3.headD 0) (r3.tail.headD 0) n pins k m3 a2 r4 m4 ⟨hS3, by exact_mod_cast hn, hI3⟩ h4
    refine ⟨(), a4, ?_, hS4, hG2.trans (hg3.trans hg4), trivial⟩
    simp only [divGateT, StateT.run_bind, hrun1, exc_ok_bind']
    have hrun1' : natDivModNames.run a = .ok (x1, a2) := hrun1
    simp only [hrun1', exc_ok_bind', hx2', if_true]
    exact hrun4
  · rw [if_neg z2] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have z2' : r2.headD 0 = 0 := by simpa using z2
    have hx2 := decW0B_false hd2 z2'
    have hx2' : x1.contains (decI n) = false := by rw [← hx2e]; exact hx2
    refine ⟨(), a2, ?_, hS2, hG2, trivial⟩
    have hrun1' : natDivModNames.run a = .ok (x1, a2) := hrun1
    simp only [divGateT, StateT.run_bind, hrun1', exc_ok_bind', hx2', Bool.false_eq_true, if_false]
    rfl

end divgate

end L.Ind
