import ConAgua.Arena.DeclDivMod9
import ConAgua.Arena.DeclArmDefn
import ConAgua.Rom.PinReadSpec
import ConAgua.L.ModelGen

/-!
# The `Nat.div` family's pin gate: `defn_div_gate` (lane `decls3`, `decls3-divmod`)

Part 10: `rom_pin_sets()` (the variant records at `CTL[150]`, `CTL[151]` copied into `IW`: `PinsIW`),
then `defn_div_gate(vis, w, n)` as `DivGateSpec` of `DeclArmDefn.lean`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetsR PinSetR)

namespace L.Ind

open L.Arena

/-- The words `er_to_iw` leaves: the copy at the old top. -/
theorem erToIwW_words {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : erToIwW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (_hc : 200 < (m.arr64 CTL).size) (hE : (m.arr64 EREC).size < 2 ^ 64)
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
  rw [hG, ite_eq_left (by omega)]
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

/-- **`defn_div_gate` is its model `dgW`** (generated). -/
l_model dg_specW (p : Prog) (hp : p.lookup "defn_div_gate" = some defnDivGate)
  fns [hp ↦ dgW list]
  specs [callW_spec p n "nat_div_mod_names", callW_spec p n "sl_contains", callW_spec p n "rom_pin_sets", callW_spec p n "check_div_mod_pin"]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW]

/-- The gate and its callees. -/
def dgFns : List FnName :=
  ["defn_div_gate", "nat_div_mod_names", "sl_contains", "rom_pin_sets", "check_div_mod_pin"]

end divgate

end L.Ind
