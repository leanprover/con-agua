module

public import ConAgua.Arena.DeclDivModSpec.DecCIDefnValue
public import ConAgua.Arena.DeclDivModSpec.DivModEnvGuard
import ConAgua.Arena.DeclPins
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPartsSpec.MemberNames
import all ConAgua.Rom.PinRead

@[expose] public section

/-!
# RomPinSets

`DmProg8`, `DmProg9`, `erToIwW_words`, `DmProg10`, `romPinSets_spec'`, `romPinSets_ref` and the lemmas only they use.
-/

section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetR)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

structure DmProg8 (p : Prog) : Prop extends DmProg7 p where
  lCheckDivModCerts : p.lookup "check_div_mod_certs" = some checkDivModCertsL
  lCheckDivModPinAt : p.lookup "check_div_mod_pin_at" = some checkDivModPinAtL
  lCheckTypePins : p.lookup "check_type_pins" = some checkTypePinsL
  lCheckDivModPinValue : p.lookup "check_div_mod_pin_value" = some checkDivModPinValueL
  lCheckDivModPinLoop : p.lookup "check_div_mod_pin_loop" = some checkDivModPinLoopL
  lCheckDivModPin : p.lookup "check_div_mod_pin" = some checkDivModPinL

end L.Ind

end

section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetR)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

structure DmProg9 (p : Prog) : Prop extends DmProg8 p

end L.Ind

end

section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetsR PinSetR)

namespace L.Ind

open L.Arena

/-- `erRd` does not read `CTL`. -/
theorem erRd_allocMem (m : Mem) (k a : Word) : erRd (allocMem m k) a = erRd m a := by
  unfold erRd allocMem; rw [Mem.arr64_set64_ne _ _ _ _ _ (by rw [tierA_EREC]; split <;> decide)]

/-- **`er_to_iw` under the stage relation, word by word** (`erToIwW_stage` without a decoding of
the source: the words need not be handles): the copy at the old top, word `i` the tagged read
`EREC⦃o + i⦄`. -/
theorem erToIwW_words {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {o l : Word}
    {r : List Word} (h : erToIwW n m o l = some (r, m')) (hS : StageR vis fe m a)
    (hsrc : o.toNat + l.toNat ≤ 2 ^ 64) :
    r = [rdW (m.arr64 CTL) 200, l] ∧ StageR vis fe m' a ∧ IWGrow m m' ∧
      MemFrame [IW] [200] m m' ∧ (rdW (m.arr64 CTL) 200).toNat + l.toNat = iwTop m' ∧
      ∀ i < l.toNat, (m'.arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + i]? =
        some (erRd m (UInt64.ofNat (o.toNat + i))) := by
  have hsz := hS.iw.iwSize
  have hc := hS.iw.ctl
  simp only [erToIwW] at h
  cases hal : allocW m l with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  rcases hcp : erCopyW (n - 1) m1 q o l with _ | m2 <;>
    simp only [hcp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq hm1
  have hIW := allocMem_IW m l
  obtain ⟨hA, hSz, hG⟩ := erCopyW_get (n - 1) _ _ _ _ _ hcp hsrc
    (by rw [hIW]; exact hroom) (by rw [hIW]; exact hsz)
  rw [hIW] at hSz hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m l).trans (copy_frame hA (by rw [hSz, hIW]))
  have htop : rdW (m2.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + l := by
    rw [hA CTL (by decide), allocMem_top m _ hc]
  have hsum : (rdW (m.arr64 CTL) 200 + l).toNat = (rdW (m.arr64 CTL) 200).toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hg : IWGrow m m2 := iwGrow_of_frame hfr (N := l) htop (by simp only [iwTop]; omega) hsz
    (fun i hi => by simp only [iwTop] at hi; rw [hG, ite_eq_right (by omega)])
  have hti : (rdW (m.arr64 CTL) 200).toNat + l.toNat = iwTop m2 := by simp only [iwTop, htop, hsum]
  have hroom' : iwTop m2 ≤ (m2.arr64 IW).size := by rw [← hti, hSz]; exact hroom
  refine ⟨rfl, ⟨CheckR.frame_iw hfr hS.check, hS.iw.of_iw hfr hroom'⟩, hg, hfr, hti, fun i hi => ?_⟩
  rw [hG, ite_eq_left (by omega), erRd_allocMem]
  congr 3; omega

section divgate
variable {dn : NIdx → Option ConLeche.Name} {p : Prog}

structure DmProg10 (p : Prog) : Prop extends DmProg9 p where
  lRomPinSets : p.lookup "rom_pin_sets" = some L.Rom.romPinSetsL

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
    (hS : StageR vis fe m a) (hP : PinSetsR m ips)
    (hc : callW p n "rom_pin_sets" [] m = some (r, m')) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ PinSetsR m' ips ∧
      PinsIW m' (r.headD 0).toNat (r.tail.headD 0).toNat ips := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ k =>
  obtain ⟨s', rfl, -, hmod⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (romPinSets_spec' hD k _) hc
  have hmod' : erToIwW k m (rdW (m.arr64 CTL) 150) (rdW (m.arr64 CTL) 151) = some (r, s'.mem) := hmod
  obtain ⟨hlen, hbd, hrec⟩ := hP
  have hI := hS.iw
  have hEtop : erecTop m ≤ (m.arr64 EREC).size := hI.er
  have hcap := hI.erCap
  have hsrc : (rdW (m.arr64 CTL) 150).toNat + (rdW (m.arr64 CTL) 151).toNat ≤ erecTop m := by
    omega
  obtain ⟨hr, hS', hg, hfr, htop, hw⟩ :=
    erToIwW_words hmod' hS (by have := erecTop_lt m; omega)
  have hP' : PinSetsR s'.mem ips :=
    PinSetsR.grow ⟨hlen, hbd, hrec⟩ (IWGrow.recGrow hg) (hfr.ctl 150 (by simp)) (hfr.ctl 151 (by simp))
  refine ⟨hS', hg, hP', ?_⟩
  rw [hr]
  simp only [List.headD_cons, List.tail_cons]
  have ht : iwTop s'.mem = (rdW (m.arr64 CTL) 200).toNat + (rdW (m.arr64 CTL) 151).toNat := htop.symm
  refine ⟨by omega, hlen, fun j hj => ?_⟩
  have hjl : j < (rdW (m.arr64 CTL) 151).toNat := by omega
  have hoj : (rdW (m.arr64 CTL) 150 + UInt64.ofNat j).toNat = (rdW (m.arr64 CTL) 150).toNat + j := by
    have := (rdW (m.arr64 CTL) 150).toNat_lt
    have := erecTop_lt m
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨rdW (m.arr64 EREC) (rdW (m.arr64 CTL) 150 + UInt64.ofNat j), ?_, PinSetR.grow (hrec j hj) hg⟩
  have e1 := hw j hjl
  have e2 : UInt64.ofNat ((rdW (m.arr64 CTL) 150).toNat + j) = rdW (m.arr64 CTL) 150 + UInt64.ofNat j :=
    UInt64.toNat_inj.mp (by rw [hoj]; simp; have := erecTop_lt m; omega)
  rw [e2, erRd_lo hI (by rw [hoj]; omega)] at e1
  simpa only [iwA, aread_apply] using e1

/-! ## `defn_div_gate` -/

/-- The gate and its callees. -/
def dgFns : List FnName :=
  ["nat_div_mod_names", "sl_contains", "rom_pin_sets", "check_div_mod_pin"]

end divgate

end L.Ind

end
