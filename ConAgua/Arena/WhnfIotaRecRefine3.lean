module

public import ConAgua.Arena.WhnfIotaRecRefine2
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import ConRon.Bridge.Grind

@[expose] public section

/-!
# `iota_rec_at`'s pieces, part 3: the recursor's block and the top

`iota_rec_c` (the recursor's record, the arity, the level-list length, the telescope) and
`iota_rec_at` itself: `iotaRecAt_refines'` proves `WhnfCore.lean`'s `IotaRecAtOK` from the
callees' specs and the stub assumption `ErecKeptRec`; the
census-tagged `iotaRecAt_refines` instantiates them.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `takeEidx` at the whole array -/

theorem eidxCopyUpto_size (xs : Array EIdx) : ∀ (K i : Nat) (out : Array EIdx), xs.size - i = K →
    i ≤ xs.size → eidxCopyUpto xs xs.size i out = out ++ xs.extract i xs.size := by
  intro K
  induction K with
  | zero =>
    intro i out hK hi
    have : i = xs.size := by omega
    subst this
    rw [eidxCopyUpto]
    simp
  | succ K ih =>
    intro i out hK hi
    rw [eidxCopyUpto]
    have hlt : i < xs.size := by omega
    simp only [hlt, and_self, ↓reduceDIte]
    rw [ih (i + 1) _ (by omega) (by omega)]
    apply Array.ext'
    simp only [Array.toList_append, Array.toList_push, Array.toList_extract, List.extract,
      List.append_assoc, List.singleton_append]
    congr 1
    have hl : i < xs.toList.length := by simpa using hlt
    rw [List.drop_eq_getElem_cons hl, show xs.size - i = (xs.size - (i + 1)) + 1 by omega,
      List.take_succ_cons]
    simp

theorem takeEidx_size (xs : Array EIdx) : takeEidx xs xs.size = xs := by
  unfold takeEidx
  rw [eidxCopyUpto_size xs xs.size 0 #[] (by omega) (by omega)]
  simp

/-! ## `iota_rec_c(mode, vis, d, c, us, so, sn)` -/

section cRun
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx)
  (us : LsIdx) (sargs : Array EIdx) (n : Nat)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem cT_run_find (a : AState) (hf : ∀ cv mI rP rules, fe.find? c ≠ some (.recInfo cv mI rP rules)) :
    (iotaRecCT mode r fe depth c us sargs n).run a = .ok (none, a) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem cT_run_arity (a : AState) (cv : IConstantVal) (mI rP : Nat) (rules : List IRecRule)
    (hf : fe.find? c = some (.recInfo cv mI rP rules)) (hn : n ≠ mI + 1) :
    (iotaRecCT mode r fe depth c us sargs n).run a = .ok (none, a) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem cT_run_check (a : AState) (cv : IConstantVal) (mI rP : Nat) (rules : List IRecRule)
    (usl : Nat) (pe : Option EIdx)
    (hf : fe.find? c = some (.recInfo cv mI rP rules)) (hn : n = mI + 1)
    (hl : a.store.lss.viewLen us = some usl) (hp : (peelPis (mI + 1) cv.type).run a = .ok (pe, a))
    (hc : ¬ ((takeEidx sargs n).toList.length = mI + 1 ∧ usl = cv.levelParams.length ∧
      pe.isSome = true)) :
    (iotaRecCT mode r fe depth c us sargs n).run a = .ok (none, a) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem cT_eq_major (a : AState) (cv : IConstantVal) (mI rP : Nat) (rules : List IRecRule)
    (usl : Nat) (pe : Option EIdx)
    (hf : fe.find? c = some (.recInfo cv mI rP rules)) (hn : n = mI + 1)
    (hl : a.store.lss.viewLen us = some usl) (hp : (peelPis (mI + 1) cv.type).run a = .ok (pe, a))
    (hc : (takeEidx sargs n).toList.length = mI + 1 ∧ usl = cv.levelParams.length ∧
      pe.isSome = true) :
    (iotaRecCT mode r fe depth c us sargs n).run a =
      (iotaRecMajorT mode r fe depth c us cv mI rP rules (takeEidx sargs n).toList).run a := by
  sorry

-/

end cRun

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`iota_rec_c` refines the recursor's block, both outcomes**: the errors are
`iota_rec_major`'s. -/
theorem c_ref (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us so sn : Word) (xs : Array EIdx)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hcw : HW c) (hus : HW us) (hsa : SpineR s₀.mem so sn xs)
    (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (MajorG p n) (irCE p (n + 1) s₀.mem mode vis d c us so sn)
      (iotaRecCT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (decI us) xs
        xs.size) a₀ (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`iota_rec_c` refines the recursor's block** (`c_ref`'s ok half). -/
theorem iotaRecC_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us so sn : Word) (xs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us →
    SpineR s₀.mem so sn xs → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p (n + 1) "iota_rec_c" [mode, vis, d, c, us, so, sn]
      (iotaRecCT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (decI us) xs
        xs.size) decOptR s₀ a₀ dn vis fe MM eb ResW :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us so sn xs hS hm4 hebm hcw hus hsa hsat =>
    RefE.coreSpec (irCE_spec p hp.recC hp.major (n + 1) s₀ mode vis d c us so sn)
      (c_ref p hp hc hw hsup hmtc hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us so sn xs
        hS hm4 hebm hcw hus hsa hsat)
-/

/-! ## `iota_rec_at(mode, vis, d, hd, so, sn)` -/

section atRun
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (hd : EIdx)
  (sargs : Array EIdx) (n : Nat)

theorem at_run_tag (a : AState) (ht : hd.tag ≠ ETag.const) :
    (iotaRecAt mode r fe depth hd sargs n).run a = .ok (none, a) := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem at_eq_c (a : AState) (c : NIdx) (us : LsIdx)
    (ht : hd.tag = ETag.const) (hv : a.store.viewConst hd = some (c, us)) :
    (iotaRecAt mode r fe depth hd sargs n).run a = (iotaRecCT mode r fe depth c us sargs n).run a := by
  sorry

-/

end atRun

/-- **`iota_rec_at` refines `iotaRecAt`, both outcomes**: the errors are `iota_rec_c`'s. -/
theorem at_ref (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d hd so sn : Word) (xs : Array EIdx) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (hpre : SlotPre s₀ a₀ dn vis fe M eb mode) (hhd : HW hd) (hsa : SpineR s₀.mem so sn xs)
    (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (MajorG p n) (irAtE p (n + 1) s₀.mem mode vis d hd so sn)
      (iotaRecAt (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE hd) xs xs.size) a₀
      (CorePost decOptR dn s₀.mem vis fe M eb ResW) := by
  sorry

/-- **`iota_rec_at` refines `iotaRecAt`** (`IotaRecAtOK`, what `whnf_app` assumes; `at_ref`'s ok
half), from the callees' specs and the stub assumption `ErecKeptRec` (the callees the pieces read
the record pool after leave it alone). -/
theorem iotaRecAt_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) : IotaRecAtOK p (n + 1) :=
  fun F s₀ a₀ dn vis fe M eb mode d hd so sn xs hnF hn62 hpre hhd hsa hsat =>
    RefE.coreSpec (irAtE_spec p hp.iotaRecAt hp.recC hp.major (n + 1) s₀ mode vis d hd so sn)
      (at_ref p hp hc hw hsup hmtc hEI hER hEK n hk F s₀ a₀ dn vis fe M eb mode d hd so sn xs
        (by omega) (by omega) hpre hhd hsa hsat)

end L.Arena
