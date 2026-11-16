module

public import ConAgua.Arena.WhnfIotaRecRefine2
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import ConRon.Bridge.Grind
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# `iota_rec_at`'s pieces, part 3: the top

`iota_rec_at` itself (the recursor's telescope, at the record its caller found):
`iotaRecAt_refines'` proves `WhnfCore.lean`'s `IotaRecAtOK` from the
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

/-! ## `iota_rec_at(mode, vis, d, c, us, q, so, sn)` -/

/-- **`iota_rec_at` refines `iotaRecAt`, both outcomes**: the recursor's telescope, then
`iota_rec_major`'s (its errors). -/
theorem at_ref (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d c us q so sn : Word) (xs : Array EIdx) (cv : IConstantVal) (mI rP : Nat) (isK : Bool)
    (rules : List IRecRule) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (hpre : SlotPre s₀ a₀ dn vis fe M eb mode) (hcw : HW c) (hus : HW us)
    (hq : decCI (erecP s₀.mem) q.toNat = some (.recInfo cv mI rP isK rules))
    (hfind : fe.find? (decI c) = some (.recInfo cv mI rP isK rules))
    (hsa : SpineR s₀.mem so sn xs) (hsz : xs.size = mI + 1)
    (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (MajorG p n) (irAtE p (n + 1) s₀.mem mode vis d c us q so sn)
      (iotaRecAt (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c)
        (decI us) cv mI rP isK rules xs) a₀
      (CorePost decOptR dn s₀.mem vis fe M eb ResW) := by
  sorry

/-- **`iota_rec_at` refines `iotaRecAt`** (`IotaRecAtOK`, what `whnf_app_iota` and `whnf_stuck`
assume; `at_ref`'s ok half), from the callees' specs and the stub assumption `ErecKeptRec` (the
callees the pieces read the record pool after leave it alone). -/
theorem iotaRecAt_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) : IotaRecAtOK p (n + 1) :=
  fun F s₀ a₀ dn vis fe M eb mode d c us q so sn xs cv mI rP isK rules hnF hn62 hpre hcw hus hq hfind
      hsa hsz hsat =>
    RefE.coreSpec (irAtE_spec p hp.iotaRecAt hp.major (n + 1) s₀ mode vis d c us q so sn)
      (at_ref p hp hc hw hmtc hEI hER hEK n hk F s₀ a₀ dn vis fe M eb mode d c us q so sn xs cv mI rP
        isK rules (by omega) (by omega) hpre hcw hus hq hfind hsa hsz hsat)

end L.Arena
