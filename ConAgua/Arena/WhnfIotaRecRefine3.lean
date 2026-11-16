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
    (hsa : SpineR s₀.mem so sn xs) (hsz' : xs.size = mI + 1)
    (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (MajorG p n) (irAtE p (n + 1) s₀.mem mode vis d c us q so sn)
      (iotaRecAt (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c)
        (decI us) cv mI rP isK rules xs) a₀
      (CorePost decOptR dn s₀.mem vis fe M eb ResW) := by
  have hS := hpre.rel
  have hsz : xs.size = sn.toNat := hsa.size
  have k5 : erRd s₀.mem q = 5 := Classical.byContradiction fun h =>
    (decCI_rec_rd (erRdOK s₀.mem) hq).2 h _ _ _ _ _ rfl
  obtain ⟨cv', rules', heq, hcv, hrules⟩ := (decCI_rec_rd (erRdOK s₀.mem) hq).1 k5
  injection heq with e1 e2 e3 e4 e5
  subst e1 e5
  obtain ⟨-, -, -, -, htyw, htype⟩ := decCV_rd_ci (erRdOK s₀.mem) hcv
  simp only [irAtE]
  rw [iotaRecAt_eq]
  cases n with
  | zero => rw [callW_zero, liftE_none, irAtE.k_peel_pis.eq_1]; exact RefE.of_cls0 (by simp)
  | succ N =>
  refine RefE.onlySim (fun _ => irAtE.k_peel_pis.eq_1 ..) (fun _ _ h => h) fun rp m3 c3 => ?_
  obtain ⟨t3, ht3, hm3, -, -, hrunP⟩ := triple_of_callW
    (peelPis_refines' p hp.spine.peel (N + 1) ⟨s₀.mem, Locals.init []⟩ a₀ hS.arena.base sn _ htyw) c3
  have hm3' : s₀.mem = m3 := hm3.symm.trans ht3
  subst hm3'
  have hrunP' : (peelPis (mI + 1) cv.type).run a₀ = .ok (decOpt (rp.headD 0) (rp.tail.headD 0), a₀) := by
    rw [htype, ← hsz', hsz]; exact hrunP
  refine RefE.bind_right hrunP' ?_
  dsimp only [irAtE.k_peel_pis]
  by_cases p0 : rp.headD 0 = 0
  · rw [ite_eq_left p0]
    have : decOpt (rp.headD 0) (rp.tail.headD 0) = none := by unfold decOpt; rw [ite_eq_left p0]
    rw [this]
    exact RefE.ret rfl (CorePost.ret hS rfl
      ⟨by show HW (0 : Word); unfold HW; decide, by show HW (0 : Word); unfold HW; decide⟩)
  rw [ite_eq_right p0]
  have : decOpt (rp.headD 0) (rp.tail.headD 0) = some (decE (rp.tail.headD 0)) := by
    unfold decOpt; rw [ite_eq_right p0]
  rw [this]
  have hM := major_ref p hp hc hw hmtc hEI hER hEK N (hk.mono (by omega)) F (by omega) (by omega)
    s₀ a₀ dn vis fe M eb mode d c us q so sn cv rules xs hS hpre.mode4 hpre.eb_mode hcw hus
    hcv hrules ⟨_, _, _, _, hfind⟩ hsa hsat (by rw [← e2, ← hsz, hsz'])
  rw [← e2, ← e3, ← e4] at hM
  exact RefE.tail_eq (k := irAtE.k_iota_rec_major p) (G' := MajorG p N)
    (fun _ => rfl) (fun _ => rfl) (fun hG => ⟨hG.knot.mono (Nat.le_succ N), hG.nv, hG.pm, hG.fire⟩) rfl
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩) hM

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
