module

import ConAgua.Arena.RecGenSpec.DecCIIndCv
import ConAgua.Arena.RecClassSpec.ClassNPcOf
import ConAgua.Arena.IlpRdReal
import ConAgua.Arena.RecGenSpec.OcW
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPartsSpec.BlockCounts
import ConAgua.Arena.IndPosSpec.EntryW
import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndPartsSpec.RecTW
public import ConAgua.Arena.IndPosSpec.NoGoStep
public import ConAgua.Arena.IndRealIlpL
public import ConAgua.Arena.RecCheckSpec.ToiW
public import ConAgua.Arena.TwinStep
import all ConAgua.Arena.RecCheck

@[expose] public section

/-!
# `target_outside_inst`: one model and one refinement for both outcomes

`toiE` (`l_model … unified`): every callee is outside the verdict closure, called through its
`Option` model (`inst_lp_fast` through its run, `callW`, met by its stub contract `IlpRd`), but
`e_view` (through its run, `callE`: its spec's post is a list, `r ≠ [] ∧ r = eViewW …`).
`toi_ref` refines `targetOutsideInst` for both outcomes: the four rejects are the twin's `fail`s
(the structure is not stored or not an inductive; `inst_pis_with` does not bind the parameters;
the type former does not end in a sort). It is the first step of
`target_major_of_outside_tail`'s refinement (`tmt_ref`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/- ronsync2 stage 2: commented out (statement at the old twin/L)
l_model toiE_spec (p : Prog) (P : ToiProg p)
  fns [P.toi ↦ toiE]
  specs [callW_spec p n "env_find", erToIw_specW p P.alloc P.copy P.eti n,
    callW_spec p n "inst_lp_fast", instPisWith_spec p P.v P.ipw P.hi1 n,
    piBinders_spec p P.alloc P.icopy P.v P.sc P.pb n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]
-/

/-- What `target_outside_inst` gives besides the twin's `(index count, sort)` `x` (from `m`): the
result words, the stage invariant, the growth, the frames. -/
structure ToiPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem)
    (r : List Word) (m' : Mem) (x : Nat × LIdx) (a' : AState) : Prop where
  res : ToiR r x
  stage : StageR vis fe m' a'
  grow : IWGrow m m'
  mfr : MFr [] [] m m'
  afr : AFr m m'

section sims
variable {p : Prog} (P : ToiProg p) (hIlpf : IlpfF p)
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

/- ronsync2 stage 2: commented out (statement at the old twin/L)
include P hIlpf in
/-- **`target_outside_inst` refines `targetOutsideInst`, both outcomes** (`inst_lp_fast` through
its stub contract at the `StageC` start, `IlpRd.realC`). -/
theorem toi_ref (n : Nat) {m : Mem} {a : AState} {I us dso dsl : Word} {ds : List EIdx}
    (hC : StageC dn vis fe env m a) (hI : H I) (hu : H us)
    (hds : DecB (fun m => decHL m dso.toNat dsl.toNat) m ds) (hb : dso.toNat + dsl.toNat < 2 ^ 64) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (toiE p n m vis I us dso dsl)
      (ConRon.Arena.targetOutsideInst fe (decI I) (decI us) ds) a
      (fun v x a' => ToiPost dn vis fe m v.1 v.2 x a') := by
  cases n with
  | zero => rw [toiE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hS := hC.stage
  rw [toiE.arm1, ConRon.Arena.targetOutsideInst]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r2 m2 hef => ?_
  obtain ⟨hm2, hfind, hdec⟩ := envFindW_found hef hS.check.env hI
  subst m2
  dsimp only [toiE.k_env_find]
  by_cases hf0 : r2.headD 0 = 0
  · have hfn : fe.find? (decI I) = none := by rw [hfind, decFound, ite_eq_left hf0]
    refine RefE.abortAt hf0 ?_
    simp only [hfn]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  refine RefE.pass hf0 ?_
  obtain ⟨ci, hci⟩ := hdec hf0
  have hfci : fe.find? (decI I) = some ci := by rw [hfind, decFound, ite_eq_right hf0, hci]
  obtain ⟨kk, hkk, hcase⟩ := decCI_ind_cases hci
  have hkr := erec_nat (w := r2.tail.headD 0) (c := 0) (by simpa using hkk) (by decide)
  rw [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at hkr
  rw [hfci]
  by_cases hk3 : rdW (m.arr64 EREC) (r2.tail.headD 0) ≠ 3
  · refine RefE.abortAt hk3 ?_
    have hkind : kk ≠ 3 := by
      intro hk3'
      apply hk3
      rw [hkr.1, hk3']; rfl
    obtain ⟨-, hno⟩ := hcase.resolve_left (fun ⟨hh, _⟩ => hkind hh)
    cases ci with
    | indInfo cv caps => exact absurd rfl (hno cv caps)
    | _ => exact fun _ => ErrClaim.fail _ _ (by decide)
  refine RefE.pass hk3 ?_
  have hkind : kk = 3 := by
    have : rdW (m.arr64 EREC) (r2.tail.headD 0) = 3 := by simpa using hk3
    rw [hkr.1] at this
    have := congrArg UInt64.toNat this
    rwa [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; exact hkr.2)] at this
  obtain ⟨-, cv, caps, rfl, -⟩ := hcase.resolve_right (fun ⟨hne, _⟩ => hne hkind)
  dsimp only
  have hcvP := decCI_ind_cv hci
  have hcvA : decCV (erA m) ((r2.tail.headD 0).toNat + 1) = some cv :=
    ArrExt.decCV (IWGrow.erecExt (IWGrow.refl m)) hcvP
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hcvA
  have hqE := (Array.getElem?_eq_some_iff.mp hw2).1
  have hE64 := hS.iw.erSize
  have e1 : rdW (m.arr64 EREC) (r2.tail.headD 0 + 2) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hqE ⊢; omega) hw1
  have e2 : rdW (m.arr64 EREC) (r2.tail.headD 0 + 3) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hqE ⊢; omega) hw2
  rw [e1, e2]
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (hslice?_bound _ _ _ _ hsl h0)
  -- `er_to_iw`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r3 m3 h3 => ?_
  dsimp only [toiE.k_er_to_iw]
  obtain ⟨-, hr3t, hdec3, hS3, hg3, -⟩ := L.Arena.erToIwW_stage h3 hS hsrc
  rw [hr3t]
  have hdecL : decHL m3 (r3.headD 0).toNat w2.toNat = some cv.levelParams := by rw [hdec3]; exact hsl
  have hcv3 : decCV (erA m3) ((r2.tail.headD 0).toNat + 1) = some cv :=
    ArrExt.decCV (IWGrow.erecExt hg3) hcvP
  obtain ⟨wt, hwt, hwtH, hwtE⟩ := decCV_typeW hcv3
  have hqE3 := (Array.getElem?_eq_some_iff.mp hwt).1
  have hE364 := hS3.iw.erSize
  have et : rdW (m3.arr64 EREC) (r2.tail.headD 0 + 4) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hqE3 ⊢; omega) hwt
  rw [et]
  -- `inst_lp_fast`
  refine RefE.bindLift (fun _ => rfl) fun r4 m4 h4 => ?_
  obtain ⟨x4, a4, hrun4, ⟨hS4, hg4, hx4⟩, -, hA4⟩ := (IlpRd.realC hIlpf hC) n CWF (r3.headD 0) w2 us wt
    cv.levelParams m3 m4 a r4 hu hwtH ⟨rfl, erToIwW_iwFr h3⟩ hS3 hdecL h4
  rw [CWF_eq, ← hwtE] at hrun4
  refine ⟨_, _, hrun4, ?_⟩
  dsimp only [toiE.k_inst_lp_fast]
  have hg34 := (hg3.trans hg4)
  -- `inst_pis_with`
  refine RefE.bindLift (fun _ => rfl) fun r5 m5 h5 => ?_
  obtain ⟨hx4H, rfl⟩ := hx4
  obtain ⟨x5, a5, hrun5, hS5, hg5, hx5⟩ := instW_okB h5 hS4 hx4H
    (DecB.grow (OMono.decHL _ _) hg34 hds) hb
  refine ⟨_, _, hrun5, ?_⟩
  dsimp only [toiE.k_inst_pis_with]
  cases x5 with
  | none => exact RefE.abortAt hx5 fun _ => ErrClaim.fail _ _ (by decide)
  | some ty =>
  obtain ⟨hok, hty⟩ := hx5
  refine RefE.pass (by rw [hok]; decide) ?_
  -- `pi_binders`
  refine RefE.bindLift (fun _ => rfl) fun r6 m6 h6 => ?_
  obtain ⟨bs, e, hrun6, hdec6, hb6, he6, hS6, hg6, -⟩ := piBW_cwf h6 hS5 hty.1
  rw [hty.2] at hrun6
  refine ⟨_, _, hrun6, ?_⟩
  dsimp only [toiE.k_pi_binders]
  rw [getD_two] at he6
  -- `e_view`
  refine RefE.bindCall (Q := fun b a' v => b.2 = m6 ∧ a' = a5 ∧ ViewR b.1 v) (fun _ => rfl)
    (fun hG _ h7 => ErrClaim.of_callE_nv hG (_root_.L.Checker.nv_mem (by decide +kernel)) h7)
    (fun ⟨r7, m7⟩ h7 => by
      obtain ⟨s7, hs7, hs7e, hne7, hr7⟩ := triple_of_callW (s₀ := ⟨m6, Locals.init []⟩)
        (eView_spec p P.v n ⟨m6, Locals.init []⟩ (r6.tail.tail.headD 0)) h7
      subst hs7e hs7
      obtain ⟨v, hv, hvr⟩ := eViewW_ok m6 a5 hS6.check.arena.base _ (by rw [← hr7]; exact hne7)
      rw [he6] at hv
      exact ⟨v, a5, view_run _ _ _ hv, rfl, rfl, hr7 ▸ hvr⟩)
    fun r7 m7 v a7 _ _ ⟨hm7, ha7, hvr⟩ => ?_
  subst hm7 ha7
  dsimp only [toiE.k_e_view]
  by_cases h2 : r7.headD 0 = 2
  · refine RefE.pass (by simpa using h2) ?_
    cases v
    case sort u =>
      obtain ⟨-, hu1, hu2⟩ := hvr
      rw [getD_one] at hu1 hu2
      refine RefE.ret rfl ⟨⟨rfl, ?_, hu1, hu2⟩, hS6, hg34.trans (hg5.trans hg6),
        (((envFindW_mfr hef).trans (erToIwW_mfr h3)).trans ((IlpFr.real hIlpf).mfr h4)).trans
          ((instW_mfr _ _ _ _ _ _ _ h5).trans (piBW_mfr _ _ _ _ _ _ h6)),
        (((AFr.iw (erToIwW_iwFr h3)).trans hA4).trans (instW_afr _ _ _ _ _ _ _ h5)).trans
          (piBW_afr _ _ _ _ _ _ h6)⟩
      simp only [List.headD_cons]
      rw [getD_one] at hdec6
      exact (decHL_length _ hdec6).symm
    all_goals (exfalso; revert hvr; simp only [ViewR, h2]; simp)
  refine RefE.abortAt (by simpa using h2) ?_
  cases v with
  | sort u => exact absurd hvr.1 h2
  | _ => exact fun _ => ErrClaim.fail _ _ (by decide)
-/

end sims

end L.Ind

end
