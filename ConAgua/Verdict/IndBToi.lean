import ConAgua.Arena.RecGenSpec.DecCIIndCv
import ConAgua.Arena.RecClassSpec.ClassNPcOf
import ConAgua.Arena.IlpRdReal
import ConAgua.Arena.RecGenSpec.OcW
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

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

l_model toiE_spec (p : Prog) (P : ToiProg p)
  fns [P.toi ↦ toiE]
  specs [envFind_specW p P.ix P.rowGet P.find n, erToIw_specW p P.alloc P.copy P.eti n,
    callW_spec p n "inst_lp_fast", instPisWith_spec p P.v P.ipw P.hi1 n,
    piBinders_spec p P.alloc P.icopy P.v P.sc P.pb n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `target_outside_inst` gives besides the twin's `(index count, sort)` `x` (from `m`): the
result words, the stage invariant, the growth, the frames. -/
structure ToiPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem)
    (r : List Word) (m' : Mem) (x : Nat × LIdx) (a' : AState) : Prop where
  res : ToiR r x
  stage : StageR dn vis fe m' a'
  grow : IWGrow m m'
  mfr : MFr [] [] m m'
  afr : AFr m m'

section sims
variable {p : Prog} (P : ToiProg p) (hIlpf : IlpfF p)
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

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
  rw [toiE.arm1]
  rcases hef : envFindW m I vis with _ | ⟨r2, m2⟩
  · rw [liftE_none, toiE.k_env_find.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm2, hfind, hdec⟩ := envFindW_found hef hS.1.env hI
  subst m2
  rw [ConRon.Arena.targetOutsideInst]
  by_cases hf0 : r2.headD 0 = 0
  · rw [toiE.k_env_find.abort1 p n us dso dsl r2 m hf0]
    have hfn : fe.find? (decI I) = none := by rw [hfind, decFound, ite_eq_left hf0]
    simp only [hfn]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  obtain ⟨ci, hci⟩ := hdec hf0
  have hfci : fe.find? (decI I) = some ci := by rw [hfind, decFound, ite_eq_right hf0, hci]
  obtain ⟨kk, hkk, hcase⟩ := decCI_ind_cases hci
  have hkr := erec_nat (w := r2.tail.headD 0) (c := 0) (by simpa using hkk) (by decide)
  rw [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at hkr
  by_cases hk3 : rdW (m.arr64 EREC) (r2.tail.headD 0) ≠ 3
  · rw [toiE.k_env_find.abort2 p n us dso dsl r2 m hf0 hk3]
    have hkind : kk ≠ 3 := by
      intro hk3'
      apply hk3
      rw [hkr.1, hk3']; rfl
    obtain ⟨-, hno⟩ := hcase.resolve_left (fun ⟨hh, _⟩ => hkind hh)
    rw [hfci]
    cases ci with
    | indInfo cv caps => exact absurd rfl (hno cv caps)
    | _ => exact fun _ => ErrClaim.fail _ _ (by decide)
  rw [toiE.k_env_find.arm1 p n us dso dsl r2 m hf0 (by simpa using hk3)]
  have hkind : kk = 3 := by
    have : rdW (m.arr64 EREC) (r2.tail.headD 0) = 3 := by simpa using hk3
    rw [hkr.1] at this
    have := congrArg UInt64.toNat this
    rwa [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; exact hkr.2)] at this
  obtain ⟨-, cv, caps, rfl, -⟩ := hcase.resolve_right (fun ⟨hne, _⟩ => hne hkind)
  rw [hfci]
  dsimp only
  have hcvP := decCI_ind_cv hci
  have hcvA : decCV (erA m) ((r2.tail.headD 0).toNat + 1) = some cv :=
    ArrExt.decCV (IWGrow.erecExt (IWGrow.refl m)) hcvP
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hcvA
  have hqE := (Array.getElem?_eq_some_iff.mp hw2).1
  have hE64 := hS.2.2.2.2.1
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
  rcases h3 : erToIwW n m w1 w2 with _ | ⟨r3, m3⟩
  · rw [liftE_none, toiE.k_er_to_iw.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, toiE.k_er_to_iw.arm1]
  obtain ⟨-, hr3t, hdec3, hS3, hg3, -⟩ := L.Arena.erToIwW_stage h3 hS hsrc
  rw [hr3t]
  have hdecL : decHL m3 (r3.headD 0).toNat w2.toNat = some cv.levelParams := by rw [hdec3]; exact hsl
  have hcv3 : decCV (erA m3) ((r2.tail.headD 0).toNat + 1) = some cv :=
    ArrExt.decCV (IWGrow.erecExt hg3) hcvP
  obtain ⟨wt, hwt, hwtH, hwtE⟩ := decCV_typeW hcv3
  have hqE3 := (Array.getElem?_eq_some_iff.mp hwt).1
  have hE364 := hS3.2.2.2.2.1
  have et : rdW (m3.arr64 EREC) (r2.tail.headD 0 + 4) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hqE3 ⊢; omega) hwt
  rw [et]
  -- `inst_lp_fast`
  rcases h4 : callW p n "inst_lp_fast" [CWF, r3.headD 0, w2, us, wt] m3 with _ | ⟨r4, m4⟩
  · rw [liftE_none, toiE.k_inst_lp_fast.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, toiE.k_inst_lp_fast.arm1]
  obtain ⟨x4, a4, hrun4, ⟨hS4, hg4, hx4⟩, -, hA4⟩ := (IlpRd.realC hIlpf hC) n CWF (r3.headD 0) w2 us wt
    cv.levelParams m3 m4 a r4 hu hwtH ⟨rfl, erToIwW_iwFr h3⟩ hS3 hdecL h4
  rw [CWF_eq, ← hwtE] at hrun4
  have hg34 := (hg3.trans hg4)
  refine RefE.bind_right hrun4 ?_
  -- `inst_pis_with`
  rcases h5 : instW n m4 dso dsl (r4.headD 0) with _ | ⟨r5, m5⟩
  · rw [liftE_none, toiE.k_inst_pis_with.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hx4H, rfl⟩ := hx4
  obtain ⟨x5, a5, hrun5, hS5, hg5, hx5⟩ := instW_okB h5 hS4 hx4H
    (DecB.grow (OMono.decHL _ _) hg34 hds) hb
  refine RefE.bind_right hrun5 ?_
  by_cases hok : r5.headD 0 = 0
  · rw [toiE.k_inst_pis_with.abort1 p n r5 m5 hok]
    cases x5 with
    | none => exact fun _ => ErrClaim.fail _ _ (by decide)
    | some ty => simp only [decOE] at hx5; exact absurd (hx5.1.symm.trans hok) (by decide)
  rw [toiE.k_inst_pis_with.arm1 p n r5 m5 hok]
  cases x5 with
  | none => simp only [decOE] at hx5; exact absurd hx5 hok
  | some ty =>
  obtain ⟨-, hty⟩ := hx5
  -- `pi_binders`
  rcases h6 : piBW n m5 CWF (r5.tail.headD 0) with _ | ⟨r6, m6⟩
  · rw [liftE_none, toiE.k_pi_binders.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, toiE.k_pi_binders.arm1]
  obtain ⟨bs, e, hrun6, hdec6, hb6, he6, hS6, hg6, -⟩ := piBW_cwf h6 hS5 hty.1
  rw [hty.2] at hrun6
  refine RefE.bind_right hrun6 ?_
  -- `e_view`
  cases h7 : callE p n "e_view" [r6.tail.tail.headD 0] m6 with
  | error e7 =>
    rw [toiE.k_e_view.none]
    exact RefE.bind_left fun hG => ErrClaim.of_callE_nv hG (_root_.L.Checker.nv_mem (by decide +kernel)) h7
  | ok q7 =>
  obtain ⟨r7, m7⟩ := q7
  obtain ⟨s7, hs7, hs7e, hne7, hr7⟩ := triple_of_callW (s₀ := ⟨m6, Locals.init []⟩)
    (eView_spec p P.v n ⟨m6, Locals.init []⟩ (r6.tail.tail.headD 0)) (callW_of_callE h7)
  subst hs7e
  dsimp only at hr7 hne7 hs7
  subst hs7
  obtain ⟨v, hv, hvr⟩ := eViewW_ok m6 a5 hS6.1.arena.1 _ (by rw [← hr7]; exact hne7)
  rw [getD_two] at he6
  rw [he6] at hv
  rw [← hr7] at hvr
  refine RefE.bind_right (view_run _ _ _ hv) ?_
  by_cases h2 : r7.headD 0 = 2
  · rw [toiE.k_e_view.arm1 _ _ r7 _ h2]
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
  rw [toiE.k_e_view.abort1 _ _ r7 _ h2]
  cases v with
  | sort u =>
    exfalso
    obtain ⟨hh, -, -⟩ := hvr
    exact h2 hh
  | _ => exact fun _ => ErrClaim.fail _ _ (by decide)

end sims

end L.Ind

end
