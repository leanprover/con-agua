module

import ConAgua.Arena.RecLayout.CapsDec
import ConAgua.Arena.IlpRdReal
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPartsSpec.BlockCounts
import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndRealIlpL
public import ConAgua.Arena.RecCheckSpec.ToiW
import all ConAgua.Arena.RecCheck
public import ConAgua.Verdict.PosFt
import ConRon.Bridge.Inductives.Positivity
import ConAgua.L.WordOff
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# `target_outside_inst`: one model and one refinement for both outcomes

`toiE` (`l_model … unified`): `family_telescope` (in the verdict closure) and `e_view` through their
calls, every other callee through its `Option` model (`inst_lp_fast` through its run, `callW`, met
by its stub contract `IlpRd`). `toi_ref` refines `targetOutsideInst` for both outcomes under
`StageC`: the four rejects are the twin's `fail`s (the structure is not stored or not an inductive;
`inst_pis_with` does not bind the parameters; the type former does not end in a sort), the
telescope's errors `ft_ref`'s (under `WtG`). It is the first step of
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
  specs [callW_spec p n "env_find",
    erToIw_specW p P.alloc P.copy P.eti n, callW_spec p n "inst_lp_fast", instPisWith_spec p P.v P.ipw P.hi1 n,
    piBinders_spec p P.alloc P.icopy P.v P.sc P.pb n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `target_outside_inst` gives besides the twin's `(index count, sort)` `x` (from `m`): the
result words, the stage relation, the growth, the abstraction memo, the positivity memos (the core's
`hb` memo moves inside `family_telescope`). -/
structure ToiPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem)
    (r : List Word) (m' : Mem) (x : Nat × LIdx) (a' : AState) : Prop where
  res : ToiR r x
  stage : StageR vis fe m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  pos : PosMR m → PosMR m'

section sims
variable {p : Prog} (P : ToiProg p) (hIlpf : IlpfF p) (hq : KnotStageProg p) (hF : FtProg p)
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

include P hIlpf hq hF in
/-- **`target_outside_inst` refines `targetOutsideInst`, both outcomes** under `StageC`: the stored
inductive (`env_find`, its kind word), its telescope (`family_telescope`, `ft_ref`), its level
parameters (`er_to_iw`, `cv_lps`'s reading), `inst_lp_fast` through its stub contract
(`IlpRd.realC`), `inst_pis_with`, `pi_binders`, the sort (`e_view`); the four rejects are the
twin's `fail`s, the telescope's errors `ft_ref`'s (under `WtG`). -/
theorem toi_ref (henv : ConLeche.EnvWF env) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {I us dso dsl : Word} {ds : List EIdx}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hI : H I) (hu : H us)
    (hds : DecB (fun m => decHL m dso.toNat dsl.toNat) m ds) (hb : dso.toNat + dsl.toNat < 2 ^ 64) :
    RefE (WtG p) (toiE p n m vis I us dso dsl)
      (ConRon.Arena.targetOutsideInst V fe (decI I) (decI us) ds) a
      (fun v x a' => ToiPost dn vis fe m v.1 v.2 x a') := by
  cases n with
  | zero => rw [toiE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hS := hC.stage
  have hE := hS.check.env
  have hR := hS.check.arena.base
  rw [toiE.arm1, ConRon.Arena.targetOutsideInst]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 hef => ?_
  obtain ⟨hm1, rfl⟩ : m = m1 ∧ r1 = findRes m vis I := by
    obtain ⟨s', rfl, h1, -, h3⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (envFind_spec p P.rowGet hF.brg P.find n _ vis I) hef
    exact ⟨h1.symm, h3⟩
  subst hm1
  dsimp only [toiE.k_env_find]
  by_cases hf0 : (findRes m vis I).headD 0 = 0
  · refine RefE.abortAt hf0 ?_
    rw [findRes_miss hE hI hf0]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  refine RefE.pass hf0 ?_
  obtain ⟨hfind, ci, hci⟩ := findRes_hit hE hI hf0
  rw [hci] at hfind
  generalize (findRes m vis I).tail.headD 0 = q at hfind hci ⊢
  rw [hfind]
  obtain ⟨w0, hw0⟩ := decCI_rd hci
  by_cases hk3 : erRd m q ≠ 3
  · refine RefE.abortAt hk3 ?_
    cases ci with
    | indInfo cv caps =>
      exfalso; apply hk3
      have hk := decCI_indInfo_kind hci
      rw [(erRd_of_erecP hw0).1]
      simp only [nat?, hw0, Option.map_some, Option.some.injEq] at hk
      exact UInt64.toNat_inj.mp (by simpa using hk)
    | _ => exact fun _ => ErrClaim.fail _ _ (by decide)
  refine RefE.pass hk3 ?_
  have hk3' : nat? (erecP m) q.toNat = some 3 := by
    have h3' : erRd m q = 3 := Decidable.not_not.mp hk3
    rw [(erRd_of_erecP hw0).1] at h3'
    simp [nat?, hw0, h3']
  obtain ⟨cv, caps, rfl, hcaps⟩ := decCI_kind3 hci hk3'
  have hcv : decCV (erecP m) (q.toNat + CI.cv.toNat) = some cv := by
    simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hci
    obtain ⟨kd, hkd, hci⟩ := hci
    rw [hk3'] at hkd; cases hkd
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at hci
    obtain ⟨cv', h1, _, _, h2⟩ := hci
    cases h2; exact h1
  obtain ⟨v16, hv16⟩ := decCI_indInfo_word hci
  have hq64 := L.Arena.erecP_lt64 hv16
  have := CI.indCaps_ge
  have e1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e5 : (q + 5).toNat = q.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
  -- the twin's inductive and its denotation
  obtain ⟨IP, cc, -, hcc, he⟩ := hC.check.ienv.hit _ _ hfind
  obtain ⟨cvP, capsP, hcvP, hcapsP, rfl⟩ := ConRon.Bridge.Inductives.denoteCI_indInfo_inv hcc
  have hws : ConLeche.Expr.WScoped 0 cvP.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (henv.consts _ (ConLeche.Env.find?_mem he)).1
  -- `family_telescope`
  have hcvB : DecB (fun m => decCVp m (q + 1).toNat) m cv := by
    show decCV (erA (truncM m)) _ = _
    rw [truncM_erA, e1]; exact hcv
  have hFT := ft_ref hq hF henv n (by omega) (cvq := q + CI.cv) (capsq := q + CI.indCaps) hC hA hcvB
    (by rw [e5]; exact hcaps) hcvP hws
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => rfl) (ftE_spec p hF n _ vis _ _) (fun hG => hG.nv)
    id hFT fun r3 s3 tyC a2 hc3 _ hr3 hP3 => ?_
  dsimp only [toiE.k_family_telescope]
  obtain ⟨s3', hs3', -, hfx3⟩ := triple_of_callE (ftE_spec p hF n ⟨m, Locals.init []⟩ vis (q + 1) (q + 5)) hc3
  have hS3 := hP3.stage.stage
  have hg3 := hP3.grow
  generalize s3.mem = m3 at hS3 hg3 hP3 hs3' ⊢
  -- `er_to_iw` (`cv_lps`'s reading)
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r4 m4 hlp => ?_
  dsimp only [toiE.k_er_to_iw]
  have hcv3 : decCVp m3 (q + 1).toNat = some cv := by rw [e1]; exact hg3.ext.decCV hcv
  have hlp' : cvLpsW (n + 1) m3 (q + 1) = some (r4, m4) := by
    simp only [cvLpsW, Nat.add_sub_cancel]
    rw [show q + 1 + 1 = q + 2 by rw [UInt64.add_assoc]; rfl,
      show q + 1 + 2 = q + 3 by rw [UInt64.add_assoc]; rfl]
    exact hlp
  obtain ⟨hS4, hg4, -, hdec4, -⟩ := L.Ind.cvLpsW_stage hlp' hS3 hcv3
  -- `inst_lp_fast`
  refine RefE.bindLift (fun _ => rfl) fun r5 m5 h5 => ?_
  obtain ⟨tl, a4, hrun5, ⟨hS5, hg5, htlH, htld⟩, ⟨_, _, hfA, hfC, hf5⟩, hA5⟩ :=
    IlpRd.realC hIlpf hP3.stage n CWF _ _ _ _ cv.levelParams m4 m5 a2 r5 hu hP3.hw
      ⟨rfl, erToIwW_iwFr hlp⟩ hS4 hdec4 h5
  rw [CWF_eq, hP3.dec] at hrun5
  refine ⟨_, _, hrun5, ?_⟩
  dsimp only [toiE.k_inst_lp_fast]
  have hg35 := (hg4.trans hg5)
  have hg5' := (hg3.trans hg35)
  -- `inst_pis_with`
  refine RefE.bindLift (fun _ => rfl) fun r6 m6 h6 => ?_
  obtain ⟨x6, a5, hrun6, hS6, hg6, hx6⟩ := instW_okB (dn := dn) h6 hS5 htlH
    (DecB.grow (OMono.decHL _ _) hg5' hds) hb
  rw [htld] at hrun6
  refine ⟨_, _, hrun6, ?_⟩
  dsimp only [toiE.k_inst_pis_with]
  cases x6 with
  | none => exact RefE.abortAt hx6 fun _ => ErrClaim.fail _ _ (by decide)
  | some ty =>
  obtain ⟨hok, hty⟩ := hx6
  refine RefE.pass (by rw [hok]; decide) ?_
  -- `pi_binders`
  refine RefE.bindLift (fun _ => rfl) fun r7 m7 h7 => ?_
  obtain ⟨bs, e, hrun7, hdec7, hb7, he7, hS7, hg7, -⟩ := piBW_cwf h7 hS6 hty.1
  rw [hty.2] at hrun7
  refine ⟨_, _, hrun7, ?_⟩
  dsimp only [toiE.k_pi_binders]
  rw [L.getD_two] at he7
  -- `e_view`
  refine RefE.bindCall (Q := fun b a' v => b.2 = m7 ∧ a' = a5 ∧ ViewR b.1 v) (fun _ => rfl)
    (fun hG _ h8 => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h8)
    (fun ⟨r8, m8⟩ h8 => by
      obtain ⟨s8, hs8, hs8e, hne8, hr8⟩ := triple_of_callW (s₀ := ⟨m7, Locals.init []⟩)
        (eView_spec p P.v n ⟨m7, Locals.init []⟩ (r7.tail.tail.headD 0)) h8
      subst hs8e hs8
      obtain ⟨v, hv, hvr⟩ := eViewW_ok m7 a5 hS7.check.arena.base _ (by rw [← hr8]; exact hne8)
      rw [he7] at hv
      exact ⟨v, a5, view_run _ _ _ hv, rfl, rfl, hr8 ▸ hvr⟩)
    fun r8 m8 v a8 _ _ ⟨hm8, ha8, hvr⟩ => ?_
  subst hm8 ha8
  dsimp only [toiE.k_e_view]
  by_cases h2 : r8.headD 0 = 2
  · refine RefE.pass (by simpa using h2) ?_
    cases v
    case sort u =>
      obtain ⟨-, hu1, hu2⟩ := hvr
      rw [L.getD_one] at hu1 hu2
      refine RefE.ret rfl ⟨⟨rfl, ?_, hu1, hu2⟩, hS7, ((hg3.trans hg35).trans hg6).trans hg7,
        ((((AFr.iw (erToIwW_iwFr hlp)).trans hA5).trans (instW_afr _ _ _ _ _ _ _ h6)).trans
          (piBW_afr _ _ _ _ _ _ h7)) hP3.abs,
        fun hPm => by
          have hP3m : PosMR m3 := by
            rw [← hs3']; exact ftE_pos hq.closed hF hR hcvB hPm hfx3
          exact hP3m.fr ((((erToIwW_mfr hlp).trans (MFr.of_frame hf5 hfA hfC)).trans
            (instW_mfr _ _ _ _ _ _ _ h6)).trans (piBW_mfr _ _ _ _ _ _ h7))⟩
      simp only [List.headD_cons]
      rw [L.getD_one] at hdec7
      exact (decHL_length _ hdec7).symm
    all_goals (exfalso; revert hvr; simp only [ViewR, h2]; simp)
  refine RefE.abortAt (by simpa using h2) ?_
  cases v with
  | sort u => exact absurd hvr.1 h2
  | _ => exact fun _ => ErrClaim.fail _ _ (by decide)

end sims

end L.Ind

end
