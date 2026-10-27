import ConAgua.Arena.Verdict
import ConAgua.Arena.IlpRdReal
import ConAgua.Arena.RecCheckSpec.ToiW
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree

/-!
# Error refinement of `target_outside_inst` (lane `verdicts-b`, helper `ib`)

Mirrors `toiW_ok` (`RecCheckSpec/ToiW`): the four rejects are the twin's `fail`s (the structure is not
stored or not an inductive; `inst_pis_with` does not bind the parameters; the type former does not
end in a sort); every callee is `closedNV`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model toiE_spec (p : Prog) (hf : p.lookup "target_outside_inst" = some targetOutsideInst)
  fns [hf ↦ toiE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (P : ToiProg p) (hIlpf : IlpfF p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

include P hIlpf hnv in
/-- **`target_outside_inst`'s model error claim** (`toiW_ok`'s hypotheses; `inst_lp_fast` through
its stub contract). -/
theorem toiE_claim (n : Nat) {m : Mem} {a : AState} {I us dso dsl : Word} {ds : List EIdx}
    (hC : StageC dn vis fe env m a) (hI : H I) (hu : H us)
    (hds : DecB (fun m => decHL m dso.toNat dsl.toNat) m ds) (hb : dso.toNat + dsl.toNat < 2 ^ 64) :
    ∀ e, toiE p (n + 1) m vis I us dso dsl = .error e →
      ErrClaim (ConRon.Arena.targetOutsideInst fe (decI I) (decI us) ds) a e := by
  intro e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  rw [toiE.arm1] at he
  cases h1 : callE p n "env_find" [I, vis] m with
  | error e1 =>
    rw [h1, toiE.k_env_find.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  | ok q1 =>
  obtain ⟨r2, m2⟩ := q1
  obtain ⟨s2, hs2, -, h2⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_specW p P.ix P.rowGet P.find n ⟨m, Locals.init []⟩ I vis) (callW_of_callE h1)
  dsimp only at h2
  obtain ⟨hm2, hfind, hdec⟩ := envFindW_found h2 hS.1.env hI
  rw [h1, ← hs2, hm2] at he
  rw [ConRon.Arena.targetOutsideInst]
  by_cases hf0 : r2.headD 0 = 0
  · rw [toiE.k_env_find.abort1 p n us dso dsl r2 m hf0] at he
    cases he
    have hfn : fe.find? (decI I) = none := by rw [hfind, decFound, ite_eq_left hf0]
    simp only [hfn]
    exact ErrClaim.fail _ _ (by decide)
  obtain ⟨ci, hci⟩ := hdec hf0
  have hfci : fe.find? (decI I) = some ci := by rw [hfind, decFound, ite_eq_right hf0, hci]
  obtain ⟨kk, hkk, hcase⟩ := decCI_ind_cases hci
  have hkr := erec_nat (w := r2.tail.headD 0) (c := 0) (by simpa using hkk) (by decide)
  rw [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at hkr
  by_cases hk3 : rdW (m.arr64 EREC) (r2.tail.headD 0) ≠ 3
  · rw [toiE.k_env_find.abort2 p n us dso dsl r2 m hf0 hk3] at he
    cases he
    have hkind : kk ≠ 3 := by
      intro hk3'
      apply hk3
      rw [hkr.1, hk3']; rfl
    obtain ⟨-, hno⟩ := hcase.resolve_left (fun ⟨hh, _⟩ => hkind hh)
    rw [hfci]
    cases ci with
    | indInfo cv caps => exact absurd rfl (hno cv caps)
    | _ => exact ErrClaim.fail _ _ (by decide)
  rw [toiE.k_env_find.arm1 p n us dso dsl r2 m hf0 (by simpa using hk3)] at he
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
  rw [e1, e2] at he
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (hslice?_bound _ _ _ _ hsl h0)
  cases h3 : callE p n "er_to_iw" [w1, w2] m with
  | error e3 =>
    rw [h3, toiE.k_er_to_iw.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, toiE.k_er_to_iw.arm1] at he
  obtain ⟨s3, hs3, -, h3m⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erToIw_specW p P.alloc P.copy P.eti n ⟨m, Locals.init []⟩ w1 w2) (callW_of_callE h3)
  dsimp only at h3m
  obtain ⟨-, hr3t, hdec3, hS3, hg3, -⟩ := L.Arena.erToIwW_stage h3m hS hsrc
  rw [← hs3] at he
  rw [hr3t] at he
  have hdecL : decHL s3.mem (r3.headD 0).toNat w2.toNat = some cv.levelParams := by rw [hdec3]; exact hsl
  have hcv3 : decCV (erA s3.mem) ((r2.tail.headD 0).toNat + 1) = some cv :=
    ArrExt.decCV (IWGrow.erecExt hg3) hcvP
  obtain ⟨wt, hwt, hwtH, hwtE⟩ := decCV_typeW hcv3
  have hqE3 := (Array.getElem?_eq_some_iff.mp hwt).1
  have hE364 := hS3.2.2.2.2.1
  have et : rdW (s3.mem.arr64 EREC) (r2.tail.headD 0 + 4) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hqE3 ⊢; omega) hwt
  rw [et] at he
  cases h4 : callE p n "inst_lp_fast" [CWF, r3.headD 0, w2, us, wt] s3.mem with
  | error e4 =>
    rw [h4, toiE.k_inst_lp_fast.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, toiE.k_inst_lp_fast.arm1] at he
  obtain ⟨x4, a4, hrun4, ⟨hS4, hg4, hx4⟩, -, hA4⟩ := (IlpRd.realC hIlpf hC) n CWF (r3.headD 0) w2 us wt
    cv.levelParams s3.mem m4 a r4 hu hwtH ⟨rfl, erToIwW_iwFr h3m⟩ hS3 hdecL (callW_of_callE h4)
  rw [CWF_eq, ← hwtE] at hrun4
  have hg34 := (hg3.trans hg4)
  refine ErrClaim.bind_right hrun4 ?_
  cases h5 : callE p n "inst_pis_with" [dso, dsl, r4.headD 0] m4 with
  | error e5 =>
    rw [h5, toiE.k_inst_pis_with.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  obtain ⟨s5, hs5, -, h5m⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (instPisWith_spec p P.v P.ipw P.hi1 n ⟨m4, Locals.init []⟩ dso dsl (r4.headD 0)) (callW_of_callE h5)
  subst hs5
  dsimp only at h5m
  obtain ⟨hx4H, rfl⟩ := hx4
  obtain ⟨x5, a5, hrun5, hS5, hg5, hx5⟩ := instW_okB h5m hS4 hx4H
    (DecB.grow (OMono.decHL _ _) hg34 hds) hb
  refine ErrClaim.bind_right hrun5 ?_
  by_cases hok : r5.headD 0 = 0
  · rw [h5, toiE.k_inst_pis_with.abort1 p n r5 s5.mem hok] at he
    cases he
    cases x5 with
    | none => exact ErrClaim.fail _ _ (by decide)
    | some ty => simp only [decOE] at hx5; exact absurd (hx5.1.symm.trans hok) (by decide)
  rw [h5, toiE.k_inst_pis_with.arm1 p n r5 s5.mem hok] at he
  cases x5 with
  | none => simp only [decOE] at hx5; exact absurd hx5 hok
  | some ty =>
  obtain ⟨-, hty⟩ := hx5
  have hg5' := hg34.trans hg5
  cases h6 : callE p n "pi_binders" [CWF, r5.tail.headD 0] s5.mem with
  | error e6 =>
    rw [h6, toiE.k_pi_binders.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h6)
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [h6, toiE.k_pi_binders.arm1] at he
  obtain ⟨s6, hs6, -, h6m⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (piBinders_spec' p P.alloc P.icopy P.v P.sc P.pb n ⟨s5.mem, Locals.init []⟩ CWF (r5.tail.headD 0))
    (callW_of_callE h6)
  subst hs6
  dsimp only at h6m
  obtain ⟨bs, e, hrun6, hdec6, hb6, he6, hS6, hg6, -⟩ := piBW_cwf h6m hS5 hty.1
  rw [hty.2] at hrun6
  refine ErrClaim.bind_right hrun6 ?_
  cases h7 : callE p n "e_view" [r6.tail.tail.headD 0] s6.mem with
  | error e7 =>
    rw [h7, toiE.k_e_view.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h7)
  | ok q7 =>
  obtain ⟨r7, m7⟩ := q7
  by_cases h2 : r7.headD 0 = 2
  · rw [h7, toiE.k_e_view.arm1 p _ r7 m7 h2] at he
    cases he
  rw [h7, toiE.k_e_view.abort1 p _ r7 m7 h2] at he
  cases he
  obtain ⟨s7, hs7, hs7e, hne7, hr7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (eView_spec p P.v n ⟨s6.mem, Locals.init []⟩ (r6.tail.tail.headD 0)) (callW_of_callE h7)
  dsimp only at hr7 hne7
  obtain ⟨v, hv, hvr⟩ := eViewW_ok s6.mem a5 hS6.1.arena.1 _ (by rw [← hr7]; exact hne7)
  rw [getD_two] at he6
  rw [he6] at hv
  have h2' : (eViewW s6.mem (r6.tail.tail.headD 0)).headD 0 ≠ 2 := by rw [← hr7]; exact h2
  refine ErrClaim.bind_right (view_run _ _ _ hv) ?_
  cases v with
  | sort u =>
    exfalso
    obtain ⟨hh, -, -⟩ := hvr
    exact h2' hh
  | _ => exact ErrClaim.fail _ _ (by decide)

include P hIlpf hnv in
/-- **`target_outside_inst`'s error claim** (every fuel). -/
theorem targetOutsideInst_claim (N : Nat) (s₀ : St) (a₀ : AState) (I us dso dsl : Word) (ds : List EIdx)
    (hC : StageC dn vis fe env s₀.mem a₀) (hI : H I) (hu : H us)
    (hds : DecB (fun m => decHL m dso.toNat dsl.toNat) s₀.mem ds) (hb : dso.toNat + dsl.toNat < 2 ^ 64) :
    CoreSpecE p N "target_outside_inst" [vis, I, us, dso, dsl]
      (ConRon.Arena.targetOutsideInst fe (decI I) (decI us) ds) s₀ a₀ := by
  cases N with
  | zero => exact CoreSpecE.zero _ _ _ _ _ _
  | succ n =>
    refine CoreSpecE.of_runs fun e hc => ?_
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact toiE_claim P hIlpf hnv n hC hI hu hds hb e
      (triple_of_callE_err (toiE_spec p P.toi (n + 1) s₀ vis I us dso dsl) hc (Err.code_ne_of_cls hk0))

end sims

end L.Ind
