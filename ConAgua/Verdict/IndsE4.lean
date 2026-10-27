import ConAgua.Verdict.IndsE3
import ConAgua.Verdict.IndsE2
import ConAgua.Arena.IndT.Install2
import ConAgua.Arena.Checker
/-!
# `check_block_agree_one`'s error refinement (lane `verdicts-b`, helper `ia2-inds`)

`agW_okC`'s proof on the error model `cbaoE`: the unopened member telescope and a length mismatch
are the twin's rejects, `check_block_doms_at` by `cbdaE_claim`, a `false` universe comparison the
twin's reject; `open_pis_at_fvars_f`, `fvar_type_ds`, `lvl_eq_fueled` claim nothing.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)


namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hnv hcE in
/-- **`check_block_agree_one`'s error claim** (`checkBlockAgreeOne_refinesC`'s shape). -/
theorem cbaoE_claim : CheckBlockAgreeOneE p := by
  intro hq dn vis fe env henv hOpf hLC hd hl hp had s₀ a nP fvs0O fvs0L s0 cvTa s cv fvs0 hC hA hty hfvs0
    hfot hs hs0 tyP xs0 sP s0P htyP hwx hxs0 hsc0 hsP hs0P F hF e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (cbaoE_spec p hp F ⟨s₀.mem, Locals.init []⟩ vis nP fvs0O fvs0L s0 cvTa s) he
    (Err.code_ne_of_cls hk0)
  simp only at he
  generalize s₀.mem = m at *
  cases F with
  | zero => rw [cbaoE.eq_1] at he; cases he; exact absurd Err.cls_outOfFuel hk0
  | succ n =>
  have hStage := hC.stage
  have hz : UInt64.toNat 0 = 0 := rfl
  have hty' : cv.type = decI (rdW (m.arr64 EREC) (cvTa + 3)) := hty.2.symm
  rw [cbaoE.arm1] at he
  cases h1 : callE p n "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (cvTa + 3), 0] m with
  | error e1 =>
    rw [h1, cbaoE.k_open_pis_at_fvars_f.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  | ok q1 =>
  obtain ⟨ra, m1⟩ := q1
  rw [h1] at he
  obtain ⟨x1, a1, hrun1, hSt1, hg1, hdec1, hA1⟩ :=
    opfF_okRA hty.1 (callW_opfF hOpf (callW_of_callE h1)) hStage hA
  have hdty : denoteE a.store (decI (rdW (m.arr64 EREC) (cvTa + 3))) = some tyP := by
    rw [hty.2]; exact htyP
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state hdty hrun1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hSt1 hA1 p1
  rw [hz] at hrun1
  by_cases h0 : ra.headD 0 = 0
  · rw [cbaoE.k_open_pis_at_fvars_f.abort1 p n vis nP fvs0O fvs0L s0 s ra m1 h0] at he; cases he
    cases x1 with
    | some fb => exact absurd hdec1.1 (by rw [h0]; decide)
    | none =>
    intro _
    refine ⟨.invalid "parameters of all inductive datatypes must match", ?_, rfl⟩
    simp only [agreeBodyAM, unwrapOr, hty', StateT.run_bind, hrun1]
    rfl
  cases x1 with
  | none => exact absurd hdec1 h0
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨xs1, b1, hq1, hxs1, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  rw [hz] at hq1
  obtain ⟨-, hrl1, -⟩ := hdec1
  simp only [decRL, show (1:Nat) + 1 = 2 from rfl, agGetD1, agGetD2] at hrl1
  obtain ⟨hfv1, hfvb1⟩ := hrl1
  have hlen1 := decHL_length m1 hfv1
  have hlen0 := decHL_length m hfvs0
  by_cases hL : ra.tail.tail.headD 0 = fvs0L
  case neg =>
    rw [cbaoE.k_open_pis_at_fvars_f.abort2 p n vis nP fvs0O fvs0L s0 s ra m1 h0 hL] at he; cases he
    have hne : fvs.length ≠ fvs0.length := by
      intro hc; apply hL; apply UInt64.toNat_inj.mp; omega
    intro _
    refine ⟨.invalid "parameters of all inductive datatypes must match", ?_, rfl⟩
    simp [agreeBodyAM, unwrapOr, hty', StateT.run_bind, hrun1, hne] <;> rfl
  rw [cbaoE.k_open_pis_at_fvars_f.arm1 p n vis nP fvs0O fvs0L s0 s ra m1 h0 hL] at he
  rw [hL] at hlen1
  have heq : fvs.length = fvs0.length := by omega
  cases h2 : callE p n "fvar_type_ds" [fvs0O, fvs0L] m1 with
  | error e2 =>
    rw [h2, cbaoE.k_fvar_type_ds.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨rd, m2⟩ := q2
  rw [h2, cbaoE.k_fvar_type_ds.arm1] at he
  have hrb : ftdsF m1 [fvs0O, fvs0L] = some (rd, m2) := by
    obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩) (ftdsF_spec p had n _ _)
      (callW_of_callE h2)
    rw [← hs']; exact hW
  have hbound1 : fvs0O.toNat + fvs0L.toNat ≤ iwTop m1 := by have := hg1.1; omega
  obtain ⟨x2, a2, hrun2, hSt2, hg2, hdec2⟩ :=
    ftdsF_ok dn vis fe fvs0O fvs0L fvs0 m1 m2 a1 rd hrb
      ⟨hSt1, by rw [decHL_grow hg1 (by omega)]; exact hfvs0, fun _ => hbound1⟩
  obtain ⟨p2, hdoms⟩ := ConRon.Bridge.Inductives.fvarTypeDs_run fvs0 xs0 hC1.check.state
    (ConRon.Bridge.denoteEList_ext p1.ext _ _ hxs0) hrun2
  have hA2 := ftdsF_afr hrb hA1
  have hC2 : StageC dn vis fe env m2 a2 := hC1.of_pstep hSt2 hA2 p2
  simp only [decRL, show (0:Nat) + 1 = 1 from rfl, agGetD0, agGetD1] at hdec2
  obtain ⟨hdm2, hdb2⟩ := hdec2
  have hlt1 := UInt64.toNat_lt (ra.tail.headD 0)
  have hlt2 := UInt64.toNat_lt (ra.tail.tail.headD 0)
  have hlt3 := UInt64.toNat_lt (rd.headD 0)
  have hlt4 := UInt64.toNat_lt (rd.tail.headD 0)
  have hltt : iwTop m2 < 2 ^ 64 := UInt64.toNat_lt _
  have hltt1 : iwTop m1 < 2 ^ 64 := UInt64.toNat_lt _
  have hc : ∀ (i : Nat) (x : ConLeche.Expr), xs1[i]? = some x →
      ConLeche.Expr.WScoped (0 + i) x.fvarTypeD :=
    ConRon.Bridge.Inductives.openers_typeD_WScoped hq1 hwx
  have ht : ∀ (i : Nat) (y : ConLeche.Expr), (xs0.map ConLeche.Expr.fvarTypeD)[i]? = some y →
      ConLeche.Expr.WScoped (0 + i) y := fun i y hy => by
    rw [List.getElem?_map] at hy
    obtain ⟨z, hz', rfl⟩ := Option.map_eq_some_iff.mp hy
    exact hsc0 i z hz'
  have hxs1' := ConRon.Bridge.denoteEList_ext p2.ext _ _ hxs1
  have hfv2 : decHL m2 (ra.tail.headD 0).toNat (ra.tail.tail.headD 0).toNat = some fvs := by
    rw [decHL_grow hg2 hfvb1]; exact hfv1
  cases h3 : callE p n "check_block_doms_at" [vis, 0, ra.tail.headD 0, ra.tail.tail.headD 0, rd.headD 0,
      rd.tail.headD 0, nP] m2 with
  | error e3 =>
    rw [h3, cbaoE.k_check_block_doms_at.none] at he; cases he
    have hW3 := triple_of_callE_err (cbdaE_spec p hd n ⟨m2, Locals.init []⟩ vis 0 (ra.tail.headD 0)
      (ra.tail.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) nP) h3 (Err.code_ne_of_cls hk0)
    simp only at hW3
    have hcl := cbdaE_claim hq henv hnv hcE had.ftd n (by omega) m2 a2 0 (ra.tail.headD 0)
      (ra.tail.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) nP fvs x2 xs1 (xs0.map ConLeche.Expr.fvarTypeD)
      hC2 hA2 hfv2 hdm2 (by omega) (by omega) (by have := hg2.1; omega) (by omega)
      (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact hlt2)
      hxs1' hdoms (fun i _ x y hx hy => ⟨hc i x hx, ht i y hy⟩) e hW3
    rw [hz] at hcl
    refine ErrClaim.of_twin hcl fun ce hce => ?_
    simp [agreeBodyAM, unwrapOr, hty', StateT.run_bind, hrun1, heq, hrun2, hce] <;> rfl
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, cbaoE.k_check_block_doms_at.arm1] at he
  have hw : domsW (realCall p) n m2 vis 0 (ra.tail.headD 0) (ra.tail.tail.headD 0) (rd.headD 0)
      (rd.tail.headD 0) nP = some (r3, m3) := by
    obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (domsW_spec p hd had.ftd (realCall p) (realCall_spec p) n _ _ _ _ _ _ _ _) (callW_of_callE h3)
    rw [← hs']; exact hW
  obtain ⟨hjf, hjd⟩ := domsW_le hw
  obtain ⟨u3, a3, hrun3, hC3, hg3, hA3⟩ := domsW_simC hq henv n (by omega) m2 a2 0 (ra.tail.headD 0)
    (ra.tail.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) nP fvs x2 xs1 (xs0.map ConLeche.Expr.fvarTypeD)
    hC2 hA2 hfv2 hdm2 (by omega) (by omega)
    (by have := hg2.1; omega) (by omega) (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact hlt2)
    hjf hjd hxs1' hdoms (fun i _ x y hx hy => ⟨hc i x hx, ht i y hy⟩) _ hw
  dsimp only at hC3 hg3 hA3
  rw [hz] at hrun3
  obtain ⟨c3, -⟩ := ConRon.Bridge.Inductives.checkBlockDomsAt_specF fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv 0 fvs x2 xs1 (xs0.map ConLeche.Expr.fvarTypeD) hc ht
    nP.toNat a2 a3 u3 hC2.check ⟨hxs1', hdoms⟩ hrun3
  cases h4 : callE p n "lvl_eq_fueled" [s, s0] m3 with
  | error e4 =>
    rw [h4, cbaoE.k_lvl_eq_fueled.none] at he; cases he
    have hx03 := p1.ext.trans (p2.ext.trans c3.ext)
    obtain ⟨lu, hlu⟩ : ∃ l, denoteL a3.store.ls (decI s) = some l := ⟨_, ConRon.Bridge.denoteL_ext hsP hx03⟩
    obtain ⟨lv, hlv⟩ : ∃ l, denoteL a3.store.ls (decI s0) = some l := ⟨_, ConRon.Bridge.denoteL_ext hs0P hx03⟩
    have hcl := lvlEqFueled_errT hq hLC hl (fun n args m e h => callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) n args m h)
      (fun c : Bool => if c = true then (pure () : AM Unit) else
        ConRon.Arena.fail (.invalid "mutually inductive types must live in the same universe"))
      hC3.stageT hs hs0 lu lv hlu hlv h4
    refine ErrClaim.of_twin hcl fun ce hce => ?_
    simp only [StateT.run_bind] at hce
    simp [agreeBodyAM, unwrapOr, hty', StateT.run_bind, hrun1, heq, hrun2, hrun3]
    exact hce
  | ok q4 =>
  obtain ⟨re, m4⟩ := q4
  have hl4 : lveC (realCall p) n m3 s s0 = some (re, m4) := by
    obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (lvlEqFueled_specC p hl (realCall p) (realCall_spec p) n _ _ _) (callW_of_callE h4)
    rw [← hs']; exact hW
  have hx03 := p1.ext.trans (p2.ext.trans c3.ext)
  obtain ⟨b, a4, hrun4, hC4, hg4, hA4, -, hbre⟩ := lveC_okC hq.closed hLC hl4 hC3 hA3 hs hs0
    (ConRon.Bridge.denoteL_ext hsP hx03) (ConRon.Bridge.denoteL_ext hs0P hx03)
  by_cases hre : re.headD 0 = 0
  · rw [h4, cbaoE.k_lvl_eq_fueled.abort1 p re m4 hre] at he; cases he
    have hb : b = false := by
      cases b
      · rfl
      · rw [hbre] at hre; exact absurd hre (by decide)
    subst hb
    intro _
    refine ⟨.invalid "mutually inductive types must live in the same universe", ?_, rfl⟩
    simp [agreeBodyAM, unwrapOr, hty', StateT.run_bind, hrun1, heq, hrun2, hrun3, hrun4, liftFueled] <;> rfl
  · rw [h4, cbaoE.k_lvl_eq_fueled.arm1 p re m4 hre] at he; cases he

end sims

end L.Ind
