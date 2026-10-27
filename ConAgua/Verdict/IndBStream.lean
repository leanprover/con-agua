import ConAgua.Verdict.IndBSum2
import ConAgua.Arena.DeclArmT
import ConAgua.Arena.RecGenSpec.ClassMinorSlot
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree

/-!
# Error refinement of `class_stream_recs` (lane `verdicts-b`, helper `ib`)

Each recursor constant is checked by the program's own `check_constant_val`; its error claim is a
hypothesis (`CcvE`, discharged by the declaration family).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dRec dRec_ext dExt_denoteCV mapM_option_cons_inv dRec_inv)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model csrE_spec (p : Prog) (hf : p.lookup "class_stream_recs" = some classStreamRecsL)
  fns [hf ↦ csrE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {dn : NIdx → Option ConLeche.Name} {env : ConLeche.Env}
variable {p : Prog} (hq : KnotStageProg p) (henv : ConLeche.EnvWF env) (hV : ValProg p)
  (hApd : ApdF p) (hCrk : CrKeep p) (hnv : closedNV p _root_.L.Checker.nvFns = true) (hCcv : CcvE p)

include hq henv hV hApd hCrk hnv hCcv in
/-- **`class_stream_recs`' model error claim** (`csrW_okC`'s hypotheses). -/
theorem csrE_claim (fe : IFEnv) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (vis rcso rcsl : Word) (recs : List RecShape)
      (recsP : List ConLeche.RecShape),
    StageC dn vis fe env m a → AbsOK m →
    RecsOK m rcso.toNat rcsl.toNat (recs.map (·.cvR)) → recs.mapM (dRec a.store) = some recsP →
    ∀ e, csrE p n m vis rcso rcsl = .error e →
      ErrClaim (ConRon.Arena.classStreamRecs V fe recs) a e := by
  induction n with
  | zero =>
    intro m a vis rcso rcsl recs recsP hC hA hOK hrecsP e he
    rw [csrE.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a vis rcso rcsl recs recsP hC hA hOK hrecsP e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  by_cases hrl : rcsl = 0
  · rw [csrE.arm1 p n m vis rcso rcsl hrl] at he
    cases he
  rw [csrE.arm2 p n m vis rcso rcsl hrl] at he
  have hpos : 1 ≤ rcsl.toNat := by
    rcases Nat.eq_zero_or_pos rcsl.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hrl
    · omega
  obtain ⟨l1, hl1⟩ : ∃ l1, rcsl.toNat = l1 + 1 := ⟨rcsl.toNat - 1, by omega⟩
  have hlen := hOK.2.1
  obtain ⟨rc, rest, rfl⟩ : ∃ rc rest, recs = rc :: rest := by
    cases recs with
    | nil => simp at hlen; omega
    | cons rc rest => exact ⟨rc, rest, rfl⟩
  obtain ⟨rcP, restP, rfl, hrcP, hrestP⟩ := mapM_option_cons_inv hrecsP
  have hcvR := (dRec_inv hrcP).1
  rw [hl1] at hOK
  obtain ⟨⟨p0, q, hp0, hp1, hq', hcv, hext⟩, hOKt⟩ := RecsOK_cons (by simpa using hOK)
  have e0 : UInt64.ofNat rcso.toNat = rcso := UInt64.ofNat_toNat
  have hIW64 : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
  have hrd0 := iwN_rdW hp0 (by have := iwN_lt hp0; omega)
  rw [e0] at hrd0
  have hrdq := iwN_rdW hq' (by omega)
  have hqb : q < 2 ^ 64 := hrdq.2
  rw [hrd0.1, hrdq.1] at he
  have hqt : (UInt64.ofNat q).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  unfold ConRon.Arena.classStreamRecs
  cases h1 : callE p n "check_constant_val" [vis, UInt64.ofNat q] m with
  | error e1 =>
    rw [h1, csrE.k_check_constant_val.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    have hqb3 : (UInt64.ofNat q : Word).toNat + 3 < 2 ^ 64 := by
      rw [hqt]; exact rec3CVExt_lt hS hext
    exact CoreSpecE.of_callE (hCcv n (by omega) ⟨m, Locals.init []⟩ a (UInt64.ofNat q) rc.cvR hC.stageT
      (by rw [hqt]; exact rec2DecCV_erecP hcv hext) hqb3 (denoteCV_lps hcvR) hA.crMemo.crOK) h1
  | ok q1 =>
  obtain ⟨r0, m1⟩ := q1
  rw [h1, csrE.k_check_constant_val.arm1] at he
  have hqb3 : (UInt64.ofNat q : Word).toNat + 3 < 2 ^ 64 := by
    rw [hqt]; exact rec3CVExt_lt hS hext
  obtain ⟨s1, hs1, -, hok1, hT1, hg1, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (checkConstantVal_refinesT p hV hq hApd hCrk n (by omega) _ a dn fe vis (UInt64.ofNat q) rc.cvR
      hC.stageT (by rw [hqt]; exact rec2DecCV_erecP hcv hext) hqb3 (denoteCV_lps hcvR)
      hA.crMemo.crOK) (callW_of_callE h1)
  simp only at hs1 hT1 hg1
  subst hs1
  have hrun1 := AM.run_of_ok _ a hok1
  generalize ha1 : AM.st (ConRon.Arena.checkConstantVal V fe rc.cvR) a = a1 at hrun1 hT1
  have hA1 := checkConstantVal_absOK p hV hq hApd hCrk (by omega) hC.stageT
    (by rw [hqt]; exact rec2DecCV_erecP hcv hext) hqb3 (denoteCV_lps hcvR) hA.crMemo.crOK (callW_of_callE h1) hA
  obtain ⟨c1, -⟩ := ConRon.Bridge.checkConstantVal_bridge rfl (ConRon.Bridge.CoreSpec.of_core rfl)
    hC.check henv hcvR hrun1
  have hC1 : StageC dn vis fe env s1.mem a1 := StageC.of_T hT1 c1.ok
  refine ErrClaim.bind_right hrun1 ?_
  have hOK1 : RecsOK s1.mem (rcso + 1).toNat (rcsl - 1).toNat (rest.map (·.cvR)) := by
    have htopsz : iwTop m ≤ (m.arr64 IW).size := hS.2.1
    have hOKb := hOK.1
    have hro1 : (rcso + 1).toNat = rcso.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hrl1 : (rcsl - 1).toNat = l1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
    rw [hro1, hrl1]
    exact RecsOK_grow hg1 hOKt
  refine ErrClaim.bind_left ?_
  cases h2 : csrE p n s1.mem vis (rcso + 1) (rcsl - 1) with
  | error e2 =>
    rw [h2, csrE.k_class_stream_recs.none] at he
    cases he
    exact ih (by omega) s1.mem a1 vis (rcso + 1) (rcsl - 1) rest restP hC1 hA1 hOK1
      (dRec_ext.list c1.ext _ _ hrestP) _ h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, csrE.k_class_stream_recs.arm1] at he
  cases h3 : callE p n "sl_cons" [UInt64.ofNat q, r2.headD 0, r2.tail.headD 0] m2 with
  | error e3 =>
    rw [h3, csrE.k_sl_cons.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  rw [h3, csrE.k_sl_cons.arm1] at he
  cases he

include hq henv hV hApd hCrk hnv hCcv in
/-- **`class_stream_recs`' error claim** (the hypotheses of `classStreamRecs_refinesC`). -/
theorem classStreamRecs_claim (hp : p.lookup "class_stream_recs" = some classStreamRecsL) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (fe : IFEnv) (vis rcso rcsl : Word) (recs : List RecShape)
    (recsP : List ConLeche.RecShape) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hOK : RecsOK s₀.mem rcso.toNat rcsl.toNat (recs.map (·.cvR)))
    (hrecsP : recs.mapM (dRec a₀.store) = some recsP) :
    CoreSpecE p n "class_stream_recs" [vis, rcso, rcsl] (ConRon.Arena.classStreamRecs V fe recs) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (csrE_spec p hp n ⟨s₀.mem, Locals.init []⟩ vis rcso rcsl) hc'
    (Err.code_ne_of_cls hk0)
  exact csrE_claim hq henv hV hApd hCrk hnv hCcv fe n hn s₀.mem a₀ vis rcso rcsl recs recsP hC hA hOK hrecsP er hW

end sims

end L.Ind
