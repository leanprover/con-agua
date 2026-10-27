import ConAgua.Arena.IndRealSctC
import ConAgua.Arena.Verdict
import ConAgua.Checker.NoVerdictFns

/-!
# Error refinement of `check_struct_proj_table` (lane `verdicts-b`, helper `ib`)

Mirrors `tblW_okR` (`IndRealSctC`): every callee is `closedNV`, the aborts are class `0`; the only
other error is `fail R_PROJECTION_TABLE_TAKEN`, after the bodies, the scoping, the `unless`
and the stored-structure test all passed, so the twin reaches its `invalid "projection table
taken"`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tblE_spec (p : Prog) (hf : p.lookup "check_struct_proj_table" = some checkStructProjTableL)
  fns [hf ↦ tblE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}
  (hP : TblProg p) (hp : ApdF p) (hnv : closedNV p _root_.L.Checker.nvFns = true)

include hP hp hnv in
/-- **`check_struct_proj_table`'s model error claim** (`tblW_okR`'s hypotheses). -/
theorem tblE_claim (n : Nat) {m : Mem} {a : AState} {T C lo ll nP nF rs go gl cvCaw : Word}
    {lps : List NIdx} {guards : List LIdx} {cvCa : IConstantVal}
    (hS : StageR dn vis fe m a) (hT : H T) (_hC : H C)
    (_hrs : H rs) (hnP : nP.toNat + 1 < 2 ^ 64)
    (hlps : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (_hgs : decHL m go.toNat gl.toNat = some guards) (_hgb : go.toNat + gl.toNat ≤ iwTop m)
    (hcv : DecB (fun m => decCVp m cvCaw.toNat) m cvCa) (hA : AbsOK m)
    (hok : ConRon.Bridge.StateOK a) (hks : ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks)
    {TP : ConLeche.Name} (hTP : denoteN a.store.ns (decI T) = some TP)
    {ctyP : ConLeche.Expr} (hcty : denoteE a.store cvCa.type = some ctyP) :
    ∀ e, tblE p (n + 2) m T C lo ll nP nF rs go gl cvCaw vis = .error e →
      ErrClaim (checkStructProjTable (decI T) (decI C) lps nP.toNat nF.toNat (decI rs) guards cvCa fe) a e := by
  intro e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  rw [tblE.arm1] at he
  obtain ⟨w, hw, hwl, hwd⟩ := sumTypeWord (DecB.get (OMono.decCVp _) hcv) hS.2.2.2.2.1
  rw [hw] at he
  rw [← hwd] at hcty
  unfold checkStructProjTable
  rw [← hwd]
  -- `struct_proj_bodies`
  cases h1 : callE p (n + 1) "struct_proj_bodies" [T, nP, nF, w] m with
  | error e1 =>
    rw [h1, tblE.k_struct_proj_bodies.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨rb, m1⟩ := q1
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (spbW_spec p hP.ha hP.hc hP.hsc hP.hv hP.hd hP.hpf hP.hpp hP.hib hP.hjf hP.hjp hP.hji hP.hmp hP.hap
      hP.hpg hP.hgo hP.hps hP.hpj hP.hspb hP.hi1 hP.hipal (n + 1) _ T nP nF w) (callW_of_callE h1)
  obtain ⟨x, a1, h1', hS1, hg1, hdec1, hA1⟩ := spbW_ok dn vis fe (n + 1) m s1.mem a T nP nF w rb hW1 hS hwl
    (by omega) nF.toNat_lt hA
  obtain ⟨ps, -⟩ := ConRon.Bridge.Inductives.structProjBodies_spec (decI T) TP nP.toNat nF.toNat
    (decI w) ctyP a a1 x hok ⟨hTP, hcty⟩ h1'
  subst hs1
  refine ErrClaim.bind_right h1' ?_
  by_cases h10 : rb.headD 0 = 0
  · rw [h1, tblE.k_struct_proj_bodies.abort1 p (n + 1) T C lo ll nP nF rs go gl vis rb _ h10] at he
    cases he
    exact absurd (by decide) hk0
  rw [h1, tblE.k_struct_proj_bodies.arm1 p (n + 1) T C lo ll nP nF rs go gl vis rb _ h10] at he
  cases x with
  | none => exact absurd hdec1 h10
  | some bodies =>
  obtain ⟨-, hbd, hbb⟩ := hdec1
  simp only [unwrapOr, pure_bind]
  have hlps1 : decHL s1.mem lo.toNat ll.toNat = some lps := by rw [decHL_grow hg1 hlb]; exact hlps
  have hlb1 : lo.toNat + ll.toNat ≤ iwTop s1.mem := by have := hg1.1; omega
  -- the scoping
  cases h2 : callE p (n + 1) "check_struct_proj_table_scoped"
      [vis, nP, lo, ll, rb.tail.headD 0, rb.tail.tail.headD 0] s1.mem with
  | error e2 =>
    rw [h2, tblE.k_check_struct_proj_table_scoped.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨rs', m2⟩ := q2
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (sctW_spec p hP.hbb hP.hhf hP.hcr hP.hsct (realCall p) (realCall_spec p) (n + 1) _ vis nP lo ll
      (rb.tail.headD 0) (rb.tail.tail.headD 0)) (callW_of_callE h2)
  obtain ⟨b, a2, hrun2, hS2, hg2, hsok, hsl, hA2, he2⟩ := sctW_okR hp nP lo ll lps hnP (n + 1) s1.mem a1 _ _
    bodies.toList hS1 ps.ok (names_ext ps.ext hks) hlps1 hlb1 hbd hbb hA1 rs' s2.mem hW2
  subst hs2
  rw [h2] at he
  by_cases hlen0 : rb.tail.tail.headD 0 ≠ nF
  · rw [tblE.k_check_struct_proj_table_scoped.abort1 p (n + 1) T C lo ll nP nF rs go gl vis _ _ rs' _ hlen0] at he
    cases he
    exact absurd (by decide) hk0
  have hlen : rb.tail.tail.headD 0 = nF := Decidable.of_not_not hlen0
  by_cases h10' : rs'.headD 0 ≠ 1
  · rw [tblE.k_check_struct_proj_table_scoped.abort2 p (n + 1) T C lo ll nP nF rs go gl vis _ _ rs' _ hlen h10'] at he
    cases he
    exact absurd (by decide) hk0
  have h1' : rs'.headD 0 = 1 := Decidable.of_not_not h10'
  rw [tblE.k_check_struct_proj_table_scoped.arm1 p (n + 1) T C lo ll nP nF rs go gl vis _ _ rs' _ hlen h1'] at he
  refine ErrClaim.bind_right hrun2 ?_
  have hsz : bodies.size = nF.toNat := by
    rw [← Array.length_toList, decHL_length s1.mem hbd, hlen]
  have hsok' : b = true := (sumB01 hsok hsl).1.mp h1'
  subst hsok'
  simp only [hsz, and_self, ite_true]
  -- `env_find`
  cases h3 : callE p (n + 1) "env_find" [T, vis] s2.mem with
  | error e3 =>
    rw [h3, tblE.k_env_find.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨rf, m3⟩ := q3
  obtain ⟨s3, hs3, -, hf⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (envFind_specW p hP.hix hP.hrg hP.hfind (n + 1) _ T vis) (callW_of_callE h3)
  rw [h3] at he
  by_cases hf0 : rf.headD 0 = 0
  · rw [tblE.k_env_find.abort1 p (n + 1) T C lo ll nP nF rs go gl vis _ _ rf m3 hf0] at he
    cases he
    exact absurd (by decide) hk0
  rw [tblE.k_env_find.arm1 p (n + 1) T C lo ll nP nF rs go gl vis _ _ rf m3 hf0] at he
  obtain ⟨hm32, hfind0, ci0, hci0⟩ := envFindW_hit hf hS2.1.env hT hf0
  have hm3 : m3 = s2.mem := hs3.symm.trans hm32
  subst hm3
  have hhit : (fe.find? (decI T)).isSome := by rw [hfind0, hci0]; rfl
  simp only [hhit, ite_true]
  -- `find_table`
  cases h4 : callE p (n + 1) "find_table" [vis, T] s2.mem with
  | error e4 =>
    rw [h4, tblE.k_find_table.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨rt, m4⟩ := q4
  obtain ⟨s4, hs4, hm42, -, hfind, hsome4⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (findTable_refines p hP.hix hP.hrg hP.htix hP.htrg hP.hftab (n + 1) _ vis T hS2.1.env hT)
    (callW_of_callE h4)
  rw [h4] at he
  by_cases ht0 : rt.headD 0 ≠ 0
  · rw [tblE.k_find_table.abort1 p (n + 1) T C lo ll nP nF rs go gl vis _ _ rt m4 ht0] at he
    cases he
    have hsome : ¬ (fe.findTable? (decI T)).isNone = true := by
      rw [hfind]
      have := hsome4 ht0
      simp only [Option.isNone_iff_eq_none]
      intro hn
      rw [hn] at this
      exact absurd this (by simp)
    exact ErrClaim.ite_neg hsome (ErrClaim.bind_left (ErrClaim.fail _ _ (by decide)))
  have ht0' : rt.headD 0 = 0 := Decidable.of_not_not ht0
  rw [tblE.k_find_table.arm1 p (n + 1) T C lo ll nP nF rs go gl vis _ _ rt m4 ht0'] at he
  -- the three copies, the record and the push: all `closedNV`
  unfold tblE.k_er_from_iw at he
  split at he
  · cases he
    have hc := ‹callE _ _ _ _ _ = Except.error _›
    exact absurd (callE_nv hnv (by decide +kernel) _ _ _ hc) hk0
  unfold tblE.k_er_from_iw_2 at he
  split at he
  · cases he
    have hc := ‹callE _ _ _ _ _ = Except.error _›
    exact absurd (callE_nv hnv (by decide +kernel) _ _ _ hc) hk0
  unfold tblE.k_er_from_iw_3 at he
  split at he
  · cases he
    have hc := ‹callE _ _ _ _ _ = Except.error _›
    exact absurd (callE_nv hnv (by decide +kernel) _ _ _ hc) hk0
  unfold tblE.k_erec_alloc at he
  split at he
  · cases he
    have hc := ‹callE _ _ _ _ _ = Except.error _›
    exact absurd (callE_nv hnv (by decide +kernel) _ _ _ hc) hk0
  unfold tblE.k_env_push_table at he
  split at he
  · cases he
    have hc := ‹callE _ _ _ _ _ = Except.error _›
    exact absurd (callE_nv hnv (by decide +kernel) _ _ _ hc) hk0
  cases he

include hP hp hnv in
/-- **`check_struct_proj_table`'s error claim** (every fuel). -/
theorem checkStructProjTable_claim (N : Nat) (s₀ : St) (a : AState)
    {T C lo ll nP nF rs go gl cvCaw : Word} {lps : List NIdx} {guards : List LIdx} {cvCa : IConstantVal}
    (hS : StageR dn vis fe s₀.mem a) (hT : H T) (hC : H C)
    (hrs : H rs) (hnP : nP.toNat + 1 < 2 ^ 64)
    (hlps : decHL s₀.mem lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop s₀.mem)
    (hgs : decHL s₀.mem go.toNat gl.toNat = some guards) (hgb : go.toNat + gl.toNat ≤ iwTop s₀.mem)
    (hcv : DecB (fun m => decCVp m cvCaw.toNat) s₀.mem cvCa) (hA : AbsOK s₀.mem)
    (hok : ConRon.Bridge.StateOK a) (hks : ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks)
    {TP : ConLeche.Name} (hTP : denoteN a.store.ns (decI T) = some TP)
    {ctyP : ConLeche.Expr} (hcty : denoteE a.store cvCa.type = some ctyP) :
    CoreSpecE p N "check_struct_proj_table" [T, C, lo, ll, nP, nF, rs, go, gl, cvCaw, vis]
      (checkStructProjTable (decI T) (decI C) lps nP.toNat nF.toNat (decI rs) guards cvCa fe) s₀ a := by
  refine CoreSpecE.of_runs fun e hc => ?_
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have he := triple_of_callE_err (tblE_spec p hP.htbl N s₀ T C lo ll nP nF rs go gl cvCaw vis) hc
    (Err.code_ne_of_cls hk0)
  obtain _ | _ | n := N
  · simp only [tblE] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  · rw [tblE.arm1] at he
    obtain ⟨e', he', h0⟩ := callE_zero p "struct_proj_bodies" [T, nP, nF, rdW (s₀.mem.arr64 EREC) (cvCaw + 3)] s₀.mem
    rw [he', tblE.k_struct_proj_bodies.none] at he
    cases he
    exact ErrClaim.of_cls0 h0
  · exact tblE_claim hP hp hnv n hS hT hC hrs hnP hlps hlb hgs hgb hcv hA hok hks hTP hcty e he

end sims

end L.Ind
