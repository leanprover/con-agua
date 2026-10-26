import ConAgua.Verdict.IndsE5

/-!
# `check_block_tele`'s, `check_block_teles`' error refinements (lane `verdicts-b`, helper `ia2-inds`)

`ibtW_simC`'s proof on the error model `cbtE`: the constant check by `CheckConstantValE`, the
telescope by `CheckSumTeleE`; past them only class-`0` errors (`strip_pis`, `intern_sort`, the
capacity and the defensive aborts). `check_block_teles` by induction on the fuel (`ibtsW_simC`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
  (eCcv : CheckConstantValE p) (eSum : CheckSumTeleE p)

include hnv eCcv eSum in
/-- **`check_block_tele`'s error claim** (`checkBlockTele_refinesC`'s shape). -/
theorem cbtE_claim : CheckBlockTeleE p := by
  intro hq dn vis fe env henv hV hApd hCrk hP hp s₀ a nP ms msh hC hms hA msP hmsP hfe F hF e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (cbtE_spec p hp F ⟨s₀.mem, Locals.init []⟩ vis nP ms) he
    (Err.code_ne_of_cls hk0)
  simp only at he
  generalize s₀.mem = m at *
  cases F with
  | zero => rw [cbtE.eq_1] at he; cases he; exact absurd Err.cls_outOfFuel hk0
  | succ n =>
  have hn : n ≤ 2 ^ 62 := by omega
  have hS := hC.stage
  obtain ⟨hcvP, -, -⟩ := ConRon.Bridge.Inductives.dMember_inv hmsP
  obtain ⟨hmsB, hcx⟩ := hms
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨⟨c, hc, hcv⟩, hni, -⟩ := decMS_some (m := truncM m) hmsB
  obtain ⟨hw0, hcb, hmsl⟩ := partsIwRd hc rfl
  obtain ⟨hw1, hnb, -⟩ := partsIwRd hni (w := ms + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨-, hcN⟩ := rec2IwN_trunc hc
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  have hcvx : CVExt m (UInt64.ofNat c : Word).toNat := by rw [hc']; exact hcx c hcN
  have hcvm : decCVp m (UInt64.ofNat c : Word).toNat = some msh.cvT := by
    rw [hc']; exact DecB.get (OMono.decCVp _) hcv

  by_cases hov : nP + UInt64.ofNat msh.nIdx < nP
  · rw [cbtE.abort1 p n m vis nP ms (by rw [hw1]; exact hov)] at he; cases he; exact absurd rfl hk0
  rw [cbtE.arm1 p n m vis nP ms (by rw [hw1]; exact hov), hw0, hw1] at he
  have hk : (nP + UInt64.ofNat msh.nIdx).toNat = nP.toNat + msh.nIdx := by
    rw [partsAddNoOv hov, UInt64.toNat_ofNat_of_lt' hnb]
  unfold ConRon.Arena.checkBlockTele
  cases h1 : callE p n "check_constant_val" [vis, UInt64.ofNat c] m with
  | error e1 =>
    rw [h1, cbtE.k_check_constant_val.none] at he; cases he
    exact ErrClaim.bind_left (eCcv hV hq hApd hCrk ⟨m, Locals.init []⟩ a dn fe vis _ msh.cvT hC.stageT
      (rec2DecCV_erecP hcvm hcvx) (rec3CVExt_lt hS hcvx) (denoteCV_lps hcvP) hA.crMemo.crOK n hn e h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, cbtE.k_check_constant_val.arm1] at he
  obtain ⟨s1, hs1, -, hok1, hT1, hg1, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (checkConstantVal_refinesT p hV hq hApd hCrk n hn _ a dn fe vis _ msh.cvT hC.stageT
      (rec2DecCV_erecP hcvm hcvx) (rec3CVExt_lt hS hcvx) (denoteCV_lps hcvP) hA.crMemo.crOK) (callW_of_callE h1)
  subst hs1
  have hr1 := partsRunOfOk hok1
  have hA1 : AbsOK s1.mem := checkConstantVal_absOK p hV hq hApd hCrk hn hC.stageT
    (rec2DecCV_erecP hcvm hcvx) (rec3CVExt_lt hS hcvx) (denoteCV_lps hcvP) hA.crMemo.crOK (callW_of_callE h1) hA
  generalize AM.st (checkConstantVal V fe msh.cvT) a = a1 at hr1 hT1
  generalize AM.res (checkConstantVal V fe msh.cvT) a = u1 at hr1
  obtain ⟨c1, F₁, hF₁⟩ := ConRon.Bridge.checkConstantVal_bridge rfl (ConRon.Bridge.CoreSpec.of_core rfl)
    hC.check henv hcvP hr1
  have hC1 : StageC dn vis fe env s1.mem a1 := StageC.of_T hT1 c1.ok
  have hcA := ConRon.Bridge.denoteCV_ext hcvP c1.ext
  have hw1' : ConLeche.Expr.WScoped 0 msP.cvT.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF₁).1
  have hcvm1 : decCVp s1.mem (UInt64.ofNat c : Word).toNat = some msh.cvT := by
    rw [hc']; exact DecB.stab (OMono.decCVp _) hcv s1.mem hg1
  have hx1 := CVExt_grow hg1 hcvx
  refine ErrClaim.bind_right hr1 ?_
  cases h2 : callE p n "check_sum_tele" [vis, UInt64.ofNat c, nP + UInt64.ofNat msh.nIdx, UInt64.ofNat c] s1.mem with
  | error e2 =>
    rw [h2, cbtE.k_check_sum_tele.none] at he; cases he
    have hcl := eSum hq henv hV hApd hCrk hP.alloc hP.copy hP.cons hP.view hP.fvarFind hP.fvarPush
      hP.internFVar hP.wt hP.sortFind hP.sortPush hP.internSort hP.derB hP.forallFind hP.forallPush
      hP.internForall hP.mkForall hP.closeTele hP.erAlloc hP.cvNew hP.slow hP.i1 hP.ab hP.tele hP.strip
      ⟨s1.mem, Locals.init []⟩ a1 _ _ _ msh.cvT msh.cvT hC1 hcvm1 hx1.1 hx1.2 hcvm1 hx1.1 hx1.2 hA1 hcA hcA hw1'
      (ConRon.Bridge.denoteFEnv_mono c1.ext hfe) n hn e h2
    rw [hk] at hcl
    exact ErrClaim.bind_left hcl
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, cbtE.k_check_sum_tele.arm1] at he
  -- past the telescope: class-`0` errors only
  cases h3 : callE p n "strip_pis" [nP + UInt64.ofNat msh.nIdx, rdW (m2.arr64 EREC) (r2.headD 0 + 3)] m2 with
  | error e3 =>
    rw [h3, cbtE.k_strip_pis.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3] at he
  by_cases h30 : r3.headD 0 = 0
  · rw [cbtE.k_strip_pis.abort1 p n _ _ r3 m3 h30] at he; cases he; exact absurd rfl hk0
  rw [cbtE.k_strip_pis.arm1 p n _ _ r3 m3 h30] at he
  cases h4 : callE p n "intern_sort" [r2.tail.headD 0] m3 with
  | error e4 =>
    rw [h4, cbtE.k_intern_sort.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4] at he
  by_cases h40 : r3.tail.tail.tail.headD 0 = r4.headD 0
  · rw [cbtE.k_intern_sort.arm1 p _ _ _ r4 m4 h40] at he; cases he
  · rw [cbtE.k_intern_sort.abort1 p _ _ _ r4 m4 h40] at he; cases he; exact absurd rfl hk0

variable (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p) (hApd : ApdF p) (hCrk : CrKeep p)

include hnv eCcv eSum hq henv hV hApd hCrk in
/-- **`check_block_teles`' error claim** (the model at L fuel `n`, `ibtsW_simC`'s hypotheses). -/
theorem cbtsE_claim (hP : InstProg p) (nP : Word) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (o l : Word) (mss : List MemberShape)
      (mssP : List ConLeche.MemberShape),
    StageC dn vis fe env m a → MemsOK m o l mss → AbsOK m →
    mss.mapM (ConRon.Bridge.Inductives.dMember a.store) = some mssP →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    ∀ e, cbtsE p n m vis nP o l = .error e →
      ErrClaim (ConRon.Arena.checkBlockTeles V fe nP.toNat mss) a e := by
  induction n with
  | zero =>
    intro m a o l mss mssP _ _ _ _ _ e he
    rw [cbtsE.eq_1] at he; cases he; exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a o l mss mssP hC hms hA hmssP hfe e he
  have hS := hC.stage
  by_cases hl : l = 0
  · rw [cbtsE.arm1 p n m vis nP o l hl] at he; cases he
  obtain ⟨q, x, rest, rfl, hw, hqb, hmok, hrest⟩ := hms.cons hl
  obtain ⟨xP, restP, rfl, hxP, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmssP
  rw [cbtsE.arm2 p n m vis nP o l hl, hw] at he
  unfold ConRon.Arena.checkBlockTeles
  cases h1 : callE p n "check_block_tele" [vis, nP, UInt64.ofNat q] m with
  | error e1 =>
    rw [h1, cbtsE.k_check_block_tele.none] at he; cases he
    exact ErrClaim.bind_left (cbtE_claim hnv eCcv eSum hq henv hV hApd hCrk hP.toCstProg hP.bTele
      ⟨m, Locals.init []⟩ a nP _ x hC hmok hA hxP hfe n (by omega) e h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, cbtsE.k_check_block_tele.arm1] at he
  cases n with
  | zero => have := callW_of_callE h1; rw [callW_zero] at this; cases this
  | succ k =>
  obtain ⟨s1, hs1, -, hok1, hT1, hA1, c1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (checkBlockTele_refinesC hq henv hV hApd hCrk hP.toCstProg hP.bTele k (by omega)
      ⟨m, Locals.init []⟩ a nP _ x hC hmok hA hxP hfe) (callW_of_callE h1)
  subst hs1
  have hr1 := partsRunOfOk hok1
  generalize AM.st (ConRon.Arena.checkBlockTele V fe nP.toNat x) a = a1 at hr1 hT1 c1
  generalize AM.res (ConRon.Arena.checkBlockTele V fe nP.toNat x) a = x1 at hr1 hT1
  refine ErrClaim.bind_right hr1 ?_
  cases h2 : callE p (k + 1) "rec2" [r1.headD 0, r1.tail.headD 0] s1.mem with
  | error e2 =>
    rw [h2, cbtsE.k_rec2.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, cbtsE.k_rec2.arm1] at he
  obtain ⟨hS2, hg2, hd2, hlt2⟩ := installRec2Tele hP (k + 1) hT1.toR (callW_of_callE h2)
  have hA2 : AbsOK m2 := by
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
      (rec2_specW p hP.alloc (k + 1) hP.rec2 _ _ _) (callW_of_callE h2)
    exact recW_afr hW hA1
  have hC2 : StageC dn vis fe env m2 a1 := hT1.1.of_pstep hS2 hA2 (PStep.refl hT1.1.check.state)
  cases h3 : cbtsE p (k + 1) m2 vis nP (o + 1) (l - 1) with
  | error e3 =>
    rw [h3, cbtsE.k_check_block_teles.none] at he; cases he
    exact ErrClaim.bind_left (ih (by omega) m2 a1 (o + 1) (l - 1) rest restP hC2 (hrest.grow hg2) hA2
      (ConRon.Bridge.Inductives.dMember_ext.list c1.ext _ _ hrestP)
      (ConRon.Bridge.denoteFEnv_mono c1.ext hfe) e h3)
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, cbtsE.k_check_block_teles.arm1] at he
  cases h4 : callE p (k + 1) "sl_cons" [r2.headD 0, r3.headD 0, r3.tail.headD 0] m3 with
  | error e4 =>
    rw [h4, cbtsE.k_sl_cons.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4, cbtsE.k_sl_cons.arm1] at he; cases he

end sims

end L.Ind
