import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndPosSpec.NestGroupCtors
import ConAgua.Arena.IndPosSpec.UnW
import ConAgua.Arena.IlpRd
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# NuW

`nestRootCanon_spec`, `nrcW_ok`, `nestUniformOk_spec`, `nuW_ok`, `cvLps_exec1`, `rootCanon_small` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem nestRootCanon_spec (p : Prog) (hl : PccLook p) (hc : p.lookup "er_copy" = some erCopy)
    (he : p.lookup "er_to_iw" = some erToIw) (hcv : p.lookup "cv_lps" = some cvLps)
    (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St) (ctx cv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 3)) "nest_root_canon" [ctx, cv]
    ⦃fun r s' => LocEq s' s₀ ∧ nrcW cR k s₀.mem ctx cv = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hl.hp', callFn, nestRootCanonL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      cvLps_spec p hl.ha hc he hcv (k + 2), hcR (k + 2) "inst_lp_fast",
      nestCanonCrest_spec p hl.ha hl.hl hl.hk hl.hng hl.hnp hl.hip hl.hf hl.hput hl.hgo hl.hnode hl.hcl
        hl.hra hl.hp k] <;>
    finish (gen := 20) [nrcW, rdW_eq]

theorem nrcW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem)
    (a : AState) (ctx cv : Word) (c : NestCtx) (cvv : IConstantVal) (r : List Word) (cR : CallM)
    (hI : IlpRd cR dn vis fe (IlpBase m a))
    (h : nrcW cR k m ctx cv = some (r, m')) (hS : StageR dn vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat)
    (hcv : decCV (erecP m) cv.toNat = some cvv)
    (hnn : c.nP + c.names.length < 2 ^ 64) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.nestRootCanon c cvv).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decOE m' r x ∧ PosMR m' ∧ (PccAfr → AFr m m') := by
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨-, -, hty⟩ := decCV_some hcv
  obtain ⟨wt, hwt, hwtH, hwtd⟩ := hd?_some hty
  have hcv3 : cv.toNat + 3 < erTop m := by
    have := (Array.getElem?_eq_some_iff.mp hwt).1; have := erecP_size_le m; omega
  have hEb : erTop m ≤ (m.arr64 EREC).size := hS.2.2.1
  have hEs : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  unfold nrcW at h
  rcases hlp : cvLpsW (k + 2) m cv with _ | ⟨r1, m1⟩ <;> rw [hlp] at h; · simp [nrcK1] at h
  rw [nrcK1_some] at h
  obtain ⟨hS1, hg1, hE1, hdec1, -⟩ := pos2_cvLpsW_stage hlp hS ((erecP_ext m).decCV hcv) (by omega)
  -- the instantiation's arguments
  obtain ⟨cin1, cin1'⟩ := CtxIn.grow hin hg1
  rw [hc] at cin1
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨-, -, -, -, -, hlvH, hlvd, -⟩ := ctx_fields cin1 cin1' htop1
  have e3 : (cv + 3).toNat = cv.toNat + 3 := word_add_toNat (by simp; omega)
  have hrd3 : rdW (m1.arr64 EREC) (cv + 3) = wt := by
    rw [hE1]; simp [rdW, e3, erecP_get hwt]
  rw [hrd3] at h
  rcases hst : cR (k + 2) "inst_lp_fast" [CWF, r1.headD 0, r1.tail.headD 0, rdW (m1.arr64 IW) (ctx + 10), wt] m1 with _ | ⟨r2, m2⟩ <;> rw [hst] at h; · simp [nrcK2] at h
  rw [nrcK2_some] at h
  obtain ⟨t, a2, hrun2, ⟨hS2, hg2, htH, htd⟩, ⟨A2, C2, hA2s, hC2s, hfr2⟩, hAF2⟩ :=
    hI (k + 2) CWF _ _ _ _ cvv.levelParams _ _ a r2 hlvH hwtH ⟨rfl, erToIwW_iwFr hlp⟩ hS1 hdec1 hst
  have hP2 : PosMR m2 := (hP.fr (posmemo_cvLpsW_mfr hlp)).fr (MFr.of_frame hfr2 hA2s hC2s)
  obtain ⟨mp2, hM2⟩ := hP2.rp
  rw [CWF_eq, hlvd, ← hwtd] at hrun2
  have hg12 := hg1.trans hg2
  obtain ⟨cin2, cin2'⟩ := CtxIn.grow hin hg12
  rw [hc] at cin2
  have hsl2 := hsl.grow hin hg12
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hn2, -, -, -, hnP2, hlvH2, hlvd2, -⟩ := ctx_fields cin2 cin2' htop2
  have hne2 := ctx_names_end cin2 cin2' hsl2 htop2
  rcases hpc : pccW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 10))
      (rdW (m2.arr64 IW) (ctx + 4)) (r2.headD 0) with _ | ⟨r3, m3⟩; · rw [hpc] at h; simp [nrcK3] at h
  rw [hpc, nrcK3_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨x, a3, hrun3, hS3, hg3, hx, hM3⟩ := pccW_ok k dn fe vis m2 m3 a2 _ _ _ _ _ c.names r3 hpc hS2 htH hlvH2 hn2
    (by omega) hne2 (by rw [hnP2]; omega) mp2 hM2
  refine ⟨x, a3, ?_, hS3, hg12.trans hg3, ?_, hP2.setRp (pccW_mfr hpc) hM3,
    fun hpcc => (AFr.iw (erToIwW_iwFr hlp)).trans (hAF2.trans (hpcc _ _ _ _ _ _ _ _ _ hpc))⟩
  · simp only [ConRon.Arena.nestRootCanon, StateT.run_bind, hrun2, except_ok_bind]
    rw [hnP2, hlvd2, htd] at hrun3
    exact hrun3
  · cases x with
    | none => exact hx
    | some e => exact hx

theorem nestUniformOk_spec (p : Prog) (hl : NuLook p) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St)
    (ctx cv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 4)) "nest_uniform_ok" [ctx, cv]
    ⦃fun r s' => LocEq s' s₀ ∧ nuW cR k s₀.mem ctx cv = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hl.hp, callFn, nestUniformOkL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      nestCtxHiAt_specE p hl.hh (k + 3), piDomsOcc_spec p hl.no hl.hpd (k + 3),
      nestRootCanon_spec p hl.pcc hl.hc hl.he hl.hcv cR hcR k, nestOcc_spec' p hl.no (k + 3)] <;>
    finish (gen := 20) [nuW, rdW_eq]

theorem nuW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem)
    (a : AState) (ctx cv : Word) (c : NestCtx) (cvv : IConstantVal) (r : List Word) (cR : CallM)
    (hI : ∀ (m1 : Mem) (a1 : AState) (r1 : List Word) (b : Bool),
      pdoW (k + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 EREC) (cv + 3)) = some (r1, m1) →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a = .ok (b, a1) →
      StageR dn vis fe m1 a1 → IlpRd cR dn vis fe (IlpBase m1 a1))
    (h : nuW cR k m ctx cv = some (r, m')) (hS : StageR dn vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat)
    (hcv : decCV (erecP m) cv.toNat = some cvv) (hhi : c.hiAt 0 < 2 ^ 64) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.nestUniformOk c cvv).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ r = [if x then 1 else 0] ∧ PosMR m' ∧ (NuAfr → AFr m m') := by
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hn, hnb, -, -, hnP, -⟩ := ctx_fields hc hin htop
  have hhiW := nhiW_toNat (nf := 0) hc hin htop (by simpa using hhi)
  obtain ⟨-, -, hty⟩ := decCV_some hcv
  obtain ⟨wt, hwt, hwtH, hwtd⟩ := hd?_some hty
  have hcv3 : cv.toNat + 3 < erTop m := by
    have := (Array.getElem?_eq_some_iff.mp hwt).1; have := erecP_size_le m; omega
  have e3 : (cv + 3).toNat = cv.toNat + 3 := word_add_toNat (by have := hS.2.2.1; have := hS.2.2.2.2.1; simp; omega)
  have hrd3 : rdW (m.arr64 EREC) (cv + 3) = wt := by simp [rdW, e3, erecP_get hwt]
  unfold nuW at h
  rw [hrd3] at h
  obtain ⟨mp0, hM0⟩ := hP.no
  rcases hpd : pdoW (k + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
      (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) wt with _ | ⟨r1, m1⟩; · rw [hpd] at h; simp [nuK1] at h
  rw [hpd] at h
  obtain ⟨b1, a1, mp1, hrun1, hS1, hg1, hr1, hM1, hf1⟩ := pdoW_ok dn fe vis _ _ _ _ c.names (k + 3) m m1 a _ wt r1 mp0
    hpd hS hwtH hn hnb hM0
  have hP1 := hP.setNo hf1 ⟨mp1, hM1⟩
  rw [hnP, hhiW, decE_eq, ← hwtd, show (0 : Word).toNat = 0 from rfl] at hrun1
  have hI1 := hI m1 a1 r1 b1 (by rw [hrd3]; exact hpd) hrun1 hS1
  have hpre : ConRon.Arena.nestUniformOk c cvv = (do
      let o1 ← ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type
      if o1 = true then pure false
      else match ← ConRon.Arena.nestRootCanon c cvv with
        | none => pure false
        | some crest => do
          let occ ← ConRon.Arena.nestOcc c.names 0 0 crest
          pure !occ) := rfl
  rw [hpre]
  cases b1 with
  | true =>
    rw [nuK1_occ (h := by rw [hr1]; decide)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨false, a1, ?_, hS1, hg1, rfl, hP1, fun hN => hN.pdo _ _ _ _ _ _ _ _ _ _ hpd⟩
    simp only [StateT.run_bind, hrun1, except_ok_bind]; rfl
  | false =>
  rw [nuK1_ok (h := by rw [hr1]; decide)] at h
  have hcv1 : decCV (erecP m1) cv.toNat = some cvv := (GrowX.of_grow (q := 0) (n := 0) hg1).erecP.decCV hcv
  rcases hrc : nrcW cR k m1 ctx cv with _ | ⟨r2, m2⟩ <;> rw [hrc] at h; · simp [nuK2] at h
  obtain ⟨cin1, cin1'⟩ := CtxIn.grow hin hg1
  rw [hc] at cin1
  have hnn : c.nP + c.names.length < 2 ^ 64 := by simpa [NestCtx.hiAt] using hhi
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2, hP2, hA2⟩ := nrcW_ok k dn fe vis m1 m2 a1 ctx cv c cvv r2 cR hI1 hrc hS1 cin1 cin1'
    (hsl.grow hin hg1) hcv1 hnn hP1
  cases x2 with
  | none =>
    rw [nuK2_none (h := hx2)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨false, a2, ?_, hS2, hg1.trans hg2, rfl, hP2,
      fun hN => (hN.pdo _ _ _ _ _ _ _ _ _ _ hpd).trans (hA2 hN.pcc)⟩
    simp only [StateT.run_bind, hrun1, except_ok_bind]
    simp only [Bool.false_eq_true, ite_false, StateT.run_bind, hrun2, except_ok_bind]; rfl
  | some crest =>
  obtain ⟨hx0, hcH, hcd⟩ := hx2
  rw [nuK2_some (h := by rw [hx0]; decide)] at h
  have hg12 := hg1.trans hg2
  obtain ⟨cin2, cin2'⟩ := CtxIn.grow hin hg12
  rw [hc] at cin2
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hn2, -⟩ := ctx_fields cin2 cin2' htop2
  have hne2 := ctx_names_end cin2 cin2' (hsl.grow hin hg12) htop2
  obtain ⟨mp2, hM2⟩ := hP2.no
  rcases hno : noConstWf (k + 3) m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) 0 0 (r2.tail.headD 0) with _ | ⟨o, m3⟩ <;> rw [hno] at h; · simp [nuK3] at h
  rw [nuK3_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨b, hrun3, hb, hM3, hS3, hg3, hf3⟩ := noConstWf_ok (k + 3) dn fe vis m2 m3 a2 _ _ 0 0 _ o c.names mp2 hno hS2
    hcH hn2 (by omega) hM2
  refine ⟨!b, a2, ?_, hS3, hg12.trans hg3, ?_, hP2.setNo hf3 ⟨∅, hM3⟩,
    fun hN => ((hN.pdo _ _ _ _ _ _ _ _ _ _ hpd).trans (hA2 hN.pcc)).trans (hN.noc _ _ _ _ _ _ _ _ _ hno)⟩
  · simp only [StateT.run_bind, hrun1, except_ok_bind]
    simp only [Bool.false_eq_true, ite_false, StateT.run_bind, hrun2, except_ok_bind]
    rw [decE_eq, hcd, show (0 : Word).toNat = 0 from rfl] at hrun3
    simp only [hrun3, except_ok_bind]; rfl
  · subst hb; by_cases ho : o = 0 <;> simp [ho]

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order
namespace L.Ind
open L.Arena

theorem cvLps_exec1 (p : Prog) (hcv : p.lookup "cv_lps" = some cvLps) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p 1) "cv_lps" [q] ⦃fun _ _ => False; ⊤⦄ := by
  rw [invoke_eq _ hcv]; simp only [callFn, cvLps]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, invoke_exec0 p] <;> finish

theorem rootCanon_small (p : Prog) (hcv : p.lookup "cv_lps" = some cvLps)
    (hp : p.lookup "nest_root_canon" = some nestRootCanonL) (k : Nat) (hk : k ≤ 2) (s₀ : St) (ctx cv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_root_canon" [ctx, cv] ⦃fun _ _ => False; ⊤⦄ := by
  match k, hk with
  | 0, _ => exact invoke_exec0 p _ _ s₀
  | 1, _ =>
    rw [invoke_eq _ hp]; simp only [callFn, nestRootCanonL]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, invoke_exec0 p] <;> finish
  | 2, _ =>
    rw [invoke_eq _ hp]; simp only [callFn, nestRootCanonL]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, cvLps_exec1 p hcv] <;> finish
  | _ + 3, h => exact absurd h (by omega)

theorem nestUniformOk_spec' (p : Prog) (hl : NuLook p) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St)
    (ctx cv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_uniform_ok" [ctx, cv]
    ⦃fun r s' => LocEq s' s₀ ∧ nuWf cR k s₀.mem ctx cv = some (r, s'.mem); ⊤⦄ := by
  match k with
  | 0 => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | 1 =>
    rw [invoke_eq _ hl.hp]; simp only [callFn, nestUniformOkL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, invoke_exec0 p] <;> finish
  | 2 =>
    rw [invoke_eq _ hl.hp]; simp only [callFn, nestUniformOkL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestCtxHiAt_specE p hl.hh 1, piDomsOcc_spec p hl.no hl.hpd 1,
        rootCanon_small p hl.hcv hl.pcc.hp' 1 (by omega)] <;> finish [pdoW, pdoK1, noConstWf]
  | 3 =>
    rw [invoke_eq _ hl.hp]; simp only [callFn, nestUniformOkL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestCtxHiAt_specE p hl.hh 2, piDomsOcc_spec p hl.no hl.hpd 2,
        rootCanon_small p hl.hcv hl.pcc.hp' 2 (by omega)] <;>
      finish [pdoW, pdoK1, noConstWf, noConstW, noClrK, noGoW]
  | k + 4 => exact nestUniformOk_spec p hl cR hcR k s₀ ctx cv

theorem nestUniformCs_spec (p : Prog) (hl : NuLook p) (hp : p.lookup "nest_uniform_cs" = some nestUniformCsL)
    (cR : CallM) (hcR : CallSpec p cR) (k : Nat) : ∀ (s₀ : St) (ctx o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_uniform_cs" [ctx, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ucW cR k s₀.mem ctx o l = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ ctx o l
    rw [invoke_eq _ hp]; simp only [callFn, nestUniformCsL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ ctx o l
    simp only [invoke_eq _ hp, callFn, nestUniformCsL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestUniformOk_spec' p hl cR hcR k, ih] <;>
      finish (gen := 20) [rdW_eq]

/-! ### `nest_uniform`: the relational side -/

theorem nuWf_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem)
    (a : AState) (ctx cv : Word) (c : NestCtx) (cvv : IConstantVal) (r : List Word) (cR : CallM)
    (hI : ∀ (k' : Nat) (m1 : Mem) (a1 : AState) (r1 : List Word) (b : Bool),
      pdoW (k' + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 EREC) (cv + 3)) = some (r1, m1) →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a = .ok (b, a1) →
      StageR dn vis fe m1 a1 → IlpRd cR dn vis fe (IlpBase m1 a1))
    (h : nuWf cR k m ctx cv = some (r, m')) (hS : StageR dn vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat)
    (hcv : decCV (erecP m) cv.toNat = some cvv) (hhi : c.hiAt 0 < 2 ^ 64) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.nestUniformOk c cvv).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ r = [if x then 1 else 0] ∧ PosMR m' ∧ (NuAfr → AFr m m') := by
  match k, h with
  | k + 4, h => exact nuW_ok k dn fe vis m m' a ctx cv c cvv r cR (hI k) h hS hc hin hsl hcv hhi hP

theorem ucW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx : Word) (c : NestCtx)
    (hhi : c.hiAt 0 < 2 ^ 64) (cR : CallM) (J : Mem → AState → Prop) (Pcv : IConstantVal → Prop)
    (hJI : ∀ (m : Mem) (a : AState) (cv : Word) (cvv : IConstantVal), J m a → Pcv cvv →
      decCV (erecP m) cv.toNat = some cvv → ∀ (k' : Nat) (m1 : Mem) (a1 : AState) (r1 : List Word) (b : Bool),
      pdoW (k' + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 EREC) (cv + 3)) = some (r1, m1) →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a = .ok (b, a1) →
      StageR dn vis fe m1 a1 → IlpRd cR dn vis fe (IlpBase m1 a1))
    (hJnu : ∀ (k : Nat) (m m' : Mem) (a a' : AState) (cv : Word) (cvv : IConstantVal) (r : List Word) (x : Bool),
      J m a → Pcv cvv → nuWf cR k m ctx cv = some (r, m') →
      (ConRon.Arena.nestUniformOk c cvv).run a = .ok (x, a') → StageR dn vis fe m' a' → (NuAfr → AFr m m') →
      J m' a') (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (o l : Word) (cs : List (IConstantVal × Nat)) (r : List Word),
    ucW cR k m ctx o l = some (r, m') → StageR dn vis fe m a → J m a → (∀ x ∈ cs, Pcv x.1) →
    UCtx dn vis fe m ctx c →
    l.toNat = cs.length → o.toNat + cs.length ≤ iwTop m → CsAt m o.toNat cs (· < iwTop m) → PosMR m →
    ∃ b a', (cs.allM (fun x => ConRon.Arena.nestUniformOk c x.1)).run a = .ok (b, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) ∧ PosMR m' ∧ J m' a' := by
  induction k with
  | zero => intro m m' a o l cs r h; simp [ucW] at h
  | succ k ih =>
    intro m m' a o l cs r h hS hJ hPc hU hl hob hcs hP
    by_cases hl0 : l = 0
    · rw [ucW_nil (h := hl0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl0
      have : cs = [] := List.eq_nil_of_length_eq_zero (by rw [← hl]; rfl)
      subst this
      exact ⟨true, a, rfl, hS, IWGrow.refl _, rfl, hP, hJ⟩
    rw [ucW_cons (h := hl0)] at h
    have hlz : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨x, cs', rfl⟩ := List.exists_cons_of_ne_nil (show cs ≠ [] from fun e => by rw [e] at hl; exact hlz hl)
    obtain ⟨w, hw, h0, h1, qn, hqn, hcvv, -⟩ := hcs 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hw hcvv
    have hrw : rdW (m.arr64 IW) o = w := by simp [rdW, hw]
    obtain ⟨q, hq, rfl⟩ : ∃ q : Word, (m.arr64 IW)[w.toNat]? = some q ∧ q.toNat = qn := by
      simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at hqn; exact hqn
    have hrq : rdW (m.arr64 IW) w = q := by simp [rdW, hq]
    rw [hrw, hrq] at h
    rcases hnu : nuWf cR k m ctx q with _ | ⟨r1, m1⟩ <;> rw [hnu] at h; · simp [ucK] at h
    have hPx := hPc x List.mem_cons_self
    obtain ⟨b1, a1, hrun1, hS1, hg1, hr1, hP1, hA1⟩ := nuWf_ok k dn fe vis m m1 a ctx q c x.1 r1 cR
      (hJI m a q x.1 hJ hPx hcvv) hnu hS hU.dec hU.inn hU.sl hcvv hhi hP
    have hJ1 := hJnu k m m1 a a1 q x.1 r1 b1 hJ hPx hnu hrun1 hS1 hA1
    rw [List.allM_cons]
    cases b1 with
    | false =>
      subst hr1
      rw [ucK_no (h := rfl)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨false, a1, ?_, hS1, hg1, rfl, hP1, hJ1⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind]; rfl
    | true =>
      subst hr1
      rw [ucK_yes (h := by simp)] at h
      have ho1 : (o + 1).toNat = o.toNat + 1 := word_add_toNat (by
        have := hS.2.1; have := hS.2.2.2.1; simp at hob; simp; omega)
      have hl1 : (l - 1).toNat = l.toNat - 1 :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
      have hcs1 := hcs.tail
      have hb1 : o.toNat + 1 + cs'.length ≤ iwTop m := by simp at hob; omega
      obtain ⟨b, a', hrun, hS', hg', hr, hP', hJ'⟩ := ih m1 m' a1 (o + 1) (l - 1) cs' r h hS1 hJ1
        (fun y hy => hPc y (List.mem_cons_of_mem _ hy)) (hU.grow hg1)
        (by rw [hl1, hl]; simp) (by rw [ho1]; have := hg1.1; omega)
        (by rw [ho1]; exact hcs1.grow hb1 hg1) hP1
      refine ⟨b, a', ?_, hS', hg1.trans hg', hr, hP', hJ'⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, ite_true]
      exact hrun

end L.Ind

end

end
