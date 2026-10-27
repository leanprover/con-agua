import ConAgua.Arena.IndT.Sum4
import ConAgua.Arena.IndSumSpec.CtorX
import ConAgua.Arena.IndSumSpec.SoaW
import ConAgua.Census.Attr

/-!
# `checkSumCtors` under `StageC` (lane `indstaget`)

`check_sum_ctors`' model at `realCall p`, from `StageC` and con-ron's preconditions of
`checkSumCtors_spec`, its twin side transcribed from that spec's proof: `checkSumCtor`
(`ctorW_okC`, its `CoreStep` moving the preconditions), the records and the conses (L only).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p) (hOpf : OpfF p) (hLC : LvlCacheProg p)
  (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p)

include hq henv hV hOpf hLC hLT hApd hCrk in
/-- **`check_sum_ctors` under `StageC`** (twin side: con-ron's `checkSumCtors_spec`'s proof). -/
theorem sctsW_okC
    (vis0 T lo ll nP nIdx rs isP lg cvTaw : Word) (lps : List NIdx) (cvTa : IConstantVal)
    (hT : H T) (hrs : H rs) {env₀ : ConLeche.Env} {TP : ConLeche.Name} {lpsP : List ConLeche.Name}
    {rsP : ConLeche.Level} {cvTaP : ConLeche.ConstantVal} (hws : ConLeche.Expr.WScoped 0 cvTaP.type)
    (k : Nat) (hk : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (cO cL : Word) (cs : List (IConstantVal × Nat))
      (csP : List (ConLeche.ConstantVal × Nat)),
    StageC dn vis fe env m a → decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    DecB (fun m => decCVp m cvTaw.toNat) m cvTa →
    DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) m cs → AbsOK m →
    denoteN a.store.ns (decI T) = some TP → Frontend.denoteNList a.store.ns lps = some lpsP →
    denoteL a.store.ls (decI rs) = some rsP → Frontend.denoteCV a.store cvTa = some cvTaP →
    ConRon.Bridge.Inductives.denoteCtors a.store cs = some csP →
    ConRon.Bridge.Inductives.IFEnvOKS env₀ (fe.restrictTo vis0.toNat) a.store →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    Sim (sctsW (realCall p) k m vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL)
      (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs)
        (isP != 0) (lg != 0) cvTa cs) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        DecB (fun m => decPL m (decCN m) (r.headD 0).toNat (r.tail.headD 0).toNat) m' x.1 ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧
        DecB (fun m => decPL m (sortsDec m) (r.tail.tail.headD 0).toNat
          (r.tail.tail.tail.headD 0).toNat) m' x.2 ∧
        (r.tail.tail.headD 0).toNat + (r.tail.tail.tail.headD 0).toNat ≤ iwTop m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
  induction k with
  | zero => intros; exact Sim.of_none
  | succ k ih =>
  intro m a cO cL cs csP hC hlps hlb hta hcs hA hTP hlpsP hrsP hcvTaP hcsP hok₀ hfe
  have hS := hC.stage
  have hcl := decPL_length (m := truncM m) hcs
  by_cases hl : cL = 0
  · rw [sctsW_nil (h := hl)]
    have : cs = [] := by subst hl; cases cs with | nil => rfl | cons _ _ => simp at hcl
    subst this
    simp only [checkSumCtors]
    exact Sim.ret ⟨hC, IWGrow.refl _, by simp [DecB, decPL], by simp, by simp [DecB, decPL], by simp, hA,
      ConRon.Bridge.CoreStep.refl hC.check⟩
  by_cases hov1 : nP + nIdx < nP
  · rw [sctsW_ov1 (h := hl) (h1 := hov1)]; exact Sim.of_none
  have hni : nP.toNat + nIdx.toNat < 2 ^ 64 := by rw [← sumAddNoOv hov1]; exact UInt64.toNat_lt _
  obtain ⟨L, hL⟩ : ∃ L, cL.toNat = L + 1 :=
    ⟨cL.toNat - 1, by have : cL.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hcs' : decPL (truncM m) (decCN (truncM m)) cO.toNat (L + 1) = some cs := by
    have := hcs; simp only [DecB, hL] at this; exact this
  cases cs with
  | nil => simp at hcl; omega
  | cons c cs =>
  obtain ⟨cv, nF⟩ := c
  simp only [ConRon.Bridge.Inductives.denoteCtors] at hcsP
  cases hcvP : Frontend.denoteCV a.store cv with
  | none => rw [hcvP] at hcsP; simp at hcsP
  | some cP =>
  cases hrestP : ConRon.Bridge.Inductives.denoteCtors a.store cs with
  | none => rw [hcvP, hrestP] at hcsP; simp at hcsP
  | some restP =>
  obtain ⟨pv, hpv, hc⟩ := decPL_head hcs'
  have htail := decPL_tail hcs'
  obtain ⟨⟨cqN, hcq, hcv⟩, hnF⟩ := decCN_some hc
  obtain ⟨w, hw, hwv, hcO⟩ := rdW_of_iwN_truncM hpv
  have hcq' : iwN (truncM m) w.toNat = some cqN := by rw [hwv]; exact hcq
  obtain ⟨w2, hw2, hw2v, hpvlt⟩ := rdW_of_iwN_truncM hcq'
  have hT0 := hS.lt64 (x := iwTop m) (Nat.le_refl _)
  have hw1 : (w + 1).toNat = pv + 1 := by rw [UInt64.toNat_add, hwv]; simp; omega
  have hnF' : iwN (truncM m) (w + 1).toNat = some nF := by rw [hw1]; exact hnF
  obtain ⟨w3, hw3, hw3v, -⟩ := rdW_of_iwN_truncM hnF'
  by_cases hov2 : nP + rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1) < nP
  · rw [sctsW_ov2 (h := hl) (h1 := hov1) (h2 := hov2)]; exact Sim.of_none
  rw [sctsW_cons (h := hl) (h1 := hov1) (h2 := hov2)]
  rw [hw, hw3] at hov2
  rw [hw, hw2, hw3]
  have hcvB : DecB (fun m => decCVp m w2.toNat) m cv := by
    show decCVp (truncM m) w2.toNat = some cv; rw [hw2v]; exact hcv
  have hnf : nP.toNat + w3.toNat < 2 ^ 64 := by rw [← sumAddNoOv hov2]; exact UInt64.toNat_lt _
  -- the head constructor
  obtain hk | ⟨j, rfl⟩ : k < 3 ∨ ∃ j, k = j + 3 := by
    rcases Nat.lt_or_ge k 3 with h | h
    · exact .inl h
    · exact .inr ⟨k - 3, by omega⟩
  · have : ctorX (realCall p) k m vis0 vis T lo ll nP nIdx rs isP lg w2 w3 cvTaw = none := by
      match k, hk with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
    rw [this]; exact Sim.of_none
  subst hw3v
  simp only [checkSumCtors]
  refine Sim.bindK (K := sctsK1 _ (j + 3) w3) rfl (fun _ _ => rfl)
    (ctorW_okC hq henv hV hOpf hLC hLT hApd hCrk j (by omega) m a vis0 T lo ll nP nIdx rs isP lg w2 w3 cvTaw lps cv cvTa hC hT hlps
      hlb hcvB hta hrs hni hnf hA hTP hlpsP hrsP hcvP hcvTaP hws hok₀ hfe) fun r x m1 a1 hQ => ?_
  obtain ⟨hC1, hg1, hr0, hx1, hsorts, hsb, hA1, c1⟩ := hQ
  have hS1 := hC1.stage
  obtain ⟨cvCa, sorts⟩ := x
  simp only at hx1 hsorts
  subst hx1
  rw [sctsK1_some]
  rcases hn : recW m1 2 [r.headD 0, w3] with _ | ⟨rn, m2⟩
  · exact Sim.of_none
  rw [sctsK2_some]
  obtain ⟨hS2, hg2, hn0, hn1⟩ := sumRec2 hn hS1
  have hA2 : AbsOK m2 := recW_afr hn hA1
  have hC2 : StageC dn vis fe env m2 a1 := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  rcases hh : recW m2 2 [r.tail.headD 0, r.tail.tail.headD 0] with _ | ⟨rh, m3⟩
  · exact Sim.of_none
  rw [sctsK3_some]
  obtain ⟨hS3, hg3, hh0, hh1⟩ := sumRec2 hh hS2
  have hA3 : AbsOK m3 := recW_afr hh hA2
  have hC3 : StageC dn vis fe env m3 a1 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  have x1 := c1.ext
  have hg03 := (hg1.trans hg2).trans hg3
  have hcO1 : (cO + 1).toNat = cO.toNat + 1 := sumToNat_succ (by omega)
  have hcL1 : (cL - 1).toNat = L := by rw [sumToNat_pred hl]; omega
  refine Sim.bindK (K := sctsK4 (j + 3) (rn.headD 0) (rh.headD 0)) rfl (fun _ _ => rfl)
    (ih (by omega) m3 a1 (cO + 1) (cL - 1) cs restP hC3 (by rw [decHL_grow hg03 hlb]; exact hlps)
      (by have := hg03.1; omega) (DecB.grow (OMono.decCVp _) hg03 hta)
      (by rw [hcO1, hcL1]; exact DecB.grow (OMono.decPL decCN_mono _ _) hg03 htail) hA3
      (ConRon.Bridge.denoteN_ext hTP x1) (ConRon.Bridge.denoteNListE_ext x1 _ _ hlpsP)
      (ConRon.Bridge.denoteL_ext hrsP x1) (ConRon.Bridge.denoteCV_ext hcvTaP x1)
      (ConRon.Bridge.Inductives.denoteCtors_ext x1 _ _ hrestP) (hok₀.mono x1)
      (ConRon.Bridge.denoteFEnv_mono x1 hfe))
    fun rr y m4 a4 hQ => ?_
  obtain ⟨hC4, hg4, hD1, hb1, hD2, hb2, hA4, c4⟩ := hQ
  have hS4 := hC4.stage
  obtain ⟨rest, srest⟩ := y
  simp only at hD1 hD2
  rw [sctsK4_some]
  obtain ⟨ps1, hps1t, hps1, hmap1⟩ := sumDecNL_of_decB hD1
  rcases hc1 : consW (j + 3) m4 (rn.headD 0) (rr.headD 0) (rr.tail.headD 0) with _ | ⟨r1, m5⟩
  · exact Sim.of_none
  rw [sctsK5_some]
  obtain ⟨hS5, hg5, hd5, ht5⟩ := consW_stageN hc1 hS4 hb1 hps1
  obtain ⟨ps2, hps2t, hps2, hmap2⟩ := sumDecNL_of_decB hD2
  have hb2' : (rr.tail.tail.headD 0).toNat + (rr.tail.tail.tail.headD 0).toNat ≤ iwTop m5 := by
    have := hg5.1; omega
  rcases hc2 : consW (j + 3) m5 (rh.headD 0) (rr.tail.tail.headD 0) (rr.tail.tail.tail.headD 0) with _ | ⟨r2, m6⟩
  · exact Sim.of_none
  rw [sctsK6_some]
  obtain ⟨hS6, hg6, hd6, ht6⟩ := consW_stageN hc2 hS5 hb2'
    ((OMono.decNL _ _).mono _ _ _ (IWGrow.truncExt hg5) hps2t)
  -- the head's records, decoded at the end
  have hy1 : DecB (fun m => decCN m (rn.headD 0).toNat) m5 (cvCa, w3.toNat) := by
    have h0 : DecB (fun m => decCN m (rn.headD 0).toNat) m2 (cvCa, w3.toNat) := by
      refine sumDecCN_of hn0 hn1 ?_
      rw [hr0]; exact DecB.grow (OMono.decCVp _) (hg1.trans hg2) hcvB
    exact DecB.grow (decCN_mono _) ((hg3.trans hg4).trans hg5) h0
  have hy2 : DecB (fun m => sortsDec m (rh.headD 0).toNat) m6 sorts := by
    have h0 : DecB (fun m => sortsDec m (rh.headD 0).toNat) m3 sorts :=
      sumSortsDec_of hh0 hh1 (by rw [decHL_grow (hg2.trans hg3) hsb]; exact hsorts)
        (by have := (hg2.trans hg3).1; omega)
    exact DecB.grow (sortsDec_mono _) ((hg4.trans hg5).trans hg6) h0
  have hg46 := hg5.trans hg6
  have hA6 := consW_afr hc2 (consW_afr hc1 hA4)
  refine Sim.ret ⟨hC4.of_pstep hS6 hA6 (PStep.refl hC4.check.state), (hg03.trans hg4).trans hg46, ?_, ?_,
    ?_, ?_, hA6, c1.trans c4⟩
  · simp only [List.headD_cons, List.tail_cons]
    exact DecB.grow (OMono.decPL decCN_mono _ _) hg6
      (sumDecB_cons decCN_mono hmap1 hd5 (by omega) hg5 hy1)
  · simp only [List.headD_cons, List.tail_cons]; have := hg6.1; omega
  · simp only [List.headD_cons, List.tail_cons]
    exact sumDecB_cons sortsDec_mono hmap2 hd6 (by omega) hg46 hy2
  · simp only [List.headD_cons, List.tail_cons]; omega

include hq henv hV hOpf hLC hLT hApd hCrk in
/-- **`check_sum_ctors` refines `checkSumCtors .verified`** under `StageC` (the inputs'
denotations as con-ron's `checkSumCtors_spec` asks), the pre-block environment the restriction of
`fe` to `vis0`: the new constructor list and the sorts lists as fresh pointer slices decoded below
the tops. -/
@[refines ConRon.Arena.checkSumCtors]
theorem checkSumCtors_refinesC (hP : SumProg p) (k : Nat) (hk : k ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (vis0 T lo ll nP nIdx rs isP lg cvTaw cO cL : Word) (lps : List NIdx) (cvTa : IConstantVal)
    (cs : List (IConstantVal × Nat)) (hC : StageC dn vis fe env s₀.mem a₀) (hT : H T) (hrs : H rs)
    (hlps : decHL s₀.mem lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop s₀.mem)
    (hta : DecB (fun m => decCVp m cvTaw.toNat) s₀.mem cvTa)
    (hcs : DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) s₀.mem cs) (hA : AbsOK s₀.mem)
    {env₀ : ConLeche.Env} {TP : ConLeche.Name} {lpsP : List ConLeche.Name} {rsP : ConLeche.Level}
    {cvTaP : ConLeche.ConstantVal} {csP : List (ConLeche.ConstantVal × Nat)}
    (hTP : denoteN a₀.store.ns (decI T) = some TP)
    (hlpsP : Frontend.denoteNList a₀.store.ns lps = some lpsP)
    (hrsP : denoteL a₀.store.ls (decI rs) = some rsP)
    (hcvTaP : Frontend.denoteCV a₀.store cvTa = some cvTaP) (hws : ConLeche.Expr.WScoped 0 cvTaP.type)
    (hcsP : ConRon.Bridge.Inductives.denoteCtors a₀.store cs = some csP)
    (hok₀ : ConRon.Bridge.Inductives.IFEnvOKS env₀ (fe.restrictTo vis0.toNat) a₀.store)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_ctors"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvTaw, cO, cL]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs)
        (isP != 0) (lg != 0) cvTa cs) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps
        nP.toNat nIdx.toNat (decI rs) (isP != 0) (lg != 0) cvTa cs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      DecB (fun m => decPL m (decCN m) (r.headD 0).toNat (r.tail.headD 0).toNat) s'.mem
        (AM.res (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat
          (decI rs) (isP != 0) (lg != 0) cvTa cs) a₀).1 ∧
      DecB (fun m => decPL m (sortsDec m) (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat)
        s'.mem (AM.res (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat
          nIdx.toNat (decI rs) (isP != 0) (lg != 0) cvTa cs) a₀).2 ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (sctsW_spec p hP (realCall p) (realCall_spec p) k s₀ vis0 vis T lo ll nP nIdx rs isP
    lg cvTaw cO cL) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hok, hC', hg', hd1, -, hd2, -, hA', -⟩ := (sctsW_okC hq henv hV hOpf hLC hLT hApd hCrk vis0 T lo ll nP nIdx rs isP lg
    cvTaw lps cvTa hT hrs hws k hk _ a₀ cO cL cs csP hC hlps hlb hta hcs hA hTP hlpsP hrsP hcvTaP hcsP
    hok₀ hfe).run hm
  exact ⟨hl, hok, hC', hg', hd1, hd2, hA'⟩

end sims

end L.Ind
