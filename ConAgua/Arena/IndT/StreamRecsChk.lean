module

public import ConAgua.Arena.IndT.StreamRecsRules
public import ConAgua.Arena.RecGenSpec.DecRR
public import ConRon.Bridge.Inductives.RecCheck
import ConRon.Bridge.Inductives.StreamRecs
import ConRon.Bridge.Core.Walks.Cached
import ConAgua.Arena.DeclCanonConst
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.RecGenSpec.Rec3IwSlice
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.RefWalk
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndInstallSpec.DomsW
import all ConAgua.Arena.IndStream
public import ConAgua.Arena.IndDecStab
import ConAgua.L.WordOff
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# `stream_rec_compare` under `StageC` (lane `ronsync2`, stage 3)

`src_ref`: `stream_rec_compare(vis, rc, g)` (`IndStream.lean`) refines con-ron's
`streamRecCompare`, both outcomes: `cv_lps` (no twin step), the type check unless the two type
words agree (`rtyc_ref`), the rules (`srk_ref`). Inputs: the record `rc` (`decRS`) and the
generated triple `g` (`decRR`), decoded below the tops, and their denotations (`dRec`, `dRecOut`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A generated triple `[cv, M, rhss.off, rhss.len]` decoded below the tops: its words. -/
theorem decRR_parts {m : Mem} {p : Nat} {g : IConstantVal × TargetMajor × List EIdx}
    (h : DecB (fun m => decRR m p) m g) :
    (∃ q, iwN m p = some q ∧ decCVp m q = some g.1) ∧
    (∃ q, p + 1 < iwTop m ∧ iwN m (p + 1) = some q ∧ DecB (fun m => decTM m q) m g.2.1) ∧
    ∃ o l, p + 2 < iwTop m ∧ p + 3 < iwTop m ∧ iwN m (p + 2) = some o ∧ iwN m (p + 3) = some l ∧
      DecB (fun m => decHL m o l) m g.2.2 ∧ (o + l ≤ iwTop m ∨ l = 0) := by
  have h' : decRR (truncM m) p = some g := h
  simp only [decRR, decAt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h'
  obtain ⟨q, hq, cv, hcv, mp, hmp, M, hM, rh, ⟨o, ho, l, hl, hrh⟩, rfl⟩ := h'
  exact ⟨⟨q, (L.Ind.iwN_truncM_some hq).2, decCVp_truncM hcv⟩,
    ⟨mp, (L.Ind.iwN_truncM_some hmp).1, (L.Ind.iwN_truncM_some hmp).2, hM⟩,
    ⟨o, l, (L.Ind.iwN_truncM_some ho).1, (L.Ind.iwN_truncM_some hl).1, (L.Ind.iwN_truncM_some ho).2, (L.Ind.iwN_truncM_some hl).2,
      hrh, rec3IwSlice hrh⟩⟩

/-- An `IW` word below the top, read after a growth. -/
theorem iwN_at {m m' : Mem} (hg : IWGrow m m') {w : Word} {k v : Nat}
    (hi : w.toNat + k < iwTop m) (h : iwN m (w.toNat + k) = some v)
    (hsz : (m'.arr64 IW).size < 2 ^ 64) :
    rdW (m'.arr64 IW) (w + UInt64.ofNat k) = UInt64.ofNat v ∧ (UInt64.ofNat v : Word).toNat = v :=
  rec2RdN (by rw [iwN_grow hg hi]; exact h) hsz

/-- An `IW` word at `w` read through `iwN`. -/
theorem iwN_rd0 {m : Mem} {w : Word} {v : Nat} (h : iwN m w.toNat = some v)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    rdW (m.arr64 IW) w = UInt64.ofNat v ∧ (UInt64.ofNat v : Word).toNat = v := by
  have := rec2RdN (w := w) (k := 0) (by simpa using h) hsz
  simpa using this

section sims
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env}

/-- **`stream_rec_compare` refines `streamRecCompare`, both outcomes** (twin side con-ron's
`streamRecCompare_spec`): `cv_lps` of the generated constant (no twin step), `rec_ty_check`
(`rtyc_ref`) unless the two type words agree, then `stream_rules_check` (`srk_ref`). -/
theorem src_ref (hP : StrProg p) (hq : KnotStageProg p) (henv : ConLeche.EnvWF env)
    (hApd : ApdF p) (hCrf : CrfF p) (N : Nat) (hN : N ≤ 2 ^ 62) {m : Mem} {a : AState}
    {rcw gw : Word} {rc : RecShape} {g : IConstantVal × TargetMajor × List EIdx}
    {rcP : ConLeche.RecShape}
    {gP : ConLeche.ConstantVal × ConLeche.TargetMajor × List ConLeche.Expr}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hrc : DecB (fun m => decRS m rcw.toNat) m rc) (hg : DecB (fun m => decRR m gw.toNat) m g)
    (hrcP : ConRon.Bridge.Inductives.dRec a.store rc = some rcP)
    (hgP : ConRon.Bridge.Inductives.dRecOut a.store g = some gP) :
    RefE (VerdictCtxU p) (srcE p N m vis rcw gw) (ConRon.Arena.streamRecCompare V fe rc g) a
      (fun v _ a' => SrPost dn vis fe env m a v.2 a') := by
  cases N with
  | zero => rw [srcE.eq_1]; exact RefE.of_cls0 rfl
  | succ N =>
  rw [srcE.arm1]
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hC.stage.iw.iwSize
  obtain ⟨hcvR, -, -, -, hrules, -⟩ := ConRon.Bridge.Inductives.dRec_inv hrcP
  obtain ⟨hcvG, -, hrh⟩ := ConRon.Bridge.Inductives.RC.dRecOut_inv hgP
  obtain ⟨-, hlpsG, htyG⟩ := ConRon.Bridge.Core.denoteCV_inv hcvG
  have htyR := (ConRon.Bridge.Core.denoteCV_inv hcvR).2.2
  -- the two constants' pointers
  obtain ⟨⟨qr, hqr, hcvr⟩, -⟩ := decRS_some (hrc.get (decRS_mono _))
  obtain ⟨⟨qg, hqg, hcvg⟩, -, -⟩ := decRR_parts hg
  obtain ⟨eqr, hqrN⟩ := iwN_rd0 hqr hsz
  obtain ⟨eqg, hqgN⟩ := iwN_rd0 hqg hsz
  rw [eqr, eqg]
  -- `cv_lps(cvG)`
  refine RefE.onlySim (fun _ => srcE.k_cv_lps.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
  obtain ⟨hS1, hg1, ⟨hl1, hlb1⟩, -⟩ := cvLpsW_ok h1 hC.stage (by rw [hqgN]; exact hcvg)
  rw [L.getD_zero, L.getD_one] at hl1 hlb1
  have hA1 : AbsOK m1 := cvLpsA_afr h1 hA
  have hC1 : StageC dn vis fe env m1 a :=
    hC.of_pstep hS1 hA1 (ConRon.Bridge.Inductives.PStep.refl hC.check.state)
  have hR1 : SrPost dn vis fe env m a m1 a :=
    ⟨hC1, hg1, hA1, ConRon.Bridge.CoreStep.refl hC.check⟩
  have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := hS1.iw.iwSize
  -- the record's and the triple's words, below the top
  obtain ⟨-, -, hwmI, -, ⟨ro, rn, hro, hrn, hrls⟩, -⟩ := decRS_some (show decRS (truncM m) rcw.toNat = some rc from hrc)
  rw [truncM_erA] at hrls
  obtain ⟨hwmIb, hwmI⟩ := L.Ind.iwN_truncM_some hwmI
  obtain ⟨hrob, hro⟩ := L.Ind.iwN_truncM_some hro
  obtain ⟨hrnb, hrn⟩ := L.Ind.iwN_truncM_some hrn
  obtain ⟨-, -, ⟨go, gl, hgob, hglb, hgo, hgl, hgsB, hgb⟩⟩ := decRR_parts hg
  have hW : ∀ m', IWGrow m m' → (m'.arr64 IW).size < 2 ^ 64 →
      rdW (m'.arr64 IW) (rcw + 2) = UInt64.ofNat rc.mI ∧
      rdW (m'.arr64 IW) (rcw + 4) = UInt64.ofNat ro ∧ rdW (m'.arr64 IW) (rcw + 5) = UInt64.ofNat rn ∧
      rdW (m'.arr64 IW) (gw + 2) = UInt64.ofNat go ∧ rdW (m'.arr64 IW) (gw + 3) = UInt64.ofNat gl :=
    fun m' hg' hsz' => ⟨(iwN_at (k := 2) hg' hwmIb hwmI hsz').1, (iwN_at (k := 4) hg' hrob hro hsz').1,
      (iwN_at (k := 5) hg' hrnb hrn hsz').1, (iwN_at (k := 2) hg' hgob hgo hsz').1,
      (iwN_at (k := 3) hg' hglb hgl hsz').1⟩
  obtain ⟨-, e2N⟩ := iwN_at (k := 2) (IWGrow.refl m) hwmIb hwmI hsz
  obtain ⟨-, e4N⟩ := iwN_at (k := 4) (IWGrow.refl m) hrob hro hsz
  obtain ⟨-, e5N⟩ := iwN_at (k := 5) (IWGrow.refl m) hrnb hrn hsz
  obtain ⟨-, g2N⟩ := iwN_at (k := 2) (IWGrow.refl m) hgob hgo hsz
  obtain ⟨-, g3N⟩ := iwN_at (k := 3) (IWGrow.refl m) hglb hgl hsz
  have hrls' : ∀ m', IWGrow m m' →
      decRules (erA m') (UInt64.ofNat ro : Word).toNat (UInt64.ofNat rn : Word).toNat = some rc.rules :=
    fun m' hg' => by rw [e4N, e5N]; exact ArrExt.decRules hg'.ext hrls
  have hgs' : ∀ m', IWGrow m m' →
      decHL m' (UInt64.ofNat go : Word).toNat (UInt64.ofNat gl : Word).toNat = some g.2.2 :=
    fun m' hg' => by rw [g2N, g3N]; exact hgsB.stab (OMono.decHL _ _) m' hg'
  have hgb' : ∀ m', IWGrow m m' → ((UInt64.ofNat go : Word).toNat + (UInt64.ofNat gl : Word).toNat ≤
      iwTop m' ∨ (UInt64.ofNat gl : Word).toNat = 0) :=
    fun m' hg' => by rw [g2N, g3N]; exact hgb.imp_left fun h => Nat.le_trans h hg'.iw
  -- the two type words
  obtain ⟨-, -, ⟨wt, hwt, hwtH, hwtE⟩⟩ := decCV_words hcvr
  obtain ⟨-, -, ⟨wg, hwg, hwgH, hwgE⟩⟩ := decCV_words hcvg
  have et : rdW (m1.arr64 (L.tierA EREC ((UInt64.ofNat qr + CV.type) >>> 40)))
      (UInt64.ofNat qr + CV.type &&& 1099511627775) = wt :=
    (erRdOK m1).off (hg1.ext _ _ hwt) (by rw [hqrN])
  have eg : rdW (m1.arr64 (L.tierA EREC ((UInt64.ofNat qg + CV.type) >>> 40)))
      (UInt64.ofNat qg + CV.type &&& 1099511627775) = wg :=
    (erRdOK m1).off (hg1.ext _ _ hwg) (by rw [hqgN])
  have key : (rc.cvR.type == g.1.type) = true ↔ wt = wg := by
    rw [beq_iff_eq, hwtE, hwgE, decI_inj_iff hwtH hwgH]
  unfold ConRon.Arena.streamRecCompare
  by_cases heq : wt = wg
  · rw [srcE.k_cv_lps.arm2 p N vis rcw gw _ _ r1 m1 (by rw [et, eg]; exact heq), srcE.j1.arm1]
    obtain ⟨-, e4, e5, g2, g3⟩ := hW m1 hg1 hsz1
    rw [e4, e5, g2, g3, ite_eq_left (key.mpr heq)]
    dsimp only
    exact RefE.lastE (K := srcE.k_stream_rules_check p) (f := fun v => (0, v.2)) (fun _ => rfl)
      (fun _ => rfl) id
      (srk_ref hq henv hApd hCrf N (by omega) m1 a _ _ _ _ _ _ _ gP.1.levelParams rc.rules rcP.rules
        g.2.2 gP.2.2 hC1 hA1 hl1 hlb1 hlpsG (hrls' m1 hg1) hrules (hgs' m1 hg1) (hgb' m1 hg1) hrh)
      fun _ _ _ _ h => hR1.trans h
  obtain ⟨e2, -⟩ := hW m1 hg1 hsz1
  by_cases h0 : (UInt64.ofNat rc.mI : Word) + 1 = 0
  · rw [srcE.k_cv_lps.abort1 p N vis rcw gw _ _ r1 m1 (by rw [et, eg]; exact heq)
      (by rw [e2]; exact h0)]
    exact RefE.of_cls0 rfl
  rw [srcE.k_cv_lps.arm1 p N vis rcw gw _ _ r1 m1 (by rw [et, eg]; exact heq) (by rw [e2]; exact h0),
    et, eg, e2, ite_eq_right (fun h => heq (key.mp h))]
  have hn1 : ((UInt64.ofNat rc.mI : Word) + 1).toNat = rc.mI + 1 := by
    have hlt := UInt64.toNat_lt (UInt64.ofNat rc.mI)
    rw [e2N] at hlt
    rcases Nat.lt_or_ge (rc.mI + 1) (2 ^ 64) with h | h
    · rw [UInt64.toNat_add, e2N]; simp; omega
    · exact absurd (UInt64.toNat_inj.mp (by rw [UInt64.toNat_add, e2N]; simp; omega)) h0
  rw [hwtE, hwgE, ← hn1]
  refine RefE.bindE (fun _ => srcE.k_rec_ty_check.none ..) id
    (rtyc_ref hP.toStrTyProg hq henv hApd hCrf N (by omega) hC1 hA1 hwtH hwgH hl1 hlb1 hlpsG
      (by rw [← hwtE]; exact htyR) (by rw [← hwgE]; exact htyG)) fun ⟨u2, m2⟩ _ a2 _ hR2 => ?_
  have hg2 : IWGrow m m2 := hg1.trans hR2.grow
  obtain ⟨-, e4, e5, g2, g3⟩ := hW m2 hg2 hR2.stage.stage.iw.iwSize
  rw [srcE.k_rec_ty_check.arm1, srcE.j1.arm1, e4, e5, g2, g3]
  exact RefE.lastE (K := srcE.k_stream_rules_check p) (f := fun v => (0, v.2)) (fun _ => rfl)
    (fun _ => rfl) id
    (srk_ref hq henv hApd hCrf N (by omega) m2 a2 _ _ _ _ _ _ _ gP.1.levelParams rc.rules rcP.rules
      g.2.2 gP.2.2 hR2.stage hR2.abs (by rw [decHL_grow hR2.grow hlb1]; exact hl1)
      (Nat.le_trans hlb1 hR2.grow.iw)
      (ConRon.Bridge.denoteNList_ext hR2.core.ext.lss.ls.ns _ _ hlpsG) (hrls' m2 hg2)
      (ConRon.Bridge.denoteRules_ext hR2.core.ext _ _ hrules) (hgs' m2 hg2) (hgb' m2 hg2)
      (ConRon.Bridge.denoteEList_ext hR2.core.ext _ _ hrh))
    fun _ _ _ _ h => (hR1.trans hR2).trans h

end sims

end L.Ind

end
