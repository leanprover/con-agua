module

public import ConAgua.Arena.IndT.StreamRecsFire
import ConAgua.Arena.IndT.StreamRecsChk
public import ConAgua.Arena.IndT.TailStream
import ConRon.Bridge.Inductives.Records
import ConAgua.Arena.RefWalk
import ConRon.Bridge.Inductives.StreamRecs
import ConRon.Bridge.Core.Walks.Cached
import all ConAgua.Arena.IndStream
import ConAgua.Arena.BasisBlockC
public import ConAgua.Arena.IndT.StreamRecsRules
import ConAgua.L.WordOff

@[expose] public section

/-!
# `stream_rec_check` and `stream_recs_check` under `StageC` (lane `ronsync2`, stage 3)

`sr1_ref`: `stream_rec_check(vis, rc, g)` refines con-ron's `streamRecCheck`, both outcomes:
`stream_rules_shape` (`srs_ref`), `generated_fire` (`gf_sim`), `stream_nested_ok` (its step, the
hypothesis `SnoSim`), the guard, then `stream_rec_compare` (`src_ref`). `srsc_ref`: the loop.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A target major's constructor slice (`[cv, nF]` pointers at words `6`, `7`). -/
theorem decTM_ctorsT {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    ∃ o l, iwN m (p + 6) = some o ∧ iwN m (p + 7) = some l ∧ decPL m (decCN m) o l = some M.ctors := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, c, hc, _, -, _, -, _, -, rfl⟩ := h
  exact decAt_some hc

/-- **`stream_nested_ok`'s step** (the obligation `sr1_ref` takes): con-ron's `streamNestedOk` at
the stored type, the major's binder, the fire `generated_fire` decoded; `0` exactly when it is
`false`. -/
def SnoSim (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (n : Nat) (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState)
    (ty mI rP : Word) (r : List Word) (f : IRecRuleFire) (tyP : ConLeche.Expr)
    (fP : ConLeche.RecRuleFire),
    StageC dn vis fe env m a → AbsOK m → ConLeche.EnvWF env → ty.toNat < 2 ^ 32 →
    denoteE a.store (decI ty) = some tyP → decFireG m r f →
    Frontend.denoteFire a.store f = some fP →
    Sim (callW p n "stream_nested_ok" [ty, mI, rP, r.headD 0, r.tail.headD 0, r.tail.tail.headD 0,
        r.tail.tail.tail.headD 0, r.tail.tail.tail.tail.headD 0] m)
      (ConRon.Arena.streamNestedOk (decI ty) mI.toNat rP.toNat f) a
      fun r' b m' a' => SrPost dn vis fe env m a m' a' ∧ (r'.headD 0 = 0 ↔ b = false)

/-- A pointer slice decoded below the tops at a nonzero length: its head and its tail. -/
theorem pslR_cons {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o l : Word} {m : Mem}
    (h : PSlR f xs o l m) (hl : l ≠ 0) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∃ v y xs', xs = y :: xs' ∧ rdW (m.arr64 IW) o = UInt64.ofNat v ∧ DecB (fun m => f m v) m y ∧
      PSlR f xs' (o + 1) (l - 1) m ∧ (UInt64.ofNat v : Word).toNat = v := by
  obtain ⟨hd, hb⟩ := h
  have hd' : decPL (truncM m) (f (truncM m)) o.toNat l.toNat = some xs := hd
  obtain ⟨k, hk⟩ : ∃ k, l.toNat = k + 1 := ⟨l.toNat - 1, by have := L.toNat_ne_zero_of_ne _ hl; omega⟩
  rw [hk, decPL_succ] at hd'
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hd'
  obtain ⟨v, hv, y, hy, xs', hxs', rfl⟩ := hd'
  obtain ⟨hvb, hv⟩ := L.Ind.iwN_truncM_some hv
  obtain ⟨e, eN⟩ := iwN_rd0 hv hsz
  have htop : iwTop m < 2 ^ 64 := by simp only [iwTop]; exact UInt64.toNat_lt _
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hl1 : (l - 1).toNat = k := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  exact ⟨v, y, xs', rfl, e, hy, ⟨by show decPL (truncM m) _ _ _ = _; rw [ho1, hl1]; exact hxs',
    by rw [ho1, hl1]; omega⟩, eN⟩

section sims
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env}

/-- **`stream_rec_check` refines `streamRecCheck`, both outcomes** (twin side con-ron's
`streamRecCheck_spec`), `stream_nested_ok`'s step taken as `hSno`. -/
theorem sr1_ref (hP : StrProg p) (hG : GfLook p) (hSno : SnoSim p dn) (hq : KnotStageProg p)
    (henv : ConLeche.EnvWF env) (hApd : ApdF p) (hCrf : CrfF p) (N : Nat) (hN : N ≤ 2 ^ 62)
    {m : Mem} {a : AState} {rcw gw : Word} {rc : RecShape}
    {g : IConstantVal × TargetMajor × List EIdx} {rcP : ConLeche.RecShape}
    {gP : ConLeche.ConstantVal × ConLeche.TargetMajor × List ConLeche.Expr}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hrc : DecB (fun m => decRS m rcw.toNat) m rc) (hg : DecB (fun m => decRR m gw.toNat) m g)
    (hrcP : ConRon.Bridge.Inductives.dRec a.store rc = some rcP)
    (hgP : ConRon.Bridge.Inductives.dRecOut a.store g = some gP) :
    RefE (VerdictCtxU p) (sr1E p N m vis rcw gw) (ConRon.Arena.streamRecCheck V fe rc g) a
      (fun v _ a' => SrPost dn vis fe env m a v.2 a') := by
  cases N with
  | zero => rw [sr1E.eq_1]; exact RefE.of_cls0 rfl
  | succ N =>
  rw [sr1E.arm1]
  unfold ConRon.Arena.streamRecCheck
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hC.stage.iw.iwSize
  obtain ⟨hcvRd, hrPe, hmIe, -, hrules, -⟩ := ConRon.Bridge.Inductives.dRec_inv hrcP
  obtain ⟨-, hMP, -⟩ := ConRon.Bridge.Inductives.RC.dRecOut_inv hgP
  -- the record's words, below the top
  obtain ⟨⟨qr, hqr, hcvr⟩, hwrP, hwmI, -, ⟨ro, rn, hro, hrn, hrls⟩, -⟩ :=
    decRS_some (show decRS (truncM m) rcw.toNat = some rc from hrc)
  rw [truncM_erA] at hrls
  obtain ⟨hqrb, hqr⟩ := L.Ind.iwN_truncM_some hqr
  obtain ⟨hwrPb, hwrP⟩ := L.Ind.iwN_truncM_some hwrP
  obtain ⟨hwmIb, hwmI⟩ := L.Ind.iwN_truncM_some hwmI
  obtain ⟨hrob, hro⟩ := L.Ind.iwN_truncM_some hro
  obtain ⟨hrnb, hrn⟩ := L.Ind.iwN_truncM_some hrn
  -- the generated triple's major and its constructors
  obtain ⟨-, ⟨mp, hmpb, hmp, hTM⟩, -⟩ := decRR_parts hg
  obtain ⟨co, cl, hco, hcl, hcs⟩ := decTM_ctorsT (show decTM (truncM m) mp = some g.2.1 from hTM)
  obtain ⟨hcob, hco⟩ := L.Ind.iwN_truncM_some hco
  obtain ⟨hclb, hcl⟩ := L.Ind.iwN_truncM_some hcl
  have hcs0 : decPL m (decCN m) co cl = some g.2.1.ctors :=
    (show DecB (fun m => decPL m (decCN m) co cl) m g.2.1.ctors from hcs).get
      (OMono.decPL decCN_mono co cl)
  obtain ⟨eM, eMN⟩ := iwN_at (k := 1) (IWGrow.refl m) hmpb hmp hsz
  obtain ⟨e4, e4N⟩ := iwN_at (k := 4) (IWGrow.refl m) hrob hro hsz
  obtain ⟨e5, e5N⟩ := iwN_at (k := 5) (IWGrow.refl m) hrnb hrn hsz
  obtain ⟨e6, e6N⟩ := iwN_at (w := UInt64.ofNat mp) (k := 6) (IWGrow.refl m) (by rw [eMN]; exact hcob)
    (by rw [eMN]; exact hco) hsz
  obtain ⟨e7, e7N⟩ := iwN_at (w := UInt64.ofNat mp) (k := 7) (IWGrow.refl m) (by rw [eMN]; exact hclb)
    (by rw [eMN]; exact hcl) hsz
  obtain ⟨e1, e1N⟩ := iwN_at (k := 1) (IWGrow.refl m) hwrPb hwrP hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl,
    show UInt64.ofNat 5 = (5 : Word) from rfl, show UInt64.ofNat 6 = (6 : Word) from rfl,
    show UInt64.ofNat 7 = (7 : Word) from rfl] at eM e4 e5 e6 e7 e1
  rw [e4, e5, eM, e6, e7]
  -- `stream_rules_shape`
  refine RefE.bindE (fun _ => sr1E.k_stream_rules_shape.none ..) (fun _ => trivial)
    (srs_ref (G := True) N m a _ _ _ _ rc.rules g.2.1.ctors hsz (by rw [e4N, e5N]; exact hrls)
      (by rw [e6N, e7N]; exact hcs0)) fun ⟨u1, m1⟩ _ a1 _ ⟨hm1, ha1⟩ => ?_
  dsimp only at hm1 ha1
  subst hm1 ha1
  rw [sr1E.k_stream_rules_shape.arm1, e1]
  generalize hrw : (UInt64.ofNat rc.rP : Word) = rPw at e1N ⊢
  rw [← e1N]
  -- `generated_fire`
  refine RefE.bindSim (fun _ => sr1E.k_generated_fire.none ..)
    (gf_sim hG hC hA (by rw [eMN]; exact hTM) hMP) fun r2 x2 m2 a2 _ hrun2 ⟨hR2, hdf2, hden2⟩ => ?_
  rw [sr1E.k_generated_fire.arm1]
  -- `stream_nested_ok` on the stored type
  have hsz2 : (m2.arr64 IW).size < 2 ^ 64 := hR2.stage.stage.iw.iwSize
  obtain ⟨eq2, hqrN⟩ := iwN_at (k := 0) hR2.grow (by simpa using hqrb) (by simpa using hqr) hsz2
  obtain ⟨e2', e2N⟩ := iwN_at (k := 2) hR2.grow hwmIb hwmI hsz2
  obtain ⟨e1', -⟩ := iwN_at (k := 1) hR2.grow hwrPb hwrP hsz2
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl,
    show UInt64.ofNat 2 = (2 : Word) from rfl, UInt64.add_zero] at eq2 e2' e1'
  obtain ⟨-, -, ⟨wt, hwt, hwtH, hwtE⟩⟩ := decCV_words hcvr
  have et : rdW (m2.arr64 (L.tierA EREC ((UInt64.ofNat qr + CV.type) >>> 40)))
      (UInt64.ofNat qr + CV.type &&& 1099511627775) = wt :=
    (erRdOK m2).off (hR2.grow.ext _ _ (by have h := hwt; rw [truncM_erA] at h; exact h)) (by rw [hqrN])
  rw [hrw] at e1'
  rw [eq2, et, e2', e1', hwtE]
  generalize hmw : (UInt64.ofNat rc.mI : Word) = mIw at e2N ⊢
  rw [← e2N]
  have htyP := (ConRon.Bridge.Core.denoteCV_inv hcvRd).2.2
  rw [hwtE] at htyP
  refine RefE.bindSim (fun _ => sr1E.k_stream_nested_ok.none ..)
    (hSno N vis fe env m2 a2 wt _ _ r2 x2 _ _ hR2.stage hR2.abs henv hwtH
      (ConRon.Bridge.denote_ext htyP hR2.core.ext) hdf2 hden2)
    fun r3 b3 m3 a3 _ hrun3 ⟨hR3, hb3⟩ => ?_
  refine RefE.ofArms (fun h => sr1E.k_stream_nested_ok.abort1 _ _ _ _ _ _ _ h)
    (fun h => sr1E.k_stream_nested_ok.arm1 _ _ _ _ _ _ _ h) ?_
  refine RefE.guard (jp := fun _ => ConRon.Arena.streamRecCompare V fe rc g) rfl
    (fun h => hb3.mp h) (fun h => hb3.mpr h) fun _ _ => ?_
  have hR23 := hR2.trans hR3
  exact RefE.lastE (K := sr1E.k_stream_rec_compare p) (f := fun v => (0, v.2)) (fun _ => rfl)
    (fun _ => rfl) id
    (src_ref hP hq henv hApd hCrf N (by omega) hR3.stage hR3.abs
      (hrc.grow (decRS_mono _) hR23.grow) (hg.grow (decRR_mono _) hR23.grow)
      (ConRon.Bridge.Inductives.dRec_ext hR23.core.ext _ _ hrcP)
      (ConRon.Bridge.Inductives.dRecOut_ext hR23.core.ext _ _ hgP))
    fun _ _ _ _ h => hR23.trans h

open ConRon.Bridge.Inductives (mapM_option_cons_inv mapM_option_nil_inv dRec_ext dRecOut_ext) in
/-- **`stream_recs_check` refines `streamRecsCheck`, both outcomes** (twin side con-ron's
`streamRecsCheck_spec`): record by record (`sr1_ref`), the lengths' mismatch class `0`. -/
theorem srsc_ref (hP : StrProg p) (hG : GfLook p) (hSno : SnoSim p dn) (hq : KnotStageProg p)
    (henv : ConLeche.EnvWF env) (hApd : ApdF p) (hCrf : CrfF p) (N : Nat) (hN : N ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (ro rl go gl : Word) (rcs : List RecShape)
      (gs : List (IConstantVal × TargetMajor × List EIdx)) (rcsP : List ConLeche.RecShape)
      (gsP : List (ConLeche.ConstantVal × ConLeche.TargetMajor × List ConLeche.Expr)),
    StageC dn vis fe env m a → AbsOK m → PSlR decRS rcs ro rl m → PSlR decRR gs go gl m →
    rcs.mapM (ConRon.Bridge.Inductives.dRec a.store) = some rcsP →
    gs.mapM (ConRon.Bridge.Inductives.dRecOut a.store) = some gsP →
    RefE (VerdictCtxU p) (srscE p N m vis ro rl go gl) (ConRon.Arena.streamRecsCheck V fe rcs gs) a
      (fun v _ a' => SrPost dn vis fe env m a v.2 a') := by
  induction N with
  | zero => intros; rw [srscE.eq_1]; exact RefE.of_cls0 rfl
  | succ N ih =>
  intro m a ro rl go gl rcs gs rcsP gsP hC hA hr hgs hrP hgP
  have hsz := hC.stage.iw.iwSize
  by_cases h0 : rl = 0 ∧ gl = 0
  · rw [srscE.arm1 _ _ _ _ _ _ _ _ h0]
    obtain ⟨e1, e2⟩ := h0
    subst e1 e2
    rw [L.Ind.pslR_nil hr, L.Ind.pslR_nil hgs]
    simp only [ConRon.Arena.streamRecsCheck]
    exact RefE.ret rfl (SrPost.refl hC hA)
  by_cases h1 : rl = 0 ∨ gl = 0
  · rw [srscE.abort1 _ _ _ _ _ _ _ _ h0 h1]; exact RefE.of_cls0 rfl
  rw [srscE.arm2 _ _ _ _ _ _ _ _ h0 h1]
  obtain ⟨v, rc, rcs', rfl, ev, hrc, hr', evN⟩ := pslR_cons hr (fun h => h1 (.inl h)) hsz
  obtain ⟨w, g, gs', rfl, ew, hg, hgs', ewN⟩ := pslR_cons hgs (fun h => h1 (.inr h)) hsz
  obtain ⟨rcP, rcsP', rfl, hrcP, hrcsP⟩ := mapM_option_cons_inv hrP
  obtain ⟨gP, gsP', rfl, hgP1, hgsP⟩ := mapM_option_cons_inv hgP
  rw [ev, ew]
  simp only [ConRon.Arena.streamRecsCheck]
  refine RefE.bindE (fun _ => srscE.k_stream_rec_check.none ..) id
    (sr1_ref hP hG hSno hq henv hApd hCrf N (by omega) hC hA (by rw [evN]; exact hrc)
      (by rw [ewN]; exact hg) hrcP hgP1) fun ⟨u1, m1⟩ _ a1 _ hR1 => ?_
  rw [srscE.k_stream_rec_check.arm1]
  exact RefE.lastE (K := srscE.k_stream_recs_check p) (f := fun v => (0, v.2)) (fun _ => rfl)
    (fun _ => rfl) id
    (ih (by omega) m1 a1 _ _ _ _ rcs' gs' rcsP' gsP' hR1.stage hR1.abs
      (hr'.grow (fun q => decRS_mono q) hR1.grow) (hgs'.grow (fun q => decRR_mono q) hR1.grow)
      (dRec_ext.list hR1.core.ext _ _ hrcsP) (dRecOut_ext.list hR1.core.ext _ _ hgsP))
    fun _ _ _ _ h => hR1.trans h

end sims

/-- **`stream_recs_check`'s contract** (`IndT/TailStream`'s `StreamRecsRefS`), from `srsc_ref`
through the call (`srscE_spec`), `stream_nested_ok`'s step taken as `hSno`. -/
theorem streamRecsRefS_of {p : Prog} {dn : NIdx → Option ConLeche.Name} (hP : StrProg p)
    (hG : GfLook p) (hSno : SnoSim p dn) (hq : KnotStageProg p) (hApd : ApdF p) (hCrf : CrfF p) :
    StreamRecsRefS (VerdictCtxU p) p dn := by
  intro n hn vis fe env m a ro rl go gl rcs gs rcsP gsP hC hA henv hr hgs hrP hgP
  exact (RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩) (srscE_spec p hP n _ vis ro rl go gl)
    (fun hV => hV.nv) (srsc_ref hP hG hSno hq henv hApd hCrf n hn m a ro rl go gl rcs gs rcsP gsP
      hC hA hr hgs hrP hgP)).mono
    fun _ _ _ ⟨s', hs', _, hR⟩ => by rw [← hs']; exact ⟨hR.stage, hR.grow, hR.abs, hR.core⟩

end L.Ind

end
