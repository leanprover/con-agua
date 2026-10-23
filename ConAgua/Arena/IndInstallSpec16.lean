import ConAgua.Arena.IndInstallSpec15

/-!
# Refinements of `IndInstall`, part 16 (lane `indproofs2`, helper `install`): `checkBlockInds`,
the relation
-/


noncomputable section

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups of stage 1. -/
structure IndsProg (p : Prog) : Prop extends InstProg p, ConsIndsProg p where
  agreeP : AgreeProg p
  pinWord : p.lookup "pin_word" = some pinWordL
  withSort : p.lookup "block_shape_with_sort" = some blockShapeWithSort
  cvTas : p.lookup "check_block_inds_cv_tas" = some checkBlockIndsCvTas
  cvTasGo : p.lookup "check_block_inds_cv_tas_go" = some checkBlockIndsCvTasGo
  inds : p.lookup "check_block_inds" = some checkBlockInds

/-- Stage 1's post: the environment with the formers pushed at the returned view, the formers'
constants a slice below the tops, the shape with its sort below the tops. -/
def IndsOut (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : List Word)
    (x : IFEnv × List IConstantVal × BlockShape) (m' : Mem) (a' : AState) : Prop :=
  StageR dn (r.headD 0) x.1 m' a' ∧ IWGrow m m' ∧
    PSlR decCVp x.2.1 (r.tail.headD 0) (r.tail.tail.headD 0) m' ∧
    DecB (fun m => decBS m (r.tail.tail.tail.headD 0).toNat) m' x.2.2 ∧
    ShapeSrc m' (r.tail.tail.tail.headD 0)

/-- The callees of `check_block_inds` outside the `abstract1` cascade, which keep its memo
(`AbsKeep`, a program fact). -/
def indsKeepCallees : List FnName :=
  ["check_block_agree", "block_shape_with_sort", "check_block_inds_cv_tas", "cons_block_inds"]

/-- **`check_block_inds`' model refines `checkBlockInds`.** -/
theorem ibiW_sim {p : Prog} (hP : IndsProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp isRec : Word} {bs : BlockShape} {b : Bool}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcx : ShapeCV m pp) (hb : (isRec != 0) = b) (hA : AbsOK m)
    (hk : ∀ f ∈ indsKeepCallees, AbsKeep p f) :
    Sim (ibiW p n m vis pp isRec) (ConRon.Arena.checkBlockInds V fe ⟨bs⟩ b) a
      (fun r x m' a' => IndsOut dn m r x m' a' ∧ AbsOK m' ∧
        (RecsB m pp → RecsB m' (r.tail.tail.tail.headD 0))) := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, -⟩ := partsShapeFacts hq hsrc
  have hkw := partsShapeK hq' hq9
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdm, hob⟩ := partsAt decMS_mono hmem
  have hdm' : decPL (truncM m) (decMS (truncM m)) o.toNat l.toNat = some bs.members := hdm
  have hlk : bs.k = l.toNat := decPL_length _ hdm'
  have hkb : bs.k < 2 ^ 64 := by rw [hlk]; exact l.toNat_lt
  obtain ⟨hw0, -, -⟩ := partsIwRd ho (w := pp) rfl
  rw [UInt64.ofNat_toNat] at hw0
  have hkl : UInt64.ofNat bs.k = l := by rw [hlk]; exact UInt64.ofNat_toNat
  unfold ibiW
  rw [hkw, hkl, hw0, hnpw]
  split
  · exact Sim.of_none
  rename_i hl0
  -- the members, with their formers' constant records below the tops
  have hob' : o.toNat + l.toNat ≤ iwTop m := hob.resolve_left hl0
  have hoN : iwN m pp.toNat = some o.toNat := (rec2IwN_trunc ho).2
  have hlN : iwN m (pp.toNat + 1) = some l.toNat := (rec2IwN_trunc hl).2
  have hms : MemsOK m o l bs.members :=
    ⟨⟨hdm, hob'⟩, fun j hj c hc d hd => hcx o.toNat l.toNat hoN hlN j hj c hc d hd⟩
  obtain ⟨q0, ms0, rest, hmeq, hw, hqb, hmok, hrest⟩ := hms.cons hl0
  rw [hw]
  unfold ConRon.Arena.checkBlockInds
  simp only [hmeq]
  have hq0 : (UInt64.ofNat q0 : Word).toNat = q0 := UInt64.toNat_ofNat_of_lt' hqb
  -- member 0's former
  refine Sim.bindK (K := ibiK1 p n vis pp isRec (UInt64.ofNat bs.nP) o l)
    (body := fun r1 m1 => ibiK2 p n vis pp isRec (UInt64.ofNat bs.nP) r1
      (callW p n "check_block_teles" [vis, UInt64.ofNat bs.nP, o + 1, l - 1] m1)) rfl (fun _ _ => rfl)
    (by
      have h := installTeleSim hP.toInstProg n (nP := UInt64.ofNat bs.nP) hS hmok hA
      rw [UInt64.toNat_ofNat_of_lt' hnpb] at h; exact h) ?_
  rintro r1 ⟨cvTa0, s0⟩ m1 a1 ⟨⟨hS1, hg1, hcv1, hcx1, hs32, hsd⟩, hA1⟩
  dsimp only
  have hc0 := installCvDecB hcv1 hcx1
  -- the other members' formers
  refine Sim.bindK (K := ibiK2 p n vis pp isRec (UInt64.ofNat bs.nP) r1)
    (body := fun r2 m2 => ibiK3 p n vis pp isRec r1 r2 (callW p n "check_block_agree"
      [vis, UInt64.ofNat bs.nP, r1.headD 0, r1.tail.headD 0, r2.headD 0, r2.tail.headD 0] m2))
    rfl (fun _ _ => rfl)
    (by
      have h := Sim.callW_pos (fun k => installSimCall
        (Q := fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m1 m' ∧
          PSlR decTele x (r.headD 0) (r.tail.headD 0) m' ∧ AbsOK m')
        (checkBlockTeles_refines p hP.toInstProg (k + 1) ⟨m1, Locals.init []⟩ a1 dn vis fe
        (UInt64.ofNat bs.nP) (o + 1) (l - 1) rest hS1 (hrest.grow hg1) hA1)
        fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩) n
      rw [UInt64.toNat_ofNat_of_lt' hnpb] at h; exact h) ?_
  rintro r2 cvs m2 a2 ⟨hS2, hg2, hcvs, hA2⟩
  -- the agreements
  have hsd' : decI (r1.tail.headD 0) = s0 := hsd
  rw [← hsd']
  refine Sim.bindK (K := ibiK3 p n vis pp isRec r1 r2)
    (body := fun _ m3 => ibiK4 p n vis isRec r1 r2 (callW p n "block_shape_with_sort"
      [pp, r1.tail.headD 0] m3)) rfl (fun _ _ => rfl)
    (by
      have h := Sim.callW_pos (fun k => installSimCall
        (Q := fun _ _ m' a' => StageR dn vis fe m' a' ∧ IWGrow m2 m')
        (checkBlockAgree_refines p hP.agreeP (k + 1) ⟨m2, Locals.init []⟩ a2 dn vis fe
          (UInt64.ofNat bs.nP) (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) cvTa0 cvs hS2
          (hc0.grow (OMono.decCVp _) hg2) hs32 hcvs)
        fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩) n
      rw [UInt64.toNat_ofNat_of_lt' hnpb] at h
      exact Sim.withFr h (fun _ _ e => hk _ (by simp [indsKeepCallees]) _ _ _ _ _ e hA2)) ?_
  rintro - - m3 a3 ⟨⟨hS3, hg3⟩, hA3⟩
  have hg03 := (hg1.trans hg2).trans hg3
  -- the shape with its sort
  refine Sim.bindK (K := ibiK4 p n vis isRec r1 r2)
    (body := fun r4 m4 => ibiK5 p n vis isRec r4 (callW p n "check_block_inds_cv_tas"
      [r1.headD 0, r2.headD 0, r2.tail.headD 0] m4)) rfl (fun _ _ => rfl)
    (Sim.withFr (installWithSortSim hP.alloc hP.pinWord hP.withSort n hS3 (hq.grow (decBS_mono _) hg03)
      (partsHsrc_grow hg03 hq9 hsrc) hs32)
      (fun _ _ e => hk _ (by simp [indsKeepCallees]) _ _ _ _ _ e hA3)) ?_
  rintro r4 p1 m4 a4 ⟨⟨hS4, hg4, hp1, hsrc4, hrb4⟩, hA4⟩
  -- the formers' constants
  refine Sim.mstep (K := ibiK5 p n vis isRec r4) rfl (fun _ _ => rfl) fun r5 m5 h5 => ?_
  obtain ⟨hS5, hg5, hcvT⟩ := installCvTasRun hP.toCstProg hP.cvTas hP.cvTasGo h5 hS4
    ((hc0.grow (OMono.decCVp _) ((hg2.trans hg3).trans hg4)))
    (hcvs.grow decTele_mono (hg3.trans hg4))
  have hA5 := hk _ (by simp [indsKeepCallees]) _ _ _ _ _ h5 hA4
  -- the formers consed
  have hp1' := hp1.grow (decBS_mono _) hg5
  obtain ⟨-, hp9, -⟩ := partsShapeFacts hp1 hsrc4
  have hsrc5 := partsHsrc_grow hg5 hp9 hsrc4
  refine Sim.bindK (K := ibiK6 r4 r5) (body := fun r6 m6 =>
      some ([r6.headD 0, r5.headD 0, r5.tail.headD 0, r4.headD 0], m6)) rfl (fun _ _ => rfl)
    (Sim.callW_pos (fun k => installSimCall
      (Q := fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m5 m')
      (consBlockInds_refines p hP.toConsIndsProg (k + 1) ⟨m5, Locals.init []⟩ a4 dn vis fe (r4.headD 0) isRec
        (r5.headD 0) (r5.tail.headD 0) 0 p1 b _ hb hS5 hp1' hsrc5 hcvT (by have := (r5.tail.headD 0).toNat_lt; simp only [UInt64.toNat_zero, Nat.zero_add]; exact this))
      fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩) n |>.withFr
      (fun _ _ e => hk _ (by simp [indsKeepCallees]) _ _ _ _ _ e hA5)) ?_
  rintro r6 fe1 m6 a6 ⟨⟨hS6, hg6⟩, hA6⟩
  obtain ⟨-, hp9', -⟩ := partsShapeFacts hp1' hsrc5
  refine Sim.ret ⟨⟨hS6, (((((hg1.trans hg2).trans hg3).trans hg4).trans hg5).trans hg6), hcvT.grow (fun q => OMono.decCVp q) hg6,
    hp1'.grow (decBS_mono _) hg6, partsHsrc_grow hg6 hp9' hsrc5⟩, hA6, fun hrb =>
    ((hrb4 ((hrb.grow (hg1.trans hg2) (by omega)).grow hg3 (by have := hg1.trans hg2; have := this.1; omega))).grow
      (hg5.trans hg6) (by omega))⟩

/-- **`check_block_inds` refines `checkBlockInds`** (stage 1, through the stubs of its callees:
`check_constant_val`, `strip_pis`, `open_pis_at_fvars_f`, `fvar_type_d(s)`, `is_def_eq_core`,
`lvl_eq_c`, `lv_zero_caps`): the shape record decoded below the tops, its members' slice below the
top and their formers' constant records below the tops (`ShapeCV`); the environment with the
formers pushed at the returned view, the formers' constants and the shape with its sort below the
tops, the latter's recursor slice below the top if the input's is (`RecsB`: a copy). -/
@[refines ConRon.Arena.checkBlockInds]
theorem checkBlockInds_refines (p : Prog) (hP : IndsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (pp isRec : Word) (bs : BlockShape)
    (b : Bool) (hS : StageR dn vis fe s₀.mem a₀) (hq : DecB (fun m => decBS m pp.toNat) s₀.mem bs)
    (hsrc : ShapeSrc s₀.mem pp) (hcx : ShapeCV s₀.mem pp) (hb : (isRec != 0) = b) (hA : AbsOK s₀.mem)
    (hk : ∀ f ∈ indsKeepCallees, AbsKeep p f) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_inds" [vis, pp, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockInds V fe ⟨bs⟩ b) a₀ ∧
      IndsOut dn s₀.mem r (AM.res (ConRon.Arena.checkBlockInds V fe ⟨bs⟩ b) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlockInds V fe ⟨bs⟩ b) a₀) ∧ AbsOK s'.mem ∧
      (RecsB s₀.mem pp → RecsB s'.mem (r.tail.tail.tail.headD 0)); ⊤⦄ :=
  triple_post (ibi_spec p hP.inds n s₀ vis pp isRec) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ, hA', hR'⟩ := Sim.run (ibiW_sim hP n hS hq hsrc hcx hb hA hk) hm
    ⟨hl, hok, hQ, hA', hR'⟩

end L.Ind
