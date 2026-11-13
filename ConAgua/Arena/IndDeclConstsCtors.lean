module

public import ConAgua.Arena.IndDeclConstsFormers
public import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndPosSpec.RootHoles
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.IndInstallSpec.PartsAt
public import ConAgua.Arena.IndInstallSpec.InstallCtxWord9
import all ConAgua.Arena.IndParts
public import ConAgua.Arena.IndInstallSpec.ConsBlockCtors
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndDeclConsts

import ConAgua.L.ModelGen

@[expose] public section

/-!
# A declaration's constants: the constructors (lane `ronsync2`, stage 3)

`block_ctors_go(nP, T, c.off, c.len)`, `block_ctors_groups(nP, g.off, g.len)` and `block_ctors(p)`
refine con-ron's `blockCtors` (`Arena/Install.lean`, pure): the constructor groups
(`block_shape_ctor_groups`, the member records read as `(name, ctors)`), each constructor an
`.ctorInfo` record under its group's name (`ctor_info_rec`, `ciRec_stage`), consed into an `IW`
slice of `EREC` constant records (`sl_cons`, `consW_ci`), the groups appended (`sl_append`,
`appendW_ci`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `block_ctors`. -/
structure DcCtorsProg (p : Prog) : Prop extends FormersProg p where
  ctorInfo : p.lookup "ctor_info_rec" = some ctorInfoRecL
  numCtors : p.lookup "num_ctors_of" = some numCtorsOf
  ctorsCopy : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy
  allCtorsGo : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo
  allCtors : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors
  bcg : p.lookup "block_ctors_go" = some blockCtorsGo
  bcgs : p.lookup "block_ctors_groups" = some blockCtorsGroups
  cg : p.lookup "block_shape_ctor_groups" = some blockShapeCtorGroups
  slAppend : p.lookup "sl_append" = some slAppend
  bc : p.lookup "block_ctors" = some blockCtors

/-! ## `block_ctors_go` -/

/-- **The model of `block_ctors_go(nP, co, cl)`** at exec fuel `n`. -/
l_model bcg_spec (p : Prog) (hp : p.lookup "block_ctors_go" = some blockCtorsGo)
  fns [hp ↦ bcgW list]
  specs [callW_spec p n "ctor_info_rec", callW_spec p n "sl_cons"]
  grind [arena_grind]

/-- `ctor_info_rec`'s run, as its model. -/
theorem ciCall {p : Prog} (hP : DcCtorsProg p) {n : Nat} {m m' : Mem} {cv nP nF T : Word} {r : List Word}
    (h : callW p n "ctor_info_rec" [cv, nP, nF, T] m = some (r, m')) :
    ciRecW m cv nP nF T = some (r.headD 0, m') := by
  obtain ⟨s', rfl, -, hK⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ciRec_specW p hP.erAlloc hP.erPut hP.ctorInfo n _ cv nP nF T) h
  exact hK

/-- The twin's constructors of a constructor list, under the family `T`. -/
def ctorsOf (N : Nat) (T : NIdx) (cs : List (IConstantVal × Nat)) : List IConstantInfo :=
  cs.map fun c => .ctorInfo c.1 N c.2 T

/-- **`block_ctors_go` refines the constructors' records**: an `IW` slice of `EREC` constant
records below the pool's top. -/
theorem bcgW_ok {p : Prog} (hP : DcCtorsProg p) (nP T : Word) (a : AState) (vis : Word) (fe : IFEnv)
    (n : Nat) :
    ∀ (m m' : Mem) (co cl : Word) (cs : List (IConstantVal × Nat)) (r : List Word),
    StageR vis fe m a → PSlR0 decCN cs co cl m → bcgW p n m nP T co cl = some (r, m') →
    decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some (ctorsOf nP.toNat (decI T) cs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a ∧ IWGrow m m' := by
  induction n with
  | zero => intro m m' co cl cs r _ _ h; simp [bcgW] at h
  | succ n ih =>
  intro m m' co cl cs r hS hcs h
  by_cases hl : cl = 0
  · rw [bcgW.arm1 p n m nP T co cl hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : cs = [] := by
      have h := hcs.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact ⟨by simp [decPL, ctorsOf], by simp, hS, IWGrow.refl m⟩
  obtain ⟨q, ⟨cv, nF⟩, rest, rfl, hw, hqb, hdc, hrest⟩ := partsPSl_cons ⟨hcs.1, hcs.2.resolve_left hl⟩ hl
  rw [bcgW.arm2 p n m nP T co cl hl, hw] at h
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hdc' : decCN (truncM m) q = some (cv, nF) := hdc
  obtain ⟨⟨cqN, hcq, hcv⟩, hnF⟩ := decCN_some hdc'
  rw [← hq'] at hcq
  obtain ⟨w2, hw2, hw2v, hqlt⟩ := rdW_of_iwN_truncM hcq
  have hw1 : (UInt64.ofNat q + 1 : Word).toNat = q + 1 := by
    have := hS.iw.iwSize; have := hS.iw.iw; rw [UInt64.toNat_add, hq']; simp; omega
  have hnF' : iwN (truncM m) (UInt64.ofNat q + 1 : Word).toNat = some nF := by rw [hw1]; exact hnF
  obtain ⟨w3, hw3, hw3v, -⟩ := rdW_of_iwN_truncM hnF'
  rw [hw2, hw3] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [bcgW.k_ctor_info_rec.none])
  rw [bcgW.k_ctor_info_rec.arm1] at h
  have hcvE : decCV (erecP m) w2.toNat = some cv := by rw [hw2v]; exact decCVp_truncM hcv
  obtain ⟨hS1, hg1, hci⟩ := ciRec_stage (ciCall hP h1) hS hcvE
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [bcgW.k_block_ctors_go.none])
  obtain ⟨hd3, hb3, hS3, hg3⟩ := ih m1 m3 (co + 1) (cl - 1) rest r3 hS1 (PSlR0.grow (fun q => decCN_mono q) ⟨hrest.1, .inr hrest.2⟩ hg1) h3
  rw [bcgW.k_block_ctors_go.arm1] at h
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [bcgW.k_sl_cons.none])
  rw [bcgW.k_sl_cons.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hd5, hb5, hS5, hg5⟩ := consW_ci (consCall hP.toFormersProg h4) hS3 hb3 hd3
    (hg3.ext.decCI hci)
  refine ⟨by simpa [ctorsOf, hw3v] using hd5, by simp only [List.headD_cons, List.tail_cons]; omega, hS5,
    hg1.trans (hg3.trans hg5)⟩

/-- Two `EREC` constant-record slices appended (`sl_append`). -/
theorem appendW_ci {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {o1 l1 o2 l2 : Word}
    {r : List Word} {xs ys : List IConstantInfo}
    (h : appendW n m o1 l1 o2 l2 = some (r, m')) (hS : StageR vis fe m a)
    (hb1 : o1.toNat + l1.toNat ≤ iwTop m) (hb2 : o2.toNat + l2.toNat ≤ iwTop m)
    (hx : decPL m (decCI (erecP m)) o1.toNat l1.toNat = some xs)
    (hy : decPL m (decCI (erecP m)) o2.toNat l2.toNat = some ys) :
    decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some (xs ++ ys) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' ∧ StageR vis fe m' a ∧ IWGrow m m' := by
  obtain ⟨hS', hg, h0, h1, htop, hc1, hc2⟩ := appendW_stage h hS hb1 hb2
  have hlx := decPL_length m hx
  have hly := decPL_length m hy
  refine ⟨?_, by omega, hS', hg⟩
  rw [h0, h1, ← hlx, ← hly, ← List.length_append]
  apply decPL_of_get
  intro j hj
  simp only [List.length_append] at hj
  by_cases hj1 : j < xs.length
  · obtain ⟨v, x, hv, hfx, hgx⟩ := decPL_get _ _ _ hx j (by omega)
    refine ⟨v, ?_, ?_⟩
    · simp only [iwN, nat?, iwA, aread_apply] at hv ⊢
      rw [hc1 j (by omega)]; exact hv
    · rw [List.getElem_append_left hj1]
      rw [List.getElem?_eq_getElem hj1] at hgx
      rw [Option.some.inj hgx]; exact hg.ext.decCI hfx
  · obtain ⟨v, x, hv, hfx, hgx⟩ := decPL_get _ _ _ hy (j - xs.length) (by omega)
    refine ⟨v, ?_, ?_⟩
    · simp only [iwN, nat?, iwA, aread_apply] at hv ⊢
      rw [show iwTop m + j = iwTop m + l1.toNat + (j - xs.length) by omega, hc2 _ (by omega)]; exact hv
    · rw [List.getElem_append_right (by omega)]
      rw [List.getElem?_eq_getElem (by omega)] at hgx
      rw [Option.some.inj hgx]; exact hg.ext.decCI hfx

/-! ## `block_ctors_groups` -/

/-- **The model of `block_ctors_groups(nP, go, gl)`** (generated). -/
l_model bcgs_spec (p : Prog) (hp : p.lookup "block_ctors_groups" = some blockCtorsGroups)
  fns [hp ↦ bcgsW list]
  specs [callW_spec p n "block_ctors_go", callW_spec p n "sl_append"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- The twin's constructors of the groups. -/
def groupsCtors (N : Nat) (gs : List (NIdx × List (IConstantVal × Nat))) : List IConstantInfo :=
  gs.flatMap fun g => ctorsOf N g.1 g.2

/-- **`block_ctors_groups` refines the groups' constructors**: an `IW` slice of `EREC` constant
records below the pool's top. -/
theorem bcgsW_ok {p : Prog} (hP : DcCtorsProg p) (nP : Word) (a : AState) (vis : Word) (fe : IFEnv)
    (n : Nat) :
    ∀ (m m' : Mem) (go gl : Word) (gs : List (NIdx × List (IConstantVal × Nat))) (r : List Word),
    StageR vis fe m a → PSlR decCtorGrp gs go gl m → bcgsW p n m nP go gl = some (r, m') →
    decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some (groupsCtors nP.toNat gs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a ∧ IWGrow m m' := by
  induction n with
  | zero => intro m m' go gl gs r _ _ h; rw [bcgsW.eq_1] at h; cases h
  | succ n ih =>
  intro m m' go gl gs r hS hgs h
  by_cases hl : gl = 0
  · rw [bcgsW.arm1 p n m nP go gl hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : gs = [] := by
      have h := hgs.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact ⟨by simp [decPL, groupsCtors], by simp, hS, IWGrow.refl m⟩
  obtain ⟨q, g, rest, rfl, hw, hqb, hdx, hrest⟩ := partsPSl_cons hgs hl
  rw [bcgsW.arm2 p n m nP go gl hl, hw] at h
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hdx' : decCtorGrp (truncM m) q = some g := hdx
  simp only [decCtorGrp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hdx'
  obtain ⟨ms, hms, rfl⟩ := hdx'
  obtain ⟨⟨av, hav, hcvT⟩, -, -, hct⟩ := decMS_some hms
  obtain ⟨hwa, havb, -⟩ := partsIwRd hav (w := UInt64.ofNat q) hq'
  have hcvE : decCV (erecP m) av = some ms.cvT := decCVp_truncM hcvT
  obtain ⟨wn, hwn, hwnl, hname⟩ := decCV_name hcvE
  have hav' : (UInt64.ofNat av : Word).toNat = av := UInt64.toNat_ofNat_of_lt' havb
  have hrn : erRd m (UInt64.ofNat av) = wn := (erRd_of_erecP (by rw [hav']; exact hwn)).1
  obtain ⟨co, cl, hco, hcl, hcsd, hcb⟩ := partsAt decCN_mono (show decAt (truncM m) (decPL (truncM m) (decCN (truncM m))) (q + 2) = some ms.ctors from hct)
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hq2 : (UInt64.ofNat q + 2 : Word).toNat = q + 2 := by
    have := partsIwLt hcl; have := hq'; rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  have hq3 : (UInt64.ofNat q + 3 : Word).toNat = q + 2 + 1 := by
    have := partsIwLt hcl; have := hq'; rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  obtain ⟨hwo, -, -⟩ := partsIwRd hco (w := UInt64.ofNat q + 2) hq2
  obtain ⟨hwl, -, -⟩ := partsIwRd hcl (w := UInt64.ofNat q + 3) hq3
  rw [UInt64.ofNat_toNat] at hwo hwl
  have hrd : rdW (m.arr64 (tierA EREC (rdW (m.arr64 IW) (UInt64.ofNat q) >>> 40)))
      (rdW (m.arr64 IW) (UInt64.ofNat q) &&& 1099511627775) = wn := by
    rw [hwa]; exact hrn
  rw [hrd, hwo, hwl] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [bcgsW.k_block_ctors_go.none])
  rw [bcgsW.k_block_ctors_go.arm1] at h
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (bcg_spec p hP.bcg n _ nP wn co cl) h1
  have hcs : PSlR0 decCN ms.ctors co cl m := ⟨hcsd, hcb⟩
  obtain ⟨hd1, hb1, hS1, hg1⟩ := bcgW_ok hP nP wn a vis fe n _ _ _ _ _ _ hS hcs hW1
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [bcgsW.k_block_ctors_groups.none])
  obtain ⟨hd2, hb2, hS2, hg2⟩ := ih s1.mem m2 (go + 1) (gl - 1) rest r2 hS1 (hrest.grow decCtorGrp_mono hg1) h2
  rw [bcgsW.k_block_ctors_groups.arm1] at h
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [bcgsW.k_sl_append.none])
  rw [bcgsW.k_sl_append.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (slAppend_specW p hP.alloc hP.iwCopy hP.slAppend n _ _ _ _ _) h3
  have hb1' : (r1.headD 0).toNat + (r1.tail.headD 0).toNat ≤ iwTop m2 := by have := hg2.iw; omega
  obtain ⟨hd3, hb3, hS3, hg3⟩ := appendW_ci hW3 hS2 hb1' hb2 (decPL_ci_grow hg2 hb1 hd1) hd2
  refine ⟨?_, by simp only [List.headD_cons, List.tail_cons]; omega, hS3, (hg1.trans hg2).trans hg3⟩
  simp only [List.headD_cons, List.tail_cons]
  rw [hd3]
  simp [groupsCtors, hname]
/-! ## `block_ctors` -/

/-- **The model of `block_ctors(p)`** (generated). -/
l_model dbct_spec (p : Prog) (hp : p.lookup "block_ctors" = some blockCtors)
  fns [hp ↦ dbctW list]
  specs [callW_spec p n "block_shape_ctor_groups", callW_spec p n "block_ctors_groups"]
  grind [arena_grind]

/-- The shape's `nP` word (`p + 4`), in any memory grown into. -/
theorem shape_nP {m : Mem} {pp : Word} {bs : BlockShape} (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (h9 : pp.toNat + 9 ≤ iwTop m) {m' : Mem} (hg : IWGrow m m') :
    (rdW (m'.arr64 IW) (pp + 4)).toNat = bs.nP := by
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨-, -, hnp, -⟩ := decBS_some hqt
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have e4 : (pp + 4).toNat = pp.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  rw [← e4] at hnp
  obtain ⟨w, hw, hwv, hlt⟩ := rdW_of_iwN_truncM hnp
  have : rdW (m'.arr64 IW) (pp + 4) = rdW (m.arr64 IW) (pp + 4) := by
    simp only [rdW]; rw [hg.iwGet _ hlt]
  rw [this, hw, hwv]

/-- **`block_ctors` refines `blockCtors`** (pure in the twin): an `IW` slice of `EREC` constant
records below the pool's top. -/
theorem dbctW_ok {p : Prog} (hP : DcCtorsProg p) {n : Nat} {m m' : Mem} {pp : Word}
    {bs : BlockShape} {r : List Word} {a : AState} {vis : Word} {fe : IFEnv}
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (hsrc : ShapeSrc m pp) (h : dbctW p n m pp = some (r, m')) :
    decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (ConRon.Arena.blockCtors bs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a ∧ IWGrow m m' := by
  rcases n with _ | n
  · simp [dbctW] at h
  rw [dbctW.arm1] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [dbctW.k_block_shape_ctor_groups.none])
  rw [dbctW.k_block_shape_ctor_groups.arm1] at h
  obtain ⟨s1, hs1, -, hm1, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (bscg_spec p hP.cg n _ pp) h1
  subst hs1
  simp only at hm1 hW1
  simp only [bscgW, Option.some.injEq] at hW1
  subst hW1
  rw [hm1] at h
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [dbctW.k_block_ctors_groups.none])
  rw [dbctW.k_block_ctors_groups.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  have hnP := shape_nP hq hq9 (IWGrow.refl m)
  simp only [List.headD_cons, List.tail_cons] at h2
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (bcgs_spec p hP.bcgs n _ _ _ _) h2
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdm, -⟩ := partsAt decMS_mono hmem
  obtain ⟨hw0, -, -⟩ := partsIwRd ho (w := pp) rfl
  obtain ⟨hw1, -, -⟩ := partsIwRd hl (w := pp + 1) (by
    have := partsIwLt hl; have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega)
  rw [UInt64.ofNat_toNat] at hw0 hw1
  have hgs : PSlR decCtorGrp bs.ctorGroups (rdW (m.arr64 IW) pp) (rdW (m.arr64 IW) (pp + 1)) m := by
    rw [hw0, hw1]
    exact ⟨decPL_decCtorGrp hdm, hsrc _ _ (L.Ind.iwN_truncM_some ho).2 (L.Ind.iwN_truncM_some hl).2⟩
  obtain ⟨hd, hbd, hS2, hg2⟩ := bcgsW_ok hP _ a vis fe n _ _ _ _ _ _ hS hgs hW2
  refine ⟨?_, by simpa using hbd, hS2, hg2⟩
  rw [hnP] at hd
  simpa [ConRon.Arena.blockCtors, groupsCtors, ctorsOf, BlockShape.ctorGroups, List.flatMap] using hd

end L.Ind

end
