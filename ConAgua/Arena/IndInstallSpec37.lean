import ConAgua.Arena.IndInstallSpec36

/-!
# Refinements of `IndInstall`, part 37 (lane `indproofs4`): `checkBlock`

`check_block(vis, block.off, block.len, p0)` (`icbW`, `IndInstallSpec29`): the constructors' and the
members' names checked distinct (`block_shape_all_ctors`, `block_caps_ctor_names`,
`block_shape_member_names`, `sl_nodup` twice), the flush, the raw recursion bit
(`block_raw_rec`, the `mentions_any` memo `maMR`), the pass (`checkBlockPass_refines`) and the tail
(`checkBlockTail_refines`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The `mentions_any` memo across a writer outside the stage memos. -/
theorem maMR_mfr {m m' : Mem} {mp : Std.HashMap EIdx Bool} (h : MFr [] [] m m') (hm : maMR m mp) :
    maMR m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := h.memo maSch.arr maSch.cs (by decide) (by decide) (by simp) (by simp)
  exact memoRG_frame maSch maSch_wf bmKey _ A C hA hC m m' f mp hm

/-- The lookups of `check_block`. -/
structure CbProg (p : Prog) : Prop where
  pass : PassProg p
  tail : TailProg p
  cbr : CbrLook p
  ma : MaProg p
  ha : p.lookup "iw_alloc" = some iwAlloc
  cp : p.lookup "iw_copy" = some iwCopy
  nco : p.lookup "num_ctors_of" = some numCtorsOf
  acc : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy
  acg : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo
  ac : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors
  mnc : p.lookup "member_names_copy" = some memberNamesCopy
  bccn : p.lookup "block_caps_ctor_names" = some blockCapsCtorNames
  bsmn : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  slc : p.lookup "sl_contains" = some slContains
  nodup : p.lookup "sl_nodup" = some slNodup
  pdm : p.lookup "pi_doms_mention_any" = some piDomsMentionAny
  brm : p.lookup "block_raw_rec_member" = some blockRawRecMember
  brg : p.lookup "block_raw_rec_go" = some blockRawRecGo
  brr : p.lookup "block_raw_rec" = some blockRawRec
  cb : p.lookup "check_block" = some checkBlock

theorem ShapeCV.grow {m m' : Mem} {q : Word} (h : ShapeCV m q) (hg : IWGrow m m')
    (hq9 : q.toNat + 9 ≤ iwTop m)
    (hsrc : ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l ≤ iwTop m)
    (hptr : ∀ o l j v, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v + 1 < iwTop m) : ShapeCV m' q := by
  intro o l ho hl j hj c hc d hd
  rw [iwN_grow hg (by omega)] at ho
  rw [iwN_grow hg (by omega)] at hl
  have hb := hsrc o l ho hl
  rw [iwN_grow hg (by omega)] at hc
  have hcv := hptr o l j c ho hl hj hc
  rw [iwN_grow hg (by omega)] at hd
  exact CVExt_grow hg (h o l ho hl j hj c hc d hd)

/-! ## What the recursor stage needs of the pass -/

/-- Every word array below 256 but `target_abs`' memo's. -/
def taFreeA : List ArrId := (List.range 256).filter (· ≠ TAM)
/-- Every `CTL` word below 256 but that memo's two control words. -/
def taFreeC : List Word := ((List.range 256).filter (fun c => c ≠ 212 ∧ c ≠ 213)).map Nat.toUInt64

/-- A callee of a program whose text writes outside `target_abs`' memo keeps it. -/
theorem taMR.ofClosed {p : Prog} {fs : List FnName} (hcl : closedA p taFreeA taFreeC fs = true)
    {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word} {m' : Mem}
    (h : callW p n f vs m = some (r, m')) (hM : ∃ mp, taMR m mp) : ∃ mp, taMR m' mp := by
  obtain ⟨mp, hm⟩ := hM
  refine ⟨mp, taMR_mfr (S := [201, 202, 203, 204, 205, 207, 208])
    (T := [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 214, 215, 216, 217, 218, 219])
    ⟨taFreeA, taFreeC, (run_memFrame hcl hf (run_of_callW h)).1, fun b hb => ?_, fun x hx => ?_⟩
    (by decide) (by decide) hm⟩
  · simp only [taFreeA, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb
    have key : ∀ x < 256, x ≠ 206 → x < 201 ∨ 208 < x ∨ x ∈ [201, 202, 203, 204, 205, 207, 208] := by
      decide +kernel
    exact key b hb.1 (by simpa [TAM] using hb.2)
  · simp only [taFreeC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
    obtain ⟨c, ⟨hc, h2⟩, rfl⟩ := hx
    have : (Nat.toUInt64 c).toNat = c := by simp; omega
    rw [this]
    have key : ∀ x < 256, ¬ (x = 212 ∨ x = 213) → x < 202 ∨ 219 < x ∨
        x.toUInt64 ∈ ([202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 214, 215, 216, 217, 218, 219] : List Word) := by
      decide +kernel
    exact key c hc (by omega)

/-- **The members' constructors' level-parameter slices lie in `EREC`**: every constructor record
`[cv, nF]` of every member of the shape at `p0` (its words `+ 2`, `+ 3`) satisfies `CtorLp`. -/
def ShapeLp (m : Mem) (p0 : Word) : Prop :=
  ∀ o l, iwN m p0.toNat = some o → iwN m (p0.toNat + 1) = some l → ∀ j < l, ∀ c, iwN m (o + j) = some c →
    ∀ co cl, iwN m (c + 2) = some co → iwN m (c + 3) = some cl → CtorsLp m (UInt64.ofNat co) (UInt64.ofNat cl)

theorem ShapeLp.grow {m m' : Mem} {p0 : Word} {bs : BlockShape} (h : ShapeLp m p0)
    (hq : DecB (fun m => decBS m p0.toNat) m bs) (hsrc : ShapeSrc m p0) (hg : IWGrow m m') (hk : KeepW m m')
    (hsz : (m.arr64 IW).size < 2 ^ 64) : ShapeLp m' p0 := by
  intro o l ho hl j hj c hc co cl hco hcl
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some (show decBS (truncM m) p0.toNat = some bs from hq)
  obtain ⟨o', l', ho', hl', hd⟩ := decAt_some hmem
  have ho0 := (rec2IwN_trunc ho').2
  have hl0 := (rec2IwN_trunc hl').2
  rw [iwN_grow hg (rec2IwN_trunc ho').1, ho0] at ho
  rw [iwN_grow hg (rec2IwN_trunc hl').1, hl0] at hl
  have e1 := Option.some.inj ho
  have e2 := Option.some.inj hl
  subst e1 e2
  obtain ⟨c', hc', hms⟩ := decPL_getH (truncM m) hd j hj
  obtain ⟨hct, hcm⟩ := rec2IwN_trunc hc'
  rw [iwN_grow hg hct, hcm] at hc
  have e3 := Option.some.inj hc
  subst e3
  simp only [decMS, bind, Option.bind_eq_some_iff, pure] at hms
  obtain ⟨_, -, _, -, _, -, cts, hcts, -⟩ := hms
  obtain ⟨co', cl', hco', hcl', hdc⟩ := decAt_some hcts
  rw [iwN_grow hg (rec2IwN_trunc hco').1, (rec2IwN_trunc hco').2] at hco
  rw [show c' + 2 + 1 = c' + 3 by omega] at hcl'
  rw [iwN_grow hg (rec2IwN_trunc hcl').1, (rec2IwN_trunc hcl').2] at hcl
  have e4 := Option.some.inj hco
  have e5 := Option.some.inj hcl
  subst e4 e5
  have hol : co' < 2 ^ 64 ∧ cl' < 2 ^ 64 := by
    have h6 := (rec2IwN_trunc hco').2; have h7 := (rec2IwN_trunc hcl').2
    simp only [iwN, nat?, Option.map_eq_some_iff] at h6 h7
    obtain ⟨w1, -, rfl⟩ := h6; obtain ⟨w2, -, rfl⟩ := h7
    exact ⟨w1.toNat_lt, w2.toNat_lt⟩
  refine (h o' l' ho0 hl0 j hj c' hcm co' cl' (rec2IwN_trunc hco').2 (rec2IwN_trunc hcl').2).grow
    (cAs := cts) ?_ hsz hg hk
  show decPL (truncM m) (decCN (truncM m)) _ _ = some cts
  rw [UInt64.toNat_ofNat_of_lt' hol.1, UInt64.toNat_ofNat_of_lt' hol.2]
  exact hdc

/-- **What the recursor stage needs of the pass's record** (a pending program fact, like
`ConsRecsTFSim` was: to be discharged from the pass's refinement, whose shape copies the input's
recursor slice and parameter count, and whose classes' constructor records are the input members').
From an input shape whose recursor slice lies below the top (`RecsB`), whose members' constructors'
level-parameter slices lie in `EREC` (`ShapeLp`) and whose parameter count is below `2^63`, the
record's shape's recursor slice lies below the top, its classes' constructors' level-parameter
slices lie in `EREC`, and its shape's parameter count is below `2^63`. -/
def PassGrcOK (p : Prog) : Prop :=
  ∀ (n : Nat) (vis p0 isRec : Word) (m m' : Mem) (r : List Word),
    callW p n "check_block_pass" [vis, p0, isRec] m = some (r, m') →
    RecsB m p0 → ShapeLp m p0 → (∀ v, iwN m (p0.toNat + 4) = some v → v < 2 ^ 63) →
    RecsB m' (rdW (m'.arr64 IW) (r.headD 0 + 3)) ∧
    ClassesLp m' (rdW (m'.arr64 IW) (r.headD 0 + 15)) (rdW (m'.arr64 IW) (r.headD 0 + 16)) ∧
    (∀ v, iwN m' ((rdW (m'.arr64 IW) (r.headD 0 + 3)).toNat + 4) = some v → v < 2 ^ 63)

/-- The callees of `check_block` before the tail that keep `target_abs`' memo by their text. -/
def blockTaCallees : List FnName := ["block_raw_rec", "check_block_pass"]

/-- **`check_block`'s model refines `checkBlock`.** -/
theorem icbW_sim {p : Prog} (hP : CbProg p) {fs fs2 : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) {fsR fsT : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (hgp : PassGrcOK p) (n : Nat)
    (hn : 2 ^ 31 + (n + 4) ≤ coreWalkFuel)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    {bO bL p0 : Word} {bs : BlockShape} {block : List IConstantInfo}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m p0.toNat) m bs) (hsrc : ShapeSrc m p0)
    (hcx : ShapeCV m p0) (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block)
    (hv : AllVis fe) (hcs : CtorSums fe) (hPm : PosMR m) (hma : ∃ mp, maMR m mp)
    (hta : ∃ mp, taMR m mp) (hrb : RecsB m p0) (hlp : ShapeLp m p0) (hnP : bs.nP < 2 ^ 63)
    (hsz : (m.arr64 IW).size < 2 ^ 63) :
    Sim (icbW p (n + 4) m vis bO bL p0) (ConRon.Arena.checkBlock V fe block ⟨bs⟩) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m') := by
  intro r m' h
  unfold icbW at h
  have hT0 : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, hptr⟩ := partsShapeFacts hq hsrc
  -- the constructors
  cases c1 : callW p (n + 4) "block_shape_all_ctors" [p0] m with
  | none => rw [c1] at h; cases h
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1, icbK1_some] at h
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeAllCtors_spec p hP.ha hP.cp hP.nco hP.acc hP.acg hP.ac (n + 4) _ p0) c1
  simp only at hs1 hW1
  subst hs1
  obtain ⟨cq, tot, rfl, hdc, hg1, hf1, htop1, hroom1⟩ := acW_ok _ _ _ p0 _ bs hW1 hq hS.2.2.2.1 hS.2.2.2.2.2
  have hS1 := stage_frame_iw hS hf1 (by omega)
  have hP1 := hPm.fr (MFr.of_iw hf1)
  obtain ⟨mp0, hmp0⟩ := hma
  have hma1 := maMR_mfr (MFr.of_iw hf1) hmp0
  obtain ⟨tp0, htp0⟩ := hta
  have hta1 : ∃ mp, taMR s1.mem mp := ⟨tp0, taMR_mfr (MFr.of_iw hf1) (by simp) (by simp) htp0⟩
  have hk1 := callW_keepW c1
  simp only [List.headD_cons, List.tail_cons] at h
  have hT1 : iwTop s1.mem < 2 ^ 64 := (rdW (s1.mem.arr64 CTL) 200).toNat_lt
  -- the constructors' names
  have hdc1 : decPL s1.mem (decCN s1.mem) cq.toNat tot.toNat = some bs.allCtors :=
    hdc.get (OMono.decPL (fun q => decCN_mono q) _ _)
  cases c2 : callW p (n + 4) "block_caps_ctor_names" [cq, tot] s1.mem with
  | none => rw [c2] at h; cases h
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [c2, icbK2_some] at h
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (blockCapsCtorNames_spec p hP.ha hP.mnc hP.bccn (n + 4) _ cq tot) c2
  simp only at hs2 hW2
  subst hs2
  have hcsd : decPL (truncM s1.mem) (decCN (truncM s1.mem)) cq.toNat tot.toNat = some bs.allCtors := hdc
  have hlen := decPL_length _ hcsd
  obtain ⟨hr2, hd2, hg2, hf2, ht2⟩ := ctorNamesW_dec hW2 hS1.2.2.2.1 hS1.2.2.2.2.2 (Nat.le_of_eq htop1)
    (bs.allCtors.map (·.1)) (by simp [hlen]) (fun j hj => by
      obtain ⟨v, y, hv, hy, hget⟩ := decPL_get tot.toNat cq.toNat bs.allCtors hcsd j hj
      obtain ⟨⟨a', hva, hcv⟩, -⟩ := decCN_some hy
      obtain ⟨hvlt, hv'⟩ := rec2IwN_trunc hv
      obtain ⟨hvlt2, hva'⟩ := rec2IwN_trunc hva
      have hj' : j < bs.allCtors.length := by omega
      have hy' : bs.allCtors[j] = y := by simpa [List.getElem?_eq_getElem hj'] using hget
      refine ⟨v, a', hv', by omega, hva', ?_⟩
      simp only [List.getElem_map, hy']
      exact DecB.get (f := fun m => decCVp m a') (OMono.decCVp _) hcv)
  have hS2 : StageR dn vis fe s2.mem a := stage_frame_iw hS1 hf2 (by
    have := ctorNamesW_room hW2 hS1.2.2.2.1; simp only [iwTop] at this ht2 ⊢; omega)
  subst hr2
  simp only [List.headD_cons, List.tail_cons, List.map_map] at h hd2
  have hP2 := hP1.fr (MFr.of_iw hf2)
  have hma2 := maMR_mfr (MFr.of_iw hf2) hma1
  have hta2 : ∃ mp, taMR s2.mem mp :=
    let ⟨mp, h⟩ := hta1; ⟨mp, taMR_mfr (MFr.of_iw hf2) (by simp) (by simp) h⟩
  have hk2 := hk1.trans (callW_keepW c2)
  have hg12 := hg1.trans hg2
  have hT2 : iwTop s2.mem < 2 ^ 64 := (rdW (s2.mem.arr64 CTL) 200).toNat_lt
  -- the members' names
  have hq2 := hq.grow (decBS_mono _) hg12
  have hsrc2 := partsHsrc_grow hg12 hq9 hsrc
  obtain ⟨hqd2, hq92, hptr2⟩ := partsShapeFacts hq2 hsrc2
  cases c3 : callW p (n + 4) "block_shape_member_names" [p0] s2.mem with
  | none => rw [c3] at h; cases h
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3, icbK3_some] at h
  obtain ⟨s3, hs3, hr3, hdn3, hg3, hf3, ht3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (blockShapeMemberNames_refines p hP.ha hP.mnc hP.bsmn (n + 4) _ p0 bs hqd2 (by omega) hS2.2.2.2.1
      hS2.2.2.2.2.2 hsrc2 (fun o l j v h1 h2 h3 h4 => Nat.lt_of_succ_lt (hptr2 o l j v h1 h2 h3 h4))) c3
  obtain ⟨s3', hs3', -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (blockShapeMemberNames_spec p hP.ha hP.mnc hP.bsmn (n + 4) _ p0) c3
  have hroom := memberNamesW_room hW3 hS2.2.2.2.1
  rw [partsShapeK hqd2 hq92] at hroom
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hqd2).1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  rw [UInt64.toNat_ofNat_of_lt' hkb] at hroom
  simp only at hs3 hr3 hdn3 hg3 hf3 ht3
  subst hs3
  have hS3 : StageR dn vis fe s3.mem a := stage_frame_iw hS2 hf3 (by
    rw [← ht3]; simp only [iwTop] at hroom ⊢; omega)
  subst hr3
  simp only [List.headD_cons, List.tail_cons] at h
  have hP3 := hP2.fr (MFr.of_iw hf3)
  have hma3 := maMR_mfr (MFr.of_iw hf3) hma2
  have hta3 : ∃ mp, taMR s3.mem mp :=
    let ⟨mp, h⟩ := hta2; ⟨mp, taMR_mfr (MFr.of_iw hf3) (by simp) (by simp) h⟩
  have hk3 := hk2.trans (callW_keepW c3)
  -- the two `sl_nodup`s
  have hcn3 : (decHL s3.mem (rdW (s1.mem.arr64 CTL) 200).toNat tot.toNat : Option (List NIdx)) =
      some (bs.allCtors.map (fun x => x.1.name)) := by
    rw [decHL_grow3 hg3 (by omega), hd2]; rfl
  obtain ⟨wc, hslc, hwc, hwcl⟩ := slR_of_decHL s3.mem _ _ _ hcn3 (by rw [ht2]; exact hT2)
  rw [UInt64.ofNat_toNat, UInt64.ofNat_toNat] at hslc
  obtain ⟨wm, hslm, hwm, hwml⟩ := slR_of_decHL s3.mem _ _ _ hdn3
    (by rw [ht3]; exact (rdW (s3.mem.arr64 CTL) 200).toNat_lt)
  rw [UInt64.ofNat_toNat] at hslm
  cases c4 : callW p (n + 4) "sl_nodup" [rdW (s1.mem.arr64 CTL) 200, tot] s3.mem with
  | none => rw [c4] at h; cases h
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [c4, icbK4_some] at h
  obtain ⟨s4, hs4, -, hm4, hnd1⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (slNodup_refines p hP.slc hP.nodup (n + 4) _ _ _ wc hslc hwcl) c4
  simp only at hs4 hm4 hnd1
  subst hs4
  rw [hm4] at h
  simp only [List.headD_cons, List.tail_cons] at h
  cases c5 : callW p (n + 4) "sl_nodup" [rdW (s2.mem.arr64 CTL) 200, UInt64.ofNat bs.k] s3.mem with
  | none => rw [c5] at h; cases h
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [c5] at h
  obtain ⟨s5, hs5, -, hm5, hnd2⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (slNodup_refines p hP.slc hP.nodup (n + 4) _ _ _ wm hslm hwml) c5
  simp only at hs5 hm5 hnd2
  subst hs5
  rw [← hwc] at hnd1
  rw [← hwm] at hnd2
  by_cases hdup : r4.headD 0 = 0 ∨ r5.headD 0 = 0
  · rw [icbK5_dup (h := hdup)] at h; cases h
  rw [icbK5_ok (h := hdup), hm5] at h
  have hnodup : (!ConRon.Arena.nameNodup (bs.allCtors.map (fun x => x.1.name)) ||
      !ConRon.Arena.nameNodup bs.memberNames) = false := by
    rw [← hnd1, ← hnd2]
    have h1 : r4.headD 0 ≠ 0 := fun e => hdup (.inl e)
    have h2 : r5.headD 0 ≠ 0 := fun e => hdup (.inr e)
    have e1 : (r4.headD 0 != 0) = true := by simpa using h1
    have e2 : (r5.headD 0 != 0) = true := by simpa using h2
    rw [e1, e2]; rfl
  -- the flush
  have hg13 := hg12.trans hg3
  cases c6 : callW p (n + 4) "flush_caches" [] s3.mem with
  | none => rw [c6] at h; cases h
  | some q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [c6, icbK6_some] at h
  obtain ⟨s6, hs6, -, hfok, hfm⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (flushCaches_spec p hP.pass.flush (n + 4) _) c6
  simp only at hs6 hfok hfm
  subst hs6
  obtain ⟨hS6, hg6⟩ := flush_stage hS3 hfok
  have hfr6 : MFr [] [] s3.mem s6.mem := by
    rw [hfm]; exact MFr.of_frame (flushMem_frame s3.mem) (by simp) (by
      intro x hx; left; have := flushCtl_lt x hx; omega)
  rw [← hfm] at hS6 hg6
  have hP6 := hP3.fr hfr6
  have hma6 := maMR_mfr hfr6 hma3
  have hta6 : ∃ mp, taMR s6.mem mp :=
    let ⟨mp, h⟩ := hta3; ⟨mp, taMR_mfr hfr6 (by simp) (by simp) h⟩
  have hk6 := hk3.trans (callW_keepW c6)
  have hg16 := hg13.trans hg6
  -- the raw recursion bit
  have hq6 := hq.grow (decBS_mono _) hg16
  have hsrc6 := partsHsrc_grow hg16 hq9 hsrc
  cases c7 : callW p (n + 4) "block_raw_rec" [p0] s6.mem with
  | none => rw [c7] at h; cases h
  | some q7 =>
  obtain ⟨r7, m7⟩ := q7
  rw [c7, icbK7_some] at h
  obtain ⟨s7, hs7, -, hok7, hst7, hr7, -, hS7, hg7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (blockRawRec_refines p hP.ma hP.ha hP.mnc hP.bsmn hP.pdm hP.brm hP.brg hP.brr (n + 3) _ _ dn vis fe p0 bs
      _ hS6 hq6 hsrc6 hma6) c7
  simp only at hs7 hst7 hr7 hS7 hg7
  subst hs7
  have hP7 := PosMR.ofClosed hcl hfr c7 hP6
  have hrun7 := AM.run_of_ok _ _ hok7
  rw [hst7] at hrun7
  generalize AM.res (ConRon.Arena.blockRawRec ⟨bs⟩) { a with caches := Caches.empty } = raw at hrun7 hr7
  subst hr7
  have hg17 := hg16.trans hg7
  have hta7 := taMR.ofClosed hclT (hfT _ (by decide)) c7 hta6
  have hk7 := hk6.trans (callW_keepW c7)
  -- the pass
  have hq7 := hq.grow (decBS_mono _) hg17
  have hsrc7 := partsHsrc_grow hg17 hq9 hsrc
  have hcx7 := hcx.grow hg17 hq9 hsrc hptr
  cases c8 : callW p (n + 4) "check_block_pass" [vis, p0, [if raw then (1 : Word) else 0].headD 0] s7.mem with
  | none => rw [c8] at h; cases h
  | some q8 =>
  obtain ⟨r8, m8⟩ := q8
  rw [c8, icbK8_some] at h
  obtain ⟨s8, hs8, -, x8, a8, hrun8, hS8, hg8, hBP8, hP8⟩ := triple_of_callW (s₀ := ⟨s7.mem, Locals.init []⟩)
    (checkBlockPass_refines hP.pass hcl hfs n hn _ _ hS7 hq7 hsrc7 hcx7 (b := raw) (by cases raw <;> rfl)
      hv hcs hP7) c8
  simp only at hs8 hS8 hg8 hBP8 hP8
  subst hs8
  have hg18 := hg17.trans hg8
  have hta8 := taMR.ofClosed hclT (hfT _ (by decide)) c8 hta7
  have hk8 := hk7.trans (callW_keepW c8)
  have hq0 : decBS (truncM m) p0.toNat = some bs := hq
  obtain ⟨-, -, hnpw, -⟩ := decBS_some hq0
  obtain ⟨hnpt, hnpm⟩ := rec2IwN_trunc hnpw
  obtain ⟨hrb8, hlp8, hnP8⟩ := hgp (n + 4) vis p0 _ s7.mem s8.mem r8 c8 (hrb.grow hg17 (by omega))
    (hlp.grow hq hsrc hg17 hk7 (by omega))
    (fun v hv => by rw [iwN_grow hg17 hnpt, hnpm] at hv; cases hv; omega)
  -- the tail
  cases c9 : callW p (n + 4) "check_block_tail" [bO, bL, r8.headD 0] s8.mem with
  | none => rw [c9] at h; cases h
  | some q9 =>
  obtain ⟨r9, m9⟩ := q9
  rw [c9, icbK9_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s9, hs9, -, hok9, hS9, hg9, hM9⟩ := triple_of_callW (s₀ := ⟨s8.mem, Locals.init []⟩)
    (checkBlockTail_refines hP.tail hP.cbr hfs2 hcl2 (n + 3) (by omega) hclR hfR _ _ hS8 hBP8
      (hblk.grow (decEBlk_mono _ _ _) hg18) hP8.hbOK ⟨hP8, hta8⟩ hrb8 hlp8 hnP8
      (by rw [hk8 IW]; exact hsz)) c9
  simp only at hs9 hS9 hg9 hM9
  subst hs9
  have hrun9 := AM.run_of_ok _ _ hok9
  refine ⟨_, _, ?_, by simpa using hS9, hg18.trans hg9, hM9⟩
  simp only [ConRon.Arena.checkBlock, hnodup]
  simp only [Bool.false_eq_true, ite_false, StateT.run_bind, flushCaches_run, except_ok_bind, hrun7,
    hrun8, hrun9]

/-- **`check_block(vis, block.off, block.len, p0)` refines `checkBlock`**: from the stage relation,
the block's shape decoded below the tops (`ShapeSrc`, `ShapeCV`), the raw block decoded, an
unrestricted environment whose stored constructors' sums are words, and the walk memos
(`PosMR`, the `mentions_any` memo, `target_abs`' memo) well formed, and what the recursor stage
needs of the input shape (its recursor slice below the top, its members' constructors'
level-parameter slices in `EREC`: `ShapeLp`, its parameter count and the pool's size below
`2^63`): the stage relation at the returned view of the twin's environment, the pools grown, the
`hb` memo kept. Program facts: the lookups (`CbProg`), the write sets (`hcl`, `hcl2`, `hclR`,
`hclT`) and the pending fact `PassGrcOK p` (what the recursor stage needs of the pass's record). -/
@[refines ConRon.Arena.checkBlock]
theorem checkBlock_refines {p : Prog} (hP : CbProg p) {fs fs2 : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) {fsR fsT : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (hgp : PassGrcOK p) (n : Nat)
    (hn : 2 ^ 31 + (n + 4) ≤ coreWalkFuel)
    (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {bO bL p0 : Word} {bs : BlockShape} {block : List IConstantInfo}
    (hS : StageR dn vis fe s₀.mem a₀) (hq : DecB (fun m => decBS m p0.toNat) s₀.mem bs)
    (hsrc : ShapeSrc s₀.mem p0) (hcx : ShapeCV s₀.mem p0)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block) (hv : AllVis fe)
    (hcs : CtorSums fe) (hPm : PosMR s₀.mem) (hma : ∃ mp, maMR s₀.mem mp) (hta : ∃ mp, taMR s₀.mem mp)
    (hrb : RecsB s₀.mem p0) (hlp : ShapeLp s₀.mem p0) (hnP : bs.nP < 2 ^ 63)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 63) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 5)) "check_block" [vis, bO, bL, p0]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlock V fe block ⟨bs⟩) a₀ ∧
      StageR dn (r.headD 0) (AM.res (ConRon.Arena.checkBlock V fe block ⟨bs⟩) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlock V fe block ⟨bs⟩) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ HbMemo s'.mem; ⊤⦄ :=
  triple_post (icb_spec p hP.cb (n + 4) s₀ vis bO bL p0) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (icbW_sim hP hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT hgp n hn hS hq hsrc hcx hblk hv
      hcs hPm hma hta hrb hlp hnP hsz) hm
    ⟨hl, hok, hQ⟩

end L.Ind
