import ConAgua.Arena.IndInstallSpec37
import ConAgua.Arena.IndT.KeepC
import ConAgua.Arena.IndT.Pass

/-!
# `checkBlock` under `StageC` (lane `indstaget`)

`check_block`'s model (`icbW_sim`'s proof) from `StageC` at the entry index: the iw-only steps and
the names' checks keep the twin's state; the flush (`ReadOK.flush`: `CheckOK` at the cleared caches)
and the raw recursion bit (core-free, the state kept) before the pass (`checkBlockPass_refinesC`:
`StageC` at the formers' index and what the tail takes), then the tail (`checkBlockTail_refinesC`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p) (hLz : LzcF p)

include hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz in
/-- **`check_block`'s model under `StageC`** (`icbW_sim`'s; twin side con-ron's
`checkBlock_bridge_of`). -/
theorem icbW_simC (hP : CbProg p) {fs fs2 : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) {fsR fsT : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (n : Nat)
    (hn : n + 4 ≤ 2 ^ 62)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    {bO bL p0 : Word} {bs : BlockShape} {block : List IConstantInfo}
    (hC : StageC dn vis fe env m a) (hq : DecB (fun m => decBS m p0.toNat) m bs) (hsrc : ShapeSrc m p0)
    (hcx : ShapeCV m p0) (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block)
    (hPm : PosMR m) (hma : ∃ mp, maMR m mp) (hA : AbsOK m)
    (hkP : ∀ f ∈ passKeepCalleesC, AbsKeep p f) (hkt : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hkr : AbsKeep p "block_raw_rec")
    (hta : ∃ mp, taMR m mp) (hrb : RecsB m p0)
    (hcoh : ConRon.Bridge.IFEnvCoh fe) (hden : ConRon.Bridge.denoteFEnv a.store fe = some env)
    {shP : ConLeche.BlockShape} (hshP : ConRon.Bridge.Inductives.dShape a.store bs = some shP)
    {blockP : List ConLeche.ConstantInfo} (hbP : Frontend.denoteCIList a.store block = some blockP)
    {fsH fsM : List FnName} (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR)
    (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true) (hfH : "check_block_tables" ∈ fsH)
    (hclM : closedA p maFreeA maFreeC fsM = true)
    (hfM : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ fsM)
    (hlpsDn : ∀ ms ∈ bs.members, ∀ k ∈ ms.cvT.levelParams, (dn k).isSome) :
    Sim (icbW p (n + 4) m vis bO bL p0) (ConRon.Arena.checkBlock V fe block ⟨bs⟩) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m' ∧ AbsOK m' ∧ RcMR m' ∧
        ∃ mp, maMR m' mp) := by
  have hS := hC.stage
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
  have hA1 : AbsOK s1.mem := AFr.of_frame hf1 (by decide) (by decide) hA
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
  simp only [List.map_map] at h hd2
  have hP2 := hP1.fr (MFr.of_iw hf2)
  have hma2 := maMR_mfr (MFr.of_iw hf2) hma1
  have hA2 : AbsOK s2.mem := AFr.of_frame hf2 (by decide) (by decide) hA1
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
  have hA3 : AbsOK s3.mem := AFr.of_frame hf3 (by decide) (by decide) hA2
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
  have hA6 : AbsOK s6.mem := by rw [hfm]; exact AFr.of_frame (flushMem_frame s3.mem) (by decide) (by decide) hA3
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
  obtain ⟨s7, hs7, -, hok7, hst7, hr7, hma7, hS7, hg7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (blockRawRec_refines p hP.ma hP.ha hP.mnc hP.bsmn hP.pdm hP.brm hP.brg hP.brr (n + 3) _ _ dn vis fe p0 bs
      _ hS6 hq6 hsrc6 hma6) c7
  simp only at hs7 hst7 hr7 hma7 hS7 hg7
  subst hs7
  have hP7 := PosMR.ofClosed hcl hfr c7 hP6
  have hA7 : AbsOK s7.mem := hkr _ _ _ _ _ c7 hA6
  have hrun7 := AM.run_of_ok _ _ hok7
  rw [hst7] at hrun7
  generalize AM.res (ConRon.Arena.blockRawRec ⟨bs⟩) { a with caches := Caches.empty } = raw at hrun7 hr7
  subst hr7
  have hg17 := hg16.trans hg7
  have hta7 := taMR.ofClosed hclT (hfT _ (by decide)) c7 hta6
  have hk7 := hk6.trans (callW_keepW c7)
  obtain ⟨cf, -, -⟩ := ConRon.Bridge.Inductives.ReadOK.flush (μ := V) hC.check.toR
    (show ConRon.Arena.flushCaches a = .ok ((), { a with caches := Caches.empty }) from rfl)
  have hC7 := StageC.of_parts hS7 cf hA7 hC.mem.dnN
  -- the pass
  have hq7 := hq.grow (decBS_mono _) hg17
  have hsrc7 := partsHsrc_grow hg17 hq9 hsrc
  have hcx7 := hcx.grow hg17 hq9 hsrc hptr
  cases c8 : callW p (n + 4) "check_block_pass" [vis, p0, [if raw then (1 : Word) else 0].headD 0] s7.mem with
  | none => rw [c8] at h; cases h
  | some q8 =>
  obtain ⟨r8, m8⟩ := q8
  rw [c8, icbK8_some] at h
  obtain ⟨s8, hs8, -, x8, a8, hrun8, ⟨hS8, hg8, hBP8, hP8, hA8, hrb8, hlp8⟩, env₁, hC8, qP, i8, hcoh8,
      hden8, henv₁, hqP, hTw, henv₂, hMs⟩ :=
    triple_of_callW (s₀ := ⟨s7.mem, Locals.init []⟩)
    (checkBlockPass_refinesC hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz hP.pass hcl hfs n hn _ _ hC7 hq7 hsrc7 hcx7 (b := raw)
      (by cases raw <;> rfl) hP7 hA7 hkP hcoh hden hshP hlpsDn) c8
  simp only at hs8 hS8 hg8 hBP8 hP8 hA8 hrb8 hlp8 hC8
  subst hs8
  have hma8 := maMR.ofClosed hclM (hfM _ (by simp)) c8 hma7
  have hg18 := hg17.trans hg8
  have hta8 := taMR.ofClosed hclT (hfT _ (by decide)) c8 hta7
  replace hrb8 := hrb8 (hrb.grow hg17 (by omega))
  -- the tail
  cases c9 : callW p (n + 4) "check_block_tail" [bO, bL, r8.headD 0] s8.mem with
  | none => rw [c9] at h; cases h
  | some q9 =>
  obtain ⟨r9, m9⟩ := q9
  rw [c9, icbK9_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s9, hs9, -, hok9, hS9, hg9, hM9, hA9, hR9⟩ := triple_of_callW (s₀ := ⟨s8.mem, Locals.init []⟩)
    (checkBlockTail_refinesC hkp henv₁ hV hOpf hLC hLT hApd hCrk hIlpf hP.tail hP.cbr hfs2 hcl2 (n + 3) (by omega) hclR hfR _ _ hC8
      hBP8 (hblk.grow (decEBlk_mono _ _ _) hg18) hP8.hbOK hA8 hkt ⟨hP8, hta8⟩ hrb8 hlp8 hcoh8 hden8 hqP
      (ConRon.Bridge.denoteCIList_mono i8.ext _ _ hbP) hTw henv₂ hMs hfRc hclH hfH) c9
  simp only at hs9 hS9 hg9 hM9 hA9 hR9
  subst hs9
  have hrun9 := AM.run_of_ok _ _ hok9
  have hma9 := maMR.ofClosed hclM (hfM _ (by simp)) c9 hma8
  refine ⟨_, _, ?_, by simpa using hS9, hg18.trans hg9, hM9, hA9, hR9, hma9⟩
  simp only [ConRon.Arena.checkBlock, hnodup]
  simp only [Bool.false_eq_true, ite_false, StateT.run_bind, flushCaches_run, except_ok_bind, hrun7,
    hrun8, hrun9]

include hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz in
/-- **`check_block(vis, block.off, block.len, p0)` refines `checkBlock` under `StageC`**
(`checkBlock_refines`'s, from `StageC` at the entry index and con-ron's `checkBlock_bridge_of`
preconditions: the environment's coherence and denotation, the shape's and the block's
denotations). -/
@[refines ConRon.Arena.checkBlock]
theorem checkBlock_refinesC (hP : CbProg p) {fs fs2 : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) {fsR fsT : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (n : Nat) (hn : n + 4 ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {bO bL p0 : Word} {bs : BlockShape} {block : List IConstantInfo}
    (hC : StageC dn vis fe env s₀.mem a₀) (hq : DecB (fun m => decBS m p0.toNat) s₀.mem bs)
    (hsrc : ShapeSrc s₀.mem p0) (hcx : ShapeCV s₀.mem p0)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block)
    (hPm : PosMR s₀.mem) (hma : ∃ mp, maMR s₀.mem mp) (hA : AbsOK s₀.mem)
    (hkP : ∀ f ∈ passKeepCalleesC, AbsKeep p f) (hkt : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hkr : AbsKeep p "block_raw_rec") (hta : ∃ mp, taMR s₀.mem mp)
    (hrb : RecsB s₀.mem p0)
    (hcoh : ConRon.Bridge.IFEnvCoh fe) (hden : ConRon.Bridge.denoteFEnv a₀.store fe = some env)
    {shP : ConLeche.BlockShape} (hshP : ConRon.Bridge.Inductives.dShape a₀.store bs = some shP)
    {blockP : List ConLeche.ConstantInfo} (hbP : Frontend.denoteCIList a₀.store block = some blockP)
    {fsH fsM : List FnName} (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR)
    (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true) (hfH : "check_block_tables" ∈ fsH)
    (hclM : closedA p maFreeA maFreeC fsM = true)
    (hfM : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ fsM)
    (hlpsDn : ∀ ms ∈ bs.members, ∀ k ∈ ms.cvT.levelParams, (dn k).isSome) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 5)) "check_block" [vis, bO, bL, p0]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlock V fe block ⟨bs⟩) a₀ ∧
      StageR dn (r.headD 0) (AM.res (ConRon.Arena.checkBlock V fe block ⟨bs⟩) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlock V fe block ⟨bs⟩) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ HbMemo s'.mem ∧ AbsOK s'.mem ∧ RcMR s'.mem ∧ (∃ mp, maMR s'.mem mp); ⊤⦄ :=
  triple_post (icb_spec p hP.cb (n + 4) s₀ vis bO bL p0) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (icbW_simC hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz hP hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT n hn hC hq
      hsrc hcx hblk hPm hma hA hkP hkt hkr hta hrb hcoh hden hshP hbP hfRc hclH hfH hclM hfM hlpsDn) hm
    ⟨hl, hok, hQ⟩

end sims

end L.Ind
