import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndPartsSpec.PartsSliceCopy
import ConAgua.Arena.IndPartsSpec.PlW

/-!
# NestCtx: `ConRon.Arena.BlockShape.nestCtx`

The refinement theorems `blockShapeNestCtx_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

set_option maxHeartbeats 3200000 in
theorem nck_spec (p : Prog) (hP : NckProg p) (n : Nat) (s₀ : St) (q fo fl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "block_shape_nest_ctx" [q, fo, fl]
    ⦃fun r s' => LocEq s' s₀ ∧ nckW n s₀.mem q fo fl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.nctx]
  simp only [callFn, blockShapeNestCtx]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      blockShapeMemberNames_spec p hP.alloc hP.namesCopy hP.names n,
      blockShapeLps_spec2 p hP.alloc hP.erCopy hP.erToIw hP.lps n,
      blockShapeNIdxs_spec p hP.alloc hP.nIdxsCopy hP.nIdxs n,
      plW_spec p hP.alloc hP.copy hP.cons hP.slGet hP.paramFind hP.paramPush hP.internParam hP.plGo hP.pl hP.il n,
      iwAlloc_specW p hP.alloc n] <;>
    finish (gen := 20) [nckW, nckRec, nctxMem, allocMem, allocW, rdW_eq]

theorem nIdxsW_room {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : nIdxsW n m p = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    iwTop m + (rdW (m.arr64 IW) (p + 1)).toNat ≤ (m.arr64 IW).size := by
  unfold nIdxsW at h
  cases hal : allocW m (rdW (m.arr64 IW) (p + 1)) with
  | none => rw [hal] at h; cases h
  | some x =>
    obtain ⟨hq, -, hr⟩ := allocW_facts hal hsz
    simp only [iwTop]; rw [hq] at hr; exact hr

/-- **`block_shape_lps`, below the tops** (no global bound on the record pool needed). -/
theorem lpsW_ok' {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q : Word} {r : List Word} {bs : BlockShape} (h : lpsW n m q = some (r, m'))
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m q.toNat) m bs) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some bs.lps ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  have hqt : decBS (truncM m) q.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, hpr⟩ := decBS_some hqt
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hq8 : q.toNat + 8 < iwTop m := by
    simp only [iwB, bool?, Option.map_eq_some_iff] at hpr
    obtain ⟨w, hw, -⟩ := hpr
    exact (truncM_iw_get hw).1
  obtain ⟨o, l, ho, hl, hdm, hb⟩ := partsAt decMS_mono hmem
  obtain ⟨how, -, -⟩ := partsIwRd ho rfl
  obtain ⟨hlw, -, -⟩ := partsIwRd hl (show (q + 1).toNat = q.toNat + 1 by rw [UInt64.toNat_add]; simp; omega)
  rw [ofNat_toNat_word] at how hlw
  rcases n with _ | n
  · simp [lpsW] at h
  by_cases hl0 : l = 0
  · rw [lpsW_nil n m q (by rw [hlw, hl0])] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : bs.members = [] := by have := decPL_length _ (show decPL _ _ _ _ = _ from hdm); rw [hl0] at this; simpa using this
    refine ⟨hS, IWGrow.refl _, ?_, by simp⟩
    simp [BlockShape.lps, this, decHL, hslice?]
  rw [lpsW_cons n m q (by rw [hlw]; exact hl0)] at h
  have hPS : PSlR decMS bs.members o l m := ⟨hdm, hb.resolve_left hl0⟩
  obtain ⟨pc, ms0, ms', hms, hw0, hpb, hm0, -⟩ := partsPSl_cons hPS hl0
  obtain ⟨⟨cvp, hcvp, hcv⟩, -, -⟩ := decMS_some (show decMS (truncM m) pc = some ms0 from hm0)
  obtain ⟨hcw, hcvb, -⟩ := partsIwRd hcvp (UInt64.toNat_ofNat_of_lt' hpb)
  rw [how, hw0, hcw] at h
  obtain ⟨hS', hg, hd, ht⟩ := partsLpsCopy h hS (show DecB (fun m => decCVp m cvp) m ms0.cvT from hcv) hcvb
  refine ⟨hS', hg, ?_, Nat.le_of_eq ht⟩
  rw [hd]; simp [BlockShape.lps, hms]

/-- The model of `block_shape_nest_ctx` against `BlockShape.nestCtx` (through `param_levels`' stub
`intern_ls_iw`): the shape record decoded below the tops, its members' slice below the top
(`hsrc`), the parameters' free variables a handle slice below the top; the context record decoded
below the tops. -/
theorem nckW_ok (n : Nat) (s₀ s' : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q fo fl : Word) (bs : BlockShape)
    (fvsP : List EIdx) (hS : StageR dn vis fe s₀.mem a₀) (hq : DecB (fun m => decBS m q.toNat) s₀.mem bs)
    (hsrc : ∀ o l, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l → o + l ≤ iwTop s₀.mem)
    (hf : decHL s₀.mem fo.toNat fl.toNat = some fvsP) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem)
    (r : List Word) (hm : nckW n s₀.mem q fo fl = some (r, s'.mem)) :
    AM.ok (bs.nestCtx fvsP) a₀ ∧
      DecB (fun m => decCtx m (r.headD 0).toNat) s'.mem (AM.res (bs.nestCtx fvsP) a₀) ∧
      StageR dn vis fe s'.mem (AM.st (bs.nestCtx fvsP) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      CtxIn s'.mem (r.headD 0).toNat (· < iwTop s'.mem) ∧ CtxSl s'.mem (r.headD 0).toNat := by
  obtain ⟨hI1, hE1, hsz, hEs, hcl⟩ := hS.2
  have hT : iwTop s₀.mem < 2 ^ 64 := (rdW (s₀.mem.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, hptr1⟩ := partsShapeFacts hq hsrc
  have hptr0 : ∀ o l j v, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l → j < l →
      iwN s₀.mem (o + j) = some v → v < iwTop s₀.mem :=
    fun o l j v h1 h2 h3 h4 => by have := hptr1 o l j v h1 h2 h3 h4; omega
  have hkw := partsShapeK hq' hq9
  have hkb : bs.k < 2 ^ 64 := by
    have : bs.k = (UInt64.ofNat bs.k).toNat := by
      obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hq').1
      have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']
      rw [UInt64.toNat_ofNat_of_lt' this.2]
    rw [this]; exact UInt64.toNat_lt _
  unfold nckW at hm
  -- the member names
  rcases h1 : memberNamesW n s₀.mem q with _ | ⟨r1, m1⟩
  · rw [h1] at hm; cases hm
  rw [h1] at hm; simp only at hm
  obtain ⟨hr1, hd1, hg1, hf1, ht1⟩ := memberNamesW_dec h1 hsz hcl hq' (by omega) hsrc hptr0
  have hS1 : StageR dn vis fe m1 a₀ := stage_frame_iw hS hf1 (by
    have := memberNamesW_room h1 hsz; rw [hkw, UInt64.toNat_ofNat_of_lt' hkb] at this
    simp only [iwTop] at this ht1 ⊢; omega)
  -- the level parameters
  rcases h2 : lpsW n m1 q with _ | ⟨r2, m2⟩
  · rw [h2] at hm; cases hm
  rw [h2] at hm; simp only at hm
  obtain ⟨hS2, hg2, hd2, hb2⟩ := lpsW_ok' h2 hS1 (hq.grow (decBS_mono _) hg1)
  have hg02 := hg1.trans hg2
  -- the index counts
  rcases h3 : nIdxsW n m2 q with _ | ⟨r3, m3⟩
  · rw [h3] at hm; cases hm
  rw [h3] at hm; simp only at hm
  have hqg := hq.grow (decBS_mono _) hg02
  obtain ⟨hq'2, hq92, hptr2⟩ := partsShapeFacts hqg (partsHsrc_grow hg02 hq9 hsrc)
  obtain ⟨hI2, hE2, hsz2, hEs2, hcl2⟩ := hS2.2
  obtain ⟨hr3, hd3, hg3, hf3, ht3⟩ := nIdxsW_dec h3 hsz2 hcl2 hq'2 (by have := hg02.1; omega)
    (partsHsrc_grow hg02 hq9 hsrc) hptr2
  have hkw2 := partsShapeK hq'2 hq92
  have hS3 : StageR dn vis fe m3 a₀ := stage_frame_iw hS2 hf3 (by
    have := nIdxsW_room h3 hsz2; rw [hkw2, UInt64.toNat_ofNat_of_lt' hkb] at this
    simp only [iwTop] at this ht3 ⊢; omega)
  have hg03 := hg02.trans hg3
  -- `param_levels`
  obtain ⟨⟨r4, m4⟩, h4, hm⟩ := of_K hm rfl
  obtain ⟨lv, a4, hrun4, hl4, hle4, hS4, hg4⟩ := plW_sim hS3 (by rw [decHL_grow3 hg3 hb2]; exact hd2)
    (Nat.le_trans hb2 hg3.1) r4 m4 h4
  have hg04 := hg03.trans hg4
  -- the record
  simp only [nckRec] at hm
  have hpr := partsNctx_eq m4 (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0)
    (rdW (m4.arr64 IW) (q + 4)) (r3.headD 0) (r3.tail.headD 0) fo fl (rdW (m4.arr64 IW) (q + 6)) (r4.headD 0)
  rcases h5 : allocW m4 11 with _ | ⟨qq, m5⟩
  · rw [h5] at hm; cases hm
  rw [h5] at hm hpr
  simp only [Option.some.injEq, Prod.mk.injEq] at hm hpr
  obtain ⟨rfl, hm5⟩ := hm
  rw [hm5] at hpr
  obtain ⟨hS6, hg6, htop6, hget⟩ := partsFreshGet hpr.symm hS4 (by simp)
  obtain ⟨hnpw, hnpb, hsl, hse⟩ := partsShapeWords hg04 hq hq9
  have g : ∀ j (hj : j < 11), (iwA (truncM s'.mem))[qq.toNat + j]? = some ([r1.headD 0, r1.tail.headD 0,
      r2.headD 0, r2.tail.headD 0, rdW (m4.arr64 IW) (q + 4), r3.headD 0, r3.tail.headD 0, fo, fl,
      rdW (m4.arr64 IW) (q + 6), r4.headD 0][j]'(by simpa using hj)) := fun j hj => hget j (by simpa using hj)
  have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega); have g3 := g 3 (by omega)
  have g4 := g 4 (by omega); have g5 := g 5 (by omega); have g6 := g 6 (by omega); have g7 := g 7 (by omega)
  have g8 := g 8 (by omega); have g9 := g 9 (by omega); have g10 := g 10 (by omega)
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hrun : (bs.nestCtx fvsP).run a₀ = .ok (⟨bs.memberNames, bs.lps, bs.nP, bs.nIdxs, fvsP, bs.resSort, lv⟩, a4) := by
    simp only [ConRon.Arena.BlockShape.nestCtx, StateT.run_bind, hrun4]; rfl
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  subst hr1 hr3
  simp only [List.length_cons, List.length_nil] at htop6
  have gi : ∀ j (hj : j < 11), iwN s'.mem (qq.toNat + j) = some ([rdW (s₀.mem.arr64 CTL) 200,
      UInt64.ofNat bs.k, r2.headD 0, r2.tail.headD 0, rdW (m4.arr64 IW) (q + 4), rdW (m2.arr64 CTL) 200,
      UInt64.ofNat bs.k, fo, fl, rdW (m4.arr64 IW) (q + 6), r4.headD 0][j]'(by simpa using hj)).toNat := by
    intro j hj
    rw [← iwN_truncM (by omega)]
    simp only [iwN, nat?]; rw [g j hj]; simp
  have hT' : iwTop s'.mem < 2 ^ 64 := (rdW (s'.mem.arr64 CTL) 200).toNat_lt
  have hsl4 : CtxSl s'.mem qq.toNat := by
    intro i hi o l ho hl'
    have hg6' := hg04.trans hg6
    rcases hi with rfl | rfl | rfl | rfl
    · rw [gi 0 (by omega)] at ho; rw [gi 1 (by omega)] at hl'
      simp only [Option.some.injEq, List.getElem_cons_zero, List.getElem_cons_succ] at ho hl'
      subst ho hl'
      rw [UInt64.toNat_ofNat_of_lt' hkb]
      have := (hg2.trans (hg3.trans (hg4.trans hg6))).1; omega
    · rw [gi 2 (by omega)] at ho; rw [gi 3 (by omega)] at hl'
      simp only [Option.some.injEq, List.getElem_cons_zero, List.getElem_cons_succ] at ho hl'
      subst ho hl'
      have := (hg3.trans (hg4.trans hg6)).1; omega
    · rw [gi 5 (by omega)] at ho; rw [gi 6 (by omega)] at hl'
      simp only [Option.some.injEq, List.getElem_cons_zero, List.getElem_cons_succ] at ho hl'
      subst ho hl'
      rw [UInt64.toNat_ofNat_of_lt' hkb]
      have := (hg4.trans hg6).1; omega
    · rw [gi 7 (by omega)] at ho; rw [gi 8 (by omega)] at hl'
      simp only [Option.some.injEq, List.getElem_cons_zero, List.getElem_cons_succ] at ho hl'
      subst ho hl'
      have := hg6'.1; omega
  have hin4 : CtxIn s'.mem qq.toNat (· < iwTop s'.mem) :=
    ⟨fun j hj => by omega, fun i hi o l ho hl' j hj => by have := hsl4 i hi o l ho hl'; omega⟩
  refine ⟨hok, ?_, by rw [hst]; exact hS6, hg04.trans hg6, hin4, hsl4⟩
  rw [hres]
  simp only [List.headD_cons, List.tail_cons] at g0 g1 g5 g6 ⊢
  have hn1 : DecB (fun m => decHL m (rdW (s₀.mem.arr64 CTL) 200).toNat (UInt64.ofNat bs.k).toNat) s'.mem
      bs.memberNames := by
    rw [UInt64.toNat_ofNat_of_lt' hkb]
    exact (decHL_decB hd1 (Nat.le_of_eq ht1)).grow (OMono.decHL _ _) (hg2.trans (hg3.trans (hg4.trans hg6)))
  have hn2 : DecB (fun m => decHL m (r2.headD 0).toNat (r2.tail.headD 0).toNat) s'.mem bs.lps :=
    (decHL_decB hd2 hb2).grow (OMono.decHL _ _) (hg3.trans (hg4.trans hg6))
  have hn3 : DecB (fun m => decNL m (rdW (m2.arr64 CTL) 200).toNat (UInt64.ofNat bs.k).toNat) s'.mem bs.nIdxs := by
    rw [UInt64.toNat_ofNat_of_lt' hkb]
    exact (decNL_decB hd3 (Nat.le_of_eq ht3)).grow (OMono.decNL _ _) (hg4.trans hg6)
  have hn4 : DecB (fun m => decHL m fo.toNat fl.toNat) s'.mem fvsP :=
    (decHL_decB hf hfb).grow (OMono.decHL _ _) (hg04.trans hg6)
  have hl4' : (r4.headD 0).toNat < 2 ^ 32 := hl4
  have hsl' : (rdW (m4.arr64 IW) (q + 6)).toNat < 2 ^ 32 := hsl
  show decCtx (truncM s'.mem) qq.toNat = _
  simp only [decCtx, decAt, iwN, iwH, nat?, hd?, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, Nat.add_assoc,
    Option.map_some, Option.bind_some, bind, pure, hnpw, UInt64.toNat_ofNat_of_lt' hnpb, hl4', hsl', ite_true]
  simp only [show decHL _ _ _ = _ from hn1, show decHL _ _ _ = _ from hn2, show decNL _ _ _ = _ from hn3,
    show decHL _ _ _ = _ from hn4, Option.bind_some, hle4, hse]

/-- **`block_shape_nest_ctx` refines `BlockShape.nestCtx`** (through `param_levels`' stub
`intern_ls_iw`): the shape record decoded below the tops, its members' slice below the top
(`hsrc`), the parameters' free variables a handle slice below the top; the context record decoded
below the tops. -/
@[refines ConRon.Arena.BlockShape.nestCtx]
theorem blockShapeNestCtx_refines (p : Prog) (hP : NckProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q fo fl : Word) (bs : BlockShape)
    (fvsP : List EIdx) (hS : StageR dn vis fe s₀.mem a₀) (hq : DecB (fun m => decBS m q.toNat) s₀.mem bs)
    (hsrc : ∀ o l, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l → o + l ≤ iwTop s₀.mem)
    (hf : decHL s₀.mem fo.toNat fl.toNat = some fvsP) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_shape_nest_ctx" [q, fo, fl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (bs.nestCtx fvsP) a₀ ∧
      DecB (fun m => decCtx m (r.headD 0).toNat) s'.mem (AM.res (bs.nestCtx fvsP) a₀) ∧
      StageR dn vis fe s'.mem (AM.st (bs.nestCtx fvsP) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      CtxIn s'.mem (r.headD 0).toNat (· < iwTop s'.mem) ∧ CtxSl s'.mem (r.headD 0).toNat; ⊤⦄ :=
  triple_post (nck_spec p hP n s₀ q fo fl) fun r s' ⟨hl, hm⟩ =>
    ⟨hl, nckW_ok n s₀ s' a₀ dn vis fe q fo fl bs fvsP hS hq hsrc hf hfb r hm⟩

end L.Ind

end
