import ConAgua.Arena.IndInstallSpec5

/-!
# Refinements of `IndInstall`, part 6 (lane `indproofs2`, helper `parts`): `BlockShape.nestCtx`

The walk's context record (`decCtx`, 11 words) from the shape's projections (`memberNames`,
`lps`, `nIdxs`) and `paramLevels`. The shape record is taken decoded below the tops (`DecB`), its
members' slice below the pool's top (`hsrc`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The memory after `block_shape_nest_ctx`'s eleven writes. -/
def nctxMem (m : Mem) (a b c d e f g h i j k : Word) : Mem :=
  let q := rdW (m.arr64 CTL) 200
  (((((((((((allocMem m 11).set64 IW q a).set64 IW (q + 1) b).set64 IW (q + 2) c).set64 IW (q + 3) d).set64
    IW (q + 4) e).set64 IW (q + 5) f).set64 IW (q + 6) g).set64 IW (q + 7) h).set64 IW (q + 8) i).set64
    IW (q + 9) j).set64 IW (q + 10) k

theorem nctxMem_eq (m : Mem) (a b c d e f g h i j k : Word) :
    nctxMem m a b c d e f g h i j k =
      wrIW (allocMem m 11) (rdW (m.arr64 CTL) 200) [a, b, c, d, e, f, g, h, i, j, k] := by
  simp [nctxMem, wrIW, UInt64.add_assoc]

theorem partsNctx_eq (m : Mem) (a b c d e f g h i j k : Word) :
    (match allocW m 11 with | none => none | some (q, _) => some (q, nctxMem m a b c d e f g h i j k)) =
      posRecW m [a, b, c, d, e, f, g, h, i, j, k] := by
  rw [posRecW_eq m _ 11 rfl, nctxMem_eq]; cases allocW m 11 <;> rfl

/-- After `param_levels`: the record. -/
def nckRec (p fo fl : Word) (r1 r2 r3 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    match allocW m4 11 with
    | none => none
    | some (q, _) => some ([q], nctxMem m4 (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0)
        (rdW (m4.arr64 IW) (p + 4)) (r3.headD 0) (r3.tail.headD 0) fo fl (rdW (m4.arr64 IW) (p + 6)) (r4.headD 0))

/-- **The model of `block_shape_nest_ctx`** (at exec fuel `n + 1`). -/
def nckW (n : Nat) (m : Mem) (p fo fl : Word) : Option (List Word × Mem) :=
  match memberNamesW n m p with
  | none => none
  | some (r1, m1) =>
    match lpsW n m1 p with
    | none => none
    | some (r2, m2) =>
      match nIdxsW n m2 p with
      | none => none
      | some (r3, m3) => nckRec p fo fl r1 r2 r3 (plW n m3 (r2.headD 0) (r2.tail.headD 0))

/-- The lookups of `BlockShape.nestCtx` (and `param_levels`). -/
structure NckProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  slGet : p.lookup "sl_get" = some slGet
  paramFind : p.lookup "param_find" = some paramFind
  paramPush : p.lookup "param_push" = some paramPush
  internParam : p.lookup "intern_param" = some internParam
  plGo : p.lookup "param_levels_go" = some paramLevelsGoL
  pl : p.lookup "param_levels" = some paramLevelsL
  namesCopy : p.lookup "member_names_copy" = some memberNamesCopy
  names : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  nIdxsCopy : p.lookup "n_idxs_copy" = some nIdxsCopy
  nIdxs : p.lookup "block_shape_n_idxs" = some blockShapeNIdxs
  nctx : p.lookup "block_shape_nest_ctx" = some blockShapeNestCtx

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
      plW_spec p hP.alloc hP.copy hP.cons hP.slGet hP.paramFind hP.paramPush hP.internParam hP.plGo hP.pl n,
      iwAlloc_specW p hP.alloc n] <;>
    finish (gen := 20) [nckW, nckRec, nctxMem, allocMem, allocW, rdW_eq]

/-! ## The shape record's members, below the tops -/

/-- What the projections' lemmas ask of a shape record decoded below the tops whose members' slice
lies below the top. -/
theorem partsShapeFacts {m : Mem} {q : Word} {bs : BlockShape}
    (hq : DecB (fun m => decBS m q.toNat) m bs)
    (hsrc : ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l ≤ iwTop m) :
    decBS m q.toNat = some bs ∧ q.toNat + 9 ≤ iwTop m ∧
    (∀ o l j v, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v + 1 < iwTop m) := by
  have hqt : decBS (truncM m) q.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, hpr⟩ := decBS_some hqt
  have hq8 : q.toNat + 8 < iwTop m := by
    simp only [iwB, bool?, Option.map_eq_some_iff] at hpr
    obtain ⟨w, hw, -⟩ := hpr
    exact (truncM_iw_get hw).1
  refine ⟨hq.get (decBS_mono _), by omega, ?_⟩
  obtain ⟨o, l, ho, hl, hdm, -⟩ := partsAt decMS_mono hmem
  have hoN : iwN m q.toNat = some o.toNat := by rw [← iwN_truncM (by omega)]; exact ho
  have hlN : iwN m (q.toNat + 1) = some l.toNat := by rw [← iwN_truncM (by omega)]; exact hl
  intro o' l' j v h1 h2 hj hv
  rw [hoN] at h1; rw [hlN] at h2
  simp only [Option.some.injEq] at h1 h2; subst h1 h2
  obtain ⟨v', hv', hms⟩ := decPL_getH (truncM m) (show decPL _ _ _ _ = _ from hdm) j hj
  have hlt := partsIwLt hv'
  rw [iwN_truncM hlt, hv] at hv'
  simp only [Option.some.injEq] at hv'; subst hv'
  obtain ⟨-, hn, -⟩ := decMS_some hms
  exact partsIwLt hn

theorem nIdxsW_room {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : nIdxsW n m p = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    iwTop m + (rdW (m.arr64 IW) (p + 1)).toNat ≤ (m.arr64 IW).size := by
  unfold nIdxsW at h
  cases hal : allocW m (rdW (m.arr64 IW) (p + 1)) with
  | none => rw [hal] at h; cases h
  | some x =>
    obtain ⟨hq, -, hr⟩ := allocW_facts hal hsz
    simp only [iwTop]; rw [hq] at hr; exact hr

/-- The members' count word of a decoded shape record. -/
theorem partsShapeK {m : Mem} {q : Word} {bs : BlockShape} (hq : decBS m q.toNat = some bs)
    (hb : q.toNat + 9 ≤ iwTop m) : rdW (m.arr64 IW) (q + 1) = UInt64.ofNat bs.k := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have := decBS_k hq (by omega)
  rwa [show UInt64.ofNat (q.toNat + 1) = q + 1 from by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp] at this

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
  cases n with
  | zero => simp [lpsW] at h
  | succ n =>
  by_cases hl0 : l = 0
  · rw [lpsW_nil n m q (by rw [hlw, hl0])] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
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

end L.Ind
