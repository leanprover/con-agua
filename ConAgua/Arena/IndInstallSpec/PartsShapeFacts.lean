import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndSumSpec.ColW

/-!
# PartsShapeFacts

`nctxMem`, `nctxMem_eq`, `partsNctx_eq`, `nckRec`, `nckW`, `NckProg` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

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
  il : IlF p
  namesCopy : p.lookup "member_names_copy" = some memberNamesCopy
  names : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  nIdxsCopy : p.lookup "n_idxs_copy" = some nIdxsCopy
  nIdxs : p.lookup "block_shape_n_idxs" = some blockShapeNIdxs
  nctx : p.lookup "block_shape_nest_ctx" = some blockShapeNestCtx

/-! ## The shape record's members, below the tops -/

/-- What the projections' lemmas ask of a shape record decoded below the tops whose members' slice
lies below the top. -/
theorem partsShapeFacts {m : Mem} {q : Word} {bs : BlockShape}
    (hq : DecB (fun m => decBS m q.toNat) m bs)
    (_hsrc : ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l ≤ iwTop m) :
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

/-- The members' count word of a decoded shape record. -/
theorem partsShapeK {m : Mem} {q : Word} {bs : BlockShape} (hq : decBS m q.toNat = some bs)
    (hb : q.toNat + 9 ≤ iwTop m) : rdW (m.arr64 IW) (q + 1) = UInt64.ofNat bs.k := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have := decBS_k hq (by omega)
  rwa [show UInt64.ofNat (q.toNat + 1) = q + 1 from by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp] at this

theorem partsHsrc_grow {m m' : Mem} (hg : IWGrow m m') {q : Word} (hq9 : q.toNat + 9 ≤ iwTop m)
    (hsrc : ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l ≤ iwTop m) :
    ∀ o l, iwN m' q.toNat = some o → iwN m' (q.toNat + 1) = some l → o + l ≤ iwTop m' := by
  intro o l h1 h2
  have e1 : iwN m' q.toNat = iwN m q.toNat := by simp only [iwN, nat?, iwA]; rw [hg.2.2.1 _ (by omega)]
  have e2 : iwN m' (q.toNat + 1) = iwN m (q.toNat + 1) := by simp only [iwN, nat?, iwA]; rw [hg.2.2.1 _ (by omega)]
  rw [e1] at h1; rw [e2] at h2
  exact Nat.le_trans (hsrc o l h1 h2) hg.1

/-- The record's words read off a decoded shape (`nP`, `resSort`), in a grown memory. -/
theorem partsShapeWords {m m' : Mem} (hg : IWGrow m m') {q : Word} {bs : BlockShape}
    (hq : DecB (fun m => decBS m q.toNat) m bs) (hq9 : q.toNat + 9 ≤ iwTop m) :
    rdW (m'.arr64 IW) (q + 4) = UInt64.ofNat bs.nP ∧ bs.nP < 2 ^ 64 ∧
      H (rdW (m'.arr64 IW) (q + 6)) ∧ decI (rdW (m'.arr64 IW) (q + 6)) = bs.resSort := by
  have hqt : decBS (truncM m) q.toNat = some bs := hq
  obtain ⟨-, -, hnp, -, hsort, -, -⟩ := decBS_some hqt
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have h4 : (q + 4).toNat = q.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have h6 : (q + 6).toNat = q.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hw4, hnb, -⟩ := partsIwRd hnp h4
  rw [partsRdIW_grow hg (by omega)]
  refine ⟨hw4, hnb, ?_⟩
  obtain ⟨w, hw, hwl, hwe⟩ := hd?_some (show hd? (iwA (truncM m)) (q.toNat + 6) = some bs.resSort from hsort)
  obtain ⟨-, hw'⟩ := truncM_iw_get hw
  simp only [iwA] at hw'
  rw [partsRdIW_grow hg (by omega), rdW_of_get? h6.symm hw']
  exact ⟨hwl, hwe.symm⟩

end L.Ind

end
