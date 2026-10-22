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

end L.Ind
