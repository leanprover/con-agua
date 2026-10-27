import ConAgua.Arena.IndGrindAttr
import ConAgua.Arena.RecGen
import ConAgua.Arena.WhnfBase
import ConAgua.L.Records
import ConAgua.Scan.Common

/-!
# GenRecCheckPrep

`grpG1`, `grpG2`, `grpG2b`, `grpG3`, `grpD`, `grpS3` and the lemmas only they use.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The `ClassGen` record's words 0‥4 (`g` the allocation, the read of `p` at the memory of the
store). -/
def grpG1 (m : Mem) (g pp pO pL m2o m2l : Word) : Mem :=
  ((((m.set64 IW g (rdW (m.arr64 IW) (pp + 4))).set64 IW (g + 1) pO).set64 IW (g + 2) pL).set64 IW
    (g + 3) m2o).set64 IW (g + 4) m2l

/-- Words 5‥7 (the read of `rd` at the memory of the store). -/
def grpG2 (m : Mem) (g fo fl rd : Word) : Mem :=
  ((m.set64 IW (g + 5) fo).set64 IW (g + 6) fl).set64 IW (g + 7)
    (rdW (((m.set64 IW (g + 5) fo).set64 IW (g + 6) fl).arr64 IW) rd)

/-- Words 8‥9. -/
def grpG2b (m : Mem) (g rd co : Word) : Mem :=
  (m.set64 IW (g + 8) (rdW (m.arr64 IW) (rd + 1))).set64 IW (g + 9) co

/-- Words 10‥13. -/
def grpG3 (m : Mem) (g cl el : Word) : Mem :=
  (((m.set64 IW (g + 10) cl).set64 IW (g + 11) el).set64 IW (g + 12) 0).set64 IW (g + 13) 0

/-- `genRecCheckPrep`'s prefix, recursor types and return (a suffix of its body), named for its
spec. -/
-- con-ron: none — `genRecCheckPrep`'s last part (`rfl`), a named block for the proof
def grpD : Stmt := lblk (vis, p, nestedBit, paramsOff, paramsLen, tblOff, tblLen, rd, msOff, msLen, cvTasOff, cvTasLen,
    blockOff, blockLen, r, cvRisOff, cvRisLen, nb, allowed, ftOff, ftLen, ms2Off, ms2Len, ctorsOff, ctorsLen,
    minorOk, ftcOff, ftcLen, elim, g, preOk, preOff, preLen, cvGsOff, cvGsLen) {
  (preOk, preOff, preLen) := call class_gen_prefix_binders(g);
  if preOk == 0 { abort };
  IW.u64[g + 12] := preOff;
  IW.u64[g + 13] := preLen;
  (cvGsOff, cvGsLen) := call class_rec_tys_ok(vis, g, IW.u64[p + 1], IW.u64[p + 2], IW.u64[p + 3],
    cvRisOff, cvRisLen, IW.u64[rd + 2], IW.u64[rd + 3]);
  return (g, cvGsOff, cvGsLen)
}

/-- `genRecCheckPrep`'s last record words and the rest (a suffix of its body), named for its spec. -/
-- con-ron: none — a suffix of `genRecCheckPrep` (`rfl`), a named block for the proof
def grpS3 : Stmt := lblk (vis, p, nestedBit, paramsOff, paramsLen, tblOff, tblLen, rd, msOff, msLen, cvTasOff, cvTasLen,
    blockOff, blockLen, r, cvRisOff, cvRisLen, nb, allowed, ftOff, ftLen, ms2Off, ms2Len, ctorsOff, ctorsLen,
    minorOk, ftcOff, ftcLen, elim, g, preOk, preOff, preLen, cvGsOff, cvGsLen) {
  IW.u64[g + 10] := ctorsLen;
  IW.u64[g + 11] := elim;
  IW.u64[g + 12] := 0;
  IW.u64[g + 13] := 0;
  ⟪grpD⟫
}

/-- `genRecCheckPrep`'s record words 8‥9 and the rest (a suffix of its body), named for its spec. -/
-- con-ron: none — a suffix of `genRecCheckPrep` (`rfl`), a named block for the proof
def grpS2b : Stmt := lblk (vis, p, nestedBit, paramsOff, paramsLen, tblOff, tblLen, rd, msOff, msLen, cvTasOff, cvTasLen,
    blockOff, blockLen, r, cvRisOff, cvRisLen, nb, allowed, ftOff, ftLen, ms2Off, ms2Len, ctorsOff, ctorsLen,
    minorOk, ftcOff, ftcLen, elim, g, preOk, preOff, preLen, cvGsOff, cvGsLen) {
  IW.u64[g + 8] := IW.u64[rd + 1];
  IW.u64[g + 9] := ctorsOff;
  ⟪grpS3⟫
}

/-- `genRecCheckPrep`'s middle record words and the rest (a suffix of its body), named for its spec. -/
-- con-ron: none — a suffix of `genRecCheckPrep` (`rfl`), a named block for the proof
def grpS2 : Stmt := lblk (vis, p, nestedBit, paramsOff, paramsLen, tblOff, tblLen, rd, msOff, msLen, cvTasOff, cvTasLen,
    blockOff, blockLen, r, cvRisOff, cvRisLen, nb, allowed, ftOff, ftLen, ms2Off, ms2Len, ctorsOff, ctorsLen,
    minorOk, ftcOff, ftcLen, elim, g, preOk, preOff, preLen, cvGsOff, cvGsLen) {
  IW.u64[g + 5] := ftcOff;
  IW.u64[g + 6] := ftcLen;
  IW.u64[g + 7] := IW.u64[rd];
  ⟪grpS2b⟫
}

/-- `genRecCheckPrep`'s generator record and the rest (a suffix of its body), named for its spec. -/
-- con-ron: none — `genRecCheckPrep`'s third part (`rfl`), a named block for the proof
def grpC : Stmt := lblk (vis, p, nestedBit, paramsOff, paramsLen, tblOff, tblLen, rd, msOff, msLen, cvTasOff, cvTasLen,
    blockOff, blockLen, r, cvRisOff, cvRisLen, nb, allowed, ftOff, ftLen, ms2Off, ms2Len, ctorsOff, ctorsLen,
    minorOk, ftcOff, ftcLen, elim, g, preOk, preOff, preLen, cvGsOff, cvGsLen) {
  g := call iw_alloc(14);
  IW.u64[g] := IW.u64[p + 4];
  IW.u64[g + 1] := paramsOff;
  IW.u64[g + 2] := paramsLen;
  IW.u64[g + 3] := ms2Off;
  IW.u64[g + 4] := ms2Len;
  ⟪grpS2⟫
}

/-- `genRecCheckPrep`'s classes, constructors, count, formers, level and the rest (a suffix of its
body), named for its spec. -/
-- con-ron: none — `genRecCheckPrep`'s second part (`rfl`), a named block for the proof
def grpB : Stmt := lblk (vis, p, nestedBit, paramsOff, paramsLen, tblOff, tblLen, rd, msOff, msLen, cvTasOff, cvTasLen,
    blockOff, blockLen, r, cvRisOff, cvRisLen, nb, allowed, ftOff, ftLen, ms2Off, ms2Len, ctorsOff, ctorsLen,
    minorOk, ftcOff, ftcLen, elim, g, preOk, preOff, preLen, cvGsOff, cvGsLen) {
  (ftOff, ftLen) := call gen_rec_check_former_tys(cvTasOff, cvTasLen);
  (ms2Off, ms2Len) := call classes_nfs(vis, p, ftOff, ftLen, tblOff, tblLen, msOff, msLen);
  (ctorsOff, ctorsLen) := call classes_ctors(vis, p, ftOff, ftLen, rd, ms2Off, ms2Len);
  minorOk := call gen_rec_check_minor_ok(IW.u64[rd], IW.u64[rd + 1], ctorsOff, ctorsLen);
  if minorOk == 0 { fail R_GENERATED_RECURSOR_THE_RECURSORS_PREFIX };
  (ftcOff, ftcLen) := call gen_rec_check_former_tys_c(vis, cvTasOff, cvTasLen, ms2Off, ms2Len);
  elim := call struct_elim_level(IW.u64[p + 5], IW.u64[p + 7]);
  ⟪grpC⟫
}

/-- `genRecCheckPrep`, its suffixes spliced from `grpB`. -/
-- con-ron: none — `genRecCheckPrep` itself (`rfl`), its suffixes named blocks for the proof
def genRecCheckPrep' : FunDecl := lfn
    (vis, p, nestedBit, paramsOff, paramsLen, tblOff, tblLen, rd, msOff, msLen, cvTasOff, cvTasLen,
     blockOff, blockLen)
    locals
    (r, cvRisOff, cvRisLen, nb, allowed, ftOff, ftLen, ms2Off, ms2Len, ctorsOff, ctorsLen, minorOk,
     ftcOff, ftcLen, elim, g, preOk, preOff, preLen, cvGsOff, cvGsLen) {
  if len(IW.u64) + 5 < 5 { abort };
  if IW.u64[p + 4] + IW.u64[p + 1] < IW.u64[p + 4] { abort };
  if IW.u64[p + 4] + IW.u64[rd + 1] < IW.u64[p + 4] { abort };
  r := call target_rec_pins(p, blockOff, blockLen);
  (cvRisOff, cvRisLen) := call class_stream_recs(vis, IW.u64[p + 2], IW.u64[p + 3]);
  if IW.u64[p + 1] == 0 { fail R_GENERATED_RECURSOR_THE };
  if IW.u64[p + 7] != 0 {
    nb := nestedBit;
    if nb == 0 { nb := call gen_rec_check_any_no_member(msOff, msLen) };
    allowed := call block_large_elim_allowed(p, nb);
    if allowed == 0 { fail R_GENERATED_RECURSOR_LARGE }
  };
  ⟪grpB⟫
}

theorem genRecCheckPrep_eq : genRecCheckPrep = genRecCheckPrep' := rfl

/-! ## The models -/

section model
variable (p : Prog) (n : Nat)

/-- After `block_large_elim_allowed`: the guard. -/
def grpK4 (rest : Mem → Option (List Word × Mem)) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else rest m

/-- After `gen_rec_check_any_no_member`: `block_large_elim_allowed`. -/
def grpK3 (pp : Word) (rest : Mem → Option (List Word × Mem)) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => grpK4 rest (callW p n "block_large_elim_allowed" [pp, r.headD 0] m)

/-- After `class_stream_recs`: the family guard, the elimination guard. -/
def grpK2 (pp nested mO mL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if rdW (m.arr64 IW) (pp + 1) = 0 then none
    else if rdW (m.arr64 IW) (pp + 7) = 0 then some ([r.headD 0, r.tail.headD 0], m)
    else if nested = 0 then
      grpK3 p n pp (fun m => some ([r.headD 0, r.tail.headD 0], m))
        (callW p n "gen_rec_check_any_no_member" [mO, mL] m)
    else
      grpK4 (fun m => some ([r.headD 0, r.tail.headD 0], m))
        (callW p n "block_large_elim_allowed" [pp, nested] m)

/-- After `target_rec_pins`: `class_stream_recs`. -/
def grpK1 (vis pp nested mO mL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => grpK2 p n pp nested mO mL
      (callW p n "class_stream_recs" [vis, rdW (m.arr64 IW) (pp + 2), rdW (m.arr64 IW) (pp + 3)] m)

/-- **The model of the capacity guards, the pins, the stream and the guards**: `cvRis.off,
cvRis.len`. -/
def grpAW (m : Mem) (vis pp nested rd mO mL bO bL : Word) : Option (List Word × Mem) :=
  if m.len64 IW + 5 < 5 then none
  else if rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (pp + 1) < rdW (m.arr64 IW) (pp + 4) then none
  else if rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (rd + 1) < rdW (m.arr64 IW) (pp + 4) then none
  else grpK1 p n vis pp nested mO mL (callW p n "target_rec_pins" [pp, bO, bL] m)

/-- After `class_rec_tys_ok`. -/
def grpC4 (g : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([g, r.headD 0, r.tail.headD 0], m)

/-- The prefix's words stored. -/
def grpPMem (m : Mem) (g o l : Word) : Mem := (m.set64 IW (g + 12) o).set64 IW (g + 13) l

/-- After the prefix: the guard, its words, `class_rec_tys_ok`. -/
def grpC3 (vis pp rd g cRo cRl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then none
    else grpC4 g (callW p n "class_rec_tys_ok" [vis, g,
      rdW ((grpPMem m g (r.tail.headD 0) (r.tail.tail.headD 0)).arr64 IW) (pp + 1),
      rdW ((grpPMem m g (r.tail.headD 0) (r.tail.tail.headD 0)).arr64 IW) (pp + 2),
      rdW ((grpPMem m g (r.tail.headD 0) (r.tail.tail.headD 0)).arr64 IW) (pp + 3), cRo, cRl,
      rdW ((grpPMem m g (r.tail.headD 0) (r.tail.tail.headD 0)).arr64 IW) (rd + 2),
      rdW ((grpPMem m g (r.tail.headD 0) (r.tail.tail.headD 0)).arr64 IW) (rd + 3)]
      (grpPMem m g (r.tail.headD 0) (r.tail.tail.headD 0)))

/-- **The model of `grpD`**: `g, cvGs.off, cvGs.len`. -/
def grpDW (m : Mem) (vis pp rd g cRo cRl : Word) : Option (List Word × Mem) :=
  grpC3 p n vis pp rd g cRo cRl (callW p n "class_gen_prefix_binders" [g] m)

/-- **The model of `grpC3`**. -/
def grpC3W (m : Mem) (vis pp rd g cRo cRl cl el : Word) : Option (List Word × Mem) :=
  grpDW p n (grpG3 m g cl el) vis pp rd g cRo cRl

/-- **The model of `grpS2b`**. -/
def grpC2bW (m : Mem) (vis pp rd g cRo cRl co cl el : Word) : Option (List Word × Mem) :=
  grpC3W p n (grpG2b m g rd co) vis pp rd g cRo cRl cl el

/-- **The model of `grpS2`**. -/
def grpC2W (m : Mem) (vis pp rd g cRo cRl fo fl co cl el : Word) : Option (List Word × Mem) :=
  grpC2bW p n (grpG2 m g fo fl rd) vis pp rd g cRo cRl co cl el

/-- After `iw_alloc(14)`: the record, the rest. -/
def grpC1 (vis pp pO pL rd cRo cRl m2o m2l fo fl co cl el : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    grpC2W p n (grpG1 m (r.headD 0) pp pO pL m2o m2l) vis pp rd (r.headD 0) cRo cRl fo fl co cl el

/-- **The model of `grpC`**: `g, cvGs.off, cvGs.len`. -/
def grpCW (m : Mem) (vis pp pO pL rd cRo cRl m2o m2l fo fl co cl el : Word) : Option (List Word × Mem) :=
  grpC1 p n vis pp pO pL rd cRo cRl m2o m2l fo fl co cl el (callW p n "iw_alloc" [14] m)

/-- After `struct_elim_level`: the rest. -/
def grpB6 (vis pp pO pL rd cRo cRl m2o m2l fo fl co cl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => grpCW p n m vis pp pO pL rd cRo cRl m2o m2l fo fl co cl (r.headD 0)

/-- After the classes' formers: `struct_elim_level`. -/
def grpB5 (vis pp pO pL rd cRo cRl m2o m2l co cl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => grpB6 p n vis pp pO pL rd cRo cRl m2o m2l (r.headD 0) (r.tail.headD 0) co cl
      (callW p n "struct_elim_level" [rdW (m.arr64 IW) (pp + 5), rdW (m.arr64 IW) (pp + 7)] m)

/-- After the count: the guard, the classes' formers. -/
def grpB4 (vis pp pO pL rd cO cL cRo cRl m2o m2l co cl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then none
    else grpB5 p n vis pp pO pL rd cRo cRl m2o m2l co cl
      (callW p n "gen_rec_check_former_tys_c" [vis, cO, cL, m2o, m2l] m)

/-- After `classes_ctors`: the count. -/
def grpB3 (vis pp pO pL rd cO cL cRo cRl m2o m2l : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => grpB4 p n vis pp pO pL rd cO cL cRo cRl m2o m2l (r.headD 0) (r.tail.headD 0)
      (callW p n "gen_rec_check_minor_ok" [rdW (m.arr64 IW) rd, rdW (m.arr64 IW) (rd + 1), r.headD 0,
        r.tail.headD 0] m)

/-- After `classes_nfs`: `classes_ctors`. -/
def grpB2 (vis pp pO pL rd cO cL cRo cRl fo fl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => grpB3 p n vis pp pO pL rd cO cL cRo cRl (r.headD 0) (r.tail.headD 0)
      (callW p n "classes_ctors" [vis, pp, fo, fl, rd, r.headD 0, r.tail.headD 0] m)

/-- After the formers' types: `classes_nfs`. -/
def grpB1 (vis pp pO pL tO tL rd mO mL cO cL cRo cRl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => grpB2 p n vis pp pO pL rd cO cL cRo cRl (r.headD 0) (r.tail.headD 0)
      (callW p n "classes_nfs" [vis, pp, r.headD 0, r.tail.headD 0, tO, tL, mO, mL] m)

/-- **The model of `grpB`**: `g, cvGs.off, cvGs.len`. -/
def grpBW (m : Mem) (vis pp pO pL tO tL rd mO mL cO cL cRo cRl : Word) : Option (List Word × Mem) :=
  grpB1 p n vis pp pO pL tO tL rd mO mL cO cL cRo cRl (callW p n "gen_rec_check_former_tys" [cO, cL] m)

/-- After the guards: the rest. -/
def grpKA (vis pp pO pL tO tL rd mO mL cO cL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, ma) => grpBW p n ma vis pp pO pL tO tL rd mO mL cO cL (ra.headD 0) (ra.tail.headD 0)

/-- **The model of `gen_rec_check_prep`** (body fuel `n`). -/
def grpW (m : Mem) (vis pp nested pO pL tO tL rd mO mL cO cL bO bL : Word) : Option (List Word × Mem) :=
  grpKA p n vis pp pO pL tO tL rd mO mL cO cL (grpAW p n m vis pp nested rd mO mL bO bL)

end model

section arms
variable (p : Prog) (n : Nat) (m : Mem) (r : List Word) (rest : Mem → Option (List Word × Mem))
  (vis pp nested pO pL tO tL rd mO mL cO cL cRo cRl fo fl m2o m2l co cl el g : Word)
theorem grpK4_bad (h : r.headD 0 = 0) : grpK4 rest (some (r, m)) = none := by simp only [grpK4]; rw [ite_eq_left h]
theorem grpK4_ok (h : r.headD 0 ≠ 0) : grpK4 rest (some (r, m)) = rest m := by simp only [grpK4]; rw [ite_eq_right h]
theorem grpK3_some : grpK3 p n pp rest (some (r, m)) =
    grpK4 rest (callW p n "block_large_elim_allowed" [pp, r.headD 0] m) := rfl
theorem grpK2_fam (h : rdW (m.arr64 IW) (pp + 1) = 0) :
    grpK2 p n pp nested mO mL (some (r, m)) = none := by simp [grpK2, h]
theorem grpK2_small (h1 : rdW (m.arr64 IW) (pp + 1) ≠ 0) (h : rdW (m.arr64 IW) (pp + 7) = 0) :
    grpK2 p n pp nested mO mL (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := by
  simp [grpK2, h1, h]
theorem grpK2_any (h1 : rdW (m.arr64 IW) (pp + 1) ≠ 0) (h : rdW (m.arr64 IW) (pp + 7) ≠ 0)
    (hn : nested = 0) :
    grpK2 p n pp nested mO mL (some (r, m)) =
      grpK3 p n pp (fun m => some ([r.headD 0, r.tail.headD 0], m))
        (callW p n "gen_rec_check_any_no_member" [mO, mL] m) := by
  simp [grpK2, h1, h, hn]
theorem grpK2_nested (h1 : rdW (m.arr64 IW) (pp + 1) ≠ 0) (h : rdW (m.arr64 IW) (pp + 7) ≠ 0)
    (hn : nested ≠ 0) :
    grpK2 p n pp nested mO mL (some (r, m)) =
      grpK4 (fun m => some ([r.headD 0, r.tail.headD 0], m))
        (callW p n "block_large_elim_allowed" [pp, nested] m) := by
  simp [grpK2, h1, h, hn]
theorem grpK1_some : grpK1 p n vis pp nested mO mL (some (r, m)) =
    grpK2 p n pp nested mO mL
      (callW p n "class_stream_recs" [vis, rdW (m.arr64 IW) (pp + 2), rdW (m.arr64 IW) (pp + 3)] m) := rfl
theorem grpC4_some : grpC4 g (some (r, m)) = some ([g, r.headD 0, r.tail.headD 0], m) := rfl
theorem grpC3_bad (h : r.headD 0 = 0) : grpC3 p n vis pp rd g cRo cRl (some (r, m)) = none := by
  simp only [grpC3]; rw [ite_eq_left h]
theorem grpC3_ok (h : r.headD 0 ≠ 0) : grpC3 p n vis pp rd g cRo cRl (some (r, m)) =
    grpC4 g (callW p n "class_rec_tys_ok" [vis, g,
      rdW ((grpPMem m g (r.tail.headD 0) (r.tail.tail.headD 0)).arr64 IW) (pp + 1),
      rdW ((grpPMem m g (r.tail.headD 0) (r.tail.tail.headD 0)).arr64 IW) (pp + 2),
      rdW ((grpPMem m g (r.tail.headD 0) (r.tail.tail.headD 0)).arr64 IW) (pp + 3), cRo, cRl,
      rdW ((grpPMem m g (r.tail.headD 0) (r.tail.tail.headD 0)).arr64 IW) (rd + 2),
      rdW ((grpPMem m g (r.tail.headD 0) (r.tail.tail.headD 0)).arr64 IW) (rd + 3)]
      (grpPMem m g (r.tail.headD 0) (r.tail.tail.headD 0))) := by
  simp only [grpC3]; rw [ite_eq_right h]
theorem grpC1_some : grpC1 p n vis pp pO pL rd cRo cRl m2o m2l fo fl co cl el (some (r, m)) =
    grpC2W p n (grpG1 m (r.headD 0) pp pO pL m2o m2l) vis pp rd (r.headD 0) cRo cRl fo fl co cl el := rfl
theorem grpB6_some : grpB6 p n vis pp pO pL rd cRo cRl m2o m2l fo fl co cl (some (r, m)) =
    grpCW p n m vis pp pO pL rd cRo cRl m2o m2l fo fl co cl (r.headD 0) := rfl
theorem grpB5_some : grpB5 p n vis pp pO pL rd cRo cRl m2o m2l co cl (some (r, m)) =
    grpB6 p n vis pp pO pL rd cRo cRl m2o m2l (r.headD 0) (r.tail.headD 0) co cl
      (callW p n "struct_elim_level" [rdW (m.arr64 IW) (pp + 5), rdW (m.arr64 IW) (pp + 7)] m) := rfl
theorem grpB4_bad (h : r.headD 0 = 0) :
    grpB4 p n vis pp pO pL rd cO cL cRo cRl m2o m2l co cl (some (r, m)) = none := by
  simp only [grpB4]; rw [ite_eq_left h]
theorem grpB4_ok (h : r.headD 0 ≠ 0) : grpB4 p n vis pp pO pL rd cO cL cRo cRl m2o m2l co cl (some (r, m)) =
    grpB5 p n vis pp pO pL rd cRo cRl m2o m2l co cl
      (callW p n "gen_rec_check_former_tys_c" [vis, cO, cL, m2o, m2l] m) := by
  simp only [grpB4]; rw [ite_eq_right h]
theorem grpB3_some : grpB3 p n vis pp pO pL rd cO cL cRo cRl m2o m2l (some (r, m)) =
    grpB4 p n vis pp pO pL rd cO cL cRo cRl m2o m2l (r.headD 0) (r.tail.headD 0)
      (callW p n "gen_rec_check_minor_ok" [rdW (m.arr64 IW) rd, rdW (m.arr64 IW) (rd + 1), r.headD 0,
        r.tail.headD 0] m) := rfl
theorem grpB2_some : grpB2 p n vis pp pO pL rd cO cL cRo cRl fo fl (some (r, m)) =
    grpB3 p n vis pp pO pL rd cO cL cRo cRl (r.headD 0) (r.tail.headD 0)
      (callW p n "classes_ctors" [vis, pp, fo, fl, rd, r.headD 0, r.tail.headD 0] m) := rfl
theorem grpB1_some : grpB1 p n vis pp pO pL tO tL rd mO mL cO cL cRo cRl (some (r, m)) =
    grpB2 p n vis pp pO pL rd cO cL cRo cRl (r.headD 0) (r.tail.headD 0)
      (callW p n "classes_nfs" [vis, pp, r.headD 0, r.tail.headD 0, tO, tL, mO, mL] m) := rfl
theorem grpKA_some : grpKA p n vis pp pO pL tO tL rd mO mL cO cL (some (r, m)) =
    grpBW p n m vis pp pO pL tO tL rd mO mL cO cL (r.headD 0) (r.tail.headD 0) := rfl
end arms

attribute [ind_grind] grpK4_bad grpK4_ok grpK3_some grpK2_fam grpK2_small grpK2_any grpK2_nested
  grpK1_some grpB6_some grpB5_some grpB4_bad grpB4_ok grpB3_some grpB2_some grpB1_some grpC4_some
  grpC3_bad grpC3_ok grpC1_some grpKA_some

/-! ## The `vcgen` specs -/

set_option maxHeartbeats 1600000 in
theorem grpD_spec (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p (f + 1) grpD
    ⦃fun r s' => r = .ret [s'.loc 29, s'.loc 33, s'.loc 34] ∧
      grpDW p f s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 7) (s₀.loc 29) (s₀.loc 15) (s₀.loc 16) =
        some ([s'.loc 29, s'.loc 33, s'.loc 34], s'.mem); ⊤⦄ := by
  rw [exec]
  simp only [grpD, L.Notation.blk]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p f "class_gen_prefix_binders", callW_spec p f "class_rec_tys_ok"] <;>
    finish (gen := 40) (instances := 20000) [grpDW, grpPMem, rdW_eq]

set_option maxHeartbeats 1600000 in
theorem grpS3_spec (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p (f + 1) grpS3
    ⦃fun r s' => r = .ret [s'.loc 29, s'.loc 33, s'.loc 34] ∧
      grpC3W p f s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 7) (s₀.loc 29) (s₀.loc 15) (s₀.loc 16) (s₀.loc 24)
        (s₀.loc 28) = some ([s'.loc 29, s'.loc 33, s'.loc 34], s'.mem); ⊤⦄ := by
  rw [exec]
  simp only [grpS3, L.Notation.blk]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      fun s => Triple.step_exec (grpD_spec p f s)] <;>
    finish (gen := 40) (instances := 20000) [grpC3W, grpG3]

set_option maxHeartbeats 1600000 in
theorem grpS2b_spec (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p (f + 1) grpS2b
    ⦃fun r s' => r = .ret [s'.loc 29, s'.loc 33, s'.loc 34] ∧
      grpC2bW p f s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 7) (s₀.loc 29) (s₀.loc 15) (s₀.loc 16)
        (s₀.loc 23) (s₀.loc 24) (s₀.loc 28) = some ([s'.loc 29, s'.loc 33, s'.loc 34], s'.mem); ⊤⦄ := by
  rw [exec]
  simp only [grpS2b, L.Notation.blk]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      fun s => Triple.step_exec (grpS3_spec p f s)] <;>
    finish (gen := 40) (instances := 20000) [grpC2bW, grpG2b, rdW_eq]

set_option maxHeartbeats 1600000 in
theorem grpS2_spec (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p (f + 1) grpS2
    ⦃fun r s' => r = .ret [s'.loc 29, s'.loc 33, s'.loc 34] ∧
      grpC2W p f s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 7) (s₀.loc 29) (s₀.loc 15) (s₀.loc 16) (s₀.loc 26)
        (s₀.loc 27) (s₀.loc 23) (s₀.loc 24) (s₀.loc 28) = some ([s'.loc 29, s'.loc 33, s'.loc 34], s'.mem); ⊤⦄ := by
  rw [exec]
  simp only [grpS2, L.Notation.blk]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      fun s => Triple.step_exec (grpS2b_spec p f s)] <;>
    finish (gen := 40) (instances := 20000) [grpC2W, grpG2, rdW_eq]

set_option maxHeartbeats 1600000 in
theorem grpC_spec (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p (f + 1) grpC
    ⦃fun r s' => r = .ret [s'.loc 29, s'.loc 33, s'.loc 34] ∧
      grpCW p f s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 3) (s₀.loc 4) (s₀.loc 7) (s₀.loc 15) (s₀.loc 16)
        (s₀.loc 21) (s₀.loc 22) (s₀.loc 26) (s₀.loc 27) (s₀.loc 23) (s₀.loc 24) (s₀.loc 28) =
        some ([s'.loc 29, s'.loc 33, s'.loc 34], s'.mem); ⊤⦄ := by
  rw [exec]
  simp only [grpC, L.Notation.blk]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, callW_spec p f "iw_alloc",
      fun s => Triple.step_exec (grpS2_spec p f s)] <;>
    finish (gen := 40) (instances := 20000) [grpCW, grpG1, rdW_eq]

set_option maxHeartbeats 1600000 in
theorem grpB_spec (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p (f + 1) grpB
    ⦃fun r s' => r = .ret [s'.loc 29, s'.loc 33, s'.loc 34] ∧
      grpBW p f s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7)
        (s₀.loc 8) (s₀.loc 9) (s₀.loc 10) (s₀.loc 11) (s₀.loc 15) (s₀.loc 16) =
        some ([s'.loc 29, s'.loc 33, s'.loc 34], s'.mem); ⊤⦄ := by
  rw [exec]
  simp only [grpB, L.Notation.blk]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p f "gen_rec_check_former_tys", callW_spec p f "classes_nfs",
      callW_spec p f "classes_ctors", callW_spec p f "gen_rec_check_minor_ok",
      callW_spec p f "gen_rec_check_former_tys_c", callW_spec p f "struct_elim_level",
      fun s => Triple.step_exec (grpC_spec p f s)] <;>
    finish (gen := 40) (instances := 20000) [grpBW, rdW_eq]

set_option maxHeartbeats 1600000 in
theorem grp_spec (p : Prog) (hp : p.lookup "gen_rec_check_prep" = some genRecCheckPrep) (n : Nat)
    (s₀ : St) (vis pp nested pO pL tO tL rd mO mL cO cL bO bL : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "gen_rec_check_prep"
      [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL]
    ⦃fun r s' => LocEq s' s₀ ∧
      grpW p n s₀.mem vis pp nested pO pL tO tL rd mO mL cO cL bO bL = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp, genRecCheckPrep_eq]
  simp only [callFn, genRecCheckPrep']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "target_rec_pins", callW_spec p n "class_stream_recs",
      callW_spec p n "gen_rec_check_any_no_member", callW_spec p n "block_large_elim_allowed",
      fun s => Triple.step_exec (grpB_spec p n s)] <;>
    finish (gen := 40) (instances := 20000) [grpW, grpAW, rdW_eq]

end L.Ind
