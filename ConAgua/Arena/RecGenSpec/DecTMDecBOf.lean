import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndRealNames

/-!
# DecTMDecBOf

`decTM_decB_of`, `tmmK4`, `TmmProg`.
-/

namespace L.Ind

open L.Arena
open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-! ## A fresh `TargetMajor` record, decoded below the tops -/

theorem decTM_decB_of {m : Mem} {q : Nat} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word}
    {ds pfvs : List EIdx} {ctors : List (IConstantVal × Nat)} {nfs : List NestCtorNf}
    (hq : q + 13 ≤ iwTop m)
    (h0 : (m.arr64 IW)[q]? = some a0) (h1 : (m.arr64 IW)[q + 1]? = some a1)
    (h2 : (m.arr64 IW)[q + 2]? = some a2) (h3 : (m.arr64 IW)[q + 3]? = some a3)
    (h4 : (m.arr64 IW)[q + 4]? = some a4) (h5 : (m.arr64 IW)[q + 5]? = some a5)
    (h6 : (m.arr64 IW)[q + 6]? = some a6) (h7 : (m.arr64 IW)[q + 7]? = some a7)
    (h8 : (m.arr64 IW)[q + 8]? = some a8) (h9 : (m.arr64 IW)[q + 9]? = some a9)
    (h10 : (m.arr64 IW)[q + 10]? = some a10) (h11 : (m.arr64 IW)[q + 11]? = some a11)
    (h12 : (m.arr64 IW)[q + 12]? = some a12)
    (hI : a0.toNat < 2 ^ 32) (hu : a1.toNat < 2 ^ 32)
    (hds : DecB (fun m => decHL m a2.toNat a3.toNat) m ds)
    (hct : DecB (fun m => decPL m (decCN m) a6.toNat a7.toNat) m ctors)
    (hnf : DecB (fun m => decPL m (decNCN m) a9.toNat a10.toNat) m nfs)
    (hpf : DecB (fun m => decHL m a11.toNat a12.toNat) m pfvs) :
    DecB (fun m => decTM m q) m
      { ind := decI a0, lvls := decI a1, ds := ds, nPc := a4.toNat, nIdx := a5.toNat,
        ctors := ctors, member := decON a8.toNat, nfs := nfs, pfvs := pfvs } := by
  have t : ∀ j, j < 13 → ∀ a, (m.arr64 IW)[q + j]? = some a → (iwA (truncM m))[q + j]? = some a :=
    fun j hj a h => by rw [truncM_iw_eq (by omega)]; exact h
  have r0 := t 0 (by omega) _ h0; have r1 := t 1 (by omega) _ h1; have r2 := t 2 (by omega) _ h2
  have r3 := t 3 (by omega) _ h3; have r4 := t 4 (by omega) _ h4; have r5 := t 5 (by omega) _ h5
  have r6 := t 6 (by omega) _ h6; have r7 := t 7 (by omega) _ h7; have r8 := t 8 (by omega) _ h8
  have r9 := t 9 (by omega) _ h9; have r10 := t 10 (by omega) _ h10; have r11 := t 11 (by omega) _ h11
  have r12 := t 12 (by omega) _ h12
  have hds' : decHL (truncM m) a2.toNat a3.toNat = some ds := hds
  have hct' : decPL (truncM m) (decCN (truncM m)) a6.toNat a7.toNat = some ctors := hct
  have hnf' : decPL (truncM m) (decNCN (truncM m)) a9.toNat a10.toNat = some nfs := hnf
  have hpf' : decHL (truncM m) a11.toNat a12.toNat = some pfvs := hpf
  show decTM (truncM m) q = _
  simp only [Nat.add_zero] at r0
  simp only [decTM, bind, pure, iwH, hd?, iwN, nat?, decAt]
  simp [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, hI, hu, hds', hct', hnf', hpf']

/-! ## `target_major_of_member` -/

def tmmK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
/-- The lookups of `target_major_of_member`. -/
structure TmmProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  cvl : p.lookup "cv_lps" = some cvLps
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  get : p.lookup "sl_get" = some slGet
  pfind : p.lookup "param_find" = some paramFind
  ppush : p.lookup "param_push" = some paramPush
  iparam : p.lookup "intern_param" = some internParam
  plgo : p.lookup "param_levels_go" = some paramLevelsGoL
  pl : p.lookup "param_levels" = some paramLevelsL
  il : IlF p
  eq : p.lookup "sl_eq" = some slEq
  mkTm : p.lookup "mk_target_major" = some mkTargetMajor
  mem : p.lookup "target_major_of_member" = some targetMajorOfMember

end L.Ind
