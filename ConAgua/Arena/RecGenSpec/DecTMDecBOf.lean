module

public import ConAgua.Arena.IndRealNames
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.IndParts
public import ConAgua.Arena.IndSum
public import ConAgua.Arena.RecCheck
import ConRon.Bridge.Grind

@[expose] public section

/-!
# DecTMDecBOf

`decTM_decB_of`, `TmmProg`.
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
  sorry

/-! ## `target_major_of_member` -/

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
