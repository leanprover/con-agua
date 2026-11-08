module

import ConAgua.Arena.RecClassSpec.MkTMWAfr
import ConAgua.Arena.RecClassSpec.Rec2AppendWDec
import ConAgua.Arena.RecClassSpec.Rec2SimTMA
import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.IndPosSpec.InstW
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Arena.RecStab
public import ConAgua.Arena.RecClassSpec.ClassGenMajorCi

@[expose] public section

/-!
# MjW

`rec2DecB_HL_stab`, `rec2SimInstW`, `rec2Major_eq`, `mjtW_sim`, `mjtW_afr`, `mjoW_sim` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem rec2DecB_HL_stab {k : IdxKind} {m m' : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : DecB (fun m => (decHL m o l : Option (List (Idx k)))) m xs) (hg : IWGrow m m') :
    decHL m' o l = some xs :=
  h.stab (OMono.decHL o l) m' hg

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}

/-- `inst_pis_with` on a slice decoded below the tops (possibly empty, at any offset). -/
theorem rec2SimInstW (n : Nat) (hS : StageR vis fe m a) {ao al e : Word} (he : H e) {args : List EIdx}
    (hd : DecB (fun m => (decHL m ao.toNat al.toNat : Option (List EIdx))) m args) :
    RSim (instW n m ao al e) (ConRon.Arena.instPisWith args (decI e)) a (KP dn vis fe m decOE) := by
  sorry

end sims

theorem rec2Major_eq (g : ClassGen) (c d : Nat) : ConRon.Arena.ClassGen.major g c d = (do
    let ci ← ConRon.Arena.targetMajorAt g.cls c
    let fty ← ConRon.Arena.exprGetD g.formerTys c
    match ← ConRon.Arena.instPisWith ci.ds fty with
    | none => pure none
    | some ty => rec2MajOpen ci.ind ci.lvls ci.ds ci.nIdx ty d) := by rfl

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem mjtW_sim (n : Nat) (m : Mem) (a : AState) (ind lvls ds0 dl0 fo fl : Word) (I : NIdx) (U : LsIdx)
    (ds ifs : List EIdx) (hS : StageR vis fe m a) (hI : ind.toNat < 2 ^ 32 ∧ decI ind = I)
    (hU : lvls.toNat < 2 ^ 32 ∧ decI lvls = U)
    (hds : DecB (fun m => (decHL m ds0.toNat dl0.toNat : Option (List EIdx))) m ds)
    (hifs : decHL m fo.toNat fl.toNat = some ifs) (hfb : fo.toNat + fl.toNat ≤ iwTop m) :
    RSim (mjtW n m ind lvls ds0 dl0 fo fl) (rec2MajTail I U ds ifs) a (KP dn vis fe m decOLE) := by
  sorry

theorem mjtW_afr {n : Nat} {m m' : Mem} {ind lvls ds0 dl0 fo fl : Word} {r : List Word}
    (h : mjtW n m ind lvls ds0 dl0 fo fl = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [mjtW] at h
  simp only [mjtW, mjtW.k_intern_const.eq_def, mjtW.k_sl_append.eq_def, mjtW.k_mk_app_n_f.eq_def] at h
  afr_auto h [ceinternW_afr, appendW_afr, mknF_afr]

theorem mjoW_sim (n : Nat) (m : Mem) (a : AState) (ind lvls ds0 dl0 nIdx ty d : Word) (I : NIdx) (U : LsIdx)
    (ds : List EIdx) (hS : StageR vis fe m a) (hI : ind.toNat < 2 ^ 32 ∧ decI ind = I)
    (hU : lvls.toNat < 2 ^ 32 ∧ decI lvls = U)
    (hds : DecB (fun m => (decHL m ds0.toNat dl0.toNat : Option (List EIdx))) m ds) (hty : H ty)
    (hA : AbsOK m) :
    RSim (mjoW n m ind lvls ds0 dl0 nIdx ty d) (rec2MajOpen I U ds nIdx.toNat (decI ty) d.toNat) a
      (fun b a' x => KP dn vis fe m decOLE b a' x ∧ AbsOK b.2) := by
  sorry

end sims

theorem mjW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (g c d : Word) (G : ClassGen) (hS : StageR vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hA : AbsOK m) :
    RSim (mjW n m g c d) (ConRon.Arena.ClassGen.major G c.toNat d.toNat) a
      (fun b a' x => KP dn vis fe m decOLE b a' x ∧ AbsOK b.2) := by
  sorry

/-! ## `class_gen_motive_ty` -/

theorem rec2MapM_classBinder : ∀ xs : List EIdx, xs.mapM ConRon.Arena.classBinder = fvarTypeDs xs
  | [] => rfl
  | x :: xs => by
    simp only [List.mapM_cons, fvarTypeDs, ConRon.Arena.classBinder, rec2MapM_classBinder xs]

/-- The decoded result of an `Option EIdx` producer. -/
theorem motW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (g c d : Word) (G : ClassGen) (hS : StageR vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hA : AbsOK m) :
    RSim (motW n m g c d) (ConRon.Arena.ClassGen.motiveTy G c.toNat d.toNat) a
      (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  sorry

end L.Ind

end
