import ConAgua.Arena.IndPosSpec.InstW
import ConAgua.Arena.IndPosSpec.PiBWStage
import ConAgua.Arena.RecClassSpec.ClassNPcOf
import ConAgua.Arena.RecGenSpec.DecCIIndCv
import ConAgua.Arena.IndPartsSpec.BlockCounts
import ConAgua.Arena.IlpRd
import ConAgua.Arena.RecCheckSpec.DecHLTruncMBound
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# ToiW

`ToiProg` (the lookups of `target_outside_inst`), `instW_okB`, `ToiR`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `target_outside_inst` -/

/-- The lookups `target_outside_inst` needs. -/
structure ToiProg (p : Prog) : Prop where
  hi1 : I1Prog p
  ix : p.lookup "env_ix" = some envIxL
  rowGet : p.lookup "env_row_get" = some envRowGetL
  find : p.lookup "env_find" = some envFindL
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "er_copy" = some erCopy
  eti : p.lookup "er_to_iw" = some erToIw
  icopy : p.lookup "iw_copy" = some iwCopy
  v : p.lookup "e_view" = some eView
  sc : p.lookup "sl_cons" = some slCons
  pb : p.lookup "pi_binders" = some piBinders
  ipw : p.lookup "inst_pis_with" = some instPisWith
  toi : p.lookup "target_outside_inst" = some targetOutsideInst

/-- `inst_pis_with` from a stable decoding of the arguments. -/
theorem instW_okB {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {n : Nat}
    {m m' : Mem} {a : AState} {ao al e : Word} {args : List EIdx} {r : List Word}
    (h : instW n m ao al e = some (r, m')) (hS : StageR dn vis fe m a) (he : H e)
    (hdec : DecB (fun m => decHL m ao.toNat al.toNat) m args) (hb : ao.toNat + al.toNat < 2 ^ 64) :
    ∃ x a', (ConRon.Arena.instPisWith args (decI e)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decOE m' r x := by
  have hds : decHL m ao.toNat al.toNat = some args :=
    (OMono.decHL ao.toNat al.toNat).mono _ _ _ (IWGrow.refl m).truncExt hdec
  by_cases hl0 : al.toNat = 0
  · cases n with
    | zero => simp [instW] at h
    | succ n =>
    rw [instW_nil (h := UInt64.toNat_inj.mp (by simpa using hl0))] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : args = [] := by rw [hl0] at hds; simpa [decHL, hslice?] using hds.symm
    subst this
    exact ⟨some (decI e), a, rfl, hS, IWGrow.refl _, rfl, he, rfl⟩
  exact instW_ok n dn fe vis m m' a ao al e args r h hS he hds hb (decHL_truncM_bound hdec hl0)

/-- The words `[bsl, x]` of `target_outside_inst` denote the twin's `(index count, sort)`. -/
def ToiR (r : List Word) (x : Nat × LIdx) : Prop :=
  r = [r.headD 0, r.tail.headD 0] ∧ (r.headD 0).toNat = x.1 ∧ (r.tail.headD 0).toNat < 2 ^ 32 ∧
    decI (r.tail.headD 0) = x.2

end L.Ind

end
