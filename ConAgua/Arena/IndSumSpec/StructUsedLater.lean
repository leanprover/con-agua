module

public import ConAgua.Arena.IndSumSpec.Bnums
public import ConAgua.Arena.IndSumSpec.McGoStep
import ConAgua.Arena.IndSumSpec.StructProjArgP
import ConAgua.Arena.RecClassSpec.Classes
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.StripTeleSpec
import all ConAgua.Arena.IndSum

@[expose] public section

/-!
# StructUsedLater: `ConRon.Arena.structUsedLater`

The refinement theorem `structUsedLater_refines` and the lemmas only it uses.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `struct_used_later`: the word model -/

/-- After `strip_pis`: `0` if it failed, else the fresh-memo `has_loose_b_var_b_fast` walk of the body
from index `0`. -/
def ustK1 (n : Nat) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (rs, m1) => if rs.headD 0 = 0 then some (0, m1) else hbFastW n m1 0 (rs.tail.tail.tail.headD 0)

def ustW (n : Nat) (m : Mem) (cty nP j : Word) : Option (Word × Mem) :=
  ustK1 n (stripF 6 m [nP + j + 1, cty])

theorem ustK1_some_zero {n : Nat} {rs : List Word} {m1 : Mem} (h : rs.headD 0 = 0) :
    ustK1 n (some (rs, m1)) = some (0, m1) := by simp only [ustK1, ite_eq_left h]
theorem ustK1_some_ne {n : Nat} {rs : List Word} {m1 : Mem} (h : ¬ rs.headD 0 = 0) :
    ustK1 n (some (rs, m1)) = hbFastW n m1 0 (rs.tail.tail.tail.headD 0) := by simp only [ustK1, ite_eq_right h]
attribute [ind_grind] ustK1_some_zero ustK1_some_ne

section spec
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p) (hst : StripProg p)

include hv hf hput hins hgo hbp hst in
theorem structUsedLater_spec (hcl : p.lookup "hb_clear" = some (memoClearG hbSch))
    (hfast : p.lookup "has_loose_b_var_b_fast" = some hasLooseBVarBFastL)
    (hp : p.lookup "struct_used_later" = some structUsedLaterL)
    (n : Nat) (s₀ : St) (cty nP j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "struct_used_later" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧ ustW n s₀.mem cty nP j = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structUsedLaterL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, stripPis_specF p hst (n + 1),
      hbFast_spec p hv hf hput hins hgo hbp hcl hfast n] <;>
    finish [ustW]

end spec

/-! ## The relation to the twin -/

theorem usDrop3_eq (rs : List Word) : rs.drop 3 = rs.tail.tail.tail := by
  rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> rfl

theorem add3_toNat {nP j : Word} (h : nP.toNat + j.toNat + 1 < 2 ^ 64) :
    (nP + j + 1).toNat = nP.toNat + j.toNat + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_add]; simp; omega

theorem ustW_ok {vis : Word} {fe : IFEnv} (n : Nat)
    (m m' : Mem) (a : AState) (cty nP j r : Word) (mp : Std.HashMap (EIdx × Nat) Bool)
    (hsum : nP.toNat + j.toNat + 1 < 2 ^ 64) (hc : H cty)
    (hS : StageR vis fe m a) (hM : hbMR m mp) (h : ustW n m cty nP j = some (r, m')) :
    ∃ b a', (structUsedLater (decI cty) nP.toNat j.toNat).run a = .ok (b, a') ∧
      r = (if b then 1 else 0) ∧ (∃ mp1, hbMR m' mp1) ∧ StageR vis fe m' a' ∧ IWGrow m m' := by
  simp only [ustW] at h
  obtain ⟨rs, m1, hst, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  obtain ⟨x, a1, hrun, hS1, hg1, hdec⟩ := stripF_pis_ok vis fe (nP + j + 1) cty hc m m1 a rs hst hS
  have hM1 : hbMR m1 mp := memoRV_frame hbSch hbSch_wf lfKey hbVR [IW] [200] (by simp [hbSch, HBM, IW])
    (by simp [hbSch]) m m1 (stripF_frame hst) (fun _ _ h => h) mp hM
  rw [add3_toNat hsum] at hrun
  cases x with
  | none =>
    have hz : rs.headD 0 = 0 := hdec
    rw [ustK1_some_zero hz] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨false, a1, ?_, rfl, ⟨mp, hM1⟩, hS1, hg1⟩
    simp only [structUsedLater, StateT.run_bind]
    rw [hrun]
    rfl
  | some le =>
    obtain ⟨l, e⟩ := le
    obtain ⟨h1, -, hb32, hbe⟩ := hdec
    rw [ustK1_some_ne (by rw [h1]; decide)] at h
    rw [usDrop3_eq] at hb32 hbe
    have hbH : H (rs.tail.tail.tail.headD 0) := hb32
    obtain ⟨b, a', hr2, hb, hM2, hS2, hg2⟩ :=
      hbFastW_ok n m1 m' a1 0 (rs.tail.tail.tail.headD 0) r mp hbH hS1 hM1 h
    refine ⟨b, a', ?_, hb, hM2, hS2, hg1.trans hg2⟩
    rw [show (0 : Word).toNat = 0 from rfl, decE_eq, hbe] at hr2
    simp only [structUsedLater, StateT.run_bind, hrun, except_ok_bind]
    exact hr2

/-! ## The census theorems -/

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p) (hst : StripProg p)

include hv hf hput hins hgo hbp hst in
/-- **`struct_used_later` refines `structUsedLater`** (through `strip_pis`, `bvar_b`): clears the `hb`
memo and walks. -/
@[refines ConRon.Arena.structUsedLater]
theorem structUsedLater_refines (hcl : p.lookup "hb_clear" = some (memoClearG hbSch))
    (hfast : p.lookup "has_loose_b_var_b_fast" = some hasLooseBVarBFastL)
    (hp : p.lookup "struct_used_later" = some structUsedLaterL)
    (n : Nat) (s₀ : St) (a₀ : AState) (fe : IFEnv) (vis cty nP j : Word)
    (mp : Std.HashMap (EIdx × Nat) Bool)
    (hsum : nP.toNat + j.toNat + 1 < 2 ^ 64) (hc : H cty) (hS : StageR vis fe s₀.mem a₀)
    (hM : hbMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "struct_used_later" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (structUsedLater (decI cty) nP.toNat j.toNat) a₀ ∧
      r.headD 0 = (if AM.res (structUsedLater (decI cty) nP.toNat j.toNat) a₀ then 1 else 0) ∧
      (∃ mp1, hbMR s'.mem mp1) ∧
      StageR vis fe s'.mem (AM.st (structUsedLater (decI cty) nP.toNat j.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (structUsedLater_spec p hv hf hput hins hgo hbp hst hcl hfast hp n s₀ cty nP j) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hb, hM', hS', hg⟩ := ustW_ok n _ _ a₀ cty nP j _ mp hsum hc hS hM hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hb, hM', by rw [hst]; exact hS', hg⟩

end census

end L.Ind
end
