module

public import ConAgua.Arena.RecCheckSpec.RpLook
import ConAgua.Arena.IndPartsSpec.AllCtors
import ConAgua.Arena.IndPartsSpec.BlockSplitRecs
import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
public import ConAgua.Arena.IndGrindAttr
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.EqW
import ConAgua.Arena.IndPartsSpec.RecTW
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved

@[expose] public section

/-!
# TpsW

`decCN_cv`, `decCN_lt`, `decSC_cv`, `decSC_lt`, `tpsK4`, `tpsK3` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Records whose word `0` is a constant pointer -/

theorem decCN_cv (m : Mem) (pp : Nat) (x : IConstantVal × Nat) (h : decCN m pp = some x) :
    ∃ a, iwN m pp = some a ∧ decCVp m a = some x.1 := (decCN_some h).1

theorem decCN_lt (m : Mem) (pp : Nat) (x : IConstantVal × Nat) (h : decCN (truncM m) pp = some x) :
    pp < iwTop m := by
  obtain ⟨⟨a, ha, -⟩, -⟩ := decCN_some h; exact partsIwLt ha

theorem decSC_cv (m : Mem) (pp : Nat) (x : IConstantVal × Nat × Nat) (h : decSC m pp = some x) :
    ∃ a, iwN m pp = some a ∧ decCVp m a = some x.1 := by
  unfold decSC at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, c, -, d, -, he⟩ := h
  subst he; exact ⟨a, ha, hb⟩

theorem decSC_lt (m : Mem) (pp : Nat) (x : IConstantVal × Nat × Nat) (h : decSC (truncM m) pp = some x) :
    pp < iwTop m := by
  obtain ⟨a, ha, -⟩ := decSC_cv _ _ _ h; exact partsIwLt ha

/-! ## `target_rec_pins_split` -/

def tpsK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
def tpsK3 (p : Prog) (n : Nat) (ra : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m) => tpsK4 (callW p n "sl_eq" [ra.headD 0, ra.tail.headD 0, rc.headD 0, rc.tail.headD 0] m)
def tpsK2 (p : Prog) (n : Nat) (cso csl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m) => tpsK3 p n ra (callW p n "ptr_list_names" [cso, csl] m)
def tpsK1 (p : Prog) (n : Nat) (cso csl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rac, m) => tpsK2 p n cso csl (callW p n "ptr_list_names" [rac.headD 0, rac.tail.headD 0] m)
def tpsK0 (p : Prog) (n : Nat) (pp k recl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs, m) =>
    if rs.headD 0 = 0 then some ([0], m)
    else if rdW (m.arr64 IW) (rs.tail.headD 0 + 1) ≠ k then some ([0], m)
    else if rdW (m.arr64 IW) (rs.tail.headD 0 + 5) ≠ recl then some ([0], m)
    else tpsK1 p n (rdW (m.arr64 IW) (rs.tail.headD 0 + 2)) (rdW (m.arr64 IW) (rs.tail.headD 0 + 3))
      (callW p n "block_shape_all_ctors" [pp] m)

/-- **The model of `target_rec_pins_split`** (body fuel `n`). -/
def tpsW (p : Prog) (n : Nat) (m : Mem) (pp k recl bo bl : Word) : Option (List Word × Mem) :=
  tpsK0 p n pp k recl (callW p n "block_split" [bo, bl] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp k recl cso csl : Word) (r ra : List Word)
theorem tpsK4_some : tpsK4 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem tpsK0_fail (h : r.headD 0 = 0) : tpsK0 p n pp k recl (some (r, m)) = some ([0], m) := by
  simp only [tpsK0]; rw [ite_eq_left h]
theorem tpsK0_k (h : ¬ r.headD 0 = 0) (h1 : rdW (m.arr64 IW) (r.tail.headD 0 + 1) ≠ k) :
    tpsK0 p n pp k recl (some (r, m)) = some ([0], m) := by
  simp only [tpsK0]; rw [ite_eq_right h, ite_eq_left h1]
theorem tpsK0_r (h : ¬ r.headD 0 = 0) (h1 : ¬ rdW (m.arr64 IW) (r.tail.headD 0 + 1) ≠ k)
    (h5 : rdW (m.arr64 IW) (r.tail.headD 0 + 5) ≠ recl) : tpsK0 p n pp k recl (some (r, m)) = some ([0], m) := by
  simp only [tpsK0]; rw [ite_eq_right h, ite_eq_right h1, ite_eq_left h5]
theorem tpsK0_ok (h : ¬ r.headD 0 = 0) (h1 : ¬ rdW (m.arr64 IW) (r.tail.headD 0 + 1) ≠ k)
    (h5 : ¬ rdW (m.arr64 IW) (r.tail.headD 0 + 5) ≠ recl) : tpsK0 p n pp k recl (some (r, m)) =
    tpsK1 p n (rdW (m.arr64 IW) (r.tail.headD 0 + 2)) (rdW (m.arr64 IW) (r.tail.headD 0 + 3))
      (callW p n "block_shape_all_ctors" [pp] m) := by
  simp only [tpsK0]; rw [ite_eq_right h, ite_eq_right h1, ite_eq_right h5]
end arms
attribute [ind_grind] tpsK4_some tpsK0_fail tpsK0_k tpsK0_r tpsK0_ok

/-- The twin's constructor grouping test. -/
def splitOk (p : BlockShape) (block : List IConstantInfo) : Bool :=
  match ConRon.Arena.blockSplit block with
  | some (cvTs, cs, rs) =>
    cvTs.length == p.k && rs.length == p.recs.length && p.allCtors.map (·.1.name) == cs.map (·.1.name)
  | none => false

/-- **`target_rec_pins_split`'s model is the twin's grouping test**: the shape and the block decoded
below the tops. -/
theorem tpsW_sim (p : Prog) (L : RpLook p) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} (m : Mem) (a : AState) (pp k recl bo bl : Word) (bs : BlockShape) (blk : List IConstantInfo)
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (hblk : DecB (fun m => decEBlk dn m bo.toNat bl.toNat) m blk) (hk : k.toNat = bs.k)
    (hrl : recl.toNat = bs.recs.length) :
    Sim (tpsW p (n + 1) m pp k recl bo bl) (pure (splitOk bs blk)) a
      (fun r b m' a' => r.headD 0 = (if b then 1 else 0) ∧ a' = a ∧ StageR vis fe m' a ∧ IWGrow m m') := by
  sorry

end L.Ind

end
