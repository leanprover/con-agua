module

public import ConAgua.Arena.RecCheckSpec.RpLook
public import ConAgua.Arena.RecCheckSpec.PtrNamesWDec
import ConAgua.Arena.IndPartsSpec.AllCtors
import ConAgua.Arena.IndPartsSpec.BlockSplitRecs
import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
public import ConAgua.Arena.IndGrindAttr
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.EqW
import ConAgua.L.ModelGen
import all ConAgua.Arena.RecCheck
import ConAgua.Arena.IndPartsSpec.RecTW
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved

@[expose] public section

/-!
# TpsW

`decCN_cv`, `decCN_lt`, `decSC_cv`, `decSC_lt`, the generated `tpsW` and the lemmas only they use.
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

/-- **`target_rec_pins_split` is its model `tpsW`** (generated; body fuel `n`). -/
l_model tps_spec (p : Prog) (hp : p.lookup "target_rec_pins_split" = some targetRecPinsSplit)
  fns [hp ↦ tpsW list]
  specs [callW_spec p n "block_split", callW_spec p n "block_shape_all_ctors",
    callW_spec p n "ptr_list_names", callW_spec p n "sl_eq"]
  grind [arena_grind, ind_grind] finish [rdW_eq] gen 20 pfuel

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
  have hT : ∀ m : Mem, iwTop m < 2 ^ 64 := fun m => (rdW (m.arr64 CTL) 200).toNat_lt
  unfold tpsW
  refine Sim.mstep (K := tpsW.k_block_split p (n + 1) pp k recl) rfl (fun _ _ => rfl) fun rs m1 h1 => ?_
  obtain ⟨s1, rfl, -, hS1, hg1, hsp⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockSplit_refines p L.toIndPartsProg (n + 1) _ a dn vis fe bo bl blk hS hblk) h1
  dsimp only at hS1 hg1 hsp
  unfold splitOk
  cases hbs : ConRon.Arena.blockSplit blk with
  | none =>
    rw [hbs] at hsp
    rw [tpsW.k_block_split.arm1 (hc1 := hsp)]
    exact Sim.ret ⟨by simp, rfl, hS1, hg1⟩
  | some t =>
  obtain ⟨cvTs, cs, rs'⟩ := t
  rw [hbs] at hsp
  obtain ⟨h1', q6, hcv, hcs, hrr⟩ := hsp
  dsimp only
  have hne : ¬ rs.headD 0 = 0 := by rw [h1']; decide
  have hq1 : rs.tail.headD 0 + 1 = rs.tail.headD 0 + 1 := rfl
  have hlen1 : (rdW (s1.mem.arr64 IW) (rs.tail.headD 0 + 1)).toNat = cvTs.length := (decPL_length _ hcv.1).symm
  have hlen5 : (rdW (s1.mem.arr64 IW) (rs.tail.headD 0 + 5)).toNat = rs'.length := (decPL_length _ hrr.1).symm
  by_cases hc1 : rdW (s1.mem.arr64 IW) (rs.tail.headD 0 + 1) ≠ k
  · rw [tpsW.k_block_split.arm2 (hc1 := hne) (hc2 := hc1)]
    have : cvTs.length ≠ bs.k := fun e => hc1 (UInt64.toNat_inj.mp (by rw [hlen1, hk, e]))
    exact Sim.ret ⟨by simp [this], rfl, hS1, hg1⟩
  by_cases hc5 : rdW (s1.mem.arr64 IW) (rs.tail.headD 0 + 5) ≠ recl
  · rw [tpsW.k_block_split.arm3 (hc1 := hne) (hc2 := Classical.not_not.mp hc1) (hc3 := hc5)]
    have : rs'.length ≠ bs.recs.length := fun e => hc5 (UInt64.toNat_inj.mp (by rw [hlen5, hrl, e]))
    exact Sim.ret ⟨by simp [this], rfl, hS1, hg1⟩
  rw [tpsW.k_block_split.arm4 (hc1 := hne) (hc2 := Classical.not_not.mp hc1)
    (hc3 := Classical.not_not.mp hc5)]
  have e1 : cvTs.length = bs.k := by rw [← hlen1, ← hk, Classical.not_not.mp hc1]
  have e5 : rs'.length = bs.recs.length := by rw [← hlen5, ← hrl, Classical.not_not.mp hc5]
  -- the constructors of the shape
  refine Sim.mstep (K := tpsW.k_block_shape_all_ctors p (n + 1) _ _) rfl (fun _ _ => rfl) fun rac m2 h2 => ?_
  obtain ⟨s2, rfl, -, hS2, hg2, hac, hacb⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (blockShapeAllCtors_refines p L.alloc L.copy L.nco L.acc L.acg L.ac (n + 1) _ a dn vis fe pp bs hS1
      (hq.grow (decBS_mono _) hg1)) h2
  dsimp only at hS2 hg2 hac hacb
  rw [getD1] at hac hacb
  -- their names
  refine Sim.mstep (K := tpsW.k_ptr_list_names p (n + 1) _ _) rfl (fun _ _ => rfl) fun ra m3 h3 => ?_
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (ptrListNames_spec p L.alloc L.pnc L.pln (n + 1) _ _ _) h3
  dsimp only at hW3
  obtain ⟨hS3, hg3, hr3, hd3, ht3⟩ := plnW_stage (·.1) (fun q => decCN_mono q) decCN_cv decCN_lt hW3 hS2
    ⟨hac, Or.inr hacb⟩
  subst hr3
  -- the stream's constructors' names
  refine Sim.mstep (K := tpsW.k_ptr_list_names_2 p (n + 1) _ _) rfl (fun _ _ => rfl) fun rc m4 h4 => ?_
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (ptrListNames_spec p L.alloc L.pnc L.pln (n + 1) _ _ _) h4
  dsimp only at hW4
  have hcs3 := hcs.grow (fun q => decSC_mono q) (hg2.trans hg3)
  obtain ⟨hS4, hg4, hr4, hd4, ht4⟩ := plnW_stage (·.1) (fun q => decSC_mono q) decSC_cv decSC_lt hW4 hS3
    ⟨hcs3.1, Or.inr hcs3.2⟩
  subst hr4
  -- the comparison
  refine Sim.mstep (K := tpsW.k_sl_eq p) rfl (fun _ _ => rfl) fun re m5 h5 => ?_
  obtain ⟨s5, rfl, -, hm5, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (slEq_spec p L.slEq (n + 1) _ _ _ _ _) h5
  simp only [List.headD_cons, List.tail_cons] at hW5 hm5
  have hd3' : decHL s4.mem (rdW (s2.mem.arr64 CTL) 200).toNat (rac.tail.headD 0).toNat =
      some (bs.allCtors.map fun x => x.1.name) := by
    rw [decHL_grow3 hg4 (Nat.le_of_eq ht3)]; exact hd3
  obtain ⟨ws1, hs1, hm1, hl1⟩ := slR_of_decHL s4.mem _ _ _ hd3' (by have := hg4.iw; have := hT s4.mem; omega)
  obtain ⟨ws2, hs2, hm2, hl2⟩ := slR_of_decHL s4.mem _ _ _ hd4 (by rw [ht4]; exact hT _)
  rw [ofNat_toNat_word, ofNat_toNat_word] at hs1 hs2
  have heq := eqW_ok _ _ _ _ _ _ _ ws1 ws2 hs1 hs2 hW5
  rw [tpsW.k_sl_eq.arm1, hm5]
  refine Sim.ret ⟨?_, rfl, hS4, hg1.trans (hg2.trans (hg3.trans hg4))⟩
  simp only [List.headD_cons, e1, e5, beq_self_eq_true, Bool.true_and]
  rw [heq, hm1, hm2, map_decI_beq ws1 ws2 hl1 hl2]
  by_cases h : ws1 = ws2 <;> simp [h]

end L.Ind

end
