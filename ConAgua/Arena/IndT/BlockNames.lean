module

public import ConAgua.Arena.IndT.BlockC
public import ConAgua.Arena.IndInstallSpec.CbProg
public import ConAgua.Arena.Pins
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndPartsSpec.AllCtors
import ConAgua.Arena.IndPartsSpec.BlockShapeAllCtorsGo
import ConAgua.Arena.IndPartsSpec.MemberNames
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndInstallSpec.IcaW
import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# `check_block_names`' contract (lane `ronsync2`, stage 3)

`check_block_names(p0)` (`IndInstall.lean`): the constructors' and the members' names
(`block_shape_all_ctors`, `block_caps_ctor_names`, `block_shape_member_names`), their two
`sl_nodup`s, the `Bool` constructors' pins (`pin_at`) and the members' `sl_contains` against them:
`cbNamesT`, both outcomes, the twin's state kept (`namesRefS_of`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups `check_block_names` takes. -/
structure NamesProg (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  cp : p.lookup "iw_copy" = some iwCopy
  nco : p.lookup "num_ctors_of" = some numCtorsOf
  acc : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy
  acg : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo
  ac : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors
  mnc : p.lookup "member_names_copy" = some memberNamesCopy
  bccn : p.lookup "block_caps_ctor_names" = some blockCapsCtorNames
  bsmn : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  slc : p.lookup "sl_contains" = some slContains
  nodup : p.lookup "sl_nodup" = some slNodup
  pin : p.lookup "pin_at" = some pinAtL
  cbn : p.lookup "check_block_names" = some checkBlockNames

set_option experimental.vcgen true in
/-- **`check_block_names`' unified model**: its callees (outside the verdict closure) lifted. -/
l_model cbnE_spec (p : Prog) (hP : NamesProg p)
  fns [hP.cbn ↦ cbnE]
  specs [callW_spec p n "block_shape_all_ctors", callW_spec p n "block_caps_ctor_names",
    callW_spec p n "block_shape_member_names", callW_spec p n "sl_nodup", callW_spec p n "pin_at",
    callW_spec p n "sl_contains"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`BkMem` across a write of fresh `IW` words** (and the top). -/
theorem BkMem.ofIW {m m' : Mem} (h : BkMem m) (hf : MemFrame [IW] [200] m m') : BkMem m' :=
  ⟨h.ind.frame hf (fun b hb => by simp only [List.mem_singleton] at hb; subst hb; exact ⟨by decide, by decide, by decide⟩)
      (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; decide),
    CoreMemos.frame hf ⟨by simp; decide, by simp; decide⟩ ⟨by simp, by simp⟩ h.core,
    AFr.of_frame hf (by decide) (by decide) h.abs⟩

section ref
variable {G : Prop} {p : Prog} {dn : NIdx → Option ConLeche.Name}

/-- **`check_block_names`' model refines `cbNamesT`, both outcomes**, the twin's state kept. -/
theorem cbn_ref (hP : NamesProg p) {N : Nat} {vis : Word} {fe : IFEnv} {env : ConLeche.Env} {m : Mem}
    {a : AState} {p0 : Word} {bs : BlockShape} (hB : BkSt dn vis fe env m a)
    (hq : DecB (fun m => decBS m p0.toNat) m bs) (hsl : ShapeSl m p0) :
    RefE G (cbnE p N m p0) (cbNamesT bs) a (fun v _ a' => BkGo dn vis fe env m a v.2 a') := by
  have hS := hB.c.stage
  have hM := hB.mem
  have hsrc : ShapeSrc m p0 := hsl.1
  obtain ⟨hq', hq9, hptr⟩ := partsShapeFacts hq hsrc
  rcases N with _ | n
  · rw [cbnE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [cbnE.arm1]
  -- the constructors
  refine RefE.onlySim (fun _ => cbnE.k_block_shape_all_ctors.none ..) (fun _ _ h => h) fun r1 m1 c1 => ?_
  rw [cbnE.k_block_shape_all_ctors.arm1]
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeAllCtors_spec p hP.ha hP.cp hP.nco hP.acc hP.acg hP.ac n _ p0) c1
  simp only at hs1 hW1
  subst hs1
  obtain ⟨cq, tot, rfl, hdc, hg1, hf1, htop1, hroom1⟩ := acW_ok _ _ _ p0 _ bs hW1 hq hS.iw.iwSize hS.iw.ctl
  have hS1 := stage_frame_iw hS hf1 (by omega)
  have hM1 := hM.ofIW hf1
  simp only [List.headD_cons, List.tail_cons]
  have hT1 : iwTop s1.mem < 2 ^ 64 := (rdW (s1.mem.arr64 CTL) 200).toNat_lt
  -- the constructors' names
  refine RefE.onlySim (fun _ => cbnE.k_block_caps_ctor_names.none ..) (fun _ _ h => h) fun r2 m2 c2 => ?_
  rw [cbnE.k_block_caps_ctor_names.arm1]
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (blockCapsCtorNames_spec p hP.ha hP.mnc hP.bccn n _ cq tot) c2
  simp only at hs2 hW2
  subst hs2
  have hcsd : decPL (truncM s1.mem) (decCN (truncM s1.mem)) cq.toNat tot.toNat = some bs.allCtors := hdc
  have hlen := decPL_length _ hcsd
  obtain ⟨hr2, hd2, hg2, hf2, ht2⟩ := ctorNamesW_dec hW2 hS1.iw.iwSize hS1.iw.ctl (Nat.le_of_eq htop1)
    (bs.allCtors.map (·.1)) (by simp [hlen]) (fun j hj => by
      obtain ⟨v, y, hv, hy, hget⟩ := decPL_get tot.toNat cq.toNat bs.allCtors hcsd j hj
      obtain ⟨⟨a', hva, hcv⟩, -⟩ := decCN_some hy
      obtain ⟨hvlt, hv'⟩ := rec2IwN_trunc hv
      obtain ⟨hvlt2, hva'⟩ := rec2IwN_trunc hva
      have hj' : j < bs.allCtors.length := by omega
      have hy' : bs.allCtors[j] = y := by simpa [List.getElem?_eq_getElem hj'] using hget
      refine ⟨v, a', hv', by omega, hva', ?_⟩
      simp only [List.getElem_map, hy']
      exact DecB.get (f := fun m => decCVp m a') (OMono.decCVp _) hcv)
  have hS2 : StageR vis fe s2.mem a := stage_frame_iw hS1 hf2 (by
    have := ctorNamesW_room hW2 hS1.iw.iwSize; simp only [iwTop] at this ht2 ⊢; omega)
  subst hr2
  simp only [List.map_map] at hd2
  have hM2 := hM1.ofIW hf2
  have hg12 := hg1.trans hg2
  have hT2 : iwTop s2.mem < 2 ^ 64 := (rdW (s2.mem.arr64 CTL) 200).toNat_lt
  -- the members' names
  have hq2 := hq.grow (decBS_mono _) hg12
  have hsrc2 := partsHsrc_grow hg12 hq9 hsrc
  obtain ⟨hqd2, hq92, hptr2⟩ := partsShapeFacts hq2 hsrc2
  refine RefE.onlySim (fun _ => cbnE.k_block_shape_member_names.none ..) (fun _ _ h => h) fun r3 m3 c3 => ?_
  rw [cbnE.k_block_shape_member_names.arm1]
  obtain ⟨s3, hs3, hr3, hdn3, hg3, hf3, ht3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (blockShapeMemberNames_refines p hP.ha hP.mnc hP.bsmn n _ p0 bs hqd2 (by omega) hS2.iw.iwSize
      hS2.iw.ctl hsrc2 (fun o l j v h1 h2 h3 h4 => Nat.lt_of_succ_lt (hptr2 o l j v h1 h2 h3 h4))) c3
  obtain ⟨s3', hs3', -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (blockShapeMemberNames_spec p hP.ha hP.mnc hP.bsmn n _ p0) c3
  have hroom := memberNamesW_room hW3 hS2.iw.iwSize
  rw [partsShapeK hqd2 hq92] at hroom
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hqd2).1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  rw [UInt64.toNat_ofNat_of_lt' hkb] at hroom
  simp only at hs3 hr3 hdn3 hg3 hf3 ht3
  subst hs3
  have hS3 : StageR vis fe s3.mem a := stage_frame_iw hS2 hf3 (by
    rw [← ht3]; simp only [iwTop] at hroom ⊢; omega)
  subst hr3
  simp only [List.headD_cons, List.tail_cons]
  have hM3 := hM2.ofIW hf3
  have hg13 := hg12.trans hg3
  -- the two `sl_nodup`s
  have hcn3 : (decHL s3.mem (rdW (s1.mem.arr64 CTL) 200).toNat tot.toNat : Option (List NIdx)) =
      some (bs.allCtors.map (fun x => x.1.name)) := by
    rw [decHL_grow3 hg3 (by omega), hd2]; rfl
  obtain ⟨wc, hslc, hwc, hwcl⟩ := slR_of_decHL s3.mem _ _ _ hcn3 (by rw [ht2]; exact hT2)
  rw [UInt64.ofNat_toNat, UInt64.ofNat_toNat] at hslc
  obtain ⟨wm, hslm, hwm, hwml⟩ := slR_of_decHL s3.mem _ _ _ hdn3
    (by rw [ht3]; exact (rdW (s3.mem.arr64 CTL) 200).toNat_lt)
  rw [UInt64.ofNat_toNat] at hslm
  refine RefE.onlySim (fun _ => cbnE.k_sl_nodup.none ..) (fun _ _ h => h) fun r4 m4 c4 => ?_
  rw [cbnE.k_sl_nodup.arm1]
  obtain ⟨s4, hs4, -, hm4, hnd1⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (slNodup_refines p hP.slc hP.nodup n _ _ _ wc hslc hwcl) c4
  simp only at hs4 hm4 hnd1
  subst hs4
  rw [hm4]
  refine RefE.onlySim (fun _ => cbnE.k_sl_nodup_2.none ..) (fun _ _ h => h) fun r5 m5 c5 => ?_
  obtain ⟨s5, hs5, -, hm5, hnd2⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (slNodup_refines p hP.slc hP.nodup n _ _ _ wm hslm hwml) c5
  simp only at hs5 hm5 hnd2
  subst hs5
  rw [← hwc] at hnd1
  rw [← hwm] at hnd2
  unfold cbNamesT
  refine RefE.ofArms (fun h => cbnE.k_sl_nodup_2.abort1 (hc1 := h) ..) (fun h => cbnE.k_sl_nodup_2.arm1 (hc1 := h) ..)
    (RefE.guardThen (by decide) (fun h => by simpa [← hnd1, ← hnd2] using h)
      (fun h => by simpa [← hnd1, ← hnd2] using h) fun _ _ => ?_)
  rw [hm5]
  -- the `Bool` constructors' pins
  refine RefE.bindLift (fun _ => cbnE.k_pin_at.none ..) fun r6 m6 c6 => ?_
  obtain ⟨s6, hs6, hm6, -, hw6, hrun6⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (pinBoolTrue_refines p hP.pin n _ a hS3.check.pins) (by exact c6)
  simp only at hs6 hm6
  rw [hm6] at hs6
  subst hs6
  refine ⟨_, _, hrun6, ?_⟩
  rw [cbnE.k_pin_at.arm1]
  refine RefE.bindLift (fun _ => cbnE.k_pin_at_2.none ..) fun r7 m7 c7 => ?_
  obtain ⟨s7, hs7, hm7, -, hw7, hrun7⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (pinBoolFalse_refines p hP.pin n _ a hS3.check.pins) (by exact c7)
  simp only at hs7 hm7
  rw [hm7] at hs7
  subst hs7
  refine ⟨_, _, hrun7, ?_⟩
  rw [cbnE.k_pin_at_2.arm1]
  -- the members against them
  refine RefE.onlySim (fun _ => cbnE.k_sl_contains.none ..)
    (Q := fun r m₁ => m₁ = s3.mem ∧ r.headD 0 = if wm.contains (r6.headD 0) then 1 else 0)
    (fun r m₁ c => by
      obtain ⟨s', hs', -, hm', hc⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
        (slContains_spec p hP.slc n _ _ _ _) c
      simp only at hs' hm' hc
      exact ⟨hs' ▸ hm', containsW_ok n _ _ _ _ _ wm hslm hc⟩) fun r8 m8 ⟨hm8, hr8⟩ => ?_
  rw [cbnE.k_sl_contains.arm1, hm8]
  refine RefE.onlySim (fun _ => cbnE.k_sl_contains_2.none ..)
    (Q := fun r m₁ => m₁ = s3.mem ∧ r.headD 0 = if wm.contains (r7.headD 0) then 1 else 0)
    (fun r m₁ c => by
      obtain ⟨s', hs', -, hm', hc⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
        (slContains_spec p hP.slc n _ _ _ _) c
      simp only at hs' hm' hc
      exact ⟨hs' ▸ hm', containsW_ok n _ _ _ _ _ wm hslm hc⟩) fun r9 m9 ⟨hm9, hr9⟩ => ?_
  have e1 : bs.memberNames.contains (decI (r6.headD 0)) = wm.contains (r6.headD 0) := by
    rw [hwm]; exact contains_map_decI _ hw6 wm hwml
  have e2 : bs.memberNames.contains (decI (r7.headD 0)) = wm.contains (r7.headD 0) := by
    rw [hwm]; exact contains_map_decI _ hw7 wm hwml
  refine RefE.ofArms (fun h => cbnE.k_sl_contains_2.abort1 (hc1 := h) ..)
    (fun h => cbnE.k_sl_contains_2.arm1 (hc1 := h) ..)
    (RefE.guardThen (by decide) (fun h => ?_) (fun h => ?_) fun _ _ => ?_)
  · rw [e1, e2]; rw [hr8, hr9] at h
    revert h; cases wm.contains (r6.headD 0) <;> cases wm.contains (r7.headD 0) <;> simp
  · rw [e1, e2] at h; rw [hr8, hr9]
    revert h; cases wm.contains (r6.headD 0) <;> cases wm.contains (r7.headD 0) <;> simp
  · rw [hm9]
    exact RefE.ret rfl ⟨⟨StageC.of_check hB.c hS3 hM3.abs hB.c.check (ConRon.Arena.Ext.refl _), hM3.ind,
      hM3.abs⟩, hg13, ⟨hB.c.check.state, ConRon.Arena.Ext.refl _, rfl⟩⟩

/-- **`check_block_names`' contract.** -/
theorem namesRefS_of (hP : NamesProg p) (hGnv : G → closedNV p _root_.L.Checker.nvFns = true) :
    NamesRefS G p dn := by
  intro n vis fe env m a p0 bs bsP hB hq hsl _
  have h := RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩) (cbnE_spec p hP n _ p0) hGnv
    (cbn_ref (G := G) hP (N := n) hB hq hsl)
  exact RefE.weakenP h fun ⟨r, m'⟩ y a' h => by
    obtain ⟨s', hs', -, hR⟩ := h; simp only at hs'; subst hs'; exact hR

end ref

end L.Ind

end
