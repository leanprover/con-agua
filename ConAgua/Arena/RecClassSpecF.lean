import ConAgua.Arena.RecClassSpecE
import ConAgua.Arena.IndSumSpec4

/-!
# `RecClass`: `classReadSlot`, `classReadSlots` (lane `indproofs2`, helper `rec`)
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Models -/

section models
variable (n : Nat) (p vis : Word)

def sK6 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => some ([1, r6.headD 0], m6)

def sK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => sK6 (newRecM m5 2 [0, r5.headD 0])

def sK4 (iName us ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => sK5 (newRecM m4 4 [iName, us, ao, if r4.headD 0 < al then r4.headD 0 else al])

def sK3 (iName us : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => sK4 iName us (r3.headD 0) (r3.tail.headD 0) (npcW n m3 p vis iName)

def sK2 (mdom : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 >>> 28 ≠ 3 then some ([0, 0], m2)
    else if eViewW m2 (r2.headD 0) = [] then none
    else sK3 n p vis ((eViewW m2 (r2.headD 0)).tail.headD 0)
      ((eViewW m2 (r2.headD 0)).tail.tail.headD 0) (gaaF m2 [CWF, mdom])

def sK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.tail.headD 0 = 0 then some ([0, 0], m1)
    else sK2 n p vis (rdW (m1.arr64 IW) (r1.headD 0 + r1.tail.headD 0 - 1))
      (gafF m1 [CWF, rdW (m1.arr64 IW) (r1.headD 0 + r1.tail.headD 0 - 1)])

end models

/-- **The model of `class_read_slot_motive`.** -/
def slotMotW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, p, vis, dom => sK1 n p vis (piBW n m CWF dom)

def slK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

def slK1 (cR : CallM) (n : Nat) (p vis np mo ml d dom : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 >>> 28 = 2 then slK2 (slotMotW n m1 p vis dom)
    else slK2 (minorW cR n m1 np mo ml d dom)

/-- **The model of `class_read_slot`.** -/
def slotW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, p, vis, np, mo, ml, d, dom => slK1 cR n p vis np mo ml d dom (pirF m [CWF, dom])

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (p vis np mo ml d dom mdom iName us ao al : Word)
  (r r1 r2 r3 r4 r5 r6 : List Word) (cR : CallM)
theorem slotMotW_eq : slotMotW (n + 1) m p vis dom = sK1 n p vis (piBW n m CWF dom) := rfl
theorem sK1_nil (h : r1.tail.headD 0 = 0) : sK1 n p vis (some (r1, m1)) = some ([0, 0], m1) := by
  rw [sK1, if_pos h]
theorem sK1_ok (h : r1.tail.headD 0 ≠ 0) : sK1 n p vis (some (r1, m1)) =
    sK2 n p vis (rdW (m1.arr64 IW) (r1.headD 0 + r1.tail.headD 0 - 1))
      (gafF m1 [CWF, rdW (m1.arr64 IW) (r1.headD 0 + r1.tail.headD 0 - 1)]) := by
  rw [sK1, if_neg h]
theorem sK2_tag (h : r2.headD 0 >>> 28 ≠ 3) : sK2 n p vis mdom (some (r2, m2)) = some ([0, 0], m2) := by
  rw [sK2, if_pos h]
theorem sK2_nil (h : ¬ r2.headD 0 >>> 28 ≠ 3) (h2 : eViewW m2 (r2.headD 0) = []) :
    sK2 n p vis mdom (some (r2, m2)) = none := by rw [sK2, if_neg h, if_pos h2]
theorem sK2_ok (h : ¬ r2.headD 0 >>> 28 ≠ 3) (h2 : eViewW m2 (r2.headD 0) ≠ []) :
    sK2 n p vis mdom (some (r2, m2)) = sK3 n p vis ((eViewW m2 (r2.headD 0)).tail.headD 0)
      ((eViewW m2 (r2.headD 0)).tail.tail.headD 0) (gaaF m2 [CWF, mdom]) := by
  rw [sK2, if_neg h, if_neg h2]
theorem sK3_some : sK3 n p vis iName us (some (r3, m3)) =
    sK4 iName us (r3.headD 0) (r3.tail.headD 0) (npcW n m3 p vis iName) := rfl
theorem sK4_some : sK4 iName us ao al (some (r4, m4)) =
    sK5 (newRecM m4 4 [iName, us, ao, if r4.headD 0 < al then r4.headD 0 else al]) := rfl
theorem sK5_some : sK5 (some (r5, m5)) = sK6 (newRecM m5 2 [0, r5.headD 0]) := rfl
theorem sK6_some : sK6 (some (r6, m6)) = some ([1, r6.headD 0], m6) := rfl
theorem slotW_eq : slotW cR (n + 1) m p vis np mo ml d dom =
    slK1 cR n p vis np mo ml d dom (pirF m [CWF, dom]) := rfl
theorem slK1_mot (h : r1.headD 0 >>> 28 = 2) : slK1 cR n p vis np mo ml d dom (some (r1, m1)) =
    slK2 (slotMotW n m1 p vis dom) := by rw [slK1, if_pos h]
theorem slK1_min (h : ¬ r1.headD 0 >>> 28 = 2) : slK1 cR n p vis np mo ml d dom (some (r1, m1)) =
    slK2 (minorW cR n m1 np mo ml d dom) := by rw [slK1, if_neg h]
theorem slK2_some : slK2 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] slotMotW_eq => slotMotW (n + 1) m p vis dom
grind_pattern [ind_grind] sK1_nil => sK1 n p vis (some (r1, m1))
grind_pattern [ind_grind] sK1_ok => sK1 n p vis (some (r1, m1))
grind_pattern [ind_grind] sK2_tag => sK2 n p vis mdom (some (r2, m2))
grind_pattern [ind_grind] sK2_nil => sK2 n p vis mdom (some (r2, m2))
grind_pattern [ind_grind] sK2_ok => sK2 n p vis mdom (some (r2, m2))
grind_pattern [ind_grind] sK3_some => sK3 n p vis iName us (some (r3, m3))
grind_pattern [ind_grind] sK4_some => sK4 iName us ao al (some (r4, m4))
grind_pattern [ind_grind] sK5_some => sK5 (some (r5, m5))
grind_pattern [ind_grind] sK6_some => sK6 (some (r6, m6))
grind_pattern [ind_grind] slotW_eq => slotW cR (n + 1) m p vis np mo ml d dom
grind_pattern [ind_grind] slK1_mot => slK1 cR n p vis np mo ml d dom (some (r1, m1))
grind_pattern [ind_grind] slK1_min => slK1 cR n p vis np mo ml d dom (some (r1, m1))
grind_pattern [ind_grind] slK2_some => slK2 (some (r, m))

/-- The lookups `class_read_slot` needs. -/
structure SlotProg (p : Prog) : Prop where
  fh : p.lookup "fvar_head" = some fvarHead
  ad : AdF p
  v : p.lookup "e_view" = some eView
  f : p.lookup "sl_find" = some slFind
  cm : p.lookup "class_of_motive_var" = some classOfMotiveVar
  c : p.lookup "iw_copy" = some iwCopy
  a : p.lookup "iw_alloc" = some iwAlloc
  sc : p.lookup "sl_cons" = some slCons
  r2 : p.lookup "rec2" = some rec2
  r4 : p.lookup "rec4" = some rec4
  r5 : p.lookup "rec5" = some rec5
  i1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1
  is : p.lookup "class_read_minor_ihs" = some classReadMinorIhs
  fin : p.lookup "class_read_minor_finish" = some classReadMinorFinish
  pb : p.lookup "pi_binders" = some piBinders
  min : p.lookup "class_read_minor" = some classReadMinor
  tl : p.lookup "class_read_minor_tail" = some classReadMinorTail
  mc : p.lookup "member_names_copy" = some memberNamesCopy
  mn : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  ct : p.lookup "sl_contains" = some slContains
  x : p.lookup "env_ix" = some envIxL
  g : p.lookup "env_row_get" = some envRowGetL
  ef : p.lookup "env_find" = some envFindL
  npc : p.lookup "class_n_pc_of" = some classNPcOf
  smot : p.lookup "class_read_slot_motive" = some classReadSlotMotive
  slot : p.lookup "class_read_slot" = some classReadSlot

theorem classReadSlotMotive_spec (p : Prog) (hP : SlotProg p) (n : Nat) (s₀ : St) (q vis dom : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_slot_motive" [q, vis, dom]
    ⦃fun r s' => LocEq s' s₀ ∧ slotMotW n s₀.mem q vis dom = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.smot]; simp only [callFn, classReadSlotMotive]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        piBinders_spec' p hP.a hP.c hP.v hP.sc hP.pb n, gafF_spec p hP.ad n,
        gaaF_spec p hP.ad n, eView_spec p hP.v n,
        classNPcOf_spec p hP.a hP.mc hP.mn hP.ct hP.x hP.g hP.ef hP.npc n,
        rec4_specW p hP.a n hP.r4, rec2_specW p hP.a n hP.r2] <;>
      finish (gen := 20) [rdW_eq]

theorem classReadSlot_spec (p : Prog) (hP : SlotProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat)
    (s₀ : St) (q vis np mo ml d dom : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_slot" [q, vis, np, mo, ml, d, dom]
    ⦃fun r s' => LocEq s' s₀ ∧ slotW cR n s₀.mem q vis np mo ml d dom = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.slot]; simp only [callFn, classReadSlot]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        pirF_spec p hP.ad n, classReadSlotMotive_spec p hP n,
        classReadMinor_spec p hP.fh hP.v hP.f hP.cm hP.c hP.a hP.sc hP.r2 hP.r5 hP.i1 hP.is hP.fin
          hP.pb hP.min hP.tl hP.ad cR hcR n] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6]

/-! ## Relational lemmas -/

theorem tag_beq (e : Word) (hh : H e) (t : UInt32) (k : Nat) (hk : k < 16) (ht : t = UInt32.ofNat k) :
    (((decI e : EIdx).tag == t) = true) ↔ e >>> 28 = UInt64.ofNat k := by
  subst ht
  have := decE_tag_eq e hh k hk
  simp only [beq_iff_eq]; exact this

theorem decAt_stab {α : Type} {g : Mem → Nat → Nat → Option (List α)} {m : Mem} {i o l : Nat}
    {xs : List α} (h0 : StabD (fun m => iwN m i) m o) (h1 : StabD (fun m => iwN m (i + 1)) m l)
    (hg : StabD (fun m => g m o l) m xs) : StabD (fun m => decAt m (g m) i) m xs := by
  intro m' hgr
  simp only [decAt, h0 m' hgr, h1 m' hgr]; exact hg m' hgr

theorem decCS_motive_stab {m : Mem} {q kp : Nat} {key : ClassKey}
    (h0 : StabD (fun m => iwN m q) m 0) (h1 : StabD (fun m => iwN m (q + 1)) m kp)
    (hk : StabD (fun m => decCK m kp) m key) : StabD (fun m => decCS m q) m (.motive key) := by
  intro m' hg
  simp [decCS, h0 m' hg, h1 m' hg, hk m' hg]

/-- The twin's `classReadSlot` motive arm. -/
def slotMot (bs : BlockShape) (fe : IFEnv) (dom : EIdx) : AM (Option ClassSlot) := do
  let (bss, _) ← ConRon.Arena.piBinders coreWalkFuel dom
  match bss.getLast? with
  | none => pure none
  | some mdom => do
    let hd ← getAppFn coreWalkFuel mdom
    if hd.tag == ETag.const then
      match ← viewConst hd with
      | none => failDanglingE
      | some (iName, us) => do
        let args ← getAppArgs coreWalkFuel mdom
        let n := ConRon.Arena.classNPcOf bs fe iName
        pure (some (.motive ⟨iName, us, args.take n⟩))
    else pure none

theorem slotMotW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (p dom : Word) (bs : BlockShape) (hS : StageR dn vis fe m a) (hH : H dom)
    (hb : BSOK m p.toNat bs) :
    RSim (slotMotW n m p vis dom) (slotMot bs fe (decI dom)) a (KP dn vis fe m decSlot) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [slotMotW_eq]
  refine RSim.bind (K := sK1 n p vis) rfl (simPiBinders n hS hH) ?_
  rintro ⟨r1, m1⟩ ⟨bss, e⟩ a1 - ⟨hS1, hg1, hd1, ht1⟩
  dsimp only at hS1 hg1 hd1 ht1
  have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
    have h1 : iwTop m1 ≤ (m1.arr64 IW).size := hS1.2.1
    have h2 : (m1.arr64 IW).size < 2 ^ 64 := hS1.2.2.2.1
    omega
  by_cases hz : r1.tail.headD 0 = 0
  · rw [sK1_nil (h := hz)]
    have hnil : bss = [] := by
      have := decHL_length m1 hd1; rw [hz] at this; exact List.eq_nil_of_length_eq_zero this
    subst hnil
    exact RSim.pure_some ⟨hS1, hg1, rfl⟩
  obtain ⟨w, hw, hwH, hlast⟩ := decHL_last hd1 hz hb1
  rw [sK1_ok (h := hz), hw]
  simp only []
  rw [hlast]
  refine RSim.bind (K := sK2 n p vis w) rfl (simGetAppFn hS1 hwH) ?_
  rintro ⟨r2, m2⟩ hd a2 - ⟨hS2, hg2, hb2, rfl⟩
  dsimp only at hS2 hg2 hb2
  have hg12 := hg1.trans hg2
  by_cases hg : r2.headD 0 >>> 28 ≠ 3
  · rw [sK2_tag (h := hg)]
    have ht : ¬ (((decI (r2.headD 0) : EIdx)).tag == ETag.const) = true :=
      fun e => hg ((tag_beq _ hb2 _ 3 (by decide) rfl).mp e)
    rw [if_neg ht]
    exact RSim.pure_some ⟨hS2, hg12, rfl⟩
  by_cases hne : eViewW m2 (r2.headD 0) = []
  · rw [sK2_nil (h := hg) (h2 := hne)]; exact RSim.none
  rw [sK2_ok (h := hg) (h2 := hne)]
  have hg3 : r2.headD 0 >>> 28 = 3 := by simpa using hg
  have ht : (((decI (r2.headD 0) : EIdx)).tag == ETag.const) = true :=
    (tag_beq _ hb2 _ 3 (by decide) rfl).mpr hg3
  obtain ⟨hvc, hnH, huH⟩ := viewConstW hS2.1.arena.1 hne hg3
  rw [if_pos ht]
  refine RSim.tstep hvc ?_
  refine RSim.bind (K := sK3 n p vis ((eViewW m2 (r2.headD 0)).tail.headD 0)
    ((eViewW m2 (r2.headD 0)).tail.tail.headD 0)) rfl (simGetAppArgs hS2 hwH) ?_
  rintro ⟨r3, m3⟩ args a3 - ⟨hS3, hg3', hd3, ht3⟩
  dsimp only at hS3 hg3' hd3 ht3
  simp only [Nat.zero_add, getD_zero, getD_one] at hd3 ht3
  have hg13 := hg12.trans hg3'
  rw [sK3_some]
  refine RSim.lstep (K := sK4 _ _ (r3.headD 0) (r3.tail.headD 0)) rfl ?_
  rintro ⟨r4, m4⟩ h4
  obtain ⟨hS4, hg4, rfl, hN⟩ := npcW_ok h4 hS3 (hb.grow hg13) hnH
  rw [sK4_some]
  simp only [List.headD_cons]
  generalize hNd : ConRon.Arena.classNPcOf bs fe (decI ((eViewW m2 (r2.headD 0)).tail.headD 0)) = N at hN ⊢
  refine RSim.lstep (K := sK5) rfl ?_
  rintro ⟨r5, m5⟩ h5
  obtain ⟨hS5, hg5, hr5, hget5, htop5⟩ := recW_stage h5 hS4 rfl
  rw [sK5_some, hr5]
  simp only [List.headD_cons]
  refine RSim.lstep (K := sK6) rfl ?_
  rintro ⟨r6, m6⟩ h6
  obtain ⟨hS6, hg6, hr6, hget6, htop6⟩ := recW_stage h6 hS5 rfl
  rw [sK6_some, hr6]
  refine RSim.pure_some ⟨hS6, ((hg13.trans hg4).trans hg5).trans hg6, rfl, ?_⟩
  simp only [List.headD_cons, List.tail_cons]
  have hlen3 := decHL_length m3 hd3
  have hds : decHL m3 (r3.headD 0).toNat (min N (r3.tail.headD 0).toNat) = some (args.take N) := by
    rw [decHL_take hd3 _ (Nat.min_le_right _ _)]
    congr 1; rw [List.take_eq_take_iff]; simp [hlen3]
  have hq5 : rdW (m4.arr64 CTL) 200 = rdW (m4.arr64 CTL) 200 := rfl
  have k0 := rec_iwH_stab (kk := IdxKind.name) hq5 hget5 htop5 0 (by simp) hnH
  have k1 := rec_iwH_stab (kk := IdxKind.levels) hq5 hget5 htop5 1 (by simp) huH
  have k2 := rec_iwN_stab hq5 hget5 htop5 2 (by simp)
  have k3 := rec_iwN_stab hq5 hget5 htop5 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at k0 k1 k2 k3
  replace k3 : StabD (fun m => iwN m ((rdW (m4.arr64 CTL) 200).toNat + 3)) m5
      (min N (r3.tail.headD 0).toNat) := by
    refine fun m' hg => (k3 m' hg).trans (congrArg some ?_)
    by_cases h : UInt64.ofNat N < r3.tail.headD 0
    · simp only [h, if_true]
      have := UInt64.lt_iff_toNat_lt.mp h
      rw [UInt64.toNat_ofNat_of_lt' hN] at this ⊢; omega
    · simp only [h, if_false]
      have : ¬ N < (r3.tail.headD 0).toNat := fun e => h (UInt64.lt_iff_toNat_lt.mpr
        (by rw [UInt64.toNat_ofNat_of_lt' hN]; exact e))
      omega
  have hdsS : StabD (fun m => (decHL m (r3.headD 0).toNat (min N (r3.tail.headD 0).toNat) :
      Option (List EIdx))) m5 (args.take N) := by
    refine StabD.of_eq (fun m'' hg => decHL_grow hg ?_) ?_
    · have := Nat.min_le_right N (r3.tail.headD 0).toNat
      have := Nat.le_trans ht3 ((hg4.trans hg5).1); omega
    · rw [decHL_grow (hg4.trans hg5) (by have := Nat.min_le_right N (r3.tail.headD 0).toNat; omega)]
      exact hds
  have hkey : StabD (fun m => decCK m (rdW (m4.arr64 CTL) 200).toNat) m5
      ⟨decI ((eViewW m2 (r2.headD 0)).tail.headD 0), decI ((eViewW m2 (r2.headD 0)).tail.tail.headD 0),
        args.take N⟩ := by
    intro m' hg
    have e3 : iwN m' ((rdW (m4.arr64 CTL) 200).toNat + 2 + 1) = some (min N (r3.tail.headD 0).toNat) :=
      k3 m' hg
    simp only [decCK, decAt, k0 m' hg, k1 m' hg, k2 m' hg, e3, Option.bind_eq_bind, Option.bind_some, hdsS m' hg]; rfl
  have hq6 : rdW (m5.arr64 CTL) 200 = rdW (m5.arr64 CTL) 200 := rfl
  have j0 := rec_iwN_stab hq6 hget6 htop6 0 (by simp)
  have j1 := rec_iwN_stab hq6 hget6 htop6 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at j0 j1
  exact decCS_motive_stab j0 j1 (hkey.grow hg6)

theorem nameCopyW_afrR : ∀ (n : Nat) (m m' : Mem) (d s l : Word), nameCopyW n m d s l = some m' →
    AFr m m'
  | 0, _, _, _, _, _, h => by simp [nameCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [nameCopyW_nil n m d s l hl] at h; cases h; exact AFr.refl _
    · rw [nameCopyW_step n m d s l hl] at h
      exact (set64IW_afr _ _ _).trans (nameCopyW_afrR n _ _ _ _ _ h)

/-- (`IndT/RecGen19`'s `memberNamesW_afr`, here for the `class_read` chain.) -/
theorem memberNamesW_afrR {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : memberNamesW n m p = some (r, m')) : AFr m m' := by
  unfold memberNamesW at h
  split at h; · cases h
  rename_i q m1 hal
  split at h; · cases h
  rename_i m2 hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (allocW_afr hal).trans (nameCopyW_afrR _ _ _ _ _ _ hc)

theorem envFindW_afrR {m m' : Mem} {w vis : Word} {r : List Word} (h : envFindW m w vis = some (r, m')) :
    AFr m m' := by
  unfold envFindW at h
  afr_auto h []

theorem npcW_afr {n : Nat} {m m' : Mem} {p vis i : Word} {r : List Word}
    (h : npcW n m p vis i = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [npcW] at h
  | succ n =>
  simp only [npcW, npcK1.eq_def, npcK2.eq_def, npcK3.eq_def] at h
  afr_auto h [memberNamesW_afrR, envFindW_afrR]

theorem slotMotW_afr {n : Nat} {m m' : Mem} {p vis dom : Word} {r : List Word}
    (h : slotMotW n m p vis dom = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [slotMotW] at h
  | succ n =>
  simp only [slotMotW, sK1.eq_def, sK2.eq_def, sK3.eq_def, sK4.eq_def, sK5.eq_def, sK6.eq_def] at h
  afr_auto h [piBW_afrR _ _ _ _ _ _, gafF_afrR, gaaF_afr, npcW_afr, recW_afr]

theorem slotW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (n : Nat) (m : Mem)
    (a : AState) (p np mo ml d dom : Word) (bs : BlockShape) (motPos : List Nat)
    (hS : StageR dn vis fe m a) (hJ : J m) (hH : H dom) (hb : BSOK m p.toNat bs)
    (hmot : decNL m mo.toNat ml.toNat = some motPos) (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (slotW cR n m p vis np mo ml d dom)
      (ConRon.Arena.classReadSlot bs fe np.toNat motPos d.toNat (decI dom)) a
      (fun b a' x => KP dn vis fe m decSlot b a' x ∧ J b.2) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [slotW_eq]
  refine RSim.bind (K := slK1 cR n p vis np mo ml d dom) rfl
    (RSim.withJ hO.1 (simPiResult hS hH) (fun _ _ hb => pirF_afrR hb) hJ) ?_
  rintro ⟨r1, m1⟩ r a1 - ⟨⟨hS1, hg1, hb1, rfl⟩, hJ1⟩
  dsimp only at hS1 hg1 hb1 hJ1
  by_cases ht : r1.headD 0 >>> 28 = 2
  · rw [slK1_mot (h := ht)]
    have ht' : (((decI (r1.headD 0) : EIdx)).tag == ETag.sort) = true :=
      (tag_beq _ hb1 _ 2 (by decide) rfl).mpr ht
    rw [if_pos ht']
    refine RSim.bindPure (K := slK2) rfl (RSim.withJ hO.1
      (slotMotW_sim dn vis fe n m1 a1 p dom bs hS1 hH (hb.grow hg1)) (fun _ _ hb => slotMotW_afr hb) hJ1) ?_
    rintro ⟨r2, m2⟩ x a2 - ⟨⟨hS2, hg2, hd2⟩, hJ2⟩
    rw [slK2_some]
    exact RSim.pure_some ⟨⟨hS2, hg1.trans hg2, decSlot_pair hd2⟩, hJ2⟩
  · rw [slK1_min (h := ht)]
    have ht' : ¬ (((decI (r1.headD 0) : EIdx)).tag == ETag.sort) = true :=
      fun e => ht ((tag_beq _ hb1 _ 2 (by decide) rfl).mp e)
    rw [if_neg ht']
    refine RSim.bindPure (K := slK2) rfl (minorW_sim dn vis fe cR J hO n m1 a1 np mo ml d dom motPos hS1
      hJ1 hH (by rw [decNL_grow hg1 hmt]; exact hmot) (Nat.le_trans hmt hg1.1)) ?_
    rintro ⟨r2, m2⟩ x a2 - ⟨⟨hS2, hg2, hd2⟩, hJ2⟩
    rw [slK2_some]
    exact RSim.pure_some ⟨⟨hS2, hg1.trans hg2, decSlot_pair hd2⟩, hJ2⟩

/-- **`class_read_slot` refines `classReadSlot`** (through the stubs `pi_result`, `get_app_fn`,
`get_app_args`, `open_pis_at_fvars_f`, `fvar_type_d`): the slot is a stably decoding record. -/
@[refines ConRon.Arena.classReadSlot]
theorem classReadSlot_refines (p : Prog) (hP : SlotProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q np mo ml d dom : Word)
    (bs : BlockShape) (motPos : List Nat) (hS : StageR dn vis fe s₀.mem a₀) (hH : H dom)
    (hb : BSOK s₀.mem q.toNat bs) (hmot : decNL s₀.mem mo.toNat ml.toNat = some motPos)
    (hmt : mo.toNat + ml.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_slot" [q, vis, np, mo, ml, d, dom]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classReadSlot bs fe np.toNat motPos d.toNat (decI dom)) a₀ ∧
      KP dn vis fe s₀.mem decSlot (r, s'.mem)
        (AM.st (ConRon.Arena.classReadSlot bs fe np.toNat motPos d.toNat (decI dom)) a₀)
        (AM.res (ConRon.Arena.classReadSlot bs fe np.toNat motPos d.toNat (decI dom)) a₀); ⊤⦄ :=
  triple_post (classReadSlot_spec p hP stubCall (stubCall_spec p) n s₀ q vis np mo ml d dom) fun _ _ ⟨hl, hw⟩ =>
    ⟨hl, ((slotW_sim dn vis fe stubCall _ (opfJ_stub dn vis fe) n _ a₀ q np mo ml d dom bs motPos hS trivial
      hH hb hmot hmt).mono fun _ _ _ _ h => h.1).am hw⟩

end L.Ind
