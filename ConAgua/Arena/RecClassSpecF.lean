import ConAgua.Arena.RecClassSpecE
import ConAgua.Arena.IndSumSpec4
import ConAgua.Arena.RecClassSpecD

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

l_model classReadSlotMotive_spec (p : Prog) (hP : SlotProg p)
  fns [hP.smot ↦ slotMotW list]
  specs [piBinders_spec' p hP.a hP.c hP.v hP.sc hP.pb n, gafF_spec p hP.ad n,
    gaaF_spec p hP.ad n, eView_spec p hP.v n,
    classNPcOf_spec p hP.a hP.mc hP.mn hP.ct hP.x hP.g hP.ef hP.npc n,
    rec4_specW p hP.a n hP.r4, rec2_specW p hP.a n hP.r2]
  grind [arena_grind] simp [rdW_eq, getElem_rdW']

/-- After `class_n_pc_of`: the join point of `cnt := min n al`. -/
theorem slotMotW_npc_some (iName us ao al : Word) (r : List Word) (m : Mem) :
    slotMotW.k_class_n_pc_of iName us ao al (some (r, m)) =
      slotMotW.k_rec4 (recW m 4 [iName, us, ao, if r.headD 0 < al then r.headD 0 else al]) := by
  by_cases h : r.headD 0 < al
  · rw [slotMotW.k_class_n_pc_of.arm1 (hc1 := h), slotMotW.j1, ite_eq_left h]
  · rw [slotMotW.k_class_n_pc_of.arm2 (hc1 := h), slotMotW.j1, ite_eq_right h]

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
theorem slotW_eq : slotW cR (n + 1) m p vis np mo ml d dom =
    slK1 cR n p vis np mo ml d dom (pirF m [CWF, dom]) := rfl
theorem slK1_mot (h : r1.headD 0 >>> 28 = 2) : slK1 cR n p vis np mo ml d dom (some (r1, m1)) =
    slK2 (slotMotW n m1 p vis dom) := by rw [slK1, ite_eq_left h]
theorem slK1_min (h : ¬ r1.headD 0 >>> 28 = 2) : slK1 cR n p vis np mo ml d dom (some (r1, m1)) =
    slK2 (minorW cR n m1 np mo ml d dom) := by rw [slK1, ite_eq_right h]
theorem slK2_some : slK2 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] slotW_eq => slotW cR (n + 1) m p vis np mo ml d dom
grind_pattern [ind_grind] slK1_mot => slK1 cR n p vis np mo ml d dom (some (r1, m1))
grind_pattern [ind_grind] slK1_min => slK1 cR n p vis np mo ml d dom (some (r1, m1))
grind_pattern [ind_grind] slK2_some => slK2 (some (r, m))

theorem classReadSlot_spec (p : Prog) (hP : SlotProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat)
    (s₀ : St) (q vis np mo ml d dom : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_slot" [q, vis, np, mo, ml, d, dom]
    ⦃fun r s' => LocEq s' s₀ ∧ slotW cR n s₀.mem q vis np mo ml d dom = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.slot]; simp only [callFn, classReadSlot]
  rcases n with _ | n
  · vcgen [exec] <;> grind
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
  rcases n with _ | n
  · exact RSim.none
  rw [slotMotW.arm1]
  refine RSim.bind (K := slotMotW.k_pi_binders n p vis) rfl (simPiBinders n hS hH) ?_
  rintro ⟨r1, m1⟩ ⟨bss, e⟩ a1 - ⟨hS1, hg1, hd1, ht1⟩
  dsimp only at hS1 hg1 hd1 ht1
  have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
    have h1 : iwTop m1 ≤ (m1.arr64 IW).size := hS1.2.1
    have h2 : (m1.arr64 IW).size < 2 ^ 64 := hS1.2.2.2.1
    omega
  by_cases hz : r1.tail.headD 0 = 0
  · rw [slotMotW.k_pi_binders.arm1 (hc1 := hz)]
    have hnil : bss = [] := by
      have := decHL_length m1 hd1; rw [hz] at this; exact List.eq_nil_of_length_eq_zero this
    subst hnil
    exact RSim.pure_some ⟨hS1, hg1, rfl⟩
  obtain ⟨w, hw, hwH, hlast⟩ := decHL_last hd1 hz hb1
  rw [slotMotW.k_pi_binders.arm2 (hc1 := hz), hw]
  simp only []
  rw [hlast]
  refine RSim.bind (K := slotMotW.k_get_app_fn_f n p vis w) rfl (simGetAppFn hS1 hwH) ?_
  rintro ⟨r2, m2⟩ hd a2 - ⟨hS2, hg2, hb2, rfl⟩
  dsimp only at hS2 hg2 hb2
  have hg12 := hg1.trans hg2
  by_cases hg : r2.headD 0 >>> 28 ≠ 3
  · rw [slotMotW.k_get_app_fn_f.arm1 (hc1 := hg)]
    have ht : ¬ (((decI (r2.headD 0) : EIdx)).tag == ETag.const) = true :=
      fun e => hg ((tag_beq _ hb2 _ 3 (by decide) rfl).mp e)
    rw [ite_eq_right ht]
    exact RSim.pure_some ⟨hS2, hg12, rfl⟩
  by_cases hne : eViewW m2 (r2.headD 0) = []
  · rw [slotMotW.k_get_app_fn_f.abort1 (hc1 := Decidable.of_not_not hg) (hc2 := hne)]; exact RSim.none
  rw [slotMotW.k_get_app_fn_f.arm2 (hc1 := Decidable.of_not_not hg) (hc2 := hne)]
  have hg3 : r2.headD 0 >>> 28 = 3 := by simpa using hg
  have ht : (((decI (r2.headD 0) : EIdx)).tag == ETag.const) = true :=
    (tag_beq _ hb2 _ 3 (by decide) rfl).mpr hg3
  obtain ⟨hvc, hnH, huH⟩ := viewConstW hS2.1.arena.1 hne hg3
  rw [ite_eq_left ht]
  refine RSim.tstep hvc ?_
  refine RSim.bind (K := slotMotW.k_get_app_args_f n p vis ((eViewW m2 (r2.headD 0)).tail.headD 0)
    ((eViewW m2 (r2.headD 0)).tail.tail.headD 0)) rfl (simGetAppArgs hS2 hwH) ?_
  rintro ⟨r3, m3⟩ args a3 - ⟨hS3, hg3', hd3, ht3⟩
  dsimp only at hS3 hg3' hd3 ht3
  simp only [Nat.zero_add, getD_zero, getD_one] at hd3 ht3
  have hg13 := hg12.trans hg3'
  rw [slotMotW.k_get_app_args_f.arm1]
  refine RSim.lstep (K := slotMotW.k_class_n_pc_of _ _ (r3.headD 0) (r3.tail.headD 0)) rfl ?_
  rintro ⟨r4, m4⟩ h4
  obtain ⟨hS4, hg4, rfl, hN⟩ := npcW_ok h4 hS3 (hb.grow hg13) hnH
  rw [slotMotW_npc_some]
  simp only [List.headD_cons]
  generalize hNd : ConRon.Arena.classNPcOf bs fe (decI ((eViewW m2 (r2.headD 0)).tail.headD 0)) = N at hN ⊢
  refine RSim.lstep (K := slotMotW.k_rec4) rfl ?_
  rintro ⟨r5, m5⟩ h5
  obtain ⟨hS5, hg5, hr5, hget5, htop5⟩ := recW_stage h5 hS4 rfl
  rw [slotMotW.k_rec4.arm1, hr5]
  simp only [List.headD_cons]
  refine RSim.lstep (K := slotMotW.k_rec2) rfl ?_
  rintro ⟨r6, m6⟩ h6
  obtain ⟨hS6, hg6, hr6, hget6, htop6⟩ := recW_stage h6 hS5 rfl
  rw [slotMotW.k_rec2.arm1, hr6]
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
    · simp only [h, ite_true]
      have := UInt64.lt_iff_toNat_lt.mp h
      rw [UInt64.toNat_ofNat_of_lt' hN] at this ⊢; omega
    · simp only [h, ite_false]
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

theorem nameCopyW_afr : ∀ (n : Nat) (m m' : Mem) (d s l : Word), nameCopyW n m d s l = some m' →
    AFr m m'
  | 0, _, _, _, _, _, h => by simp [nameCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [nameCopyW_nil n m d s l hl] at h; cases h; exact AFr.refl _
    · rw [nameCopyW_step n m d s l hl] at h
      exact (set64IW_afr _ _ _).trans (nameCopyW_afr n _ _ _ _ _ h)

/-- `memberNamesW` keeps `AbsOK`. -/
theorem memberNamesW_afr {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : memberNamesW n m p = some (r, m')) : AFr m m' := by
  unfold memberNamesW at h
  afr_auto h [allocW_afr, nameCopyW_afr _ _ _ _ _ _]

theorem envFindW_afrR {m m' : Mem} {w vis : Word} {r : List Word} (h : envFindW m w vis = some (r, m')) :
    AFr m m' := by
  unfold envFindW at h
  afr_auto h []

theorem npcW_afr {n : Nat} {m m' : Mem} {p vis i : Word} {r : List Word}
    (h : npcW n m p vis i = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [npcW] at h
  simp only [npcW, npcK1.eq_def, npcK2.eq_def, npcK3.eq_def] at h
  afr_auto h [memberNamesW_afr, envFindW_afrR]

theorem slotMotW_afr {n : Nat} {m m' : Mem} {p vis dom : Word} {r : List Word}
    (h : slotMotW n m p vis dom = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [slotMotW] at h
  simp only [slotMotW, slotMotW.k_pi_binders.eq_def, slotMotW.k_get_app_fn_f.eq_def,
    slotMotW.k_get_app_args_f.eq_def, slotMotW.k_class_n_pc_of.eq_def, slotMotW.j1, slotMotW.k_rec4.eq_def,
    slotMotW.k_rec2.eq_def] at h
  afr_auto h [piBW_afrR _ _ _ _ _ _, gafF_afr, gaaF_afr, npcW_afr, recW_afr]

theorem slotW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (n : Nat) (m : Mem)
    (a : AState) (p np mo ml d dom : Word) (bs : BlockShape) (motPos : List Nat)
    (hS : StageR dn vis fe m a) (hJ : J m) (hH : H dom) (hb : BSOK m p.toNat bs)
    (hmot : decNL m mo.toNat ml.toNat = some motPos) (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (slotW cR n m p vis np mo ml d dom)
      (ConRon.Arena.classReadSlot bs fe np.toNat motPos d.toNat (decI dom)) a
      (fun b a' x => KP dn vis fe m decSlot b a' x ∧ J b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [slotW_eq]
  refine RSim.bind (K := slK1 cR n p vis np mo ml d dom) rfl
    (RSim.withJ hO.1 (simPiResult hS hH) (fun _ _ hb => pirF_afrR hb) hJ) ?_
  rintro ⟨r1, m1⟩ r a1 - ⟨⟨hS1, hg1, hb1, rfl⟩, hJ1⟩
  dsimp only at hS1 hg1 hb1 hJ1
  by_cases ht : r1.headD 0 >>> 28 = 2
  · rw [slK1_mot (h := ht)]
    have ht' : (((decI (r1.headD 0) : EIdx)).tag == ETag.sort) = true :=
      (tag_beq _ hb1 _ 2 (by decide) rfl).mpr ht
    rw [ite_eq_left ht']
    refine RSim.bindPure (K := slK2) rfl (RSim.withJ hO.1
      (slotMotW_sim dn vis fe n m1 a1 p dom bs hS1 hH (hb.grow hg1)) (fun _ _ hb => slotMotW_afr hb) hJ1) ?_
    rintro ⟨r2, m2⟩ x a2 - ⟨⟨hS2, hg2, hd2⟩, hJ2⟩
    rw [slK2_some]
    exact RSim.pure_some ⟨⟨hS2, hg1.trans hg2, decSlot_pair hd2⟩, hJ2⟩
  · rw [slK1_min (h := ht)]
    have ht' : ¬ (((decI (r1.headD 0) : EIdx)).tag == ETag.sort) = true :=
      fun e => ht ((tag_beq _ hb1 _ 2 (by decide) rfl).mp e)
    rw [ite_eq_right ht']
    refine RSim.bindPure (K := slK2) rfl (minorW_sim dn vis fe cR J hO n m1 a1 np mo ml d dom motPos hS1
      hJ1 hH (by rw [decNL_grow hg1 hmt]; exact hmot) (Nat.le_trans hmt hg1.1)) ?_
    rintro ⟨r2, m2⟩ x a2 - ⟨⟨hS2, hg2, hd2⟩, hJ2⟩
    rw [slK2_some]
    exact RSim.pure_some ⟨⟨hS2, hg1.trans hg2, decSlot_pair hd2⟩, hJ2⟩

end L.Ind
