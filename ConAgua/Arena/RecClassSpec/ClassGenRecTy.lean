import ConAgua.Arena.RecClassSpec.GtProg
import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.RecClassSpec.MjW
import ConAgua.Arena.RecClassSpec.SlotsProg

/-!
# ClassGenRecTy: `ConRon.Arena.classGenRecTy`

The refinement theorems `classGenRecTy_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `class_gen_mot_var` at every fuel. -/
def rec2MotVarF (n : Nat) (m : Mem) (g c : Word) : Option (List Word × Mem) :=
  fuelW n (motVarW (n - 1) m g c)

theorem slotVarW_afr {m m' : Mem} {g s : Word} {r : List Word} (h : slotVarW m g s = some (r, m')) :
    AFr m m' := by
  simp only [slotVarW, svK2.eq_def] at h
  afr_auto h [sointernW_afr, fvinternW_afr]

theorem rec2MotVarF_afr {n : Nat} {m m' : Mem} {g c : Word} {r : List Word}
    (h : rec2MotVarF n m g c = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [rec2MotVarF, fuelW] at h
  simp only [rec2MotVarF, fuelW, motVarW, mvK.eq_def, mvK2.eq_def] at h
  afr_auto h [slotVarW_afr]

theorem rec2MotVar_specF (p : Prog) (h : MtProg p) (hff : p.lookup "fvar_find" = some fvarFind)
    (hfp : p.lookup "fvar_push" = some fvarPush) (hif : p.lookup "intern_fvar" = some internFVar)
    (hsv : p.lookup "class_gen_slot_var" = some classGenSlotVar)
    (hms : p.lookup "class_read_motive_slot" = some classReadMotiveSlot)
    (hp : p.lookup "class_gen_mot_var" = some classGenMotVar) (n : Nat) (s₀ : St) (g c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_mot_var" [g, c]
    ⦃fun r s' => LocEq s' s₀ ∧ rec2MotVarF n s₀.mem g c = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact motVar_spec p h.pw h.sf h.sp h.isort hff hfp hif hsv hms hp n s₀ g c

theorem rec2SimMotVar {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (n : Nat) (hS : StageR dn vis fe m a) {g : Word} (c : Word) {G : ClassGen}
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64) :
    RSim (rec2MotVarF n m g c) (ConRon.Arena.ClassGen.motVar G c.toNat) a
      (fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ H (b.1.headD 0) ∧ decE (b.1.headD 0) = x) := by
  rcases n with _ | n
  · exact RSim.none
  rintro ⟨r, m'⟩ h
  obtain ⟨-, hgt, -⟩ := rec2CG_parts hG
  obtain ⟨hg, hsl⟩ := rec2CG_get (hG.get (decCG_mono _))
  have := hS.2.1; have := hS.2.2.2.1
  obtain ⟨x, a', hrun, hS', hg', h1, h2⟩ := motVarW_ok dn vis fe n m m' a g c G r hS hg (by omega) hsl
    hns (by omega) hS.2.2.2.1 h
  exact ⟨x, a', hrun, hS', hg', h1, h2⟩

l_model classGenRecTyTail_spec (p : Prog) (h : GtProg p)
  fns [h.rtt ↦ grtW list]
  specs [ftdsF_spec p h.ad n, slAppend_specW p h.alloc h.copy h.app n,
    slSnoc_specW p h.alloc h.copy h.snoc n,
    rec2MotVar_specF p h.toMtProg h.fvf h.fvp h.ifv h.sv h.ms h.mv n,
    mknF_spec p h.ad n, closeTelescope_spec p h.db h.ff h.fp h.ifa h.mkf h.ct h.ab n]
  grind [arena_grind] simp [rdW_eq]

l_model classGenRecTy_spec (p : Prog) (h : GtProg p)
  fns [h.rt ↦ gtW list]
  specs [classGenMajor_spec p h.toMjProg n, internFVar_spec p h.fvf h.fvp h.ifv n,
    classGenRecTyTail_spec p h n]
  grind [arena_grind] simp [rdW_eq]

/-! ## `class_gen_rec_ty` refines `classGenRecTy` -/

/-- The twin's `classGenRecTy` after the major variable. -/
def rec2RecTyTail (G : ClassGen) (c : Nat) (ifs : List EIdx) (maj t : EIdx) : AM (Option EIdx) := do
  let ibs ← ifs.mapM G.binder
  let mv ← G.motVar c
  let body ← mkAppN mv (ifs ++ [t])
  let r ← ConRon.Arena.closeTelescope (G.pre ++ ibs ++ [maj]) 0 body
  pure (some r)

theorem rec2RecTy_eq (G : ClassGen) (c : Nat) : ConRon.Arena.classGenRecTy G c = (do
    match ← G.major c G.pre.length with
    | none => pure none
    | some (ifs, maj) => do
      let t ← internE (.fvar (G.pre.length + ifs.length) maj)
      rec2RecTyTail G c ifs maj t) := rfl

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem grtW_sim (n : Nat) (m : Mem) (a : AState) (g c rP fo fl maj t : Word) (G : ClassGen)
    (ifs : List EIdx) (po : Nat) (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64)
    (hpo : iwN m (g.toNat + 12) = some po)
    (hpre : DecB (fun m => (decHL m po rP.toNat : Option (List EIdx))) m G.pre)
    (hifs : decHL m fo.toNat fl.toNat = some ifs) (hfb : fo.toNat + fl.toNat ≤ iwTop m)
    (hmaj : H maj) (ht : H t) (hA : AbsOK m) :
    RSim (grtW n m g c rP fo fl maj t) (rec2RecTyTail G c.toNat ifs (decI maj) (decI t)) a
      (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [grtW.arm1]
  unfold rec2RecTyTail
  rw [rec2MapM_genBinder]
  obtain ⟨-, hgt, -⟩ := rec2CG_parts hG
  refine RSim.bind (K := grtW.k_fvar_type_ds n g c rP fo fl maj t) rfl (RSim.withF ((ftdsF_ok dn vis fe fo fl ifs).sim
      ⟨hS, hifs, fun _ => hfb⟩) (fun _ hb => ftdsF_afr hb)) ?_
  rintro ⟨r1, m1⟩ ibs a1 - ⟨⟨hS1, hg1, hibs, hib⟩, hf1⟩
  dsimp only at hS1 hg1 hibs hib
  simp only [getD_zero, Nat.zero_add, getD_one] at hibs hib
  rw [grtW.k_fvar_type_ds.arm1]
  have hpo1 : iwN m1 (g.toNat + 12) = some po := by rw [iwN_grow hg1 (by omega)]; exact hpo
  obtain ⟨e12, t12⟩ := rec2RdN (w := g) (k := 12) hpo1 hS1.2.2.2.1
  simp only [show UInt64.ofNat 12 = (12 : Word) from rfl] at e12
  rw [e12]
  refine RSim.lstep (K := grtW.k_sl_append n g c fo fl maj t) rfl fun ⟨r2, m2⟩ h2 => ?_
  obtain ⟨hS2, hg2, hd2, hb2⟩ := rec2AppendW_dec h2 hS1 (by rw [t12]; exact hpre.grow (OMono.decHL _ _) hg1) hibs hib
  rw [grtW.k_sl_append.arm1]
  refine RSim.lstep (K := grtW.k_sl_snoc n g c fo fl t) rfl fun ⟨r3, m3⟩ h3 => ?_
  obtain ⟨hr3, hd3, hg3, -, -, ht3⟩ := snocW_dec h3 hS2.2.2.2.1 hS2.2.2.2.2.2 hb2 hmaj hd2
  have hS3 := snocW_stage h3 hS2
  have hA3 := snocW_afr h3 (appendW_afr h2 (hf1 hA))
  rw [grtW.k_sl_snoc.arm1]
  have hg13 := hg1.trans (hg2.trans hg3)
  refine RSim.bind (K := grtW.k_class_gen_mot_var n fo fl t (r3.headD 0) (r3.tail.headD 0)) rfl
    (RSim.withF (rec2SimMotVar n hS3 c (hG.grow (decCG_mono _) hg13) hns) (fun _ hb => rec2MotVarF_afr hb)) ?_
  rintro ⟨r4, m4⟩ mv a4 - ⟨⟨hS4, hg4, hmvH, hmvd⟩, hf4⟩
  dsimp only at hS4 hg4 hmvH hmvd
  subst hmvd
  rw [grtW.k_class_gen_mot_var.arm1]
  have hg14 := hg13.trans hg4
  refine RSim.lstep (K := grtW.k_sl_snoc_2 n (r3.headD 0) (r3.tail.headD 0) (r4.headD 0)) rfl fun ⟨r5, m5⟩ h5 => ?_
  obtain ⟨hr5, hd5, hg5, -, -, ht5⟩ := snocW_dec h5 hS4.2.2.2.1 hS4.2.2.2.2.2 (Nat.le_trans hfb hg14.1) ht
    (by rw [decHL_grow hg14 hfb]; exact hifs)
  have hS5 := snocW_stage h5 hS4
  have hA5 := snocW_afr h5 (hf4 hA3)
  rw [grtW.k_sl_snoc_2.arm1]
  rw [hr5] at ⊢
  simp only [List.headD_cons, List.tail_cons]
  refine RSim.bind (K := grtW.k_mk_app_n_f n (r3.headD 0) (r3.tail.headD 0)) rfl
    (RSim.withF ((mknF_ok dn vis fe _ _ _ hmvH (ifs ++ [decI t])).sim ⟨hS5, hd5⟩) (fun _ hb => mknF_afr hb)) ?_
  rintro ⟨r6, m6⟩ body a6 - ⟨⟨hS6, hg6, hbH, hbd⟩, hf6⟩
  dsimp only at hS6 hg6 hbH hbd
  rw [grtW.k_mk_app_n_f.arm1]
  have hg36 := hg4.trans (hg5.trans hg6)
  have hb3 : (r3.headD 0).toNat + (r3.tail.headD 0).toNat ≤ iwTop m3 := by rw [hr3]; simp only [List.headD_cons, List.tail_cons]; omega
  have hd3' : decHL m6 (r3.headD 0).toNat (r3.tail.headD 0).toNat = some (G.pre ++ ibs ++ [decI maj]) := by
    rw [decHL_grow hg36 hb3, hr3]; exact hd3
  refine RSim.bind (K := grtW.k_close_telescope) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m6 b.2 ∧
    decW0E b.2 b.1 x ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨r7, m7⟩ h7
    obtain ⟨x, a', hrun, hS', hg, hx, hA7⟩ := closeW_ok n dn fe vis m6 m7 a6 _ _ 0 _ _ r7 h7 hS6 hbH hd3'
      (hS6.lt64 (Nat.le_trans hb3 hg36.1)) (Nat.le_trans hb3 hg36.1) (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact UInt64.toNat_lt _)
      (hf6 hA5)
    refine ⟨x, a', ?_, hS', hg, hx, hA7⟩
    rw [← hbd]; simpa using hrun
  rintro ⟨r7, m7⟩ x a7 - ⟨hS7, hg7, hx, hA7⟩
  rw [grtW.k_close_telescope.arm1]
  exact RSim.pure_some ⟨⟨hS7, hg14.trans (hg5.trans (hg6.trans hg7)), rfl, by simpa [decW0E] using hx⟩, hA7⟩

end sims

theorem gtW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (g c : Word) (G : ClassGen) (hS : StageR dn vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64) (hA : AbsOK m) :
    RSim (gtW n m g c) (ConRon.Arena.classGenRecTy G c.toNat) a
      (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [gtW.arm1, rec2RecTy_eq]
  obtain ⟨-, hgt, -, -, -, ⟨o12, l12, h12, h13, hpre⟩⟩ := rec2CG_parts hG
  obtain ⟨e13, t13⟩ := rec2RdN (w := g) (k := 13) h13 hS.2.2.2.1
  simp only [show UInt64.ofNat 13 = (13 : Word) from rfl] at e13
  rw [e13]
  have hlen : G.pre.length = l12 := decHL_length _ (hpre.get (OMono.decHL _ _))
  have hm := mjW_sim dn vis fe n m a g c (UInt64.ofNat l12) G hS hG hA
  have hd13 : (UInt64.ofNat l12 : Word).toNat = G.pre.length := by rw [t13, hlen]
  rw [hd13] at hm
  refine RSim.bind (K := gtW.k_class_gen_major n g c (UInt64.ofNat l12)) rfl hm ?_
  rintro ⟨r1, m1⟩ o1 a1 - ⟨⟨hS1, hg1, ho1⟩, hA1⟩
  dsimp only at hS1 hg1 ho1
  rcases o1 with _ | p1
  · rw [gtW.k_class_gen_major.arm1 (hc1 := ho1)]; exact RSim.pure_some ⟨⟨hS1, hg1, rfl⟩, hA1⟩
  obtain ⟨ifs, maj⟩ := p1
  obtain ⟨h11, ⟨hifs, hfb⟩, hmH, hmd⟩ := ho1
  simp only [getD_one, getD_two, Nat.reduceAdd] at hifs hfb
  simp only [drop3_headD] at hmH hmd
  have h10 : r1.headD 0 ≠ 0 := by rw [h11]; decide
  by_cases hov : UInt64.ofNat l12 + r1.tail.tail.headD 0 < UInt64.ofNat l12
  · rw [gtW.k_class_gen_major.abort1 (hc1 := h10) (hc2 := hov)]; exact RSim.none
  rw [gtW.k_class_gen_major.arm2 (hc1 := h10) (hc2 := hov)]
  have hu : (UInt64.ofNat l12 + r1.tail.tail.headD 0).toNat = G.pre.length + ifs.length := by
    have : ¬ (UInt64.ofNat l12 + r1.tail.tail.headD 0).toNat < (UInt64.ofNat l12 : Word).toNat :=
      fun x => hov (UInt64.lt_iff_toNat_lt.mpr x)
    rw [UInt64.toNat_add] at this ⊢
    have h1 : l12 < 2 ^ 64 := by have := (UInt64.ofNat l12 : Word).toNat_lt; rw [t13] at this; exact this
    have h2 := (r1.tail.tail.headD 0).toNat_lt
    rw [decHL_length _ hifs, hlen]
    rw [t13] at this ⊢
    omega
  have hi := simInternFVar hS1 (UInt64.ofNat l12 + r1.tail.tail.headD 0) hmH
  rw [hu, hmd] at hi
  refine RSim.bind (K := gtW.k_intern_fvar n g c _ _ _ _) rfl (RSim.withF hi (fun _ hb => fvinternW_afr hb)) ?_
  rintro ⟨t, m2⟩ x a2 - ⟨⟨hS2, hg2, rfl⟩, hf2⟩
  dsimp only at hS2 hg2
  by_cases hbig : 4294967296 ≤ t
  · rw [gtW.k_intern_fvar.abort1 (hc1 := hbig)]; exact RSim.none
  rw [gtW.k_intern_fvar.arm1 (hc1 := hbig)]
  have htH : H t := by
    have : ¬ (4294967296 : Word).toNat ≤ t.toNat := fun x => hbig (UInt64.le_iff_toNat_le.mpr x)
    simp at this; exact this
  have hg12 := hg1.trans hg2
  have hr := grtW_sim (dn := dn) (vis := vis) (fe := fe) n m2 a2 g c (UInt64.ofNat l12) _ _ _ t G ifs o12 hS2
    (hG.grow (decCG_mono _) hg12) hns (by rw [iwN_grow hg12 (by omega)]; exact h12)
    (by rw [t13]; exact hpre.grow (OMono.decHL _ _) hg12) (by rw [decHL_grow hg2 hfb]; exact hifs)
    (Nat.le_trans hfb hg2.1) hmH htH (hf2 hA1)
  rw [hmd] at hr
  refine RSim.bindPure (K := gtW.k_class_gen_rec_ty_tail) rfl hr ?_
  rintro ⟨r5, m5⟩ y a5 - ⟨⟨hS5, hg5, hy⟩, hA5⟩
  rw [gtW.k_class_gen_rec_ty_tail.arm1]
  refine RSim.pure_some ⟨⟨hS5, hg12.trans hg5, ?_⟩, hA5⟩
  cases y with
  | none => exact hy
  | some e => obtain ⟨h1, h2⟩ := hy; exact ⟨by simpa using h1, by simpa [decW0E] using h2⟩

/-- **`class_gen_rec_ty` refines `classGenRecTy`** (through the stubs of `class_gen_major`,
`fvar_type_ds`, `mk_app_n_f` and `close_telescope`'s `abstract1_fast`; the generator decoded below
the tops). -/
@[refines ConRon.Arena.classGenRecTy]
theorem classGenRecTy_refines (p : Prog) (hp : GtProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g c : Word) (G : ClassGen)
    (hS : StageR dn vis fe s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rec_ty" [g, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classGenRecTy G c.toNat) a₀ ∧
      KP dn vis fe s₀.mem decOE (r, s'.mem) (AM.st (ConRon.Arena.classGenRecTy G c.toNat) a₀)
        (AM.res (ConRon.Arena.classGenRecTy G c.toNat) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classGenRecTy_spec p hp n s₀ g c) fun _ _ ⟨hl, hw⟩ =>
    let h := (gtW_sim dn vis fe n _ a₀ g c G hS hG hns hA).am hw
    ⟨hl, h.1, h.2.1, h.2.2⟩

end L.Ind

end
