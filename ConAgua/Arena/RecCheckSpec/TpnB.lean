import ConAgua.Arena.RecCheckSpec.RpLook
import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
import ConAgua.Arena.IndPartsSpec.BlockRecNameSetOk
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# TpnB

`rpShape9`, `soa_spec`, `soaW`, `wan_spec`, `wanW`, `wantAuxFrom` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `block_rec_lps_ok`, below the tops -/

/-- The shape record's nine words lie below the top. -/
theorem rpShape9 {m : Mem} {q : Word} {bs : BlockShape} (hq : DecB (fun m => decBS m q.toNat) m bs) :
    q.toNat + 9 ≤ iwTop m := by
  obtain ⟨-, -, -, -, -, -, hpr⟩ := decBS_some (show decBS (truncM m) q.toNat = some bs from hq)
  simp only [iwB, bool?, Option.map_eq_some_iff] at hpr
  obtain ⟨w, hw, -⟩ := hpr
  have := (truncM_iw_get hw).1
  omega

/-! ## `block_rec_split_own_aux` -/

l_model soa_spec (p : Prog) (hP : IndPartsProg p)
    (hp : p.lookup "block_rec_split_own_aux" = some blockRecSplitOwnAux)
  fns [hp ↦ soaW]
  specs [slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [arena_grind] simp [rdW_eq]

/-! ## `block_rec_want_aux_names` -/

l_model wan_spec (p : Prog) (hP : IndPartsProg p) (hNri : NriF p)
    (hp : p.lookup "block_rec_want_aux_names" = some blockRecWantAuxNames)
  fns [hp ↦ wanW]
  specs [nriF_spec p hNri n, slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [arena_grind] simp []

/-- The wanted auxiliary names from index `j` on. -/
def wantAuxFrom (n0 : NIdx) (j k : Nat) : AM (List NIdx) :=
  (List.range k).mapM fun i => internNNode (.str n0 s!"rec_{j + i + 1}")

theorem wantAuxFrom_succ (n0 : NIdx) (j k : Nat) :
    wantAuxFrom n0 j (k + 1) = (do
      let x ← internNNode (.str n0 s!"rec_{j + 1}")
      let xs ← wantAuxFrom n0 (j + 1) k
      pure (x :: xs)) := by
  unfold wantAuxFrom
  rw [List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
  congr 1
  funext x
  congr 1
  congr 1
  funext i
  simp only [Function.comp, Nat.succ_eq_add_one]
  rw [show j + (i + 1) + 1 = j + 1 + i + 1 by omega]

/-- **`block_rec_want_aux_names`' model refines the twin's `mapM` of `name_rec_i`** (the real
`name_rec_i`, `nriF_ok`). -/
theorem wanW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m : Mem) (a : AState) (n0 j auxl : Word), H n0 → StageR dn vis fe m a →
    j.toNat + auxl.toNat < 2 ^ 64 →
    Sim (wanW n m n0 j auxl) (wantAuxFrom (decI n0) j.toNat auxl.toNat) a
      (fun r xs m' a' => decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  induction n with
  | zero => intro m a n0 j auxl _ _ _ r m' e; simp [wanW] at e
  | succ n ih =>
    intro m a n0 j auxl hn0 hS hb
    by_cases hl : auxl = 0
    · rw [wanW.arm1 n m n0 j auxl hl]
      subst hl
      exact Sim.ret ⟨by simp [decHL, hslice?], by simp, hS, IWGrow.refl _⟩
    rw [wanW.arm2 n m n0 j auxl hl]
    have hl0 : auxl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hal1 : (auxl - 1).toNat = auxl.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
    obtain ⟨k, hk⟩ : ∃ k, auxl.toNat = k + 1 := ⟨auxl.toNat - 1, by omega⟩
    rw [hk, wantAuxFrom_succ]
    have h1 := partsSimW (nriF_ok dn vis fe n0 (j + 1) hn0) hS
    rw [hj1] at h1
    refine Sim.bindK (K := wanW.k_name_rec_i n n0 j auxl)
      (body := fun r1 m1 => wanW.k_block_rec_want_aux_names n (r1.headD 0) (wanW n m1 n0 (j + 1) (auxl - 1)))
      (by simp [wanW.k_name_rec_i]) (fun _ _ => wanW.k_name_rec_i.arm1 ..) h1 ?_
    rintro r1 x1 m1 a1 ⟨hS1, hg1, hx1l, hx1⟩
    have hrec := ih m1 a1 n0 (j + 1) (auxl - 1) hn0 hS1 (by rw [hj1, hal1]; omega)
    rw [hj1, hal1, hk, Nat.add_sub_cancel] at hrec
    refine Sim.bindK (K := wanW.k_block_rec_want_aux_names n (r1.headD 0))
      (body := fun r2 m2 => wanW.k_sl_cons (consW n m2 (r1.headD 0) (r2.headD 0) (r2.tail.headD 0)))
      (by simp [wanW.k_block_rec_want_aux_names]) (fun _ _ => wanW.k_block_rec_want_aux_names.arm1 ..) hrec ?_
    rintro r2 xs m2 a2 ⟨hd2, hb2, hS2, hg2⟩
    intro r m' e
    rcases h3 : consW n m2 (r1.headD 0) (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> simp only [h3, wanW.k_sl_cons, reduceCtorEq] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 hb2 hx1l hd2
    refine ⟨x1 :: xs, a2, rfl, ?_, by simp only [List.headD_cons, List.tail_cons]; omega, hS3,
      (hg1.trans hg2).trans hg3⟩
    simp only [List.headD_cons, List.tail_cons]; rw [← hx1]; exact hd3

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem decRS_cv (m : Mem) (pp : Nat) (x : RecShape) (h : decRS m pp = some x) :
    ∃ a, iwN m pp = some a ∧ decCVp m a = some x.cvR := (decRS_some h).1

theorem decRS_lt (m : Mem) (pp : Nat) (x : RecShape) (h : decRS (truncM m) pp = some x) : pp < iwTop m := by
  obtain ⟨⟨a, ha, -⟩, -⟩ := decRS_some h; exact partsIwLt ha

/-- From `n₀` on: the wanted names, the stream's, the set test, the duplicate test. -/
theorem tpnB_sim (p : Prog) (L : RpLook p) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} (bs : BlockShape) (reco recl auxo auxl n0 : Word) (x : NIdx) (hn0 : H n0)
    (hx : decI n0 = x) :
    ∀ (m : Mem) (a : AState), StageR dn vis fe m a → PSlR0 decRS bs.recs reco recl m →
    PSlR decRS (rpAux bs) auxo auxl m →
    Sim (tpnB p (n + 1) reco recl auxo auxl n0 m)
      (do
        let wantAux ← (List.range (rpAux bs).length).mapM fun i => internNNode (.str x s!"rec_{i + 1}")
        if rpSetOk ((rpAux bs).map (·.cvR.name)) wantAux then pure (nameNodup (bs.recs.map (·.cvR.name)))
        else pure false)
      a (fun r b m' a' => r.headD 0 = (if b then 1 else 0) ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  intro m a hS hrs haux
  have hl : auxl.toNat = (rpAux bs).length := (decPL_length _ haux.1).symm
  have hT : ∀ m : Mem, iwTop m < 2 ^ 64 := fun m => (rdW (m.arr64 CTL) 200).toNat_lt
  have hwant : Sim (callW p (n + 1) "block_rec_want_aux_names" [n0, 0, auxl] m)
      ((List.range (rpAux bs).length).mapM fun i => internNNode (.str x s!"rec_{i + 1}")) a
      (fun r xs m' a' => decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
    intro r m' e
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (wan_spec p L.toIndPartsProg L.nri L.wan (n + 1) _ n0 0 auxl) e
    have h := wanW_sim (dn := dn) (vis := vis) (fe := fe) (n + 1) m a n0 0 auxl hn0 hS
      (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact auxl.toNat_lt) r s'.mem hW
    have heq : wantAuxFrom (decI n0) (0 : Word).toNat auxl.toNat =
        (List.range (rpAux bs).length).mapM fun i => internNNode (.str x s!"rec_{i + 1}") := by
      unfold wantAuxFrom; rw [hx, hl]; simp only [UInt64.toNat_zero, Nat.zero_add]
    rw [heq] at h; exact h
  refine Sim.bindK (K := tpnK1 p (n + 1) reco recl auxo auxl) rfl (fun _ _ => rfl) hwant ?_
  rintro rw want m1 a1 ⟨hd1, hb1, hS1, hg1⟩
  refine Sim.mstep (K := tpnK2 p (n + 1) reco recl rw) rfl (fun _ _ => rfl) fun rg m2 h2 => ?_
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (ptrListNames_spec p L.alloc L.pnc L.pln (n + 1) _ auxo auxl) h2
  dsimp only at hW2
  have haux1 := haux.grow (fun q => decRS_mono q) hg1
  obtain ⟨hS2, hg2, hr2, hd2, ht2⟩ := plnW_stage (·.cvR) (fun q => decRS_mono q) decRS_cv decRS_lt hW2 hS1
    ⟨haux1.1, Or.inr haux1.2⟩
  subst hr2
  refine Sim.mstep (K := tpnK3 p (n + 1) reco recl) rfl (fun _ _ => rfl) fun ro m3 h3 => ?_
  obtain ⟨s3, rfl, -, hm3, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (slSetEq_spec p L.contains L.allIn L.setEq n _ _ _ _ _) h3
  simp only [List.headD_cons, List.tail_cons] at hW3 hm3
  rw [hm3]
  have hd1' : decHL s2.mem (rw.headD 0).toNat (rw.tail.headD 0).toNat = some want := by
    rw [decHL_grow3 hg2 hb1]; exact hd1
  obtain ⟨wws, hws, hwm, hwl⟩ := slR_of_decHL s2.mem _ _ _ hd1' (by have := hg2.1; have := hT s2.mem; omega)
  obtain ⟨gws, hgs, hgm, hgl⟩ := slR_of_decHL s2.mem _ _ _ hd2 (by rw [ht2]; exact hT _)
  rw [ofNat_toNat_word, ofNat_toNat_word] at hws hgs
  have hset := setEqW_ok hws hgs hW3
  have hcond : (wws.length == gws.length && gws.all (fun w => wws.contains w) &&
      wws.all (fun w => gws.contains w)) = rpSetOk ((rpAux bs).map (·.cvR.name)) want := by
    unfold rpSetOk
    rw [hgm, hwm, partsAll_decI wws gws hwl hgl, partsAll_decI gws wws hgl hwl, List.length_map,
      List.length_map]
    cases gws.all (fun w => wws.contains w) <;> cases wws.all (fun w => gws.contains w) <;>
      simp [Bool.and_comm, BEq.comm]
  by_cases hok : rpSetOk ((rpAux bs).map (·.cvR.name)) want = true
  · have hro : ro.headD 0 = 1 := by rw [hset, hcond, ite_eq_left hok]
    rw [tpnK3_ok _ _ _ _ _ _ (by rw [hro]; decide), ite_eq_left hok]
    refine Sim.mstep (K := tpnK4 p (n + 1)) rfl (fun _ _ => rfl) fun rn m4 h4 => ?_
    obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
      (ptrListNames_spec p L.alloc L.pnc L.pln (n + 1) _ reco recl) h4
    dsimp only at hW4
    have hrs2 := PSlR0.grow (fun q => decRS_mono q) hrs (hg1.trans hg2)
    obtain ⟨hS4, hg4, hr4, hd4, ht4⟩ := plnW_stage (·.cvR) (fun q => decRS_mono q) decRS_cv decRS_lt hW4 hS2 hrs2
    subst hr4
    refine Sim.mstep (K := tpnK5) rfl (fun _ _ => rfl) fun rd m5 h5 => ?_
    obtain ⟨s5, rfl, -, hm5, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
      (slNodup_spec p L.contains L.nodup (n + 1) _ _ _) h5
    simp only [List.headD_cons, List.tail_cons] at hW5 hm5
    obtain ⟨nws, hns, hnm, hnl⟩ := slR_of_decHL s4.mem _ _ _ hd4 (by rw [ht4]; exact hT _)
    rw [ofNat_toNat_word, ofNat_toNat_word] at hns
    have hnd := nodupW_ok _ _ _ _ _ _ hns hW5
    rw [tpnK5_some, hm5]
    refine Sim.ret ⟨?_, hS4, hg1.trans (hg2.trans hg4)⟩
    simp only [List.headD_cons]
    rw [hnd, hnm, nameNodup_map nws hnl]
    by_cases h : nws.Nodup <;> simp [h]
  · have hro : ro.headD 0 = 0 := by rw [hset, hcond, ite_eq_right hok]
    rw [tpnK3_zero _ _ _ _ _ _ hro, ite_eq_right hok]
    exact Sim.ret ⟨by simp, hS2, hg1.trans hg2⟩

/-- **`target_rec_pins_names`' model refines the twin's name pins** (through the stubs
`intern_nanon`, `name_rec_i`): the members' and recursors' slices of the shape and the auxiliary
recursors' slice decoded below the tops. -/
theorem tpnW_sim (p : Prog) (L : RpLook p) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} (m : Mem) (a : AState) (mo k reco recl auxo auxl : Word) (bs : BlockShape)
    (hS : StageR dn vis fe m a) (hms : PSlR0 decMS bs.members mo k m)
    (hrs : PSlR0 decRS bs.recs reco recl m) (haux : PSlR decRS (rpAux bs) auxo auxl m) :
    Sim (tpnW p (n + 1) m mo k reco recl auxo auxl) (namesTwin bs) a
      (fun r b m' a' => r.headD 0 = (if b then 1 else 0) ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  unfold tpnW namesTwin
  by_cases hk : k = 0
  · rw [ite_eq_left hk]
    have hm : bs.members = [] := hms.nil hk
    have h0 : rpN0 bs = internNNode .anonymous := by unfold rpN0; rw [hm]
    rw [h0]
    refine Sim.bindK (K := tpnK0 p (n + 1) reco recl auxo auxl) rfl (fun _ _ => rfl)
      (show Sim (callW p (n + 1) "intern_nanon" [] m) (internNNode .anonymous) a
        (fun r x m' a' => KeepPost dn vis fe decW0N m m' a' r x) from fun r m' e => by
        obtain ⟨s', rfl, -, hs⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (naF_spec p L.rna (n + 1) _ []) e
        exact naF_ok dn vis fe m s'.mem a r hs hS) ?_
    rintro r0 x0 m0 a0 ⟨hS0, hg0, hx0b, hx0⟩
    refine (tpnB_sim p L n bs reco recl auxo auxl (r0.headD 0) x0 hx0b hx0 m0 a0 hS0
      (hrs.grow (fun q => decRS_mono q) hg0) (haux.grow (fun q => decRS_mono q) hg0)).mono ?_
    rintro r b m' a' ⟨h1, h2, h3⟩
    exact ⟨h1, h2, hg0.trans h3⟩
  · rw [ite_eq_right hk]
    obtain ⟨pc, ms0, ms', hmeq, hw, hpb, hms0, -⟩ := partsPSl_cons (hms.pslr hk) hk
    obtain ⟨⟨ca, hca, hcv⟩, -⟩ := decMS_some (show decMS (truncM m) pc = some ms0 from hms0)
    obtain ⟨hcw, hcab, -⟩ := partsIwRd hca (UInt64.toNat_ofNat_of_lt' hpb)
    obtain ⟨hnl, hne⟩ := partsCVName (IWGrow.refl m) (show DecB (fun m => decCVp m ca) m ms0.cvT from hcv) hcab
    have h0 : rpN0 bs = pure ms0.cvT.name := by unfold rpN0; rw [hmeq]
    rw [h0, hw, hcw]
    refine Sim.bind_twin (x := ms0.cvT.name) rfl ?_
    exact tpnB_sim p L n bs reco recl auxo auxl _ _ hnl hne m a hS hrs haux

end L.Ind

end

end
