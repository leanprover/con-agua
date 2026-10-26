import ConAgua.Arena.RecCheckSpec20
import ConAgua.Arena.IndInstallSpec23
import ConAgua.Arena.IndRealIlpN

/-!
# `RecCheck`: `targetRecPins`' callees (lane `indproofs3`, helper `rec2`)

`block_rec_lps_ok` under the stage relation (the shape decoded below the tops), the split of the
recursors into the block's own and the auxiliary ones (`block_rec_split_own_aux`, the twin's two
`filter`s), and the wanted auxiliary names (`block_rec_want_aux_names`, the twin's `mapM` of
`name_rec_i`).
-/

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

/-- **`block_rec_lps_ok` under the stage relation**: no hypothesis beyond the shape decoded below
the tops. -/
theorem lokW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q : Word} {r : List Word} {bs : BlockShape} (h : lokW n m q = some (r, m'))
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m q.toNat) m bs) :
    r = [if ConRon.Arena.blockRecLpsOk bs then 1 else 0] ∧ StageR dn vis fe m' a ∧ IWGrow m m' := by
  obtain ⟨hI1, -, hsz, hEs, hc⟩ := hS.2
  obtain ⟨hr, hg, hf, hw⟩ := lokW_ok n m m' q r bs h (hq.get (decBS_mono _)) (hq.stab (decBS_mono _))
    (rpShape9 hq) hsz hc hEs
  exact ⟨hr, stage_frame_iw hS hf (by rw [← hf.2.2.1 IW]; exact hw hI1), hg⟩

/-! ## `block_rec_split_own_aux` -/

l_model soa_spec (p : Prog) (hP : IndPartsProg p)
    (hp : p.lookup "block_rec_split_own_aux" = some blockRecSplitOwnAux)
  fns [hp ↦ soaW]
  specs [slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [arena_grind] simp [rdW_eq]

/-- **`block_rec_split_own_aux`'s model is the twin's two `filter`s** (as slices of `RecShape`
pointers decoded below the tops). -/
theorem soaW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (reco recl k : Word) (recs : List RecShape) (r : List Word),
    soaW n m reco recl k = some (r, m') → StageR dn vis fe m a → PSlR decRS recs reco recl m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      PSlR decRS (recs.filter fun rc => decide (rc.tgt < k.toNat)) (r.headD 0) (r.tail.headD 0) m' ∧
      PSlR decRS (recs.filter fun rc => !decide (rc.tgt < k.toNat)) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) m' := by
  induction n with
  | zero => intro m m' a reco recl k recs r h; simp [soaW] at h
  | succ n ih =>
    intro m m' a reco recl k recs r h hS hrs
    by_cases hl : recl = 0
    · rw [soaW.arm1 n m reco recl k hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl; rw [partsPSl_nil hrs]
      exact ⟨hS, IWGrow.refl _, PSlR.nil _ _, PSlR.nil _ _⟩
    rw [soaW.arm2 n m reco recl k hl] at h
    obtain ⟨pc, rs0, rs', rfl, hw, hpb, hrs0, hrs'⟩ := partsPSl_cons hrs hl
    rcases h1 : soaW n m (reco + 1) (recl - 1) k with _ | ⟨r1, m1⟩ <;> rw [h1] at h <;>
      try (simp only [soaW.k_block_rec_split_own_aux, reduceCtorEq] at h; done)
    obtain ⟨hS1, hg1, hown, haux⟩ := ih m m1 a (reco + 1) (recl - 1) k rs' r1 h1 hS hrs'
    -- the recursor's pointer and its target, as the model reads them in `m1`
    have hrlt : reco.toNat < iwTop m := by
      have := hrs.2
      have : recl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
      omega
    have hw1 : rdW (m1.arr64 IW) reco = UInt64.ofNat pc := by rw [partsRdIW_grow hg1 hrlt, hw]
    obtain ⟨-, -, -, htg, -⟩ := decRS_some (show decRS (truncM m) pc = some rs0 from hrs0)
    obtain ⟨htw, htb, htlt⟩ := partsIwRd htg
      (show (UInt64.ofNat pc + 3).toNat = pc + 3 by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hpb]; simp
        have := partsIwLt htg; have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at *; omega)
    have hw3 : rdW (m1.arr64 IW) (rdW (m1.arr64 IW) reco + 3) = UInt64.ofNat rs0.tgt := by
      rw [hw1, partsRdIW_grow hg1 (by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hpb]; simp
        have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at *; omega), htw]
    have hlt : (UInt64.ofNat rs0.tgt < k) = (rs0.tgt < k.toNat) := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' htb]
    have hy : DecB (fun m => decRS m (UInt64.ofNat pc : Word).toNat) m1 rs0 := by
      rw [UInt64.toNat_ofNat_of_lt' hpb]; exact hrs0.grow (decRS_mono _) hg1
    by_cases hc : rs0.tgt < k.toNat
    · rw [soaW.k_block_rec_split_own_aux.arm1 n reco k r1 m1 (by rw [hw3, hlt]; exact hc), hw1] at h
      rcases h2 : consW n m1 (UInt64.ofNat pc) (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r2, m2⟩ <;> simp only [h2, soaW.k_sl_cons, reduceCtorEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS2, hg2, hd2, -⟩ := consW_pslr (fun q => decRS_mono q) h2 hS1 hown hy
      refine ⟨hS2, hg1.trans hg2, ?_, ?_⟩
      · simp only [List.filter_cons, decide_eq_true hc, if_true, List.headD_cons, List.tail_cons]
        exact hd2
      · simp only [List.filter_cons, decide_eq_true hc, Bool.not_true, Bool.false_eq_true, if_false,
          List.headD_cons, List.tail_cons]
        exact haux.grow (fun q => decRS_mono q) hg2
    · rw [soaW.k_block_rec_split_own_aux.arm2 n reco k r1 m1 (by rw [hw3, hlt]; exact hc), hw1] at h
      rcases h2 : consW n m1 (UInt64.ofNat pc) (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0) with _ | ⟨r2, m2⟩ <;> simp only [h2, soaW.k_sl_cons_2, reduceCtorEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS2, hg2, hd2, -⟩ := consW_pslr (fun q => decRS_mono q) h2 hS1 haux hy
      refine ⟨hS2, hg1.trans hg2, ?_, ?_⟩
      · simp only [List.filter_cons, decide_eq_false hc, Bool.false_eq_true, if_false, List.headD_cons,
          List.tail_cons]
        exact hown.grow (fun q => decRS_mono q) hg2
      · simp only [List.filter_cons, decide_eq_false hc, Bool.not_false, if_true, List.headD_cons,
          List.tail_cons]
        exact hd2

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
