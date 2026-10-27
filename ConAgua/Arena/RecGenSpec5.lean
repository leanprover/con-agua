import ConAgua.Arena.IlpRd
import ConAgua.Arena.IndPartsSpec3
import ConAgua.Arena.RecClassSpecB
import ConAgua.Arena.RecClassSpecE
import ConAgua.Arena.RecGenSpec2

/-!
# `RecGen`: `classFormerTy` (lane `indproofs2`, helper `rec`)
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Model -/

def cftK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => some ([r4.headD 0], m4)

def cftK3 (cR : CallM) (N : Nat) (mp q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => cftK4 (cR N "inst_lp_fast"
      [CWF, r3.headD 0, r3.tail.headD 0, rdW (m3.arr64 IW) (mp + 1), rdW (m3.arr64 EREC) (q + 4)] m3)

def cftK2 (cR : CallM) (N : Nat) (mp : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then none
    else if rdW (m2.arr64 EREC) (r2.tail.headD 0) ≠ 3 then none
    else cftK3 cR N mp (r2.tail.headD 0) (erToIwW N m2 (rdW (m2.arr64 EREC) (r2.tail.headD 0 + 2))
      (rdW (m2.arr64 EREC) (r2.tail.headD 0 + 3)))

def cftK1 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (e, m1) => if 4294967296 ≤ e then none else some ([e], m1)

/-- **The model of `class_former_ty`** (its `inst_lp_fast` read through `cR`). -/
def cftW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | N + 1, m, vis, o, l, mp =>
    if rdW (m.arr64 IW) (mp + 8) ≠ 0 then
      if rdW (m.arr64 IW) (mp + 8) - 1 < l then
        some ([rdW (m.arr64 EREC) (rdW (m.arr64 IW) (o + (rdW (m.arr64 IW) (mp + 8) - 1)) + 3)], m)
      else cftK1 (binternW m 0)
    else cftK2 cR N mp (envFindW m (rdW (m.arr64 IW) mp) vis)

section arms
variable (cR : CallM) (N : Nat) (m m1 m2 m3 m4 : Mem) (vis o l mp q e : Word) (r2 r3 r4 : List Word)
theorem cftW_mem (h : rdW (m.arr64 IW) (mp + 8) ≠ 0) (h2 : rdW (m.arr64 IW) (mp + 8) - 1 < l) :
    cftW cR (N + 1) m vis o l mp =
      some ([rdW (m.arr64 EREC) (rdW (m.arr64 IW) (o + (rdW (m.arr64 IW) (mp + 8) - 1)) + 3)], m) := by
  simp only [cftW]; rw [ite_eq_left h, ite_eq_left h2]
theorem cftW_out (h : rdW (m.arr64 IW) (mp + 8) ≠ 0) (h2 : ¬ rdW (m.arr64 IW) (mp + 8) - 1 < l) :
    cftW cR (N + 1) m vis o l mp = cftK1 (binternW m 0) := by
  simp only [cftW]; rw [ite_eq_left h, ite_eq_right h2]
theorem cftW_ext (h : ¬ rdW (m.arr64 IW) (mp + 8) ≠ 0) :
    cftW cR (N + 1) m vis o l mp = cftK2 cR N mp (envFindW m (rdW (m.arr64 IW) mp) vis) := by
  simp only [cftW]; rw [ite_eq_right h]
theorem cftK1_some : cftK1 (some (e, m1)) = if 4294967296 ≤ e then none else some ([e], m1) := rfl
theorem cftK2_some : cftK2 cR N mp (some (r2, m2)) =
    if r2.headD 0 = 0 then none
    else if rdW (m2.arr64 EREC) (r2.tail.headD 0) ≠ 3 then none
    else cftK3 cR N mp (r2.tail.headD 0) (erToIwW N m2 (rdW (m2.arr64 EREC) (r2.tail.headD 0 + 2))
      (rdW (m2.arr64 EREC) (r2.tail.headD 0 + 3))) := rfl
theorem cftK3_some : cftK3 cR N mp q (some (r3, m3)) = cftK4 (cR N "inst_lp_fast"
      [CWF, r3.headD 0, r3.tail.headD 0, rdW (m3.arr64 IW) (mp + 1), rdW (m3.arr64 EREC) (q + 4)] m3) := rfl
theorem cftK4_some : cftK4 (some (r4, m4)) = some ([r4.headD 0], m4) := rfl
end arms

grind_pattern [ind_grind] cftW_mem => cftW cR (N + 1) m vis o l mp
grind_pattern [ind_grind] cftW_out => cftW cR (N + 1) m vis o l mp
grind_pattern [ind_grind] cftW_ext => cftW cR (N + 1) m vis o l mp
grind_pattern [ind_grind] cftK1_some => cftK1 (some (e, m1))
grind_pattern [ind_grind] cftK2_some => cftK2 cR N mp (some (r2, m2))
grind_pattern [ind_grind] cftK3_some => cftK3 cR N mp q (some (r3, m3))
grind_pattern [ind_grind] cftK4_some => cftK4 (some (r4, m4))

/-- The lookups `class_former_ty` needs. -/
structure CftProg (p : Prog) : Prop where
  ix : p.lookup "env_ix" = some envIxL
  rowGet : p.lookup "env_row_get" = some envRowGetL
  find : p.lookup "env_find" = some envFindL
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "er_copy" = some erCopy
  eti : p.lookup "er_to_iw" = some erToIw
  bf : p.lookup "bvar_find" = some bvarFind
  bp : p.lookup "bvar_push" = some bvarPush
  ib : p.lookup "intern_bvar" = some internBVar
  cft : p.lookup "class_former_ty" = some classFormerTyL

theorem classFormerTy_spec (p : Prog) (h : CftProg p) (cR : CallM) (hcR : CallSpec p cR) (N : Nat) (s₀ : St)
    (vis o l mp : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_former_ty" [vis, o, l, mp]
    ⦃fun r s' => LocEq s' s₀ ∧ cftW cR N s₀.mem vis o l mp = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.cft]
  simp only [callFn, classFormerTyL]
  cases N with
  | zero => vcgen [exec] <;> grind
  | succ N =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        internBVar_spec p h.bf h.bp h.ib N, envFind_specW p h.ix h.rowGet h.find N,
        erToIw_specW p h.alloc h.copy h.eti N, hcR N "inst_lp_fast"] <;>
      finish (gen := 20) [rdW_eq]

/-! ## Relational lemma -/

theorem decCI_ind_cv {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat} {cv : IConstantVal}
    {caps : IIndCaps} (h : decCI a dn q = some (.indInfo cv caps)) : decCV a (q + 1) = some cv := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  match k, h with
  | 0, h => simp [Option.bind_eq_some_iff] at h
  | 1, h => simp only [Option.bind_eq_some_iff, Option.some.injEq] at h; obtain ⟨_, _, _, _, _, _, h⟩ := h; cases h
  | 2, h => simp [Option.bind_eq_some_iff] at h
  | 3, h =>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv', hcv, caps', -, he⟩ := h
    cases he; exact hcv
  | 4, h => simp only [Option.bind_eq_some_iff, Option.some.injEq] at h; obtain ⟨_, _, _, _, _, _, h⟩ := h; cases h
  | 5, h => simp only [Option.bind_eq_some_iff, Option.some.injEq] at h; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h; cases h
  | 6, h => simp at h
  | (_ + 7), h => simp at h

theorem decTM_lvls' {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    iwH m (p + 1) = some M.lvls := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨w5, h5, a1, ha1, w4, h4, w3, h3, w2, h2, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h
  exact ha1

theorem cftW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {N : Nat} {m m' : Mem} {o l mp : Word} {r : List Word} {M : TargetMajor} {cvTas : List IConstantVal}
    (cR : CallM) (hI : IlpRd cR dn vis fe (IlpBase m a))
    (h : cftW cR N m vis o l mp = some (r, m')) (hS : StageR dn vis fe m a)
    (hM : DecB (fun m => decTM m mp.toNat) m M) (hcv : decPL m (decCVp m) o.toNat l.toNat = some cvTas)
    (hol : o.toNat + l.toNat < 2 ^ 64) :
    ∃ x a', (ConRon.Arena.classFormerTy fe cvTas M).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decW0E m' r x ∧ AFr m m' := by
  cases N with
  | zero => simp [cftW] at h
  | succ N =>
  have hsz := hS.2.2.2.1
  have hM0 := hM.get (decTM_mono _)
  obtain ⟨k, hk, hmem⟩ := decTM_member hM0
  have hrk := iwN_rdW_at (w := mp) (k := 8) hk hsz
  rw [show UInt64.ofNat 8 = (8 : Word) from rfl] at hrk
  have hlen := decPL_length m hcv
  by_cases hk0 : rdW (m.arr64 IW) (mp + 8) ≠ 0
  · have hk0' : k ≠ 0 := by intro e; apply hk0; rw [hrk.1, e]; rfl
    have hmem' : M.member = some (k - 1) := by rw [hmem]; simp [decON, hk0']
    have hkw : rdW (m.arr64 IW) (mp + 8) - 1 = UInt64.ofNat (k - 1) := by
      rw [hrk.1]; apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hrk.2]; simp; omega),
        UInt64.toNat_ofNat_of_lt' hrk.2, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; have := hrk.2; omega)]
      simp
    by_cases hlt : rdW (m.arr64 IW) (mp + 8) - 1 < l
    · rw [cftW_mem (h := hk0) (h2 := hlt)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hkw] at hlt ⊢
      have hlt' : k - 1 < l.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp hlt
        rwa [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; have := hrk.2; omega)] at this
      obtain ⟨v, hv, hcvv⟩ := decPL_getH m hcv (k - 1) hlt'
      have hrv := iwN_rdW_at (w := o) (k := k - 1) hv hsz
      rw [hrv.1]
      have hv64 := hrv.2
      have hty := decCVp_type (q := UInt64.ofNat v) (by rw [UInt64.toNat_ofNat_of_lt' hv64]; exact hcvv)
        (by
          rw [UInt64.toNat_ofNat_of_lt' hv64]
          have := hS.2.2.2.2.1
          simp only [decCVp, decCV, bind, Option.bind_eq_some_iff] at hcvv
          obtain ⟨_, _, _, _, _, hty, -⟩ := hcvv
          obtain ⟨w, hw, -⟩ := hd?_some hty
          have := (Array.getElem?_eq_some_iff.mp hw).1
          simp only [erA] at this; omega)
      refine ⟨_, a, ?_, hS, IWGrow.refl m, ⟨hty.1, hty.2⟩, AFr.refl _⟩
      simp only [ConRon.Arena.classFormerTy, hmem', List.getElem?_eq_getElem (by omega : k - 1 < cvTas.length)]
      rfl
    · rw [cftW_out (h := hk0) (h2 := hlt)] at h
      obtain ⟨⟨e, m1⟩, hb, h⟩ := of_K h rfl
      rw [cftK1_some] at h
      obtain ⟨hbig, h⟩ := of_ite_none h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨a1, hrun, hS1, hg1⟩ := internBVar_stage hS 0 hb
      have hge : ¬ k - 1 < cvTas.length := by
        rw [hkw] at hlt; intro h'; apply hlt
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; have := hrk.2; omega)]
        omega
      refine ⟨_, a1, ?_, hS1, hg1, ⟨?_, rfl⟩, binternW_afr hb⟩
      · simp only [ConRon.Arena.classFormerTy, hmem', List.getElem?_eq_none (by omega : cvTas.length ≤ k - 1)]
        exact hrun
      · show e.toNat < 2 ^ 32
        have : ¬ (4294967296 : Word).toNat ≤ e.toNat := fun x => hbig (UInt64.le_iff_toNat_le.mpr x); simpa using this
  · rw [cftW_ext (h := hk0)] at h
    have hk00 : k = 0 := by
      have := congrArg UInt64.toNat ((show rdW (m.arr64 IW) (mp + 8) = 0 by simpa using hk0).symm.trans hrk.1)
      rw [UInt64.toNat_ofNat_of_lt' hrk.2] at this; exact this.symm
    have hmem' : M.member = none := by rw [hmem, hk00]; rfl
    obtain ⟨wi, hwi, hwiH, hwiE⟩ := iwH_rdW_at (w := mp) (k := 0) (by simpa using decTM_ind hM0) hsz
    rw [show mp + UInt64.ofNat 0 = mp by simp] at hwi
    rw [hwi] at h
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl
    rw [cftK2_some] at h
    obtain ⟨hm2, hfind, hdec⟩ := envFindW_found h2 hS.1.env hwiH
    subst m2
    obtain ⟨hf0, h⟩ := of_ite_none h
    obtain ⟨hk3, h⟩ := of_ite_none h
    obtain ⟨ci, hci⟩ := hdec hf0
    have hfci : fe.find? M.ind = some ci := by rw [← hwiE, hfind, decFound, ite_eq_right hf0, hci]
    obtain ⟨kk, hkk, hcase⟩ := decCI_ind_cases hci
    have hkr := erec_nat (w := r2.tail.headD 0) (c := 0) (by simpa using hkk) (by decide)
    rw [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at hkr
    have hkind : kk = 3 := by
      have := congrArg UInt64.toNat ((show rdW (m.arr64 EREC) (r2.tail.headD 0) = 3 by simpa using hk3).symm.trans hkr.1)
      rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; exact hkr.2)] at this; exact this.symm
    obtain ⟨-, cv, caps, rfl, -⟩ := hcase.resolve_right (fun ⟨hne, _⟩ => hne hkind)
    have hcvP := decCI_ind_cv hci
    have hcvA : decCV (erA m) ((r2.tail.headD 0).toNat + 1) = some cv :=
      ArrExt.decCV (IWGrow.erecExt (IWGrow.refl m)) hcvP
    obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hcvA
    have hqE := (Array.getElem?_eq_some_iff.mp hw2).1
    have hE64 := hS.2.2.2.2.1
    have e1 : rdW (m.arr64 EREC) (r2.tail.headD 0 + 2) = w1 :=
      rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hqE ⊢; omega) hw1
    have e2 : rdW (m.arr64 EREC) (r2.tail.headD 0 + 3) = w2 :=
      rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hqE ⊢; omega) hw2
    rw [e1, e2] at h
    have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m.arr64 EREC).size := by
      rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
      · exact .inl h0
      · exact .inr (hslice?_bound _ _ _ _ hsl h0)
    obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl
    rw [cftK3_some] at h
    obtain ⟨-, hr3t, hdec3, hS3, hg3, -⟩ := L.Arena.erToIwW_stage h3 hS hsrc
    rw [hr3t] at h
    have hdecL : decHL m3 (r3.headD 0).toNat w2.toNat = some cv.levelParams := by rw [hdec3]; exact hsl
    have hM3 : decTM m3 mp.toNat = some M := hM.stab (decTM_mono _) m3 hg3
    obtain ⟨wu, hwu, hwuH, hwuE⟩ := iwH_rdW_at (w := mp) (k := 1) (decTM_lvls' hM3) hS3.2.2.2.1
    rw [show UInt64.ofNat 1 = (1 : Word) from rfl] at hwu
    have hcv3 : decCV (erA m3) ((r2.tail.headD 0).toNat + 1) = some cv :=
      ArrExt.decCV (IWGrow.erecExt hg3) hcvP
    obtain ⟨wt, hwt, hwtH, hwtE⟩ := decCV_typeW hcv3
    have hqE3 := (Array.getElem?_eq_some_iff.mp hwt).1
    have hE364 := hS3.2.2.2.2.1
    have et : rdW (m3.arr64 EREC) (r2.tail.headD 0 + 4) = wt :=
      rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hqE3 ⊢; omega) hwt
    rw [hwu, et] at h
    obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h rfl
    rw [cftK4_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨x, a4, hrun4, ⟨hS4, hg4, hx4⟩, -, hA4⟩ := hI N CWF (r3.headD 0) w2 wu wt cv.levelParams m3 m4 a r4
      hwuH hwtH ⟨rfl, erToIwW_iwFr h3⟩ hS3 hdecL h4
    rw [CWF_eq, hwuE, ← hwtE] at hrun4
    refine ⟨x, a4, ?_, hS4, hg3.trans hg4, hx4, (erToIwW_afr h3).trans hA4⟩
    simp only [ConRon.Arena.classFormerTy, hmem', hfci]
    exact hrun4

end L.Ind
