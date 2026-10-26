import ConAgua.Arena.PromoteCIRef22

/-!
# `promote_ci` refines `promoteCI`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem nat?_erecP {m : Mem} {i : Nat} {w : Word} (h : i < erecTop m)
    (hw : (m.arr64 EREC)[i]? = some w) : nat? (erecP m) i = some w.toNat := nat?_of_pre h hw

theorem decHint_bound {a : Array Word} {q : Nat} {h : ConLeche.ReducibilityHint}
    (hd : decHint a q = some h) : q < a.size := by
  unfold decHint at hd
  cases hk : nat? a q with
  | none => simp [hk] at hd
  | some t =>
    obtain ⟨w, hw, -⟩ := nat?_get hk
    exact (Array.getElem?_eq_some_iff.mp hw).1

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem ci_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (dn : NIdx → Option ConLeche.Name) (ci : IConstantInfo) (r : List Word) (m' : Mem)
    (hD : ArenaD m a) (hP : PMemoR m pm) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hci : decCI (preE m D) dn q.toNat = some ci) (hDt : D ≤ erecTop m)
    (hc : callW p n "promote_ci" [f, q] m = some (r, m')) :
    ∃ a' pm' ci', (promoteCI pm f.toNat ci).run a = .ok ((pm', ci'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ cp a' = cp a ∧ MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧
      ErecGrow m m' ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧ erecTop m ≤ (r.headD 0).toNat ∧
      (r.headD 0).toNat < erecTop m' ∧ decCI (erecP m') dn (r.headD 0).toNat = some ci' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteCI_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [ciW] at hW
  have hkk : ∃ k, nat? (preE m D) q.toNat = some k := by
    unfold decCI at hci
    cases hk : nat? (preE m D) q.toNat with
    | none => simp [hk] at hci
    | some k => exact ⟨k, rfl⟩
  obtain ⟨kk, hkk⟩ := hkk
  obtain ⟨kw, hkwm, hkwk, hqD0⟩ := nat_word_pre hkk
  obtain ⟨⟨rr, m0⟩, hrd, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm0, hr0, -⟩ := rd1_call p hp hrd
  obtain rfl := hm0.symm
  rw [rd1W_of hsz (by simpa using hkwm)] at hr0
  subst hr0
  simp only [g0, List.headD_cons] at hW
  have hPG : ∀ {i : Nat} {w : Word} {m'' : Mem}, i < erecTop m'' → (m''.arr64 EREC)[i]? = some w →
      nat? (erecP m'') i = some w.toNat := fun hi h => nat?_of_pre hi h
  rcases decCI_cases hci with ⟨cv, hk, hcv, rfl⟩ | ⟨cv, e, hh, hk, hcv, he, hhh, rfl⟩ |
    ⟨cv, hk, hcv, rfl⟩ | ⟨cv, caps, hk, hcv, hcp, rfl⟩ | ⟨cv, np, nf, hk, hcv, hnp, hnf, rfl⟩ |
    ⟨cv, mi, rp, ro, rc, rls, hk, hcv, hmi, hrp, hro, hrc, hrl, rfl⟩
  · -- axiom
    have hK : kk = 0 := (Option.some.inj (hkk.symm.trans hk))
    have hkw0 : kw = 0 := UInt64.toNat_inj.mp (by rw [hkwk, hK]; rfl)
    subst hkw0
    simp only [show ((0:Word) = 0 ∨ (0:Word) = 2) by decide, show ¬((0:Word) = 1) by decide, show ¬((0:Word) = 3) by decide, show ¬((0:Word) = 4) by decide, show ¬((0:Word) = 5) by decide, ↓reduceIte] at hW
    simp only [promoteArmK] at hW
    obtain ⟨⟨dl, m1⟩, hcl, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hr, hm1⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm1
    have hr' : dl.headD 0 = r.headD 0 := hr
    have hpre := preE_size_le m D
    have hb := decCV_bound hcv
    obtain ⟨a', pm1, cv', hrun, hDf, hPf, hcp, hfr, htk, hg, hts', d, hdr, hdlo, hdhi, hkind, hQ⟩ :=
      plain_rel p hp n m a pm f q D cv 0 dl m1 hD hP hsz hts hcv hkwm (by omega) hDt hcl
    refine ⟨a', pm1, .axiomInfo cv', ?_, hDf, hPf, hcp, hfr, htk, hg, hts', ?_, ?_, ?_⟩
    · simp only [promoteCI]; rw [run_bind_ok hrun]; rfl
    · rw [← hr', hdr]; exact hdlo
    · rw [← hr', hdr]; omega
    · rw [← hr', hdr]
      exact decCI_ax (by have h := nat?_erecP (m := m1) (i := d) (by omega) hkind; simpa using h) hQ.1
  · -- defn
    have hK : kk = 1 := (Option.some.inj (hkk.symm.trans hk))
    have hkw0 : kw = 1 := UInt64.toNat_inj.mp (by rw [hkwk, hK]; rfl)
    subst hkw0
    simp only [show ¬((1:Word) = 0 ∨ (1:Word) = 2) by decide, show ((1:Word) = 1) by decide, show ¬((1:Word) = 3) by decide, show ¬((1:Word) = 4) by decide, show ¬((1:Word) = 5) by decide, ↓reduceIte] at hW
    simp only [promoteArmK] at hW
    obtain ⟨⟨dl, m1⟩, hcl, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hr, hm1⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm1
    have hr' : dl.headD 0 = r.headD 0 := hr
    have hpre := preE_size_le m D
    obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some he
    obtain ⟨hlt5, hm5⟩ := preE_get_lt hwv
    have hb6 := decHint_bound hhh
    obtain ⟨a', pm1, x, ⟨aA, pmA, hrun1, hrun2⟩, hDf, hPf, hcp, hfr, htk, hg, hts', d, hdr, hdlo, hdhi,
      hkind, hdcv, hd5, w6, w7, e6, e7, s6, s7⟩ :=
      defn_rel p hp n m a pm f q D cv 1 wv dl m1 hD hP hsz hts hcv hkwm hm5 hwvl (by omega) hDt hcl
    have hrun2' : (promoteE pmA f.toNat (decI wv)).run aA = .ok ((pm1, x.2), a') := hrun2
    have hhint : decHint (erecP m1) (d + 6) = some hh := by
      refine decHint_move' (a := preE m D) (b := erecP m1) (i := q.toNat + 6) (j := d + 6) ?_ ?_ hhh
      · rw [e6, preE_get, ite_eq_left (by omega)]; exact s6.symm
      · by_cases h : q.toNat + 6 + 1 < D
        · right
          have e7' : (erecP m1)[d + 6 + 1]? = some w7 := e7
          rw [e7', preE_get, ite_eq_left h]; exact s7.symm
        · left; rw [preE_get, ite_eq_right h]
    refine ⟨a', pm1, .defnInfo x.1 x.2 hh, ?_, hDf, hPf, hcp, hfr, htk, hg, hts', ?_, ?_, ?_⟩
    · simp only [promoteCI]; rw [run_bind_ok hrun1]; simp only; rw [run_bind_ok hrun2']; rfl
    · rw [← hr', hdr]; exact hdlo
    · rw [← hr', hdr]; omega
    · rw [← hr', hdr]
      exact decCI_df (by have h := nat?_erecP (m := m1) (i := d) (by omega) hkind; simpa using h) hdcv hd5 hhint
  · -- thm
    have hK : kk = 2 := (Option.some.inj (hkk.symm.trans hk))
    have hkw0 : kw = 2 := UInt64.toNat_inj.mp (by rw [hkwk, hK]; rfl)
    subst hkw0
    simp only [show ((2:Word) = 0 ∨ (2:Word) = 2) by decide, show ¬((2:Word) = 1) by decide, show ¬((2:Word) = 3) by decide, show ¬((2:Word) = 4) by decide, show ¬((2:Word) = 5) by decide, ↓reduceIte] at hW
    simp only [promoteArmK] at hW
    obtain ⟨⟨dl, m1⟩, hcl, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hr, hm1⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm1
    have hr' : dl.headD 0 = r.headD 0 := hr
    have hpre := preE_size_le m D
    have hb := decCV_bound hcv
    obtain ⟨a', pm1, cv', hrun, hDf, hPf, hcp, hfr, htk, hg, hts', d, hdr, hdlo, hdhi, hkind, hQ⟩ :=
      plain_rel p hp n m a pm f q D cv 2 dl m1 hD hP hsz hts hcv hkwm (by omega) hDt hcl
    refine ⟨a', pm1, .thmInfo cv', ?_, hDf, hPf, hcp, hfr, htk, hg, hts', ?_, ?_, ?_⟩
    · simp only [promoteCI]; rw [run_bind_ok hrun]; rfl
    · rw [← hr', hdr]; exact hdlo
    · rw [← hr', hdr]; omega
    · rw [← hr', hdr]
      exact decCI_th (by have h := nat?_erecP (m := m1) (i := d) (by omega) hkind; simpa using h) hQ.1
  · -- ind
    have hK : kk = 3 := (Option.some.inj (hkk.symm.trans hk))
    have hkw0 : kw = 3 := UInt64.toNat_inj.mp (by rw [hkwk, hK]; rfl)
    subst hkw0
    simp only [show ¬((3:Word) = 0 ∨ (3:Word) = 2) by decide, show ¬((3:Word) = 1) by decide, show ((3:Word) = 3) by decide, show ¬((3:Word) = 4) by decide, show ¬((3:Word) = 5) by decide, ↓reduceIte] at hW
    simp only [promoteArmK] at hW
    obtain ⟨⟨dl, m1⟩, hcl, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hr, hm1⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm1
    have hr' : dl.headD 0 = r.headD 0 := hr
    have hpre := preE_size_le m D
    have hb := decCaps_bound hcp
    obtain ⟨a', pm1, x, ⟨aA, pmA, hrun1, hrun2⟩, hDf, hPf, hcp', hfr, htk, hg, hts', d, hdr, hdlo, hdhi,
      hkind, hdcv, hdcaps⟩ :=
      ind_rel p hp n m a pm f q D dn cv caps 3 dl m1 hD hP hsz hts hcv hcp hkwm (by omega) hDt hcl
    refine ⟨a', pm1, .indInfo x.1 x.2, ?_, hDf, hPf, hcp', hfr, htk, hg, hts', ?_, ?_, ?_⟩
    · simp only [promoteCI]; rw [run_bind_ok hrun1]; simp only; rw [run_bind_ok hrun2]; rfl
    · rw [← hr', hdr]; exact hdlo
    · rw [← hr', hdr]; omega
    · rw [← hr', hdr]
      exact decCI_in (by have h := nat?_erecP (m := m1) (i := d) (by omega) hkind; simpa using h) hdcv hdcaps
  · -- ctor
    have hK : kk = 4 := (Option.some.inj (hkk.symm.trans hk))
    have hkw0 : kw = 4 := UInt64.toNat_inj.mp (by rw [hkwk, hK]; rfl)
    subst hkw0
    simp only [show ¬((4:Word) = 0 ∨ (4:Word) = 2) by decide, show ¬((4:Word) = 1) by decide, show ¬((4:Word) = 3) by decide, show ((4:Word) = 4) by decide, show ¬((4:Word) = 5) by decide, ↓reduceIte] at hW
    simp only [promoteArmK] at hW
    obtain ⟨⟨dl, m1⟩, hcl, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hr, hm1⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm1
    have hr' : dl.headD 0 = r.headD 0 := hr
    have hpre := preE_size_le m D
    obtain ⟨w5, hw5, rfl, hlt5⟩ := nat_word_pre hnp
    obtain ⟨w6, hw6, rfl, hlt6⟩ := nat_word_pre hnf
    obtain ⟨a', pm1, cv', hrun, hDf, hPf, hcp', hfr, htk, hg, hts', d, hdr, hdlo, hdhi,
      hkind, hdcv, hn5, hn6⟩ :=
      ctor_rel p hp n m a pm f q D cv 4 w5 w6 dl m1 hD hP hsz hts hcv hkwm hw5 hw6 (by omega) hDt hcl
    refine ⟨a', pm1, .ctorInfo cv' w5.toNat w6.toNat, ?_, hDf, hPf, hcp', hfr, htk, hg, hts', ?_, ?_, ?_⟩
    · simp only [promoteCI]; rw [run_bind_ok hrun]; rfl
    · rw [← hr', hdr]; exact hdlo
    · rw [← hr', hdr]; omega
    · rw [← hr', hdr]
      exact decCI_ct (by have h := nat?_erecP (m := m1) (i := d) (by omega) hkind; simpa using h) hdcv (by simp [nat?, hn5]) (by simp [nat?, hn6])
  · -- rec
    have hK : kk = 5 := (Option.some.inj (hkk.symm.trans hk))
    have hkw0 : kw = 5 := UInt64.toNat_inj.mp (by rw [hkwk, hK]; rfl)
    subst hkw0
    simp only [show ¬((5:Word) = 0 ∨ (5:Word) = 2) by decide, show ¬((5:Word) = 1) by decide, show ¬((5:Word) = 3) by decide, show ¬((5:Word) = 4) by decide, show ((5:Word) = 5) by decide, ↓reduceIte] at hW
    simp only [promoteArmK] at hW
    obtain ⟨⟨dl, m1⟩, hcl, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hr, hm1⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm1
    have hr' : dl.headD 0 = r.headD 0 := hr
    have hpre := preE_size_le m D
    obtain ⟨w5, hw5, rfl, hlt5⟩ := nat_word_pre hmi
    obtain ⟨w6, hw6, rfl, hlt6⟩ := nat_word_pre hrp
    obtain ⟨w7, hw7, rfl, hlt7⟩ := nat_word_pre hro
    obtain ⟨w8, hw8, rfl, hlt8⟩ := nat_word_pre hrc
    obtain ⟨a', pm1, x, ⟨aA, pmA, hrun1, hrun2⟩, hDf, hPf, hcp', hfr, htk, hg, hts', d, hdr, hdlo, hdhi,
      hkind, hdcv, hn5, hn6, hn8, pw, hn7, hdr7⟩ :=
      rec_rel p hp n m a pm f q D cv rls 5 w5 w6 w7 w8 dl m1 hD hP hsz hts hcv hkwm hw5 hw6 hw7 hw8
        hrl (by omega) hDt hcl
    refine ⟨a', pm1, .recInfo x.1 w5.toNat w6.toNat x.2, ?_, hDf, hPf, hcp', hfr, htk, hg, hts', ?_, ?_, ?_⟩
    · simp only [promoteCI]; rw [run_bind_ok hrun1]; simp only; rw [run_bind_ok hrun2]; rfl
    · rw [← hr', hdr]; exact hdlo
    · rw [← hr', hdr]; omega
    · rw [← hr', hdr]
      exact decCI_rc (by have h := nat?_erecP (m := m1) (i := d) (by omega) hkind; simpa using h) hdcv hn5 hn6 hn7 hn8 hdr7

end rel

end L.Arena
