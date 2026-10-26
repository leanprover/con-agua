import ConAgua.Arena.PromoteCIRef23

/-!
# `promote_ci_list` refines `promoteCIList`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem promoteCIList_nil (pm : PMemo) (fuel : Nat) : promoteCIList pm fuel [] = pure (pm, []) := by
  rw [promoteCIList]
theorem promoteCIList_cons (pm : PMemo) (fuel : Nat) (c : IConstantInfo) (cs : List IConstantInfo) :
    promoteCIList pm fuel (c :: cs) = (do
      let (m, c) ← promoteCI pm fuel c
      let (m, cs) ← promoteCIList m fuel cs
      pure (m, c :: cs)) := by
  rw [promoteCIList]

/-- The constants at `ECON` positions `j, j - 1, …`, decoded in the pool `A`, are `cs`. -/
def ConstsAt (dn : NIdx → Option ConLeche.Name) (A E : Array Word) : Nat → List IConstantInfo → Prop
  | _, [] => True
  | j, ci :: cs => (∃ ptr : Word, E[j]? = some ptr ∧ decCI A dn ptr.toNat = some ci) ∧
      ConstsAt dn A E (j - 1) cs

theorem ConstsAt.mono {dn : NIdx → Option ConLeche.Name} {A A' E E' : Array Word}
    (hA : ArrExt A A') : ∀ (cs : List IConstantInfo) (j : Nat), cs.length ≤ j + 1 →
    (∀ i, i ≤ j → j + 1 ≤ i + cs.length → E'[i]? = E[i]?) → ConstsAt dn A E j cs →
    ConstsAt dn A' E' j cs
  | [], _, _, _, _ => trivial
  | ci :: cs, j, hl, hE, ⟨⟨ptr, hp, hd⟩, hrest⟩ => by
    refine ⟨⟨ptr, by rw [hE j (Nat.le_refl _) (by simp)]; exact hp, hA.decCI hd⟩, ?_⟩
    refine ConstsAt.mono hA cs (j - 1) (by simp at hl; omega) (fun i hi1 hi2 => ?_) hrest
    simp only [List.length_cons] at hE hl
    exact hE i (by omega) (by omega)

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem ciList_rel (dn : NIdx → Option ConLeche.Name) : ∀ (n : Nat) (m : Mem) (a : AState)
    (pm : PMemo) (f j k : Word) (D : Nat) (installed : List IConstantInfo) (r : List Word)
    (m' : Mem), ArenaD m a → PMemoR m pm → (m.arr64 EREC).size < 2 ^ 64 →
    erecTop m ≤ (m.arr64 EREC).size → k.toNat = installed.length →
    installed.length ≤ j.toNat + 1 →
    ConstsAt dn (preE m D) (m.arr64 ECON) j.toNat installed → D ≤ erecTop m →
    callW p n "promote_ci_list" [f, j, k] m = some (r, m') →
    ∃ a' pm' installed', (promoteCIList pm f.toNat installed).run a = .ok ((pm', installed'), a') ∧
      ArenaD m' a' ∧ PMemoR m' pm' ∧ cp a' = cp a ∧
      MemFrame (ECON :: EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧ ErecGrow m m' ∧
      erecTop m' ≤ (m'.arr64 EREC).size ∧ installed'.length = installed.length ∧
      ConstsAt dn (erecP m') (m'.arr64 ECON) j.toNat installed' ∧
      (∀ i, (j.toNat < i ∨ i + installed.length ≤ j.toNat) →
        (m'.arr64 ECON)[i]? = (m.arr64 ECON)[i]?) ∧
      (m'.arr64 ECON).size = (m.arr64 ECON).size := by
  intro n
  induction n with
  | zero => intro m a pm f j k D installed r m' _ _ _ _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m a pm f j k D installed r m' hD hP hsz hts hk hj hcon hDt hc
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteCIList_spec p hp n ⟨m, Locals.init []⟩ f j k) hc
  simp only at hW
  rw [hs'] at hW
  simp only [ciListW] at hW
  cases installed with
  | nil =>
    have hk0 : k = 0 := UInt64.toNat_inj.mp (by simpa using hk)
    rw [ite_eq_left hk0] at hW
    have hm : m = m' := Option.some.inj hW
    subst hm
    refine ⟨a, pm, [], ?_, hD, hP, rfl, MemFrame.refl _ _ _, TierKeep.refl _, ErecGrow.refl _, hts, rfl, trivial,
      fun _ _ => rfl, rfl⟩
    rw [promoteCIList_nil]; rfl
  | cons ci cs =>
    have hk0 : k ≠ 0 := by
      intro h; rw [h] at hk; simp at hk
    rw [ite_eq_right hk0] at hW
    obtain ⟨⟨ptr, hptr, hdec⟩, hrest⟩ := hcon
    have hbd := (Array.getElem?_eq_some_iff.mp hptr).1
    rw [ite_eq_right (by omega)] at hW
    have hrd : rdW (m.arr64 ECON) j = ptr := by
      rw [pci_rdW_of_get? _ j (by simpa using hptr)]
    rw [hrd] at hW
    obtain ⟨⟨dl, m1⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨a1, pm1, ci', hrun1, hD1, hP1, hcp1, hfr1, htk1, hg1, hts1, hlo, hhi, hdec1⟩ :=
      ci_rel p hp n m a pm f ptr D dn ci dl m1 hD hP hsz hts hdec hDt hca
    have hE1 : m1.arr64 ECON = m.arr64 ECON := hfr1.1 ECON (by decide) (by decide)
    have hsz1 : (m1.arr64 EREC).size < 2 ^ 64 := by rw [hg1.2.2]; exact hsz
    rw [ite_eq_right (by rw [hE1]; omega)] at hW
    cases hcb : callW p n "promote_ci_list" [f, j - 1, k - 1] (m1.set64 ECON j (dl.headD 0)) with
    | none => rw [hcb] at hW; cases hW
    | some x =>
    obtain ⟨z, m3⟩ := x
    rw [hcb, memK_some] at hW
    have hm3 : m3 = m' := Option.some.inj hW
    subst hm3
    have hE2 : (m1.set64 ECON j (dl.headD 0)).arr64 ECON = (m1.arr64 ECON).set! j.toNat (dl.headD 0) :=
      Mem.arr64_set64_same _ _ _ _
    have hfs : MemFrame [ECON] [] m1 (m1.set64 ECON j (dl.headD 0)) :=
      MemFrame.set64 m1 ECON (by decide) _ _
    have hlenk : (k - 1).toNat = cs.length := by
      rw [toNat_sub1 k hk0]; simp at hk; omega
    have hjn : cs = [] ∨ j ≠ 0 := by
      by_cases h : j = 0
      · left
        cases cs with
        | nil => rfl
        | cons c0 cs0 => simp only [List.length_cons] at hj; rw [h] at hj; simp at hj
      · exact .inr h
    have hj1 : cs.length ≤ (j - 1).toNat + 1 := by
      rcases hjn with h | h
      · subst h; simp
      · rw [toNat_sub1 j h]; simp only [List.length_cons] at hj; have := toNat_pred j h; omega
    have hcsj : cs.length + 1 ≤ j.toNat + 1 := by simpa using hj
    obtain ⟨hDf, hPf⟩ : ArenaD (m1.set64 ECON j (dl.headD 0)) a1 ∧
        PMemoR (m1.set64 ECON j (dl.headD 0)) pm1 :=
      ⟨⟨ArenaR.frame_ext _ _ (by simp [ECON]) (by simp) m1 _ hfs a1 hD1.1,
        DerR.frameM _ _ m1 _ hfs (by simp [ECON]) a1 hD1.2⟩,
        hP1.frame (by simp [ECON]) (by simp) hfs⟩
    have hEE : (m1.set64 ECON j (dl.headD 0)).arr64 EREC = m1.arr64 EREC :=
      Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have hT2 : erecTop (m1.set64 ECON j (dl.headD 0)) = erecTop m1 := by
      simp only [erecTop]; rw [hfs.2.1 129 (by simp)]
    have hg12 : ErecGrow m1 (m1.set64 ECON j (dl.headD 0)) := ErecGrow.of_eq hEE hT2
    have hP2e : erecP (m1.set64 ECON j (dl.headD 0)) = erecP m1 := by
      rw [erecP_eq_preE, erecP_eq_preE, hT2]; exact preE_congr hEE _
    have hg02 : ErecGrow m m1 := hg1
    have hEcon : ∀ i, i ≠ j.toNat → ((m1.set64 ECON j (dl.headD 0)).arr64 ECON)[i]? = (m.arr64 ECON)[i]? := by
      intro i hi
      rw [hE2, arr_set!_get?, ite_eq_right (by omega), hE1]
    have hcon' : ConstsAt dn (preE (m1.set64 ECON j (dl.headD 0)) D)
        ((m1.set64 ECON j (dl.headD 0)).arr64 ECON) (j - 1).toNat cs := by
      rcases hjn with h | h
      · subst h; trivial
      · rw [toNat_sub1 j h]
        refine ConstsAt.mono (A := preE m D) ?_ cs (j.toNat - 1) (by have := toNat_pred j h; omega)
          (fun i hi1 hi2 => hEcon i (by have := toNat_pred j h; omega)) hrest
        exact preE_ext (fun i hi => by
          rw [hEE]; exact hg1.2.1 i (by omega))
    obtain ⟨a3, pm3, cs', hrun3, hD3, hP3, hcp3, hfr3, htk3, hg3, hts3, hlen3, hcons3, hout3, hsz3E⟩ :=
      ih (m1.set64 ECON j (dl.headD 0)) a1 pm1 f (j - 1) (k - 1) D cs z m3 hDf hPf
        (by rw [hEE]; exact hsz1) (by rw [hEE, hT2]; exact hts1) hlenk hj1 hcon'
        (by rw [hT2]; have := hg1.1; omega) hcb
    have hext : ErecGrow m1 m3 := hg12.trans hg3
    refine ⟨a3, pm3, ci' :: cs', ?_, hD3, hP3, hcp3.trans hcp1, ?_,
      htk1.trans ((TierKeep.of_frame hfs (by simp)).trans htk3), hg1.trans hext, hts3, ?_, ?_, ?_, ?_⟩
    · rw [promoteCIList_cons, run_bind_ok hrun1]
      simp only
      rw [run_bind_ok hrun3]; rfl
    · exact ((hfr1.mono (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h)).trans (hfs.mono (by simp) (by simp))).trans hfr3
    · simp [hlen3]
    · have hj_out : (j - 1).toNat < j.toNat ∨ j.toNat + cs.length ≤ (j - 1).toNat := by
        rcases hjn with h | h
        · subst h; simp; omega
        · rw [toNat_sub1 j h]; have := toNat_pred j h; omega
      have hbd' : j.toNat < (m1.arr64 ECON).size := by rw [hE1]; exact hbd
      refine ⟨⟨dl.headD 0, ?_, hext.ext.decCI hdec1⟩, ?_⟩
      · rw [hout3 _ hj_out, hE2, arr_set!_get?, ite_eq_left ⟨rfl, hbd'⟩]
      · rcases hjn with h | h
        · subst h; have : cs' = [] := List.length_eq_zero_iff.mp (by simpa using hlen3)
          subst this; trivial
        · rw [← toNat_sub1 j h]; exact hcons3
    · intro i hi
      simp only [List.length_cons] at hi
      have hne : i ≠ j.toNat := by omega
      have hi' : (j - 1).toNat < i ∨ i + cs.length ≤ (j - 1).toNat := by
        rcases hjn with h | h
        · subst h; simp; omega
        · rw [toNat_sub1 j h]; have := toNat_pred j h; omega
      rw [hout3 i hi', hEcon i hne]
    · rw [hsz3E, hE2]; simp [hE1]

end rel

end L.Arena
