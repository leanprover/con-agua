import ConAgua.L.ModelGen
import ConAgua.Arena.DeclNatCv

/-!
# The structural-`Nat` gate: stored definitions and the guard (lane `decls3`, helper `decls3-nat`)

`nat_op_deps_stored`, `bool_ctor_ok`, `nat_op_guard`, `nat_op_cod`, `nat_op_ty_pinned`,
`nat_op_stored_ok`, `nat_op_stored_ok_all` against the twin, on `DeclNatBase.lean`'s `CallRef`s.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- Stored as a level-monomorphic definition. -/
def defnMono : IConstantInfo → Bool
  | .defnInfo cv _ _ => cv.levelParams.isEmpty
  | _ => false

theorem decCI_defn_cases {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} (h : decCI a dn p = some ci) :
    (∃ cv v hint, ci = .defnInfo cv v hint ∧ a[p]? = some 1 ∧ decCV a (p + 1) = some cv) ∨
    (∃ w, a[p]? = some w ∧ w ≠ 1 ∧ ∀ cv v hint, ci ≠ .defnInfo cv v hint) := by
  unfold decCI at h
  cases hk : nat? a p with
  | none => simp [hk] at h
  | some k =>
  have hw : ∃ w, a[p]? = some w ∧ w.toNat = k := by
    simp only [nat?, Option.map_eq_some_iff] at hk
    obtain ⟨w, hw, hk⟩ := hk; exact ⟨w, hw, hk⟩
  obtain ⟨w, hw, hwk⟩ := hw
  rw [hk] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨a1, ha1, h⟩ := h
  cases ha1
  by_cases h1 : k = 1
  · subst h1
    left
    simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, v, hv, hh, hhint, rfl⟩ := h
    have : w = 1 := UInt64.toNat_inj.mp (by simpa using hwk)
    exact ⟨cv, v, hh, rfl, by rw [hw, this], hcv⟩
  · right
    refine ⟨w, hw, ?_, ?_⟩
    · intro e; apply h1; rw [← hwk, e]; rfl
    · intro cv v hint e; subst e
      rcases k with _ | _ | _ | _ | _ | _ | _ | k
      · simp [Option.bind_eq_some_iff] at h
      · exact h1 rfl
      all_goals simp [Option.bind_eq_some_iff] at h

theorem decCV_lps_len {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    ∃ w, a[q + 2]? = some w ∧ w.toNat = cv.levelParams.length := by
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := (by
    simp only [decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨nm, -, lv, hlv, ty, -, rfl⟩ := h
    simp only [hlist?, bind, Option.bind_eq_some_iff] at hlv
    obtain ⟨o', ho2, l', hl2, hsl⟩ := hlv
    simp only [nat?, Option.map_eq_some_iff] at ho2 hl2
    obtain ⟨w1, hw1, rfl⟩ := ho2
    obtain ⟨w2, hw2, rfl⟩ := hl2
    exact ⟨w1, w2, hw1, hw2, hsl⟩ : ∃ w1 w2 : Word, a[q + 1]? = some w1 ∧ a[q + 1 + 1]? = some w2 ∧
      hslice? a w1.toNat w2.toNat = some cv.levelParams)
  refine ⟨w2, hw2, ?_⟩
  unfold hslice? at hsl
  simpa using (mapM_opt_length _ _ _ hsl).symm

theorem defnMono_words {m : Mem} {dn : NIdx → Option ConLeche.Name} {q : Word} {ci : IConstantInfo}
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (h : decCI (erecP m) dn q.toNat = some ci) :
    (rdW (m.arr64 EREC) q ≠ 1 ∧ defnMono ci = false) ∨
    (rdW (m.arr64 EREC) q = 1 ∧ (defnMono ci = true ↔ rdW (m.arr64 EREC) (q + 3) = 0)) := by
  rcases decCI_defn_cases h with ⟨cv, v, hint, rfl, hk, hcv⟩ | ⟨w, hw, hne, hnd⟩
  · right
    have hk' := erecP_get hk
    have e1 : rdW (m.arr64 EREC) q = 1 := by simp [rdW, hk']
    refine ⟨e1, ?_⟩
    obtain ⟨w, hw, hwl⟩ := decCV_lps_len hcv
    have hw' := erecP_get hw
    have hq3 : (q + 3).toNat = q.toNat + 3 := by
      have : q.toNat + 1 + 2 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp hw').1
      rw [UInt64.toNat_add]; simp; omega
    have e3 : rdW (m.arr64 EREC) (q + 3) = w := by
      simp only [rdW, hq3]; rw [show q.toNat + 3 = q.toNat + 1 + 2 by omega, hw']; rfl
    rw [e3]
    simp only [defnMono, List.isEmpty_iff_length_eq_zero]
    constructor
    · intro hl; exact UInt64.toNat_inj.mp (by simpa [hwl] using hl)
    · intro hw0; rw [← hwl, hw0]; rfl
  · left
    have hw' := erecP_get hw
    refine ⟨?_, ?_⟩
    · simp [rdW, hw']; exact hne
    · cases ci with
      | defnInfo cv v hint => exact absurd rfl (hnd cv v hint)
      | _ => rfl

/-! ## `nat_op_deps_stored` -/

/-- **`nat_op_deps_stored` is its model `depsStoredW`** (generated). -/
l_model depsStored_specW (p : Prog) (hp : p.lookup "nat_op_deps_stored" = some natOpDepsStoredL)
  fns [hp ↦ depsStoredW list]
  specs [callW_spec p n "env_find", callW_spec p n "nat_op_deps_stored"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW

theorem natOpDepsStored_cons (fe : IFEnv) (n : NIdx) (ns : List NIdx) :
    natOpDepsStored fe (n :: ns) = (match fe.find? n with
      | some ci => if defnMono ci = true then natOpDepsStored fe ns else pure false
      | none => pure false) := by
  simp only [natOpDepsStored]
  cases fe.find? n with
  | none => rfl
  | some ci => cases ci <;> simp [defnMono]

section stored
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

theorem decHL_cons_iw {κ : IdxKind} {m : Mem} {o l : Word} {n : Idx κ} {ns : List (Idx κ)}
    (hsz : (m.arr64 IW).size < 2 ^ 64) (h : decHL m o.toNat l.toNat = some (n :: ns)) :
    l ≠ 0 ∧ (rdW (m.arr64 IW) o).toNat < 2 ^ 32 ∧ n = decI (rdW (m.arr64 IW) o) ∧
      decHL m (o + 1).toNat (l - 1).toNat = some ns := by
  have hb := decHL_bnd m o l h hsz
  have hl0 : l ≠ 0 := by
    intro e; subst e; simp [decHL, hslice?] at h
  have hl : l.toNat = (l - 1).toNat + 1 := by
    have : 0 < l.toNat := by
      rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl0
      · exact h0
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
  have ho : (o + 1).toNat = o.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  rw [hl] at h
  simp only [decHL, hslice?_succ] at h
  cases hx : (hd? (iwA m) o.toNat : Option (Idx κ)) with
  | none => simp [hx] at h
  | some x =>
    cases hxs : (hslice? (iwA m) (o.toNat + 1) (l - 1).toNat : Option (List (Idx κ))) with
    | none => simp [hx, hxs] at h
    | some xs =>
      simp [hx, hxs] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hl0, ?_, ?_, by rw [ho]; exact hxs⟩
      all_goals
        obtain ⟨w, hw, hlt, rfl⟩ := hd?_some hx
        have : rdW (m.arr64 IW) o = w := by simp [rdW, iwA] at hw ⊢; rw [hw]; rfl
        rw [this]
      exact hlt

theorem depsStored_ref (hN : NatGateProg p) (o l : Word) (ns : List NIdx) :
    ∀ (k : Nat) (m : Mem) (a : AState) (r : List Word) (m' : Mem), StageR dn vis fe m a →
      decHL m o.toNat l.toNat = some ns →
      callW p k "nat_op_deps_stored" [vis, o, l] m = some (r, m') →
      ∃ x a', (natOpDepsStored fe ns).run a = .ok (x, a') ∧ KeepPost dn vis fe decW0B m m' a' r x := by
  induction ns generalizing o l with
  | nil =>
    intro k m a r m' hS hd hc
    have hl0 : l = 0 := by
      have : l.toNat = 0 := by simpa [decHL, hslice?] using (decHL_length m hd).symm
      exact UInt64.toNat_inj.mp (by simpa using this)
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mm => depsStoredW p (k + 1) mm vis o l) (depsStored_specW p hN.lNatOpDepsStored (k + 1) · vis o l) hc
    simp only [depsStoredW.eq_2, hl0, ite_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨true, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
  | cons n ns ih =>
    intro k m a r m' hS hd hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    obtain ⟨hl0, hwlt, hn, hrest⟩ := decHL_cons_iw hS.2.2.2.1 hd
    have hw := callW_model (M := fun mm => depsStoredW p (k + 1) mm vis o l) (depsStored_specW p hN.lNatOpDepsStored (k + 1) · vis o l) hc
    rw [depsStoredW.eq_2] at hw
    rw [ite_eq_right hl0] at hw
    replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
    obtain ⟨rfl, hfd⟩ := envFind_call hN.toMasterProg (rdW (m.arr64 IW) o) hwlt hS.1.env h1
    subst hn
    rw [natOpDepsStored_cons]
    cases hf : fe.find? (decI (rdW (m1.arr64 IW) o)) with
    | none =>
      rw [hf] at hfd
      simp only [decFd] at hfd
      rw [ite_eq_left hfd] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨false, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
    | some ci =>
      rw [hf] at hfd
      obtain ⟨hr1, hci⟩ := hfd
      rw [ite_eq_right (by rw [hr1]; decide)] at hw
      rcases defnMono_words hS.2.2.2.2.1 hci with ⟨hne, hdm⟩ | ⟨hk1, hiff⟩
      · rw [ite_eq_left hne] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [hdm]
        exact ⟨false, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
      · rw [ite_eq_right (by simpa using hk1)] at hw
        by_cases h3 : rdW (m1.arr64 EREC) (r1.tail.headD 0 + 3) = 0
        · rw [ite_eq_right (by simpa using h3)] at hw
          have hdm : defnMono ci = true := hiff.mpr h3
          simp only [hdm, ite_true]
          cases h2 : callW p k "nat_op_deps_stored" [vis, o + 1, l - 1] m1 with
          | none => rw [h2] at hw; simp at hw
          | some q2 =>
            obtain ⟨r2, m2⟩ := q2
            rw [h2, bW_some] at hw
            simp only [Option.some.injEq, Prod.mk.injEq] at hw
            obtain ⟨rfl, rfl⟩ := hw
            obtain ⟨x, a', hrun, hK⟩ := ih (o + 1) (l - 1) k m1 a r2 m2 hS hrest h2
            refine ⟨x, a', hrun, hK.1, hK.2.1, ?_⟩
            simpa [decW0B] using hK.2.2
        · rw [ite_eq_left (by simpa using h3)] at hw
          simp only [Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          have hdm : defnMono ci = false := by
            cases h : defnMono ci
            · rfl
            · exact absurd (hiff.mp h) h3
          simp only [hdm]
          exact ⟨false, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
theorem natOpDepsStored_ref (hN : NatGateProg p) (o l : Word) (ns : List NIdx) :
    CallRef p "nat_op_deps_stored" [vis, o, l]
      (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some ns)
      (natOpDepsStored fe ns) (KeepPost dn vis fe decW0B) :=
  fun k m a r m' ⟨hS, hd⟩ hc => depsStored_ref hN o l ns k m a r m' hS hd hc

@[refines ConRon.Arena.natOpDepsStored]
theorem natOpDepsStored_refines (hN : NatGateProg p) (o l : Word) (ns : List NIdx) :
    RefAM p "nat_op_deps_stored" [vis, o, l]
      (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some ns)
      (natOpDepsStored fe ns) (KeepPost dn vis fe decW0B) :=
  (natOpDepsStored_ref hN o l ns).refAM

end stored

end L.Ind
