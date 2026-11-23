module

import ConAgua.Arena.DeclNatCv
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConRon.Bridge.Grind
public import ConAgua.Arena.DeclNatSpec
import all ConAgua.Arena.DeclArmsNat
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

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

theorem decCI_defn_cases {rd : Nat → Option Word} {p : Nat}
    {ci : IConstantInfo} (h : decCI rd p = some ci) :
    (∃ cv v hint, ci = .defnInfo cv v hint ∧ rd p = some 1 ∧ decCV rd (p + CI.cv.toNat) = some cv) ∨
    (∃ w, rd p = some w ∧ w ≠ 1 ∧ ∀ cv v hint, ci ≠ .defnInfo cv v hint) := by
  obtain ⟨w, hw, hx⟩ := decCI_cases h
  by_cases h1 : w = 1
  · subst h1
    rcases hx with ⟨hk, -⟩ | ⟨-, cv, v, hi, hcv, -, -, rfl⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩
    all_goals first | (exfalso; simp at hk; done) | skip
    exact .inl ⟨cv, v, hi, rfl, hw, hcv⟩
  · refine .inr ⟨w, hw, h1, fun cv v hint e => ?_⟩
    subst e
    rcases hx with ⟨-, -, -, ⟨⟩⟩ | ⟨hk, -⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, -, -, ⟨⟩⟩ |
      ⟨-, -, -, -, -, -, -, -, -, ⟨⟩⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨⟩⟩
    exact h1 (UInt64.toNat_inj.mp (by rw [hk]; rfl))

theorem defnMono_words {m : Mem} {q : Word} {ci : IConstantInfo}
    (h : decCI (erecP m) q.toNat = some ci) :
    (erRd m q ≠ 1 ∧ defnMono ci = false) ∨
    (erRd m q = 1 ∧ (defnMono ci = true ↔ erRd m (q + (CI.cv + CV.lpsLen)) = 0)) := by
  rcases decCI_defn_cases h with ⟨cv, v, hint, rfl, hk, hcv⟩ | ⟨w, hw, hne, hnd⟩
  · right
    refine ⟨(erRd_of_erecP hk).1, ?_⟩
    have hwl := (decCV_rd_ci (erRdOK m) hcv).2.2.2.1
    simp only [defnMono, List.isEmpty_iff_length_eq_zero, hwl]
    constructor
    · intro hl; exact UInt64.toNat_inj.mp (by simpa using hl)
    · intro hw0; rw [hw0]; rfl
  · left
    refine ⟨by rw [(erRd_of_erecP hw).1]; exact hne, ?_⟩
    cases ci with
    | defnInfo cv v hint => exact absurd rfl (hnd cv v hint)
    | _ => rfl

/-! ## `nat_op_deps_stored` -/

/-- **`nat_op_deps_stored` is its model `depsStoredW`** (generated). -/
l_model depsStored_specW (p : Prog) (hp : p.lookup "nat_op_deps_stored" = some natOpDepsStoredL)
  fns [hp ↦ depsStoredW list]
  specs [callW_spec p n "env_find", callW_spec p n "nat_op_deps_stored"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW

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
    ∀ (k : Nat) (m : Mem) (a : AState) (r : List Word) (m' : Mem), StageR vis fe m a →
      decHL m o.toNat l.toNat = some ns →
      callW p k "nat_op_deps_stored" [vis, o, l] m = some (r, m') →
      ∃ x a', (natOpDepsStored fe ns).run a = .ok (x, a') ∧ KeepPost vis fe decW0B m m' a' r x := by
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
    obtain ⟨hl0, hwlt, hn, hrest⟩ := decHL_cons_iw hS.iw.iwSize hd
    have hw := callW_model (M := fun mm => depsStoredW p (k + 1) mm vis o l) (depsStored_specW p hN.lNatOpDepsStored (k + 1) · vis o l) hc
    rw [depsStoredW.eq_2] at hw
    rw [ite_eq_right hl0] at hw
    replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
    obtain ⟨rfl, hfd⟩ := envFind_call hN.toMasterProg (rdW (m.arr64 IW) o) hwlt hS.check.env h1
    subst hn
    simp only [natOpDepsStored]
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
      obtain ⟨hr1, -⟩ := hfd
      rw [ite_eq_right (by rw [hr1]; decide)] at hw
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

theorem natOpDepsStored_ref (hN : NatGateProg p) (o l : Word) (ns : List NIdx) :
    CallRef p "nat_op_deps_stored" [vis, o, l]
      (fun m a => StageR vis fe m a ∧ decHL m o.toNat l.toNat = some ns)
      (natOpDepsStored fe ns) (KeepPost vis fe decW0B) :=
  fun k m a r m' ⟨hS, hd⟩ hc => depsStored_ref hN o l ns k m a r m' hS hd hc

@[refines ConRon.Arena.natOpDepsStored]
theorem natOpDepsStored_refines (hN : NatGateProg p) (o l : Word) (ns : List NIdx) :
    RefAM p "nat_op_deps_stored" [vis, o, l]
      (fun m a => StageR vis fe m a ∧ decHL m o.toNat l.toNat = some ns)
      (natOpDepsStored fe ns) (KeepPost vis fe decW0B) :=
  (natOpDepsStored_ref hN o l ns).refAM

end stored

end L.Ind
