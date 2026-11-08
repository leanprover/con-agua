module

import ConAgua.Arena.DeclNatCv
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConRon.Bridge.Grind
public import ConAgua.Arena.DeclNatSpec
import all ConAgua.Arena.DeclArmsNat

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

theorem decCI_defn_cases {a : Array Word} {p : Nat}
    {ci : IConstantInfo} (h : decCI (aread a) p = some ci) :
    (∃ cv v hint, ci = .defnInfo cv v hint ∧ a[p]? = some 1 ∧ decCV (aread a) (p + 1) = some cv) ∨
    (∃ w, a[p]? = some w ∧ w ≠ 1 ∧ ∀ cv v hint, ci ≠ .defnInfo cv v hint) := by
  unfold decCI at h
  cases hk : nat? (aread a) p with
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

theorem decCV_lps_len {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV (aread a) q = some cv) :
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
      hslice? (aread a) w1.toNat w2.toNat = some cv.levelParams)
  refine ⟨w2, hw2, ?_⟩
  unfold hslice? at hsl
  simpa using (mapM_opt_length _ _ _ hsl).symm

theorem defnMono_words {m : Mem} {q : Word} {ci : IConstantInfo}
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (h : decCI (erecP m) q.toNat = some ci) :
    (rdW (m.arr64 EREC) q ≠ 1 ∧ defnMono ci = false) ∨
    (rdW (m.arr64 EREC) q = 1 ∧ (defnMono ci = true ↔ rdW (m.arr64 EREC) (q + 3) = 0)) := by
  sorry

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
    ∀ (k : Nat) (m : Mem) (a : AState) (r : List Word) (m' : Mem), StageR vis fe m a →
      decHL m o.toNat l.toNat = some ns →
      callW p k "nat_op_deps_stored" [vis, o, l] m = some (r, m') →
      ∃ x a', (natOpDepsStored fe ns).run a = .ok (x, a') ∧ KeepPost vis fe decW0B m m' a' r x := by
  sorry

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
