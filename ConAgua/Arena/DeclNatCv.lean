import ConAgua.Arena.DeclNatSpec

/-!
# `ci_to_cv` refines `IConstantInfo.toConstantVal` (lane `decls3`, helper `decls3-nat`)

The stored record's inline constant value, or for a projection table a fresh one (the table's
name and level parameters, `Sort 1` interned as the twin interns it). The result decodes in the
record prefix `erecP` of the memory after (`decCV (erecP m') q`), whichever arm ran.
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A returning `ntBW`: its callee returned. -/
theorem ntBW_some {β : Type} {mo : Option (List Word × Mem)} {k : List Word → Mem → Option β} {res : β}
    (hw : ntBW mo k = some res) : ∃ r m, mo = some (r, m) ∧ k r m = some res := by
  cases mo with
  | none => cases hw
  | some q => exact ⟨q.1, q.2, rfl, hw⟩

/-- The inline constant value of a non-projection record. -/
def ciCv? : IConstantInfo → Option IConstantVal
  | .axiomInfo v | .defnInfo v _ _ | .thmInfo v => some v
  | .indInfo v _ | .ctorInfo v _ _ | .recInfo v _ _ _ => some v
  | .projInfo _ => none

theorem decCI_shape {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} (h : decCI a dn p = some ci) :
    ∃ w, a[p]? = some w ∧
      ((w.toNat ≤ 5 ∧ ∃ cv, ciCv? ci = some cv ∧ decCV a (p + 1) = some cv) ∨
       (w.toNat = 6 ∧ ∃ tbl, ci = .projInfo tbl ∧ decTbl a p = some tbl)) := by
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
  refine ⟨w, hw, ?_⟩
  rcases k with _ | _ | _ | _ | _ | _ | _ | k
  · -- the tag 6 case is the seventh; the first six are inline constant values
    simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, h⟩ := h
    left
    exact ⟨by omega, cv, by subst h; rfl, hcv⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, h⟩ := h
    left
    exact ⟨by omega, cv, by obtain ⟨_, -, _, -, rfl⟩ := h; rfl, hcv⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, h⟩ := h
    left
    exact ⟨by omega, cv, by subst h; rfl, hcv⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, h⟩ := h
    left
    exact ⟨by omega, cv, by obtain ⟨_, -, rfl⟩ := h; rfl, hcv⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, h⟩ := h
    left
    exact ⟨by omega, cv, by obtain ⟨_, -, _, -, rfl⟩ := h; rfl, hcv⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, h⟩ := h
    left
    exact ⟨by omega, cv, by obtain ⟨_, -, _, -, _, -, _, -, _, -, rfl⟩ := h; rfl, hcv⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tbl, htbl, rfl⟩ := h
    right
    exact ⟨by omega, tbl, rfl, htbl⟩
  · simp at h

section cvref
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

structure NatCvProg (p : Prog) : Prop extends NatGateProg p where
  lCanon : CanonProg p

theorem IWGrow.erec_get {m m' : Mem} (h : IWGrow m m') {i : Nat} {v : Word}
    (hv : (erecP m)[i]? = some v) : (m'.arr64 EREC)[i]? = some v := by
  simp only [erecP, Array.getElem?_extract] at hv
  split at hv
  · rename_i hi
    have hi' : i < erTop m := by simp [erTop, erecTop] at hi ⊢; omega
    rw [h.2.2.2 i hi']; simpa using hv
  · simp at hv

theorem erecP_size_le' (m : Mem) : (erecP m).size ≤ erTop m := by
  simp only [erecP, Array.size_extract, erecTop, erTop]; omega

theorem rdW_erec_of {m : Mem} {q : Word} {w : Word} (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (h : (erecP m)[q.toNat]? = some w) : rdW (m.arr64 EREC) q = w := by
  simp [rdW, erecP_get h]

theorem ciToCv_ref (hN : NatCvProg p) (q : Word) (ci : IConstantInfo) :
    CallRef p "ci_to_cv" [q]
      (fun m a => StageR dn vis fe m a ∧ decCI (erecP m) dn q.toNat = some ci)
      ci.toConstantVal
      (KeepPost dn vis fe (fun m r (cv : IConstantVal) => decCV (erecP m) (r.headD 0).toNat = some cv)) :=
  CallRef.of_refAM (ciToCv_refines p hN.lCanon dn vis fe q ci)

end cvref

end L.Ind
