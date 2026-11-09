module

public import ConAgua.Arena.BasisBlockT
public import ConAgua.Arena.DeclBasisRef
import ConAgua.Arena.QuotRecW
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.InferLeaves
import ConAgua.Arena.RecCheckSpec.ErToIwWStage
import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.IndTwin
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Inv

@[expose] public section

/-!
# `pin_list_ok` refines `pinListOk` (lane `ronsync2`, stage 3)

`BasisL.lean`'s comparison of a block with its pin, `pin_list_ok(bo, bl, po, pl)` on two `IW`
slices of constant records: the copies (`pin_copies_ok`, each `pin_copy_ok` as `quot_pin_hit`
does it: the names, the pin at them, `pin_agrees`) and the links (`block_links_ok`: a
constructor's names against the former's, a recursor's rules' constructors linked through
`pin_link_ok`). The contract is `PinListOkRef` (`BasisBlockT.lean`); `pinListOkRef_of` proves it
from the program facts `PinListLProg`.
-/

noncomputable section

open ConRon.Arena

namespace L.Ind

open L.Arena

/-! ## `pin_agrees` -/

theorem pinAgrees_eq_of_not_ind {x y : IConstantInfo}
    (h : ¬ ((∃ v c, x = .indInfo v c) ∧ ∃ v c, y = .indInfo v c)) :
    ConRon.Arena.pinAgrees x y = decide (x = y) := by
  cases x <;> cases y <;> simp_all [ConRon.Arena.pinAgrees]
  all_goals (rw [Bool.eq_iff_iff]; simp)

theorem ciD_ind {R : Nat → Option Word} {q : Nat} {v : IConstantVal} {c : IIndCaps}
    (h : decCI R q = some (.indInfo v c)) : ∃ w, R q = some w ∧ w.toNat = 3 := by
  obtain ⟨wk, e, hx⟩ := ciD h
  refine ⟨wk, e, ?_⟩
  rcases hx with ⟨k, _, _, h1⟩ | ⟨k, _, _, _, _, _, _, h1⟩ | ⟨k, _, _, h1⟩ | ⟨k, _⟩ |
    ⟨k, _, _, _, _, _, _, h1⟩ | ⟨k, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1⟩
  all_goals first | exact k | cases h1

/-- **`pin_agrees(c, d)` decides `pinAgrees`** (pure). -/
theorem pinAgreesW_ok {p : Prog} (hc : CanonProg p)
    (hp : p.lookup "pin_agrees" = some L.Ind.pinAgrees) {n : Nat} {m m' : Mem} {c d : Word}
    {r : List Word} {x y : IConstantInfo}
    (hx : decCI (erecP m) c.toNat = some x) (hy : decCI (erecP m) d.toNat = some y)
    (h : callW p n "pin_agrees" [c, d] m = some (r, m')) :
    m' = m ∧ (r.headD 0 ≠ 0 ↔ ConRon.Arena.pinAgrees x y = true) := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinAgrees_specW p hp n _ c d) h
  cases n with
  | zero => simp [pinAgreesW] at hW
  | succ n =>
  obtain ⟨wk, e, hxk⟩ := ciD hx
  obtain ⟨wk', e', hyk⟩ := ciD hy
  have r1 : erRdT m c = wk := erRdT_of _ _ e
  have r2 : erRdT m d = wk' := erRdT_of _ _ e'
  by_cases h3 : erRdT m c = 3 ∧ erRdT m d = 3
  · rw [pinAgreesW.arm1 p n m c d h3] at hW
    cases h1 : callW p n "cv_eq" [c + 1, d + 1] m with
    | none => rw [h1] at hW; simp [pinAgreesW.k_cv_eq] at hW
    | some x1 =>
    obtain ⟨r1', m1⟩ := x1
    obtain ⟨s1, rfl, -, hm1, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (cvEq_spec' p hc n _ (c + 1) (d + 1)) h1
    rw [h1] at hW; simp only [pinAgreesW.k_cv_eq, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, hm⟩ := hW
    refine ⟨hm.symm.trans hm1, ?_⟩
    rw [r1] at h3; rw [r2] at h3
    obtain ⟨rfl, rfl⟩ := h3
    rcases hxk with ⟨k0, -⟩ | ⟨k0, -⟩ | ⟨k0, -⟩ | ⟨-, cv, caps, hcv, -, rfl⟩ | ⟨k0, -⟩ | ⟨k0, -⟩ <;>
      try (simp at k0)
    rcases hyk with ⟨k0, -⟩ | ⟨k0, -⟩ | ⟨k0, -⟩ | ⟨-, cv', caps', hcv', -, rfl⟩ | ⟨k0, -⟩ | ⟨k0, -⟩ <;>
      try (simp at k0)
    have hb := cvEqB_ok' (erRdOK m) (p := c) (q := d) (k := 1) (kn := 1) rfl hcv hcv'
    simp only [List.headD_cons, hr1, hm1, hb, ConRon.Arena.pinAgrees, beq_iff_eq]
    by_cases hcc : cv = cv' <;> simp [hcc]
  · rw [pinAgreesW.eq_2, if_neg h3] at hW
    cases h1 : callW p n "ci_eq" [c, d] m with
    | none => rw [h1] at hW; simp [pinAgreesW.k_cv_eq] at hW
    | some x1 =>
    obtain ⟨r1', m1⟩ := x1
    obtain ⟨s1, rfl, -, hm1, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (ciEq_spec' p hc n _ c d) h1
    rw [h1] at hW; simp only [pinAgreesW.k_cv_eq, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, hm⟩ := hW
    refine ⟨hm.symm.trans hm1, ?_⟩
    have hni : ¬ ((∃ v c, x = .indInfo v c) ∧ ∃ v c, y = .indInfo v c) := by
      rintro ⟨⟨v, cp, rfl⟩, ⟨v', cp', rfl⟩⟩
      apply h3
      obtain ⟨w, e1, k0⟩ := ciD_ind hx
      obtain ⟨w', e1', k1⟩ := ciD_ind hy
      rw [r1, r2]
      rw [e] at e1; rw [e'] at e1'
      cases e1; cases e1'
      exact ⟨UInt64.toNat_inj.mp (by rw [k0]; rfl), UInt64.toNat_inj.mp (by rw [k1]; rfl)⟩
    have hb := ciEqB_ok (erRdOK m) hx hy
    simp only [List.headD_cons, hr1, hm1, hb, pinAgrees_eq_of_not_ind hni]
    by_cases hcc : x = y <;> simp [hcc]

end L.Ind
