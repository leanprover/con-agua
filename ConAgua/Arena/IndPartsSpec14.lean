import ConAgua.Arena.IndPartsSpec13

/-!
# Refinements of `IndParts`, part 14 (lane `indproofs2`, helper `parts`): `blockShape?`

The result sort (`block_shape_result_sort`, through `strip_pis`; `nP + nIdx` wrapping is a capacity
abort), the record (`block_shape_pack`), `block_shape_build` composing every piece, `block_shape`,
`block_parts`.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `block_shape_result_sort` -/

/-- After `e_view`: the sort's level, else `zeroLevel`. -/
def bsoK2 (m1 : Mem) (v : List Word) : Option (List Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 2 then some ([v.getD 1 0], m1)
  else match pinWordV m1 53 with
    | none => none
    | some z => some ([z], m1)

/-- After `strip_pis`. -/
def bsoK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then (match pinWordV m1 53 with
      | none => none
      | some z => some ([z], m1))
    else bsoK2 m1 (eViewW m1 (r1.tail.tail.tail.headD 0))

/-- **The model of `block_shape_result_sort`.** -/
def bsoW (m : Mem) (nP io il ty : Word) : Option (List Word × Mem) :=
  if nP + getDW m io il 0 0 < nP then none
  else bsoK1 (stubM "strip_pis" m [nP + getDW m io il 0 0, ty])

theorem bso_spec (p : Prog) (hv : p.lookup "e_view" = some eView) (hpw : p.lookup "pin_word" = some pinWordL)
    (hg : p.lookup "sl_getd" = some slGetD)
    (hp : p.lookup "block_shape_result_sort" = some blockShapeResultSort) (n : Nat) (s₀ : St)
    (nP io il ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_shape_result_sort" [nP, io, il, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ bsoW s₀.mem nP io il ty = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeResultSort]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, slGetD_specW p hg n,
      stubM_spec p "strip_pis" n, eViewSpec4 p hv n, pinWord_specV p hpw n] <;>
    finish (gen := 20) [bsoW, bsoK1, bsoK2]

/-- The twin's result sort (`blockShape?`'s first `let s`). -/
def bsoTwin (nP : Nat) (nIdxs : List Nat) (ty : EIdx) : AM LIdx := do
  match ← stripPis (nP + nIdxs.headD 0) ty with
  | some q => do
    match ← view q.2 with
    | .sort s => pure s
    | _ => zeroLevel
  | none => zeroLevel

theorem getDW_head {m : Mem} {io il : Word} {ns : List Nat} (h : DecB (fun m => decNL m io.toNat il.toNat) m ns)
    (hb : io.toNat + il.toNat ≤ iwTop m) : (getDW m io il 0 0).toNat = ns.headD 0 := by
  unfold getDW
  by_cases hl : il = 0
  · subst hl
    have : ns = [] := by have := h; simp only [DecB, UInt64.toNat_zero] at this; simpa [decNL] using this.symm
    subst this; simp
  rw [if_neg (by rw [UInt64.le_iff_toNat_le]; simp; intro e; exact hl (UInt64.toNat_inj.mp (by simpa using e)))]
  obtain ⟨x, xs, rfl, hw, hxb, -, -⟩ := partsNL_cons h hb hl
  simp [hw, UInt64.toNat_ofNat_of_lt' hxb]

/-- **`block_shape_result_sort`'s model refines the twin's result sort.** -/
theorem bsoW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    {nP io il ty : Word} {ns : List Nat} (hS : StageR dn vis fe m a)
    (hns : DecB (fun m => decNL m io.toNat il.toNat) m ns) (hb : io.toNat + il.toNat ≤ iwTop m)
    (hty : H ty) :
    Sim (bsoW m nP io il ty) (bsoTwin nP.toNat ns (decI ty)) a
      (fun r s m' a' => H (r.headD 0) ∧ decI (r.headD 0) = s ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  intro r m' e
  unfold bsoW at e
  split at e
  · cases e
  rename_i hov
  have hk : (nP + getDW m io il 0 0).toNat = nP.toNat + ns.headD 0 := by
    rw [partsAddNoOv hov, getDW_head hns hb]
  revert r m' e
  have h1 := partsSimStub (stripPis_spec dn vis fe (nP + getDW m io il 0 0) ty hty) hS
  rw [hk] at h1
  unfold bsoTwin
  refine Sim.bindK (K := bsoK1) (body := fun r1 m1 => if r1.headD 0 = 0 then (match pinWordV m1 53 with
      | none => none
      | some z => some ([z], m1)) else bsoK2 m1 (eViewW m1 (r1.tail.tail.tail.headD 0))) rfl
    (fun _ _ => rfl) h1 ?_
  rintro r1 x1 m1 a1 ⟨hS1, hg1, hd1⟩
  have hz : ∀ (R : List Word → LIdx → Mem → AState → Prop),
      (∀ z, H z → R [z] (decI z) m1 a1) →
      Sim (match pinWordV m1 53 with | none => none | some z => some ([z], m1)) zeroLevel a1 R := by
    intro R hR r m' e
    cases hp : pinWordV m1 53 with
    | none => rw [hp] at e; cases e
    | some z =>
      rw [hp] at e; simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      obtain ⟨hrun, hzh⟩ := pinZero_stage hS1 hp
      exact ⟨_, a1, hrun, hR z hzh⟩
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    simp only [h0, if_true]
    exact hz _ fun z hz' => ⟨hz', rfl, hS1, hg1⟩
  | some q =>
    obtain ⟨l1, e1⟩ := q
    obtain ⟨h1', -, hbl, hbe⟩ := hd1
    rw [partsDrop3] at hbl hbe
    simp only [h1', show (1 : Word) ≠ 0 by decide, if_false]
    intro r m' e
    unfold bsoK2 at e
    split at e
    · cases e
    rename_i hne
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m1 a1 hS1.1.arena.1 _ hne
    have hvrun := view_run _ a1 v hv
    rw [show (decE (r1.tail.tail.tail.headD 0)) = e1 from hbe] at hvrun
    simp only [StateT.run_bind, hvrun]
    split at e
    · rename_i h2
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨u, rfl⟩ := (sort_head_iff m1 _ v hvr).mp h2
      obtain ⟨-, hul, hue⟩ := hvr
      exact ⟨u, a1, rfl, hul, hue, hS1, hg1⟩
    · rename_i h2
      have hns : ∀ u, v ≠ .sort u := fun u hu => h2 ((sort_head_iff m1 _ v hvr).mpr ⟨u, hu⟩)
      have hzz := hz (fun r s m' a' => H (r.headD 0) ∧ decI (r.headD 0) = s ∧ StageR dn vis fe m' a' ∧
        IWGrow m m') (fun z hz' => ⟨hz', rfl, hS1, hg1⟩) r m' e
      cases v with
      | sort u => exact absurd rfl (hns u)
      | _ => exact hzz

end L.Ind
