import ConAgua.Arena.IndPartsSpec13
import ConAgua.Arena.IndSumSpec2

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

/-! ## `block_shape_pack` -/

/-- The memory after `block_shape_pack`. -/
def packMem (m : Mem) (a b c d e f g h i : Word) : Mem :=
  let q := rdW (m.arr64 CTL) 200
  (((((((((allocMem m 9).set64 IW q a).set64 IW (q + 1) b).set64 IW (q + 2) c).set64 IW (q + 3) d).set64
    IW (q + 4) e).set64 IW (q + 5) f).set64 IW (q + 6) g).set64 IW (q + 7) h).set64 IW (q + 8) i

theorem packMem_eq (m : Mem) (a b c d e f g h i : Word) :
    packMem m a b c d e f g h i = wrIW (allocMem m 9) (rdW (m.arr64 CTL) 200) [a, b, c, d, e, f, g, h, i] := by
  simp [packMem, wrIW, UInt64.add_assoc]

theorem partsPack_eq (m : Mem) (a b c d e f g h i : Word) :
    (match allocW m 9 with | none => none | some (q, _) => some (q, packMem m a b c d e f g h i)) =
      posRecW m [a, b, c, d, e, f, g, h, i] := by
  rw [posRecW_eq m _ 9 rfl, packMem_eq]; cases allocW m 9 <;> rfl

theorem bsp_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "block_shape_pack" = some blockShapePack) (n : Nat) (s₀ : St)
    (mo ml ro rl nP elim s large isProp : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_shape_pack" [mo, ml, ro, rl, nP, elim, s, large, isProp]
    ⦃fun r s' => LocEq s' s₀ ∧
      posRecW s₀.mem [mo, ml, ro, rl, nP, elim, s, large, isProp] = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [← partsPack_eq, invoke_eq _ hp]
  simp only [callFn, blockShapePack]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish (gen := 20) [packMem, allocMem, allocW]

/-! ## `block_shape_build`: the model -/

/-- After the pack. -/
def bbPack : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m) => some ([1, q], m)

/-- After `intern_nanon` (the small eliminator). -/
def bbK14 (mo ml ro2 rl2 nPd s ip : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbPack (posRecW m [mo, ml, ro2, rl2, nPd, r.headD 0, s, 0, ip])

/-- After `block_shape_large`. -/
def bbK13 (mo ml ro2 rl2 nPd s ip : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then bbPack (posRecW m [mo, ml, ro2, rl2, nPd, r.tail.headD 0, s, 1, ip])
    else bbK14 mo ml ro2 rl2 nPd s ip (stubM "intern_nanon" m [])

/-- After `block_shape_recs_of`. -/
def bbK12 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (lo ll s ip mo ml : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK13 mo ml (r.headD 0) (r.tail.headD 0) nPd s ip (bslW n m cvR0 lo ll)

/-- After `block_shape_members_of`. -/
def bbK11 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl lo ll s ip : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK12 n nPd cto ctl cso csl rso rsl cvT0 cvR0 lo ll s ip (r.headD 0) (r.tail.headD 0) (brsW (n + 1) m no nl rso rsl)

/-- After `block_groups`. -/
def bbK10 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl io lo ll s ip : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK11 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl lo ll s ip (bmoW (n + 1) m cto ctl io (r.headD 0))

/-- After `param_levels`. -/
def bbK9 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl io lo ll s ip cof cl2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK10 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (bgW n m no nl (r.headD 0) nPd ctl cof cl2)

/-- After `block_shape_ctors_of`. -/
def bbK8 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl io lo ll s ip : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK9 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (r.headD 0) (r.tail.headD 0) (plW (n + 1) m lo ll)

/-- After `lvl_eq_c`. -/
def bbK7 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl io lo ll s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK8 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s (if r.headD 0 = 2 then 1 else 0) (bctW (n + 1) m cso csl)

/-- After `pin_word(53)`. -/
def bbK6 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl io lo ll s : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some z => bbK7 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s (stubM "lvl_eq_c" m [s, z])

/-- After `block_shape_result_sort`. -/
def bbK5 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl io lo ll : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK6 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll (r.headD 0) m (pinWordV m 53)

/-- After `block_shape_pins_ok`. -/
def bbK4 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl io il lo ll : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0, 0], m)
    else bbK5 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll (bsoW m nPd io il (rdW (m.arr64 EREC) (cvT0 + 3)))

/-- After `er_to_iw` (the block's level parameters). -/
def bbK3 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl io il : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK4 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io il (r.headD 0) (r.tail.headD 0)
      (bpoW n m nPd cto ctl (r.headD 0) (r.tail.headD 0) rso rsl cso csl)

/-- After `block_member_counts`. -/
def bbK2 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0, 0], m)
    else bbK3 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl (r.tail.headD 0) (r.tail.tail.headD 0)
      (erToIwW (n + 1) m (rdW (m.arr64 EREC) (cvT0 + 1)) (rdW (m.arr64 EREC) (cvT0 + 2)))

/-- After `block_shape_names_of`. -/
def bbK1 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK2 n nPd cto ctl cso csl rso rsl cvT0 cvR0 (r.headD 0) (r.tail.headD 0)
      (bmcW n m nPd ctl csl (r.headD 0) (r.tail.headD 0) rso rsl cto ctl)

/-- **The model of `block_shape_build`** (at exec fuel `n + 2`). -/
def bbW (n : Nat) (m : Mem) (nPd cto ctl cso csl rso rsl : Word) : Option (List Word × Mem) :=
  bbK1 n nPd cto ctl cso csl rso rsl (rdW (m.arr64 IW) cto) (rdW (m.arr64 IW) (rdW (m.arr64 IW) rso))
    (bsnW (n + 1) m cto ctl)

section arms
variable (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (m : Mem) (r : List Word) (no nl io il lo ll s ip cof cl2 mo ml ro2 rl2 z : Word) (q : Word)
theorem bbPack_some : bbPack (some (q, m)) = some ([1, q], m) := rfl
theorem bbK14_some : bbK14 mo ml ro2 rl2 nPd s ip (some (r, m)) =
    bbPack (posRecW m [mo, ml, ro2, rl2, nPd, r.headD 0, s, 0, ip]) := rfl
theorem bbK13_large (h : r.headD 0 ≠ 0) : bbK13 mo ml ro2 rl2 nPd s ip (some (r, m)) =
    bbPack (posRecW m [mo, ml, ro2, rl2, nPd, r.tail.headD 0, s, 1, ip]) := by
  simp only [bbK13]; exact if_pos h
theorem bbK13_small (h : ¬ r.headD 0 ≠ 0) : bbK13 mo ml ro2 rl2 nPd s ip (some (r, m)) =
    bbK14 mo ml ro2 rl2 nPd s ip (stubM "intern_nanon" m []) := by simp only [bbK13]; exact if_neg h
theorem bbK12_some : bbK12 n nPd cto ctl cso csl rso rsl cvT0 cvR0 lo ll s ip mo ml (some (r, m)) =
    bbK13 mo ml (r.headD 0) (r.tail.headD 0) nPd s ip (bslW n m cvR0 lo ll) := rfl
theorem bbK11_some : bbK11 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl lo ll s ip (some (r, m)) =
    bbK12 n nPd cto ctl cso csl rso rsl cvT0 cvR0 lo ll s ip (r.headD 0) (r.tail.headD 0) (brsW (n + 1) m no nl rso rsl) := rfl
theorem bbK10_some : bbK10 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (some (r, m)) =
    bbK11 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl lo ll s ip (bmoW (n + 1) m cto ctl io (r.headD 0)) := rfl
theorem bbK9_some : bbK9 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip cof cl2 (some (r, m)) =
    bbK10 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (bgW n m no nl (r.headD 0) nPd ctl cof cl2) := rfl
theorem bbK8_some : bbK8 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (some (r, m)) =
    bbK9 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (r.headD 0) (r.tail.headD 0) (plW (n + 1) m lo ll) := rfl
theorem bbK7_some : bbK7 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s (some (r, m)) =
    bbK8 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s (if r.headD 0 = 2 then 1 else 0) (bctW (n + 1) m cso csl) := rfl
theorem bbK6_some : bbK6 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s m (some z) =
    bbK7 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s (stubM "lvl_eq_c" m [s, z]) := rfl
theorem bbK5_some : bbK5 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll (some (r, m)) =
    bbK6 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll (r.headD 0) m (pinWordV m 53) := rfl
theorem bbK4_fail (h : r.headD 0 = 0) : bbK4 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io il lo ll (some (r, m)) = some ([0, 0], m) := by
  simp only [bbK4]; exact if_pos h
theorem bbK4_ok (h : ¬ r.headD 0 = 0) : bbK4 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io il lo ll (some (r, m)) =
    bbK5 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll (bsoW m nPd io il (rdW (m.arr64 EREC) (cvT0 + 3))) := by
  simp only [bbK4]; exact if_neg h
theorem bbK3_some : bbK3 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io il (some (r, m)) = bbK4 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io il (r.headD 0) (r.tail.headD 0)
      (bpoW n m nPd cto ctl (r.headD 0) (r.tail.headD 0) rso rsl cso csl) := rfl
theorem bbK2_fail (h : r.headD 0 = 0) : bbK2 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl (some (r, m)) = some ([0, 0], m) := by
  simp only [bbK2]; exact if_pos h
theorem bbK2_ok (h : ¬ r.headD 0 = 0) : bbK2 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl (some (r, m)) =
    bbK3 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl (r.tail.headD 0) (r.tail.tail.headD 0)
      (erToIwW (n + 1) m (rdW (m.arr64 EREC) (cvT0 + 1)) (rdW (m.arr64 EREC) (cvT0 + 2))) := by
  simp only [bbK2]; exact if_neg h
theorem bbK1_some : bbK1 n nPd cto ctl cso csl rso rsl cvT0 cvR0 (some (r, m)) = bbK2 n nPd cto ctl cso csl rso rsl cvT0 cvR0 (r.headD 0) (r.tail.headD 0)
      (bmcW n m nPd ctl csl (r.headD 0) (r.tail.headD 0) rso rsl cto ctl) := rfl
end arms
attribute [ind_grind] bbPack_some bbK14_some bbK13_large bbK13_small bbK12_some bbK11_some bbK10_some
  bbK9_some bbK8_some bbK7_some bbK6_some bbK5_some bbK4_fail bbK4_ok bbK3_some bbK2_fail bbK2_ok bbK1_some

end L.Ind
