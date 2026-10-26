import ConAgua.Arena.IndPartsSpec13
import ConAgua.Arena.IndSumSpec2
import ConAgua.Arena.IndRealNames
import ConAgua.Arena.IndCallM

/-!
# Refinements of `IndParts`, part 14 (lane `indproofs2`, helper `parts`): `blockShape?`

The result sort (`block_shape_result_sort`, through `strip_pis`; `nP + nIdx` wrapping is a capacity
abort), the record (`block_shape_pack`), `block_shape_build` composing every piece, `block_shape`,
`block_parts`.
-/


noncomputable section

set_option experimental.vcgen true

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
  else bsoK1 (stripF 6 m [nP + getDW m io il 0 0, ty])

theorem bso_spec (p : Prog) (hv : p.lookup "e_view" = some eView) (hpw : p.lookup "pin_word" = some pinWordL)
    (hg : p.lookup "sl_getd" = some slGetD)
    (hp : p.lookup "block_shape_result_sort" = some blockShapeResultSort) (hst : StripProg p)
    (n : Nat) (s₀ : St) (nP io il ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_shape_result_sort" [nP, io, il, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ bsoW s₀.mem nP io il ty = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeResultSort]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, slGetD_specW p hg n,
      stripPis_specF p hst n, eViewSpec4 p hv n, pinWord_specV p hpw n] <;>
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
  have h1 := partsSimW (stripF_pis_ok dn vis fe (nP + getDW m io il 0 0) ty hty) hS
  rw [hk] at h1
  unfold bsoTwin
  refine Sim.bindK rfl (fun _ _ => by rw [bsoK1]) h1 ?_
  rintro r1 x1 m1 a1 ⟨hS1, hg1, hd1⟩
  have hz : ∀ (R : List Word → LIdx → Mem → AState → Prop),
      (∀ z, H z → R [z] (decI z) m1 a1) →
      Sim (match pinWordV m1 53 with | none => none | some z => some ([z], m1)) zeroLevel a1 R := by
    intro R hR r m' e
    rcases hp : pinWordV m1 53 with _ | z
    · rw [hp] at e; cases e
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
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
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

/-- **`block_shape_seal` is its model `bsealW`** (generated). -/
l_model bseal_spec (p : Prog) (hna : NaF p) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hpk : p.lookup "block_shape_pack" = some blockShapePack)
    (hp : p.lookup "block_shape_seal" = some blockShapeSeal)
  fns [hp ↦ bsealW list]
  specs [naF_spec p hna n, bsp_spec p ha hpk n]
  grind [ind_grind] simp []

/-- After `block_shape_large`. -/
def bbK13' (mo ml ro2 rl2 nPd s ip : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bgoK3 (bsealW m mo ml ro2 rl2 nPd s ip (r.headD 0) (r.tail.headD 0))

/-- After `block_shape_recs_of`. -/
def bbK12 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (lo ll s ip mo ml : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK13' mo ml (r.headD 0) (r.tail.headD 0) nPd s ip (bslW n m cvR0 lo ll)

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

section arms
variable (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (m : Mem) (r : List Word)
  (no nl io lo ll s ip mo ml : Word) (q : Word)
theorem bbK12_some : bbK12 n nPd cto ctl cso csl rso rsl cvT0 cvR0 lo ll s ip mo ml (some (r, m)) =
    bbK13' mo ml (r.headD 0) (r.tail.headD 0) nPd s ip (bslW n m cvR0 lo ll) := rfl
theorem bbK13'_some (ro2 rl2 : Word) : bbK13' mo ml ro2 rl2 nPd s ip (some (r, m)) =
    bgoK3 (bsealW m mo ml ro2 rl2 nPd s ip (r.headD 0) (r.tail.headD 0)) := rfl
theorem bbK11_some : bbK11 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl lo ll s ip (some (r, m)) =
    bbK12 n nPd cto ctl cso csl rso rsl cvT0 cvR0 lo ll s ip (r.headD 0) (r.tail.headD 0)
      (brsW (n + 1) m no nl rso rsl) := rfl
theorem bbK10_some : bbK10 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (some (r, m)) =
    bbK11 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl lo ll s ip (bmoW (n + 1) m cto ctl io (r.headD 0)) := rfl
theorem bbK9_some (cof cl2 : Word) :
    bbK9 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip cof cl2 (some (r, m)) =
    bbK10 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip
      (bgW n m no nl (r.headD 0) nPd ctl cof cl2) := rfl
theorem bbK8_some : bbK8 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (some (r, m)) =
    bbK9 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (r.headD 0) (r.tail.headD 0)
      (plW (n + 1) m lo ll) := rfl
end arms
attribute [ind_grind] bbK13'_some bbK12_some bbK11_some bbK10_some
  bbK9_some bbK8_some

/-- **The model of `block_shape_fin`** (at exec fuel `n + 2`). -/
def bfW (n : Nat) (m : Mem) (nPd cto ctl cso csl rso rsl no nl io lo ll s ip : Word) :
    Option (List Word × Mem) :=
  bbK8 n nPd cto ctl cso csl rso rsl 0 (rdW (m.arr64 IW) (rdW (m.arr64 IW) rso)) no nl io lo ll s ip
    (bctW (n + 1) m cso csl)

/-- After `lvl_eq_c`. -/
def btK3 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl no nl io lo ll s : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bgoK3 (bfW n m nPd cto ctl cso csl rso rsl no nl io lo ll s (if r.headD 0 = 2 then 1 else 0))

/-- After `pin_word(53)`. -/
def btK2 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl no nl io lo ll s : Word) (m : Mem) :
    Option Word → Option (List Word × Mem)
  | none => none
  | some z => btK3 c n nPd cto ctl cso csl rso rsl no nl io lo ll s (c (n + 2) "lvl_eq_c" [s, z] m)

/-- After `block_shape_result_sort`. -/
def btK1 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl no nl io lo ll : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => btK2 c n nPd cto ctl cso csl rso rsl no nl io lo ll (r.headD 0) m (pinWordV m 53)

/-- **The model of `block_shape_tail`** (at exec fuel `n + 3`). -/
def btW (c : CallM) (n : Nat) (m : Mem) (nPd cto ctl cso csl rso rsl no nl io il lo ll : Word) :
    Option (List Word × Mem) :=
  btK1 c n nPd cto ctl cso csl rso rsl no nl io lo ll
    (bsoW m nPd io il (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cto + 3)))

/-- After `block_shape_pins_ok`. -/
def bbH4 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl no nl io il lo ll : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0, 0], m)
    else bgoK3 (btW c n m nPd cto ctl cso csl rso rsl no nl io il lo ll)

/-- After `er_to_iw`. -/
def bbH3 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl no nl io il : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbH4 c n nPd cto ctl cso csl rso rsl no nl io il (r.headD 0) (r.tail.headD 0)
      (bpoW (n + 2) m nPd cto ctl (r.headD 0) (r.tail.headD 0) rso rsl cso csl)

/-- After `block_member_counts`. -/
def bbH2 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 no nl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0, 0], m)
    else bbH3 c n nPd cto ctl cso csl rso rsl no nl (r.tail.headD 0) (r.tail.tail.headD 0)
      (erToIwW (n + 3) m (rdW (m.arr64 EREC) (cvT0 + 1)) (rdW (m.arr64 EREC) (cvT0 + 2)))

/-- After `block_shape_names_of`. -/
def bbH1 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbH2 c n nPd cto ctl cso csl rso rsl cvT0 (r.headD 0) (r.tail.headD 0)
      (bmcW (n + 2) m nPd ctl csl (r.headD 0) (r.tail.headD 0) rso rsl cto ctl)

/-- **The model of `block_shape_build`** (at exec fuel `n + 4`). -/
def bbW (c : CallM) (n : Nat) (m : Mem) (nPd cto ctl cso csl rso rsl : Word) : Option (List Word × Mem) :=
  bbH1 c n nPd cto ctl cso csl rso rsl (rdW (m.arr64 IW) cto) (bsnW (n + 3) m cto ctl)

section arms
variable (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 : Word) (m : Mem) (r : List Word)
  (no nl io il lo ll s z : Word)
theorem btK3_some : btK3 c n nPd cto ctl cso csl rso rsl no nl io lo ll s (some (r, m)) =
    bgoK3 (bfW n m nPd cto ctl cso csl rso rsl no nl io lo ll s (if r.headD 0 = 2 then 1 else 0)) := rfl
theorem btK2_some : btK2 c n nPd cto ctl cso csl rso rsl no nl io lo ll s m (some z) =
    btK3 c n nPd cto ctl cso csl rso rsl no nl io lo ll s (c (n + 2) "lvl_eq_c" [s, z] m) := rfl
theorem btK1_some : btK1 c n nPd cto ctl cso csl rso rsl no nl io lo ll (some (r, m)) =
    btK2 c n nPd cto ctl cso csl rso rsl no nl io lo ll (r.headD 0) m (pinWordV m 53) := rfl
theorem bbH4_fail (h : r.headD 0 = 0) : bbH4 c n nPd cto ctl cso csl rso rsl no nl io il lo ll (some (r, m)) =
    some ([0, 0], m) := by simp only [bbH4]; exact if_pos h
theorem bbH4_ok (h : ¬ r.headD 0 = 0) : bbH4 c n nPd cto ctl cso csl rso rsl no nl io il lo ll (some (r, m)) =
    bgoK3 (btW c n m nPd cto ctl cso csl rso rsl no nl io il lo ll) := by simp only [bbH4]; exact if_neg h
theorem bbH3_some : bbH3 c n nPd cto ctl cso csl rso rsl no nl io il (some (r, m)) =
    bbH4 c n nPd cto ctl cso csl rso rsl no nl io il (r.headD 0) (r.tail.headD 0)
      (bpoW (n + 2) m nPd cto ctl (r.headD 0) (r.tail.headD 0) rso rsl cso csl) := rfl
theorem bbH2_fail (h : r.headD 0 = 0) : bbH2 c n nPd cto ctl cso csl rso rsl cvT0 no nl (some (r, m)) =
    some ([0, 0], m) := by simp only [bbH2]; exact if_pos h
theorem bbH2_ok (h : ¬ r.headD 0 = 0) : bbH2 c n nPd cto ctl cso csl rso rsl cvT0 no nl (some (r, m)) =
    bbH3 c n nPd cto ctl cso csl rso rsl no nl (r.tail.headD 0) (r.tail.tail.headD 0)
      (erToIwW (n + 3) m (rdW (m.arr64 EREC) (cvT0 + 1)) (rdW (m.arr64 EREC) (cvT0 + 2))) := by
  simp only [bbH2]; exact if_neg h
theorem bbH1_some : bbH1 c n nPd cto ctl cso csl rso rsl cvT0 (some (r, m)) =
    bbH2 c n nPd cto ctl cso csl rso rsl cvT0 (r.headD 0) (r.tail.headD 0)
      (bmcW (n + 2) m nPd ctl csl (r.headD 0) (r.tail.headD 0) rso rsl cto ctl) := rfl
end arms
attribute [ind_grind] btK3_some btK2_some btK1_some bbH4_fail bbH4_ok bbH3_some bbH2_fail bbH2_ok bbH1_some

/-- **The program bundle of `blockShape?`.** -/
structure IndPartsProg5 (p : Prog) : Prop extends IndPartsProg4 p where
  resFrom : p.lookup "reserved_from" = some reservedFrom
  resCont : p.lookup "reserved_contains" = some reservedContains
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  slEq : p.lookup "sl_eq" = some slEq
  slGetD : p.lookup "sl_getd" = some slGetD
  pinWord : p.lookup "pin_word" = some pinWordL
  rec4 : p.lookup "rec4" = some rec4
  slGet : p.lookup "sl_get" = some slGet
  paramFind : p.lookup "param_find" = some paramFind
  paramPush : p.lookup "param_push" = some paramPush
  internParam : p.lookup "intern_param" = some internParam
  plGo : p.lookup "param_levels_go" = some paramLevelsGoL
  pl : p.lookup "param_levels" = some paramLevelsL
  il : IlF p
  namesOf : p.lookup "block_shape_names_of" = some blockShapeNamesOf
  pinsF : p.lookup "block_shape_pins_formers" = some blockShapePinsFormers
  pinsR : p.lookup "block_shape_pins_recs" = some blockShapePinsRecs
  pinsC : p.lookup "block_shape_pins_ctors" = some blockShapePinsCtors
  pinsOk : p.lookup "block_shape_pins_ok" = some blockShapePinsOk
  sort : p.lookup "block_shape_result_sort" = some blockShapeResultSort
  ctorsOf : p.lookup "block_shape_ctors_of" = some blockShapeCtorsOf
  membersOf : p.lookup "block_shape_members_of" = some blockShapeMembersOf
  rhssOf : p.lookup "block_shape_rhss_of" = some blockShapeRhssOf
  recsOf : p.lookup "block_shape_recs_of" = some blockShapeRecsOf
  large : p.lookup "block_shape_large" = some blockShapeLarge
  pack : p.lookup "block_shape_pack" = some blockShapePack
  sealF : p.lookup "block_shape_seal" = some blockShapeSeal
  fin : p.lookup "block_shape_fin" = some blockShapeFin
  tail : p.lookup "block_shape_tail" = some blockShapeTail
  build : p.lookup "block_shape_build" = some blockShapeBuild
  shape : p.lookup "block_shape" = some blockShape
  parts : p.lookup "block_parts" = some blockParts
  na : NaF p

set_option maxHeartbeats 20000000 in
theorem bf_spec (p : Prog) (hP : IndPartsProg5 p) (n : Nat) (s₀ : St)
    (nPd cto ctl cso csl rso rsl no nl io lo ll s ip : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 2)) "block_shape_fin"
      [nPd, cto, ctl, cso, csl, rso, rsl, no, nl, io, lo, ll, s, ip]
    ⦃fun r s' => LocEq s' s₀ ∧ bfW n s₀.mem nPd cto ctl cso csl rso rsl no nl io lo ll s ip = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.fin]
  simp only [callFn, blockShapeFin]
  sym (gen := 24) (instances := 30000) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bct_spec p hP.toIndPartsProg4 hP.ctorsOf (n + 1),
      plW_spec p hP.alloc hP.copy hP.cons hP.slGet hP.paramFind hP.paramPush hP.internParam hP.plGo hP.pl hP.il (n + 1),
      bg_spec p hP.toIndPartsProg hP.view hP.find hP.midx hP.cmem hP.gone hP.rec2 hP.ggo hP.groups n,
      bmo_spec p hP.toIndPartsProg4 hP.rec4 hP.membersOf (n + 1),
      brs_spec p hP.toIndPartsProg4 hP.rec6 hP.rhssOf hP.recsOf (n + 1),
      bsl_spec p hP.toIndPartsProg4 hP.erCopy hP.erToIw hP.slEq hP.large n,
      bseal_spec p hP.na hP.alloc hP.pack hP.sealF (n + 1)] <;>
    finish (gen := 20) [bfW, rdW_eq, bbK8_some, bbK9_some, bbK10_some, bbK11_some, bbK12_some,
      bbK13'_some, bgoK3_some]

set_option maxHeartbeats 20000000 in
theorem bt_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c) (n : Nat) (s₀ : St)
    (nPd cto ctl cso csl rso rsl no nl io il lo ll : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 3)) "block_shape_tail"
      [nPd, cto, ctl, cso, csl, rso, rsl, no, nl, io, il, lo, ll]
    ⦃fun r s' => LocEq s' s₀ ∧ btW c n s₀.mem nPd cto ctl cso csl rso rsl no nl io il lo ll = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.tail]
  simp only [callFn, blockShapeTail]
  sym (gen := 24) (instances := 30000) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bso_spec p hP.view hP.pinWord hP.slGetD hP.sort hP.strip (n + 1), pinWord_specV p hP.pinWord (n + 2),
      hc (n + 2) "lvl_eq_c", bf_spec p hP n] <;>
    finish (gen := 20) [btW, rdW_eq, btK1_some, btK2_some, btK3_some, bgoK3_some]

set_option maxHeartbeats 20000000 in
theorem bb_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c) (n : Nat) (s₀ : St) (nPd cto ctl cso csl rso rsl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 4)) "block_shape_build" [nPd, cto, ctl, cso, csl, rso, rsl]
    ⦃fun r s' => LocEq s' s₀ ∧ bbW c n s₀.mem nPd cto ctl cso csl rso rsl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.build]
  simp only [callFn, blockShapeBuild]
  sym (gen := 24) (instances := 30000) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bsn_spec p hP.toIndPartsProg4 hP.namesOf (n + 3), bmc_spec p hP.toIndPartsProg4 (n + 2),
      erToIw_specW p hP.alloc hP.erCopy hP.erToIw (n + 3),
      bpo_spec p hP.toIndPartsProg4 hP.resFrom hP.resCont hP.erCopy hP.erToIw hP.slEq hP.pinsF hP.pinsR
        hP.pinsC hP.pinsOk (n + 2), bt_spec p hP c hc n] <;>
    finish (gen := 20) [bbW, rdW_eq, bbH1_some, bbH2_fail, bbH2_ok, bbH3_some, bbH4_fail, bbH4_ok, bgoK3_some]

end L.Ind
