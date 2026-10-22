import ConAgua.Arena.IndPartsSpec2
import ConAgua.Arena.IndView
import ConAgua.Arena.WhnfSpineRefine
import ConAgua.Arena.IndStubs
import ConAgua.Arena.PinsNatOp

/-!
# Refinements of `IndParts`, part 3 (lane `indproofs`, helper `parts`)

`piBinders` and what is built on it.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `e_view` with the result's shape -/

theorem eViewShape (p : Prog) (hp : p.lookup "e_view" = some eView) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "e_view" [h]
    ⦃fun r _ => r = [r.headD 0, r.getD 1 0, r.getD 2 0, r.getD 3 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, eView]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [List.getD_cons_zero, List.getD_cons_succ, List.headD_cons]

/-- `e_view`'s spec with its four result words spelt out. -/
theorem eViewSpec4 (p : Prog) (hp : p.lookup "e_view" = some eView) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "e_view" [h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = eViewW s₀.mem h ∧
      r = [r.headD 0, r.getD 1 0, r.getD 2 0, r.getD 3 0]; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  have h1 := M.of_run (P := fun s => s = s₀) hs hrun (eView_spec p hp n s₀ h)
  have h2 := M.of_run (P := fun s => s = s₀) hs hrun (eViewShape p hp n s₀ h)
  exact ⟨h1.1, h1.2.1, h1.2.2, h2⟩

/-- A returning `e_view` of a `forallE` handle: the view checks hold and the words are the
binder's. -/
theorem eViewW_forall (m : Mem) (h : Word) (hg : h >>> 28 = 6) (hne : eViewW m h ≠ []) :
    viewOK m h 30 ∧ eViewW m h = [6, rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2),
      rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1), 0] := by
  unfold eViewW at hne ⊢
  have h1 : ¬ (4294967295 : Word) < h := fun c => by simp [c] at hne
  simp only [h1, if_false] at hne ⊢
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, if_false] at hne ⊢
  have n0 : ¬ h >>> 28 = 0 := by rw [hg]; decide
  have n1 : ¬ h >>> 28 = 1 := by rw [hg]; decide
  have n2 : ¬ h >>> 28 = 2 := by rw [hg]; decide
  have n3 : ¬ h >>> 28 = 3 := by rw [hg]; decide
  have n4 : ¬ h >>> 28 = 4 := by rw [hg]; decide
  have n5 : ¬ h >>> 28 = 5 := by rw [hg]; decide
  simp only [n0, n1, n2, n3, n4, n5, hg, if_false, if_true] at hne ⊢
  by_cases c : rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h
  · simp [c] at hne
  simp only [c, if_false]
  exact ⟨⟨hs, by simpa using c⟩, rfl⟩

/-! ## `pi_binders` -/

mutual
/-- **The model of `pi_binders`** (the L fuel `n`; the word `fuel` is the twin's). -/
def piBW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, fuel, h =>
    if fuel = 0 then none
    else if h >>> 28 ≠ 6 then some ([0, 0, h], m)
    else piBK1 n m fuel (eViewW m h)

/-- After `e_view`. -/
def piBK1 (n : Nat) (m : Mem) (fuel : Word) (r : List Word) : Option (List Word × Mem) :=
  if r = [] then none
  else piBK2 n fuel (r.getD 1 0) (piBW n m (fuel - 1) (r.getD 2 0))

/-- After the recursive call. -/
def piBK2 (n : Nat) (fuel ty : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs, m1) => piBK3 (rs.getD 2 0) (consW n m1 ty (rs.headD 0) (rs.getD 1 0))

/-- After `sl_cons`. -/
def piBK3 (be : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0, r.getD 1 0, be], m2)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (fuel h ty be : Word) (r rs : List Word)
theorem piBW_fuel0 (hf : fuel = 0) : piBW (n + 1) m fuel h = none := by simp [piBW, hf]
theorem piBW_leaf (hf : fuel ≠ 0) (hg : h >>> 28 ≠ 6) :
    piBW (n + 1) m fuel h = some ([0, 0, h], m) := by simp [piBW, hf, hg]
theorem piBW_node (hf : fuel ≠ 0) (hg : ¬ h >>> 28 ≠ 6) :
    piBW (n + 1) m fuel h = piBK1 n m fuel (eViewW m h) := by simp [piBW, hf, hg]
theorem piBK1_nil : piBK1 n m fuel [] = none := by simp [piBK1]
theorem piBK1_ne (hr : r ≠ []) :
    piBK1 n m fuel r = piBK2 n fuel (r.getD 1 0) (piBW n m (fuel - 1) (r.getD 2 0)) := by
  simp [piBK1, hr]
theorem piBK2_some : piBK2 n fuel ty (some (rs, m1)) =
    piBK3 (rs.getD 2 0) (consW n m1 ty (rs.headD 0) (rs.getD 1 0)) := rfl
theorem piBK3_some : piBK3 be (some (r, m2)) = some ([r.headD 0, r.getD 1 0, be], m2) := rfl
end arms

grind_pattern [ind_grind] piBW_fuel0 => piBW (n + 1) m fuel h
grind_pattern [ind_grind] piBW_leaf => piBW (n + 1) m fuel h
grind_pattern [ind_grind] piBW_node => piBW (n + 1) m fuel h
grind_pattern [ind_grind] piBK1_ne => piBK1 n m fuel r
grind_pattern [ind_grind] piBK2_some => piBK2 n fuel ty (some (rs, m1))
grind_pattern [ind_grind] piBK3_some => piBK3 be (some (r, m2))

theorem consW_two {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word}
    (h : consW n m x o l = some (r, m')) : r = [r.headD 0, r.getD 1 0] := by
  simp only [consW] at h
  by_cases h0 : l + 1 = 0
  · simp [h0] at h
  simp only [h0, if_false] at h
  cases hal : allocW m (l + 1) with
  | none => simp [hal] at h
  | some qm =>
    obtain ⟨q, m1⟩ := qm
    simp only [hal] at h
    cases hcp : copyW (n - 1) (m1.set64 IW q x) (q + 1) o l with
    | none => simp [hcp] at h
    | some m2 =>
      simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl

theorem piBW_three {n : Nat} {m m' : Mem} {fuel h : Word} {r : List Word}
    (hh : piBW n m fuel h = some (r, m')) : r = [r.headD 0, r.getD 1 0, r.getD 2 0] := by
  cases n with
  | zero => simp [piBW] at hh
  | succ n =>
    by_cases hf : fuel = 0
    · rw [piBW_fuel0 n m fuel h hf] at hh; simp at hh
    by_cases hg : h >>> 28 ≠ 6
    · rw [piBW_leaf n m fuel h hf hg] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh
      obtain ⟨rfl, -⟩ := hh; rfl
    · rw [piBW_node n m fuel h hf hg] at hh
      by_cases hr : eViewW m h = []
      · rw [hr, piBK1_nil] at hh; simp at hh
      rw [piBK1_ne n m fuel _ hr] at hh
      cases hrec : piBW n m (fuel - 1) ((eViewW m h).getD 2 0) with
      | none => rw [hrec] at hh; simp [piBK2] at hh
      | some rm =>
        obtain ⟨rs, m1⟩ := rm
        rw [hrec, piBK2_some] at hh
        cases hcons : consW n m1 ((eViewW m h).getD 1 0) (rs.headD 0) (rs.getD 1 0) with
        | none => rw [hcons] at hh; simp [piBK3] at hh
        | some rm2 =>
          obtain ⟨r2, m2⟩ := rm2
          rw [hcons, piBK3_some] at hh
          simp only [Option.some.injEq, Prod.mk.injEq] at hh
          obtain ⟨rfl, -⟩ := hh
          rfl

theorem slConsSpec2 (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hp : p.lookup "sl_cons" = some slCons) (n : Nat)
    (s₀ : St) (x o l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "sl_cons" [x, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ consW n s₀.mem x o l = some (r, s'.mem) ∧
      r = [r.headD 0, r.getD 1 0]; ⊤⦄ :=
  triple_post (slCons_specW p ha hc hp n s₀ x o l) (fun r s' ⟨h1, h2⟩ => ⟨h1, h2, consW_two h2⟩)

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hv : p.lookup "e_view" = some eView)
  (hs : p.lookup "sl_cons" = some slCons)
  (hp : p.lookup "pi_binders" = some piBinders)
include ha hc hv hs hp

theorem piBinders_spec (n : Nat) : ∀ (s₀ : St) (fuel h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_binders" [fuel, h]
    ⦃fun r s' => LocEq s' s₀ ∧ piBW n s₀.mem fuel h = some (r, s'.mem) ∧
      r = [r.headD 0, r.getD 1 0, r.getD 2 0]; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ fuel h; rw [invoke_eq _ hp]; simp only [callFn, piBinders]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ fuel h
    rw [invoke_eq _ hp]
    simp only [callFn, piBinders]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        eViewSpec4 p hv n, slConsSpec2 p ha hc hs n, ih] <;>
      finish (gen := 20) [List.getD_cons_zero, List.getD_cons_succ, List.headD_cons, Sig.retVal]

theorem piBinders_spec' (n : Nat) (s₀ : St) (fuel h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_binders" [fuel, h]
    ⦃fun r s' => LocEq s' s₀ ∧ piBW n s₀.mem fuel h = some (r, s'.mem); ⊤⦄ :=
  triple_post (piBinders_spec p ha hc hv hs hp n s₀ fuel h) (fun r s' ⟨h1, h2, _⟩ => ⟨h1, h2⟩)

end spec


theorem piBW_ok (n : Nat) : ∀ (m m' : Mem) (a : AState) (fuel h : Word) (rs : List Word),
    ArenaR m a → piBW n m fuel h = some (rs, m') → h.toNat < 2 ^ 32 →
    (m.arr64 IW).size < 2 ^ 64 → 200 < (m.arr64 CTL).size →
    ∃ bs e, (ConRon.Arena.piBinders fuel.toNat (decE h)).run a = .ok ((bs, e), a) ∧
      rs = [rs.headD 0, rs.getD 1 0, rs.getD 2 0] ∧
      decHL m' (rs.headD 0).toNat (rs.getD 1 0).toNat = some bs ∧
      (rs.getD 2 0).toNat < 2 ^ 32 ∧ decE (rs.getD 2 0) = e ∧
      IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
      (rs.headD 0).toNat + (rs.getD 1 0).toNat ≤ iwTop m' := by
  induction n with
  | zero => intro m m' a fuel h rs _ hh; simp [piBW] at hh
  | succ n ih =>
    intro m m' a fuel h rs hR hpb hh hsz hc
    by_cases hf : fuel = 0
    · rw [piBW_fuel0 n m fuel h hf] at hpb; simp at hpb
    by_cases hg : h >>> 28 ≠ 6
    · rw [piBW_leaf n m fuel h hf hg] at hpb
      simp only [Option.some.injEq, Prod.mk.injEq] at hpb
      obtain ⟨rfl, rfl⟩ := hpb
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
        (fun h0 => hf (UInt64.toNat_inj.mp (by simpa using h0)))
      have htag : (decE h).tag ≠ ETag.forallE := fun h' => hg ((decE_tag_forall h hh).mp h')
      refine ⟨[], decE h, ?_, rfl, ?_, hh, rfl, IWGrow.refl m, MemFrame.refl _ _ m, by simp⟩
      · rw [hk, ConRon.Arena.piBinders]; simp [htag]; rfl
      · simp [decHL, hslice?]
    · rw [piBW_node n m fuel h hf hg] at hpb
      have hg6 : h >>> 28 = 6 := by simpa using hg
      by_cases hr : eViewW m h = []
      · rw [hr, piBK1_nil] at hpb; simp at hpb
      obtain ⟨hvok, hew⟩ := eViewW_forall m h hg6 hr
      rw [piBK1_ne n m fuel _ hr] at hpb
      cases hrec : piBW n m (fuel - 1) ((eViewW m h).getD 2 0) with
      | none => rw [hrec] at hpb; simp [piBK2] at hpb
      | some rm =>
        obtain ⟨rs1, m1⟩ := rm
        rw [hrec, piBK2_some] at hpb
        cases hcons : consW n m1 ((eViewW m h).getD 1 0) (rs1.headD 0) (rs1.getD 1 0) with
        | none => rw [hcons] at hpb; simp [piBK3] at hpb
        | some rm2 =>
          obtain ⟨r2, m2⟩ := rm2
          rw [hcons, piBK3_some] at hpb
          simp only [Option.some.injEq, Prod.mk.injEq] at hpb
          obtain ⟨rfl, rfl⟩ := hpb
          obtain ⟨hvw, hty, hb⟩ := view_forall m a hR h hh hvok hg6
          have hty2 : ((eViewW m h).getD 1 0).toNat < 2 ^ 32 := by rw [hew]; exact hty
          have hb2 : ((eViewW m h).getD 2 0).toNat < 2 ^ 32 := by rw [hew]; exact hb
          have hbeq : (eViewW m h).getD 2 0 = rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1) := by
            rw [hew]; rfl
          have hteq : (eViewW m h).getD 1 0 = rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2) := by
            rw [hew]; rfl
          have hfm1 : (fuel - 1).toNat = fuel.toNat - 1 := by
            have : fuel.toNat ≠ 0 := fun h0 => hf (UInt64.toNat_inj.mp (by simpa using h0))
            rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp
          obtain ⟨bs1, e1, hrun1, hsh1, hdec1, hbe1, hbe2, hg1, hf1, hle1⟩ :=
            ih m m1 a (fuel - 1) _ rs1 hR hrec hb2 hsz hc
          have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := by rw [hf1.2.2.1 IW]; exact hsz
          have hc1 : 200 < (m1.arr64 CTL).size := by rw [hf1.2.2.1 CTL]; exact hc
          obtain ⟨hr2, hdec2, hg2, hf2, hl1, htop2⟩ :=
            consW_dec hcons hsz1 hc1 hle1 hty2 hdec1
          have hk : fuel.toNat = (fuel.toNat - 1) + 1 := by
            have : fuel.toNat ≠ 0 := fun h0 => hf (UInt64.toNat_inj.mp (by simpa using h0))
            omega
          refine ⟨decE ((eViewW m h).getD 1 0) :: bs1, e1, ?_, ?_, ?_, ?_, ?_, hg1.trans hg2,
            hf1.trans hf2, ?_⟩
          · rw [hk, ConRon.Arena.piBinders, (decE_tag_forall h hh).mpr hg6]
            have hvb := viewBind_forall m a hR h hh hvok hg6
            rw [← hbeq, ← hteq] at hvb
            simp only [beq_self_eq_true, if_true, StateT.run_bind, viewBind_run' _ a, hvb,
              except_ok_bind]
            rw [← hfm1]
            rw [hrun1]
            rfl
          · simp
          · simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
            rw [hr2]
            simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
            exact hdec2
          · simp only [List.getD_cons_succ, List.getD_cons_zero]; exact hbe1
          · simp only [List.getD_cons_succ, List.getD_cons_zero]; exact hbe2
          · rw [hr2]
            simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
            omega

/-- **`pi_binders` is `piBinders`**: under `ArenaR`, a returning run is a successful twin run
(no state change) whose binders are the new `IW` slice and whose body is the third result. -/
@[refines ConRon.Arena.piBinders]
theorem piBinders_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hv : p.lookup "e_view" = some eView)
    (hs : p.lookup "sl_cons" = some slCons) (hp : p.lookup "pi_binders" = some piBinders)
    (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (fuel h : Word)
    (hh : h.toNat < 2 ^ 32) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hcl : 200 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_binders" [fuel, h]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [r.headD 0, r.getD 1 0, r.getD 2 0] ∧
      (∃ bs e, (ConRon.Arena.piBinders fuel.toNat (decE h)).run a₀ = .ok ((bs, e), a₀) ∧
        decHL s'.mem (r.headD 0).toNat (r.getD 1 0).toNat = some bs ∧
        (r.getD 2 0).toNat < 2 ^ 32 ∧ decE (r.getD 2 0) = e) ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem ∧
      (r.headD 0).toNat + (r.getD 1 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  refine triple_post (piBinders_spec' p ha hc hv hs hp n s₀ fuel h) ?_
  intro r s' ⟨hl, hm⟩
  obtain ⟨bs, e, hrun, hsh, hdec, hb1, hb2, hg, hf, hle⟩ :=
    piBW_ok n s₀.mem s'.mem a₀ fuel h r hR hm hh hsz hcl
  exact ⟨hl, hsh, ⟨bs, e, hrun, hdec, hb1, hb2⟩, hg, hf, hle⟩


theorem viewConst_run' (h : EIdx) (a : AState) :
    (viewConst h).run a = .ok (a.store.viewConst h, a) := rfl

theorem mapM_opt_congr3 {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons]
    rw [h x (List.mem_cons_self ..),
      mapM_opt_congr3 f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- A decoded handle slice below the pool's top survives growth. -/
theorem decHL_grow3 {k : IdxKind} {m m' : Mem} (hg : IWGrow m m') {o l : Nat}
    (h : o + l ≤ iwTop m) : (decHL m' o l : Option (List (Idx k))) = decHL m o l := by
  simp only [decHL, hslice?]
  apply mapM_opt_congr3
  intro j hj
  have hj' : j < l := List.mem_range.mp hj
  simp only [hd?, iwA]
  rw [hg.2.2.1 (o + j) (by omega)]

/-- A returning `e_view` of a `const` handle. -/
theorem eViewW_const (m : Mem) (h : Word) (hg : h >>> 28 = 3) (hne : eViewW m h ≠ []) :
    viewOK m h 18 ∧ eViewW m h = [3, rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2),
      rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1), 0] := by
  unfold eViewW at hne ⊢
  have h1 : ¬ (4294967295 : Word) < h := fun c => by simp [c] at hne
  simp only [h1, if_false] at hne ⊢
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, if_false] at hne ⊢
  have n0 : ¬ h >>> 28 = 0 := by rw [hg]; decide
  have n1 : ¬ h >>> 28 = 1 := by rw [hg]; decide
  have n2 : ¬ h >>> 28 = 2 := by rw [hg]; decide
  simp only [n0, n1, n2, hg, if_false, if_true] at hne ⊢
  by_cases c : rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h
  · simp [c] at hne
  simp only [c, if_false]
  exact ⟨⟨hs, by simpa using c⟩, rfl⟩

/-- The `viewConst` projection of a `const` handle. -/
theorem viewConst_ok (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h 18) :
    a.store.viewConst (decE h) = some (decI (rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2)),
      decI (rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1))) := by
  obtain ⟨k, hk, hn, hu⟩ := node_of m a h constSch CeRecRel cehash (·.consts) _ hR.const hv.2
  simp only [EStore.viewConst, EStore.persGetConst]
  rw [proj_tier m a hR h hh (fun t i => t.getConst i) hv.1]
  simp only [ETables.getConst, Tbl.node?, decE_idx]
  rw [hk]
  simp [hn, hu, decI_word]

/-! ## `rec_target_of` -/

mutual
/-- **The model of `rec_target_of`**: strip the telescope, look at the major's domain head. -/
def recTW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, no, nl, mI, ty => recTK1 n no nl (stubM "strip_pis" m [mI, ty])

/-- After `strip_pis`. -/
def recTK1 (n : Nat) (no nl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([nl], m1)
    else if r.tail.tail.tail.headD 0 >>> 28 ≠ 6 then some ([nl], m1)
    else recTK2 n no nl m1 (eViewW m1 (r.tail.tail.tail.headD 0))

/-- After the major's `e_view`. -/
def recTK2 (n : Nat) (no nl : Word) (m1 : Mem) : List Word → Option (List Word × Mem)
  | [] => none
  | v => recTK3 n no nl (stubM "get_app_fn" m1 [CWF, v.getD 1 0])

/-- After `get_app_fn`. -/
def recTK3 (n : Nat) (no nl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) =>
    if r.headD 0 >>> 28 ≠ 3 then some ([nl], m3)
    else recTK4 n no nl m3 (eViewW m3 (r.headD 0))

/-- After the head's `e_view`. -/
def recTK4 (n : Nat) (no nl : Word) (m3 : Mem) : List Word → Option (List Word × Mem)
  | [] => none
  | v => recTK5 nl m3 (findW n m3 no nl (v.getD 1 0))

/-- After `sl_find`. -/
def recTK5 (nl : Word) (m3 : Mem) : Option (List Word) → Option (List Word × Mem)
  | none => none
  | some rf => if rf.headD 0 = 0 then some ([nl], m3) else some ([rf.tail.headD 0], m3)
end

section arms
variable (n : Nat) (m m1 m3 : Mem) (no nl mI ty : Word) (r v rf : List Word)
theorem recTW_step : recTW (n + 1) m no nl mI ty = recTK1 n no nl (stubM "strip_pis" m [mI, ty]) := rfl
theorem recTK1_some_nil (h : r.headD 0 = 0) : recTK1 n no nl (some (r, m1)) = some ([nl], m1) := by
  simp only [recTK1]; rw [if_pos h]
theorem recTK1_some_nf (h : r.headD 0 ≠ 0) (h2 : r.tail.tail.tail.headD 0 >>> 28 ≠ 6) :
    recTK1 n no nl (some (r, m1)) = some ([nl], m1) := by
  simp only [recTK1]; rw [if_neg h, if_pos h2]
theorem recTK1_some_f (h : r.headD 0 ≠ 0) (h2 : ¬ r.tail.tail.tail.headD 0 >>> 28 ≠ 6) :
    recTK1 n no nl (some (r, m1)) =
      recTK2 n no nl m1 (eViewW m1 (r.tail.tail.tail.headD 0)) := by
  simp only [recTK1]; rw [if_neg h, if_neg h2]
theorem recTK2_nil : recTK2 n no nl m1 [] = none := rfl
theorem recTK2_ne (h : v ≠ []) :
    recTK2 n no nl m1 v = recTK3 n no nl (stubM "get_app_fn" m1 [CWF, v.getD 1 0]) := by
  cases v with
  | nil => exact absurd rfl h
  | cons a as => rfl
theorem recTK3_some_nc (h : r.headD 0 >>> 28 ≠ 3) : recTK3 n no nl (some (r, m3)) = some ([nl], m3) := by
  simp only [recTK3]; rw [if_pos h]
theorem recTK3_some_c (h : ¬ r.headD 0 >>> 28 ≠ 3) :
    recTK3 n no nl (some (r, m3)) = recTK4 n no nl m3 (eViewW m3 (r.headD 0)) := by
  simp only [recTK3]; rw [if_neg h]
theorem recTK4_nil : recTK4 n no nl m3 [] = none := rfl
theorem recTK4_ne (h : v ≠ []) :
    recTK4 n no nl m3 v = recTK5 nl m3 (findW n m3 no nl (v.getD 1 0)) := by
  cases v with
  | nil => exact absurd rfl h
  | cons a as => rfl
theorem recTK5_miss (h : rf.headD 0 = 0) : recTK5 nl m3 (some rf) = some ([nl], m3) := by
  simp only [recTK5]; rw [if_pos h]
theorem recTK5_hit (h : rf.headD 0 ≠ 0) : recTK5 nl m3 (some rf) = some ([rf.tail.headD 0], m3) := by
  simp only [recTK5]; rw [if_neg h]
end arms

grind_pattern [ind_grind] recTW_step => recTW (n + 1) m no nl mI ty
grind_pattern [ind_grind] recTK1_some_nil => recTK1 n no nl (some (r, m1))
grind_pattern [ind_grind] recTK1_some_nf => recTK1 n no nl (some (r, m1))
grind_pattern [ind_grind] recTK1_some_f => recTK1 n no nl (some (r, m1))
grind_pattern [ind_grind] recTK2_ne => recTK2 n no nl m1 v
grind_pattern [ind_grind] recTK3_some_nc => recTK3 n no nl (some (r, m3))
grind_pattern [ind_grind] recTK3_some_c => recTK3 n no nl (some (r, m3))
grind_pattern [ind_grind] recTK4_ne => recTK4 n no nl m3 v
grind_pattern [ind_grind] recTK5_miss => recTK5 nl m3 (some rf)
grind_pattern [ind_grind] recTK5_hit => recTK5 nl m3 (some rf)

section spec
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
  (hp : p.lookup "rec_target_of" = some recTargetOf)
include hv hf hp

theorem recTargetOf_spec (n : Nat) (s₀ : St) (no nl mI ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec_target_of" [no, nl, mI, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ recTW n s₀.mem no nl mI ty = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, recTargetOf]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "strip_pis" n, stubM_spec p "get_app_fn" n, eViewSpec4 p hv n,
        slFind_spec p hf n] <;>
      finish (gen := 20)

end spec


theorem decE_tag_const (e : Word) (hh : e.toNat < 2 ^ 32) :
    ((decE e).tag = ETag.const) ↔ e >>> 28 = 3 := decE_tag_eq e hh 3 (by decide)

theorem findIdx_decI (ws : List Word) (x : Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) :
    ((ws.map (decI : Word → NIdx)).findIdx? (· == (decI x : NIdx))) = ws.findIdx? (· == x) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.findIdx?_cons]
    have hw := hws w (List.mem_cons_self ..)
    rw [L.Arena.decI_beq w x hw hx]
    by_cases h : w = x
    · simp [h]
    · simp only [h, decide_false, Bool.false_eq_true, if_false, beq_iff_eq]
      rw [ih (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw'))]

theorem recTW_ok (n : Nat) : ∀ (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl mI ty : Word) (r : List Word) (names : List NIdx),
    recTW n m no nl mI ty = some (r, m') → StageR dn vis fe m a → ty.toNat < 2 ^ 32 →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat < 2 ^ 64 →
    no.toNat + nl.toNat ≤ iwTop m →
    ∃ t a', (ConRon.Arena.recTargetOf names mI.toNat (decI ty)).run a = .ok (t, a') ∧
      r = [UInt64.ofNat t] ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  intro dn fe vis m m' a no nl mI ty r names hrt hS hty hnames hb hbt
  cases n with
  | zero => simp [recTW] at hrt
  | succ n =>
  have hnl : nl.toNat = names.length := (decHL_length m hnames).symm
  rw [recTW_step] at hrt
  cases hra : stubM "strip_pis" m [mI, ty] with
  | none => rw [hra] at hrt; simp [recTK1] at hrt
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [hra] at hrt
  obtain ⟨x1, a1, hrun1, hS1, hg1, hdec1⟩ := stripPis_spec dn vis fe mI ty hty m m1 a r1 hra hS
  have hty' : (decI ty : EIdx) = decE ty := rfl
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hdec1
    rw [recTK1_some_nil n m1 no nl r1 h0] at hrt
    simp only [Option.some.injEq, Prod.mk.injEq] at hrt
    obtain ⟨rfl, rfl⟩ := hrt
    refine ⟨names.length, a1, ?_, ?_, hS1, hg1⟩
    · simp only [ConRon.Arena.recTargetOf, StateT.run_bind, hrun1, except_ok_bind]
      rfl
    · have : UInt64.ofNat names.length = nl := by rw [← hnl]; exact ofNat_toNat_word nl
      rw [this]
  | some q =>
    obtain ⟨l1, e1⟩ := q
    obtain ⟨h1, -, hbl, hbe⟩ := hdec1
    have h1ne : r1.headD 0 ≠ 0 := by rw [h1]; decide
    have hd3 : r1.drop 3 = r1.tail.tail.tail := by
      cases r1 with
      | nil => rfl
      | cons a as =>
        cases as with
        | nil => rfl
        | cons b bs => cases bs with
          | nil => rfl
          | cons c cs => rfl
    rw [hd3] at hbl hbe
    have hR1 : ArenaR m1 a1 := hS1.1.arena.1
    have hnamesz : names.length = nl.toNat := hnl.symm
    by_cases hg6 : r1.tail.tail.tail.headD 0 >>> 28 ≠ 6
    · rw [recTK1_some_nf n m1 no nl r1 h1ne hg6] at hrt
      simp only [Option.some.injEq, Prod.mk.injEq] at hrt
      obtain ⟨rfl, rfl⟩ := hrt
      have htag : e1.tag ≠ ETag.forallE := by
        rw [← hbe]; exact fun h' => hg6 ((decE_tag_forall _ hbl).mp h')
      refine ⟨names.length, a1, ?_, ?_, hS1, hg1⟩
      · simp only [ConRon.Arena.recTargetOf, StateT.run_bind, hrun1, except_ok_bind]
        simp [htag]
        rfl
      · have : UInt64.ofNat names.length = nl := by rw [← hnl]; exact ofNat_toNat_word nl
        rw [this]
    · have hg6' : r1.tail.tail.tail.headD 0 >>> 28 = 6 := by simpa using hg6
      rw [recTK1_some_f n m1 no nl r1 h1ne hg6] at hrt
      by_cases hr : eViewW m1 (r1.tail.tail.tail.headD 0) = []
      · rw [hr, recTK2_nil] at hrt; simp at hrt
      obtain ⟨hvok, hew⟩ := eViewW_forall m1 _ hg6' hr
      rw [recTK2_ne n m1 no nl _ hr] at hrt
      obtain ⟨hvw, hty2, hb2⟩ := view_forall m1 a1 hR1 _ hbl hvok hg6'
      have hdomw : (eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0 =
          rdW (m1.arr64 FAREC) (idxW (r1.tail.tail.tail.headD 0) * 4 +
            tierW (r1.tail.tail.tail.headD 0) * 2) := by rw [hew]; rfl
      have hdomlt : ((eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0).toNat < 2 ^ 32 := by
        rw [hdomw]; exact hty2
      cases hra3 : stubM "get_app_fn" m1 [CWF, (eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0] with
      | none => rw [hra3] at hrt; simp [recTK3] at hrt
      | some rm3 =>
      obtain ⟨r3, m3⟩ := rm3
      rw [hra3] at hrt
      obtain ⟨x3, a3, hrun3, hS3, hg3, hdl3, hdI3⟩ :=
        getAppFn_spec dn vis fe CWF _ hdomlt m1 m3 a1 r3 hra3 hS1
      have hR3 : ArenaR m3 a3 := hS3.1.arena.1
      have hvb := viewBind_forall m1 a1 hR1 _ hbl hvok hg6'
      by_cases hc : r3.headD 0 >>> 28 ≠ 3
      · rw [recTK3_some_nc n m3 no nl r3 hc] at hrt
        simp only [Option.some.injEq, Prod.mk.injEq] at hrt
        obtain ⟨rfl, rfl⟩ := hrt
        have htag : x3.tag ≠ ETag.const := by
          rw [← hdI3]; exact fun h' => hc ((decE_tag_const _ hdl3).mp h')
        refine ⟨names.length, a3, ?_, ?_, hS3, hg1.trans hg3⟩
        · subst hbe
          have hvb' : a1.store.viewBind (decI (r1.tail.tail.tail.headD 0)) = some
              (decE ((eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0),
               decE ((eViewW m1 (r1.tail.tail.tail.headD 0)).getD 2 0)) := by
            rw [hew]; exact hvb
          have hftag : ((decI (r1.tail.tail.tail.headD 0) : EIdx).tag == ETag.forallE) = true := by
            simp only [beq_iff_eq]; exact (decE_tag_forall _ hbl).mpr hg6'
          simp only [ConRon.Arena.recTargetOf, StateT.run_bind, hrun1, except_ok_bind, hftag,
            if_true, viewBind_run' _ a1, hvb']
          have hrun3' : StateT.run (getAppFn coreWalkFuel (decE
              ((eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0))) a1 = Except.ok (x3, a3) := by
            rw [← CWF_eq]; exact hrun3
          have hctag : (x3.tag == ETag.const) = false := by
            simpa using htag
          simp only [hrun3', except_ok_bind, hctag]
          rfl
        · have : UInt64.ofNat names.length = nl := by rw [← hnl]; exact ofNat_toNat_word nl
          rw [this]
      · have hc3 : r3.headD 0 >>> 28 = 3 := by simpa using hc
        rw [recTK3_some_c n m3 no nl r3 hc] at hrt
        by_cases hr2 : eViewW m3 (r3.headD 0) = []
        · rw [hr2, recTK4_nil] at hrt; simp at hrt
        obtain ⟨hvok2, hew2⟩ := eViewW_const m3 _ hc3 hr2
        rw [recTK4_ne n m3 no nl _ hr2] at hrt
        obtain ⟨hvc, hn2, hu2⟩ := view_const_f m3 a3 hR3 _ hdl3 hvok2 hc3
        have hxw : (eViewW m3 (r3.headD 0)).getD 1 0 =
            rdW (m3.arr64 CREC) (idxW (r3.headD 0) * 4 + tierW (r3.headD 0) * 2) := by
          rw [hew2]; rfl
        have hxlt : ((eViewW m3 (r3.headD 0)).getD 1 0).toNat < 2 ^ 32 := by rw [hxw]; exact hn2
        have hvcc := viewConst_ok m3 a3 hR3 _ hdl3 hvok2
        have hnames3 : decHL m3 no.toNat nl.toNat = some names := by
          rw [decHL_grow3 (hg1.trans hg3) hbt]; exact hnames
        obtain ⟨ws, hws, hnm, hwlt⟩ := slR_of_decHL m3 nl.toNat no.toNat names hnames3 hb
        rw [ofNat_toNat_word, ofNat_toNat_word] at hws
        have hlen : ws.length < 2 ^ 64 := by
          have := decHL_length m3 hnames3
          rw [hnm] at this; simp at this; omega
        cases hf : findW n m3 no nl ((eViewW m3 (r3.headD 0)).getD 1 0) with
        | none => rw [hf] at hrt; simp [recTK5] at hrt
        | some rf =>
        have hfk := findW_ok n m3 no nl _ rf ws hws hf hlen
        have hfi := findIdx_decI ws _ hwlt hxlt
        rw [← hnm] at hfi
        have hrun3' : StateT.run (getAppFn coreWalkFuel (decE
            ((eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0))) a1 = Except.ok (x3, a3) := by
          rw [← CWF_eq]; exact hrun3
        have hctag : (x3.tag == ETag.const) = true := by
          simp only [beq_iff_eq]; rw [← hdI3]; exact (decE_tag_const _ hdl3).mpr hc3
        have hvcc' : a3.store.viewConst x3 = some
            (decI ((eViewW m3 (r3.headD 0)).getD 1 0), decI ((eViewW m3 (r3.headD 0)).getD 2 0)) := by
          rw [← hdI3, hew2]; exact hvcc
        subst hbe
        have hvb' : a1.store.viewBind (decI (r1.tail.tail.tail.headD 0)) = some
            (decE ((eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0),
             decE ((eViewW m1 (r1.tail.tail.tail.headD 0)).getD 2 0)) := by
          rw [hew]; exact hvb
        have hftag : ((decI (r1.tail.tail.tail.headD 0) : EIdx).tag == ETag.forallE) = true := by
          simp only [beq_iff_eq]; exact (decE_tag_forall _ hbl).mpr hg6'
        rw [hf] at hrt
        by_cases hf0 : rf.headD 0 = 0
        · rw [recTK5_miss m3 nl rf hf0] at hrt
          simp only [Option.some.injEq, Prod.mk.injEq] at hrt
          obtain ⟨rfl, rfl⟩ := hrt
          have hnone : ws.findIdx? (· == (eViewW m3 (r3.headD 0)).getD 1 0) = none := by
            rw [hfk] at hf0
            cases h' : ws.findIdx? (· == (eViewW m3 (r3.headD 0)).getD 1 0) with
            | none => rfl
            | some i => rw [h'] at hf0; simp at hf0
          refine ⟨names.length, a3, ?_, ?_, hS3, hg1.trans hg3⟩
          · simp only [ConRon.Arena.recTargetOf, StateT.run_bind, hrun1, except_ok_bind, hftag,
              if_true, viewBind_run' _ a1, hvb', hrun3', hctag, viewConst_run', hvcc', hfi, hnone]
            rfl
          · have : UInt64.ofNat names.length = nl := by rw [← hnl]; exact ofNat_toNat_word nl
            rw [this]
        · rw [recTK5_hit m3 nl rf hf0] at hrt
          simp only [Option.some.injEq, Prod.mk.injEq] at hrt
          obtain ⟨rfl, rfl⟩ := hrt
          obtain ⟨i, hi⟩ : ∃ i, ws.findIdx? (· == (eViewW m3 (r3.headD 0)).getD 1 0) = some i := by
            rw [hfk] at hf0
            cases h' : ws.findIdx? (· == (eViewW m3 (r3.headD 0)).getD 1 0) with
            | none => rw [h'] at hf0; simp at hf0
            | some i => exact ⟨i, rfl⟩
          refine ⟨i, a3, ?_, ?_, hS3, hg1.trans hg3⟩
          · simp only [ConRon.Arena.recTargetOf, StateT.run_bind, hrun1, except_ok_bind, hftag,
              if_true, viewBind_run' _ a1, hvb', hrun3', hctag, viewConst_run', hvcc', hfi, hi]
            rfl
          · rw [hfk, hi]; rfl


/-- **`rec_target_of` refines `recTargetOf`** (through the stubs `strip_pis`, `get_app_fn`). -/
@[refines ConRon.Arena.recTargetOf]
theorem recTargetOf_refines (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hp : p.lookup "rec_target_of" = some recTargetOf)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis no nl mI ty : Word) (names : List NIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hty : ty.toNat < 2 ^ 32) (hnames : decHL s₀.mem no.toNat nl.toNat = some names)
    (hb : no.toNat + nl.toNat < 2 ^ 64) (hbt : no.toNat + nl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec_target_of" [no, nl, mI, ty]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.recTargetOf names mI.toNat (decI ty)) a₀ ∧
      r = [UInt64.ofNat (AM.res (ConRon.Arena.recTargetOf names mI.toNat (decI ty)) a₀)] ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.recTargetOf names mI.toNat (decI ty)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (recTargetOf_spec p hv hf hp n s₀ no nl mI ty) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨t, a', hrun, hr, hS', hg⟩ := recTW_ok n dn fe vis s₀.mem s'.mem a₀ no nl mI ty r names hm
    hS hty hnames hb hbt
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hr, by rw [hst]; exact hS', hg⟩

end L.Ind
