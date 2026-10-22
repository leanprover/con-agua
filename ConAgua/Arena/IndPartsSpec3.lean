import ConAgua.Arena.IndPartsSpec2
import ConAgua.Arena.IndView
import ConAgua.Arena.WhnfSpineRefine

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

end L.Ind
