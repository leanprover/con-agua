import ConAgua.Arena.DefEqMidLams

/-!
# The easy cases: `quick_defeq` (lane `defeq`)

`quickDefEq`'s dispatch on the two tags (`quick_defeq`) and its four arms, each its own function
(`DefEq.lean`): `quick_sort` (the level comparison, `lvl_eq_c`), `lit_eq` (`DefEqLeaves2.lean`),
`quick_forall` (`defeq_binders`), `quick_lam` (`defeq_lams`). The arms read their pairs through
`e_view`. `quickDefeq_refines` closes `QuickDefeqSpec` (`DefEqMid.lean`, `delta_quick`'s
hypothesis).

**Store hypotheses** (`StoreDenotes`): a stored sort's level and a stored constant's level list
read back (`denoteL`/`denoteLs`); `lvl_eq_c`'s refinement (`CoreLevels.lean`) takes the readbacks
as hypotheses. A property of the store relation, not proved here.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **Stored levels read back.** -/
structure StoreDenotes : Prop where
  sort : ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word), CoreS dn m a vis fe M eb → ∀ (h : EIdx) (u : LIdx),
    a.store.view h = some (.sort u) → ∃ l, denoteL a.store.ls u = some l
  constLs : ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word), CoreS dn m a vis fe M eb → ∀ (h : EIdx) (c : NIdx) (us : LsIdx),
    a.store.view h = some (.const c us) → ∃ ls, denoteLs a.store.lss us = some ls

/-- The lookups of this file. -/
structure QuickProg (p : Prog) : Prop where
  lams : LamsProg p
  lv : LvlCacheProg p
  qd : p.lookup "quick_defeq" = some quickDefeqL
  qs : p.lookup "quick_sort" = some quickSortL
  qf : p.lookup "quick_forall" = some quickForallL
  ql : p.lookup "quick_lam" = some quickLamL
  le : p.lookup "lit_eq" = some litEqL
  lq : p.lookup "limbs_eq" = some limbsEq

/-! ## `e_view` runs -/

theorem eViewW_head (m : Mem) (h : Word) (hne : L.Ind.eViewW m h ≠ []) :
    (L.Ind.eViewW m h).headD 0 = h >>> 28 := by
  unfold L.Ind.eViewW at hne ⊢
  by_cases c1 : (4294967295 : Word) < h
  · simp [c1] at hne
  by_cases c2 : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [c1, c2] at hne
  simp only [c1, c2, ite_false] at hne ⊢
  by_cases g0 : h >>> 28 = 0
  · simp only [g0, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g0, ite_false] at hne ⊢
  by_cases g1 : h >>> 28 = 1
  · simp only [g1, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g1, ite_false] at hne ⊢
  by_cases g2 : h >>> 28 = 2
  · simp only [g2, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g2, ite_false] at hne ⊢
  by_cases g3 : h >>> 28 = 3
  · simp only [g3, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g3, ite_false] at hne ⊢
  by_cases g4 : h >>> 28 = 4
  · simp only [g4, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g4, ite_false] at hne ⊢
  by_cases g5 : h >>> 28 = 5
  · simp only [g5, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g5, ite_false] at hne ⊢
  by_cases g6 : h >>> 28 = 6
  · simp only [g6, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g6, ite_false] at hne ⊢
  by_cases g7 : h >>> 28 = 7
  · simp only [g7, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g7, ite_false] at hne ⊢
  by_cases g8 : h >>> 28 = 8
  · simp only [g8, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g8, ite_false] at hne ⊢
  by_cases g9 : h >>> 28 = 9
  · simp only [g9, ite_true] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hh; simp only [hh, ite_false, List.headD_cons]
  simp only [g9, ite_false] at hne ⊢
  exact absurd rfl hne

theorem getD_one (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> rfl

theorem getD_two (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> rfl

/-- **A run of `e_view`**: the memory kept, the twin's view, the words denoting it, the tag word. -/
theorem eView_callW_view {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} {r : List Word}
    (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ ∃ v, a.store.view (decE h) = some v ∧ L.Ind.ViewR r v ∧ r.headD 0 = h >>> 28 := by
  obtain ⟨s', hm, rfl, hne, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Ind.eView_spec p hp n ⟨m, Locals.init []⟩ h) hc
  obtain ⟨v, hv, hvr⟩ := L.Ind.eViewW_ok m a hR h (hr ▸ hne)
  refine ⟨hm.symm, v, hv, hr ▸ hvr, ?_⟩
  rw [hr]; exact eViewW_head m h (hr ▸ hne)

theorem viewR_sort {r : List Word} {v : ENodeView} (hr : L.Ind.ViewR r v) (h2 : r.headD 0 = 2) :
    v = .sort (decI (r.tail.headD 0)) ∧ HW (r.tail.headD 0) := by
  cases v <;> simp only [L.Ind.ViewR, h2] at hr
  all_goals first
    | (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide)
    | (exfalso; revert hr; decide)
    | (obtain ⟨-, h1, h3⟩ := hr; rw [getD_one] at h1 h3; exact ⟨by rw [h3], h1⟩)

theorem viewR_forall {r : List Word} {v : ENodeView} (hr : L.Ind.ViewR r v) (h6 : r.headD 0 = 6) :
    v = .forallE (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0)) ∧ HW (r.tail.headD 0) ∧
      HW (r.tail.tail.headD 0) := by
  cases v <;> simp only [L.Ind.ViewR, h6] at hr
  all_goals first
    | (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide)
    | (exfalso; revert hr; decide)
    | (obtain ⟨-, h1, h3, h4, h5⟩ := hr; rw [getD_one] at h1 h3; rw [getD_two] at h4 h5
       exact ⟨by rw [h3, h5], h1, h4⟩)

theorem viewR_lam {r : List Word} {v : ENodeView} (hr : L.Ind.ViewR r v) (h5 : r.headD 0 = 5) :
    v = .lam (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0)) ∧ HW (r.tail.headD 0) ∧
      HW (r.tail.tail.headD 0) := by
  cases v <;> simp only [L.Ind.ViewR, h5] at hr
  all_goals first
    | (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide)
    | (exfalso; revert hr; decide)
    | (obtain ⟨-, h1, h3, h4, h6⟩ := hr; rw [getD_one] at h1 h3; rw [getD_two] at h4 h6
       exact ⟨by rw [h3, h6], h1, h4⟩)

/-- The twin's arm match of `quickDefEq` (after the tag tests). -/
def quickPairT (mode : ConLeche.CheckMode) (r : CoreFnsA) (depth : Nat) (a b : EIdx) :
    AM (Option Bool) := do
  match ← view a, ← view b with
  | .sort u, .sort v => do
    let ok ← liftFueled "level comparison" (← lvlEq? u v)
    pure (some ok)
  | .lit l₁, .lit l₂ => pure (some (l₁ == l₂))
  | .forallE ty₁ body₁, .forallE ty₂ body₂ => do
    let ok ← defeqBinders r depth ty₁ body₁ ty₂ body₂
    pure (some ok)
  | .lam ty₁ body₁, .lam ty₂ body₂ => do
    let ok ← defeqLams mode r lamsFuel depth ty₁ body₁ ty₂ body₂
    pure (some ok)
  | _, _ => pure none

theorem quickDefEq_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (depth : Nat) (a b : EIdx) :
    quickDefEq mode r depth a b =
      if a == b then pure (some true)
      else if a.tag != b.tag then pure none
      else if a.tag == ETag.sort || a.tag == ETag.lit || a.tag == ETag.forallE ||
          a.tag == ETag.lam then quickPairT mode r depth a b
      else pure none := rfl

section qp
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (depth : Nat) (a b : EIdx) (s : AState)

theorem quickPairT_sort (u v : LIdx) (ha : s.store.view a = some (.sort u))
    (hb : s.store.view b = some (.sort v)) :
    (quickPairT mode r depth a b).run s = (do
      let o ← lvlEq? u v
      let ok ← liftFueled "level comparison" o
      pure (some ok) : AM (Option Bool)).run s := by
  simp only [quickPairT, StateT.run_bind, view_run _ _ _ ha, view_run _ _ _ hb, except_ok_bind]

theorem quickPairT_lit (l₁ l₂ : ConLeche.Literal) (ha : s.store.view a = some (.lit l₁))
    (hb : s.store.view b = some (.lit l₂)) :
    (quickPairT mode r depth a b).run s = .ok (some (l₁ == l₂), s) := by
  simp only [quickPairT, StateT.run_bind, view_run _ _ _ ha, view_run _ _ _ hb, except_ok_bind]; rfl

theorem quickPairT_forall (t₁ c₁ t₂ c₂ : EIdx) (ha : s.store.view a = some (.forallE t₁ c₁))
    (hb : s.store.view b = some (.forallE t₂ c₂)) :
    (quickPairT mode r depth a b).run s = (do
      let ok ← defeqBinders r depth t₁ c₁ t₂ c₂
      pure (some ok) : AM (Option Bool)).run s := by
  simp only [quickPairT, StateT.run_bind, view_run _ _ _ ha, view_run _ _ _ hb, except_ok_bind]

theorem quickPairT_lam (t₁ c₁ t₂ c₂ : EIdx) (ha : s.store.view a = some (.lam t₁ c₁))
    (hb : s.store.view b = some (.lam t₂ c₂)) :
    (quickPairT mode r depth a b).run s = (do
      let ok ← defeqLams mode r lamsFuel depth t₁ c₁ t₂ c₂
      pure (some ok) : AM (Option Bool)).run s := by
  simp only [quickPairT, StateT.run_bind, view_run _ _ _ ha, view_run _ _ _ hb, except_ok_bind]

end qp

/-- Nothing returns at fuel `0`. -/
theorem invoke_zero_false (p : Prog) (f : FnName) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p 0) f vs ⦃fun _ _ => False; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  have := L.M.of_run (P := fun s => s = s₀) hs hrun (callW_spec p 0 f vs s₀)
  rw [callW_zero] at this
  cases this.2

/-- `lvl_eq_c` does not return at fuel `1` (its first statement is a call). -/
theorem lvlEqC_one (p : Prog) (hp : LvlCacheProg p) (u v : Word) (m m' : Mem) (r : List Word) :
    callW p 1 "lvl_eq_c" [u, v] m ≠ some (r, m') := by
  intro hc
  have h : ⦃fun s => s = (⟨m, Locals.init []⟩ : St)⦄ invoke p (exec p 1) "lvl_eq_c" [u, v]
      ⦃fun _ _ => False; ⊤⦄ := by
    rw [invoke_eq _ hp.c]
    simp only [callFn, lvlEqCL]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, invoke_zero_false p "lq_find",
      invoke_zero_false p "lvl_eq_rec"] <;>
      grind
  obtain ⟨_, _, hf⟩ := triple_of_callW h hc
  exact hf

/-! ## `quick_sort` -/

section qsK
variable (p : Prog) (n : Nat) (b : Word)

def qsK3 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else some (r.headD 0 - 1, m)

def qsK2 (ra : List Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (rb, m) => qsK3 (callW p n "lvl_eq_c" [ra.tail.headD 0, rb.tail.headD 0] m)

def qsK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (ra, m) => qsK2 p n ra (callW p n "e_view" [b] m)

variable (r ra rb : List Word) (m : Mem)
theorem qsK3_ok (h : r.headD 0 ≠ 0) : qsK3 (some (r, m)) = some (r.headD 0 - 1, m) := by
  simp only [qsK3, h, ↓reduceIte]
theorem qsK2_s : qsK2 p n ra (some (rb, m)) =
    qsK3 (callW p n "lvl_eq_c" [ra.tail.headD 0, rb.tail.headD 0] m) := rfl
theorem qsK1_s : qsK1 p n b (some (ra, m)) = qsK2 p n ra (callW p n "e_view" [b] m) := rfl
end qsK

theorem quickSort_spec (p : Prog) (hp : QuickProg p) (n : Nat) (s₀ : St) (a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "quick_sort" [a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ qsK1 p n b (callW p n "e_view" [a] s₀.mem) =
      some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.qs]
  simp only [callFn, quickSortL]
  sym (gen := 80) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "e_view",
      callW_spec p n "lvl_eq_c"] <;>
    finish [qsK1_s, qsK2_s, qsK3_ok, St.setLocs_mem']

theorem decO_ne_zero {w : Word} (h : w ≠ 0) : decO w = some ((w - 1) != 0) := by
  unfold decO
  by_cases h1 : w = 1
  · subst h1; rfl
  · simp only [h, h1, ↓reduceIte, Option.some.injEq]
    have : w - 1 ≠ 0 := fun h' => h1 (by
      have := congrArg (· + 1) h'; simpa using this)
    simp [this]

/-- **`quick_sort` refines `quickDefEq`'s sort arm.** -/
theorem quickSort_refines (p : Prog) (hp : QuickProg p) (hsd : StoreDenotes) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb : Word) (mode : ConLeche.CheckMode) (r : CoreFnsA) (depth : Nat) (a b : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (ha : HW a) (hb : HW b) (h2a : a >>> 28 = 2)
    (h2b : b >>> 28 = 2) :
    CoreSpec p (n + 1) "quick_sort" [a, b] (quickPairT mode r depth (decE a) (decE b))
      (fun r => some (decBool r)) s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s rr s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (quickSort_spec p hp n s₀ a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc1 : callW p n "e_view" [a] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨ra, m₁⟩ := q
  rw [hc1, qsK1_s] at hW
  obtain ⟨rfl, va, hva, hvra, hta⟩ := eView_callW_view (a := a₀) hp.lams.peel.eview hS.arena.1 hc1
  obtain ⟨rfl, hwa⟩ := viewR_sort hvra (hta.trans h2a)
  cases hc2 : callW p n "e_view" [b] s.mem with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨rb, m₂⟩ := q
  rw [hc2, qsK2_s] at hW
  obtain ⟨rfl, vb, hvb, hvrb, htb⟩ := eView_callW_view (a := a₀) hp.lams.peel.eview hS.arena.1 hc2
  obtain ⟨rfl, hwb⟩ := viewR_sort hvrb (htb.trans h2b)
  refine coreRef_congr (quickPairT_sort mode r depth _ _ a₀ _ _ hva hvb) ?_
  obtain ⟨lu, hdu⟩ := hsd.sort dn s.mem a₀ vis fe M eb hS _ _ hva
  obtain ⟨lv, hdv⟩ := hsd.sort dn s.mem a₀ vis fe M eb hS _ _ hvb
  cases hc3 : callW p n "lvl_eq_c" [ra.tail.headD 0, rb.tail.headD 0] s.mem with
  | none => rw [hc3] at hW; cases hW
  | some q =>
  obtain ⟨rz, m₃⟩ := q
  rw [hc3] at hW
  obtain ⟨n₁, rfl⟩ := callW_succ hc3
  cases n₁ with
  | zero => exact absurd hc3 (lvlEqC_one p hp.lv _ _ _ _ _)
  | succ n₂ =>
  have e₃ := CoreSpec.of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
    (lvlEqC_refines p hp.lv n₂ ⟨s.mem, Locals.init []⟩ a₀ dn vis fe M eb hS _ _ hwa hwb lu lv hdu hdv) hc3
  refine coreRef_bind e₃ (fun M₃ hS₃ => ?_)
  by_cases hz : rz.headD 0 = 0
  · simp only [qsK3, hz, ↓reduceIte, reduceCtorEq] at hW
  rw [qsK3_ok (h := hz), Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [decO_ne_zero hz, ← hm]
  have h3 := e₃.2.2.2
  unfold ResH HW at h3
  have hres : HW (rz.headD 0 - 1) := by
    unfold HW
    generalize rz.headD 0 = z at h3 hz ⊢
    have hz' : z.toNat ≠ 0 := fun h' => hz (UInt64.toNat_inj.mp (by simpa using h'))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_one]; omega)),
      UInt64.toNat_one]
    omega
  exact coreRef_ret hS₃ (by simp only [liftFueled, decBool, ← hr]) (by unfold ResH; rw [← hr]; exact hres)

end L.Arena
