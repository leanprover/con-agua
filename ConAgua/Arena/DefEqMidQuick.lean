import ConAgua.Arena.DefEqMidLams
import ConAgua.Arena.CoreDen
import ConAgua.Arena.DefEqLeaves2
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

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

theorem StoreDenotes.of_den (h : CoreDen) : StoreDenotes :=
  ⟨fun dn m a vis fe M eb hS => (h dn m a vis fe M eb hS).sort,
    fun dn m a vis fe M eb hS => (h dn m a vis fe M eb hS).constLs⟩

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

theorem quick_eViewW_head (m : Mem) (h : Word) (hne : L.Ind.eViewW m h ≠ []) :
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
  rw [hr]; exact quick_eViewW_head m h (hr ▸ hne)

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
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (_ha : HW a) (_hb : HW b) (h2a : a >>> 28 = 2)
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
  exact coreRef_ret hS₃ (by simp only [decBool, ← hr]) (by unfold ResH; rw [← hr]; exact hres)

/-! ## `quick_forall`, `quick_lam` -/

section qfK
variable (p : Prog) (n : Nat) (f : FnName) (mode vis d b : Word)

def qfK2 (ra : List Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (rb, m) => call1W p n f [mode, vis, d, ra.tail.headD 0, ra.tail.tail.headD 0,
      rb.tail.headD 0, rb.tail.tail.headD 0] m

def qfK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (ra, m) => qfK2 p n f mode vis d ra (callW p n "e_view" [b] m)

variable (ra rb : List Word) (m : Mem)
theorem qfK2_s : qfK2 p n f mode vis d ra (some (rb, m)) = call1W p n f [mode, vis, d,
    ra.tail.headD 0, ra.tail.tail.headD 0, rb.tail.headD 0, rb.tail.tail.headD 0] m := rfl
theorem qfK1_s : qfK1 p n f mode vis d b (some (ra, m)) =
    qfK2 p n f mode vis d ra (callW p n "e_view" [b] m) := rfl
end qfK

theorem quickForall_spec (p : Prog) (hp : QuickProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "quick_forall" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ qfK1 p n "defeq_binders" mode vis d b (callW p n "e_view" [a] s₀.mem) =
      some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.qf]
  simp only [callFn, quickForallL]
  sym (gen := 80) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "e_view",
      callW_spec p n "defeq_binders"] <;>
    finish [qfK1_s, qfK2_s, call1W_some, St.setLocs_mem']

theorem quickLam_spec (p : Prog) (hp : QuickProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "quick_lam" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ qfK1 p n "defeq_lams" mode vis d b (callW p n "e_view" [a] s₀.mem) =
      some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ql]
  simp only [callFn, quickLamL]
  sym (gen := 80) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "e_view",
      callW_spec p n "defeq_lams"] <;>
    finish [qfK1_s, qfK2_s, call1W_some, St.setLocs_mem']

theorem peelFuel_lt : peelFuel < 2 ^ 62 := by unfold peelFuel; decide

/-- A run that answers `ok`, then `pure (some ok)`. -/
theorem coreRef_some {T : AM Bool} {a₀ : AState} {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
    (h : CoreRef T a₀ decBool dn m₀ vis fe M eb r m) :
    CoreRef (T >>= fun ok => pure (some ok)) a₀ (fun r => some (decBool r)) dn m₀ vis fe M eb r m :=
  coreRef_bind h (fun _M' hS' => coreRef_ret hS' rfl h.2.2.2)

/-- **`quick_forall` refines `quickDefEq`'s `∀` arm** at the knot. -/
theorem quickForall_refines (p : Prog) (hp : QuickProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (_ha : HW a) (_hb : HW b)
    (h6a : a >>> 28 = 6) (h6b : b >>> 28 = 6) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "quick_forall" [mode, vis, d, a, b]
      (quickPairT (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b))
      (fun r => some (decBool r)) s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s rr s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (quickForall_spec p hp n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  cases hc1 : callW p n "e_view" [a] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨ra, m₁⟩ := q
  rw [hc1, qfK1_s] at hW
  obtain ⟨rfl, va, hva, hvra, hta⟩ := eView_callW_view (a := a₀) hp.lams.peel.eview hS.arena.1 hc1
  obtain ⟨rfl, hwa1, hwa2⟩ := viewR_forall hvra (hta.trans h6a)
  cases hc2 : callW p n "e_view" [b] s.mem with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨rb, m₂⟩ := q
  rw [hc2, qfK2_s] at hW
  obtain ⟨rfl, vb, hvb, hvrb, htb⟩ := eView_callW_view (a := a₀) hp.lams.peel.eview hS.arena.1 hc2
  obtain ⟨rfl, hwb1, hwb2⟩ := viewR_forall hvrb (htb.trans h6b)
  refine coreRef_congr (quickPairT_forall _ _ _ _ _ a₀ _ _ _ _ hva hvb) (coreRef_some ?_)
  obtain ⟨k, rfl⟩ := call1W_succ hW
  have hpf := peelFuel_lt
  exact CoreSpec.of_call1W (s₀ := ⟨s.mem, Locals.init []⟩)
    (defeqBinders_refines p hp.lams.peel hil k (hk.mono (by omega)) F (by omega) (by omega) _ a₀ dn
      vis fe M eb mode d _ _ _ _ ⟨hS, hs.mode4, hs.eb_mode⟩ hwa1 hwa2 hwb1 hwb2 (by omega))
    (fun r r' h => by simp only [decBool, h]) hW

/-- **`quick_lam` refines `quickDefEq`'s `λ` arm** at the knot. -/
theorem quickLam_refines (p : Prog) (hp : QuickProg p) (hi : Inst1OK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (_ha : HW a) (_hb : HW b)
    (h5a : a >>> 28 = 5) (h5b : b >>> 28 = 5) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "quick_lam" [mode, vis, d, a, b]
      (quickPairT (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b))
      (fun r => some (decBool r)) s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s rr s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (quickLam_spec p hp n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  cases hc1 : callW p n "e_view" [a] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨ra, m₁⟩ := q
  rw [hc1, qfK1_s] at hW
  obtain ⟨rfl, va, hva, hvra, hta⟩ := eView_callW_view (a := a₀) hp.lams.peel.eview hS.arena.1 hc1
  obtain ⟨rfl, hwa1, hwa2⟩ := viewR_lam hvra (hta.trans h5a)
  cases hc2 : callW p n "e_view" [b] s.mem with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨rb, m₂⟩ := q
  rw [hc2, qfK2_s] at hW
  obtain ⟨rfl, vb, hvb, hvrb, htb⟩ := eView_callW_view (a := a₀) hp.lams.peel.eview hS.arena.1 hc2
  obtain ⟨rfl, hwb1, hwb2⟩ := viewR_lam hvrb (htb.trans h5b)
  refine coreRef_congr (quickPairT_lam _ _ _ _ _ a₀ _ _ _ _ hva hvb) (coreRef_some ?_)
  obtain ⟨k, rfl⟩ := call1W_succ hW
  exact CoreSpec.of_call1W (s₀ := ⟨s.mem, Locals.init []⟩)
    (defeqLams_refines p hp.lams hi k (hk.mono (by omega)) F (by omega) (by omega) _ a₀ dn
      vis fe M eb mode d _ _ _ _ ⟨hS, hs.mode4, hs.eb_mode⟩ hwa1 hwa2 hwb1 hwb2 hd)
    (fun r r' h => by simp only [decBool, h]) hW

/-! ## `quick_defeq`: the dispatch -/

/-- After the arm's run: `(1, r)`. -/
def qdK (res : Option (List Word × Mem)) : Option (Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => some (1, r.headD 0, m)

theorem qdK_s (r : List Word) (m : Mem) : qdK (some (r, m)) = some (1, r.headD 0, m) := rfl

/-- The model of `quick_defeq`. -/
def qdW (p : Prog) (n : Nat) (m : Mem) (mode vis d a b : Word) : Option (Word × Word × Mem) :=
  if a = b then some (1, 1, m)
  else if a >>> 28 ≠ b >>> 28 then some (0, 0, m)
  else if a >>> 28 = 2 then qdK (callW p n "quick_sort" [a, b] m)
  else if a >>> 28 = 8 then qdK (callW p n "lit_eq" [a, b] m)
  else if a >>> 28 = 6 then qdK (callW p n "quick_forall" [mode, vis, d, a, b] m)
  else if a >>> 28 = 5 then qdK (callW p n "quick_lam" [mode, vis, d, a, b] m)
  else some (0, 0, m)

section qdArms
variable (p : Prog) (n : Nat) (m : Mem) (mode vis d a b : Word)
theorem qdW_eq (h : a = b) : qdW p n m mode vis d a b = some (1, 1, m) := by simp [qdW, h]
theorem qdW_ne (h : ¬ a = b) (hg : a >>> 28 ≠ b >>> 28) : qdW p n m mode vis d a b = some (0, 0, m) := by
  simp [qdW, h, hg]
theorem qdW_sort (h : ¬ a = b) (hg : a >>> 28 = b >>> 28) (h2 : a >>> 28 = 2) :
    qdW p n m mode vis d a b = qdK (callW p n "quick_sort" [a, b] m) := by
  unfold qdW; rw [ite_eq_right h, ite_eq_right (fun h' => h' hg), ite_eq_left h2]
theorem qdW_lit (h : ¬ a = b) (hg : a >>> 28 = b >>> 28) (h2 : ¬ a >>> 28 = 2) (h8 : a >>> 28 = 8) :
    qdW p n m mode vis d a b = qdK (callW p n "lit_eq" [a, b] m) := by
  unfold qdW; rw [ite_eq_right h, ite_eq_right (fun h' => h' hg), ite_eq_right h2, ite_eq_left h8]
theorem qdW_fa (h : ¬ a = b) (hg : a >>> 28 = b >>> 28) (h2 : ¬ a >>> 28 = 2) (h8 : ¬ a >>> 28 = 8)
    (h6 : a >>> 28 = 6) :
    qdW p n m mode vis d a b = qdK (callW p n "quick_forall" [mode, vis, d, a, b] m) := by
  unfold qdW; rw [ite_eq_right h, ite_eq_right (fun h' => h' hg), ite_eq_right h2, ite_eq_right h8, ite_eq_left h6]
theorem qdW_lam (h : ¬ a = b) (hg : a >>> 28 = b >>> 28) (h2 : ¬ a >>> 28 = 2) (h8 : ¬ a >>> 28 = 8)
    (h6 : ¬ a >>> 28 = 6) (h5 : a >>> 28 = 5) :
    qdW p n m mode vis d a b = qdK (callW p n "quick_lam" [mode, vis, d, a, b] m) := by
  unfold qdW; rw [ite_eq_right h, ite_eq_right (fun h' => h' hg), ite_eq_right h2, ite_eq_right h8, ite_eq_right h6, ite_eq_left h5]
theorem qdW_none (h : ¬ a = b) (hg : a >>> 28 = b >>> 28) (h2 : ¬ a >>> 28 = 2) (h8 : ¬ a >>> 28 = 8)
    (h6 : ¬ a >>> 28 = 6) (h5 : ¬ a >>> 28 = 5) : qdW p n m mode vis d a b = some (0, 0, m) := by
  unfold qdW; rw [ite_eq_right h, ite_eq_right (fun h' => h' hg), ite_eq_right h2, ite_eq_right h8, ite_eq_right h6, ite_eq_right h5]
end qdArms

theorem quickDefeq_spec (p : Prog) (hp : QuickProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "quick_defeq" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ qdW p n s₀.mem mode vis d a b =
      some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.qd]
  simp only [callFn, quickDefeqL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "quick_sort",
      callW_spec p n "lit_eq", callW_spec p n "quick_forall", callW_spec p n "quick_lam"] <;>
    finish [qdW_eq, qdW_ne, qdW_sort, qdW_lit, qdW_fa, qdW_lam, qdW_none, qdK_s]

theorem coreRef_redec {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec₁ dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r r' : List Word} {ok₁ ok : List Word → Prop}
    (h : CoreRef T a₀ dec₁ dn m₀ vis fe M eb r m ok₁) (hd : dec₁ r = dec r') (hok : ok r') :
    CoreRef T a₀ dec dn m₀ vis fe M eb r' m ok :=
  ⟨h.1, h.2.1, h.2.2.1.trans hd, hok⟩

theorem tag_bne (x y : Word) (hx : HW x) (hy : HW y) :
    ((decE x).tag != (decE y).tag) = decide (x >>> 28 ≠ y >>> 28) := by
  rw [decE_tag x hx, decE_tag y hy]
  have h1 : (x >>> 28).toNat < 2 ^ 32 := by
    rw [UInt64.toNat_shiftRight]; unfold HW at hx; simp; omega
  have h2 : (y >>> 28).toNat < 2 ^ 32 := by
    rw [UInt64.toNat_shiftRight]; unfold HW at hy; simp; omega
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · intro h e; exact h (by rw [e])
  · intro h e; apply h; apply UInt64.toNat_inj.mp
    have := congrArg UInt32.toNat e
    simp only [UInt64.toNat_toUInt32] at this
    omega

/-- `lit_eq`'s model passed its view checks. -/
theorem litEqW_views {m : Mem} {a b w : Word} (h : litEqW m a b = some w) :
    viewOK m a LIT ∧ viewOK m b LIT := by
  unfold litEqW at h
  by_cases as : tierW a ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [as] at h
  by_cases ac : tcnt m LIT (tierW a) ≤ idxW a
  · simp [as, ac] at h
  by_cases bs : tierW b ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [ac, bs] at h
  by_cases bc : tcnt m LIT (tierW b) ≤ idxW b
  · simp [as, ac, bs, bc] at h
  exact ⟨⟨as, by simpa using ac⟩, ⟨bs, by simpa using bc⟩⟩

theorem hw_tail1 {r : List Word} {x : Word} (h : 1 = r.headD 0) (h2 : x = r.tail.headD 0) (hx : HW x) :
    ResW r := ⟨h ▸ hw1, h2 ▸ hx⟩

/-- **`quick_defeq` refines `quickDefEq`** at the knot: closes `QuickDefeqSpec` one level up. -/
@[refines ConRon.Arena.quickDefEq]
theorem quickDefeq_refines (p : Prog) (hp : QuickProg p) (hil : InstListOK p) (hi : Inst1OK p)
    (hsd : StoreDenotes) (n : Nat) (hk : KnotUpTo p n) : QuickDefeqSpec p (n + 1) := by
  intro F s₀ a₀ dn vis fe M eb mode d x y hF hn hs hx hy hd
  apply L.M.triple_of_run
  intro s rr s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (quickDefeq_spec p hp n s₀ mode vis d x y)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  rw [quickDefEq_eq]
  by_cases he : x = y
  · rw [qdW_eq (h := he), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
    obtain ⟨h1, h2, hm⟩ := hW
    have hb : (decE x == decE y) = true := by rw [decE_beq_eq _ _ hx hy]; simp [he]
    simp only [hb, ↓reduceIte, ← hm]
    exact coreRef_ret hS (by simp only [decOB, ← h1, ← h2]; rfl) ⟨h1 ▸ hw1, h2 ▸ hw1⟩
  have hb : (decE x == decE y) = false := by rw [decE_beq_eq _ _ hx hy]; simp [he]
  simp only [hb, Bool.false_eq_true, ↓reduceIte, tag_bne x y hx hy, decide_eq_true_eq]
  by_cases hg : x >>> 28 ≠ y >>> 28
  · rw [qdW_ne (h := he) (hg := hg), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
    obtain ⟨h1, h2, hm⟩ := hW
    rw [ite_eq_left hg, ← hm]
    exact coreRef_ret hS (by simp only [decOB, ← h1, ↓reduceIte]) ⟨h1 ▸ hw0, h2 ▸ hw0⟩
  have hg' : x >>> 28 = y >>> 28 := Classical.byContradiction hg
  rw [ite_eq_right hg]
  simp only [tag_beq_w x hx 2 (by decide) ETag.sort rfl 2 rfl,
    tag_beq_w x hx 8 (by decide) ETag.lit rfl 8 rfl, tag_beq_w x hx 6 (by decide) ETag.forallE rfl 6 rfl,
    tag_beq_w x hx 5 (by decide) ETag.lam rfl 5 rfl, Bool.or_eq_true, decide_eq_true_eq]
  -- the arms: the callee's run, re-decoded
  have arm : ∀ (f : FnName) (args : List Word) (T : AM (Option Bool)),
      qdK (callW p n f args s.mem) = some (rr.headD 0, rr.tail.headD 0, s'.mem) →
      (∀ k r m₁, n = k + 1 → callW p (k + 1) f args s.mem = some (r, m₁) →
        CoreRef T a₀ (fun r => some (decBool r)) dn s.mem vis fe M eb r m₁) →
      CoreRef T a₀ decOB dn s.mem vis fe M eb rr s'.mem ResW := by
    intro f args T hq hT
    cases hc : callW p n f args s.mem with
    | none => rw [hc] at hq; cases hq
    | some q =>
    obtain ⟨r, m₁⟩ := q
    rw [hc, qdK_s, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hq
    obtain ⟨h1, h2, hm⟩ := hq
    obtain ⟨k, rfl⟩ := callW_succ hc
    have e := hT k r m₁ rfl hc
    rw [← hm]
    exact coreRef_redec e (by simp only [decOB, ← h1, ← h2, decBool]; rfl)
      (hw_tail1 h1 h2 e.2.2.2)
  by_cases h2 : x >>> 28 = 2
  · rw [qdW_sort (h := he) (hg := hg') (h2 := h2)] at hW
    simp only [h2, true_or, ↓reduceIte]
    exact arm _ _ _ hW (fun k r m₁ _ hc => CoreSpec.of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
      (quickSort_refines p hp hsd k _ a₀ dn vis fe M eb _ _ _ x y hS hx hy h2 (hg' ▸ h2)) hc)
  by_cases h8 : x >>> 28 = 8
  · rw [qdW_lit (h := he) (hg := hg') (h2 := h2) (h8 := h8)] at hW
    simp only [h8, true_or, or_true, ↓reduceIte]
    cases hc : callW p n "lit_eq" [x, y] s.mem with
    | none => rw [hc] at hW; cases hW
    | some q =>
    obtain ⟨r, m₁⟩ := q
    rw [hc, qdK_s, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
    obtain ⟨h1, h2', hm⟩ := hW
    obtain ⟨k, rfl⟩ := callW_succ hc
    obtain ⟨t, ht, htm, -, hlw⟩ := triple_of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
      (litEq_spec p hp.le hp.lq k ⟨s.mem, Locals.init []⟩ x y) hc
    obtain ⟨vx, vy⟩ := litEqW_views hlw
    obtain ⟨l₁, hl₁⟩ := view_lit s.mem a₀ hS.arena.1 x hx vx h8
    obtain ⟨l₂, hl₂⟩ := view_lit s.mem a₀ hS.arena.1 y hy vy (hg' ▸ h8)
    obtain ⟨t', ht', -, -, hdec, hrh⟩ := triple_of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
      (litEq_refines p hp.le hp.lq k ⟨s.mem, Locals.init []⟩ a₀ hS.arena.1 x y hx hy h8 (hg' ▸ h8)
        l₁ l₂ hl₁ hl₂) hc
    have hm₁ : m₁ = s.mem := by rw [← ht, htm]
    rw [← hm, hm₁]
    exact coreRef_pure' hS (quickPairT_lit _ _ _ _ _ a₀ _ _ hl₁ hl₂)
      (by rw [decOB, ← h1, ← h2', ite_eq_right (by decide), ← hdec]; rfl)
      (hw_tail1 h1 h2' hrh)
  by_cases h6 : x >>> 28 = 6
  · rw [qdW_fa (h := he) (hg := hg') (h2 := h2) (h8 := h8) (h6 := h6)] at hW
    simp only [h6, true_or, or_true, ↓reduceIte]
    exact arm _ _ _ hW (fun k r m₁ hnk hc => CoreSpec.of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
      (quickForall_refines p hp hil k (hk.mono (by omega)) F (by omega) (by omega) _ a₀ dn vis fe M
        eb mode d x y ⟨hS, hs.mode4, hs.eb_mode⟩ hx hy h6 (hg' ▸ h6) hd) hc)
  by_cases h5 : x >>> 28 = 5
  · rw [qdW_lam (h := he) (hg := hg') (h2 := h2) (h8 := h8) (h6 := h6) (h5 := h5)] at hW
    simp only [h5, or_true, ↓reduceIte]
    exact arm _ _ _ hW (fun k r m₁ hnk hc => CoreSpec.of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
      (quickLam_refines p hp hi k (hk.mono (by omega)) F (by omega) (by omega) _ a₀ dn vis fe M
        eb mode d x y ⟨hS, hs.mode4, hs.eb_mode⟩ hx hy h5 (hg' ▸ h5) hd) hc)
  rw [qdW_none (h := he) (hg := hg') (h2 := h2) (h8 := h8) (h6 := h6) (h5 := h5),
    Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
  obtain ⟨h1, h2', hm⟩ := hW
  simp only [h2, h8, h6, h5, or_self, ↓reduceIte, ← hm]
  exact coreRef_ret hS (by simp only [decOB, ← h1, ↓reduceIte]) ⟨h1 ▸ hw0, h2' ▸ hw0⟩

end L.Arena
