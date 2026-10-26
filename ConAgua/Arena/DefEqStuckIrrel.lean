import ConAgua.Arena.DefEqStuckUnit

/-!
# `stuck_irrel` refines `stuckIrrel` (lane `defeq`, helper `defeq-top`)

Structural η both ways, unit-likeness, then proof irrelevance.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

theorem setCert_at (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d a b : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      HW a → HW b →
      CoreSpec p n "struct_eta_cert" [mode, vis, d, a, b]
        (structEtaCert (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
        s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, b, hF, hn, hs, h1, h2 =>
      setCert_refines p hq hi hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b
        (by omega) (by omega) hs h1 h2

theorem suCert_at (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d a b : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      HW a → HW b →
      CoreSpec p n "struct_unit_cert" [mode, vis, d, a, b]
        (structUnitCert (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
        s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, b, hF, hn, hs, h1, h2 =>
      suCert_refines p hq hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b
        (by omega) (by omega) hs h1 h2

section siK
variable (p : Prog) (n : Nat) (mode vis d a b : Word)

def siK3 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then some (1, m) else call1W p n "proof_irrel" [mode, vis, d, a, b] m

def siK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then some (1, m)
    else siK3 p n mode vis d a b (callW p n "struct_unit_cert" [mode, vis, d, a, b] m)

/-- **The model of `stuck_irrel`** past the first `struct_eta_cert`'s run. -/
def siK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then some (1, m)
    else siK2 p n mode vis d a b (callW p n "struct_eta_cert" [mode, vis, d, b, a] m)

variable (r : List Word) (m : Mem)
theorem siK3_yes (h : r.headD 0 ≠ 0) : siK3 p n mode vis d a b (some (r, m)) = some (1, m) := by
  simp only [siK3, h, ne_eq, not_false_eq_true, ↓reduceIte]
theorem siK3_no (h : r.headD 0 = 0) : siK3 p n mode vis d a b (some (r, m)) =
    call1W p n "proof_irrel" [mode, vis, d, a, b] m := by
  simp only [siK3, h, ne_eq, not_true_eq_false, ↓reduceIte]
theorem siK2_yes (h : r.headD 0 ≠ 0) : siK2 p n mode vis d a b (some (r, m)) = some (1, m) := by
  simp only [siK2, h, ne_eq, not_false_eq_true, ↓reduceIte]
theorem siK2_no (h : r.headD 0 = 0) : siK2 p n mode vis d a b (some (r, m)) =
    siK3 p n mode vis d a b (callW p n "struct_unit_cert" [mode, vis, d, a, b] m) := by
  simp only [siK2, h, ne_eq, not_true_eq_false, ↓reduceIte]
theorem siK1_yes (h : r.headD 0 ≠ 0) : siK1 p n mode vis d a b (some (r, m)) = some (1, m) := by
  simp only [siK1, h, ne_eq, not_false_eq_true, ↓reduceIte]
theorem siK1_no (h : r.headD 0 = 0) : siK1 p n mode vis d a b (some (r, m)) =
    siK2 p n mode vis d a b (callW p n "struct_eta_cert" [mode, vis, d, b, a] m) := by
  simp only [siK1, h, ne_eq, not_true_eq_false, ↓reduceIte]

end siK

theorem stuckIrrel_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "stuck_irrel" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ siK1 p n mode vis d a b
      (callW p n "struct_eta_cert" [mode, vis, d, a, b] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.stuckIrrel]
  simp only [callFn, stuckIrrelL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "struct_eta_cert",
      callW_spec p n "struct_unit_cert", callW_spec p n "proof_irrel"] <;>
  simp_all [siK1, siK2, siK3, call1W, LocEq, St.setLocs_cons, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

/-- One `if ← c then pure true else k` step: a `true` verdict answers `1`. -/
theorem coreRef_true {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word} {m' : Mem}
    (hS : CoreS dn m a vis fe M eb) (hW : some ((1 : Word), m) = some (r.headD 0, m')) :
    CoreRef (pure true : AM Bool) a decBool dn m vis fe M eb r m' := by
  obtain ⟨hr, hm⟩ := some_pair_inj hW
  rw [← hm]
  exact coreRef_pure hS rfl (decBool_true_of (by rw [← hr]; decide)).symm
    (by unfold ResH; rw [← hr]; exact hw1)

/-- **`stuck_irrel` refines `stuckIrrel`** at the knot. -/
@[refines ConRon.Arena.stuckIrrel]
theorem stuckIrrel_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "stuck_irrel" [mode, vis, d, a, b]
      (stuckIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (stuckIrrel_spec p hq n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  unfold stuckIrrel
  obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
  have h₁ := CoreSpec.of_callW (setCert_at p hq hi hc n hk F s a₀ dn vis fe M eb mode d a b hF hn hs
    ha hb) hc1
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  by_cases h1 : r₁.headD 0 ≠ 0
  · rw [siK1_yes (h := h1)] at hW1
    rw [decBool_true_of h1]; exact coreRef_true hS₁ hW1
  rw [siK1_no (h := by simpa using h1)] at hW1
  rw [decBool_false_of (by simpa using h1)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  obtain ⟨r₂, m₂, hc2, hW2⟩ := callW_cases rfl hW1
  have h₂ := CoreSpec.of_callW (setCert_at p hq hi hc n hk F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
    mode d b a hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb ha) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  by_cases h2 : r₂.headD 0 ≠ 0
  · rw [siK2_yes (h := h2)] at hW2
    rw [decBool_true_of h2]; exact coreRef_true hS₂ hW2
  rw [siK2_no (h := by simpa using h2)] at hW2
  rw [decBool_false_of (by simpa using h2)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  obtain ⟨r₃, m₃, hc3, hW3⟩ := callW_cases rfl hW2
  have h₃ := CoreSpec.of_callW (suCert_at p hq hc n hk F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb
    mode d a b hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb) hc3
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  by_cases h3 : r₃.headD 0 ≠ 0
  · rw [siK3_yes (h := h3)] at hW3
    rw [decBool_true_of h3]; exact coreRef_true hS₃ hW3
  rw [siK3_no (h := by simpa using h3)] at hW3
  rw [decBool_false_of (by simpa using h3)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact CoreSpec.of_call1W (s₀ := ⟨m₃, Locals.init []⟩)
    (proofIrrel_at p hc n hk F hF hn _ _ dn vis fe M₃ eb mode d a b hS₃ hs.mode4 hs.eb_mode ha hb)
    (fun r r' h => by simp only [decBool, h]) hW3

end L.Arena
