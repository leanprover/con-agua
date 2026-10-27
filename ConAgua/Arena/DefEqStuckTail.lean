import ConAgua.Arena.DefEqStuckProj
import ConAgua.Arena.DefEqStuckDisp

/-!
# `defeq_tail` refines `defeqBody`'s tail (lane `defeq`, helper `defeq-top`)

`defeqBody` from the lazy-delta loop's `.unknown` pair on (`defeqTailT`): the projection pair,
the stuck comparison when neither head is a projection, else the full `whnfCore` of both sides
and a restart unless neither moved.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **`defeqBody` past the lazy-delta loop's `.unknown a₁ b₁`**, copied. -/
def defeqTailT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a₁ b₁ : EIdx) :
    AM Bool := do
  if ← defeqProjPair mode r fe depth a₁ b₁ then pure true else do
  let pa ← headIsProj a₁
  let pb ← headIsProj b₁
  if !pa && !pb then defeqStuck mode r fe depth a₁ b₁ else do
  let a₂ ← r.whnfCore false depth a₁
  let b₂ ← r.whnfCore false depth b₁
  if a₂ == a₁ && b₂ == b₁ then defeqStuck mode r fe depth a₁ b₁
  else r.defeq depth a₂ b₂

/-! ## Leaves at any fuel -/

theorem projPair_at (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d a b : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      HW a → HW b → d.toNat < 2 ^ 63 →
      CoreSpec p n "defeq_proj_pair" [mode, vis, d, a, b]
        (defeqProjPair (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
        decBool s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, b, hF, hn, hs, h1, h2, hd =>
      projPair_refines p hq hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b
        (by omega) (by omega) hs h1 h2 hd

theorem defeqStuck_at (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d a b : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      HW a → HW b →
      CoreSpec p n "defeq_stuck" [mode, vis, d, a, b]
        (defeqStuck (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
        decBool s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, b, hF, hn, hs, h1, h2 =>
      defeqStuck_refines p hq hi hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b
        (by omega) (by omega) hs h1 h2

theorem headIsProj_at (p : Prog) (hq : StuckProg p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
      (fe : IFEnv) (MM : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
      CoreSpec p n "head_is_proj" [e] (headIsProj (decE e)) decBool s₀ a₀ dn vis fe MM eb
  | 0, s₀, a₀, dn, vis, fe, MM, eb, _, _, _ => CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe MM eb _
  | n + 1, s₀, a₀, dn, vis, fe, MM, eb, e, hS, he =>
      headIsProj_refines p hq.leaf n s₀ a₀ dn vis fe MM eb e hS he

theorem decE_beq {x y : Word} (hx : HW x) (hy : HW y) : (decE x == decE y) = decide (x = y) := by
  rw [decE_eq, decE_eq, decI_beq x y hx hy]

/-! ## The model -/

section dtK
variable (p : Prog) (n : Nat) (mode vis d a1 b1 : Word)

def dtK5 (a2 : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if a2 = a1 ∧ r.headD 0 = b1 then call1W p n "defeq_stuck" [mode, vis, d, a1, b1] m
    else call1W p n "defeq" [mode, vis, d, a2, r.headD 0] m

def dtK4 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => dtK5 p n mode vis d a1 b1 (r.headD 0) (callW p n "whnf_core" [mode, 0, vis, d, b1] m)

def dtK3 (pa : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if pa = 0 ∧ r.headD 0 = 0 then call1W p n "defeq_stuck" [mode, vis, d, a1, b1] m
    else dtK4 p n mode vis d a1 b1 (callW p n "whnf_core" [mode, 0, vis, d, a1] m)

def dtK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => dtK3 p n mode vis d a1 b1 (r.headD 0) (callW p n "head_is_proj" [b1] m)

/-- **The model of `defeq_tail`** past `defeq_proj_pair`'s run. -/
def dtK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then some (1, m)
    else dtK2 p n mode vis d a1 b1 (callW p n "head_is_proj" [a1] m)

variable (r : List Word) (m : Mem) (pa a2 : Word)
theorem dtK2_some : dtK2 p n mode vis d a1 b1 (some (r, m)) =
    dtK3 p n mode vis d a1 b1 (r.headD 0) (callW p n "head_is_proj" [b1] m) := rfl
theorem dtK4_some : dtK4 p n mode vis d a1 b1 (some (r, m)) =
    dtK5 p n mode vis d a1 b1 (r.headD 0) (callW p n "whnf_core" [mode, 0, vis, d, b1] m) := rfl

end dtK

theorem defeqTail_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (mode vis d a1 b1 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_tail" [mode, vis, d, a1, b1]
    ⦃fun r s' => LocEq s' s₀ ∧ dtK1 p n mode vis d a1 b1
      (callW p n "defeq_proj_pair" [mode, vis, d, a1, b1] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.defeqTail]
  simp only [callFn, defeqTailL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "defeq_proj_pair",
      callW_spec p n "head_is_proj", callW_spec p n "defeq_stuck", callW_spec p n "whnf_core",
      callW_spec p n "defeq"] <;>
  simp_all [dtK1, dtK2, dtK3, dtK4, dtK5, call1W, LocEq, St.setLocs_cons, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

/-- **`defeq_tail` refines `defeqTailT`** (`defeqBody` past the lazy-delta loop) at the knot. -/
@[refines_part ConRon.Arena.defeqBody "past the lazy-delta loop (defeqTailT)"]
theorem defeqTail_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a1 b1 : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a1) (hb : HW b1) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "defeq_tail" [mode, vis, d, a1, b1]
      (defeqTailT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a1) (decE b1))
      decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqTail_spec p hq n s₀ mode vis d a1 b1)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hK := hk n (Nat.le_refl _)
  have hstk : ∀ (st : AState) (m : Mem) (M' : ModeMaps), CoreS dn m st vis fe M' eb →
      call1W p n "defeq_stuck" [mode, vis, d, a1, b1] m = some (r.headD 0, s'.mem) →
      CoreRef (defeqStuck (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a1)
        (decE b1)) st decBool dn m vis fe M' eb r s'.mem := fun st m M' hS' hc' =>
    CoreSpec.of_call1W (s₀ := ⟨m, Locals.init []⟩)
      (defeqStuck_at p hq hi hc n hk F _ st dn vis fe M' eb mode d a1 b1 hF hn
        ⟨hS', hs.mode4, hs.eb_mode⟩ ha hb) (fun r r' h => by simp only [decBool, h]) hc'
  unfold defeqTailT
  obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
  have h₁ := CoreSpec.of_callW (projPair_at p hq hc n hk F s a₀ dn vis fe M eb mode d a1 b1 hF hn hs
    ha hb hd) hc1
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  simp only [dtK1] at hW1
  by_cases h0 : r₁.headD 0 ≠ 0
  · simp only [h0, ne_eq, not_false_eq_true, ↓reduceIte] at hW1
    rw [decBool_true_of h0]; exact coreRef_true hS₁ hW1
  simp only [h0, ↓reduceIte] at hW1
  rw [decBool_false_of (by simpa using h0)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  obtain ⟨r₂, m₂, hc2, hW2⟩ := callW_cases rfl hW1
  have h₂ := CoreSpec.of_callW (headIsProj_at p hq n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb a1 hS₁ ha) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  rw [dtK2_some] at hW2
  obtain ⟨r₃, m₃, hc3, hW3⟩ := callW_cases rfl hW2
  have h₃ := CoreSpec.of_callW (headIsProj_at p hq n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb b1 hS₂ hb) hc3
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  simp only [dtK3] at hW3
  have hpp : (!decBool r₂ && !decBool r₃) = decide (r₂.headD 0 = 0 ∧ r₃.headD 0 = 0) := by
    unfold decBool
    generalize r₂.headD 0 = u
    generalize r₃.headD 0 = v
    by_cases x : u = 0 <;> by_cases y : v = 0 <;> simp [x, y]
  rw [hpp]
  by_cases hp0 : r₂.headD 0 = 0 ∧ r₃.headD 0 = 0
  · rw [ite_eq_left hp0] at hW3
    simp only [hp0, and_self, decide_true, ↓reduceIte]
    exact hstk _ m₃ M₃ hS₃ hW3
  rw [ite_eq_right hp0] at hW3
  simp only [hp0, decide_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨r₄, m₄, hc4, hW4⟩ := callW_cases rfl hW3
  have h₄ := CoreSpec.of_callW (hK.whnfCore F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode 0 d a1 hF hn
    ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha) hc4
  refine coreRef_bind h₄ (fun M₄ hS₄ => ?_)
  rw [dtK4_some] at hW4
  obtain ⟨r₅, m₅, hc5, hW5⟩ := callW_cases rfl hW4
  have h₅ := CoreSpec.of_callW (hK.whnfCore F ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode 0 d b1 hF hn
    ⟨hS₄, hs.mode4, hs.eb_mode⟩ hb) hc5
  refine coreRef_bind h₅ (fun M₅ hS₅ => ?_)
  simp only [dtK5] at hW5
  have heq : (decH r₄ == decE a1 && decH r₅ == decE b1) =
      decide (r₄.headD 0 = a1 ∧ r₅.headD 0 = b1) := by
    simp only [decH, decE_beq h₄.2.2.2 ha, decE_beq h₅.2.2.2 hb, Bool.decide_and]
  rw [heq]
  by_cases hm : r₄.headD 0 = a1 ∧ r₅.headD 0 = b1
  · rw [ite_eq_left hm] at hW5
    simp only [hm, and_self, decide_true, ↓reduceIte]
    exact hstk _ m₅ M₅ hS₅ hW5
  rw [ite_eq_right hm] at hW5
  simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte]
  exact CoreSpec.of_call1W (s₀ := ⟨m₅, Locals.init []⟩)
    (hK.defeq F _ _ dn vis fe M₅ eb mode d (r₄.headD 0) (r₅.headD 0) hF hn ⟨hS₅, hs.mode4, hs.eb_mode⟩
      h₄.2.2.2 h₅.2.2.2) (fun r r' h => by simp only [decBool, h]) hW5

end L.Arena
