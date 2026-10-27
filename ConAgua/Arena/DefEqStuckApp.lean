import ConAgua.Arena.DefEqStuckStr
import ConAgua.Census.Attr

/-!
# `stuck_app_cong`, `stuck_app` refine `defeqStuck`'s application arm (lane `defeq`, helper `defeq-top`)

The arm is the congruence `appCongT` (both spines, the heads, then the arguments pairwise),
then `stuckIrrel` on a failure (`stuckAppT_eq`, by the monad laws).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin -/

/-- **`defeqStuck`'s application arm**, copied. -/
def stuckAppT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) : AM Bool := do
  let aa ← getAppArgs coreWalkFuel a
  let bb ← getAppArgs coreWalkFuel b
  if aa.length = bb.length then do
    let fa ← getAppFn coreWalkFuel a
    let fb ← getAppFn coreWalkFuel b
    if ← r.defeq depth fa fb then do
      if ← defEqList r fe depth aa bb then pure true
      else stuckIrrel r fe depth a b
    else stuckIrrel r fe depth a b
  else stuckIrrel r fe depth a b

/-- The arm's congruence (`stuck_app_cong`). -/
def appCongT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) : AM Bool := do
  let aa ← getAppArgs coreWalkFuel a
  let bb ← getAppArgs coreWalkFuel b
  if aa.length = bb.length then do
    let fa ← getAppFn coreWalkFuel a
    let fb ← getAppFn coreWalkFuel b
    if ← r.defeq depth fa fb then defEqList r fe depth aa bb else pure false
  else pure false

theorem stuckAppT_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    stuckAppT r fe depth a b =
      (appCongT r fe depth a b >>= fun ok => if ok then pure true else stuckIrrel r fe depth a b) := by
  simp only [stuckAppT, appCongT, bind_assoc]
  congr 1; funext aa; congr 1; funext bb
  by_cases h : aa.length = bb.length
  · simp only [h, ↓reduceIte, bind_assoc]
    congr 1; funext fa; congr 1; funext fb; congr 1; funext x
    cases x <;> simp
  · simp [h]

/-! ## The model of `stuck_app_cong` -/

section apK
variable (p : Prog) (n : Nat) (mode vis d a b : Word)

def apK4 (ao an bo bn : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then call1W p n "defeq_lst" [mode, vis, d, ao, an, bo, bn] m
    else some (r.headD 0, m)

def apK3 (ao an bo bn fa : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => apK4 p n mode vis d ao an bo bn (callW p n "defeq" [mode, vis, d, fa, r.headD 0] m)

def apK2' (ao an bo bn : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => apK3 p n mode vis d ao an bo bn (r.headD 0) (callW p n "get_app_fn" [b] m)

def apK2 (ao an : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if an = r.tail.headD 0 then
      apK2' p n mode vis d b ao an (r.headD 0) (r.tail.headD 0) (callW p n "get_app_fn" [a] m)
    else some (0, m)

/-- The model of `stuck_app_cong` before the top is put back. -/
def apK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => apK2 p n mode vis d a b (r.headD 0) (r.tail.headD 0) (callW p n "get_app_args" [b] m)

/-- **The model of `stuck_app_cong`.** -/
def apK (m : Mem) : Option (Word × Mem) :=
  (apK1 p n mode vis d a b (callW p n "get_app_args" [a] m)).bind
    (fun x => swRet (rdW (m.arr64 CTL) 136) x.1 x.2)

variable (r : List Word) (m : Mem) (ao an bo bn fa : Word)
theorem apK1_some : apK1 p n mode vis d a b (some (r, m)) =
    apK2 p n mode vis d a b (r.headD 0) (r.tail.headD 0) (callW p n "get_app_args" [b] m) := rfl
theorem apK2'_some : apK2' p n mode vis d b ao an bo bn (some (r, m)) =
    apK3 p n mode vis d ao an bo bn (r.headD 0) (callW p n "get_app_fn" [b] m) := rfl
theorem apK3_some : apK3 p n mode vis d ao an bo bn fa (some (r, m)) =
    apK4 p n mode vis d ao an bo bn (callW p n "defeq" [mode, vis, d, fa, r.headD 0] m) := rfl

end apK

theorem appCong_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "stuck_app_cong" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ apK p n mode vis d a b s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.stuckAppCong]
  simp only [callFn, stuckAppCongL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64_spec,
      callW_spec p n "get_app_args", callW_spec p n "get_app_fn", callW_spec p n "defeq",
      callW_spec p n "defeq_lst"] <;>
  simp_all [apK, apK1, apK2, apK2', apK3, apK4, swRet, call1W, LocEq, St.setLocs_cons,
    CTL, Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-! ## The refinements -/

section congRuns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) (st : AState) (aa bb : List EIdx)
  (h1 : (getAppArgs coreWalkFuel a).run st = .ok (aa, st))
  (h2 : (getAppArgs coreWalkFuel b).run st = .ok (bb, st))
include h1 h2

theorem appCongT_ne (h : ¬ aa.length = bb.length) :
    (appCongT r fe depth a b).run st = .ok (false, st) := by
  simp only [appCongT, StateT.run_bind, h1, h2, except_ok_bind, h, ↓reduceIte]
  rfl

theorem appCongT_eq (h : aa.length = bb.length) (fa fb : EIdx)
    (h3 : (getAppFn coreWalkFuel a).run st = .ok (fa, st))
    (h4 : (getAppFn coreWalkFuel b).run st = .ok (fb, st)) :
    (appCongT r fe depth a b).run st =
      (r.defeq depth fa fb >>= fun x => if x then defEqList r fe depth aa bb else pure false).run st := by
  simp only [appCongT, StateT.run_bind, h1, h2, except_ok_bind, h, ↓reduceIte, h3, h4]

end congRuns

/-- **`stuck_app_cong` refines `appCongT`** at the knot (the top put back). -/
@[refines_part ConRon.Arena.defeqStuck "the application arm's congruence (appCongT)"]
theorem appCong_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "stuck_app_cong" [mode, vis, d, a, b]
      (appCongT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (appCong_spec p hq n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  have hspn := hS.spn
  simp only [apK] at hW
  cases hpre : apK1 p n mode vis d a b (callW p n "get_app_args" [a] s.mem) with
  | none => rw [hpre] at hW; cases hW
  | some x =>
  obtain ⟨v, mk⟩ := x
  rw [hpre] at hW
  simp only [Option.bind_some, swRet] at hW
  have h136 : (136 : Word).toNat < (mk.arr64 CTL).size := by
    by_cases hh' : (136 : Word).toNat < (mk.arr64 CTL).size
    · exact hh'
    · simp only [hh', ↓reduceIte] at hW; cases hW
  simp only [h136, ↓reduceIte] at hW
  obtain ⟨hv, hm⟩ := some_pair_inj hW
  rw [← hm]
  suffices hG : GrowRef (appCongT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      decBool dn s.mem vis fe M eb r mk from hG.restore h136
  -- the two spines
  obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hpre
  obtain ⟨hf1, hg1, hr10, htop1, aa, hargs1, hsp1⟩ := getAppArgs_callW hq.leaf.core.spine hS ha hc1
  have hS₁ := hS.frame_stk hf1 (by simp) (by simp)
  rw [apK1_some] at hW1
  obtain ⟨r₂, m₂, hc2, hW2⟩ := callW_cases rfl hW1
  obtain ⟨hf2, hg2, hr20, htop2, bb, hargs2, hsp2⟩ := getAppArgs_callW hq.leaf.core.spine hS₁ hb hc2
  have hS₂ := hS₁.frame_stk hf2 (by simp) (by simp)
  have hla : aa.length = (r₁.tail.headD 0).toNat := by simpa using hsp1.size
  have hlb : bb.length = (r₂.tail.headD 0).toNat := by simpa using hsp2.size
  have hspn₁ : (m₁.arr64 SPN).size < 2 ^ 63 := hg1.size ▸ hspn
  have hspn₂ : (m₂.arr64 SPN).size < 2 ^ 63 := hg2.size ▸ hspn₁
  refine growRef_preG (hg1.trans hg2) ?_
  simp only [apK2] at hW2
  rcases (Classical.em (r₁.tail.headD 0 = r₂.tail.headD 0)).symm with heq | heq
  · simp only [heq, ↓reduceIte] at hW2
    obtain ⟨hv0, rfl⟩ := some_pair_inj hW2
    have hne : ¬ aa.length = bb.length := by
      rw [hla, hlb]; exact fun e => heq (UInt64.toNat_inj.mp e)
    exact growRef_pure hS₂ (appCongT_ne _ fe _ _ _ a₀ aa bb hargs1 hargs2 hne)
      (decBool_false_of (by rw [← hv, ← hv0])).symm (by unfold ResH; rw [← hv, ← hv0]; exact hw0)
  simp only [heq, ↓reduceIte] at hW2
  have heq' : aa.length = bb.length := by rw [hla, hlb, heq]
  obtain ⟨r₃, m₃, hc3, hW3⟩ := callW_cases rfl hW2
  obtain ⟨rfl, hh3, hgaf3⟩ := getAppFn_callW hq.leaf hS₂.arena.1 ha hc3
  rw [apK2'_some] at hW3
  obtain ⟨r₄, m₄, hc4, hW4⟩ := callW_cases rfl hW3
  obtain ⟨rfl, hh4, hgaf4⟩ := getAppFn_callW hq.leaf hS₂.arena.1 hb hc4
  rw [apK3_some] at hW4
  obtain ⟨r₅, m₅, hc5, hW5⟩ := callW_cases rfl hW4
  refine growRef_congrS (appCongT_eq _ fe _ _ _ a₀ aa bb hargs1 hargs2 heq' _ _ hgaf3 hgaf4) ?_
  have h₅ := CoreSpec.of_callW (hK.defeq F ⟨m₄, Locals.init []⟩ a₀ dn vis fe M eb mode d (r₃.headD 0)
    (r₄.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ hh3 hh4) hc5
  obtain ⟨_, _, _, hst₅⟩ := h₅.2.1
  refine growRef_bindS (GrowRef.of_core h₅) (fun M₅ hS₅ => ?_)
  simp only [apK4] at hW5
  by_cases h0 : r₅.headD 0 = 0
  · simp only [h0, ne_eq, not_true_eq_false, ↓reduceIte] at hW5
    obtain ⟨hv0, rfl⟩ := some_pair_inj hW5
    rw [decBool_false_of h0]
    exact growRef_pure hS₅ rfl (decBool_false_of (by rw [← hv, ← hv0])).symm
      (by unfold ResH; rw [← hv, ← hv0]; exact hw0)
  simp only [h0, ne_eq, not_false_eq_true, ↓reduceIte] at hW5
  rw [decBool_true_of h0]
  simp only [↓reduceIte]
  rw [hv] at hW5
  -- the spines below the top
  have hb1 := hsp1.bound
  have hb2 := hsp2.bound
  have e1 : (spTop m₁).toNat = (r₁.headD 0).toNat + (r₁.tail.headD 0).toNat := by
    rw [htop1, ← hr10, addW_toNat (by omega)]
  have e2 : (spTop m₄).toNat = (r₂.headD 0).toNat + (r₂.tail.headD 0).toNat := by
    rw [htop2, ← hr20, addW_toNat (by have := hg1.size; omega)]
  have hle12 : (spTop m₁).toNat ≤ (spTop m₄).toNat := UInt64.le_iff_toNat_le.mp hg2.1
  have h5top : spTop m₅ = spTop m₄ := hst₅.1
  have hA : SpineR m₅ (r₁.headD 0) (r₁.tail.headD 0) aa.toArray :=
    (hsp1.grew hg2 (by omega) hspn₁).keep hst₅.size hst₅.below (by omega) hspn₂
  have hB : SpineR m₅ (r₂.headD 0) (r₂.tail.headD 0) bb.toArray :=
    hsp2.keep hst₅.size hst₅.below (by omega) hspn₂
  have h₆ := CoreSpec.of_call1W (s₀ := ⟨m₅, Locals.init []⟩)
    (defeqLst_at p hc n hk F hF hn ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode d (r₁.headD 0)
      (r₂.tail.headD 0) (r₂.headD 0) (r₂.tail.headD 0) aa.toArray bb.toArray
      ⟨hS₅, hs.mode4, hs.eb_mode⟩ (heq ▸ hA) hB (by rw [h5top, ← heq]; omega) (by rw [h5top]; omega))
    (fun r r' h => by simp only [decBool, h]) hW5
  simp only at h₆
  exact GrowRef.of_core h₆

theorem appCong_at (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d a b : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      HW a → HW b →
      CoreSpec p n "stuck_app_cong" [mode, vis, d, a, b]
        (appCongT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
        s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, b, hF, hn, hs, h1, h2 =>
      appCong_refines p hq hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b
        (by omega) (by omega) hs h1 h2

section sapK
variable (p : Prog) (n : Nat) (mode vis d a b : Word)

/-- **The model of `stuck_app`** past the congruence's run. -/
def sapK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then some (1, m) else call1W p n "stuck_irrel" [mode, vis, d, a, b] m

end sapK

theorem stuckApp_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "stuck_app" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ sapK1 p n mode vis d a b
      (callW p n "stuck_app_cong" [mode, vis, d, a, b] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.stuckApp]
  simp only [callFn, stuckAppL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "stuck_app_cong",
      callW_spec p n "stuck_irrel"] <;>
  simp_all [sapK1, call1W, LocEq, St.setLocs_cons, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

/-- **`stuck_app` refines `defeqStuck`'s application arm** (`stuckAppT`) at the knot. -/
@[refines_part ConRon.Arena.defeqStuck "the application arm (stuckAppT)"]
theorem stuckApp_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "stuck_app" [mode, vis, d, a, b]
      (stuckAppT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (stuckApp_spec p hq n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  rw [stuckAppT_eq]
  obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
  have h₁ := CoreSpec.of_callW (appCong_at p hq hc n hk F s a₀ dn vis fe M eb mode d a b hF hn hs ha hb)
    hc1
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  simp only [sapK1] at hW1
  by_cases h0 : r₁.headD 0 ≠ 0
  · simp only [h0, ne_eq, not_false_eq_true, ↓reduceIte] at hW1
    rw [decBool_true_of h0]; exact coreRef_true hS₁ hW1
  simp only [h0, ↓reduceIte] at hW1
  simp only [ne_eq, Decidable.not_not] at h0
  rw [decBool_false_of h0]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact CoreSpec.of_call1W (s₀ := ⟨m₁, Locals.init []⟩)
    (stuckIrrel_at p hq hi hc n hk F _ _ dn vis fe M₁ eb mode d a b hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩
      ha hb) (fun r r' h => by simp only [decBool, h]) hW1

end L.Arena
