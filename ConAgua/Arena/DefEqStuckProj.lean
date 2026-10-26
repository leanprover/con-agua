import ConAgua.Arena.DefEqStuckDisp

/-!
# `ldpr_exit`, `lazy_delta_proj_reduction`, `defeq_proj_pair` (lane `defeq`, helper `defeq-top`)

The projection loop (`lazyDeltaProjReduction`) as a named block (`ldprLoopB`): one
`lazy_delta_step` per iteration, the exit on a verdict its own function (`ldprExitT`). The
model by L fuel (`ldprW`) refines the twin's loop at every twin fuel `K + 1 ≥` the L fuel
(`ldprW_ok`, the shape of lane `whnf`'s `coreLoopW_ok`); the twin's budget is `2^62`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin -/

/-- The projection loop's exit on a verdict (`.eq`, or the projections tried on both sides). -/
def ldprExitT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (sn : NIdx)
    (i : Nat) (a b : EIdx) : DeltaStepA → AM Bool
  | .cont _ _ => pure false
  | .eq => pure true
  | .diff | .unknown => do
    match ← reduceProjCore mode r fe depth sn i a with
    | some x =>
      match ← reduceProjCore mode r fe depth sn i b with
      | some y => r.defeq depth x y
      | none => r.defeq depth a b
    | none => r.defeq depth a b

theorem ldpr_cont_run (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (sn : NIdx) (i K : Nat) (a b a' b' : EIdx) (s s₁ : AState)
    (h : (lazyDeltaStep mode r fe depth a b).run s = .ok (.cont a' b', s₁)) :
    (lazyDeltaProjReduction mode r fe depth sn i (K + 1) a b).run s =
      (lazyDeltaProjReduction mode r fe depth sn i K a' b').run s₁ := by
  simp only [lazyDeltaProjReduction, StateT.run_bind, h, except_ok_bind]

theorem ldpr_exit_run (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (sn : NIdx) (i K : Nat) (a b : EIdx) (s s₁ : AState) (st : DeltaStepA)
    (hst : ∀ a' b', st ≠ .cont a' b')
    (h : (lazyDeltaStep mode r fe depth a b).run s = .ok (st, s₁)) :
    (lazyDeltaProjReduction mode r fe depth sn i (K + 1) a b).run s =
      (ldprExitT mode r fe depth sn i a b st).run s₁ := by
  simp only [lazyDeltaProjReduction, StateT.run_bind, h, except_ok_bind]
  cases st with
  | cont a' b' => exact absurd rfl (hst a' b')
  | eq | diff | unknown => rfl

/-! ## `ldpr_exit` -/

section exK
variable (p : Prog) (n : Nat) (mode vis d sn i a b k : Word)

def exK2 (px : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then call1W p n "defeq" [mode, vis, d, px, r.tail.headD 0] m
    else call1W p n "defeq" [mode, vis, d, a, b] m

def exK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then exK2 p n mode vis d a b (r.tail.headD 0)
      (callW p n "reduce_proj_core" [mode, vis, d, sn, i, b] m)
    else call1W p n "defeq" [mode, vis, d, a, b] m

/-- **The model of `ldpr_exit`.** -/
def exK (m : Mem) : Option (Word × Mem) :=
  if k = 1 then some (1, m)
  else exK1 p n mode vis d sn i a b (callW p n "reduce_proj_core" [mode, vis, d, sn, i, a] m)

end exK

theorem ldprExit_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (mode vis d sn i a b k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ldpr_exit" [mode, vis, d, sn, i, a, b, k]
    ⦃fun r s' => LocEq s' s₀ ∧ exK p n mode vis d sn i a b k s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.ldprExit]
  simp only [callFn, ldprExitL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "reduce_proj_core",
      callW_spec p n "defeq"] <;>
  simp_all [exK, exK1, exK2, call1W, LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

theorem decOptR_someS {r : List Word} (h : r.headD 0 ≠ 0) : decOptR r = some (decE (r.tail.headD 0)) := by
  simp only [decOptR, decOpt, h, ↓reduceIte]
theorem decOptR_noneS {r : List Word} (h : r.headD 0 = 0) : decOptR r = none := by
  simp only [decOptR, decOpt, h, ↓reduceIte]

theorem decDS_zero {r : List Word} (h : r.headD 0 = 0) :
    decDSs r = .cont (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0)) := by
  unfold decDSs; rw [if_pos h]

theorem decDS_nz {r : List Word} (h : r.headD 0 ≠ 0) : decDSs r = decDSs [r.headD 0] := by
  unfold decDSs
  show (if r.headD 0 = 0 then _ else _) = (if r.headD 0 = 0 then _ else _)
  rw [if_neg h, if_neg h]
  rfl

theorem decDS_ne_cont {r : List Word} (h : r.headD 0 ≠ 0) (a b : EIdx) : decDSs r ≠ .cont a b := by
  unfold decDSs; rw [if_neg h]
  split
  · exact fun e => by cases e
  split
  · exact fun e => by cases e
  · exact fun e => by cases e

/-- **`ldpr_exit` refines `ldprExitT`** on a verdict word `k ≠ 0`. -/
@[refines_part ConRon.Arena.lazyDeltaProjReduction "the exit on a verdict (ldprExitT)"]
theorem ldprExit_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d sn i a b k : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hsn : HW sn) (ha : HW a) (hb : HW b)
    (hk0 : k ≠ 0) :
    CoreSpec p (n + 1) "ldpr_exit" [mode, vis, d, sn, i, a, b, k]
      (ldprExitT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE a) (decE b) (decDSs [k])) decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (ldprExit_spec p hq n s₀ mode vis d sn i a b k)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  have hdef : ∀ (st : AState) (m : Mem) (M' : ModeMaps) (x y : Word), CoreS dn m st vis fe M' eb →
      HW x → HW y → call1W p n "defeq" [mode, vis, d, x, y] m = some (r.headD 0, s'.mem) →
      CoreRef ((coreKnot (decMode mode) fe id F).defeq d.toNat (decE x) (decE y)) st decBool
        dn m vis fe M' eb r s'.mem := fun st m M' x y hS' hx hy hc' =>
    CoreSpec.of_call1W (s₀ := ⟨m, Locals.init []⟩)
      (hK.defeq F _ st dn vis fe M' eb mode d x y hF hn ⟨hS', hs.mode4, hs.eb_mode⟩ hx hy)
      (fun r r' h => by simp only [decBool, h]) hc'
  simp only [exK] at hW
  by_cases h1 : k = 1
  · rw [if_pos h1] at hW
    have : decDSs [k] = .eq := by simp [decDSs, h1]
    rw [this]
    exact coreRef_true hS hW
  rw [if_neg h1] at hW
  have hst : decDSs [k] = (if k = 2 then .diff else .unknown) := by
    unfold decDSs; simp [hk0, h1]
  have hbody : ∀ st, (st = DeltaStepA.diff ∨ st = DeltaStepA.unknown) →
      ldprExitT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE a) (decE b) st =
      (do match ← reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
            (decI sn) i.toNat (decE a) with
          | some x =>
            match ← reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
                (decI sn) i.toNat (decE b) with
            | some y => (coreKnot (decMode mode) fe id F).defeq d.toNat x y
            | none => (coreKnot (decMode mode) fe id F).defeq d.toNat (decE a) (decE b)
          | none => (coreKnot (decMode mode) fe id F).defeq d.toNat (decE a) (decE b)) := by
    rintro st (rfl | rfl) <;> rfl
  rw [hbody _ (by rw [hst]; split <;> simp)]
  cases n with
  | zero => simp [exK1, callW_zero] at hW
  | succ n' =>
  obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
  have h₁ := CoreSpec.of_callW (hc.reduceProjCore n' (hk.mono (by omega)) F (by omega) (by omega) s a₀
    dn vis fe M eb mode d sn i a hs hsn ha) hc1
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  simp only [exK1] at hW1
  by_cases f1 : r₁.headD 0 ≠ 0
  · simp only [f1, ne_eq, not_false_eq_true, ↓reduceIte] at hW1
    rw [decOptR_someS f1]
    obtain ⟨r₂, m₂, hc2, hW2⟩ := callW_cases rfl hW1
    have h₂ := CoreSpec.of_callW (hc.reduceProjCore n' (hk.mono (by omega)) F (by omega) (by omega)
      ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d sn i b ⟨hS₁, hs.mode4, hs.eb_mode⟩ hsn hb) hc2
    refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
    simp only [exK2] at hW2
    by_cases f2 : r₂.headD 0 ≠ 0
    · simp only [f2, ne_eq, not_false_eq_true, ↓reduceIte] at hW2
      rw [decOptR_someS f2]
      exact hdef _ m₂ M₂ _ _ hS₂ h₁.2.2.2.2 h₂.2.2.2.2 hW2
    · simp only [f2, ne_eq, not_false_eq_true, ↓reduceIte, Decidable.not_not] at hW2
      rw [decOptR_noneS (by simpa using f2)]
      exact hdef _ m₂ M₂ _ _ hS₂ ha hb hW2
  · simp only [f1, ↓reduceIte] at hW1
    rw [decOptR_noneS (by simpa using f1)]
    exact hdef _ m₁ M₁ _ _ hS₁ ha hb hW1

theorem ldprExit_at (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d sn i a b k : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      HW sn → HW a → HW b → k ≠ 0 →
      CoreSpec p n "ldpr_exit" [mode, vis, d, sn, i, a, b, k]
        (ldprExitT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
          (decE a) (decE b) (decDSs [k])) decBool s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, sn, i, a, b, k, hF, hn, hs, h1, h2, h3, h4 =>
      ldprExit_refines p hq hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d sn i a b k
        (by omega) (by omega) hs h1 h2 h3 h4

/-! ## The loop -/

/-- **The model of the projection loop** at L fuel `n`. -/
def ldprW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, mode, vis, d, sn, i, a, b =>
    match callW p n "lazy_delta_step" [mode, vis, d, a, b] m with
    | none => none
    | some (r, m₁) =>
      if r.headD 0 ≠ 0 then call1W p n "ldpr_exit" [mode, vis, d, sn, i, a, b, r.headD 0] m₁
      else ldprW p n m₁ mode vis d sn i (r.tail.headD 0) (r.tail.tail.headD 0)

section ldprArms
variable (p : Prog) (n : Nat) (m m₁ : Mem) (mode vis d sn i a b : Word) (r : List Word)

end ldprArms

theorem ldprLoopB_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n ldprLoopB
    ⦃fun r s' => r ≠ .brk ∧
      ldprW p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)
        (s₀.loc 6) = some ((r.retOr [0]).headD 0, s'.mem) ∧ r ≠ .normal; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := ldprLoopB) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih, callW_spec p n "lazy_delta_step",
      callW_spec p n "ldpr_exit"] <;>
    simp_all [ldprW, call1W, LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval,
      St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr]

theorem ldpr_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (mode vis d sn i a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lazy_delta_proj_reduction" [mode, vis, d, sn, i, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ ldprW p (n + 1) s₀.mem mode vis d sn i a b =
      some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.ldpr]
  simp only [callFn, lazyDeltaProjReductionL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (ldprLoopB_spec p (n + 1) s)] <;>
    finish

/-- **The loop's model refines `lazyDeltaProjReduction`** at every twin loop fuel `K + 1 ≥ k`. -/
theorem ldprW_ok (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (mode d sn i : Word) (hmode : mode < 4) (hsn : HW sn) (hd : d.toNat < 2 ^ 63) :
    ∀ k, k ≤ n + 1 → ∀ K, k ≤ K + 1 → ∀ (m m' : Mem) (a : AState) (MM : ModeMaps) (eb x y v : Word),
      CoreS dn m a vis fe MM eb → eb = (mode >>> 1) &&& 1 → HW x → HW y →
      ldprW p k m mode vis d sn i x y = some (v, m') →
      CoreRef (lazyDeltaProjReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
        (decI sn) i.toNat K (decE x) (decE y)) a decBool dn m vis fe MM eb [v] m' := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [ldprW] at h
  | succ k ih =>
    intro hkn K hK m m' a MM eb x y v hS heb hx hy h
    simp only [ldprW] at h
    rcases hcl : callW p k "lazy_delta_step" [mode, vis, d, x, y] m with _ | ⟨r, m₁⟩ <;> simp only [hcl, reduceCtorEq] at h
    cases k with
    | zero => simp [callW_zero] at hcl
    | succ j =>
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hstep := hc.lazyDeltaStep j (hk.mono (by omega)) F (by omega) (by omega)
      ⟨m, Locals.init []⟩ a dn vis fe MM eb mode d x y ⟨hS, hmode, heb⟩ hx hy hd
    obtain ⟨hok, hA, hres, hrw⟩ := CoreSpec.of_callW hstep hcl
    have hsr := AM.run_of_ok _ _ hok
    rw [hres] at hsr
    obtain ⟨M', hS₁, hK₁, hSt₁⟩ := hA
    by_cases h0 : r.headD 0 = 0
    · rw [if_neg (by simpa using h0)] at h
      rw [decDS_zero h0] at hsr
      have hrun := ldpr_cont_run (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn)
        i.toNat K' (decE x) (decE y) _ _ a _ hsr
      obtain ⟨hok₂, hA₂, hres₂, hrw₂⟩ := ih (by omega) K' (by omega) m₁ m' _ M' eb _ _ v hS₁ heb
        hrw.2.1 hrw.2.2 h
      rw [AM.run_of_ok _ _ hok₂] at hrun
      obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
      refine ⟨hok', ?_, hres'.trans hres₂, hrw₂⟩
      rw [hst']
      exact CoreAfter.comp hK₁ hSt₁ hA₂
    · rw [if_pos h0] at h
      have hds : decDSs r = decDSs [r.headD 0] := decDS_nz h0
      have hnc : ∀ a' b', decDSs r ≠ .cont a' b' := decDS_ne_cont h0
      have hrun := ldpr_exit_run (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn)
        i.toNat K' (decE x) (decE y) _ _ _ hnc hsr
      rw [hds] at hrun
      have hex := ldprExit_at p hq hc (j + 1) (hk.mono (by omega)) F ⟨m₁, Locals.init []⟩ _ dn vis fe
        M' eb mode d sn i x y (r.headD 0) (by omega) (by omega) ⟨hS₁, hmode, heb⟩ hsn hx hy h0
      obtain ⟨hok₂, hA₂, hres₂, hrw₂⟩ := CoreSpec.of_call1W (r := [v]) hex
        (fun r r' h => by simp only [decBool, h]) (by simpa using h)
      rw [AM.run_of_ok _ _ hok₂] at hrun
      obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
      refine ⟨hok', ?_, hres'.trans hres₂, hrw₂⟩
      rw [hst']
      exact CoreAfter.comp hK₁ hSt₁ hA₂

/-- **`lazy_delta_proj_reduction` refines `lazyDeltaProjReduction`** at every twin loop fuel
`K ≥ n` (the twin's `defeqLoopFuel` is `2^62`). -/
@[refines ConRon.Arena.lazyDeltaProjReduction]
theorem ldpr_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F K : Nat) (hF : n ≤ F) (hK : n ≤ K) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d sn i a b : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hsn : HW sn) (ha : HW a)
    (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "lazy_delta_proj_reduction" [mode, vis, d, sn, i, a, b]
      (lazyDeltaProjReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn)
        i.toNat K (decE a) (decE b)) decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (ldpr_spec p hq n s₀ mode vis d sn i a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  obtain ⟨hok, hA, hres, hrw⟩ := ldprW_ok p hq hc n hk F hF hn dn vis fe mode d sn i hs.mode4 hsn hd
    (n + 1) (Nat.le_refl _) K (by omega) s.mem s'.mem a₀ M eb a b (r.headD 0) hs.rel hs.eb_mode ha hb hW
  exact ⟨hok, hA, hres.trans (by simp [decBool]), hrw⟩

/-! ## `defeq_proj_pair` -/

section ppK
variable (p : Prog) (n : Nat) (mode vis d a b : Word)

/-- **The model of `defeq_proj_pair`.** -/
def ppK (m : Mem) : Option (Word × Mem) :=
  if a >>> 28 ≠ 9 then some (0, m)
  else if b >>> 28 ≠ 9 then some (0, m)
  else if tierW a ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m PROJ (tierW a) ≤ idxW a then none
  else if tierW b ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m PROJ (tierW b) ≤ idxW b then none
  else if tfld m PROJ (tierW a) (idxW a) 0 ≠ tfld m PROJ (tierW b) (idxW b) 0
    then some (0, m)
  else if tfld m PROJ (tierW a) (idxW a) 1 ≠
      tfld m PROJ (tierW b) (idxW b) 1 then some (0, m)
  else call1W p n "lazy_delta_proj_reduction" [mode, vis, d,
    tfld m PROJ (tierW a) (idxW a) 0, tfld m PROJ (tierW a) (idxW a) 1,
    tfld m PROJ (tierW a) (idxW a) 2, tfld m PROJ (tierW b) (idxW b) 2] m

end ppK

theorem projPair_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_proj_pair" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ ppK p n mode vis d a b s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.projPair]
  simp only [callFn, defeqProjPairL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, evalE_tld, tld,
    evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "lazy_delta_proj_reduction"] <;>
  simp_all [ppK, call1W, tierW, idxW, LocEq, BinOp.eval, St.setLocs_cons, CTL,
    PJREC, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

section ppRuns
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx)
  (st : AState)

theorem pp_no (h : (a.tag == ETag.proj && b.tag == ETag.proj) = false) :
    (defeqProjPair mode r fe depth a b).run st = .ok (false, st) := by
  simp only [defeqProjPair, h, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem pp_both (h : (a.tag == ETag.proj && b.tag == ETag.proj) = true) (s₁ s₂ : NIdx) (i₁ i₂ : Nat)
    (e₁ e₂ : EIdx) (hva : st.store.view a = some (.proj s₁ i₁ e₁))
    (hvb : st.store.view b = some (.proj s₂ i₂ e₂)) :
    (defeqProjPair mode r fe depth a b).run st =
      (if (s₁ == s₂ && i₁ == i₂) = true then
        lazyDeltaProjReduction mode r fe depth s₁ i₁ defeqLoopFuel e₁ e₂
      else pure false).run st := by
  simp only [defeqProjPair, h, ↓reduceIte, StateT.run_bind, view_run _ _ _ hva, view_run _ _ _ hvb,
    except_ok_bind]

end ppRuns

theorem ldpr_at (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F K : Nat), n ≤ F → n ≤ K + 1 → n ≤ 2 ^ 62 → ∀ (s₀ : St)
      (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d sn i a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW sn → HW a → HW b →
      d.toNat < 2 ^ 63 →
      CoreSpec p n "lazy_delta_proj_reduction" [mode, vis, d, sn, i, a, b]
        (lazyDeltaProjReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn)
          i.toNat K (decE a) (decE b)) decBool s₀ a₀ dn vis fe M eb
  | 0, _, _, _, _, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, K, hF, hK, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, sn, i, a, b, hs, h1, h2, h3, hd =>
      ldpr_refines p hq hc n (hk.mono (by omega)) F K (by omega) (by omega) (by omega) s₀ a₀ dn vis fe
        M eb mode d sn i a b hs h1 h2 h3 hd

/-- **`defeq_proj_pair` refines `defeqProjPair`** at the knot. -/
@[refines ConRon.Arena.defeqProjPair]
theorem projPair_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "defeq_proj_pair" [mode, vis, d, a, b]
      (defeqProjPair (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
      decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (projPair_spec p hq n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hR := hS.arena.1
  have htag : ∀ h : Word, HW h → ((decE h).tag == ETag.proj) = decide (h >>> 28 = 9) :=
    fun h hh => tag_beq_w _ hh 9 (by decide) ETag.proj rfl 9 rfl
  have hfalse : ∀ (hW' : some ((0 : Word), s.mem) = some (r.headD 0, s'.mem)),
      (((decE a).tag == ETag.proj && (decE b).tag == ETag.proj) = false) →
      CoreRef (defeqProjPair (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a)
        (decE b)) a₀ decBool dn s.mem vis fe M eb r s'.mem := by
    intro hW' hno
    obtain ⟨hr, hm⟩ := some_pair_inj hW'
    rw [← hm]
    exact coreRef_pure hS (pp_no _ _ fe _ _ _ a₀ hno) (decBool_false_of hr.symm).symm
      (by unfold ResH; rw [← hr]; exact hw0)
  simp only [ppK] at hW
  by_cases g1 : a >>> 28 ≠ 9
  · rw [if_pos g1] at hW
    exact hfalse hW (by rw [htag a ha]; simp [g1])
  rw [if_neg g1] at hW
  by_cases g2 : b >>> 28 ≠ 9
  · rw [if_pos g2] at hW
    exact hfalse hW (by rw [htag a ha, htag b hb]; simp [g2])
  rw [if_neg g2] at hW
  have g1' : a >>> 28 = 9 := by simpa using g1
  have g2' : b >>> 28 = 9 := by simpa using g2
  obtain ⟨c1, hW⟩ := of_ite_none hW
  obtain ⟨c2, hW⟩ := of_ite_none hW
  obtain ⟨c3, hW⟩ := of_ite_none hW
  obtain ⟨c4, hW⟩ := of_ite_none hW
  obtain ⟨hva, hx1, hx3⟩ := view_proj s.mem a₀ hR a ha ⟨c1, by simpa using c2⟩ g1'
  obtain ⟨hvb, hy1, hy3⟩ := view_proj s.mem a₀ hR b hb ⟨c3, by simpa using c4⟩ g2'
  have hboth : ((decE a).tag == ETag.proj && (decE b).tag == ETag.proj) = true := by
    rw [htag a ha, htag b hb]; simp [g1', g2']
  refine coreRef_congr (pp_both _ _ fe _ _ _ a₀ hboth _ _ _ _ _ _ hva hvb) ?_
  generalize tfld s.mem PROJ (tierW a) (idxW a) 0 = x1 at hW hx1
  generalize tfld s.mem PROJ (tierW b) (idxW b) 0 = y1 at hW hy1
  generalize tfld s.mem PROJ (tierW a) (idxW a) 1 = x2 at hW
  generalize tfld s.mem PROJ (tierW b) (idxW b) 1 = y2 at hW
  generalize tfld s.mem PROJ (tierW a) (idxW a) 2 = x3 at hW hx3
  generalize tfld s.mem PROJ (tierW b) (idxW b) 2 = y3 at hW hy3
  by_cases e1 : x1 ≠ y1
  · rw [if_pos e1] at hW
    obtain ⟨hr, hm⟩ := some_pair_inj hW
    rw [← hm]
    have : ((decI x1 : NIdx) == decI y1 && x2.toNat == y2.toNat) = false := by
      rw [decI_beq _ _ hx1 hy1]; simp [e1]
    rw [this]
    exact coreRef_pure hS rfl (decBool_false_of hr.symm).symm (by unfold ResH; rw [← hr]; exact hw0)
  rw [if_neg e1] at hW
  by_cases e2 : x2 ≠ y2
  · rw [if_pos e2] at hW
    obtain ⟨hr, hm⟩ := some_pair_inj hW
    rw [← hm]
    have : ((decI x1 : NIdx) == decI y1 && x2.toNat == y2.toNat) = false := by
      have : x2.toNat ≠ y2.toNat := fun e => e2 (UInt64.toNat_inj.mp e)
      simp [this]
    rw [this]
    exact coreRef_pure hS rfl (decBool_false_of hr.symm).symm (by unfold ResH; rw [← hr]; exact hw0)
  rw [if_neg e2] at hW
  have e1' : x1 = y1 := by simpa using e1
  have e2' : x2 = y2 := by simpa using e2
  subst e1' e2'
  simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
  exact CoreSpec.of_call1W (s₀ := ⟨s.mem, Locals.init []⟩)
    (ldpr_at p hq hc n hk F defeqLoopFuel hF (by unfold defeqLoopFuel; omega) hn _ a₀ dn vis fe M eb
      mode d x1 x2 x3 y3 ⟨hS, hs.mode4, hs.eb_mode⟩ hx1 hx3 hy3 hd) (fun r r' h => by simp only [decBool, h]) hW

end L.Arena
