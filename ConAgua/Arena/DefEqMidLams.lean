module

public import ConAgua.Arena.DefEqMidPeel
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.InferBodyLet
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.Front.Preserve
import all ConAgua.Arena.DefEq

@[expose] public section

/-!
# The λ-telescope: `defeq_lams` (lane `defeq`)

The loop is split for the proofs (`DefEq.lean`): `lams_inst` (the fresh free variable, both bodies
instantiated), `lams_open` (the domains compared, then `lams_inst`), `lam_pair` (the twin's
`lamPair?`), and the uncounted loop `defeqLamsLoop` calling them and `defeq_lams_inner`. The
twin's `defeqLams` counts its levels on `lamsFuel = 2^62`; the L loop runs on its own fuel, at
most `2^62 + 1`, and an iteration at the twin's fuel `0` would call `lams_open` at L fuel `0`,
which does not return (`lams_ref`, both outcomes). Its unfolding lemmas are stated by `delta` and
`rfl`, as `defeqPeel`'s (`lamsLvl`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- The lookups of this file. -/
structure LamsProg (p : Prog) : Prop where
  peel : PeelProg p
  mid : DefEqMidProg p
  inst : p.lookup "lams_inst" = some lamsInstL
  open_ : p.lookup "lams_open" = some lamsOpenL
  pair : p.lookup "lam_pair" = some lamPairL
  lams : p.lookup "defeq_lams" = some defeqLamsL

/-- A twin run that keeps the state, as a `CoreRef` with any validity. -/
theorem coreRef_pure' {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {r : List Word} {v : α} {ok : List Word → Prop} (hS : CoreS dn m a₀ vis fe M eb)
    (hrun : T.run a₀ = .ok (v, a₀)) (hv : v = dec r) (hr : ok r) :
    CoreRef T a₀ dec dn m vis fe M eb r m ok := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok, ?_, by rw [hres, hv], hr⟩
  rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩

/-! ## `lams_inst` -/

/-- The fresh free variable, both bodies instantiated with it (the twin's lines in
`defeqLams`). -/
def lamsInstT (depth : Nat) (ty₂ body₁ body₂ : EIdx) : AM (EIdx × EIdx) := do
  let fv ← internFVarE depth ty₂
  let b₁ ← instantiate1Fast coreWalkFuel body₁ fv 0
  let b₂ ← instantiate1Fast coreWalkFuel body₂ fv 0
  pure (b₁, b₂)

/-- `(b1, b2)`. -/
def decPair (r : List Word) : EIdx × EIdx := (decE (r.headD 0), decE (r.tail.headD 0))

/-- **`lams_inst` is its model `linW`** (generated). -/
l_model lamsInst_spec (p : Prog) (hp : LamsProg p)
  fns [hp.inst ↦ linW tuple]
  specs [callW_spec p n "intern_fvar", callW_spec p n "inst1"]
  grind [arena_grind]

/-- **`lams_inst` refines `lamsInstT`.** -/
theorem lamsInst_refines (p : Prog) (hp : LamsProg p) (hi : Inst1OK p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb d ty₂ body₁ body₂ : Word) (hS : CoreS dn s₀.mem a₀ vis fe M eb) (h₂ : HW ty₂)
    (hb₁ : HW body₁) (hb₂ : HW body₂) :
    CoreSpec p (n + 1) "lams_inst" [d, ty₂, body₁, body₂]
      (lamsInstT d.toNat (decE ty₂) (decE body₁) (decE body₂)) decPair s₀ a₀ dn vis fe M eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (lamsInst_spec p hp (n + 1) s₀ d ty₂ body₁ body₂)
  subst hs0
  refine ⟨hloc, ?_⟩
  unfold lamsInstT internFVarE
  rw [linW.arm1] at hW
  cases hc1 : callW p n "intern_fvar" [d, ty₂] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1, linW.k_intern_fvar.arm1] at hW
  have e₁ := (peel_internFVar_core hp.peel hS d ty₂ h₂ r₁ hc1).1
  refine coreRef_bind e₁ (fun M₁ hS₁ => ?_)
  cases hc2 : callW p n "inst1" [body₁, r₁.headD 0, 0] m₁ with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2, linW.k_inst1.arm1] at hW
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (hi n _ _ dn vis fe M₁ eb body₁ (r₁.headD 0) 0 hS₁ hb₁ e₁.resOk) hc2
  rw [toNat_zero_w] at e₂
  refine coreRef_bind e₂ (fun M₂ hS₂ => ?_)
  cases hc3 : callW p n "inst1" [body₂, r₁.headD 0, 0] m₂ with
  | none => rw [hc3] at hW; cases hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [hc3, linW.k_inst1_2.arm1, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
  obtain ⟨h1, h2, hm⟩ := hW
  have e₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (hi n _ _ dn vis fe M₂ eb body₂ (r₁.headD 0) 0 hS₂ hb₂ e₁.resOk) hc3
  rw [toNat_zero_w] at e₃
  refine coreRef_bind e₃ (fun M₃ hS₃ => ?_)
  rw [← hm]
  exact coreRef_ret hS₃ (by simp only [decPair, decH, ← h1, ← h2]) ⟨h1 ▸ e₂.resOk, h2 ▸ e₃.resOk⟩

/-! ## `lams_open` -/

/-- One λ level opened, as the twin computes it: the domains, then `lamsInstT`. -/
def lamsOpenT (r : CoreFnsA) (depth : Nat) (ty₁ body₁ ty₂ body₂ : EIdx) :
    AM (Option (EIdx × EIdx)) := do
  if !(← r.defeq depth ty₁ ty₂) then pure none
  else do
    let x ← lamsInstT depth ty₂ body₁ body₂
    pure (some x)

/-- `(ok, b1, b2)`. -/
def decLO (r : List Word) : Option (EIdx × EIdx) :=
  if r.headD 0 = 0 then none else some (decE (r.tail.headD 0), decE (r.tail.tail.headD 0))

/-- **`lams_open`'s model, both outcomes** (generated; the `defeq` slot through its run,
`lams_inst` lifted). -/
l_model loE_spec (p : Prog) (hf : p.lookup "lams_open" = some lamsOpenL)
  fns [hf ↦ loE list]
  specs [callW_spec p n "lams_inst"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`lams_open` refines `lamsOpenT`, both outcomes**: the errors are the domains' `defeq` slot
call's. -/
theorem lo_ref (p : Prog) (hp : LamsProg p) (hi : Inst1OK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty₁ body₁ ty₂ body₂ : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (h₁ : HW ty₁) (hb₁ : HW body₁) (h₂ : HW ty₂) (hb₂ : HW body₂) :
    RefE (KnotUpToE p n) (loE p (n + 1) s₀.mem mode vis d ty₁ body₁ ty₂ body₂)
      (lamsOpenT (coreKnot (decMode mode) fe id F) d.toNat (decE ty₁) (decE body₁) (decE ty₂)
        (decE body₂)) a₀ (CorePost decLO dn s₀.mem vis fe M eb Res3) := by
  unfold lamsOpenT
  simp only [loE]
  cases n with
  | zero => exact RefE.callE_zero fun _ => rfl
  | succ n' =>
  refine RefE.bind_callE (fun _ => rfl) ((hk _ (Nat.le_refl _)).defeq F s₀ a₀ dn vis fe M eb mode d ty₁ ty₂ hF
    hn hs h₁ h₂) (fun (hG : KnotUpToE p (n' + 1)) => (hG _ (Nat.le_refl _)).defeq F s₀ a₀ dn vis fe M eb mode
      d ty₁ ty₂ hF hn hs h₁ h₂) fun r₁ m₁ _ e₁ => RefE.after_core (w := id) e₁ fun M₁ hS₁ _ => ?_
  dsimp only [loE.k_defeq]
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0, decBool_f h0]
    exact RefE.ret rfl (CorePost.ret hS₁ (by simp only [decLO]; rfl) ⟨hw0, hw0, hw0⟩)
  rw [ite_eq_right h0, decBool_t h0]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine RefE.bind_callW (fun _ => rfl) (lamsInst_refines p hp hi n' ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb d
    ty₂ body₁ body₂ hS₁ h₂ hb₁ hb₂) fun r₂ m₂ _ e₂ => RefE.after_core (w := id) e₂ fun M₂ hS₂ _ => ?_
  dsimp only [loE.k_lams_inst]
  exact RefE.ret rfl (CorePost.ret hS₂ (by simp only [decLO, decPair]; rfl)
    ⟨hw1, e₂.resOk.1, e₂.resOk.2⟩)

/-! ## `lam_pair` -/

/-- **`lam_pair` is its model `lpeelW`** (generated). -/
l_model lamPair_spec (p : Prog) (hp : LamsProg p)
  fns [hp.pair ↦ lpeelW tuple]
  specs [callW_spec p n "e_view"]
  grind [arena_grind]

/-- `(f, ty1, body1, ty2, body2)`. -/
def decLP (r : List Word) : Option (EIdx × EIdx × EIdx × EIdx) :=
  if r.headD 0 = 0 then none
  else some (decE (r.tail.headD 0), decE (r.tail.tail.headD 0), decE (r.tail.tail.tail.headD 0),
    decE (r.tail.tail.tail.tail.headD 0))

/-- Five result words below `2^32`. -/
def Res5 (r : List Word) : Prop :=
  HW (r.headD 0) ∧ HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) ∧ HW (r.tail.tail.tail.headD 0) ∧
    HW (r.tail.tail.tail.tail.headD 0)

/-- **`lam_pair` refines `lamPair?`.** -/
@[refines ConRon.Arena.lamPair?]
theorem lamPair_refines (p : Prog) (hp : LamsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb a b : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "lam_pair" [a, b] (lamPair? (decE a) (decE b)) decLP s₀ a₀ dn vis fe M eb
      Res5 := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (lamPair_spec p hp (n + 1) s₀ a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  unfold lamPair?
  simp only [decE_tag_lam_beq a ha, decE_tag_lam_beq b hb, Bool.and_eq_true, decide_eq_true_eq]
  by_cases hno : tagW a ≠ 5 ∨ tagW b ≠ 5
  · rw [lpeelW.arm1 (hc1 := hno), Option.some.injEq] at hW
    simp only [Prod.mk.injEq] at hW
    obtain ⟨g1, g2, g3, g4, g5, hm⟩ := hW
    have hc : ¬ (tagW a = 5 ∧ tagW b = 5) := fun h => hno.elim (fun h' => h' h.1) (fun h' => h' h.2)
    simp only [hc, ↓reduceIte]
    rw [← hm]
    exact coreRef_ret hS (by simp only [decLP, ← g1, ↓reduceIte])
      ⟨g1 ▸ hw0, g2 ▸ hw0, g3 ▸ hw0, g4 ▸ hw0, g5 ▸ hw0⟩
  rw [lpeelW.arm2 (hc1 := hno)] at hW
  have h5a : tagW a = 5 := Classical.byContradiction fun h => hno (.inl h)
  have h5b : tagW b = 5 := Classical.byContradiction fun h => hno (.inr h)
  simp only [h5a, h5b, and_self, ↓reduceIte]
  cases hc1 : callW p n "e_view" [a] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1, lpeelW.k_e_view.arm1] at hW
  obtain ⟨rfl, ha1, ha2, hva⟩ := eView_lam_callW (a := a₀) hp.peel.eview hS.arena.base ha h5a hc1
  cases hc2 : callW p n "e_view" [b] s.mem with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2, lpeelW.k_e_view_2.arm1, Option.some.injEq] at hW
  simp only [Prod.mk.injEq] at hW
  obtain ⟨g1, g2, g3, g4, g5, hm⟩ := hW
  obtain ⟨rfl, hb1, hb2, hvb⟩ := eView_lam_callW (a := a₀) hp.peel.eview hS.arena.base hb h5b hc2
  have hrun : (do
      match ← viewBind (decE a) with
      | none => failDanglingE
      | some (ty₁, body₁) =>
        match ← viewBind (decE b) with
        | none => failDanglingE
        | some (ty₂, body₂) => pure (some (ty₁, body₁, ty₂, body₂)) :
        AM (Option (EIdx × EIdx × EIdx × EIdx))).run a₀ =
      .ok (some (decE (r₁.tail.headD 0), decE (r₁.tail.tail.headD 0), decE (r₂.tail.headD 0),
        decE (r₂.tail.tail.headD 0)), a₀) := by
    rw [viewBind_bind_run, hva]
    simp only [viewBind_bind_run, hvb]
    rfl
  rw [← hm]
  refine coreRef_pure' hS hrun ?_ ⟨g1 ▸ hw1, g2 ▸ ha1, g3 ▸ ha2, g4 ▸ hb1, g5 ▸ hb2⟩
  simp only [decLP, ← g1, ← g2, ← g3, ← g4, ← g5]; rfl

/-! ## The twin's telescope, one level at a time -/

/-- The rest of a level after the bodies are opened: `lamPair?`, the equal-bodies shortcut, the
next level (`cont`) or the innermost comparison. -/
def lamsK (mode : ConLeche.CheckMode) (r : CoreFnsA) (depth : Nat)
    (cont : Nat → EIdx → EIdx → EIdx → EIdx → AM Bool) (b₁ b₂ : EIdx) : AM Bool := do
  match ← lamPair? b₁ b₂ with
  | some (ty₁', body₁', ty₂', body₂') =>
    if b₁ == b₂ then pure true
    else cont (depth + 1) ty₁' body₁' ty₂' body₂'
  | none => defeqLamsInner mode r depth b₁ b₂

/-- One level of the twin's `defeqLams`, verbatim, the recursive call abstracted as `cont` (as
`peelLvl`). -/
def lamsLvl (mode : ConLeche.CheckMode) (r : CoreFnsA) (fuel : Nat)
    (cont : Nat → EIdx → EIdx → EIdx → EIdx → AM Bool) (depth : Nat) (ty₁ body₁ ty₂ body₂ : EIdx) :
    AM Bool := do
  if !(← r.defeq depth ty₁ ty₂) then pure false
  else do
  let fv ← internFVarE depth ty₂
  let b₁ ← instantiate1Fast coreWalkFuel body₁ fv 0
  let b₂ ← instantiate1Fast coreWalkFuel body₂ fv 0
  match fuel with
  | 0 => defeqLamsInner mode r depth b₁ b₂
  | _ + 1 =>
    match ← lamPair? b₁ b₂ with
    | some (ty₁', body₁', ty₂', body₂') =>
      if b₁ == b₂ then pure true
      else cont (depth + 1) ty₁' body₁' ty₂' body₂'
    | none => defeqLamsInner mode r depth b₁ b₂

theorem defeqLams_succ_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (f depth : Nat)
    (ty₁ body₁ ty₂ body₂ : EIdx) :
    defeqLams mode r (f + 1) depth ty₁ body₁ ty₂ body₂ =
      lamsLvl mode r (f + 1) (defeqLams mode r f) depth ty₁ body₁ ty₂ body₂ := by
  delta defeqLams lamsLvl
  exact rfl

theorem lamsLvl_succ (mode : ConLeche.CheckMode) (r : CoreFnsA) (f : Nat)
    (cont : Nat → EIdx → EIdx → EIdx → EIdx → AM Bool) (depth : Nat) (ty₁ body₁ ty₂ body₂ : EIdx) :
    lamsLvl mode r (f + 1) cont depth ty₁ body₁ ty₂ body₂ =
      (lamsOpenT r depth ty₁ body₁ ty₂ body₂ >>= fun o => match o with
        | none => pure false
        | some (b₁, b₂) => lamsK mode r depth cont b₁ b₂) := by
  unfold lamsLvl lamsOpenT lamsInstT lamsK
  simp only [bind_assoc]
  congr 1
  funext c
  cases c <;> simp [bind_assoc]

/-! ## `defeq_lams`: the loop -/

/-- **`defeq_lams`' model, both outcomes** (the loop `lamsE.loop1`: `lams_open`, `lam_pair`,
`defeq_lams_inner` through their runs, `callE`). -/
l_model defeqLams_specE (p : Prog) (hf : p.lookup "defeq_lams" = some defeqLamsL)
  fns [hf ↦ lamsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified

/-! ## The loop refines `defeqLams` -/

section loopRef
variable (p : Prog) (hp : LamsProg p) (hi : Inst1OK p)

include hp hi in
/-- **The telescope loop refines `defeqLams`, both outcomes**, at every twin fuel `K` with
`k ≤ K + 1`. -/
theorem lams_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode : Word) (hmode : mode < 4) :
    ∀ k, k ≤ n + 1 → ∀ K, k ≤ K + 1 → ∀ (d ty₁ body₁ ty₂ body₂ : Word) (m : Mem) (s : AState)
      (M : ModeMaps) (eb : Word), CoreS dn m s vis fe M eb → eb = (mode >>> 1) &&& 1 → HW ty₁ →
      HW body₁ → HW ty₂ → HW body₂ → d.toNat + k < 2 ^ 64 →
      RefE (KnotNvG p n) (lamsE.loop1 p k m mode vis d ty₁ body₁ ty₂ body₂)
        (defeqLams (decMode mode) (coreKnot (decMode mode) fe id F) K d.toNat (decE ty₁)
          (decE body₁) (decE ty₂) (decE body₂)) s
        (fun v y a' => CorePost decBool dn m vis fe M eb ResH ([v.1], v.2) y a') := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    unfold lamsE.loop1; exact RefE.of_cls0 rfl
  | succ k ih =>
    intro hkn K hK d ty₁ body₁ ty₂ body₂ m s M eb hS heb h1 hb1 h2 hb2 hd
    rw [lamsE.loop1.arm1 (hc1 := rfl)]
    cases k with
    | zero => exact RefE.callE_zero fun _ => lamsE.k_lams_open.none ..
    | succ k' =>
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [defeqLams_succ_eq, lamsLvl_succ]
    have hL := loE_spec p hp.open_ (k' + 1) ⟨m, Locals.init []⟩ mode vis d ty₁ body₁ ty₂ body₂
    have H := lo_ref p hp hi k' (hk.mono (by omega)) F (by omega) (by omega) ⟨m, Locals.init []⟩ s dn vis
      fe M eb mode d ty₁ body₁ ty₂ body₂ ⟨hS, hmode, heb⟩ h1 hb1 h2 hb2
    refine RefE.bind_callE (s₀ := ⟨m, Locals.init []⟩) (fun _ => lamsE.k_lams_open.none ..)
      (RefE.coreSpec hL H) (fun (hG : KnotNvG p n) => RefE.coreSpecE hL hG.nv (hG.knot.mono (by omega)) H)
      fun r m₁ _ e₁ => RefE.after_core (w := fun (v : Word × Mem) => ([v.1], v.2)) e₁ fun M₁ hS₁ _ => ?_
    obtain ⟨-, hr1, hr2⟩ := e₁.resOk
    by_cases h0 : r.headD 0 = 0
    · rw [lamsE.k_lams_open.arm1 (hc1 := h0)]
      simp only [decLO, h0, ↓reduceIte]
      exact RefE.ret rfl (CorePost.ret hS₁ rfl resH_zero)
    rw [lamsE.k_lams_open.arm2 (hc1 := h0)]
    simp only [decLO, h0, ↓reduceIte, lamsK]
    refine RefE.bind_callE (s₀ := ⟨m₁, Locals.init []⟩) (fun _ => lamsE.k_lam_pair.none ..)
      (lamPair_refines p hp k' _ _ dn vis fe M₁ eb _ _ hS₁ hr1 hr2)
      (fun (hG : KnotNvG p n) => CoreSpecE.of_runs fun _ hc2 => ErrClaim.of_cls0
        (callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) _ _ _ hc2))
      fun q m₂ _ e₂ => RefE.after_core (w := fun (v : Word × Mem) => ([v.1], v.2)) e₂ fun M₂ hS₂ _ => ?_
    obtain ⟨-, hq1, hq2, hq3, hq4⟩ := e₂.resOk
    by_cases hq : q.headD 0 = 0
    · rw [lamsE.k_lam_pair.arm1 (hc1 := hq)]
      simp only [decLP, hq, ↓reduceIte]
      rcases hc3 : callE p (k' + 1) "defeq_lams_inner"
          [mode, vis, d, r.tail.headD 0, r.tail.tail.headD 0] m₂ with e | ⟨rr, m₃⟩
      · rw [lamsE.k_defeq_lams_inner.none]
        exact fun hG => RefE.run_err (liE_spec p hp.mid.lamsInner (k' + 1) ⟨m₂, Locals.init []⟩
          mode vis d _ _) trivial (hG.knot.mono (by omega)) (li_ref p k' (hk.mono (by omega)) F _ _ dn
            vis fe M₂ eb mode d _ _ (by omega) (by omega) ⟨hS₂, hmode, heb⟩ (by omega) hr1 hr2) hc3
      simp only [lamsE.k_defeq_lams_inner]
      obtain ⟨hrun, hR⟩ := (CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
        (defeqLamsInner_refines p hp.mid k' (hk.mono (by omega)) F _ _ dn vis fe M₂ eb mode d _ _
          (by omega) (by omega) ⟨hS₂, hmode, heb⟩ (by omega) hr1 hr2) (callW_of_callE hc3)).post
      exact RefE.ret hrun ⟨hR.after, by simpa [decBool] using hR.res, hR.valid⟩
    simp only [decLP, hq, ↓reduceIte, decE_beq_eq _ _ hr1 hr2]
    by_cases he : r.tail.headD 0 = r.tail.tail.headD 0
    · rw [lamsE.k_lam_pair.arm2 (hc1 := hq) (hc2 := he)]
      simp only [decide_eq_true he, ↓reduceIte]
      exact RefE.ret rfl (CorePost.ret hS₂ rfl resH_one)
    rw [lamsE.k_lam_pair.arm3 (hc1 := hq) (hc2 := he)]
    simp only [decide_eq_false he, Bool.false_eq_true, ↓reduceIte]
    have hd1 : (d + 1).toNat = d.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
    have := ih (by omega) K' (by omega) (d + 1) _ _ _ _ m₂ _ M₂ eb hS₂ heb hq1 hq2 hq3 hq4
      (by rw [hd1]; omega)
    rw [hd1] at this
    exact this

include hp hi in
/-- `defeq_lams` from its run, both outcomes (`lams_ref` at `lamsFuel`). -/
theorem defeqLams_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d ty₁ body₁ ty₂ body₂ : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (h1 : HW ty₁) (hb1 : HW body₁) (h2 : HW ty₂) (hb2 : HW body₂) (hd : d.toNat < 2 ^ 63) :
    RefE (KnotNvG p n) (lamsE p (n + 1) s₀.mem mode vis d ty₁ body₁ ty₂ body₂)
      (defeqLams (decMode mode) (coreKnot (decMode mode) fe id F) lamsFuel d.toNat (decE ty₁)
        (decE body₁) (decE ty₂) (decE body₂)) a₀
      (fun v y a' => CorePost decBool dn s₀.mem vis fe M eb ResH ([v.1], v.2) y a') := by
  rw [lamsE.arm1]
  have hL : (2 : Nat) ^ 62 = lamsFuel := rfl
  exact lams_ref p hp hi n hk F hF hn dn vis fe mode hs.mode4 (n + 1) (Nat.le_refl _) lamsFuel
    (by rw [← hL]; omega) d ty₁ body₁ ty₂ body₂ s₀.mem a₀ M eb hs.rel hs.eb_mode h1 hb1 h2 hb2
    (by omega)

include hp hi in
/-- **`defeq_lams` refines `defeqLams` at `lamsFuel`** (the twin's call in `quickDefEq`;
`defeqLams_ref`'s ok half). -/
@[refines ConRon.Arena.defeqLams]
theorem defeqLams_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d ty₁ body₁ ty₂ body₂ : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (h1 : HW ty₁) (hb1 : HW body₁) (h2 : HW ty₂) (hb2 : HW body₂) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "defeq_lams" [mode, vis, d, ty₁, body₁, ty₂, body₂]
      (defeqLams (decMode mode) (coreKnot (decMode mode) fe id F) lamsFuel d.toNat (decE ty₁)
        (decE body₁) (decE ty₂) (decE body₂)) decBool s₀ a₀ dn vis fe M eb :=
  CoreSpec.of_refE (w := fun (v : Word × Mem) => ([v.1], v.2))
    (defeqLams_specE p hp.lams (n + 1) s₀ mode vis d ty₁ body₁ ty₂ body₂)
    (defeqLams_ref p hp hi n hk F hF hn s₀ a₀ dn vis fe M eb mode d ty₁ body₁ ty₂ body₂ hs h1 hb1 h2
      hb2 hd)
    fun _ _ => ⟨rfl, by simp [decBool], id⟩

end loopRef

end L.Arena
