import ConAgua.Arena.IndPosSpec.CanonW
import ConAgua.Arena.IndPosSpec.SlRCongr
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# NoGoStep

`maClrK`, `maConstW`, `maConstW_eq`, `maClrK_some`, `noGoW`, `noG1` and the lemmas only they use.
-/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ### `mentions_any_const` -/

def maClrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => if rdW (m1.arr64 CTL) maSch.cs + 2 = 0 then none else some (r, mclearG maSch m1)

def maConstW (n : Nat) (m : Mem) (no nl e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) maSch.cs + 2 = 0 then none else maClrK (maGoW n (mclearG maSch m) no nl CWF e)

theorem maConstW_eq (n : Nat) (m : Mem) (no nl e : Word) (h0 : rdW (m.arr64 CTL) maSch.cs + 2 ≠ 0) :
    maConstW n m no nl e = maClrK (maGoW n (mclearG maSch m) no nl CWF e) := by simp [maConstW, h0]
theorem maClrK_some (r : Word) (m1 : Mem) (h0 : rdW (m1.arr64 CTL) maSch.cs + 2 ≠ 0) :
    maClrK (some (r, m1)) = some (r, mclearG maSch m1) := by simp [maClrK, h0]
attribute [ind_grind] maConstW_eq maClrK_some

/-! ## `nest_occ_go`, `nest_occ_node`: word models -/

mutual
def noGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lo, hi, f, h =>
    if f = 0 then none else noG1 n m no nl lo hi f h (eViewW m h)
def noG1 (n : Nat) (m : Mem) (no nl lo hi f h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 then some (0, m)
  else if v.headD 0 = 1 then
    some ((if lo ≤ v.tail.headD 0 ∧ v.tail.headD 0 < hi then 1 else 0), m)
  else if v.headD 0 = 3 then noC m (containsW n m no nl (v.tail.headD 0))
  else noG3 n m no nl lo hi f h v (mfindG noSch m h 0)
def noG3 (n : Nat) (m : Mem) (no nl lo hi f h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 NOM) (fr.tail.headD 0 * 4 + 3), m)
  else noG4 h (noNodeW n m no nl lo hi (f - 1) (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def noG4 (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => noG5 r (msetG noSch m1 h 0 r)
def noG5 (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 => some (r, m2)
def noC (m : Mem) : Option Word → Option (Word × Mem)
  | none => none
  | some r => some (r, m)
def noNodeW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lo, hi, f1, g, x, y, z =>
    if g = 4 ∨ g = 5 ∨ g = 6 then noB1 n no nl lo hi f1 y (noGoW n m no nl lo hi f1 x)
    else if g = 7 then noL1 n no nl lo hi f1 y z (noGoW n m no nl lo hi f1 x)
    else noGoW n m no nl lo hi f1 z
def noB1 (n : Nat) (no nl lo hi f1 y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => if b1 ≠ 0 then some (1, m1) else noGoW n m1 no nl lo hi f1 y
def noL1 (n : Nat) (no nl lo hi f1 y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => if b1 ≠ 0 then some (1, m1) else noL2 n no nl lo hi f1 z (noGoW n m1 no nl lo hi f1 y)
def noL2 (n : Nat) (no nl lo hi f1 z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b2, m2) => if b2 ≠ 0 then some (1, m2) else noGoW n m2 no nl lo hi f1 z
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (no nl lo hi f f1 h g x y z b1 b2 r : Word) (v fr : List Word)
theorem noGoW_abort (hf : f = 0) : noGoW (n + 1) m no nl lo hi f h = none := by simp [noGoW, hf]
theorem noGoW_view (hf : f ≠ 0) :
    noGoW (n + 1) m no nl lo hi f h = noG1 n m no nl lo hi f h (eViewW m h) := by simp [noGoW, hf]
theorem noG1_leaf (hv : v ≠ []) (hg : v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8) :
    noG1 n m no nl lo hi f h v = some (0, m) := by simp only [noG1]; rw [ite_eq_right hv, ite_eq_left hg]
theorem noG1_fvar (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h1 : v.headD 0 = 1) : noG1 n m no nl lo hi f h v =
      some ((if lo ≤ v.tail.headD 0 ∧ v.tail.headD 0 < hi then 1 else 0), m) := by
  simp only [noG1]; rw [ite_eq_right hv, ite_eq_right hg, ite_eq_left h1]
theorem noG1_const (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h1 : ¬ v.headD 0 = 1) (h3 : v.headD 0 = 3) :
    noG1 n m no nl lo hi f h v = noC m (containsW n m no nl (v.tail.headD 0)) := by
  simp only [noG1]; rw [ite_eq_right hv, ite_eq_right hg, ite_eq_right h1, ite_eq_left h3]
theorem noG1_node (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h1 : ¬ v.headD 0 = 1) (h3 : ¬ v.headD 0 = 3) :
    noG1 n m no nl lo hi f h v = noG3 n m no nl lo hi f h v (mfindG noSch m h 0) := by
  simp only [noG1]; rw [ite_eq_right hv, ite_eq_right hg, ite_eq_right h1, ite_eq_right h3]
theorem noG3_abort (hr : fr = []) : noG3 n m no nl lo hi f h v fr = none := by simp [noG3, hr]
theorem noG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    noG3 n m no nl lo hi f h v fr = some (rdW (m.arr64 NOM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [noG3]; rw [ite_eq_right hr, ite_eq_left hh]
theorem noG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    noG3 n m no nl lo hi f h v fr = noG4 h (noNodeW n m no nl lo hi (f - 1) (v.headD 0) (v.tail.headD 0)
      (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [noG3]; rw [ite_eq_right hr, ite_eq_right hh]
theorem noG4_some : noG4 h (some (r, m1)) = noG5 r (msetG noSch m1 h 0 r) := by rw [noG4]
theorem noG5_some : noG5 r (some m2) = some (r, m2) := by rw [noG5]
theorem noC_some : noC m (some r) = some (r, m) := by rw [noC]
theorem noNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) : noNodeW (n + 1) m no nl lo hi f1 g x y z =
    noB1 n no nl lo hi f1 y (noGoW n m no nl lo hi f1 x) := by
  simp only [noNodeW]; rw [ite_eq_left hg]
theorem noNodeW_let (hg : g = 7) : noNodeW (n + 1) m no nl lo hi f1 g x y z =
    noL1 n no nl lo hi f1 y z (noGoW n m no nl lo hi f1 x) := by
  have : ¬ (g = 4 ∨ g = 5 ∨ g = 6) := by
    intro e; rcases e with e | e | e <;> (rw [hg] at e; exact absurd e (by decide))
  simp only [noNodeW]; rw [ite_eq_right this, ite_eq_left hg]
theorem noNodeW_proj (hg2 : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (hg3 : g ≠ 7) :
    noNodeW (n + 1) m no nl lo hi f1 g x y z = noGoW n m no nl lo hi f1 z := by
  simp only [noNodeW]; rw [ite_eq_right hg2, ite_eq_right hg3]
theorem noB1_some : noB1 n no nl lo hi f1 y (some (b1, m1)) =
    (if b1 ≠ 0 then some (1, m1) else noGoW n m1 no nl lo hi f1 y) := by rw [noB1]
theorem noL1_some : noL1 n no nl lo hi f1 y z (some (b1, m1)) =
    (if b1 ≠ 0 then some (1, m1) else noL2 n no nl lo hi f1 z (noGoW n m1 no nl lo hi f1 y)) := by rw [noL1]
theorem noL2_some : noL2 n no nl lo hi f1 z (some (b2, m2)) =
    (if b2 ≠ 0 then some (1, m2) else noGoW n m2 no nl lo hi f1 z) := by rw [noL2]
end arms

attribute [ind_grind] noGoW_abort noGoW_view noG1_leaf noG1_fvar noG1_const noG1_node
  noG3_abort noG3_hit noG3_miss noG4_some noG5_some noC_some noNodeW_bin noNodeW_let noNodeW_proj
  noB1_some noL1_some noL2_some

section spec
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hc : p.lookup "sl_contains" = some slContains)
  (hf : p.lookup "no_find" = some (memoFindG noSch)) (hput : p.lookup "no_put" = some (memoPutG noSch))
  (hgo : p.lookup "nest_occ_go" = some nestOccGo)
  (hnode : p.lookup "nest_occ_node" = some nestOccNode)

def NoGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl lo hi f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_occ_go" [no, nl, lo, hi, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ noGoW n s₀.mem no nl lo hi f h = some (r.headD 0, s'.mem); ⊤⦄

def NoNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl lo hi f1 g x y z : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_occ_node" [no, nl, lo, hi, f1, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ noNodeW n s₀.mem no nl lo hi f1 g x y z = some (r.headD 0, s'.mem); ⊤⦄

include hv hc hf hput hgo in
theorem noGo_step (n : Nat) (ih : NoNodeSpec p n) : NoGoSpec p (n + 1) := by
  unfold NoNodeSpec at ih
  intro s₀ no nl lo hi f h
  simp only [invoke_eq _ hgo, callFn, nestOccGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p hv n, slContains_spec p hc n, memoFindG_spec noSch p _ hf n,
      memoPutG_spec noSch p _ hput n, ih] <;> finish (gen := 20)

include hnode in
theorem noNode_step (n : Nat) (ih : NoGoSpec p n) : NoNodeSpec p (n + 1) := by
  unfold NoGoSpec at ih
  intro s₀ no nl lo hi f1 g x y z
  simp only [invoke_eq _ hnode, callFn, nestOccNode]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      ih] <;> finish (gen := 20)

include hv hc hf hput hgo hnode in
theorem noGo_spec (n : Nat) : NoGoSpec p n ∧ NoNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ no nl lo hi f h; rw [invoke_eq _ hgo]; simp only [callFn, nestOccGo]; vcgen [exec] <;> grind
    · intro s₀ no nl lo hi f1 g x y z; rw [invoke_eq _ hnode]; simp only [callFn, nestOccNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨noGo_step p hv hc hf hput hgo n ih.2, noNode_step p hnode n ih.1⟩

end spec

def noArm (names : List NIdx) (lo hi : Nat) (memo : Std.HashMap EIdx Bool) (fuel : Nat) :
    ENodeView → AM (Bool × Std.HashMap EIdx Bool)
  | .app f a => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel f
    if b then pure (true, m) else ConRon.Arena.nestOccGo names lo hi m fuel a
  | .lam ty body => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel ty
    if b then pure (true, m) else ConRon.Arena.nestOccGo names lo hi m fuel body
  | .forallE ty body => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel ty
    if b then pure (true, m) else ConRon.Arena.nestOccGo names lo hi m fuel body
  | .letE ty val body => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel ty
    if b then pure (true, m) else do
      let (b2, m2) ← ConRon.Arena.nestOccGo names lo hi m fuel val
      if b2 then pure (true, m2) else ConRon.Arena.nestOccGo names lo hi m2 fuel body
  | .proj _ _ sub => ConRon.Arena.nestOccGo names lo hi memo fuel sub
  | _ => pure (false, memo)

/-- The twin's arm for a non-leaf view, with the memo insertion each branch makes. -/
def noArmI (names : List NIdx) (lo hi : Nat) (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx) :
    ENodeView → AM (Bool × Std.HashMap EIdx Bool)
  | .app f a => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel f
    if b then pure (true, m.insert h true) else do
      let (b2, m2) ← ConRon.Arena.nestOccGo names lo hi m fuel a
      pure (b2, m2.insert h b2)
  | .lam ty body => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel ty
    if b then pure (true, m.insert h true) else do
      let (b2, m2) ← ConRon.Arena.nestOccGo names lo hi m fuel body
      pure (b2, m2.insert h b2)
  | .forallE ty body => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel ty
    if b then pure (true, m.insert h true) else do
      let (b2, m2) ← ConRon.Arena.nestOccGo names lo hi m fuel body
      pure (b2, m2.insert h b2)
  | .letE ty val body => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel ty
    if b then pure (true, m.insert h true) else do
      let (b2, m2) ← ConRon.Arena.nestOccGo names lo hi m fuel val
      if b2 then pure (true, m2.insert h true) else do
        let (b3, m3) ← ConRon.Arena.nestOccGo names lo hi m2 fuel body
        pure (b3, m3.insert h b3)
  | .proj _ _ sub => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel sub
    pure (b, m.insert h b)
  | _ => pure (false, memo.insert h false)

def NodeVo : ENodeView → Prop
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => True
  | _ => False

theorem nestOccGo_succ' (names : List NIdx) (lo hi : Nat) (memo : Std.HashMap EIdx Bool) (fuel : Nat)
    (h : EIdx) :
    ConRon.Arena.nestOccGo names lo hi memo (fuel + 1) h = (do
      let v ← view h
      match v with
      | .bvar _ => pure (false, memo)
      | .sort _ => pure (false, memo)
      | .lit _ => pure (false, memo)
      | .fvar i _ => pure (decide (lo ≤ i) && decide (i < hi), memo)
      | .const n _ => pure (names.contains n, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => noArmI names lo hi memo fuel h v) := by
  rw [ConRon.Arena.nestOccGo.eq_2]
  congr 1

theorem noTwin_node (names : List NIdx) (lo hi : Nat) (memo : Std.HashMap EIdx Bool) (fuel : Nat)
    (h : EIdx) (a : AState) (v : ENodeView) (hv : a.store.view h = some v) (hnv : NodeVo v) :
    (ConRon.Arena.nestOccGo names lo hi memo (fuel + 1) h).run a =
      ((match memo[h]? with
        | some r => pure (r, memo)
        | none => noArmI names lo hi memo fuel h v : AM (Bool × Std.HashMap EIdx Bool)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | (rw [ConRon.Arena.nestOccGo.eq_2, StateT.run_bind, view_run _ a _ hv, except_ok_bind]; rfl)

theorem noArmI_eq (names : List NIdx) (lo hi : Nat) (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx)
    (v : ENodeView) (hnv : NodeVo v) :
    noArmI names lo hi memo fuel h v = (do
      let (r, m) ← noArm names lo hi memo fuel v
      pure (r, m.insert h r) : AM (Bool × Std.HashMap EIdx Bool)) := by
  cases v with
  | letE ty val body =>
    simp only [noArmI, noArm, bind_assoc]
    congr 1; funext x
    split
    · simp
    · simp only [bind_assoc]
      congr 1; funext y
      split <;> simp
  | bvar _ => exact False.elim hnv
  | sort _ => exact False.elim hnv
  | lit _ => exact False.elim hnv
  | const _ _ => exact False.elim hnv
  | fvar _ _ => exact False.elim hnv
  | proj _ _ _ => simp [noArmI, noArm]
  | app f a =>
    simp only [noArmI, noArm, bind_assoc]
    congr 1; funext x
    split <;> simp
  | lam f a =>
    simp only [noArmI, noArm, bind_assoc]
    congr 1; funext x
    split <;> simp
  | forallE f a =>
    simp only [noArmI, noArm, bind_assoc]
    congr 1; funext x
    split <;> simp

/-! ## Memo frames (lane `indproofs2`, helper `posmemo`)

`MFr S T m m'`: `m'` differs from `m` only outside the stage's per-call memo region (arrays
201‥208, `CTL[202‥219]`), except the memo arrays `S` and control words `T`. The memo relations
of the positivity check read only their own array and stamp word, so each survives an `MFr`
that leaves those out (`noMR_mfr`, `rpMR_mfr`, …). -/

def MFr (S : List ArrId) (T : List Word) (m m' : Mem) : Prop :=
  ∃ (A : List ArrId) (C : List Word), MemFrame A C m m' ∧ (∀ b ∈ A, b < 201 ∨ 208 < b ∨ b ∈ S) ∧
    (∀ x ∈ C, x.toNat < 202 ∨ 219 < x.toNat ∨ x ∈ T)

theorem MFr.refl (S : List ArrId) (T : List Word) (m : Mem) : MFr S T m m :=
  ⟨[], [], MemFrame.refl _ _ _, by simp, by simp⟩

theorem MFr.trans {S : List ArrId} {T : List Word} {m₁ m₂ m₃ : Mem} (h₁ : MFr S T m₁ m₂) (h₂ : MFr S T m₂ m₃) :
    MFr S T m₁ m₃ := by
  obtain ⟨A₁, C₁, f₁, a₁, c₁⟩ := h₁
  obtain ⟨A₂, C₂, f₂, a₂, c₂⟩ := h₂
  refine ⟨A₁ ++ A₂, C₁ ++ C₂, (f₁.mono (fun b hb => List.mem_append_left _ hb) (fun x hx => List.mem_append_left _ hx)).trans
    (f₂.mono (fun b hb => List.mem_append_right _ hb) (fun x hx => List.mem_append_right _ hx)), ?_, ?_⟩
  · intro b hb; rcases List.mem_append.mp hb with h | h; exact a₁ b h; exact a₂ b h
  · intro x hx; rcases List.mem_append.mp hx with h | h; exact c₁ x h; exact c₂ x h

theorem MFr.mono {S S' : List ArrId} {T T' : List Word} {m m' : Mem} (h : MFr S T m m')
    (hS : ∀ b ∈ S, b ∈ S') (hT : ∀ x ∈ T, x ∈ T') : MFr S' T' m m' := by
  obtain ⟨A, C, f, a, c⟩ := h
  refine ⟨A, C, f, fun b hb => ?_, fun x hx => ?_⟩
  · rcases a b hb with h | h | h; exact .inl h; exact .inr (.inl h); exact .inr (.inr (hS b h))
  · rcases c x hx with h | h | h; exact .inl h; exact .inr (.inl h); exact .inr (.inr (hT x h))

/-- `mfr_auto h [f₁, …]` proves `MFr S T m m'` from `h : model = some (r, m')` once the model's
continuations are unfolded at `h`: it splits `h`'s `match`es and `if`s in evaluation order, and at
each callee hypothesis `callee … = some (x, m₁)` steps the frame by the first `fᵢ` that applies
to it (an `MFr [] []` frame is weakened to any `S T`). -/
syntax "mfr_auto" ident "[" term,* "]" : tactic
macro_rules
  | `(tactic| mfr_auto $h [$ts,*]) => `(tactic|
    repeat' (first
      | with_reducible exact MFr.refl _ _ _
      | (simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident; rw [← ($h).2]; exact MFr.refl _ _ _)
      | (simp only [Option.some.injEq] at $h:ident; subst $h:ident; exact MFr.refl _ _ _)
      | (simp only [reduceCtorEq] at $h:ident; done)
      | (first $[| refine MFr.trans ($ts (by with_reducible assumption)) ?_]*)
      | (first $[| refine MFr.trans (MFr.up ($ts (by with_reducible assumption))) ?_]*)
      | (first $[| refine MFr.trans (MFr.mono ($ts (by with_reducible assumption)) (by simp) (by simp)) ?_]*)
      | split at $h:ident))

theorem MFr.of_frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 201 ∨ 208 < b) (hC : ∀ x ∈ C, x.toNat < 202 ∨ 219 < x.toNat) : MFr [] [] m m' :=
  ⟨A, C, hf, fun b hb => by rcases hA b hb with h | h; exact .inl h; exact .inr (.inl h),
    fun x hx => by rcases hC x hx with h | h; exact .inl h; exact .inr (.inl h)⟩

theorem MFr.of_iw {m m' : Mem} (h : MemFrame [IW] [200] m m') : MFr [] [] m m' :=
  MFr.of_frame h (by simp [IW]) (by simp)

theorem MFr.set_iw (m : Mem) (x v : Word) : MFr [] [] m (m.set64 IW x v) := MFr.of_iw (set64IW_frame m x v)

/-- `instantiate1_fast` writes the expression tables and its memo only (`instA`, `instC`). -/
theorem MFr.ofI1F {m m' : Mem} {args r : List Word} (h : i1F m args = some (r, m')) : MFr [] [] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact MFr.of_frame (run_memFrame i1Prog_closed (List.mem_cons_self ..) (run_of_callW hc)).1
    (fun b hb => by have := instA_lt b hb; simp only [ArrId] at this ⊢; omega)
    (fun x hx => .inl (Nat.lt_trans (instC_lt x hx) (by decide)))

/-- `mk_app_n_f` writes the stack, its top and the app tables (`mknF_frame`). -/
theorem MFr.ofMknF {m m' : Mem} {args r : List Word} (h : mknF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (mknF_frame h) (by simp [tier1, tierOff, SPN, AREC, ASLOT, ADER]) (by simp)

/-- The memo array `S.arr` and its stamp word survive an `MFr` that leaves them out. -/
theorem MFr.memo {S0 : List ArrId} {T0 : List Word} {m m' : Mem} (h : MFr S0 T0 m m') (b : ArrId) (x : Word)
    (hb : 201 ≤ b ∧ b ≤ 208) (hx : 202 ≤ x.toNat ∧ x.toNat ≤ 219) (hbS : b ∉ S0) (hxT : x ∉ T0) :
    ∃ (A : List ArrId) (C : List Word), MemFrame A C m m' ∧ b ∉ A ∧ x ∉ C := by
  obtain ⟨A, C, f, a, c⟩ := h
  refine ⟨A, C, f, fun hm => ?_, fun hm => ?_⟩
  · rcases a b hm with h | h | h
    · exact absurd hb.1 (Nat.not_le.mpr h)
    · exact absurd hb.2 (Nat.not_le.mpr h)
    · exact hbS h
  · rcases c x hm with h | h | h
    · omega
    · omega
    · exact hxT h

theorem noFrame_arena {m m' : Mem} {a : AState} (hf : MemFrame [NOM] [205] m m') (hR : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame (fun b hb => by simp at hb; subst hb; simp [arenaArrs, storeArrs, memoArrs, NOM])
    (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf hR

theorem noFrame_iw {m m' : Mem} (hf : MemFrame [NOM] [205] m m') : m'.arr64 IW = m.arr64 IW :=
  hf.1 IW (by decide) (by decide)

abbrev noMR (m : Mem) (mp : Std.HashMap EIdx Bool) : Prop :=
  MemoRG noSch bmKey (fun w : Word => w != 0) m mp

def NoGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (no nl lo hi f h r : Word) (ws : List Word) (mp : Std.HashMap EIdx Bool),
    noGoW n m no nl lo hi f h = some (r, m') → ArenaR m a → H h → SlR m no nl ws →
    (∀ w ∈ ws, w.toNat < 2 ^ 32) → noMR m mp →
    ∃ b mp', (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f.toNat
        (decE h)).run a = .ok ((b, mp'), a) ∧ (r != 0) = b ∧ noMR m' mp' ∧ MemFrame [NOM] [205] m m'

theorem noNodeBin_ok (n : Nat) (ih : NoGoOK n) (m m' : Mem) (a : AState) (no nl lo hi f1 g x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hg : g = 4 ∨ g = 5 ∨ g = 6) (hx : H x) (hy : H y)
    (hn : noNodeW (n + 1) m no nl lo hi f1 g x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : noMR m mp) :
    ∃ b mp', (do
        let (b, m) ← ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f1.toNat (decE x)
        if b then pure (true, m) else
          ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat m f1.toNat (decE y) :
          AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ noMR m' mp' ∧ MemFrame [NOM] [205] m m' := by
  rw [noNodeW_bin n m no nl lo hi f1 g x y z hg] at hn
  rcases h1 : noGoW n m no nl lo hi f1 x with _ | ⟨b1w, m1⟩ <;> rw [h1] at hn; · simp [noB1] at hn
  rw [noB1_some] at hn
  obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a no nl lo hi f1 x b1w ws mp h1 hA hx hws hwlt hM
  by_cases e1 : b1w ≠ 0
  · rw [ite_eq_left e1] at hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    have hc1 : c1 = true := by rw [← hb1]; simpa using e1
    refine ⟨true, mp1, ?_, by simp, hM1, hf1⟩
    simp only [StateT.run_bind, hr1, except_ok_bind, hc1, ite_true]
    rfl
  · rw [ite_eq_right e1] at hn
    have hc1 : c1 = false := by rw [← hb1]; simpa using e1
    obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m' a no nl lo hi f1 y r ws mp1 hn (noFrame_arena hf1 hA) hy
      (slR_congr (noFrame_iw hf1) hws) hwlt hM1
    refine ⟨c2, mp2, ?_, hb2, hM2, hf1.trans hf2⟩
    simp only [StateT.run_bind, hr1, except_ok_bind, hc1]
    simpa using hr2

theorem noNodeLet_ok (n : Nat) (ih : NoGoOK n) (m m' : Mem) (a : AState) (no nl lo hi f1 x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hx : H x) (hy : H y) (hz : H z)
    (hn : noNodeW (n + 1) m no nl lo hi f1 7 x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : noMR m mp) :
    ∃ b mp', (do
        let (b, m) ← ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f1.toNat (decE x)
        if b then pure (true, m) else do
          let (b2, m2) ← ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat m f1.toNat (decE y)
          if b2 then pure (true, m2) else
            ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat m2 f1.toNat (decE z) :
          AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ noMR m' mp' ∧ MemFrame [NOM] [205] m m' := by
  rw [noNodeW_let n m no nl lo hi f1 7 x y z rfl] at hn
  rcases h1 : noGoW n m no nl lo hi f1 x with _ | ⟨b1w, m1⟩ <;> rw [h1] at hn; · simp [noL1] at hn
  rw [noL1_some] at hn
  obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a no nl lo hi f1 x b1w ws mp h1 hA hx hws hwlt hM
  by_cases e1 : b1w ≠ 0
  · rw [ite_eq_left e1] at hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    have hc1 : c1 = true := by rw [← hb1]; simpa using e1
    refine ⟨true, mp1, ?_, by simp, hM1, hf1⟩
    simp only [StateT.run_bind, hr1, except_ok_bind, hc1, ite_true]
    rfl
  · rw [ite_eq_right e1] at hn
    have hc1 : c1 = false := by rw [← hb1]; simpa using e1
    rcases h2 : noGoW n m1 no nl lo hi f1 y with _ | ⟨b2w, m2⟩ <;> rw [h2] at hn; · simp [noL2] at hn
    rw [noL2_some] at hn
    have hA1 := noFrame_arena hf1 hA
    have hws1 := slR_congr (noFrame_iw hf1) hws
    obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m2 a no nl lo hi f1 y b2w ws mp1 h2 hA1 hy hws1 hwlt hM1
    by_cases e2 : b2w ≠ 0
    · rw [ite_eq_left e2] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      have hc2 : c2 = true := by rw [← hb2]; simpa using e2
      refine ⟨true, mp2, ?_, by simp, hM2, hf1.trans hf2⟩
      simp only [StateT.run_bind, hr1, except_ok_bind, hc1, Bool.false_eq_true, ↓reduceIte, hr2, hc2]
      rfl
    · rw [ite_eq_right e2] at hn
      have hc2 : c2 = false := by rw [← hb2]; simpa using e2
      obtain ⟨c3, mp3, hr3, hb3, hM3, hf3⟩ := ih m2 m' a no nl lo hi f1 z r ws mp2 hn
        (noFrame_arena (hf1.trans hf2) hA) hz (slR_congr (noFrame_iw (hf1.trans hf2)) hws) hwlt hM2
      refine ⟨c3, mp3, ?_, hb3, hM3, (hf1.trans hf2).trans hf3⟩
      simp only [StateT.run_bind, hr1, except_ok_bind, hc1, Bool.false_eq_true, ↓reduceIte, hr2, hc2]
      simpa using hr3

theorem noNodeProj_ok (n : Nat) (ih : NoGoOK n) (m m' : Mem) (a : AState) (no nl lo hi f1 x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hz : H z)
    (hn : noNodeW (n + 1) m no nl lo hi f1 9 x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : noMR m mp) :
    ∃ b mp', (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f1.toNat
        (decE z)).run a = .ok ((b, mp'), a) ∧ (r != 0) = b ∧ noMR m' mp' ∧ MemFrame [NOM] [205] m m' := by
  rw [noNodeW_proj n m no nl lo hi f1 9 x y z (by decide) (by decide)] at hn
  exact ih m m' a no nl lo hi f1 z r ws mp hn hA hz hws hwlt hM

theorem noNode_arm (k : Nat) (ih : NoGoOK k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVo v) (m m' : Mem) (a : AState) (no nl lo hi f1 r : Word) (ws : List Word)
    (mp : Std.HashMap EIdx Bool)
    (hn : noNodeW (k + 1) m no nl lo hi f1 (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0) = some (r, m'))
    (hA : ArenaR m a) (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : noMR m mp) :
    ∃ b mp', (noArm (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f1.toNat v).run a =
        .ok ((b, mp'), a) ∧ (r != 0) = b ∧ noMR m' mp' ∧ MemFrame [NOM] [205] m m' := by
  cases v with
  | app f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := noNodeBin_ok k ih m m' a no nl lo hi f1 _ _ _ _ r ws mp (Or.inl hg) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [noArm]; exact this
  | lam f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := noNodeBin_ok k ih m m' a no nl lo hi f1 _ _ _ _ r ws mp (Or.inr (Or.inl hg)) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [noArm]; exact this
  | forallE f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := noNodeBin_ok k ih m m' a no nl lo hi f1 _ _ _ _ r ws mp (Or.inr (Or.inr hg)) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [noArm]; exact this
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := noNodeLet_ok k ih m m' a no nl lo hi f1 _ _ _ r ws mp hx hy hz hn hA hws hwlt hM
    rw [hdx, hdy, hdz] at this
    simp only [noArm]; exact this
  | proj s i e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, -, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := noNodeProj_ok k ih m m' a no nl lo hi f1 _ _ _ r ws mp hz hn hA hws hwlt hM
    rw [hdz] at this
    simp only [noArm]; exact this
  | bvar _ => exact False.elim hnv
  | sort _ => exact False.elim hnv
  | const _ _ => exact False.elim hnv
  | lit _ => exact False.elim hnv
  | fvar _ _ => exact False.elim hnv

theorem noSch_wf : noSch.WF := ⟨by decide, by decide⟩

theorem noGo_nodeCase (j : Nat) (ih : ∀ k, k + 1 < j + 1 → NoGoOK k) (m m' : Mem) (a : AState)
    (no nl lo hi f h r : Word) (ws : List Word) (mp : Std.HashMap EIdx Bool) (F : Nat)
    (hF : f.toNat = F + 1) (hf0 : f ≠ 0) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVo v) (hv : a.store.view (decE h) = some v) (hvl : vl ≠ [])
    (hgs : vl.headD 0 = 4 ∨ vl.headD 0 = 5 ∨ vl.headD 0 = 6 ∨ vl.headD 0 = 7 ∨ vl.headD 0 = 9)
    (hb : noG1 j m no nl lo hi f h vl = some (r, m')) (hA : ArenaR m a) (hh : H h)
    (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : noMR m mp) :
    ∃ b mp', (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp (F + 1)
        (decE h)).run a = .ok ((b, mp'), a) ∧ (r != 0) = b ∧ noMR m' mp' ∧ MemFrame [NOM] [205] m m' := by
  have hnl : ¬ (vl.headD 0 = 0 ∨ vl.headD 0 = 2 ∨ vl.headD 0 = 8) := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  have hn1 : ¬ vl.headD 0 = 1 := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  have hn3 : ¬ vl.headD 0 = 3 := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  rw [noG1_node j m no nl lo hi f h vl hvl hnl hn1 hn3] at hb
  rw [noTwin_node _ _ _ _ _ _ a v hv hnv]
  by_cases hfr : mfindG noSch m h 0 = []
  · rw [noG3_abort j m no nl lo hi f h vl _ hfr] at hb; simp at hb
  by_cases hhit : (mfindG noSch m h 0).headD 0 ≠ 0
  · rw [noG3_hit j m no nl lo hi f h vl _ hfr hhit] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    have hmem := memoRG_hit noSch bmKey (fun w : Word => w != 0) m mp hM h 0 hfr hhit ⟨hh, rfl⟩
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmem
    refine ⟨_, mp, ?_, rfl, hM, MemFrame.refl _ _ _⟩
    simp only [hmem]; rfl
  · rw [noG3_miss j m no nl lo hi f h vl _ hfr hhit] at hb
    have hmiss := memoRG_miss noSch bmKey (fun w : Word => w != 0) m mp hM h 0 ⟨hh, rfl⟩ hfr (by simpa using hhit)
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmiss
    cases j with
    | zero => simp [noNodeW, noG4] at hb
    | succ k =>
      rcases hnode : noNodeW (k + 1) m no nl lo hi (f - 1) (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
          (vl.tail.tail.tail.headD 0) with _ | ⟨rn, m1⟩; · rw [hnode] at hb; simp [noG4] at hb
      rw [hnode, noG4_some] at hb
      rcases hset : msetG noSch m1 h 0 rn with _ | m2 <;> rw [hset] at hb; · simp [noG5] at hb
      rw [noG5_some] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have hF1 : (f - 1).toNat = F := by rw [toNat_sub_one' hf0, hF]; rfl
      obtain ⟨bb, mp1, hr1, hbb, hM1, hfr1⟩ := noNode_arm k (ih k (by omega)) vl v hvr hnv m m1 a no nl lo hi
        (f - 1) rn ws mp hnode hA hws hwlt hM
      rw [hF1] at hr1
      have hset' := memoRG_set noSch noSch_wf bmKey (fun w : Word => w != 0) m1 mp1 hM1 h 0 rn ⟨hh, rfl⟩ m2 hset
      have hfs : MemFrame [NOM] [205] m1 m2 := msetG_frame noSch noSch_wf m1 m2 h 0 rn hset
      refine ⟨bb, mp1.insert (decE h) bb, ?_, hbb, ?_, hfr1.trans hfs⟩
      · rw [hmiss]
        simp only [noArmI_eq _ _ _ _ _ _ v hnv, StateT.run_bind, hr1, except_ok_bind]
        rfl
      · rw [← hbb]; exact hset'

theorem noGo_step_ok (j : Nat) (ih : ∀ k, k + 1 < j + 1 → NoGoOK k) : NoGoOK (j + 1) := by
  intro m m' a no nl lo hi f h r ws mp hb hA hh hws hwlt hM
  by_cases hf0 : f = 0
  · rw [noGoW_abort j m no nl lo hi f h hf0] at hb; simp at hb
  rw [noGoW_view j m no nl lo hi f h hf0] at hb
  obtain ⟨F, hF⟩ : ∃ F, f.toNat = F + 1 := ⟨f.toNat - 1, by have := toNat_ne_zero' hf0; omega⟩
  cases hvl : eViewW m h with
  | nil => rw [hvl] at hb; simp [noG1] at hb
  | cons g vt =>
    have hne : eViewW m h ≠ [] := by rw [hvl]; simp
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA h hne
    rw [hvl] at hvr hb
    cases v with
    | bvar i =>
      rw [hF, nestOccGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 0 := by simpa [ViewR] using hvr.1
      rw [noG1_leaf j m no nl lo hi f h _ (by simp) (Or.inl hg0)] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | sort u =>
      rw [hF, nestOccGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 2 := by simpa [ViewR] using hvr.1
      rw [noG1_leaf j m no nl lo hi f h _ (by simp) (Or.inr (Or.inl hg0))] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | lit l =>
      rw [hF, nestOccGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 8 := by simpa [ViewR] using hvr
      rw [noG1_leaf j m no nl lo hi f h _ (by simp) (Or.inr (Or.inr hg0))] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | const nn us =>
      rw [hF, nestOccGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      simp only [ViewR, getD1_eq'] at hvr
      obtain ⟨hg3, hx, hdx, -⟩ := hvr
      have hg3' : (g :: vt).headD 0 = 3 := hg3
      rw [noG1_const j m no nl lo hi f h _ (by simp) (by rw [hg3']; decide) (by rw [hg3']; decide) hg3'] at hb
      rcases hc : containsW j m no nl ((g :: vt).tail.headD 0) with _ | rc <;> rw [hc] at hb; · simp [noC] at hb
      rw [noC_some] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have hcv := containsW_ok j _ _ _ _ _ _ hws hc
      refine ⟨(ws.map (fun w => (decI w : NIdx))).contains nn, mp, ?_, ?_, hM, MemFrame.refl _ _ _⟩
      · rfl
      · rw [hcv, ← hdx, contains_decI ws _ hwlt hx]
        generalize ws.contains _ = bc
        cases bc <;> simp
    | fvar i ty =>
      rw [hF, nestOccGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      simp only [ViewR, getD1_eq'] at hvr
      obtain ⟨hg1, hix, -⟩ := hvr
      have hg1' : (g :: vt).headD 0 = 1 := hg1
      rw [noG1_fvar j m no nl lo hi f h _ (by simp) (by rw [hg1']; decide) hg1'] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      refine ⟨decide (lo.toNat ≤ i) && decide (i < hi.toNat), mp, rfl, ?_, hM, MemFrame.refl _ _ _⟩
      generalize (g :: vt).tail.headD 0 = x at hix ⊢
      subst hix
      simp only [← UInt64.le_iff_toNat_le, ← UInt64.lt_iff_toNat_lt]
      by_cases c1 : lo ≤ x <;> by_cases c2 : x < hi <;> simp [c1, c2]
    | app f' x' => rw [hF]; exact noGo_nodeCase j ih m m' a no nl lo hi f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inl hvr.1) hb hA hh hws hwlt hM
    | lam f' x' => rw [hF]; exact noGo_nodeCase j ih m m' a no nl lo hi f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inl hvr.1)) hb hA hh hws hwlt hM
    | forallE f' x' => rw [hF]; exact noGo_nodeCase j ih m m' a no nl lo hi f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inl hvr.1))) hb hA hh hws hwlt hM
    | letE t v' b' => rw [hF]; exact noGo_nodeCase j ih m m' a no nl lo hi f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inr (Or.inl hvr.1)))) hb hA hh hws hwlt hM
    | proj s i e => rw [hF]; exact noGo_nodeCase j ih m m' a no nl lo hi f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inr (Or.inr hvr.1)))) hb hA hh hws hwlt hM

theorem noGoOK (n : Nat) : NoGoOK n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro m m' a no nl lo hi f h r ws mp hb; simp [noGoW] at hb
    | succ j => exact noGo_step_ok j (fun k hk => ih k (by omega))

/-! ### `nest_occ` -/

def noClrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => if rdW (m1.arr64 CTL) noSch.cs + 2 = 0 then none else some (r, mclearG noSch m1)

def noConstW (n : Nat) (m : Mem) (no nl lo hi e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) noSch.cs + 2 = 0 then none else noClrK (noGoW n (mclearG noSch m) no nl lo hi CWF e)

theorem noConstW_eq (n : Nat) (m : Mem) (no nl lo hi e : Word) (h0 : rdW (m.arr64 CTL) noSch.cs + 2 ≠ 0) :
    noConstW n m no nl lo hi e = noClrK (noGoW n (mclearG noSch m) no nl lo hi CWF e) := by simp [noConstW, h0]
theorem noClrK_some (r : Word) (m1 : Mem) (h0 : rdW (m1.arr64 CTL) noSch.cs + 2 ≠ 0) :
    noClrK (some (r, m1)) = some (r, mclearG noSch m1) := by simp [noClrK, h0]
attribute [ind_grind] noConstW_eq noClrK_some

/-! ## `member_idx_at` -/

def memK (n : Nat) (m : Mem) (no nl lvls : Word) (v : List Word) : Option (List Word × Mem) :=
  if v = [] then none
  else if v.tail.tail.headD 0 ≠ lvls then some ([0, 0], m)
  else match findW n m no nl (v.tail.headD 0) with
    | none => none
    | some r => some ([r.headD 0, r.tail.headD 0], m)

theorem memK_miss (n : Nat) (m : Mem) (no nl lvls : Word) (v : List Word) (h : v ≠ [])
    (h2 : v.tail.tail.headD 0 ≠ lvls) : memK n m no nl lvls v = some ([0, 0], m) := by
  simp only [memK]; rw [ite_eq_right h, ite_eq_left h2]
theorem memK_find (n : Nat) (m : Mem) (no nl lvls : Word) (v : List Word) (h : v ≠ [])
    (h2 : ¬ v.tail.tail.headD 0 ≠ lvls) : memK n m no nl lvls v =
      (match findW n m no nl (v.tail.headD 0) with
        | none => none
        | some r => some ([r.headD 0, r.tail.headD 0], m)) := by
  simp only [memK]; rw [ite_eq_right h, ite_eq_right h2]
attribute [ind_grind] memK_miss memK_find

/-- `(ok, idx)` against an `Option Nat`. -/
def MemIdxOut (r : List Word) : Option Nat → Prop
  | none => r = [0, 0]
  | some i => r = [1, UInt64.ofNat i]

end L.Ind

end
