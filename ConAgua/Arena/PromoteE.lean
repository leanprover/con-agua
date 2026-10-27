import ConAgua.Arena.PromoteL
import ConAgua.Arena.IndView
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# `promote_e`, `pe_arm` and the arms: models and specs

As `PromoteN.lean`. `pe_arm` views the expression with `e_view` (`eViewW`, `IndView.lean`) and
dispatches on the tag; the compound arms are `pe_const`, `pe_app`, `pe_lam`, `pe_forall`,
`pe_let`, `pe_proj` (children in the twin's order, then the persistent interning), `pe_lit`
re-interns the literal's pool slice.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind (eViewW eView_spec)

/-! ## The models -/

/-- **The model of `promote_e(f, h)`.** -/
def peW (p : Prog) (n : Nat) (m : Mem) (f h : Word) : Option (Word × Mem) :=
  if f = 0 then none
  else if tierW h = 0 then some (h, m)
  else if mfindG peSch m h 0 = [] then none
  else if (mfindG peSch m h 0).headD 0 ≠ 0 then
    some (mvG peSch m ((mfindG peSch m h 0).tail.headD 0), m)
  else memoK peSch h (callW p n "pe_arm" [f - 1, h] m)

/-- The literal record's words. -/
abbrev ltK (m : Mem) (h : Word) : Word := tfld m LIT (tierW h) (idxW h) 0
abbrev ltO (m : Mem) (h : Word) : Word := tfld m LIT (tierW h) (idxW h) 1
abbrev ltL (m : Mem) (h : Word) : Word := tfld m LIT (tierW h) (idxW h) 2

/-- **The model of `pe_lit(h)`.** -/
def peLitW (p : Prog) (n : Nat) (m : Mem) (h : Word) : Option (Word × Mem) :=
  if ltK m h = 1 then hd1 (callW p n "pi_lit_str" [ltO m h, ltL m h] m)
  else hd1 (callW p n "pi_lit" [ltO m h, ltL m h] m)

/-- After the first of two children `x` (promoted by `g₁`), promote `b` by `g₂`, intern with `g`.
-/
def pe2K (p : Prog) (n : Nat) (g₂ g : FnName) (f b : Word) :
    Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => pl2K.pl2K₂ p n g (x.headD 0) (callW p n g₂ [f, b] m₁)

/-- **The model of a two-child arm** `pe_X(f, a, b)`: `g₁(f, a)`, `g₂(f, b)`, `g(x, y)`. -/
def pe2W (p : Prog) (n : Nat) (m : Mem) (g₁ g₂ g : FnName) (f a b : Word) : Option (Word × Mem) :=
  pe2K p n g₂ g f b (callW p n g₁ [f, a] m)

/-- `pe_let`'s continuations. -/
def pe3K (p : Prog) (n : Nat) (f v b : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => pe3K₂ p n f b (x.headD 0) (callW p n "promote_e" [f, v] m₁)
where
  pe3K₂ (p : Prog) (n : Nat) (f b x : Word) : Option (List Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => pe3K₃ p n x (y.headD 0) (callW p n "promote_e" [f, b] m₂)
  pe3K₃ (p : Prog) (n : Nat) (x y : Word) : Option (List Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => hd1 (callW p n "pi_let" [x, y, z.headD 0] m₃)

/-- **The model of `pe_let(f, a, b, c)`.** -/
def peLetW (p : Prog) (n : Nat) (m : Mem) (f a b c : Word) : Option (Word × Mem) :=
  pe3K p n f b c (callW p n "promote_e" [f, a] m)

/-- `pe_proj`'s continuations. -/
def pePjK (p : Prog) (n : Nat) (f i e : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => pePjK₂ p n i (x.headD 0) (callW p n "promote_e" [f, e] m₁)
where pePjK₂ (p : Prog) (n : Nat) (i x : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => hd1 (callW p n "pi_proj" [x, i, y.headD 0] m₂)

/-- **The model of `pe_proj(f, n, i, e)`.** -/
def peProjW (p : Prog) (n : Nat) (m : Mem) (f nm i e : Word) : Option (Word × Mem) :=
  pePjK p n f i e (callW p n "promote_n" [f, nm] m)

/-- `pe_arm`'s `fvar` continuation. -/
def peFvK (p : Prog) (n : Nat) (i : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => hd1 (callW p n "pi_fvar" [i, x.headD 0] m₁)

/-- The dispatch on `e_view`'s words `r`. -/
def peK (p : Prog) (n : Nat) (m : Mem) (f h : Word) (r : List Word) : Option (Word × Mem) :=
  if r.headD 0 = 0 then hd1 (callW p n "pi_bvar" [r.tail.headD 0] m)
  else if r.headD 0 = 1 then
    peFvK p n (r.tail.headD 0) (callW p n "promote_e" [f, r.tail.tail.headD 0] m)
  else if r.headD 0 = 2 then pl1K p n "pi_sort" (callW p n "promote_l" [f, r.tail.headD 0] m)
  else if r.headD 0 = 3 then hd1 (callW p n "pe_const" [f, r.tail.headD 0, r.tail.tail.headD 0] m)
  else if r.headD 0 = 4 then hd1 (callW p n "pe_app" [f, r.tail.headD 0, r.tail.tail.headD 0] m)
  else if r.headD 0 = 5 then hd1 (callW p n "pe_lam" [f, r.tail.headD 0, r.tail.tail.headD 0] m)
  else if r.headD 0 = 6 then
    hd1 (callW p n "pe_forall" [f, r.tail.headD 0, r.tail.tail.headD 0] m)
  else if r.headD 0 = 7 then
    hd1 (callW p n "pe_let" [f, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0] m)
  else if r.headD 0 = 8 then hd1 (callW p n "pe_lit" [h] m)
  else hd1 (callW p n "pe_proj" [f, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0] m)

/-- **The model of `pe_arm(f, h)`.** -/
def peArmW (p : Prog) (n : Nat) (m : Mem) (f h : Word) : Option (Word × Mem) :=
  if eViewW m h = [] then none else peK p n m f h (eViewW m h)

/-! ## Guarded equations -/

section eqs
variable (p : Prog) (n : Nat) (m m₁ m₂ : Mem) (f h a b c v i e x y : Word) (r q : List Word)
  (g g₂ : FnName)

theorem peW_pers (hf : f ≠ 0) (ht : tierW h = 0) : peW p n m f h = some (h, m) := by
  simp [peW, hf, ht]

theorem peW_hit (hf : f ≠ 0) (ht : tierW h ≠ 0) (h0 : mfindG peSch m h 0 ≠ [])
    (h1 : (mfindG peSch m h 0).headD 0 ≠ 0) :
    peW p n m f h = some (mvG peSch m ((mfindG peSch m h 0).tail.headD 0), m) := by
  unfold peW; rw [ite_eq_right hf, ite_eq_right ht, ite_eq_right h0, ite_eq_left h1]

theorem peW_miss (hf : f ≠ 0) (ht : tierW h ≠ 0) (h0 : mfindG peSch m h 0 ≠ [])
    (h1 : (mfindG peSch m h 0).headD 0 = 0) :
    peW p n m f h = memoK peSch h (callW p n "pe_arm" [f - 1, h] m) := by
  unfold peW; rw [ite_eq_right hf, ite_eq_right ht, ite_eq_right h0, ite_eq_right (fun h2 => h2 h1)]

theorem peArmW_eq (hne : eViewW m h ≠ []) : peArmW p n m f h = peK p n m f h (eViewW m h) := by
  unfold peArmW; rw [ite_eq_right hne]

theorem pe2K_some :
    pe2K p n g₂ g f b (some (q, m₁)) = pl2K.pl2K₂ p n g (q.headD 0) (callW p n g₂ [f, b] m₁) := rfl
theorem pe3K_some :
    pe3K p n f v b (some (q, m₁)) = pe3K.pe3K₂ p n f b (q.headD 0) (callW p n "promote_e" [f, v] m₁) :=
  rfl
theorem pe3K₂_some :
    pe3K.pe3K₂ p n f b x (some (q, m₂)) =
      pe3K.pe3K₃ p n x (q.headD 0) (callW p n "promote_e" [f, b] m₂) := rfl
theorem pe3K₃_some :
    pe3K.pe3K₃ p n x y (some (q, m₂)) = hd1 (callW p n "pi_let" [x, y, q.headD 0] m₂) := rfl
theorem pePjK_some :
    pePjK p n f i e (some (q, m₁)) = pePjK.pePjK₂ p n i (q.headD 0) (callW p n "promote_e" [f, e] m₁) :=
  rfl
theorem pePjK₂_some :
    pePjK.pePjK₂ p n i x (some (q, m₂)) = hd1 (callW p n "pi_proj" [x, i, q.headD 0] m₂) := rfl
theorem peFvK_some : peFvK p n i (some (q, m₁)) = hd1 (callW p n "pi_fvar" [i, q.headD 0] m₁) :=
  rfl

end eqs

/-! ## The specs -/

section specs
variable (p : Prog) (hp : PromoteProg p) (n : Nat) (s₀ : St)
include hp

theorem promoteE_spec (f h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_e" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ peW p n s₀.mem f h = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_e")]
  simp only [callFn, promoteEL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec peSch p _ (hp.get "pe_find") n, memoPutG_spec peSch p _ (hp.get "pe_put") n,
      callW_spec p n "pe_arm", evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    finish [peW_pers, peW_hit, peW_miss, memoK_some, mvG, tierW]

theorem peArm_spec (f h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pe_arm" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ peArmW p n s₀.mem f h = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pe_arm")]
  simp only [callFn, peArm]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      eView_spec p (hp.get "e_view") n, callW_spec p n "pi_bvar", callW_spec p n "promote_e",
      callW_spec p n "pi_fvar", callW_spec p n "promote_l", callW_spec p n "pi_sort",
      callW_spec p n "pe_const", callW_spec p n "pe_app", callW_spec p n "pe_lam",
      callW_spec p n "pe_forall", callW_spec p n "pe_let", callW_spec p n "pe_lit",
      callW_spec p n "pe_proj"] <;>
    finish [peArmW_eq, peK, peFvK_some, pl1K_some, hd1_some]

theorem peLit_spec (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pe_lit" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ peLitW p n s₀.mem h = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pe_lit")]
  simp only [callFn, peLit]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pi_lit_str", callW_spec p n "pi_lit", evalE_tld, tld, evalE_cnt, tcntM,
      evalE_tierE, evalE_idxE] <;>
    finish [peLitW, hd1_some, tierW, idxW]

theorem peConst_spec (f a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pe_const" [f, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      pe2W p n s₀.mem "promote_n" "promote_ls" "pi_const" f a b = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pe_const")]
  simp only [callFn, peConst]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "promote_n", callW_spec p n "promote_ls", callW_spec p n "pi_const"] <;>
    finish [pe2W, pe2K_some, pl2K₂_some, hd1_some]

set_option hygiene false in
/-- One two-child arm's spec. -/
local macro "pe2_spec " fn:term ", " d:ident : tactic => `(tactic| (
  rw [invoke_eq _ $fn]
  simp only [callFn, $d:ident]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec] <;>
    finish [pe2W, pe2K_some, pl2K₂_some, hd1_some]))

theorem peApp_spec (f a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pe_app" [f, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      pe2W p n s₀.mem "promote_e" "promote_e" "pi_app" f a b = some (r.headD 0, s'.mem); ⊤⦄ := by
  pe2_spec (hp.get "pe_app"), peApp

theorem peLam_spec (f a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pe_lam" [f, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      pe2W p n s₀.mem "promote_e" "promote_e" "pi_lam" f a b = some (r.headD 0, s'.mem); ⊤⦄ := by
  pe2_spec (hp.get "pe_lam"), peLam

theorem peForall_spec (f a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pe_forall" [f, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      pe2W p n s₀.mem "promote_e" "promote_e" "pi_forall" f a b = some (r.headD 0, s'.mem); ⊤⦄ := by
  pe2_spec (hp.get "pe_forall"), peForall

theorem peLet_spec (f a b c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pe_let" [f, a, b, c]
    ⦃fun r s' => LocEq s' s₀ ∧ peLetW p n s₀.mem f a b c = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pe_let")]
  simp only [callFn, peLet]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "promote_e",
      callW_spec p n "pi_let"] <;>
    finish [peLetW, pe3K_some, pe3K₂_some, pe3K₃_some, hd1_some]

theorem peProj_spec (f a b c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pe_proj" [f, a, b, c]
    ⦃fun r s' => LocEq s' s₀ ∧ peProjW p n s₀.mem f a b c = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pe_proj")]
  simp only [callFn, peProj]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "promote_n",
      callW_spec p n "promote_e", callW_spec p n "pi_proj"] <;>
    finish [peProjW, pePjK_some, pePjK₂_some, hd1_some]

end specs

end L.Arena
