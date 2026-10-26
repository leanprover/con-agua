import ConAgua.Arena.PromoteN

/-!
# `promote_l`, `pl_arm`, `promote_l_pool`, `pls_arm`, `promote_ls`: models and specs

As `PromoteN.lean`: models whose callees are `callW` runs, one `vcgen` per spec. `pl_arm` views
the level with `lv_node` (`lvNodeW`, `LevelHeap.lean`); `pls_arm` views the level list with
`ls_node` (`lsNodeW`), promotes its handles above the pool top (`promote_l_pool`), raises the top
over them and interns the slice.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `promote_l` and `pl_arm` -/

/-- **The model of `promote_l(f, h)`.** -/
def plW (p : Prog) (n : Nat) (m : Mem) (f h : Word) : Option (Word × Mem) :=
  if f = 0 then none
  else if tierW h = 0 then some (h, m)
  else if mfindG plSch m h 0 = [] then none
  else if (mfindG plSch m h 0).headD 0 ≠ 0 then
    some (mvG plSch m ((mfindG plSch m h 0).tail.headD 0), m)
  else memoK plSch h (callW p n "pl_arm" [f - 1, h] m)

/-- After one child: intern with the unary interner `g`. -/
def pl1K (p : Prog) (n : Nat) (g : FnName) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => hd1 (callW p n g [x.headD 0] m₁)

/-- After the first of two children: promote the second, intern with `g`. -/
def pl2K (p : Prog) (n : Nat) (g : FnName) (f b : Word) :
    Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => pl2K₂ p n g (x.headD 0) (callW p n "promote_l" [f, b] m₁)
where pl2K₂ (p : Prog) (n : Nat) (g : FnName) (x : Word) :
    Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => hd1 (callW p n g [x, y.headD 0] m₂)

/-- The dispatch on `lv_node`'s words `r`. -/
def plK (p : Prog) (n : Nat) (m : Mem) (f : Word) (r : List Word) : Option (Word × Mem) :=
  if r.headD 0 = 0 then hd1 (callW p n "pi_zero" [] m)
  else if r.headD 0 = 1 then pl1K p n "pi_succ" (callW p n "promote_l" [f, r.tail.headD 0] m)
  else if r.headD 0 = 2 then
    pl2K p n "pi_max" f (r.tail.tail.headD 0) (callW p n "promote_l" [f, r.tail.headD 0] m)
  else if r.headD 0 = 3 then
    pl2K p n "pi_imax" f (r.tail.tail.headD 0) (callW p n "promote_l" [f, r.tail.headD 0] m)
  else if r.headD 0 = 4 then pl1K p n "pi_param" (callW p n "promote_n" [f, r.tail.headD 0] m)
  else none

/-- **The model of `pl_arm(f, h)`.** -/
def plArmW (p : Prog) (n : Nat) (m : Mem) (f h : Word) : Option (Word × Mem) :=
  if 4294967295 < h ∨ lvNodeW m h = [] then none else plK p n m f (lvNodeW m h)

section eqs
variable (p : Prog) (n : Nat) (m m₁ m₂ : Mem) (f h b x : Word) (r q : List Word) (g : FnName)

theorem pl1K_some : pl1K p n g (some (q, m₁)) = hd1 (callW p n g [q.headD 0] m₁) := rfl
theorem pl2K_some :
    pl2K p n g f b (some (q, m₁)) = pl2K.pl2K₂ p n g (q.headD 0) (callW p n "promote_l" [f, b] m₁) :=
  rfl
theorem pl2K₂_some :
    pl2K.pl2K₂ p n g x (some (q, m₂)) = hd1 (callW p n g [x, q.headD 0] m₂) := rfl

theorem plW_pers (hf : f ≠ 0) (ht : tierW h = 0) : plW p n m f h = some (h, m) := by
  simp [plW, hf, ht]

theorem plW_hit (hf : f ≠ 0) (ht : tierW h ≠ 0) (h0 : mfindG plSch m h 0 ≠ [])
    (h1 : (mfindG plSch m h 0).headD 0 ≠ 0) :
    plW p n m f h = some (mvG plSch m ((mfindG plSch m h 0).tail.headD 0), m) := by
  unfold plW; rw [if_neg hf, if_neg ht, if_neg h0, if_pos h1]

theorem plW_miss (hf : f ≠ 0) (ht : tierW h ≠ 0) (h0 : mfindG plSch m h 0 ≠ [])
    (h1 : (mfindG plSch m h 0).headD 0 = 0) :
    plW p n m f h = memoK plSch h (callW p n "pl_arm" [f - 1, h] m) := by
  unfold plW; rw [if_neg hf, if_neg ht, if_neg h0, if_neg (fun h2 => h2 h1)]

theorem plArmW_eq (hh : ¬ 4294967295 < h) (hne : lvNodeW m h ≠ []) :
    plArmW p n m f h = plK p n m f (lvNodeW m h) := by
  unfold plArmW; rw [if_neg (by simp [hh, hne])]

end eqs

section specs
variable (p : Prog) (hp : PromoteProg p) (n : Nat) (s₀ : St)
include hp

theorem promoteL_spec (f h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_l" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ plW p n s₀.mem f h = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_l")]
  simp only [callFn, promoteLL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec plSch p _ (hp.get "pl_find") n, memoPutG_spec plSch p _ (hp.get "pl_put") n,
      callW_spec p n "pl_arm", evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    finish [plW_pers, plW_hit, plW_miss, memoK_some, mvG, tierW]

theorem plArm_spec (f h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pl_arm" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ plArmW p n s₀.mem f h = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pl_arm")]
  simp only [callFn, plArm]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      lvNode_spec p (hp.get "lv_node") n, callW_spec p n "pi_zero", callW_spec p n "promote_l",
      callW_spec p n "pi_succ", callW_spec p n "pi_max", callW_spec p n "pi_imax",
      callW_spec p n "promote_n", callW_spec p n "pi_param"] <;>
    finish [plArmW_eq, plK, pl1K_some, pl2K_some, pl2K₂_some, hd1_some]

end specs

/-! ## `promote_l_pool`, `pls_arm`, `promote_ls` -/

/-- The memory of a callee's run. -/
def memK : Option (List Word × Mem) → Option Mem
  | none => none
  | some (_, m) => some m

theorem memK_some (r : List Word) (m : Mem) : memK (some (r, m)) = some m := rfl

/-- After one element: write it at the tagged address `q`, promote the rest. -/
def poolK (p : Prog) (n : Nat) (f o l q : Word) : Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m₁) =>
    if (m₁.arr64 (tierA 0 (q >>> 40))).size ≤ (q - (q >>> 40 <<< 40)).toNat then none
    else memK (callW p n "promote_l_pool" [f, o + 1, l - 1, q + 1]
      (m₁.set64 (tierA 0 (q >>> 40)) (q - (q >>> 40 <<< 40)) (r.headD 0)))

/-- **The model of `promote_l_pool(f, o, l, q)`** (the memory after; it returns `0`): the
scratch list's words at the tagged address `o`, promoted, to the tagged address `q`. -/
def plPoolW (p : Prog) (n : Nat) (m : Mem) (f o l q : Word) : Option Mem :=
  if l = 0 then some m
  else if (m.arr64 (tierA 0 (o >>> 40))).size ≤ (o &&& 1099511627775).toNat then none
  else poolK p n f o l q (callW p n "promote_l" [f, prd m o] m)

/-- After the elements: raise the top over them and intern the slice. -/
def plsK (p : Prog) (n : Nat) (q l : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (_, m₁) =>
    if (m₁.arr64 CTL).size = 0 then none
    else hd1 (callW p n "pi_ls" [q, l] (m₁.set64 CTL 0 (q + l)))

/-- **The model of `pls_arm(f, h)`**: the slice `(o, l)` of `ls_node`, its promoted copy at the
pool top `q`, in the top's tier. -/
def plsArmW (p : Prog) (n : Nat) (m : Mem) (f h : Word) : Option (Word × Mem) :=
  if 4294967295 < h ∨ lsNodeW m h = [] then none
  else if (m.arr64 CTL).size = 0 then none
  else if m.len64 (tierA 0 (m.top >>> 40)) < (m.top &&& 1099511627775) then none
  else if m.len64 (tierA 0 (m.top >>> 40)) - (m.top &&& 1099511627775) <
    (lsNodeW m h).tail.headD 0 then none
  else plsK p n m.top ((lsNodeW m h).tail.headD 0)
    (callW p n "promote_l_pool" [f, (lsNodeW m h).headD 0, (lsNodeW m h).tail.headD 0, m.top] m)

/-- **The model of `promote_ls(f, h)`** (no fuel test: the twin's `promoteLs` has none). -/
def plsW (p : Prog) (n : Nat) (m : Mem) (f h : Word) : Option (Word × Mem) :=
  if tierW h = 0 then some (h, m)
  else if mfindG plsSch m h 0 = [] then none
  else if (mfindG plsSch m h 0).headD 0 ≠ 0 then
    some (mvG plsSch m ((mfindG plsSch m h 0).tail.headD 0), m)
  else memoK plsSch h (callW p n "pls_arm" [f, h] m)

section eqs2
variable (p : Prog) (n : Nat) (m m₁ : Mem) (f h o l q : Word) (r : List Word)

theorem poolK_some (hq : ¬ (m₁.arr64 (tierA 0 (q >>> 40))).size ≤ (q - (q >>> 40 <<< 40)).toNat) :
    poolK p n f o l q (some (r, m₁)) =
      memK (callW p n "promote_l_pool" [f, o + 1, l - 1, q + 1]
        (m₁.set64 (tierA 0 (q >>> 40)) (q - (q >>> 40 <<< 40)) (r.headD 0))) := by
  simp only [poolK, hq, ↓reduceIte]

theorem plPoolW_nil (hl : l = 0) : plPoolW p n m f o l q = some m := by simp [plPoolW, hl]
theorem plPoolW_cons (hl : l ≠ 0)
    (ho : ¬ (m.arr64 (tierA 0 (o >>> 40))).size ≤ (o &&& 1099511627775).toNat) :
    plPoolW p n m f o l q = poolK p n f o l q (callW p n "promote_l" [f, prd m o] m) := by
  simp only [plPoolW, hl, ho, ↓reduceIte]

theorem plsK_some (hc : (m₁.arr64 CTL).size ≠ 0) :
    plsK p n q l (some (r, m₁)) = hd1 (callW p n "pi_ls" [q, l] (m₁.set64 CTL 0 (q + l))) := by
  simp only [plsK, hc, ↓reduceIte]

theorem plsArmW_eq (hh : ¬ 4294967295 < h) (hne : lsNodeW m h ≠ []) (hc : (m.arr64 CTL).size ≠ 0)
    (h1 : ¬ m.len64 (tierA 0 (m.top >>> 40)) < (m.top &&& 1099511627775))
    (h2 : ¬ m.len64 (tierA 0 (m.top >>> 40)) - (m.top &&& 1099511627775) < (lsNodeW m h).tail.headD 0) :
    plsArmW p n m f h = plsK p n m.top ((lsNodeW m h).tail.headD 0)
      (callW p n "promote_l_pool" [f, (lsNodeW m h).headD 0, (lsNodeW m h).tail.headD 0, m.top] m) := by
  simp only [plsArmW, hh, hne, hc, h1, h2, or_self, ↓reduceIte]

theorem plsW_pers (ht : tierW h = 0) : plsW p n m f h = some (h, m) := by simp [plsW, ht]

theorem plsW_hit (ht : tierW h ≠ 0) (h0 : mfindG plsSch m h 0 ≠ [])
    (h1 : (mfindG plsSch m h 0).headD 0 ≠ 0) :
    plsW p n m f h = some (mvG plsSch m ((mfindG plsSch m h 0).tail.headD 0), m) := by
  unfold plsW; rw [if_neg ht, if_neg h0, if_pos h1]

theorem plsW_miss (ht : tierW h ≠ 0) (h0 : mfindG plsSch m h 0 ≠ [])
    (h1 : (mfindG plsSch m h 0).headD 0 = 0) :
    plsW p n m f h = memoK plsSch h (callW p n "pls_arm" [f, h] m) := by
  unfold plsW; rw [if_neg ht, if_neg h0, if_neg (fun h2 => h2 h1)]

end eqs2

section specs2
variable (p : Prog) (hp : PromoteProg p) (n : Nat) (s₀ : St)
include hp

theorem promoteLPool_spec (f o l q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_l_pool" [f, o, l, q]
    ⦃fun _ s' => LocEq s' s₀ ∧ plPoolW p n s₀.mem f o l q = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_l_pool")]
  simp only [callFn, promoteLPool]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "promote_l", callW_spec p n "promote_l_pool"] <;>
    finish [plPoolW_nil, plPoolW_cons, poolK_some, memK_some, prd]

theorem plsArm_spec (f h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pls_arm" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ plsArmW p n s₀.mem f h = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pls_arm")]
  simp only [callFn, plsArm]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      lsNode_spec p (hp.get "ls_node") n, callW_spec p n "promote_l_pool", callW_spec p n "pi_ls"] <;>
    finish [plsArmW_eq, plsK_some, hd1_some, Mem.top]

theorem promoteLs_spec (f h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_ls" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ plsW p n s₀.mem f h = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_ls")]
  simp only [callFn, promoteLsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec plsSch p _ (hp.get "pls_find") n, memoPutG_spec plsSch p _ (hp.get "pls_put") n,
      callW_spec p n "pls_arm", evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    finish [plsW_pers, plsW_hit, plsW_miss, memoK_some, mvG, tierW]

end specs2

end L.Arena
