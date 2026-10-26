import ConAgua.Arena.DeclApd
import ConAgua.Arena.IndStubs
import ConAgua.Arena.IndPos2SpecB
import ConAgua.Arena.IndView
import ConAgua.Arena.LevelEquiv
import ConAgua.Arena.LevelArena
import ConAgua.Arena.StoreDen

/-!
# `all_level_params_defined`: the word models and the `vcgen` specs (lane `decls3`)

`DeclApd.lean` has the L code. Here: the word models of `alpd_ls`, `alpd_go` and the entry, written
as mutual continuations (the template of `IndSumSpec5.lean`'s `mentions_const_go`), with the arm
lemmas as `ind_grind` patterns, and the specs by induction on the exec fuel.

The level checks are lane `levels`' `lv_apd` at `A = IW` (`apdW`, `lvApd_spec`); `e_view` and
`ls_node` read their nodes (`eViewW`, `lsNodeW`). `alpd_go` at exec fuel `n + 1` calls everything
at `n`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Word models -/

/-- A pure result returned with the memory unchanged. -/
def apdR1 (m : Mem) : Option Word → Option (Word × Mem)
  | none => none
  | some r => some (r, m)

mutual
/-- **The model of `alpd_ls`**: every level of `POOL[lo ‥ lo + ll)` has its parameters in the
slice `(o, l)` of `IW`. -/
def alpdLsW : Nat → Mem → Word → Word → Word → Word → Option Word
  | 0, _, _, _, _, _ => none
  | n + 1, m, o, l, lo, ll =>
    if ll = 0 then some 1
    else alpdLsK n m o l lo ll (apdW IW n m (prd m lo) o l)
/-- After the first level. -/
def alpdLsK (n : Nat) (m : Mem) (o l lo ll : Word) : Option Word → Option Word
  | none => none
  | some r => if r = 0 then some 0 else alpdLsW n m o l (lo + 1) (ll - 1)
end

section alpdLsArms
variable (n : Nat) (m : Mem) (o l lo ll r : Word)
theorem alpdLsW_nil (h : ll = 0) : alpdLsW (n + 1) m o l lo ll = some 1 := by simp [alpdLsW, h]
theorem alpdLsW_cons (h : ll ≠ 0) : alpdLsW (n + 1) m o l lo ll =
    alpdLsK n m o l lo ll (apdW IW n m (prd m lo) o l) := by simp [alpdLsW, h]
theorem alpdLsK_zero : alpdLsK n m o l lo ll (some 0) = some 0 := by simp [alpdLsK]
theorem alpdLsK_ne (h : r ≠ 0) : alpdLsK n m o l lo ll (some r) = alpdLsW n m o l (lo + 1) (ll - 1) := by
  simp [alpdLsK, h]
end alpdLsArms

attribute [ind_grind] alpdLsW_nil alpdLsW_cons alpdLsK_zero alpdLsK_ne

mutual
/-- **The model of `alpd_go`** (exec fuel `n`, walk fuel word `f`): the result word and the memory
after; `none` where the L code aborts. -/
def apdGoW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, o, l, f, h => apdG1 n m o l f h
def apdG1 (n : Nat) (m : Mem) (o l f h : Word) : Option (Word × Mem) :=
  if f = 0 then none else apdG2 n m o l f h (mfindG apdSch m h 0)
def apdG2 (n : Nat) (m : Mem) (o l f h : Word) (fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 APDM) (fr.tail.headD 0 * 4 + 3), m)
  else apdG3 n m o l f h (eViewW m h)
def apdG3 (n : Nat) (m : Mem) (o l f h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else apdG4 h (apdNodeW n m o l f (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def apdG4 (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => apdG5 r (msetG apdSch m1 h 0 r)
def apdG5 (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 => some (r, m2)
/-- The node arms: the result and the memory before the final put. -/
def apdNodeW (n : Nat) (m : Mem) (o l f g x y w : Word) : Option (Word × Mem) :=
  if g = 2 then apdR1 m (apdW IW n m x o l)
  else if g = 3 then apdC1 n m o l (lsNodeW m y)
  else if g = 1 then apdGoW n m o l (f - 1) y
  else if g = 4 ∨ g = 5 ∨ g = 6 then apdB1 n o l f y (apdGoW n m o l (f - 1) x)
  else if g = 7 then apdL1 n o l f y w (apdGoW n m o l (f - 1) x)
  else if g = 9 then apdGoW n m o l (f - 1) w
  else some (1, m)
def apdC1 (n : Nat) (m : Mem) (o l : Word) (ls : List Word) : Option (Word × Mem) :=
  if ls = [] then none else apdR1 m (alpdLsW n m o l (ls.headD 0) (ls.tail.headD 0))
def apdB1 (n : Nat) (o l f y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => if r ≠ 0 then apdGoW n m1 o l (f - 1) y else some (r, m1)
def apdL1 (n : Nat) (o l f y w : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => if r ≠ 0 then apdL2 n o l f w (apdGoW n m1 o l (f - 1) y) else some (r, m1)
def apdL2 (n : Nat) (o l f w : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m2) => if r ≠ 0 then apdGoW n m2 o l (f - 1) w else some (r, m2)
end

section apdArms
variable (n : Nat) (m m1 m2 : Mem) (o l f h g x y w r : Word) (v fr ls : List Word)
theorem apdGoW_succ : apdGoW (n + 1) m o l f h = apdG1 n m o l f h := by simp [apdGoW]
theorem apdG1_abort (hf : f = 0) : apdG1 n m o l f h = none := by simp [apdG1, hf]
theorem apdG1_go (hf : f ≠ 0) : apdG1 n m o l f h = apdG2 n m o l f h (mfindG apdSch m h 0) := by
  simp [apdG1, hf]
theorem apdG2_abort (hr : fr = []) : apdG2 n m o l f h fr = none := by simp [apdG2, hr]
theorem apdG2_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    apdG2 n m o l f h fr = some (rdW (m.arr64 APDM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [apdG2]; rw [ite_eq_right hr, ite_eq_left hh]
theorem apdG2_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    apdG2 n m o l f h fr = apdG3 n m o l f h (eViewW m h) := by
  simp only [apdG2]; rw [ite_eq_right hr, ite_eq_right hh]
theorem apdG3_abort (hv : v = []) : apdG3 n m o l f h v = none := by simp [apdG3, hv]
theorem apdG3_go (hv : v ≠ []) : apdG3 n m o l f h v =
    apdG4 h (apdNodeW n m o l f (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
      (v.tail.tail.tail.headD 0)) := by simp [apdG3, hv]
theorem apdG4_some : apdG4 h (some (r, m1)) = apdG5 r (msetG apdSch m1 h 0 r) := by rw [apdG4]
theorem apdG5_some : apdG5 r (some m2) = some (r, m2) := by rw [apdG5]
theorem apdR1_some : apdR1 m (some r) = some (r, m) := by rw [apdR1]
theorem apdNodeW_sort (hg : g = 2) : apdNodeW n m o l f g x y w = apdR1 m (apdW IW n m x o l) := by
  simp [apdNodeW, hg]
theorem apdNodeW_const (hg : g = 3) : apdNodeW n m o l f g x y w = apdC1 n m o l (lsNodeW m y) := by
  simp [apdNodeW, hg]
theorem apdNodeW_fvar (hg : g = 1) : apdNodeW n m o l f g x y w = apdGoW n m o l (f - 1) y := by
  simp [apdNodeW, hg]
theorem apdNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) : apdNodeW n m o l f g x y w =
    apdB1 n o l f y (apdGoW n m o l (f - 1) x) := by
  have h2 : g ≠ 2 := by rcases hg with e | e | e <;> rw [e] <;> decide
  have h3 : g ≠ 3 := by rcases hg with e | e | e <;> rw [e] <;> decide
  have h1 : g ≠ 1 := by rcases hg with e | e | e <;> rw [e] <;> decide
  simp only [apdNodeW]; rw [ite_eq_right h2, ite_eq_right h3, ite_eq_right h1, ite_eq_left hg]
theorem apdNodeW_let (hg : g = 7) : apdNodeW n m o l f g x y w =
    apdL1 n o l f y w (apdGoW n m o l (f - 1) x) := by simp [apdNodeW, hg]
theorem apdNodeW_proj (hg : g = 9) : apdNodeW n m o l f g x y w = apdGoW n m o l (f - 1) w := by
  simp [apdNodeW, hg]
theorem apdNodeW_leaf (h1 : g ≠ 1) (h2 : g ≠ 2) (h3 : g ≠ 3) (h4 : ¬ (g = 4 ∨ g = 5 ∨ g = 6))
    (h7 : g ≠ 7) (h9 : g ≠ 9) : apdNodeW n m o l f g x y w = some (1, m) := by
  simp only [apdNodeW]; rw [ite_eq_right h2, ite_eq_right h3, ite_eq_right h1, ite_eq_right h4, ite_eq_right h7, ite_eq_right h9]
theorem apdC1_abort (hl : ls = []) : apdC1 n m o l ls = none := by simp [apdC1, hl]
theorem apdC1_go (hl : ls ≠ []) : apdC1 n m o l ls =
    apdR1 m (alpdLsW n m o l (ls.headD 0) (ls.tail.headD 0)) := by simp [apdC1, hl]
theorem apdB1_some : apdB1 n o l f y (some (r, m1)) =
    if r ≠ 0 then apdGoW n m1 o l (f - 1) y else some (r, m1) := by rw [apdB1]
theorem apdL1_some : apdL1 n o l f y w (some (r, m1)) =
    if r ≠ 0 then apdL2 n o l f w (apdGoW n m1 o l (f - 1) y) else some (r, m1) := by rw [apdL1]
theorem apdL2_some : apdL2 n o l f w (some (r, m2)) =
    if r ≠ 0 then apdGoW n m2 o l (f - 1) w else some (r, m2) := by rw [apdL2]
end apdArms

attribute [ind_grind] apdGoW_succ apdG1_abort apdG1_go apdG2_abort apdG2_hit apdG2_miss apdG3_abort
  apdG3_go apdG4_some apdG5_some apdR1_some apdNodeW_sort apdNodeW_const apdNodeW_fvar
  apdNodeW_bin apdNodeW_let apdNodeW_proj apdNodeW_leaf apdC1_abort apdC1_go apdB1_some
  apdL1_some apdL2_some

/-! ## The specs -/

section specs
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hls : p.lookup "ls_node" = some lsNode)
  (hf : p.lookup "apd_find" = some (memoFindG apdSch))
  (hput : p.lookup "apd_put" = some (memoPutG apdSch))
  (hlm : p.lookup "lv_mem" = some (lvMemG IW)) (hln : p.lookup "lv_node" = some lvNode)
  (hlv : p.lookup "lv_apd" = some lvApd)
  (hl : p.lookup "alpd_ls" = some alpdLs) (hgo : p.lookup "alpd_go" = some alpdGo)

include hlm hln hlv hl in
theorem alpdLs_spec (n : Nat) : ∀ (s₀ : St) (o l lo ll : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "alpd_ls" [o, l, lo, ll]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ alpdLsW n s₀.mem o l lo ll = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l lo ll; rw [invoke_eq _ hl]; simp only [callFn, alpdLs]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l lo ll
    rw [invoke_eq _ hl]
    simp only [callFn, alpdLs]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        lvApd_spec IW p hlm hln hlv n, ih] <;> finish (gen := 20)

/-- The spec of `alpd_go` at exec fuel `n`. -/
def ApdGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (o l f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "alpd_go" [o, l, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ apdGoW n s₀.mem o l f h = some (r.headD 0, s'.mem); ⊤⦄

set_option maxHeartbeats 4000000 in
include hv hls hf hput hlm hln hlv hl hgo in
theorem apdGo_step (n : Nat) (ih : ApdGoSpec p n) : ApdGoSpec p (n + 1) := by
  unfold ApdGoSpec at ih
  intro s₀ o l f h
  rw [invoke_eq _ hgo]
  simp only [callFn, alpdGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p hv n, lsNode_spec p hls n, memoFindG_spec apdSch p _ hf n,
      memoPutG_spec apdSch p _ hput n, lvApd_spec IW p hlm hln hlv n,
      alpdLs_spec p hlm hln hlv hl n, ih] <;> finish (gen := 20)

include hv hls hf hput hlm hln hlv hl hgo in
theorem apdGo_spec (n : Nat) : ApdGoSpec p n := by
  induction n with
  | zero =>
    intro s₀ o l f h; rw [invoke_eq _ hgo]; simp only [callFn, alpdGo]; vcgen [exec] <;> grind
  | succ n ih => exact apdGo_step p hv hls hf hput hlm hln hlv hl hgo n ih

end specs

/-! ## The entry -/

/-- **The model of `all_level_params_defined`**: clear the memo, walk at the twin's fuel. -/
def apdEntryW (n : Nat) (m : Mem) (o l e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) apdSch.cs + 2 = 0 then none
  else apdGoW n (mclearG apdSch m) o l 4000000000 e

theorem apdEntryW_eq (n : Nat) (m : Mem) (o l e : Word) (h0 : rdW (m.arr64 CTL) apdSch.cs + 2 ≠ 0) :
    apdEntryW n m o l e = apdGoW n (mclearG apdSch m) o l 4000000000 e := by simp [apdEntryW, h0]
attribute [ind_grind] apdEntryW_eq

theorem allLevelParamsDefined_spec_raw (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hls : p.lookup "ls_node" = some lsNode) (hf : p.lookup "apd_find" = some (memoFindG apdSch))
    (hput : p.lookup "apd_put" = some (memoPutG apdSch))
    (hcl : p.lookup "apd_clear" = some (memoClearG apdSch))
    (hlm : p.lookup "lv_mem" = some (lvMemG IW)) (hln : p.lookup "lv_node" = some lvNode)
    (hlv : p.lookup "lv_apd" = some lvApd)
    (hl : p.lookup "alpd_ls" = some alpdLs) (hgo : p.lookup "alpd_go" = some alpdGo)
    (hp : p.lookup "all_level_params_defined" = some allLevelParamsDefinedL) (n : Nat) (s₀ : St)
    (o l e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "all_level_params_defined" [o, l, e]
    ⦃fun r s' => LocEq s' s₀ ∧ apdEntryW n s₀.mem o l e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := apdGo_spec p hv hls hf hput hlm hln hlv hl hgo n
  unfold ApdGoSpec at ih
  rw [invoke_eq _ hp]
  simp only [callFn, allLevelParamsDefinedL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec apdSch p _ hcl n,
      ih] <;> finish

end L.Ind
