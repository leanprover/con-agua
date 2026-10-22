import ConAgua.Arena.RecCheckSpec6
import ConAgua.Arena.IndPos2SpecD

/-!
# `RecCheck`: `targetAbsGo`, `targetAbs` (lane `indproofs2`, helper `rec3`)

The member abstraction, one memoised DAG walk (memo `ta`: array `TAM`, `CTL[212]`). The shape is
`IndPos2SpecD.lean`'s `replace_apps_go` (an `EIdx`-valued memo, the interning arms through `rpMkW`):
word models by exec fuel, the L specs by `vcgen`, the relational lemma by strong induction.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Word models -/

/-- After `sl_find` in `target_abs_const`. -/
def taCK (m : Mem) (ho hl h : Word) : Option (List Word) → Option (Word × Mem)
  | none => none
  | some fr =>
    if fr.headD 0 = 0 then some (h, m)
    else if hl ≤ fr.tail.headD 0 then some (h, m)
    else some (rdW (m.arr64 IW) (ho + fr.tail.headD 0), m)

/-- **The model of `target_abs_const`.** -/
def taCW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lvls, ho, hl, h, nn, vus =>
    if vus ≠ lvls then some (h, m) else taCK m ho hl h (findW n m no nl nn)

mutual
def taGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lvls, ho, hl, f, h =>
    if f = 0 then none else taG1 n m no nl lvls ho hl f h (eViewW m h)
def taG1 (n : Nat) (m : Mem) (no nl lvls ho hl f h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 then some (h, m)
  else if v.headD 0 = 3 then taCW n m no nl lvls ho hl h (v.tail.headD 0) (v.tail.tail.headD 0)
  else taG3 n m no nl lvls ho hl f h v (mfindG taSch m h 0)
def taG3 (n : Nat) (m : Mem) (no nl lvls ho hl f h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 TAM) (fr.tail.headD 0 * 4 + 3), m)
  else taG4 h (taNodeW n m no nl lvls ho hl (f - 1) (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def taG4 (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => taG5 r (msetG taSch m1 h 0 r)
def taG5 (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 => some (r, m2)
def taNodeW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lvls, ho, hl, f1, g, x, y, z =>
    if g = 4 ∨ g = 5 ∨ g = 6 then taB1 n no nl lvls ho hl f1 g y (taGoW n m no nl lvls ho hl f1 x)
    else if g = 7 then taL1 n no nl lvls ho hl f1 y z (taGoW n m no nl lvls ho hl f1 x)
    else taP1 x y (taGoW n m no nl lvls ho hl f1 z)
def taB1 (n : Nat) (no nl lvls ho hl f1 g y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (a2, m1) => taB2 g a2 (taGoW n m1 no nl lvls ho hl f1 y)
def taB2 (g a2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x2, m2) => rpMkW m2 g a2 x2 0 0 0
def taL1 (n : Nat) (no nl lvls ho hl f1 y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (a2, m1) => taL2 n no nl lvls ho hl f1 z a2 (taGoW n m1 no nl lvls ho hl f1 y)
def taL2 (n : Nat) (no nl lvls ho hl f1 z a2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x2, m2) => taL3 a2 x2 (taGoW n m2 no nl lvls ho hl f1 z)
def taL3 (a2 x2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (c2, m3) => rpMkW m3 7 a2 x2 c2 0 0
def taP1 (x y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (a2, m1) => rpMkW m1 9 a2 0 0 y x
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (no nl lvls ho hl f f1 h g x y z a2 x2 c2 r nn vus : Word)
  (v fr : List Word)
theorem taCW_ne (hv : vus ≠ lvls) : taCW (n + 1) m no nl lvls ho hl h nn vus = some (h, m) := by simp [taCW, hv]
theorem taCW_eq (hv : ¬ vus ≠ lvls) :
    taCW (n + 1) m no nl lvls ho hl h nn vus = taCK m ho hl h (findW n m no nl nn) := by
  simp only [taCW]; rw [if_neg hv]
theorem taCK_miss (h0 : fr.headD 0 = 0) : taCK m ho hl h (some fr) = some (h, m) := by
  simp only [taCK]; rw [if_pos h0]
theorem taCK_out (h0 : ¬ fr.headD 0 = 0) (h1 : hl ≤ fr.tail.headD 0) : taCK m ho hl h (some fr) = some (h, m) := by
  simp only [taCK]; rw [if_neg h0, if_pos h1]
theorem taCK_hit (h0 : ¬ fr.headD 0 = 0) (h1 : ¬ hl ≤ fr.tail.headD 0) :
    taCK m ho hl h (some fr) = some (rdW (m.arr64 IW) (ho + fr.tail.headD 0), m) := by
  simp only [taCK]; rw [if_neg h0, if_neg h1]
theorem taGoW_abort (hf : f = 0) : taGoW (n + 1) m no nl lvls ho hl f h = none := by simp [taGoW, hf]
theorem taGoW_view (hf : f ≠ 0) :
    taGoW (n + 1) m no nl lvls ho hl f h = taG1 n m no nl lvls ho hl f h (eViewW m h) := by simp [taGoW, hf]
theorem taG1_abort (hv : v = []) : taG1 n m no nl lvls ho hl f h v = none := by simp [taG1, hv]
theorem taG1_leaf (hv : v ≠ []) (hg : v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8) :
    taG1 n m no nl lvls ho hl f h v = some (h, m) := by simp only [taG1]; rw [if_neg hv, if_pos hg]
theorem taG1_const (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : v.headD 0 = 3) :
    taG1 n m no nl lvls ho hl f h v = taCW n m no nl lvls ho hl h (v.tail.headD 0) (v.tail.tail.headD 0) := by
  simp only [taG1]; rw [if_neg hv, if_neg hg, if_pos h3]
theorem taG1_node (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : ¬ v.headD 0 = 3) :
    taG1 n m no nl lvls ho hl f h v = taG3 n m no nl lvls ho hl f h v (mfindG taSch m h 0) := by
  simp only [taG1]; rw [if_neg hv, if_neg hg, if_neg h3]
theorem taG3_abort (hr : fr = []) : taG3 n m no nl lvls ho hl f h v fr = none := by simp [taG3, hr]
theorem taG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    taG3 n m no nl lvls ho hl f h v fr = some (rdW (m.arr64 TAM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [taG3]; rw [if_neg hr, if_pos hh]
theorem taG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    taG3 n m no nl lvls ho hl f h v fr = taG4 h (taNodeW n m no nl lvls ho hl (f - 1) (v.headD 0)
      (v.tail.headD 0) (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [taG3]; rw [if_neg hr, if_neg hh]
theorem taG4_some : taG4 h (some (r, m1)) = taG5 r (msetG taSch m1 h 0 r) := by rw [taG4]
theorem taG5_some : taG5 r (some m2) = some (r, m2) := by rw [taG5]
theorem taNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) : taNodeW (n + 1) m no nl lvls ho hl f1 g x y z =
    taB1 n no nl lvls ho hl f1 g y (taGoW n m no nl lvls ho hl f1 x) := by
  simp only [taNodeW]; rw [if_pos hg]
theorem taNodeW_let : taNodeW (n + 1) m no nl lvls ho hl f1 7 x y z =
    taL1 n no nl lvls ho hl f1 y z (taGoW n m no nl lvls ho hl f1 x) := by simp [taNodeW]
theorem taNodeW_proj (hg : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (hg7 : ¬ g = 7) :
    taNodeW (n + 1) m no nl lvls ho hl f1 g x y z = taP1 x y (taGoW n m no nl lvls ho hl f1 z) := by
  simp only [taNodeW]; rw [if_neg hg, if_neg hg7]
theorem taB1_some : taB1 n no nl lvls ho hl f1 g y (some (a2, m1)) =
    taB2 g a2 (taGoW n m1 no nl lvls ho hl f1 y) := by rw [taB1]
theorem taB2_some : taB2 g a2 (some (x2, m2)) = rpMkW m2 g a2 x2 0 0 0 := by rw [taB2]
theorem taL1_some : taL1 n no nl lvls ho hl f1 y z (some (a2, m1)) =
    taL2 n no nl lvls ho hl f1 z a2 (taGoW n m1 no nl lvls ho hl f1 y) := by rw [taL1]
theorem taL2_some : taL2 n no nl lvls ho hl f1 z a2 (some (x2, m2)) =
    taL3 a2 x2 (taGoW n m2 no nl lvls ho hl f1 z) := by rw [taL2]
theorem taL3_some : taL3 a2 x2 (some (c2, m3)) = rpMkW m3 7 a2 x2 c2 0 0 := by rw [taL3]
theorem taP1_some : taP1 x y (some (a2, m1)) = rpMkW m1 9 a2 0 0 y x := by rw [taP1]
end arms
attribute [ind_grind] taCW_ne taCW_eq taCK_miss taCK_out taCK_hit taGoW_abort taGoW_view taG1_abort taG1_leaf
  taG1_const taG1_node taG3_abort taG3_hit taG3_miss taG4_some taG5_some taNodeW_bin taNodeW_let
  taNodeW_proj taB1_some taB2_some taL1_some taL2_some taL3_some taP1_some

/-- The lookups of the `target_abs` walk. -/
structure TaLook (p : Prog) : Prop where
  hk : MkLook p
  hv : p.lookup "e_view" = some eView
  hf : p.lookup "sl_find" = some slFind
  tf : p.lookup "ta_find" = some (memoFindG taSch)
  tp : p.lookup "ta_put" = some (memoPutG taSch)
  tc : p.lookup "ta_clear" = some (memoClearG taSch)
  cst : p.lookup "target_abs_const" = some targetAbsConst
  go : p.lookup "target_abs_go" = some targetAbsGo
  node : p.lookup "target_abs_node" = some targetAbsNode
  top : p.lookup "target_abs" = some targetAbs

section spec
variable (p : Prog) (L : TaLook p)

include L in
theorem taConst_spec (n : Nat) (s₀ : St) (no nl lvls ho hl h nn vus : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_abs_const" [no, nl, lvls, ho, hl, h, nn, vus]
    ⦃fun r s' => LocEq s' s₀ ∧ taCW n s₀.mem no nl lvls ho hl h nn vus = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.cst]
  simp only [callFn, targetAbsConst]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, slFind_spec p L.hf n] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7]

def TaGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl lvls ho hl f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_abs_go" [no, nl, lvls, ho, hl, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ taGoW n s₀.mem no nl lvls ho hl f h = some (r.headD 0, s'.mem); ⊤⦄

def TaNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl lvls ho hl f1 g x y z : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_abs_node" [no, nl, lvls, ho, hl, f1, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ taNodeW n s₀.mem no nl lvls ho hl f1 g x y z = some (r.headD 0, s'.mem); ⊤⦄

include L in
theorem taGo_step (n : Nat) (ih : TaNodeSpec p n) : TaGoSpec p (n + 1) := by
  unfold TaNodeSpec at ih
  intro s₀ no nl lvls ho hl f h
  rw [invoke_eq _ L.go]
  simp only [callFn, targetAbsGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p L.hv n, taConst_spec p L n, memoFindG_spec taSch p _ L.tf n,
      memoPutG_spec taSch p _ L.tp n, ih] <;> finish (gen := 20) [St.setLocs_mem', loc_init4, loc_init5, loc_init6]

include L in
theorem taNode_step (n : Nat) (ih : TaGoSpec p n) : TaNodeSpec p (n + 1) := by
  unfold TaGoSpec at ih
  intro s₀ no nl lvls ho hl f1 g x y z
  have hk := L.hk
  rw [invoke_eq _ L.node]
  simp only [callFn, targetAbsNode]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
      mkApp_spec p hk.hd hk.appF hk.appP hk.appI hk.appM n,
      mkLam_spec p hk.hd hk.lamF hk.lamP hk.lamI hk.lamM n,
      mkForall_spec p hk.hd hk.forF hk.forP hk.forI hk.forM n,
      mkLet_spec p hk.hd hk.ltF hk.ltP hk.ltI hk.ltM n,
      mkProj_spec p hk.hd hk.prjF hk.prjP hk.prjI hk.prjM n] <;>
    finish (gen := 20) [St.setLocs_mem', rpMkW, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9]

include L in
theorem taGo_spec (n : Nat) : TaGoSpec p n ∧ TaNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ no nl lvls ho hl f h; rw [invoke_eq _ L.go]; simp only [callFn, targetAbsGo]; vcgen [exec] <;> grind
    · intro s₀ no nl lvls ho hl f1 g x y z; rw [invoke_eq _ L.node]; simp only [callFn, targetAbsNode]
      vcgen [exec] <;> grind
  | succ n ih => exact ⟨taGo_step p L n ih.2, taNode_step p L n ih.1⟩

end spec

/-- **The model of `target_abs`**: clear the memo, the walk at `⟪CWF⟫`. -/
def taAW (n : Nat) (m : Mem) (no nl lvls ho hl e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) taSch.cs + 2 = 0 then none
  else taGoW n (mclearG taSch m) no nl lvls ho hl CWF e

theorem taAW_eq (n : Nat) (m : Mem) (no nl lvls ho hl e : Word) (h0 : rdW (m.arr64 CTL) taSch.cs + 2 ≠ 0) :
    taAW n m no nl lvls ho hl e = taGoW n (mclearG taSch m) no nl lvls ho hl CWF e := by simp [taAW, h0]
attribute [ind_grind] taAW_eq

theorem targetAbs_spec (p : Prog) (L : TaLook p) (n : Nat) (s₀ : St) (no nl lvls ho hl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_abs" [no, nl, lvls, ho, hl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ taAW n s₀.mem no nl lvls ho hl e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (taGo_spec p L n).1
  unfold TaGoSpec at ih
  rw [invoke_eq _ L.top]
  simp only [callFn, targetAbs]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec taSch p _ L.tc n, ih] <;>
    finish

end L.Ind
