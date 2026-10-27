import ConAgua.Arena.IndDecStab
import ConAgua.Arena.IndPosSpec2A
import ConAgua.Arena.IndSim
import ConAgua.Arena.RecStab

/-!
# `RecCheck`: `targetAbsGo`, `targetAbs` (lane `indproofs2`, helper `rec3`)

The member abstraction, one memoised DAG walk (memo `ta`: array `TAM`, `CTL[212]`). The shape is
`IndPos2SpecD.lean`'s `replace_apps_go` (an `EIdx`-valued memo, the interning arms through `rpMkW`):
word models by exec fuel, the L specs by `vcgen`, the relational lemma by strong induction.
-/

noncomputable section

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
  simp only [taCW]; rw [ite_eq_right hv]
theorem taCK_miss (h0 : fr.headD 0 = 0) : taCK m ho hl h (some fr) = some (h, m) := by
  simp only [taCK]; rw [ite_eq_left h0]
theorem taCK_out (h0 : ¬ fr.headD 0 = 0) (h1 : hl ≤ fr.tail.headD 0) : taCK m ho hl h (some fr) = some (h, m) := by
  simp only [taCK]; rw [ite_eq_right h0, ite_eq_left h1]
theorem taCK_hit (h0 : ¬ fr.headD 0 = 0) (h1 : ¬ hl ≤ fr.tail.headD 0) :
    taCK m ho hl h (some fr) = some (rdW (m.arr64 IW) (ho + fr.tail.headD 0), m) := by
  simp only [taCK]; rw [ite_eq_right h0, ite_eq_right h1]
theorem taGoW_abort (hf : f = 0) : taGoW (n + 1) m no nl lvls ho hl f h = none := by simp [taGoW, hf]
theorem taGoW_view (hf : f ≠ 0) :
    taGoW (n + 1) m no nl lvls ho hl f h = taG1 n m no nl lvls ho hl f h (eViewW m h) := by simp [taGoW, hf]
theorem taG1_leaf (hv : v ≠ []) (hg : v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8) :
    taG1 n m no nl lvls ho hl f h v = some (h, m) := by simp only [taG1]; rw [ite_eq_right hv, ite_eq_left hg]
theorem taG1_const (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : v.headD 0 = 3) :
    taG1 n m no nl lvls ho hl f h v = taCW n m no nl lvls ho hl h (v.tail.headD 0) (v.tail.tail.headD 0) := by
  simp only [taG1]; rw [ite_eq_right hv, ite_eq_right hg, ite_eq_left h3]
theorem taG1_node (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : ¬ v.headD 0 = 3) :
    taG1 n m no nl lvls ho hl f h v = taG3 n m no nl lvls ho hl f h v (mfindG taSch m h 0) := by
  simp only [taG1]; rw [ite_eq_right hv, ite_eq_right hg, ite_eq_right h3]
theorem taG3_abort (hr : fr = []) : taG3 n m no nl lvls ho hl f h v fr = none := by simp [taG3, hr]
theorem taG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    taG3 n m no nl lvls ho hl f h v fr = some (rdW (m.arr64 TAM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [taG3]; rw [ite_eq_right hr, ite_eq_left hh]
theorem taG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    taG3 n m no nl lvls ho hl f h v fr = taG4 h (taNodeW n m no nl lvls ho hl (f - 1) (v.headD 0)
      (v.tail.headD 0) (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [taG3]; rw [ite_eq_right hr, ite_eq_right hh]
theorem taG4_some : taG4 h (some (r, m1)) = taG5 r (msetG taSch m1 h 0 r) := by rw [taG4]
theorem taG5_some : taG5 r (some m2) = some (r, m2) := by rw [taG5]
theorem taNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) : taNodeW (n + 1) m no nl lvls ho hl f1 g x y z =
    taB1 n no nl lvls ho hl f1 g y (taGoW n m no nl lvls ho hl f1 x) := by
  simp only [taNodeW]; rw [ite_eq_left hg]
theorem taNodeW_let : taNodeW (n + 1) m no nl lvls ho hl f1 7 x y z =
    taL1 n no nl lvls ho hl f1 y z (taGoW n m no nl lvls ho hl f1 x) := by simp [taNodeW]
theorem taNodeW_proj (hg : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (hg7 : ¬ g = 7) :
    taNodeW (n + 1) m no nl lvls ho hl f1 g x y z = taP1 x y (taGoW n m no nl lvls ho hl f1 z) := by
  simp only [taNodeW]; rw [ite_eq_right hg, ite_eq_right hg7]
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
attribute [ind_grind] taCW_ne taCW_eq taCK_miss taCK_out taCK_hit taGoW_abort taGoW_view taG1_leaf
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

/-! ## The relational side -/

/-- The twin's `const` arm. -/
def taConstT (names : List NIdx) (lvls : LsIdx) (holes : List EIdx) (h : EIdx) (n : NIdx) (us : LsIdx) : EIdx :=
  if us == lvls then
    match names.findIdx? (· == n) with
    | some t => match holes[t]? with
      | some x => x
      | none => h
    | none => h
  else h

/-- The twin's memoised arms. -/
def taArm (names : List NIdx) (lvls : LsIdx) (holes : List EIdx) (memo : Std.HashMap EIdx EIdx)
    (fuel : Nat) (h : EIdx) : ENodeView → AM (EIdx × Std.HashMap EIdx EIdx)
  | .app a b => do
    let (a', m) ← ConRon.Arena.targetAbsGo names lvls holes memo fuel a
    let (b', m2) ← ConRon.Arena.targetAbsGo names lvls holes m fuel b
    let r ← internAppE a' b'
    pure (r, m2)
  | .lam ty body => do
    let (t', m) ← ConRon.Arena.targetAbsGo names lvls holes memo fuel ty
    let (b', m2) ← ConRon.Arena.targetAbsGo names lvls holes m fuel body
    let r ← internLamE t' b'
    pure (r, m2)
  | .forallE ty body => do
    let (t', m) ← ConRon.Arena.targetAbsGo names lvls holes memo fuel ty
    let (b', m2) ← ConRon.Arena.targetAbsGo names lvls holes m fuel body
    let r ← internForallEE t' b'
    pure (r, m2)
  | .letE ty val body => do
    let (t', m) ← ConRon.Arena.targetAbsGo names lvls holes memo fuel ty
    let (v', m2) ← ConRon.Arena.targetAbsGo names lvls holes m fuel val
    let (b', m3) ← ConRon.Arena.targetAbsGo names lvls holes m2 fuel body
    let r ← internLetEE t' v' b'
    pure (r, m3)
  | .proj s i sub => do
    let (u, m) ← ConRon.Arena.targetAbsGo names lvls holes memo fuel sub
    let r ← internProjE s i u
    pure (r, m)
  | _ => pure (h, memo)

theorem targetAbsGo_succ' (names : List NIdx) (lvls : LsIdx) (holes : List EIdx) (memo : Std.HashMap EIdx EIdx)
    (fuel : Nat) (h : EIdx) :
    ConRon.Arena.targetAbsGo names lvls holes memo (fuel + 1) h = (do
      let v ← view h
      match v with
      | .bvar _ => pure (h, memo)
      | .sort _ => pure (h, memo)
      | .lit _ => pure (h, memo)
      | .fvar _ _ => pure (h, memo)
      | .const n us => pure (taConstT names lvls holes h n us, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← taArm names lvls holes memo fuel h v
          pure (r, m.insert h r)) := by
  rw [ConRon.Arena.targetAbsGo.eq_2]
  congr 1
  funext v
  cases v with
  | app a' x' => simp only [taArm, bind_assoc, pure_bind]; rfl
  | lam t body => simp only [taArm, bind_assoc, pure_bind]; rfl
  | forallE t body => simp only [taArm, bind_assoc, pure_bind]; rfl
  | letE t v' body => simp only [taArm, bind_assoc, pure_bind]; rfl
  | proj s i x => simp only [taArm, bind_assoc, pure_bind]; rfl
  | bvar _ => rfl
  | sort _ => rfl
  | lit _ => rfl
  | fvar _ _ => rfl
  | const n us =>
    simp only [taConstT]
    by_cases hb : (us == lvls) = true
    · simp only [hb, ite_true]
      cases names.findIdx? (· == n) with
      | none => rfl
      | some t => dsimp only; cases holes[t]? <;> rfl
    · simp [hb]

theorem taSch_wf : taSch.WF := ⟨by decide, by decide⟩

/-- The `ta` memo against the twin's map. -/
abbrev taMR (m : Mem) (mp : Std.HashMap EIdx EIdx) : Prop :=
  MemoRG taSch bmKey (fun w : Word => decE w) m mp

theorem taMR_low {m m' : Mem} (hf : LowFr m m') {mp : Std.HashMap EIdx EIdx} (h : taMR m mp) : taMR m' mp := by
  obtain ⟨A, C, hf, hA, hC⟩ := hf
  exact memoRG_frame taSch taSch_wf bmKey (fun w : Word => decE w) A C
    (fun hmem => by have := hA _ hmem; simp [taSch, TAM] at this)
    (fun hmem => by have := hC _ hmem; simp [taSch] at this) m m' hf mp h

/-- **The `const` arm**: a read; the hole of a member at the walk's levels. -/
theorem taCW_ok (n : Nat) {m m' : Mem} {no nl lvls ho hl h nn vus r : Word} {names : List NIdx}
    {holes : List EIdx} (hc : taCW n m no nl lvls ho hl h nn vus = some (r, m'))
    (hlv : H lvls) (hn : H nn) (hvus : H vus)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hho : decHL m ho.toNat hl.toNat = some holes) (hhb : ho.toNat + hl.toNat < 2 ^ 64) :
    m' = m ∧ decE r = taConstT names (decI lvls) holes (decE h) (decI nn) (decI vus) := by
  obtain _ | n := n
  · simp [taCW] at hc
  by_cases hv : vus ≠ lvls
  · rw [taCW_ne (hv := hv)] at hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
    have : ¬ ((decI vus : LsIdx) == decI lvls) = true := by rw [decI_beq' vus lvls hvus hlv]; simpa using hv
    refine ⟨rfl, ?_⟩
    simp only [taConstT, this]; rfl
  rw [taCW_eq (hv := hv)] at hc
  have hbeq : ((decI vus : LsIdx) == decI lvls) = true := by rw [decI_beq' vus lvls hvus hlv]; simpa using hv
  obtain ⟨ws, hws, rfl, hwlt⟩ := slR_of_decHL m _ _ names hdec hno
  simp only [UInt64.ofNat_toNat] at hws
  have hlen : ws.length < 2 ^ 64 := by have := decHL_length m hdec; simp at this; omega
  have hhl := decHL_length m hho
  rcases hfw : findW n m no nl nn with _ | fr <;> rw [hfw] at hc <;>
    try (simp only [taCK, reduceCtorEq] at hc; done)
  have hfr := findW_ok n _ _ _ _ _ _ hws hfw hlen
  have hfi := findIdx_decIP ws nn hwlt hn
  cases hwi : ws.findIdx? (· == nn) with
  | none =>
    rw [hwi] at hfr; subst hfr
    rw [taCK_miss (h0 := rfl)] at hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
    refine ⟨rfl, ?_⟩
    simp only [taConstT, hbeq, ite_true, hfi, hwi]
  | some i =>
    rw [hwi] at hfr; subst hfr
    obtain ⟨hil, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hwi
    have hi : (UInt64.ofNat i : Word).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
    by_cases hout : hl ≤ UInt64.ofNat i
    · rw [taCK_out (h0 := by simp) (h1 := by simpa using hout)] at hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
      have : holes.length ≤ i := by
        have h1 := UInt64.le_iff_toNat_le.mp hout; rw [hi] at h1; rw [hhl]; exact h1
      refine ⟨rfl, ?_⟩
      simp only [taConstT, hbeq, ite_true, hfi, hwi, List.getElem?_eq_none this]
    · rw [taCK_hit (h0 := by simp) (h1 := by simpa using hout)] at hc
      simp only [Option.some.injEq, Prod.mk.injEq, List.tail_cons, List.headD_cons] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hih : i < hl.toNat := by
        have : ¬ hl.toNat ≤ i := fun x => hout (UInt64.le_iff_toNat_le.mpr (by rw [hi]; exact x))
        omega
      obtain ⟨-, hd⟩ := rd_iwH (p := ho) (i := UInt64.ofNat i) (by rw [hi]; exact decHL_getI hho i hih)
        (by rw [hi]; omega)
      refine ⟨rfl, ?_⟩
      simp only [taConstT, hbeq, ite_true, hfi, hwi, List.getElem?_eq_getElem (show i < holes.length by omega)]
      exact hd

/-- The inputs of the `ta` walk at `m`: the member names and the holes decode below the IW top. -/
def TaIn (m : Mem) (no nl ho hl : Word) (names : List NIdx) (holes : List EIdx) : Prop :=
  decHL m no.toNat nl.toNat = some names ∧ no.toNat + nl.toNat ≤ iwTop m ∧
    decHL m ho.toNat hl.toNat = some holes ∧ ho.toNat + hl.toNat ≤ iwTop m

theorem TaIn.grow {m m1 : Mem} {no nl ho hl : Word} {names : List NIdx} {holes : List EIdx}
    (h : TaIn m no nl ho hl names holes) (hg : IWGrow m m1) : TaIn m1 no nl ho hl names holes :=
  ⟨by rw [decHL_grow hg h.2.1]; exact h.1, by have := hg.1; have := h.2.1; omega,
    by rw [decHL_grow hg h.2.2.2]; exact h.2.2.1, by have := hg.1; have := h.2.2.2; omega⟩

/-- The post of the `ta` walk from `m`: the result decoded, the stage kept, the memo related. -/
abbrev TaQ (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m : Mem) (r : Word)
    (x : EIdx × Std.HashMap EIdx EIdx) (m' : Mem) (a' : AState) : Prop :=
  x.1 = decE r ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ taMR m' x.2

def TaGoOK (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (no nl lvls ho hl f h : Word) (names : List NIdx) (holes : List EIdx)
    (mp : Std.HashMap EIdx EIdx), StageR dn vis fe m a → H h → H lvls →
    TaIn m no nl ho hl names holes → taMR m mp →
    Sim (taGoW n m no nl lvls ho hl f h)
      (ConRon.Arena.targetAbsGo names (decI lvls) holes mp f.toNat (decE h)) a (TaQ dn fe vis m)

/-- A twin run rewritten (an unfolding at the state `a`). -/
theorem rcSim_ofRun {β α : Type} {mo : Option (β × Mem)} {op op' : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (e : op.run a = op'.run a) (h : Sim mo op' a Q) :
    Sim mo op a Q := fun r m' hm => by
  obtain ⟨x, a', h1, h2⟩ := h r m' hm; exact ⟨x, a', e ▸ h1, h2⟩

/-- Two children and an interning: `app`, `lam`, `forallE`. -/
theorem taBin_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : TaGoOK dn fe vis k) (g : Word)
    (mkW : Mem → Word → Word → Option (Word × Mem)) (iop : EIdx → EIdx → AM EIdx)
    (hmk : ∀ m a2 x2, rpMkW m g a2 x2 0 0 0 = mkW m a2 x2)
    (hst : ∀ (m m' : Mem) (a : AState) (u v r : Word), StageR dn vis fe m a → mkW m u v = some (r, m') →
      ∃ a', (iop (decE u) (decE v)).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m')
    (hlow : ∀ (m m' : Mem) (u v r : Word), mkW m u v = some (r, m') → LowFr m m')
    (m : Mem) (a : AState) (no nl lvls ho hl f1 x y : Word) (names : List NIdx) (holes : List EIdx)
    (mp : Std.HashMap EIdx EIdx) (hS : StageR dn vis fe m a) (hx : H x) (hy : H y) (hlv : H lvls)
    (hI : TaIn m no nl ho hl names holes) (hM : taMR m mp) :
    Sim (taB1 k no nl lvls ho hl f1 g y (taGoW k m no nl lvls ho hl f1 x)) (do
        let (t2, mm) ← ConRon.Arena.targetAbsGo names (decI lvls) holes mp f1.toNat (decE x)
        let (b2, m2) ← ConRon.Arena.targetAbsGo names (decI lvls) holes mm f1.toNat (decE y)
        let r ← iop t2 b2
        pure (r, m2) : AM (EIdx × Std.HashMap EIdx EIdx)) a (TaQ dn fe vis m) := by
  refine Sim.bindK (by rw [taB1]) (fun _ _ => by rw [taB1]) (ih m a _ _ _ _ _ f1 x _ _ mp hS hx hlv hI hM) ?_
  rintro a2 ⟨t2, mp1⟩ m1 a1 ⟨rfl, hS1, hg1, hM1⟩
  refine Sim.bindK (by rw [taB2]) (fun _ _ => by rw [taB2])
    (ih m1 a1 _ _ _ _ _ f1 y _ _ mp1 hS1 hy hlv (hI.grow hg1) hM1) ?_
  rintro x2 ⟨b2, mp2⟩ m2 a2' ⟨rfl, hS2, hg2, hM2⟩
  intro r m' hn
  rw [hmk] at hn
  obtain ⟨a3, hr3, hS3, hg3⟩ := hst m2 m' a2' a2 x2 r hS2 hn
  exact ⟨(decE r, mp2), a3, by rw [StateT.run_bind, hr3]; rfl, rfl, hS3, (hg1.trans hg2).trans hg3,
    taMR_low (hlow m2 m' a2 x2 r hn) hM2⟩

theorem taLet_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : TaGoOK dn fe vis k)
    (m : Mem) (a : AState) (no nl lvls ho hl f1 x y z : Word) (names : List NIdx) (holes : List EIdx)
    (mp : Std.HashMap EIdx EIdx) (hS : StageR dn vis fe m a) (hx : H x) (hy : H y) (hz : H z) (hlv : H lvls)
    (hI : TaIn m no nl ho hl names holes) (hM : taMR m mp) :
    Sim (taL1 k no nl lvls ho hl f1 y z (taGoW k m no nl lvls ho hl f1 x)) (do
        let (t2, mm) ← ConRon.Arena.targetAbsGo names (decI lvls) holes mp f1.toNat (decE x)
        let (v2, m2) ← ConRon.Arena.targetAbsGo names (decI lvls) holes mm f1.toNat (decE y)
        let (b2, m3) ← ConRon.Arena.targetAbsGo names (decI lvls) holes m2 f1.toNat (decE z)
        let r ← internLetEE t2 v2 b2
        pure (r, m3) : AM (EIdx × Std.HashMap EIdx EIdx)) a (TaQ dn fe vis m) := by
  refine Sim.bindK (by rw [taL1]) (fun _ _ => by rw [taL1]) (ih m a _ _ _ _ _ f1 x _ _ mp hS hx hlv hI hM) ?_
  rintro a2 ⟨t2, mp1⟩ m1 a1 ⟨rfl, hS1, hg1, hM1⟩
  refine Sim.bindK (by rw [taL2]) (fun _ _ => by rw [taL2])
    (ih m1 a1 _ _ _ _ _ f1 y _ _ mp1 hS1 hy hlv (hI.grow hg1) hM1) ?_
  rintro x2 ⟨v2, mp2⟩ m2 a2' ⟨rfl, hS2, hg2, hM2⟩
  have hg12 := hg1.trans hg2
  refine Sim.bindK (by rw [taL3]) (fun _ _ => by rw [taL3])
    (ih m2 a2' _ _ _ _ _ f1 z _ _ mp2 hS2 hz hlv (hI.grow hg12) hM2) ?_
  rintro c2 ⟨b2, mp3⟩ m3 a3' ⟨rfl, hS3, hg3, hM3⟩
  intro r m' hn
  rw [rpMkW_let] at hn
  obtain ⟨a4, hr4, hS4, hg4⟩ := mkLet_stage hS3 a2 x2 c2 hn
  have hr4' : (internLetEE (decE a2) (decE x2) (decE c2)).run a3' = .ok (decE r, a4) := hr4
  exact ⟨(decE r, mp3), a4, by rw [StateT.run_bind, hr4']; rfl, rfl, hS4, (hg12.trans hg3).trans hg4,
    taMR_low (mkLetW_low hn) hM3⟩

theorem taProj_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : TaGoOK dn fe vis k)
    (m : Mem) (a : AState) (no nl lvls ho hl f1 x y z : Word) (names : List NIdx) (holes : List EIdx)
    (mp : Std.HashMap EIdx EIdx) (hS : StageR dn vis fe m a) (hz : H z) (hlv : H lvls)
    (hI : TaIn m no nl ho hl names holes) (hM : taMR m mp) :
    Sim (taP1 x y (taGoW k m no nl lvls ho hl f1 z)) (do
        let (x2, mm) ← ConRon.Arena.targetAbsGo names (decI lvls) holes mp f1.toNat (decE z)
        let r ← internProjE (decI x) y.toNat x2
        pure (r, mm) : AM (EIdx × Std.HashMap EIdx EIdx)) a (TaQ dn fe vis m) := by
  refine Sim.bindK (by rw [taP1]) (fun _ _ => by rw [taP1]) (ih m a _ _ _ _ _ f1 z _ _ mp hS hz hlv hI hM) ?_
  rintro a2 ⟨t2, mp1⟩ m1 a1 ⟨rfl, hS1, hg1, hM1⟩
  intro r m' hn
  rw [rpMkW_proj] at hn
  obtain ⟨a3, hr3, hS3, hg3⟩ := mkProj_stage hS1 x y a2 hn
  have hr3' : (internProjE (decI x) y.toNat (decE a2)).run a1 = .ok (decE r, a3) := hr3
  exact ⟨(decE r, mp1), a3, by rw [StateT.run_bind, hr3']; rfl, rfl, hS3, hg1.trans hg3, taMR_low (mkProjW_low hn) hM1⟩

theorem taNode_arm (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : TaGoOK dn fe vis k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v) (hnv : NodeVr v)
    (m : Mem) (a : AState) (no nl lvls ho hl f1 h : Word) (names : List NIdx) (holes : List EIdx)
    (mp : Std.HashMap EIdx EIdx) (hS : StageR dn vis fe m a) (hlv : H lvls)
    (hI : TaIn m no nl ho hl names holes) (hM : taMR m mp) :
    Sim (taNodeW (k + 1) m no nl lvls ho hl f1 (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0)) (taArm names (decI lvls) holes mp f1.toNat (decE h) v) a
      (TaQ dn fe vis m) := by
  cases v with
  | app f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, rfl, hy, rfl⟩ := hvr
    rw [hg, taNodeW_bin k m no nl lvls ho hl f1 4 _ _ _ (Or.inl rfl)]
    exact taBin_ok dn fe vis k ih 4 (fun m a b => mkAppW m a b) internAppE (fun m a2 x2 => by simp [rpMkW])
      (fun m m' a u v r hS hI => mkApp_stage hS u v hI) (fun m m' u v r hI => mkAppW_low hI)
      m a no nl lvls ho hl f1 _ _ names holes mp hS hx hy hlv hI hM
  | lam f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, rfl, hy, rfl⟩ := hvr
    rw [hg, taNodeW_bin k m no nl lvls ho hl f1 5 _ _ _ (Or.inr (Or.inl rfl))]
    exact taBin_ok dn fe vis k ih 5 (fun m a b => mkLamW m a b) internLamE (fun m a2 x2 => by simp [rpMkW])
      (fun m m' a u v r hS hI => mkLam_stage hS u v hI) (fun m m' u v r hI => mkLamW_low hI)
      m a no nl lvls ho hl f1 _ _ names holes mp hS hx hy hlv hI hM
  | forallE f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, rfl, hy, rfl⟩ := hvr
    rw [hg, taNodeW_bin k m no nl lvls ho hl f1 6 _ _ _ (Or.inr (Or.inr rfl))]
    exact taBin_ok dn fe vis k ih 6 (fun m a b => mkForallW m a b) internForallEE
      (fun m a2 x2 => by simp [rpMkW])
      (fun m m' a u v r hS hI => mkForall_stage hS u v hI) (fun m m' u v r hI => mkForallW_low hI)
      m a no nl lvls ho hl f1 _ _ names holes mp hS hx hy hlv hI hM
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, rfl, hy, rfl, hz, rfl⟩ := hvr
    rw [hg, taNodeW_let]
    exact taLet_ok dn fe vis k ih m a no nl lvls ho hl f1 _ _ _ names holes mp hS hx hy hz hlv hI hM
  | proj s i e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, rfl, rfl, hz, rfl⟩ := hvr
    rw [hg, taNodeW_proj k m no nl lvls ho hl f1 9 _ _ _ (by decide) (by decide)]
    exact taProj_ok dn fe vis k ih m a no nl lvls ho hl f1 _ _ _ names holes mp hS hz hlv hI hM
  | bvar _ | sort _ | const _ _ | lit _ | fvar _ _ => exact False.elim hnv

theorem taTwin_node (names : List NIdx) (lvls : LsIdx) (holes : List EIdx) (memo : Std.HashMap EIdx EIdx)
    (fuel : Nat) (h : EIdx) (a : AState) (v : ENodeView) (hv : a.store.view h = some v) (hnv : NodeVr v) :
    (ConRon.Arena.targetAbsGo names lvls holes memo (fuel + 1) h).run a =
      ((match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← taArm names lvls holes memo fuel h v
          pure (r, m.insert h r) : AM (EIdx × Std.HashMap EIdx EIdx)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | (rw [targetAbsGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind])

theorem taGo_nodeCase (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (j : Nat)
    (ih : ∀ k, k + 1 < j + 1 → TaGoOK dn fe vis k) (m : Mem) (a : AState)
    (no nl lvls ho hl f h : Word) (names : List NIdx) (holes : List EIdx) (mp : Std.HashMap EIdx EIdx) (F : Nat)
    (hF : f.toNat = F + 1) (hf0 : f ≠ 0) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVr v) (hv : a.store.view (decE h) = some v) (hvl : vl ≠ [])
    (hgs : vl.headD 0 = 4 ∨ vl.headD 0 = 5 ∨ vl.headD 0 = 6 ∨ vl.headD 0 = 7 ∨ vl.headD 0 = 9)
    (hS : StageR dn vis fe m a) (hh : H h) (hlv : H lvls)
    (hI : TaIn m no nl ho hl names holes) (hM : taMR m mp) :
    Sim (taG1 j m no nl lvls ho hl f h vl)
      (ConRon.Arena.targetAbsGo names (decI lvls) holes mp (F + 1) (decE h)) a (TaQ dn fe vis m) := by
  have hnl : ¬ (vl.headD 0 = 0 ∨ vl.headD 0 = 1 ∨ vl.headD 0 = 2 ∨ vl.headD 0 = 8) := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  have hn3 : ¬ vl.headD 0 = 3 := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  rw [taG1_node j m no nl lvls ho hl f h vl hvl hnl hn3]
  refine rcSim_ofRun (taTwin_node _ _ _ _ _ _ a v hv hnv) ?_
  by_cases hfr : mfindG taSch m h 0 = []
  · rw [taG3_abort j m no nl lvls ho hl f h vl _ hfr]; exact Sim.of_none
  by_cases hhit : (mfindG taSch m h 0).headD 0 ≠ 0
  · rw [taG3_hit j m no nl lvls ho hl f h vl _ hfr hhit]
    have hmem := memoRG_hit taSch bmKey (fun w : Word => decE w) m mp hM h 0 hfr hhit ⟨hh, rfl⟩
    change mp[decE h]? = _ at hmem
    simp only [hmem]
    exact Sim.ret ⟨rfl, hS, IWGrow.refl _, hM⟩
  rw [taG3_miss j m no nl lvls ho hl f h vl _ hfr hhit]
  have hmiss := memoRG_miss taSch bmKey (fun w : Word => decE w) m mp hM h 0 ⟨hh, rfl⟩ hfr (by simpa using hhit)
  change mp[decE h]? = _ at hmiss
  simp only [hmiss]
  cases j with
  | zero => simp only [taNodeW, taG4]; exact Sim.of_none
  | succ k =>
  have hF1 : (f - 1).toNat = F := by rw [toNat_sub_one' hf0, hF]; rfl
  rw [← hF1]
  refine Sim.bindK (by rw [taG4]) (fun _ _ => by rw [taG4]) (taNode_arm dn fe vis k (ih k (by omega)) vl v
    hvr hnv m a no nl lvls ho hl (f - 1) h names holes mp hS hlv hI hM) ?_
  rintro rn ⟨r1, mp1⟩ m1 a1 ⟨rfl, hS1, hg1, hM1⟩
  rcases hset : msetG taSch m1 h 0 rn with _ | m2 <;> simp only [taG5]
  · exact Sim.of_none
  obtain ⟨hS2, hg2⟩ := StageR.frame_hi hS1 (msetG_frame taSch taSch_wf m1 m2 h 0 rn hset)
    (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp [taSch] at hx; subst hx; decide) (by decide) (by simp [taSch])
  exact Sim.ret ⟨rfl, hS2, hg1.trans hg2,
    memoRG_set taSch taSch_wf bmKey (fun w : Word => decE w) m1 mp1 hM1 h 0 rn ⟨hh, rfl⟩ m2 hset⟩

theorem taGo_step_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (j : Nat)
    (ih : ∀ k, k + 1 < j + 1 → TaGoOK dn fe vis k) : TaGoOK dn fe vis (j + 1) := by
  intro m a no nl lvls ho hl f h names holes mp hS hh hlv hI hM
  by_cases hf0 : f = 0
  · rw [taGoW_abort j m no nl lvls ho hl f h hf0]; exact Sim.of_none
  rw [taGoW_view j m no nl lvls ho hl f h hf0]
  obtain ⟨F, hF⟩ : ∃ F, f.toNat = F + 1 := ⟨f.toNat - 1, by have := toNat_ne_zero' hf0; omega⟩
  rw [hF]
  cases hvl : eViewW m h with
  | nil => simp [taG1]; exact Sim.of_none
  | cons g vt =>
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hS.1.arena.1 h (by rw [hvl]; simp)
    rw [hvl] at hvr
    cases v with
    | bvar _ | sort _ | lit _ | fvar _ _ =>
      rw [targetAbsGo_succ']
      refine Sim.bind_twin (view_run _ a _ hv) ?_
      simp only [ViewR] at hvr
      rw [taG1_leaf j m no nl lvls ho hl f h _ (by simp) (by
        first | exact Or.inl hvr.1 | exact Or.inr (Or.inl hvr.1) | exact Or.inr (Or.inr (Or.inl hvr.1)) | exact Or.inr (Or.inr (Or.inr hvr)))]
      exact Sim.ret ⟨rfl, hS, IWGrow.refl _, hM⟩
    | const nn' us' =>
      simp only [ViewR, getD1_eq', getD2_eq] at hvr
      obtain ⟨hg3, hx, hdx, hy, hdy⟩ := hvr
      rw [taG1_const j m no nl lvls ho hl f h _ (by simp) (by rw [hg3]; decide) hg3, targetAbsGo_succ']
      refine Sim.bind_twin (view_run _ a _ hv) ?_
      intro r m' hb
      obtain ⟨rfl, hr⟩ := taCW_ok j hb hlv hx hy hI.1 (hS.lt64 hI.2.1) hI.2.2.1 (hS.lt64 hI.2.2.2)
      exact ⟨_, a, rfl, by rw [hr, ← hdx, ← hdy], hS, IWGrow.refl _, hM⟩
    | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ | proj _ _ _ =>
      exact taGo_nodeCase dn fe vis j ih m a no nl lvls ho hl f h names holes mp F hF hf0 _ _ hvr trivial hv
        (by simp) (by have := hvr.1; simp only [List.headD_cons] at this ⊢; simp [this]) hS hh hlv hI hM

theorem taGoOK (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) : TaGoOK dn fe vis n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro m a no nl lvls ho hl f h names holes mp; simp only [taGoW]; exact fun _ _ _ _ _ => Sim.of_none
    | succ j => exact taGo_step_ok dn fe vis j (fun k hk => ih k (by omega))

theorem taAW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl lvls ho hl e r : Word) (names : List NIdx) (holes : List EIdx)
    (mp0 : Std.HashMap EIdx EIdx)
    (hb : taAW n m no nl lvls ho hl e = some (r, m')) (hS : StageR dn vis fe m a) (he : H e) (hlv : H lvls)
    (hdec : decHL m no.toNat nl.toNat = some names) (hit : no.toNat + nl.toNat ≤ iwTop m)
    (hho : decHL m ho.toNat hl.toNat = some holes) (hht : ho.toNat + hl.toNat ≤ iwTop m) (hM : taMR m mp0) :
    ∃ a' mp1, (ConRon.Arena.targetAbs names (decI lvls) holes (decE e)).run a = .ok (decE r, a') ∧
      taMR m' mp1 ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  by_cases h0 : rdW (m.arr64 CTL) taSch.cs + 2 = 0
  · simp [taAW, h0] at hb
  rw [taAW_eq n m no nl lvls ho hl e h0] at hb
  have hf0 := mclearG_frame taSch m
  have hM0 := memoRG_clear taSch taSch_wf bmKey (fun w : Word => decE w) m mp0 hM h0
  obtain ⟨hS0, hg0⟩ := StageR.frame_hi hS hf0 (by intro b hb; simp at hb)
    (by intro x hx; simp [taSch] at hx; rcases hx with rfl | rfl <;> decide) (by simp) (by simp [taSch])
  obtain ⟨⟨t, mp1⟩, a1, hrun, rfl, hS1, hg1, hM1⟩ := taGoOK dn fe vis n _ a no nl lvls ho hl CWF e names holes ∅
    hS0 he hlv (TaIn.grow ⟨hdec, hit, hho, hht⟩ hg0) hM0 _ _ hb
  rw [CWF_eq] at hrun
  refine ⟨a1, mp1, ?_, hM1, hS1, hg0.trans hg1⟩
  simp only [ConRon.Arena.targetAbs, StateT.run_bind]
  rw [hrun]
  rfl

section census
variable (p : Prog) (L : TaLook p)
include L

/-- **`target_abs_go` (with `target_abs_const`, `target_abs_node`) refines `targetAbsGo`**, from a memo
related to the twin's. -/
@[refines ConRon.Arena.targetAbsGo]
theorem targetAbsGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl lvls ho hl f h : Word) (names : List NIdx) (holes : List EIdx)
    (mp : Std.HashMap EIdx EIdx) (hh : H h) (hlv : H lvls) (hS : StageR dn vis fe s₀.mem a₀)
    (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem)
    (hho : decHL s₀.mem ho.toNat hl.toNat = some holes) (hht : ho.toNat + hl.toNat ≤ iwTop s₀.mem)
    (hM : taMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_abs_go" [no, nl, lvls, ho, hl, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetAbsGo names (decI lvls) holes mp f.toNat (decE h)) a₀ ∧
      decE (r.headD 0) = (AM.res (ConRon.Arena.targetAbsGo names (decI lvls) holes mp f.toNat (decE h)) a₀).1 ∧
      taMR s'.mem (AM.res (ConRon.Arena.targetAbsGo names (decI lvls) holes mp f.toNat (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetAbsGo names (decI lvls) holes mp f.toNat (decE h)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post ((taGo_spec p L n).1 s₀ no nl lvls ho hl f h) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨⟨t, mp'⟩, a', hrun, rfl, hS', hg, hM'⟩ := taGoOK dn fe vis n _ a₀ no nl lvls ho hl f h names holes mp hS
    hh hlv ⟨hdec, hit, hho, hht⟩ hM _ _ hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hres], by rw [hres]; exact hM', by rw [hst]; exact hS', hg⟩

/-- **`target_abs` refines `targetAbs`**: clear the `ta` memo (any well-formed one on entry), one
memoised walk. -/
@[refines ConRon.Arena.targetAbs]
theorem targetAbs_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl lvls ho hl e : Word) (names : List NIdx) (holes : List EIdx)
    (mp0 : Std.HashMap EIdx EIdx) (he : H e) (hlv : H lvls) (hS : StageR dn vis fe s₀.mem a₀)
    (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem)
    (hho : decHL s₀.mem ho.toNat hl.toNat = some holes) (hht : ho.toNat + hl.toNat ≤ iwTop s₀.mem)
    (hM : taMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_abs" [no, nl, lvls, ho, hl, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetAbs names (decI lvls) holes (decE e)) a₀ ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.targetAbs names (decI lvls) holes (decE e)) a₀ ∧
      (∃ mp1, taMR s'.mem mp1) ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetAbs names (decI lvls) holes (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (targetAbs_spec p L n s₀ no nl lvls ho hl e) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨a', mp1, hrun, hM', hS', hg⟩ := taAW_ok n dn fe vis _ _ a₀ no nl lvls ho hl e _ names holes mp0 hm hS he hlv
    hdec hit hho hht hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hres], ⟨mp1, hM'⟩, by rw [hst]; exact hS', hg⟩

end census

end L.Ind
