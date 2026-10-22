import ConAgua.Arena.IndSumSpec4
import ConAgua.Arena.IndPos2Spec

/-!
# Refinements of `IndSum`, fifth file (lane `indproofs`, helper `memo`)

The memoised walks of `IndSum.lean`: `mentions_const_go` / `mentions_const` (twins `mentionsConstGo`,
`mentionsConst`), `has_loose_b_var_b_*` and `struct_used_later_*`. The shape is `IndPos2Spec.lean`'s
`mentions_any_go` (`e_view`, a memo of `Bool`s keyed by the node).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `mentions_const_go`: the word model -/

mutual
def mcGoW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, T, h => mcG1 n m T h (eViewW m h)
def mcG1 (n : Nat) (m : Mem) (T h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 then some (0, m)
  else if v.headD 0 = 3 then some (if v.tail.headD 0 = T then 1 else 0, m)
  else mcG3 n m T h v (mfindG mcSch m h 0)
def mcG3 (n : Nat) (m : Mem) (T h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 MCM) (fr.tail.headD 0 * 4 + 3), m)
  else mcG4 h (mcNodeW n m T (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def mcG4 (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => mcG5 r (msetG mcSch m1 h 0 r)
def mcG5 (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 => some (r, m2)
def mcNodeW (n : Nat) (m : Mem) (T g x y z : Word) : Option (Word × Mem) :=
  if g = 1 then mcGoW n m T y
  else if g = 4 ∨ g = 5 ∨ g = 6 then mcB1 n T y (mcGoW n m T x)
  else if g = 7 then mcL1 n T y z (mcGoW n m T x)
  else mcP1 T x (mcGoW n m T z)
def mcB1 (n : Nat) (T y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => mcB2 b1 (mcGoW n m1 T y)
def mcB2 (b1 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b2, m2) => some (b1 ||| b2, m2)
def mcL1 (n : Nat) (T y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => mcL2 n T z b1 (mcGoW n m1 T y)
def mcL2 (n : Nat) (T z b1 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b2, m2) => mcL3 b1 b2 (mcGoW n m2 T z)
def mcL3 (b1 b2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b3, m3) => some (b1 ||| b2 ||| b3, m3)
def mcP1 (T x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => some ((if x = T then 1 else 0) ||| b1, m1)
end

section mcArms
variable (n : Nat) (m m1 m2 m3 : Mem) (T h g x y z b1 b2 b3 r : Word) (v fr : List Word)
theorem mcGoW_view : mcGoW (n + 1) m T h = mcG1 n m T h (eViewW m h) := by simp [mcGoW]
theorem mcG1_abort (hv : v = []) : mcG1 n m T h v = none := by simp [mcG1, hv]
theorem mcG1_leaf (hv : v ≠ []) (hg : v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8) :
    mcG1 n m T h v = some (0, m) := by simp only [mcG1]; rw [if_neg hv, if_pos hg]
theorem mcG1_const (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : v.headD 0 = 3) : mcG1 n m T h v = some (if v.tail.headD 0 = T then 1 else 0, m) := by
  simp only [mcG1]; rw [if_neg hv, if_neg hg, if_pos h3]
theorem mcG1_node (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : ¬ v.headD 0 = 3) : mcG1 n m T h v = mcG3 n m T h v (mfindG mcSch m h 0) := by
  simp only [mcG1]; rw [if_neg hv, if_neg hg, if_neg h3]
theorem mcG3_abort (hr : fr = []) : mcG3 n m T h v fr = none := by simp [mcG3, hr]
theorem mcG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    mcG3 n m T h v fr = some (rdW (m.arr64 MCM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [mcG3]; rw [if_neg hr, if_pos hh]
theorem mcG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    mcG3 n m T h v fr = mcG4 h (mcNodeW n m T (v.headD 0) (v.tail.headD 0)
      (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [mcG3]; rw [if_neg hr, if_neg hh]
theorem mcG4_some : mcG4 h (some (r, m1)) = mcG5 r (msetG mcSch m1 h 0 r) := by rw [mcG4]
theorem mcG5_some : mcG5 r (some m2) = some (r, m2) := by rw [mcG5]
theorem mcNodeW_fvar (hg : g = 1) : mcNodeW n m T g x y z = mcGoW n m T y := by simp [mcNodeW, hg]
theorem mcNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) : mcNodeW n m T g x y z =
    mcB1 n T y (mcGoW n m T x) := by
  have : ¬ g = 1 := by
    intro e; rcases hg with h | h | h <;> (rw [e] at h; exact absurd h (by decide))
  simp only [mcNodeW]; rw [if_neg this, if_pos hg]
theorem mcNodeW_let (hg : g = 7) : mcNodeW n m T g x y z = mcL1 n T y z (mcGoW n m T x) := by
  simp [mcNodeW, hg]
theorem mcNodeW_proj (hg1 : g ≠ 1) (hg2 : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (hg3 : g ≠ 7) :
    mcNodeW n m T g x y z = mcP1 T x (mcGoW n m T z) := by
  simp only [mcNodeW]; rw [if_neg hg1, if_neg hg2, if_neg hg3]
theorem mcB1_some : mcB1 n T y (some (b1, m1)) = mcB2 b1 (mcGoW n m1 T y) := by rw [mcB1]
theorem mcB2_some : mcB2 b1 (some (b2, m2)) = some (b1 ||| b2, m2) := by rw [mcB2]
theorem mcL1_some : mcL1 n T y z (some (b1, m1)) = mcL2 n T z b1 (mcGoW n m1 T y) := by rw [mcL1]
theorem mcL2_some : mcL2 n T z b1 (some (b2, m2)) = mcL3 b1 b2 (mcGoW n m2 T z) := by rw [mcL2]
theorem mcL3_some : mcL3 b1 b2 (some (b3, m3)) = some (b1 ||| b2 ||| b3, m3) := by rw [mcL3]
theorem mcP1_some : mcP1 T x (some (b1, m1)) = some ((if x = T then 1 else 0) ||| b1, m1) := by rw [mcP1]
end mcArms

attribute [ind_grind] mcGoW_view mcG1_abort mcG1_leaf mcG1_const mcG1_node mcG3_abort mcG3_hit
  mcG3_miss mcG4_some mcG5_some mcNodeW_fvar mcNodeW_bin mcNodeW_let mcNodeW_proj mcB1_some
  mcB2_some mcL1_some mcL2_some mcL3_some mcP1_some

section mcspec
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "mc_find" = some (memoFindG mcSch)) (hput : p.lookup "mc_put" = some (memoPutG mcSch))
  (hgo : p.lookup "mentions_const_go" = some mentionsConstGoL)

def McGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (T h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mentions_const_go" [T, h]
    ⦃fun r s' => LocEq s' s₀ ∧ mcGoW n s₀.mem T h = some (r.headD 0, s'.mem); ⊤⦄

set_option maxHeartbeats 2000000 in
include hv hf hput hgo in
theorem mcGo_step (n : Nat) (ih : McGoSpec p n) : McGoSpec p (n + 1) := by
  unfold McGoSpec at ih
  intro s₀ T h
  rw [invoke_eq _ hgo]
  simp only [callFn, mentionsConstGoL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p hv n, memoFindG_spec mcSch p _ hf n,
      memoPutG_spec mcSch p _ hput n, ih] <;> finish (gen := 20)

include hv hf hput hgo in
theorem mcGo_spec (n : Nat) : McGoSpec p n := by
  induction n with
  | zero => intro s₀ T h; rw [invoke_eq _ hgo]; simp only [callFn, mentionsConstGoL]; vcgen [exec] <;> grind
  | succ n ih => exact mcGo_step p hv hf hput hgo n ih

end mcspec

/-! ## `mentions_const_go`: the relation to the twin -/

theorem mcSch_wf : mcSch.WF := ⟨by decide, by decide⟩

/-- The word-valued memo relation of the `mentionsConst` walk. -/
abbrev mcMR (m : Mem) (mp : Std.HashMap EIdx Bool) : Prop :=
  MemoRG mcSch bmKey (fun w : Word => w != 0) m mp

theorem mcFrame_arena {m m' : Mem} {a : AState} (hf : MemFrame [MCM] [217] m m') (hR : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame (fun b hb => by simp at hb; subst hb; simp [arenaArrs, storeArrs, memoArrs, MCM])
    (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf hR

theorem mcFrame_iw {m m' : Mem} (hf : MemFrame [MCM] [217] m m') : m'.arr64 IW = m.arr64 IW :=
  hf.1 IW (by decide) (by decide)

/-- The twin's arms of a node view. -/
def mcArm (T : NIdx) (memo : Std.HashMap EIdx Bool) (fuel : Nat) :
    ENodeView → AM (Bool × Std.HashMap EIdx Bool)
  | .fvar _ ty => ConRon.Arena.mentionsConstGo T memo fuel ty
  | .app f a => do
    let (b1, m) ← ConRon.Arena.mentionsConstGo T memo fuel f
    let (b2, m2) ← ConRon.Arena.mentionsConstGo T m fuel a
    pure (b1 || b2, m2)
  | .lam ty body => do
    let (b1, m) ← ConRon.Arena.mentionsConstGo T memo fuel ty
    let (b2, m2) ← ConRon.Arena.mentionsConstGo T m fuel body
    pure (b1 || b2, m2)
  | .forallE ty body => do
    let (b1, m) ← ConRon.Arena.mentionsConstGo T memo fuel ty
    let (b2, m2) ← ConRon.Arena.mentionsConstGo T m fuel body
    pure (b1 || b2, m2)
  | .letE ty val body => do
    let (b1, m) ← ConRon.Arena.mentionsConstGo T memo fuel ty
    let (b2, m2) ← ConRon.Arena.mentionsConstGo T m fuel val
    let (b3, m3) ← ConRon.Arena.mentionsConstGo T m2 fuel body
    pure (b1 || b2 || b3, m3)
  | .proj s _ sub => do
    let (b, m) ← ConRon.Arena.mentionsConstGo T memo fuel sub
    pure (s == T || b, m)
  | _ => pure (false, memo)

theorem mentionsConstGo_succ' (T : NIdx) (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx) :
    ConRon.Arena.mentionsConstGo T memo (fuel + 1) h = (do
      let v ← view h
      match v with
      | .bvar _ => pure (false, memo)
      | .sort _ => pure (false, memo)
      | .lit _ => pure (false, memo)
      | .const n _ => pure (n == T, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← mcArm T memo fuel v
          pure (r, m.insert h r)) := by
  rw [ConRon.Arena.mentionsConstGo.eq_2]
  congr 1
  funext v
  cases v <;> first | rfl | (simp only [mcArm, bind_assoc, pure_bind]; rfl)

def McGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (T h r : Word) (mp : Std.HashMap EIdx Bool) (F : Nat), n ≤ F →
    mcGoW n m T h = some (r, m') → ArenaR m a → H h → H T → mcMR m mp →
    ∃ b mp', (ConRon.Arena.mentionsConstGo (decI T) mp F (decE h)).run a =
        .ok ((b, mp'), a) ∧ (r != 0) = b ∧ mcMR m' mp' ∧ MemFrame [MCM] [217] m m'

theorem word_or_ne (a b : Word) : ((a ||| b) != 0) = ((a != 0) || (b != 0)) := by
  rw [Bool.eq_iff_iff]
  simp [UInt64.or_eq_zero_iff]
  by_cases h1 : a = 0 <;> by_cases h2 : b = 0 <;> simp [h1, h2]

theorem mcNodeBin_ok (n : Nat) (ih : McGoOK n) (m m' : Mem) (a : AState) (T g x y z r : Word)
    (mp : Std.HashMap EIdx Bool) (F : Nat) (hF : n ≤ F) (hg : g = 4 ∨ g = 5 ∨ g = 6) (hx : H x) (hy : H y)
    (hT : H T) (hn : mcNodeW n m T g x y z = some (r, m')) (hA : ArenaR m a) (hM : mcMR m mp) :
    ∃ b mp', (do
        let (b1, m) ← ConRon.Arena.mentionsConstGo (decI T) mp F (decE x)
        let (b2, m2) ← ConRon.Arena.mentionsConstGo (decI T) m F (decE y)
        pure (b1 || b2, m2) : AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ mcMR m' mp' ∧ MemFrame [MCM] [217] m m' := by
  rw [mcNodeW_bin n m T g x y z hg] at hn
  cases h1 : mcGoW n m T x with
  | none => rw [h1] at hn; simp [mcB1] at hn
  | some p1 =>
    obtain ⟨b1w, m1⟩ := p1
    rw [h1, mcB1_some] at hn
    cases h2 : mcGoW n m1 T y with
    | none => rw [h2] at hn; simp [mcB2] at hn
    | some p2 =>
      obtain ⟨b2w, m2⟩ := p2
      rw [h2, mcB2_some] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a T x b1w mp F hF h1 hA hx hT hM
      obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m2 a T y b2w mp1 F hF h2 (mcFrame_arena hf1 hA) hy hT hM1
      refine ⟨c1 || c2, mp2, ?_, ?_, hM2, hf1.trans hf2⟩
      · simp only [StateT.run_bind]
        rw [hr1]
        simp only [except_ok_bind, StateT.run_bind]
        rw [hr2]
        simp only [except_ok_bind]
        rfl
      · rw [← hb1, ← hb2]
        rw [word_or_ne]

theorem mcNodeLet_ok (n : Nat) (ih : McGoOK n) (m m' : Mem) (a : AState) (T x y z r : Word)
    (mp : Std.HashMap EIdx Bool) (F : Nat) (hF : n ≤ F) (hx : H x) (hy : H y) (hz : H z) (hT : H T)
    (hn : mcNodeW n m T 7 x y z = some (r, m')) (hA : ArenaR m a) (hM : mcMR m mp) :
    ∃ b mp', (do
        let (b1, m) ← ConRon.Arena.mentionsConstGo (decI T) mp F (decE x)
        let (b2, m2) ← ConRon.Arena.mentionsConstGo (decI T) m F (decE y)
        let (b3, m3) ← ConRon.Arena.mentionsConstGo (decI T) m2 F (decE z)
        pure (b1 || b2 || b3, m3) : AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ mcMR m' mp' ∧ MemFrame [MCM] [217] m m' := by
  rw [mcNodeW_let n m T 7 x y z rfl] at hn
  cases h1 : mcGoW n m T x with
  | none => rw [h1] at hn; simp [mcL1] at hn
  | some p1 =>
    obtain ⟨b1w, m1⟩ := p1
    rw [h1, mcL1_some] at hn
    cases h2 : mcGoW n m1 T y with
    | none => rw [h2] at hn; simp [mcL2] at hn
    | some p2 =>
      obtain ⟨b2w, m2⟩ := p2
      rw [h2, mcL2_some] at hn
      cases h3 : mcGoW n m2 T z with
      | none => rw [h3] at hn; simp [mcL3] at hn
      | some p3 =>
        obtain ⟨b3w, m3⟩ := p3
        rw [h3, mcL3_some] at hn
        simp only [Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a T x b1w mp F hF h1 hA hx hT hM
        obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m2 a T y b2w mp1 F hF h2 (mcFrame_arena hf1 hA) hy hT hM1
        obtain ⟨c3, mp3, hr3, hb3, hM3, hf3⟩ := ih m2 m3 a T z b3w mp2 F hF h3
          (mcFrame_arena (hf1.trans hf2) hA) hz hT hM2
        refine ⟨c1 || c2 || c3, mp3, ?_, ?_, hM3, (hf1.trans hf2).trans hf3⟩
        · simp only [StateT.run_bind]
          rw [hr1]
          simp only [except_ok_bind, StateT.run_bind]
          rw [hr2]
          simp only [except_ok_bind, StateT.run_bind]
          rw [hr3]
          simp only [except_ok_bind]
          rfl
        · rw [← hb1, ← hb2, ← hb3]
          rw [word_or_ne, word_or_ne]

theorem mcNodeProj_ok (n : Nat) (ih : McGoOK n) (m m' : Mem) (a : AState) (T x y z r : Word)
    (mp : Std.HashMap EIdx Bool) (F : Nat) (hF : n ≤ F) (hx : H x) (hz : H z) (hT : H T)
    (hn : mcNodeW n m T 9 x y z = some (r, m')) (hA : ArenaR m a) (hM : mcMR m mp) :
    ∃ b mp', (do
        let (b, m) ← ConRon.Arena.mentionsConstGo (decI T) mp F (decE z)
        pure (decI x == (decI T : NIdx) || b, m) :
          AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ mcMR m' mp' ∧ MemFrame [MCM] [217] m m' := by
  rw [mcNodeW_proj n m T 9 x y z (by decide) (by decide) (by decide)] at hn
  cases h1 : mcGoW n m T z with
  | none => rw [h1] at hn; simp [mcP1] at hn
  | some p1 =>
    obtain ⟨b1w, m1⟩ := p1
    rw [h1, mcP1_some] at hn
    simp only [Option.some.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a T z b1w mp F hF h1 hA hz hT hM
    refine ⟨(decI x == (decI T : NIdx)) || c1, mp1, ?_, ?_, hM1, hf1⟩
    · simp only [StateT.run_bind]
      rw [hr1]
      simp only [except_ok_bind]
      rfl
    · rw [← hb1, decI_beq' x T hx hT]
      rw [word_or_ne]
      by_cases e2 : x = T <;> simp [e2]

theorem mcNodeFVar_ok (n : Nat) (ih : McGoOK n) (m m' : Mem) (a : AState) (T x y z r : Word)
    (mp : Std.HashMap EIdx Bool) (F : Nat) (hF : n ≤ F) (hy : H y) (hT : H T)
    (hn : mcNodeW n m T 1 x y z = some (r, m')) (hA : ArenaR m a) (hM : mcMR m mp) :
    ∃ b mp', (ConRon.Arena.mentionsConstGo (decI T) mp F (decE y)).run a =
        .ok ((b, mp'), a) ∧ (r != 0) = b ∧ mcMR m' mp' ∧ MemFrame [MCM] [217] m m' := by
  rw [mcNodeW_fvar n m T 1 x y z rfl] at hn
  exact ih m m' a T y r mp F hF hn hA hy hT hM

theorem mcNode_arm (k : Nat) (ih : McGoOK k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeV v) (m m' : Mem) (a : AState) (T r : Word)
    (mp : Std.HashMap EIdx Bool) (F : Nat) (hF : k ≤ F)
    (hn : mcNodeW k m T (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0) = some (r, m'))
    (hA : ArenaR m a) (hT : H T) (hM : mcMR m mp) :
    ∃ b mp', (mcArm (decI T) mp F v).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ mcMR m' mp' ∧ MemFrame [MCM] [217] m m' := by
  cases v with
  | fvar i ty =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, -, hy, hdy⟩ := hvr
    rw [hg] at hn
    have := mcNodeFVar_ok k ih m m' a T _ _ _ r mp F hF hy hT hn hA hM
    rw [← hdy] at *
    simp only [mcArm]; exact this
  | app f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := mcNodeBin_ok k ih m m' a T _ _ _ _ r mp F hF (Or.inl hg) hx hy hT hn hA hM
    rw [hdx, hdy] at this
    simp only [mcArm]; exact this
  | lam f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := mcNodeBin_ok k ih m m' a T _ _ _ _ r mp F hF (Or.inr (Or.inl hg)) hx hy hT hn hA hM
    rw [hdx, hdy] at this
    simp only [mcArm]; exact this
  | forallE f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := mcNodeBin_ok k ih m m' a T _ _ _ _ r mp F hF (Or.inr (Or.inr hg)) hx hy hT hn hA hM
    rw [hdx, hdy] at this
    simp only [mcArm]; exact this
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := mcNodeLet_ok k ih m m' a T _ _ _ r mp F hF hx hy hz hT hn hA hM
    rw [hdx, hdy, hdz] at this
    simp only [mcArm]; exact this
  | proj s i e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, -, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := mcNodeProj_ok k ih m m' a T _ _ _ r mp F hF hx hz hT hn hA hM
    rw [hdz, hdx] at this
    simp only [mcArm]; exact this
  | bvar _ => exact False.elim hnv
  | sort _ => exact False.elim hnv
  | const _ _ => exact False.elim hnv
  | lit _ => exact False.elim hnv

theorem mcTwin_node (T : NIdx) (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx)
    (a : AState) (v : ENodeView) (hv : a.store.view h = some v) (hnv : NodeV v) :
    (ConRon.Arena.mentionsConstGo T memo (fuel + 1) h).run a =
      ((match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← mcArm T memo fuel v
          pure (r, m.insert h r) : AM (Bool × Std.HashMap EIdx Bool)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | rw [mentionsConstGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]

theorem mcGo_nodeCase (j : Nat) (ih : ∀ k, k < j + 1 → McGoOK k) (m m' : Mem) (a : AState)
    (T h r : Word) (mp : Std.HashMap EIdx Bool) (F : Nat)
    (hF : j ≤ F) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v) (hnv : NodeV v)
    (hv : a.store.view (decE h) = some v) (hvl : vl ≠ [])
    (hgs : vl.headD 0 = 1 ∨ vl.headD 0 = 4 ∨ vl.headD 0 = 5 ∨ vl.headD 0 = 6 ∨ vl.headD 0 = 7 ∨ vl.headD 0 = 9)
    (hb : mcG1 j m T h vl = some (r, m')) (hA : ArenaR m a) (hh : H h) (hT : H T)
    (hM : mcMR m mp) :
    ∃ b mp', (ConRon.Arena.mentionsConstGo (decI T) mp (F + 1) (decE h)).run a =
        .ok ((b, mp'), a) ∧ (r != 0) = b ∧ mcMR m' mp' ∧ MemFrame [MCM] [217] m m' := by
  have hnl : ¬ (vl.headD 0 = 0 ∨ vl.headD 0 = 2 ∨ vl.headD 0 = 8) := by
    rcases hgs with e | e | e | e | e | e <;> rw [e] <;> decide
  have hn3 : ¬ vl.headD 0 = 3 := by
    rcases hgs with e | e | e | e | e | e <;> rw [e] <;> decide
  rw [mcG1_node j m T h vl hvl hnl hn3] at hb
  rw [mcTwin_node _ _ _ _ a v hv hnv]
  by_cases hfr : mfindG mcSch m h 0 = []
  · rw [mcG3_abort j m T h vl _ hfr] at hb; simp at hb
  by_cases hhit : (mfindG mcSch m h 0).headD 0 ≠ 0
  · rw [mcG3_hit j m T h vl _ hfr hhit] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have hmem := memoRG_hit mcSch bmKey (fun w : Word => w != 0) m mp hM h 0 hfr hhit ⟨hh, rfl⟩
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmem
    refine ⟨_, mp, ?_, rfl, hM, MemFrame.refl _ _ _⟩
    simp only [hmem]; rfl
  · rw [mcG3_miss j m T h vl _ hfr hhit] at hb
    have hmiss := memoRG_miss mcSch bmKey (fun w : Word => w != 0) m mp hM h 0 ⟨hh, rfl⟩ hfr (by simpa using hhit)
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmiss
    cases hnode : mcNodeW j m T (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
        (vl.tail.tail.tail.headD 0) with
    | none => rw [hnode] at hb; simp [mcG4] at hb
    | some pn =>
      obtain ⟨rn, m1⟩ := pn
      rw [hnode, mcG4_some] at hb
      cases hset : msetG mcSch m1 h 0 rn with
      | none => rw [hset] at hb; simp [mcG5] at hb
      | some m2 =>
        rw [hset, mcG5_some] at hb
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨bb, mp1, hr1, hbb, hM1, hfr1⟩ := mcNode_arm j (ih j (by omega)) vl v hvr hnv m m1 a T rn
          mp F hF hnode hA hT hM
        have hset' := memoRG_set mcSch mcSch_wf bmKey (fun w : Word => w != 0) m1 mp1 hM1 h 0 rn ⟨hh, rfl⟩ m2 hset
        have hfs : MemFrame [MCM] [217] m1 m2 := by
          have := msetG_frame mcSch mcSch_wf m1 m2 h 0 rn hset
          exact this.mono (by simp [mcSch]) (by simp [mcSch])
        refine ⟨bb, mp1.insert (decE h) bb, ?_, hbb, ?_, hfr1.trans hfs⟩
        · rw [hmiss]
          simp only [StateT.run_bind]
          rw [hr1]
          simp only [except_ok_bind]
          rfl
        · rw [← hbb]; exact hset'

theorem mcGo_step_ok (j : Nat) (ih : ∀ k, k < j + 1 → McGoOK k) : McGoOK (j + 1) := by
  intro m m' a T h r mp F hFj hb hA hh hT hM
  rw [mcGoW_view j m T h] at hb
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hF : j ≤ F := by omega
  cases hvl : eViewW m h with
  | nil => rw [hvl] at hb; simp [mcG1] at hb
  | cons g vt =>
    have hne : eViewW m h ≠ [] := by rw [hvl]; simp
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA h hne
    rw [hvl] at hvr hb
    cases v with
    | bvar i =>
      rw [mentionsConstGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 0 := by simpa [ViewR] using hvr.1
      rw [mcG1_leaf j m T h _ (by simp) (Or.inl hg0)] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | sort u =>
      rw [mentionsConstGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 2 := by simpa [ViewR] using hvr.1
      rw [mcG1_leaf j m T h _ (by simp) (Or.inr (Or.inl hg0))] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | lit l =>
      rw [mentionsConstGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 8 := by simpa [ViewR] using hvr
      rw [mcG1_leaf j m T h _ (by simp) (Or.inr (Or.inr hg0))] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | const nn us =>
      rw [mentionsConstGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      simp only [ViewR, getD1_eq'] at hvr
      obtain ⟨hg3, hx, hdx, -⟩ := hvr
      have hg3' : (g :: vt).headD 0 = 3 := hg3
      rw [mcG1_const j m T h _ (by simp) (by rw [hg3']; decide) hg3'] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨nn == decI T, mp, ?_, ?_, hM, MemFrame.refl _ _ _⟩
      · rfl
      · rw [← hdx, decI_beq' _ T hx hT]
        generalize (g :: vt).tail.headD 0 = xx
        by_cases e : xx = T <;> simp [e]
    | fvar i ty => exact mcGo_nodeCase j ih m m' a T h r mp F hF _ _ hvr trivial hv (by simp) (Or.inl hvr.1) hb hA hh hT hM
    | app f' x' => exact mcGo_nodeCase j ih m m' a T h r mp F hF _ _ hvr trivial hv (by simp) (Or.inr (Or.inl hvr.1)) hb hA hh hT hM
    | lam f' x' => exact mcGo_nodeCase j ih m m' a T h r mp F hF _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inl hvr.1))) hb hA hh hT hM
    | forallE f' x' => exact mcGo_nodeCase j ih m m' a T h r mp F hF _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inr (Or.inl hvr.1)))) hb hA hh hT hM
    | letE t v' b' => exact mcGo_nodeCase j ih m m' a T h r mp F hF _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvr.1))))) hb hA hh hT hM
    | proj s i e => exact mcGo_nodeCase j ih m m' a T h r mp F hF _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hvr.1))))) hb hA hh hT hM

theorem mcGoOK (n : Nat) : McGoOK n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro m m' a T h r mp F _ hb; simp [mcGoW] at hb
    | succ j => exact mcGo_step_ok j (fun k hk => ih k (by omega))

section mcCensus
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "mc_find" = some (memoFindG mcSch)) (hput : p.lookup "mc_put" = some (memoPutG mcSch))
  (hgo : p.lookup "mentions_const_go" = some mentionsConstGoL)
include hv hf hput hgo

/-- **`mentions_const_go` refines `mentionsConstGo`**, from a memo related to the twin's, at any twin
fuel at least the call depth (the L walk has no fuel: the exec fuel bounds the depth). -/
@[refines ConRon.Arena.mentionsConstGo]
theorem mentionsConstGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis T h : Word) (mp : Std.HashMap EIdx Bool) (F : Nat) (hFn : n ≤ F) (hh : H h)
    (hT : H T) (hS : StageR dn vis fe s₀.mem a₀) (hM : mcMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mentions_const_go" [T, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.mentionsConstGo (decI T) mp F (decE h)) a₀ ∧
      AM.st (ConRon.Arena.mentionsConstGo (decI T) mp F (decE h)) a₀ = a₀ ∧
      (r.headD 0 != 0) = (AM.res (ConRon.Arena.mentionsConstGo (decI T) mp F (decE h)) a₀).1 ∧
      mcMR s'.mem (AM.res (ConRon.Arena.mentionsConstGo (decI T) mp F (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (mcGo_spec p hv hf hput hgo n s₀ T h) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, mp', hrun, hb, hM', hfr⟩ := mcGoOK n _ _ a₀ T h _ mp F hFn hm hS.1.arena.1 hh hT hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  obtain ⟨hS', hg⟩ := StageR.frame_hi hS hfr (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp at hx; subst hx; decide) (by decide) (by decide)
  refine ⟨hl, hok, hst, by rw [hres]; exact hb, by rw [hres]; exact hM', hS', hg⟩

end mcCensus

/-! ## `mentions_const` -/

def mcConstW (n : Nat) (m : Mem) (T e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) mcSch.cs + 2 = 0 then none else mcGoW n (mclearG mcSch m) T e

theorem mcConstW_eq (n : Nat) (m : Mem) (T e : Word) (h0 : rdW (m.arr64 CTL) mcSch.cs + 2 ≠ 0) :
    mcConstW n m T e = mcGoW n (mclearG mcSch m) T e := by simp [mcConstW, h0]
attribute [ind_grind] mcConstW_eq

theorem mentionsConst_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "mc_find" = some (memoFindG mcSch)) (hput : p.lookup "mc_put" = some (memoPutG mcSch))
    (hgo : p.lookup "mentions_const_go" = some mentionsConstGoL)
    (hcl : p.lookup "mc_clear" = some (memoClearG mcSch))
    (hp : p.lookup "mentions_const" = some mentionsConstL) (n : Nat) (s₀ : St) (T e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "mentions_const" [T, e]
    ⦃fun r s' => LocEq s' s₀ ∧ mcConstW n s₀.mem T e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := mcGo_spec p hv hf hput hgo n
  unfold McGoSpec at ih
  rw [invoke_eq _ hp]
  simp only [callFn, mentionsConstL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec mcSch p _ hcl n, ih] <;>
    finish

section mcCensus2
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "mc_find" = some (memoFindG mcSch)) (hput : p.lookup "mc_put" = some (memoPutG mcSch))
  (hgo : p.lookup "mentions_const_go" = some mentionsConstGoL)
  (hcl : p.lookup "mc_clear" = some (memoClearG mcSch))
  (hp : p.lookup "mentions_const" = some mentionsConstL)
include hv hf hput hgo hcl hp

/-- **`mentions_const` refines `mentionsConst`**: clear the `mc` memo (any well-formed one on entry),
one memoised walk; the exec fuel is below the twin's `coreWalkFuel`. -/
@[refines ConRon.Arena.mentionsConst]
theorem mentionsConst_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis T e : Word) (mp0 : Std.HashMap EIdx Bool) (hn : n ≤ coreWalkFuel) (hh : H e)
    (hT : H T) (hS : StageR dn vis fe s₀.mem a₀) (hM : mcMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "mentions_const" [T, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.mentionsConst (decI T) (decE e)) a₀ ∧
      AM.st (ConRon.Arena.mentionsConst (decI T) (decE e)) a₀ = a₀ ∧
      (r.headD 0 != 0) = AM.res (ConRon.Arena.mentionsConst (decI T) (decE e)) a₀ ∧
      (∃ mp1, mcMR s'.mem mp1) ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (mentionsConst_spec p hv hf hput hgo hcl hp n s₀ T e) ?_
  rintro r s' ⟨hl, hm⟩
  by_cases h0 : rdW (s₀.mem.arr64 CTL) mcSch.cs + 2 = 0
  · simp [mcConstW, h0] at hm
  rw [mcConstW_eq n _ T e h0] at hm
  have hf0 := mclearG_frame mcSch s₀.mem
  have hM0 := memoRG_clear mcSch mcSch_wf bmKey (fun w : Word => w != 0) s₀.mem mp0 hM h0
  have hA0 : ArenaR (mclearG mcSch s₀.mem) a₀ :=
    ArenaR.frame (A := []) (C := [mcSch.cs, mcSch.cs + 1]) (fun b hb => by simp at hb)
      (fun x hx => by simp [mcSch] at hx; rcases hx with rfl | rfl <;> exact not_mem_arenaCtl _ (by decide)) hf0
      hS.1.arena.1
  obtain ⟨c, mp1, hrun, hbb, hM1, hfr1⟩ := mcGoOK n _ _ a₀ T e _ ∅ coreWalkFuel hn hm hA0 hh hT hM0
  have hfall : MemFrame [MCM] [mcSch.cs, mcSch.cs + 1] s₀.mem s'.mem :=
    (hf0.mono (by simp) (by simp)).trans (hfr1.mono (by simp) (by simp [mcSch]))
  obtain ⟨hS', hg'⟩ := StageR.frame_hi hS hfall (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp [mcSch] at hx; rcases hx with rfl | rfl <;> decide) (by decide)
    (by simp [mcSch])
  have hrun' : (ConRon.Arena.mentionsConst (decI T) (decE e)).run a₀ = .ok (c, a₀) := by
    simp only [ConRon.Arena.mentionsConst, StateT.run_bind]
    rw [hrun]
    rfl
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  exact ⟨hl, hok, hst, by rw [hres]; exact hbb, ⟨mp1, hM1⟩, hS', hg'⟩

end mcCensus2
