import ConAgua.Arena.IndSumSpec4
import ConAgua.Arena.IndPos2Spec
import ConAgua.Arena.BvarBRefine

/-!
# Refinements of `IndSum`, fifth file (lane `indproofs`, helper `memo`)

The memoised walks of `IndSum.lean`: `mentions_const_go` / `mentions_const` (twins `mentionsConstGo`,
`mentionsConst`), `has_loose_b_var_b_*` and `struct_used_later_*`. The shape is `IndPos2Spec.lean`'s
`mentions_any_go` (`e_view`, a memo of `Bool`s keyed by the node).
-/


noncomputable section

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
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    eView_spec p hv n, memoFindG_spec mcSch p _ hf n,
    memoPutG_spec mcSch p _ hput n, ih]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind]

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
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec mcSch p _ hcl n, ih]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq] at *)
  all_goals grind [lang_grind, arena_grind, ind_grind]

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

/-! ## The `hb` memo walks: callees outside this lane

`bvar_b` is lane `exprops4`'s real function (`bvarBL`, `BvarBRefine.lean`), run under the stage relation
(`bvbW_stage`, lane `indproofs2`); `strip_pis` (`StripTeleSpec.lean`) leaves the `hb` memo alone by
its write set `stripF_frame`. -/

section hbStubs
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- **`bvar_b` (lane `exprops4`'s, no longer a stub here) under the stage relation**: its model
refines `bvarB` at every twin fuel `F + 1 ≥ n`; it writes only the `bvarB` memo (array `BMEMO` = 24,
`CTL[24]`, `CTL[25]`), so the stage relation holds after and the pool did not change. -/
theorem bvbW_stage {m m' : Mem} {a : AState} (hS : StageR dn vis fe m a) (n F : Nat) (hF : n ≤ F + 1)
    (h x : Word) (hh : H h) (hb : bvbW n m h CWF = some (x, m')) :
    ∃ a', (bvarB F (decE h)).run a = .ok (x.toNat, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      BbFrame m m' := by
  obtain ⟨a', hrun, hD⟩ := bvbW_okF n F m m' a hS.1.arena h CWF x hh (.inr hF) hb
  have hfr : BbFrame m m' := by
    match n, hb with
    | n + 1, hb =>
      by_cases hs : derBW m h = 32767
      · rw [bvbW_sat (n := n) (m := m) (h := h) (f := CWF) hs] at hb
        match n, hb with
        | k + 1, hb => rw [bbN_succ] at hb; exact bbMemoW_frame k m m' h CWF x hb
      · rw [bvbW_pk (n := n) (m := m) (h := h) (f := CWF) hs] at hb
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb
        exact MemFrame.refl _ _ _
  have hk : sp a' = sp a := by
    rw [bvarB_run] at hrun
    split at hrun
    · exact (keeps_bvarBoundMemo F (decE h)).run hrun
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun; rw [hrun.2]
  have hcp : cp a' = cp a := by simp only [sp, Prod.mk.injEq] at hk; simp [cp, hk.2.1, hk.2.2]
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hD hfr (by simp [BMEMO]) (by
    intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide) hcp
  exact ⟨a', hrun, hS', hg, hfr⟩

end hbStubs

/-! ## `has_loose_b_var_b_ins`, `has_loose_b_var_b_go`: the word models -/

def hbInsW (m : Mem) (e i r : Word) : Option (Word × Mem) :=
  (msetG hbSch m e i r).map (fun m' => (r, m'))

mutual
def hbGoW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, i, h => hbK1 n i h (bvbW n m h CWF)
def hbK1 (n : Nat) (i h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m1) => if x ≤ i then some (0, m1) else hbK2 n m1 i h (eViewW m1 h)
def hbK2 (n : Nat) (m : Mem) (i h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 then some (if i = v.tail.headD 0 then 1 else 0, m)
  else if v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8 then some (0, m)
  else if 4294967296 ≤ i then none
  else hbK3 n m i h v (mfindG hbSch m h i)
def hbK3 (n : Nat) (m : Mem) (i h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 HBM) (fr.tail.headD 0 * 4 + 3), m)
  else hbK4 h i (hbNodeW n m i (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def hbK4 (h i : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => hbInsW m1 h i r
def hbNodeW (n : Nat) (m : Mem) (i g x y z : Word) : Option (Word × Mem) :=
  if g = 4 then hbO1 n i y (hbGoW n m i x)
  else if g = 5 ∨ g = 6 then hbO1 n (i + 1) y (hbGoW n m i x)
  else if g = 7 then hbL1 n i y z (hbGoW n m i x)
  else hbGoW n m i z
def hbO1 (n : Nat) (i2 y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r1, m1) => if r1 = 1 then some (1, m1) else hbGoW n m1 i2 y
def hbL1 (n : Nat) (i y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r1, m1) => if r1 = 1 then some (1, m1) else hbL2 n i z (hbGoW n m1 i y)
def hbL2 (n : Nat) (i z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r2, m2) => if r2 = 1 then some (1, m2) else hbGoW n m2 (i + 1) z
end

section hbArms
variable (n : Nat) (m m1 m2 : Mem) (i i2 h g x y z r r1 r2 w : Word) (v fr rs : List Word)
theorem hbGoW_succ : hbGoW (n + 1) m i h = hbK1 n i h (bvbW n m h CWF) := by simp [hbGoW]
theorem hbK1_some_le (hle : w ≤ i) : hbK1 n i h (some (w, m1)) = some (0, m1) := by
  simp only [hbK1]; rw [if_pos hle]
theorem hbK1_some_gt (hle : ¬ w ≤ i) :
    hbK1 n i h (some (w, m1)) = hbK2 n m1 i h (eViewW m1 h) := by
  simp only [hbK1]; rw [if_neg hle]
theorem hbK2_abort (hv : v = []) : hbK2 n m i h v = none := by simp [hbK2, hv]
theorem hbK2_bvar (hv : v ≠ []) (hg : v.headD 0 = 0) :
    hbK2 n m i h v = some (if i = v.tail.headD 0 then 1 else 0, m) := by
  simp only [hbK2]; rw [if_neg hv, if_pos hg]
theorem hbK2_leaf (hv : v ≠ []) (hg0 : ¬ v.headD 0 = 0)
    (hg : v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8) :
    hbK2 n m i h v = some (0, m) := by
  simp only [hbK2]; rw [if_neg hv, if_neg hg0, if_pos hg]
theorem hbK2_big (hv : v ≠ []) (hg0 : ¬ v.headD 0 = 0)
    (hg : ¬ (v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8)) (hi : 4294967296 ≤ i) :
    hbK2 n m i h v = none := by
  simp only [hbK2]; rw [if_neg hv, if_neg hg0, if_neg hg, if_pos hi]
theorem hbK2_node (hv : v ≠ []) (hg0 : ¬ v.headD 0 = 0)
    (hg : ¬ (v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8)) (hi : ¬ 4294967296 ≤ i) :
    hbK2 n m i h v = hbK3 n m i h v (mfindG hbSch m h i) := by
  simp only [hbK2]; rw [if_neg hv, if_neg hg0, if_neg hg, if_neg hi]
theorem hbK3_abort (hr : fr = []) : hbK3 n m i h v fr = none := by simp [hbK3, hr]
theorem hbK3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    hbK3 n m i h v fr = some (rdW (m.arr64 HBM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [hbK3]; rw [if_neg hr, if_pos hh]
theorem hbK3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    hbK3 n m i h v fr = hbK4 h i (hbNodeW n m i (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
      (v.tail.tail.tail.headD 0)) := by
  simp only [hbK3]; rw [if_neg hr, if_neg hh]
theorem hbK4_some : hbK4 h i (some (r, m1)) = hbInsW m1 h i r := by rw [hbK4]
theorem hbNodeW_4 (hg : g = 4) : hbNodeW n m i g x y z = hbO1 n i y (hbGoW n m i x) := by
  simp [hbNodeW, hg]
theorem hbNodeW_56 (hg : g = 5 ∨ g = 6) : hbNodeW n m i g x y z =
    hbO1 n (i + 1) y (hbGoW n m i x) := by
  have : ¬ g = 4 := by rcases hg with e | e <;> (rw [e]; decide)
  simp only [hbNodeW]; rw [if_neg this, if_pos hg]
theorem hbNodeW_7 (hg : g = 7) : hbNodeW n m i g x y z = hbL1 n i y z (hbGoW n m i x) := by
  simp [hbNodeW, hg]
theorem hbNodeW_9 (hg1 : g ≠ 4) (hg2 : ¬ (g = 5 ∨ g = 6)) (hg3 : g ≠ 7) :
    hbNodeW n m i g x y z = hbGoW n m i z := by
  simp only [hbNodeW]; rw [if_neg hg1, if_neg hg2, if_neg hg3]
theorem hbO1_one (hr : r1 = 1) : hbO1 n i2 y (some (r1, m1)) = some (1, m1) := by simp [hbO1, hr]
theorem hbO1_ne (hr : ¬ r1 = 1) : hbO1 n i2 y (some (r1, m1)) = hbGoW n m1 i2 y := by simp [hbO1, hr]
theorem hbL1_one (hr : r1 = 1) : hbL1 n i y z (some (r1, m1)) = some (1, m1) := by simp [hbL1, hr]
theorem hbL1_ne (hr : ¬ r1 = 1) :
    hbL1 n i y z (some (r1, m1)) = hbL2 n i z (hbGoW n m1 i y) := by simp [hbL1, hr]
theorem hbL2_one (hr : r2 = 1) : hbL2 n i z (some (r2, m2)) = some (1, m2) := by simp [hbL2, hr]
theorem hbL2_ne (hr : ¬ r2 = 1) : hbL2 n i z (some (r2, m2)) = hbGoW n m2 (i + 1) z := by
  simp [hbL2, hr]
end hbArms

attribute [ind_grind] hbGoW_succ hbK1_some_le hbK1_some_gt hbK2_abort hbK2_bvar hbK2_leaf hbK2_big
  hbK2_node hbK3_abort hbK3_hit hbK3_miss hbK4_some hbNodeW_4 hbNodeW_56 hbNodeW_7 hbNodeW_9 hbO1_one
  hbO1_ne hbL1_one hbL1_ne hbL2_one hbL2_ne

section hbspec
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p)

include hf hput in
theorem hbIns_spec_raw (hp : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL) (n : Nat) (s₀ : St)
    (e i r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "has_loose_b_var_b_ins" [e, i, r]
    ⦃fun rr s' => LocEq s' s₀ ∧ msetG hbSch s₀.mem e i r = some s'.mem ∧ rr.headD 0 = r; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, hasLooseBVarBInsL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoFindG_spec hbSch p _ hf n,
      memoPutG_spec hbSch p _ hput n]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
      BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq] at *)
    all_goals grind [lang_grind, arena_grind, ind_grind, msetG]

include hf hput in
theorem hbIns_spec (hp : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL) (n : Nat) (s₀ : St)
    (e i r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "has_loose_b_var_b_ins" [e, i, r]
    ⦃fun rr s' => LocEq s' s₀ ∧ hbInsW s₀.mem e i r = some (rr.headD 0, s'.mem); ⊤⦄ := by
  refine triple_post (hbIns_spec_raw p hf hput hp n s₀ e i r) ?_
  rintro rr s' ⟨hl, hm, hr⟩
  refine ⟨hl, ?_⟩
  rw [hbInsW, hm, ← hr]; rfl

def HbGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (i h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "has_loose_b_var_b_go" [i, h]
    ⦃fun r s' => LocEq s' s₀ ∧ hbGoW n s₀.mem i h = some (r.headD 0, s'.mem); ⊤⦄

set_option maxHeartbeats 4000000 in
include hv hf hput hins hgo hbp in
theorem hbGo_step (n : Nat) (ih : HbGoSpec p n) : HbGoSpec p (n + 1) := by
  unfold HbGoSpec at ih
  intro s₀ i h
  rw [invoke_eq _ hgo]
  simp only [callFn, hasLooseBVarBGoL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    bvarBL_spec p hbp n, eView_spec p hv n, memoFindG_spec hbSch p _ hf n,
    hbIns_spec p hf hput hins n, ih]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind]

include hv hf hput hins hgo hbp in
theorem hbGo_spec (n : Nat) : HbGoSpec p n := by
  induction n with
  | zero =>
    intro s₀ i h; rw [invoke_eq _ hgo]; simp only [callFn, hasLooseBVarBGoL]; vcgen [exec] <;> grind
  | succ n ih => exact hbGo_step p hv hf hput hins hgo hbp n ih

end hbspec

/-! ## `has_loose_b_var_b_*`: the relation to the twin -/

theorem hbSch_wf : hbSch.WF := ⟨by decide, by decide⟩

/-- A stored value word is exactly the answer's `0`/`1`. -/
def hbVR (_ : Mem) (w : Word) (v : Bool) : Prop := w = if v then 1 else 0

/-- The memo relation of the `hasLooseBVarB` walk (keys `(node, index)`). -/
abbrev hbMR (m : Mem) (mp : Std.HashMap (EIdx × Nat) Bool) : Prop := MemoRV hbSch lfKey hbVR m mp

theorem hbVR_stable : VStable hbSch hbVR := fun _ _ _ _ _ h => h

/-- The twin's arms of a node view, with the memo insertion pushed into the branches (as the twin's
`do` block elaborates). -/
def hbArm (memo : Std.HashMap (EIdx × Nat) Bool) (i : Nat) (fuel : Nat) (h : EIdx) :
    ENodeView → AM (Bool × Std.HashMap (EIdx × Nat) Bool)
  | .app f a => do
    match ← ConRon.Arena.hasLooseBVarBGo memo i fuel f with
    | (true, memo) => pure (ConRon.Arena.hasLooseBVarBIns h i (true, memo))
    | (false, memo) => do
      let r ← ConRon.Arena.hasLooseBVarBGo memo i fuel a
      pure (ConRon.Arena.hasLooseBVarBIns h i r)
  | .lam ty b => do
    match ← ConRon.Arena.hasLooseBVarBGo memo i fuel ty with
    | (true, memo) => pure (ConRon.Arena.hasLooseBVarBIns h i (true, memo))
    | (false, memo) => do
      let r ← ConRon.Arena.hasLooseBVarBGo memo (i + 1) fuel b
      pure (ConRon.Arena.hasLooseBVarBIns h i r)
  | .forallE ty b => do
    match ← ConRon.Arena.hasLooseBVarBGo memo i fuel ty with
    | (true, memo) => pure (ConRon.Arena.hasLooseBVarBIns h i (true, memo))
    | (false, memo) => do
      let r ← ConRon.Arena.hasLooseBVarBGo memo (i + 1) fuel b
      pure (ConRon.Arena.hasLooseBVarBIns h i r)
  | .letE t v b => do
    match ← ConRon.Arena.hasLooseBVarBGo memo i fuel t with
    | (true, memo) => pure (ConRon.Arena.hasLooseBVarBIns h i (true, memo))
    | (false, memo) => do
      match ← ConRon.Arena.hasLooseBVarBGo memo i fuel v with
      | (true, memo) => pure (ConRon.Arena.hasLooseBVarBIns h i (true, memo))
      | (false, memo) => do
        let r ← ConRon.Arena.hasLooseBVarBGo memo (i + 1) fuel b
        pure (ConRon.Arena.hasLooseBVarBIns h i r)
  | .proj _ _ sub => do
    let r ← ConRon.Arena.hasLooseBVarBGo memo i fuel sub
    pure (ConRon.Arena.hasLooseBVarBIns h i r)
  | _ => pure (ConRon.Arena.hasLooseBVarBIns h i (false, memo))

/-- The twin's walk after the `bvarB` cutoff. -/
def hbRestT (memo : Std.HashMap (EIdx × Nat) Bool) (i : Nat) (fuel : Nat) (h : EIdx) :
    AM (Bool × Std.HashMap (EIdx × Nat) Bool) := do
  let v ← view h
  match v with
  | .bvar j => pure (i == j, memo)
  | .fvar _ _ => pure (false, memo)
  | .sort _ => pure (false, memo)
  | .const _ _ => pure (false, memo)
  | .lit _ => pure (false, memo)
  | v =>
    match memo[(h, i)]? with
    | some r => pure (r, memo)
    | none => hbArm memo i fuel h v

theorem hasLooseBVarBGo_succ' (memo : Std.HashMap (EIdx × Nat) Bool) (i fuel : Nat) (h : EIdx) :
    ConRon.Arena.hasLooseBVarBGo memo i (fuel + 1) h = (do
      let bb ← bvarB fuel h
      if bb ≤ i then pure (false, memo) else hbRestT memo i fuel h) := by
  rw [ConRon.Arena.hasLooseBVarBGo.eq_2]
  rfl

/-- The non-leaf views of the `hb` walk (through the memo). -/
def HNodeV : ENodeView → Prop
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => True
  | _ => False

theorem hbTwin_node (memo : Std.HashMap (EIdx × Nat) Bool) (i fuel : Nat) (h : EIdx) (a : AState)
    (v : ENodeView) (hv : a.store.view h = some v) (hnv : HNodeV v) :
    (hbRestT memo i fuel h).run a =
      ((match memo[(h, i)]? with
        | some r => pure (r, memo)
        | none => hbArm memo i fuel h v : AM (Bool × Std.HashMap (EIdx × Nat) Bool)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | (simp only [hbRestT, StateT.run_bind]; rw [view_run _ a _ hv, except_ok_bind])

theorem hbIns_ok {m m' : Mem} {e i r r' : Word} {b : Bool} {mp : Std.HashMap (EIdx × Nat) Bool}
    (he : H e) (hr : r = if b then 1 else 0) (hM : hbMR m mp) (h : hbInsW m e i r = some (r', m')) :
    r' = r ∧ hbMR m' (ConRon.Arena.hasLooseBVarBIns (decE e) i.toNat (b, mp)).2 ∧
      MemFrame [HBM] [215] m m' := by
  simp only [hbInsW] at h
  cases hm : msetG hbSch m e i r with
  | none => rw [hm] at h; simp at h
  | some m2 =>
    rw [hm] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_, ?_⟩
    · exact memoRV_set hbSch hbSch_wf lfKey hbVR hbVR_stable m mp hM e i r he b hr m2 hm
    · exact (msetG_frame hbSch hbSch_wf m m2 e i r hm).mono (by simp [hbSch]) (by simp [hbSch])

/-- `HbOK n`: the word model at depth `n` refines the twin at any fuel `F` that is plentiful for `bvarB`. -/
def HbOK (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (i h r : Word) (mp : Std.HashMap (EIdx × Nat) Bool) (F : Nat),
    2 ^ 31 + n ≤ F → F ≤ coreWalkFuel → hbGoW n m i h = some (r, m') → StageR dn vis fe m a → H h →
    hbMR m mp →
    ∃ b mp' a', (ConRon.Arena.hasLooseBVarBGo mp i.toNat F (decE h)).run a = .ok ((b, mp'), a') ∧
      r = (if b then 1 else 0) ∧ hbMR m' mp' ∧ StageR dn vis fe m' a' ∧ IWGrow m m'

theorem word_toNat_add_one {i : Word} (hi : ¬ 4294967296 ≤ i) : (i + 1).toNat = i.toNat + 1 := by
  have : i.toNat < 4294967296 :=
    Nat.lt_of_not_ge (fun hc => hi (UInt64.le_iff_toNat_le.mpr (by simpa using hc)))
  rw [UInt64.toNat_add]; simp; omega

theorem word_one_iff {b : Bool} {r : Word} (hr : r = if b then 1 else 0) : r = 1 ↔ b = true := by
  cases b <;> simp [hr]

/-- `or`-shaped arms: the first call, then (on `false`) the second; `ins` is the memo insertion
that follows (pushed into the branches by the twin's `do`). -/
theorem hbOr_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat)
    (ih : HbOK dn vis fe n) (m m' : Mem) (a : AState) (i i2 x y rn : Word)
    (mp : Std.HashMap (EIdx × Nat) Bool) (F : Nat) (hFn : 2 ^ 31 + n ≤ F) (hFc : F ≤ coreWalkFuel)
    (hx : H x) (hy : H y) (ins : Bool × Std.HashMap (EIdx × Nat) Bool → Bool × Std.HashMap (EIdx × Nat) Bool)
    (hn : hbO1 n i2 y (hbGoW n m i x) = some (rn, m')) (hS : StageR dn vis fe m a) (hM : hbMR m mp) :
    ∃ b mp' a', (do
        match ← ConRon.Arena.hasLooseBVarBGo mp i.toNat F (decE x) with
        | (true, memo) => pure (ins (true, memo))
        | (false, memo) => do
          let r ← ConRon.Arena.hasLooseBVarBGo memo i2.toNat F (decE y)
          pure (ins r) :
          AM (Bool × Std.HashMap (EIdx × Nat) Bool)).run a = .ok (ins (b, mp'), a') ∧
      rn = (if b then 1 else 0) ∧ hbMR m' mp' ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  cases h1 : hbGoW n m i x with
  | none => rw [h1] at hn; simp [hbO1] at hn
  | some p1 =>
    obtain ⟨r1, m1⟩ := p1
    rw [h1] at hn
    obtain ⟨c1, mp1, a1, hr1, hb1, hM1, hS1, hg1⟩ := ih m m1 a i x r1 mp F hFn hFc h1 hS hx hM
    by_cases e1 : r1 = 1
    · rw [hbO1_one (n := n) (i2 := i2) (y := y) (m1 := m1) (r1 := r1) e1] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      have hc : c1 = true := (word_one_iff hb1).mp e1
      subst hc
      refine ⟨true, mp1, a1, ?_, rfl, hM1, hS1, hg1⟩
      simp only [StateT.run_bind]
      rw [hr1]
      simp only [except_ok_bind]
      rfl
    · rw [hbO1_ne (n := n) (i2 := i2) (y := y) (m1 := m1) (r1 := r1) e1] at hn
      have hc : c1 = false := by
        cases c1
        · rfl
        · exact absurd ((word_one_iff hb1).mpr rfl) e1
      subst hc
      obtain ⟨c2, mp2, a2, hr2, hb2, hM2, hS2, hg2⟩ := ih m1 m' a1 i2 y rn mp1 F hFn hFc hn hS1 hy hM1
      refine ⟨c2, mp2, a2, ?_, hb2, hM2, hS2, hg1.trans hg2⟩
      simp only [StateT.run_bind]
      rw [hr1]
      simp only [except_ok_bind, StateT.run_bind]
      rw [hr2]
      simp only [except_ok_bind]
      rfl

theorem hbLet_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat)
    (ih : HbOK dn vis fe n) (m m' : Mem) (a : AState) (i x y z rn : Word)
    (mp : Std.HashMap (EIdx × Nat) Bool) (F : Nat) (hFn : 2 ^ 31 + n ≤ F) (hFc : F ≤ coreWalkFuel)
    (hi : ¬ 4294967296 ≤ i) (hx : H x) (hy : H y) (hz : H z)
    (ins : Bool × Std.HashMap (EIdx × Nat) Bool → Bool × Std.HashMap (EIdx × Nat) Bool)
    (hn : hbL1 n i y z (hbGoW n m i x) = some (rn, m')) (hS : StageR dn vis fe m a) (hM : hbMR m mp) :
    ∃ b mp' a', (do
        match ← ConRon.Arena.hasLooseBVarBGo mp i.toNat F (decE x) with
        | (true, memo) => pure (ins (true, memo))
        | (false, memo) => do
          match ← ConRon.Arena.hasLooseBVarBGo memo i.toNat F (decE y) with
          | (true, memo) => pure (ins (true, memo))
          | (false, memo) => do
            let r ← ConRon.Arena.hasLooseBVarBGo memo (i.toNat + 1) F (decE z)
            pure (ins r) :
          AM (Bool × Std.HashMap (EIdx × Nat) Bool)).run a = .ok (ins (b, mp'), a') ∧
      rn = (if b then 1 else 0) ∧ hbMR m' mp' ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  cases h1 : hbGoW n m i x with
  | none => rw [h1] at hn; simp [hbL1] at hn
  | some p1 =>
    obtain ⟨r1, m1⟩ := p1
    rw [h1] at hn
    obtain ⟨c1, mp1, a1, hr1, hb1, hM1, hS1, hg1⟩ := ih m m1 a i x r1 mp F hFn hFc h1 hS hx hM
    by_cases e1 : r1 = 1
    · rw [hbL1_one (n := n) (i := i) (y := y) (z := z) (m1 := m1) (r1 := r1) e1] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      have hc : c1 = true := (word_one_iff hb1).mp e1
      subst hc
      refine ⟨true, mp1, a1, ?_, rfl, hM1, hS1, hg1⟩
      simp only [StateT.run_bind]
      rw [hr1]
      simp only [except_ok_bind]
      rfl
    · rw [hbL1_ne (n := n) (i := i) (y := y) (z := z) (m1 := m1) (r1 := r1) e1] at hn
      have hc : c1 = false := by
        cases c1
        · rfl
        · exact absurd ((word_one_iff hb1).mpr rfl) e1
      subst hc
      have hn' : hbO1 n (i + 1) z (hbGoW n m1 i y) = some (rn, m') := by
        cases h2 : hbGoW n m1 i y with
        | none => rw [h2] at hn; simp [hbL2] at hn
        | some p2 =>
          obtain ⟨r2, m2⟩ := p2
          rw [h2] at hn
          by_cases e2 : r2 = 1
          · rw [hbL2_one (n := n) (i := i) (z := z) (r2 := r2) (m2 := m2) e2] at hn; rw [hbO1_one (n := n) (i2 := i + 1) (y := z) (m1 := m2) (r1 := r2) e2]; exact hn
          · rw [hbL2_ne (n := n) (i := i) (z := z) (r2 := r2) (m2 := m2) e2] at hn; rw [hbO1_ne (n := n) (i2 := i + 1) (y := z) (m1 := m2) (r1 := r2) e2]; exact hn
      have := hbOr_ok n ih m1 m' a1 i (i + 1) y z rn mp1 F hFn hFc hy hz ins hn' hS1 hM1
      rw [word_toNat_add_one hi] at this
      obtain ⟨c, mp2, a2, hr2, hb2, hM2, hS2, hg2⟩ := this
      refine ⟨c, mp2, a2, ?_, hb2, hM2, hS2, hg1.trans hg2⟩
      simp only [StateT.run_bind]
      rw [hr1]
      simp only [except_ok_bind]
      exact hr2

theorem hbNode_arm {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat)
    (ih : HbOK dn vis fe k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v) (hnv : HNodeV v)
    (m m' : Mem) (a : AState) (i r : Word) (hE : EIdx) (mp : Std.HashMap (EIdx × Nat) Bool) (F : Nat)
    (hFn : 2 ^ 31 + k ≤ F) (hFc : F ≤ coreWalkFuel) (hi : ¬ 4294967296 ≤ i)
    (hn : hbNodeW k m i (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0) = some (r, m'))
    (hS : StageR dn vis fe m a) (hM : hbMR m mp) :
    ∃ b mp' a', (hbArm mp i.toNat F hE v).run a =
        .ok (ConRon.Arena.hasLooseBVarBIns hE i.toNat (b, mp'), a') ∧
      r = (if b then 1 else 0) ∧ hbMR m' mp' ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  cases v with
  | app f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    rw [hbNodeW_4 (hg := hg)] at hn
    have := hbOr_ok k ih m m' a i i _ _ r mp F hFn hFc hx hy (ConRon.Arena.hasLooseBVarBIns hE i.toNat)
      hn hS hM
    rw [hdx, hdy] at this
    simpa only [hbArm] using this
  | lam f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    rw [hbNodeW_56 (hg := Or.inl hg)] at hn
    have := hbOr_ok k ih m m' a i (i + 1) _ _ r mp F hFn hFc hx hy (ConRon.Arena.hasLooseBVarBIns hE i.toNat)
      hn hS hM
    rw [hdx, hdy, word_toNat_add_one hi] at this
    simpa only [hbArm] using this
  | forallE f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    rw [hbNodeW_56 (hg := Or.inr hg)] at hn
    have := hbOr_ok k ih m m' a i (i + 1) _ _ r mp F hFn hFc hx hy (ConRon.Arena.hasLooseBVarBIns hE i.toNat)
      hn hS hM
    rw [hdx, hdy, word_toNat_add_one hi] at this
    simpa only [hbArm] using this
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
    rw [hbNodeW_7 (hg := hg)] at hn
    have := hbLet_ok k ih m m' a i _ _ _ r mp F hFn hFc hi hx hy hz (ConRon.Arena.hasLooseBVarBIns hE i.toNat)
      hn hS hM
    rw [hdx, hdy, hdz] at this
    simpa only [hbArm] using this
  | proj s idx e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, -, hz, hdz⟩ := hvr
    rw [hbNodeW_9 (hg1 := by rw [hg]; decide) (hg2 := by rw [hg]; decide) (hg3 := by rw [hg]; decide)] at hn
    obtain ⟨c, mp1, a1, hr1, hb1, hM1, hS1, hg1⟩ := ih m m' a i _ r mp F hFn hFc hn hS hz hM
    rw [hdz] at hr1
    refine ⟨c, mp1, a1, ?_, hb1, hM1, hS1, hg1⟩
    simp only [hbArm, StateT.run_bind]
    rw [hr1]
    simp only [except_ok_bind]
    rfl
  | bvar _ => exact False.elim hnv
  | fvar _ _ => exact False.elim hnv
  | sort _ => exact False.elim hnv
  | const _ _ => exact False.elim hnv
  | lit _ => exact False.elim hnv

theorem hbGo_nodeCase {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (j : Nat)
    (ih : HbOK dn vis fe j) (m m' : Mem) (a : AState) (i h r : Word)
    (mp : Std.HashMap (EIdx × Nat) Bool) (F : Nat) (hFn : 2 ^ 31 + j ≤ F) (hFc : F ≤ coreWalkFuel)
    (vl : List Word) (v : ENodeView) (hvr : ViewR vl v) (hnv : HNodeV v)
    (hv : a.store.view (decE h) = some v) (hvl : vl ≠ [])
    (hg0 : ¬ vl.headD 0 = 0)
    (hgl : ¬ (vl.headD 0 = 1 ∨ vl.headD 0 = 2 ∨ vl.headD 0 = 3 ∨ vl.headD 0 = 8))
    (hb : hbK2 j m i h vl = some (r, m')) (hS : StageR dn vis fe m a) (hh : H h) (hM : hbMR m mp) :
    ∃ b mp' a', (hbRestT mp i.toNat F (decE h)).run a = .ok ((b, mp'), a') ∧
      r = (if b then 1 else 0) ∧ hbMR m' mp' ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  by_cases hi : 4294967296 ≤ i
  · rw [hbK2_big j m i h vl hvl hg0 hgl hi] at hb; simp at hb
  rw [hbK2_node j m i h vl hvl hg0 hgl hi] at hb
  rw [hbTwin_node _ _ _ _ a v hv hnv]
  by_cases hfr : mfindG hbSch m h i = []
  · rw [hbK3_abort j m i h vl _ hfr] at hb; simp at hb
  have hk : lfKey.ok h i := hh
  by_cases hhit : (mfindG hbSch m h i).headD 0 ≠ 0
  · rw [hbK3_hit j m i h vl _ hfr hhit] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨b, hb1, hb2⟩ := memoRV_hit hbSch lfKey hbVR m mp hM h i hfr hhit hk
    have : lfKey.dk h i = (decE h, i.toNat) := rfl
    rw [this] at hb1
    refine ⟨b, mp, a, ?_, hb2, hM, hS, IWGrow.refl _⟩
    simp only [hb1]; rfl
  · rw [hbK3_miss j m i h vl _ hfr hhit] at hb
    have hmiss := memoRV_miss hbSch lfKey hbVR m mp hM h i hk hfr (by simpa using hhit)
    have : lfKey.dk h i = (decE h, i.toNat) := rfl
    rw [this] at hmiss
    cases hnode : hbNodeW j m i (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
        (vl.tail.tail.tail.headD 0) with
    | none => rw [hnode] at hb; simp [hbK4] at hb
    | some pn =>
      obtain ⟨rn, m1⟩ := pn
      rw [hnode, hbK4_some] at hb
      obtain ⟨bb, mp1, a1, hr1, hbb, hM1, hS1, hg1⟩ :=
        hbNode_arm j ih vl v hvr hnv m m1 a i rn (decE h) mp F hFn hFc hi hnode hS hM
      obtain ⟨hr', hM2, hfr2⟩ := hbIns_ok hh hbb hM1 hb
      obtain ⟨hS2, hg2⟩ := StageR.frame_hi hS1 hfr2 (by intro b hb; simp at hb; subst hb; decide)
        (by intro x hx; simp at hx; subst hx; decide) (by decide) (by decide)
      refine ⟨bb, (ConRon.Arena.hasLooseBVarBIns (decE h) i.toNat (bb, mp1)).2, a1, ?_, ?_, hM2, hS2,
        hg1.trans hg2⟩
      · rw [hmiss]; exact hr1
      · rw [hr']; exact hbb

theorem hbGo_step_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (j : Nat)
    (ih : ∀ k, k < j + 1 → HbOK dn vis fe k) : HbOK dn vis fe (j + 1) := by
  intro m m' a i h r mp F hFn hFc hb hS hh hM
  rw [hbGoW_succ] at hb
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases hst : bvbW j m h CWF with
  | none => rw [hst] at hb; simp [hbK1] at hb
  | some pr =>
    obtain ⟨w, m1⟩ := pr
    rw [hst] at hb
    obtain ⟨a1, hbv', hS1, hg1, hfr⟩ := bvbW_stage dn vis fe hS j F (by omega) h w hh hst
    have hM1 : hbMR m1 mp := memoRV_frame hbSch hbSch_wf lfKey hbVR _ _ (by simp [hbSch, HBM, BMEMO])
      (by simp [hbSch]) m m1 hfr (fun _ _ h => h) mp hM
    rw [hasLooseBVarBGo_succ']
    simp only [StateT.run_bind]
    rw [hbv']
    simp only [except_ok_bind]
    by_cases hle : w ≤ i
    · rw [hbK1_some_le (hle := hle)] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      have : w.toNat ≤ i.toNat := UInt64.le_iff_toNat_le.mp hle
      rw [if_pos this]
      exact ⟨false, mp, a1, rfl, rfl, hM1, hS1, hg1⟩
    · rw [hbK1_some_gt (hle := hle)] at hb
      have : ¬ w.toNat ≤ i.toNat := fun c => hle (UInt64.le_iff_toNat_le.mpr c)
      rw [if_neg this]
      cases hvl : eViewW m1 h with
      | nil => rw [hvl] at hb; simp [hbK2] at hb
      | cons g vt =>
        have hne : eViewW m1 h ≠ [] := by rw [hvl]; simp
        obtain ⟨v, hv, hvr⟩ := eViewW_ok m1 a1 hS1.1.arena.1 h hne
        rw [hvl] at hvr hb
        have hg1' : IWGrow m m1 := hg1
        have hnode := fun (hgs : ¬ ((g :: vt).headD 0 = 0) ∧ ¬ ((g :: vt).headD 0 = 1 ∨ (g :: vt).headD 0 = 2 ∨ (g :: vt).headD 0 = 3 ∨ (g :: vt).headD 0 = 8)) (hnv : HNodeV v) =>
          hbGo_nodeCase j (ih j (by omega)) m1 m' a1 i h r mp F (by omega) (by omega) _ v hvr hnv hv
            (by simp) hgs.1 hgs.2 hb hS1 hh hM1
        cases v with
        | bvar i' =>
          have hg0 : (g :: vt).headD 0 = 0 := by simpa [ViewR] using hvr.1
          have hi' : ((g :: vt).tail.headD 0).toNat = i' := by rw [← getD1_eq']; exact hvr.2
          rw [hbK2_bvar j m1 i h _ (by simp) hg0] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [hbRestT, StateT.run_bind, view_run _ a1 _ hv, except_ok_bind]
          refine ⟨i.toNat == i', mp, a1, rfl, ?_, hM1, hS1, hg1'.trans (IWGrow.refl _)⟩
          generalize (g :: vt).tail.headD 0 = xx at hi' ⊢
          by_cases e : i = xx
          · have : i.toNat = i' := by rw [← hi', e]
            simp [e, this, hi']
          · have : i.toNat ≠ i' := fun c => e (UInt64.toNat_inj.mp (c.trans hi'.symm))
            simp [e, this, hi']
        | fvar i' ty =>
          have hg0 : (g :: vt).headD 0 = 1 := by simpa [ViewR] using hvr.1
          rw [hbK2_leaf j m1 i h _ (by simp) (by rw [hg0]; decide) (by rw [hg0]; simp)] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [hbRestT, StateT.run_bind, view_run _ a1 _ hv, except_ok_bind]
          exact ⟨false, mp, a1, rfl, rfl, hM1, hS1, hg1'⟩
        | sort u =>
          have hg0 : (g :: vt).headD 0 = 2 := by simpa [ViewR] using hvr.1
          rw [hbK2_leaf j m1 i h _ (by simp) (by rw [hg0]; decide) (by rw [hg0]; simp)] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [hbRestT, StateT.run_bind, view_run _ a1 _ hv, except_ok_bind]
          exact ⟨false, mp, a1, rfl, rfl, hM1, hS1, hg1'⟩
        | const nn us =>
          have hg0 : (g :: vt).headD 0 = 3 := by simpa [ViewR] using hvr.1
          rw [hbK2_leaf j m1 i h _ (by simp) (by rw [hg0]; decide) (by rw [hg0]; simp)] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [hbRestT, StateT.run_bind, view_run _ a1 _ hv, except_ok_bind]
          exact ⟨false, mp, a1, rfl, rfl, hM1, hS1, hg1'⟩
        | lit l =>
          have hg0 : (g :: vt).headD 0 = 8 := by simpa [ViewR] using hvr
          rw [hbK2_leaf j m1 i h _ (by simp) (by rw [hg0]; decide) (by rw [hg0]; simp)] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [hbRestT, StateT.run_bind, view_run _ a1 _ hv, except_ok_bind]
          exact ⟨false, mp, a1, rfl, rfl, hM1, hS1, hg1'⟩
        | app f' x' =>
          have hg0 : (g :: vt).headD 0 = 4 := by simpa [ViewR] using hvr.1
          obtain ⟨b, mp', a', e1, e2, e3, e4, e5⟩ := hnode ⟨by rw [hg0]; decide, by rw [hg0]; decide⟩ trivial
          exact ⟨b, mp', a', e1, e2, e3, e4, hg1'.trans e5⟩
        | lam f' x' =>
          have hg0 : (g :: vt).headD 0 = 5 := by simpa [ViewR] using hvr.1
          obtain ⟨b, mp', a', e1, e2, e3, e4, e5⟩ := hnode ⟨by rw [hg0]; decide, by rw [hg0]; decide⟩ trivial
          exact ⟨b, mp', a', e1, e2, e3, e4, hg1'.trans e5⟩
        | forallE f' x' =>
          have hg0 : (g :: vt).headD 0 = 6 := by simpa [ViewR] using hvr.1
          obtain ⟨b, mp', a', e1, e2, e3, e4, e5⟩ := hnode ⟨by rw [hg0]; decide, by rw [hg0]; decide⟩ trivial
          exact ⟨b, mp', a', e1, e2, e3, e4, hg1'.trans e5⟩
        | letE t v' b' =>
          have hg0 : (g :: vt).headD 0 = 7 := by simpa [ViewR] using hvr.1
          obtain ⟨b, mp', a', e1, e2, e3, e4, e5⟩ := hnode ⟨by rw [hg0]; decide, by rw [hg0]; decide⟩ trivial
          exact ⟨b, mp', a', e1, e2, e3, e4, hg1'.trans e5⟩
        | proj s idx e =>
          have hg0 : (g :: vt).headD 0 = 9 := by simpa [ViewR] using hvr.1
          obtain ⟨b, mp', a', e1, e2, e3, e4, e5⟩ := hnode ⟨by rw [hg0]; decide, by rw [hg0]; decide⟩ trivial
          exact ⟨b, mp', a', e1, e2, e3, e4, hg1'.trans e5⟩

theorem hbGoOK {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    HbOK dn vis fe n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro m m' a i h r mp F _ _ hb; simp [hbGoW] at hb
    | succ j => exact hbGo_step_ok j (fun k hk => ih k (by omega))

/-! ## The census theorems of the `hb` walk -/

section hbCensus
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p)

include hf hput hins in
/-- **`has_loose_b_var_b_ins` refines `hasLooseBVarBIns`**: the answer's word is recorded in the memo. -/
@[refines ConRon.Arena.hasLooseBVarBIns]
theorem hasLooseBVarBIns_refines (n : Nat) (s₀ : St) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis : Word) (a₀ : AState) (e i r : Word) (b : Bool) (mp : Std.HashMap (EIdx × Nat) Bool) (he : H e)
    (hr : r = if b then 1 else 0) (hS : StageR dn vis fe s₀.mem a₀) (hM : hbMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "has_loose_b_var_b_ins" [e, i, r]
    ⦃fun rr s' => LocEq s' s₀ ∧ rr.headD 0 = r ∧
      hbMR s'.mem (ConRon.Arena.hasLooseBVarBIns (decE e) i.toNat (b, mp)).2 ∧
      StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (hbIns_spec p hf hput hins n s₀ e i r) ?_
  rintro rr s' ⟨hl, hm⟩
  obtain ⟨hr', hM', hfr⟩ := hbIns_ok he hr hM hm
  obtain ⟨hS', hg⟩ := StageR.frame_hi hS hfr (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp at hx; subst hx; decide) (by decide) (by decide)
  exact ⟨hl, hr', hM', hS', hg⟩

include hv hf hput hins hgo hbp in
/-- **`has_loose_b_var_b_go` refines `hasLooseBVarBGo`** from a related memo, at twin fuel `F` with
`2^31 + n ≤ F ≤ coreWalkFuel` (`n` the exec depth; `bvar_b` is lane `exprops4`'s, `bvbW_stage`). -/
@[refines ConRon.Arena.hasLooseBVarBGo]
theorem hasLooseBVarBGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis i h : Word) (mp : Std.HashMap (EIdx × Nat) Bool) (F : Nat)
    (hFn : 2 ^ 31 + n ≤ F) (hFc : F ≤ coreWalkFuel) (hh : H h)
    (hS : StageR dn vis fe s₀.mem a₀) (hM : hbMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "has_loose_b_var_b_go" [i, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.hasLooseBVarBGo mp i.toNat F (decE h)) a₀ ∧
      r.headD 0 = (if (AM.res (ConRon.Arena.hasLooseBVarBGo mp i.toNat F (decE h)) a₀).1 then 1 else 0) ∧
      hbMR s'.mem (AM.res (ConRon.Arena.hasLooseBVarBGo mp i.toNat F (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.hasLooseBVarBGo mp i.toNat F (decE h)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (hbGo_spec p hv hf hput hins hgo hbp n s₀ i h) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, mp', a', hrun, hb, hM', hS', hg⟩ := hbGoOK n _ _ a₀ i h _ mp F hFn hFc hm hS hh hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hb, by rw [hres]; exact hM', by rw [hst]; exact hS', hg⟩

end hbCensus

/-! ## `has_loose_b_var_b_fast` -/

def hbFastW (n : Nat) (m : Mem) (i e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) hbSch.cs + 2 = 0 then none else hbGoW n (mclearG hbSch m) i e

theorem hbFastW_eq (n : Nat) (m : Mem) (i e : Word) (h0 : rdW (m.arr64 CTL) hbSch.cs + 2 ≠ 0) :
    hbFastW n m i e = hbGoW n (mclearG hbSch m) i e := by simp [hbFastW, h0]
attribute [ind_grind] hbFastW_eq

theorem hbFast_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
    (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
    (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p)
    (hcl : p.lookup "hb_clear" = some (memoClearG hbSch))
    (hp : p.lookup "has_loose_b_var_b_fast" = some hasLooseBVarBFastL) (n : Nat) (s₀ : St) (i e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "has_loose_b_var_b_fast" [i, e]
    ⦃fun r s' => LocEq s' s₀ ∧ hbFastW n s₀.mem i e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := hbGo_spec p hv hf hput hins hgo hbp n
  unfold HbGoSpec at ih
  rw [invoke_eq _ hp]
  simp only [callFn, hasLooseBVarBFastL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec hbSch p _ hcl n, ih]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq] at *)
  all_goals grind [lang_grind, arena_grind, ind_grind]

theorem hbFastW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat)
    (m m' : Mem) (a : AState) (i e r : Word) (mp0 : Std.HashMap (EIdx × Nat) Bool)
    (hn : 2 ^ 31 + n ≤ coreWalkFuel) (hh : H e) (hS : StageR dn vis fe m a) (hM : hbMR m mp0)
    (hm : hbFastW n m i e = some (r, m')) :
    ∃ b a', (ConRon.Arena.hasLooseBVarBFast i.toNat (decE e)).run a = .ok (b, a') ∧
      r = (if b then 1 else 0) ∧ (∃ mp1, hbMR m' mp1) ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  by_cases h0 : rdW (m.arr64 CTL) hbSch.cs + 2 = 0
  · simp [hbFastW, h0] at hm
  rw [hbFastW_eq n _ i e h0] at hm
  have hf0 := mclearG_frame hbSch m
  have hM0 := memoRV_clear hbSch hbSch_wf lfKey hbVR m mp0 hM h0
  have key := StageR.frame_hi hS hf0 (by simp) (by
      intro x hx; simp [hbSch] at hx; rcases hx with rfl | rfl <;> decide) (by simp) (by simp [hbSch])
  obtain ⟨b, mp1, a', hrun, hb, hM1, hS1, hg⟩ :=
    hbGoOK n _ _ a i e _ ∅ coreWalkFuel hn (Nat.le_refl _) hm key.1 hh hM0
  refine ⟨b, a', ?_, hb, ⟨mp1, hM1⟩, hS1, key.2.trans hg⟩
  simp only [ConRon.Arena.hasLooseBVarBFast, StateT.run_bind]
  rw [hrun]
  rfl

section hbCensus2
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p)
  (hcl : p.lookup "hb_clear" = some (memoClearG hbSch))
  (hp : p.lookup "has_loose_b_var_b_fast" = some hasLooseBVarBFastL)
include hv hf hput hins hgo hbp hcl hp

/-- **`has_loose_b_var_b_fast` refines `hasLooseBVarBFast`**: clear the `hb` memo (any well-formed one
on entry), one memoised walk from `coreWalkFuel`. -/
@[refines ConRon.Arena.hasLooseBVarBFast]
theorem hasLooseBVarBFast_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis i e : Word) (mp0 : Std.HashMap (EIdx × Nat) Bool) (hn : 2 ^ 31 + n ≤ coreWalkFuel)
    (hh : H e) (hS : StageR dn vis fe s₀.mem a₀) (hM : hbMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "has_loose_b_var_b_fast" [i, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.hasLooseBVarBFast i.toNat (decE e)) a₀ ∧
      r.headD 0 = (if AM.res (ConRon.Arena.hasLooseBVarBFast i.toNat (decE e)) a₀ then 1 else 0) ∧
      (∃ mp1, hbMR s'.mem mp1) ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.hasLooseBVarBFast i.toNat (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (hbFast_spec p hv hf hput hins hgo hbp hcl hp n s₀ i e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun', hb, hM1, hS1, hg⟩ := hbFastW_ok n _ _ a₀ i e _ mp0 hn hh hS hM hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  exact ⟨hl, hok, by rw [hres]; exact hb, hM1, by rw [hst]; exact hS1, hg⟩

end hbCensus2
