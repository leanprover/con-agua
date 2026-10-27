import ConAgua.Arena.LdRd
import ConAgua.Arena.IndPosSpec.NodeV
import ConAgua.Arena.IndPosSpec.MatesW
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# McGoStep

`mcGoW`, `mcG1`, `mcG3`, `mcG4`, `mcG5`, `mcNodeW` and the lemmas only they use.
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
def mcGoW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, f, T, h => if f = 0 then none else mcG1 n f m T h (eViewW m h)
def mcG1 (n : Nat) (f : Word) (m : Mem) (T h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 then some (0, m)
  else if v.headD 0 = 3 then some (if v.tail.headD 0 = T then 1 else 0, m)
  else mcG3 n f m T h v (mfindG mcSch m h 0)
def mcG3 (n : Nat) (f : Word) (m : Mem) (T h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 MCM) (fr.tail.headD 0 * 4 + 3), m)
  else mcG4 h (mcNodeW n f m T (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def mcG4 (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => mcG5 r (msetG mcSch m1 h 0 r)
def mcG5 (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 => some (r, m2)
def mcNodeW (n : Nat) (f : Word) (m : Mem) (T g x y z : Word) : Option (Word × Mem) :=
  if g = 1 then mcGoW n m (f - 1) T y
  else if g = 4 ∨ g = 5 ∨ g = 6 then mcB1 n f T y (mcGoW n m (f - 1) T x)
  else if g = 7 then mcL1 n f T y z (mcGoW n m (f - 1) T x)
  else mcP1 T x (mcGoW n m (f - 1) T z)
def mcB1 (n : Nat) (f T y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => mcB2 b1 (mcGoW n m1 (f - 1) T y)
def mcB2 (b1 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b2, m2) => some (b1 ||| b2, m2)
def mcL1 (n : Nat) (f T y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => mcL2 n f T z b1 (mcGoW n m1 (f - 1) T y)
def mcL2 (n : Nat) (f T z b1 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b2, m2) => mcL3 b1 b2 (mcGoW n m2 (f - 1) T z)
def mcL3 (b1 b2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b3, m3) => some (b1 ||| b2 ||| b3, m3)
def mcP1 (T x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => some ((if x = T then 1 else 0) ||| b1, m1)
end

section mcArms
variable (n : Nat) (m m1 m2 m3 : Mem) (f T h g x y z b1 b2 b3 r : Word) (v fr : List Word)
theorem mcGoW_zeroF (hf : f = 0) : mcGoW (n + 1) m f T h = none := by simp [mcGoW, hf]
theorem mcGoW_view (hf : f ≠ 0) : mcGoW (n + 1) m f T h = mcG1 n f m T h (eViewW m h) := by
  simp [mcGoW, hf]
theorem mcG1_leaf (hv : v ≠ []) (hg : v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8) :
    mcG1 n f m T h v = some (0, m) := by simp only [mcG1]; rw [ite_eq_right hv, ite_eq_left hg]
theorem mcG1_const (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : v.headD 0 = 3) : mcG1 n f m T h v = some (if v.tail.headD 0 = T then 1 else 0, m) := by
  simp only [mcG1]; rw [ite_eq_right hv, ite_eq_right hg, ite_eq_left h3]
theorem mcG1_node (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : ¬ v.headD 0 = 3) : mcG1 n f m T h v = mcG3 n f m T h v (mfindG mcSch m h 0) := by
  simp only [mcG1]; rw [ite_eq_right hv, ite_eq_right hg, ite_eq_right h3]
theorem mcG3_abort (hr : fr = []) : mcG3 n f m T h v fr = none := by simp [mcG3, hr]
theorem mcG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    mcG3 n f m T h v fr = some (rdW (m.arr64 MCM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [mcG3]; rw [ite_eq_right hr, ite_eq_left hh]
theorem mcG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    mcG3 n f m T h v fr = mcG4 h (mcNodeW n f m T (v.headD 0) (v.tail.headD 0)
      (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [mcG3]; rw [ite_eq_right hr, ite_eq_right hh]
theorem mcG4_some : mcG4 h (some (r, m1)) = mcG5 r (msetG mcSch m1 h 0 r) := by rw [mcG4]
theorem mcG5_some : mcG5 r (some m2) = some (r, m2) := by rw [mcG5]
theorem mcNodeW_fvar (hg : g = 1) : mcNodeW n f m T g x y z = mcGoW n m (f - 1) T y := by simp [mcNodeW, hg]
theorem mcNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) : mcNodeW n f m T g x y z =
    mcB1 n f T y (mcGoW n m (f - 1) T x) := by
  have : ¬ g = 1 := by
    intro e; rcases hg with h | h | h <;> (rw [e] at h; exact absurd h (by decide))
  simp only [mcNodeW]; rw [ite_eq_right this, ite_eq_left hg]
theorem mcNodeW_let (hg : g = 7) : mcNodeW n f m T g x y z = mcL1 n f T y z (mcGoW n m (f - 1) T x) := by
  simp [mcNodeW, hg]
theorem mcNodeW_proj (hg1 : g ≠ 1) (hg2 : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (hg3 : g ≠ 7) :
    mcNodeW n f m T g x y z = mcP1 T x (mcGoW n m (f - 1) T z) := by
  simp only [mcNodeW]; rw [ite_eq_right hg1, ite_eq_right hg2, ite_eq_right hg3]
theorem mcB1_some : mcB1 n f T y (some (b1, m1)) = mcB2 b1 (mcGoW n m1 (f - 1) T y) := by rw [mcB1]
theorem mcB2_some : mcB2 b1 (some (b2, m2)) = some (b1 ||| b2, m2) := by rw [mcB2]
theorem mcL1_some : mcL1 n f T y z (some (b1, m1)) = mcL2 n f T z b1 (mcGoW n m1 (f - 1) T y) := by rw [mcL1]
theorem mcL2_some : mcL2 n f T z b1 (some (b2, m2)) = mcL3 b1 b2 (mcGoW n m2 (f - 1) T z) := by rw [mcL2]
theorem mcL3_some : mcL3 b1 b2 (some (b3, m3)) = some (b1 ||| b2 ||| b3, m3) := by rw [mcL3]
theorem mcP1_some : mcP1 T x (some (b1, m1)) = some ((if x = T then 1 else 0) ||| b1, m1) := by rw [mcP1]
end mcArms

attribute [ind_grind] mcGoW_zeroF mcGoW_view mcG1_leaf mcG1_const mcG1_node mcG3_abort mcG3_hit
  mcG3_miss mcG4_some mcG5_some mcNodeW_fvar mcNodeW_bin mcNodeW_let mcNodeW_proj mcB1_some
  mcB2_some mcL1_some mcL2_some mcL3_some mcP1_some

section mcspec
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "mc_find" = some (memoFindG mcSch)) (hput : p.lookup "mc_put" = some (memoPutG mcSch))
  (hgo : p.lookup "mentions_const_go" = some mentionsConstGoL)

def McGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (f T h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mentions_const_go" [f, T, h]
    ⦃fun r s' => LocEq s' s₀ ∧ mcGoW n s₀.mem f T h = some (r.headD 0, s'.mem); ⊤⦄

set_option maxHeartbeats 2000000 in
include hv hf hput hgo in
theorem mcGo_step (n : Nat) (ih : McGoSpec p n) : McGoSpec p (n + 1) := by
  unfold McGoSpec at ih
  intro s₀ f T h
  rw [invoke_eq _ hgo]
  simp only [callFn, mentionsConstGoL]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64_rd_spec,
    eView_spec p hv n, memoFindG_spec mcSch p _ hf n,
    memoPutG_spec mcSch p _ hput n, ih]
  all_goals subst_vars
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    beq_iff_eq, bne_iff_ne, ne_eq, Cond.pval, Expr.pval, Bool.or_eq_true] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind]

include hv hf hput hgo in
theorem mcGo_spec (n : Nat) : McGoSpec p n := by
  induction n with
  | zero => intro s₀ f T h; rw [invoke_eq _ hgo]; simp only [callFn, mentionsConstGoL]; vcgen [exec] <;> grind
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

/-- The post of the `mentions_const_go` walk from `m`, `a`: the twin state unchanged, the result
decoded, the memo related, only the memo written. -/
abbrev McQ (m : Mem) (a : AState) (r : Word) (x : Bool × Std.HashMap EIdx Bool) (m' : Mem)
    (a' : AState) : Prop :=
  a = a' ∧ (r != 0) = x.1 ∧ mcMR m' x.2 ∧ MemFrame [MCM] [217] m m'

def McGoOK (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (f T h : Word) (mp : Std.HashMap EIdx Bool),
    ArenaR m a → H h → H T → mcMR m mp →
    Sim (mcGoW n m f T h) (ConRon.Arena.mentionsConstGo (decI T) mp f.toNat (decE h)) a (McQ m a)

theorem word_or_ne (a b : Word) : ((a ||| b) != 0) = ((a != 0) || (b != 0)) := by
  rw [Bool.eq_iff_iff]
  simp [UInt64.or_eq_zero_iff]
  by_cases h1 : a = 0 <;> by_cases h2 : b = 0 <;> simp [h1, h2]

/-- A twin run rewritten (an unfolding at the state `a`). -/
theorem Sim.ofRun {β α : Type} {mo : Option (β × Mem)} {op op' : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (e : op.run a = op'.run a) (h : Sim mo op' a Q) :
    Sim mo op a Q := fun r m' hm => by
  obtain ⟨x, a', h1, h2⟩ := h r m' hm; exact ⟨x, a', e ▸ h1, h2⟩

theorem mcNode_arm (k : Nat) (ih : McGoOK k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeV v) (m : Mem) (a : AState) (T f : Word) (mp : Std.HashMap EIdx Bool)
    (hA : ArenaR m a) (hT : H T) (hM : mcMR m mp) :
    Sim (mcNodeW k f m T (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0)) (mcArm (decI T) mp (f - 1).toNat v) a (McQ m a) := by
  have bin : ∀ (g x y : Word), (g = 4 ∨ g = 5 ∨ g = 6) → H x → H y →
      Sim (mcNodeW k f m T g x y (vl.tail.tail.tail.headD 0)) (do
        let (b1, m) ← ConRon.Arena.mentionsConstGo (decI T) mp (f - 1).toNat (decE x)
        let (b2, m2) ← ConRon.Arena.mentionsConstGo (decI T) m (f - 1).toNat (decE y)
        pure (b1 || b2, m2) : AM (Bool × Std.HashMap EIdx Bool)) a (McQ m a) := by
    intro g x y hg hx hy
    rw [mcNodeW_bin k m f T g x y _ hg]
    refine Sim.bindK (by rw [mcB1]) (fun _ _ => by rw [mcB1]) (ih m a _ T x mp hA hx hT hM) ?_
    rintro r1 ⟨c1, mp1⟩ m1 _ ⟨rfl, hb1, hM1, hf1⟩
    refine Sim.bindK (by rw [mcB2]) (fun _ _ => by rw [mcB2]) (ih m1 a _ T y mp1 (mcFrame_arena hf1 hA) hy hT hM1) ?_
    rintro r2 ⟨c2, mp2⟩ m2 _ ⟨rfl, hb2, hM2, hf2⟩
    exact Sim.ret ⟨rfl, by rw [word_or_ne, hb1, hb2], hM2, hf1.trans hf2⟩
  cases v with
  | fvar i ty =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, -, hy, hdy⟩ := hvr
    rw [hg, mcNodeW_fvar k m f T 1 _ _ _ rfl, mcArm, ← hdy]
    exact ih m a _ T _ mp hA hy hT hM
  | app f0 x' | lam f0 x' | forallE f0 x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    simp only [mcArm, ← hdx, ← hdy]
    exact bin _ _ _ (by first | exact Or.inl hg | exact Or.inr (Or.inl hg) | exact Or.inr (Or.inr hg))
      hx hy
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
    rw [hg, mcNodeW_let k m f T 7 _ _ _ rfl]
    simp only [mcArm, ← hdx, ← hdy, ← hdz]
    refine Sim.bindK (by rw [mcL1]) (fun _ _ => by rw [mcL1]) (ih m a _ T _ mp hA hx hT hM) ?_
    rintro r1 ⟨c1, mp1⟩ m1 _ ⟨rfl, hb1, hM1, hf1⟩
    refine Sim.bindK (by rw [mcL2]) (fun _ _ => by rw [mcL2]) (ih m1 a _ T _ mp1 (mcFrame_arena hf1 hA) hy hT hM1) ?_
    rintro r2 ⟨c2, mp2⟩ m2 _ ⟨rfl, hb2, hM2, hf2⟩
    refine Sim.bindK (by rw [mcL3]) (fun _ _ => by rw [mcL3])
      (ih m2 a _ T _ mp2 (mcFrame_arena (hf1.trans hf2) hA) hz hT hM2) ?_
    rintro r3 ⟨c3, mp3⟩ m3 _ ⟨rfl, hb3, hM3, hf3⟩
    exact Sim.ret ⟨rfl, by rw [word_or_ne, word_or_ne, hb1, hb2, hb3], hM3,
      (hf1.trans hf2).trans hf3⟩
  | proj s i e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, -, hz, hdz⟩ := hvr
    rw [hg, mcNodeW_proj k m f T 9 _ _ _ (by decide) (by decide) (by decide)]
    simp only [mcArm, ← hdx, ← hdz]
    refine Sim.bindK (by rw [mcP1]) (fun _ _ => by rw [mcP1]) (ih m a _ T _ mp hA hz hT hM)
      fun r1 ⟨c1, mp1⟩ m1 _ ⟨rfl, hb1, hM1, hf1⟩ => Sim.ret ⟨rfl, ?_, hM1, hf1⟩
    rw [word_or_ne, hb1, decI_beq' _ T hx hT]
    generalize vl.tail.headD 0 = xx
    by_cases e2 : xx = T <;> simp [e2]
  | bvar _ | sort _ | const _ _ | lit _ => exact False.elim hnv

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

theorem mcGo_step_ok (j : Nat) (ih : ∀ k, k < j + 1 → McGoOK k) : McGoOK (j + 1) := by
  intro m a f T h mp hA hh hT hM
  by_cases hf0 : f = 0
  · rw [mcGoW_zeroF j m f T h hf0]; exact Sim.of_none
  rw [mcGoW_view j m f T h hf0]
  have hF : f.toNat = (f - 1).toNat + 1 := by
    have : f.toNat ≠ 0 := fun e => hf0 (UInt64.toNat_inj.mp (by simpa using e))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  rw [hF]
  cases hvl : eViewW m h with
  | nil => simp only [mcG1, ite_true]; exact Sim.of_none
  | cons g vt =>
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA h (by rw [hvl]; simp)
    rw [hvl] at hvr
    cases v with
    | bvar _ | sort _ | lit _ =>
      rw [mentionsConstGo_succ']
      refine Sim.bind_twin (view_run _ a _ hv) ?_
      simp only [ViewR] at hvr
      rw [mcG1_leaf j m f T h _ (by simp) (by
        first | exact Or.inl hvr.1 | exact Or.inr (Or.inl hvr.1) | exact Or.inr (Or.inr hvr))]
      exact Sim.ret ⟨rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | const nn us =>
      rw [mentionsConstGo_succ']
      refine Sim.bind_twin (view_run _ a _ hv) ?_
      simp only [ViewR, getD1_eq'] at hvr
      obtain ⟨hg3, hx, hdx, -⟩ := hvr
      rw [mcG1_const j m f T h _ (by simp) (by rw [hg3]; decide) hg3]
      refine Sim.ret ⟨rfl, ?_, hM, MemFrame.refl _ _ _⟩
      show _ = (nn == decI T)
      rw [← hdx, decI_beq' _ T hx hT]
      generalize (g :: vt).tail.headD 0 = xx
      by_cases e : xx = T <;> simp [e]
    | fvar _ _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ | proj _ _ _ =>
      have hgs : g = 1 ∨ g = 4 ∨ g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 9 := by
        have := hvr.1; simp only [List.headD_cons] at this; simp [this]
      have hnl : ¬ ((g :: vt).headD 0 = 0 ∨ (g :: vt).headD 0 = 2 ∨ (g :: vt).headD 0 = 8) := by
        rcases hgs with e | e | e | e | e | e <;> simp only [List.headD_cons, e] <;> decide
      have hn3 : ¬ (g :: vt).headD 0 = 3 := by
        rcases hgs with e | e | e | e | e | e <;> simp only [List.headD_cons, e] <;> decide
      rw [mcG1_node j m f T h _ (by simp) hnl hn3]
      refine Sim.ofRun (mcTwin_node _ _ _ _ a _ hv trivial) ?_
      by_cases hfr : mfindG mcSch m h 0 = []
      · rw [mcG3_abort j m f T h _ _ hfr]; exact Sim.of_none
      by_cases hhit : (mfindG mcSch m h 0).headD 0 ≠ 0
      · rw [mcG3_hit j m f T h _ _ hfr hhit]
        have hmem := memoRG_hit mcSch bmKey (fun w : Word => w != 0) m mp hM h 0 hfr hhit ⟨hh, rfl⟩
        change mp[decE h]? = _ at hmem
        simp only [hmem]
        exact Sim.ret ⟨rfl, rfl, hM, MemFrame.refl _ _ _⟩
      rw [mcG3_miss j m f T h _ _ hfr hhit]
      have hmiss := memoRG_miss mcSch bmKey (fun w : Word => w != 0) m mp hM h 0 ⟨hh, rfl⟩ hfr
        (by simpa using hhit)
      change mp[decE h]? = _ at hmiss
      simp only [hmiss]
      refine Sim.bindK (by rw [mcG4]) (fun _ _ => by rw [mcG4])
        (mcNode_arm j (ih j (by omega)) _ _ hvr trivial m a T f mp hA hT hM) ?_
      rintro rn ⟨bb, mp1⟩ m1 _ ⟨rfl, hbb, hM1, hfr1⟩
      rcases hset : msetG mcSch m1 h 0 rn with _ | m2
      · exact Sim.of_none
      refine Sim.ret ⟨rfl, hbb, ?_, hfr1.trans
        ((msetG_frame mcSch mcSch_wf m1 m2 h 0 rn hset).mono (by simp [mcSch]) (by simp [mcSch]))⟩
      rw [← hbb]
      exact memoRG_set mcSch mcSch_wf bmKey (fun w : Word => w != 0) m1 mp1 hM1 h 0 rn ⟨hh, rfl⟩ m2 hset

theorem mcGoOK (n : Nat) : McGoOK n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro m a f T h mp; simp only [mcGoW]; exact fun _ _ _ _ => Sim.of_none
    | succ j => exact mcGo_step_ok j (fun k hk => ih k (by omega))

/-! ## The `hb` memo walks: callees outside this lane

`bvar_b` is lane `exprops4`'s real function (`bvarBL`, `BvarBRefine.lean`), run under the stage relation
(`bvbW_stage`, lane `indproofs2`); `strip_pis` (`StripTeleSpec.lean`) leaves the `hb` memo alone by
its write set `stripF_frame`. -/

section hbStubs
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- **`bvar_b` (lane `exprops4`'s, no longer a stub here) under the stage relation**: its model
refines `bvarB` at every twin fuel `F ≥ f` or `F + 1 ≥ n`; it writes only the `bvarB` memo (array `BMEMO` = 24,
`CTL[24]`, `CTL[25]`), so the stage relation holds after and the pool did not change. -/
theorem bvbW_stageW {m m' : Mem} {a : AState} (hS : StageR dn vis fe m a) (n F : Nat) (f : Word)
    (hF : f.toNat ≤ F ∨ n ≤ F + 1) (h x : Word) (hh : H h) (hb : bvbW n m h f = some (x, m')) :
    ∃ a', (bvarB F (decE h)).run a = .ok (x.toNat, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      BbFrame m m' := by
  obtain ⟨a', hrun, hD⟩ := bvbW_okF n F m m' a hS.1.arena h f x hh hF hb
  have hfr : BbFrame m m' := by
    match n, hb with
    | n + 1, hb =>
      by_cases hs : derBW m h = 32767
      · rw [bvbW_sat (n := n) (m := m) (h := h) (f := f) hs] at hb
        match n, hb with
        | k + 1, hb => rw [bbN_succ] at hb; exact bbMemoW_frame k m m' h f x hb
      · rw [bvbW_pk (n := n) (m := m) (h := h) (f := f) hs] at hb
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
def hbGoW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, f, i, h => if f = 0 then none else hbK1 n f i h (bvbW n m h (f - 1))
def hbK1 (n : Nat) (f i h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m1) => if x ≤ i then some (0, m1) else hbK2 n f m1 i h (eViewW m1 h)
def hbK2 (n : Nat) (f : Word) (m : Mem) (i h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 then some (if i = v.tail.headD 0 then 1 else 0, m)
  else if v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8 then some (0, m)
  else if 4294967296 ≤ i then none
  else hbK3 n f m i h v (mfindG hbSch m h i)
def hbK3 (n : Nat) (f : Word) (m : Mem) (i h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 HBM) (fr.tail.headD 0 * 4 + 3), m)
  else hbK4 h i (hbNodeW n f m i (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def hbK4 (h i : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => hbInsW m1 h i r
def hbNodeW (n : Nat) (f : Word) (m : Mem) (i g x y z : Word) : Option (Word × Mem) :=
  if g = 4 then hbO1 n f i y (hbGoW n m (f - 1) i x)
  else if g = 5 ∨ g = 6 then hbO1 n f (i + 1) y (hbGoW n m (f - 1) i x)
  else if g = 7 then hbL1 n f i y z (hbGoW n m (f - 1) i x)
  else hbGoW n m (f - 1) i z
def hbO1 (n : Nat) (f i2 y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r1, m1) => if r1 = 1 then some (1, m1) else hbGoW n m1 (f - 1) i2 y
def hbL1 (n : Nat) (f i y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r1, m1) => if r1 = 1 then some (1, m1) else hbL2 n f i z (hbGoW n m1 (f - 1) i y)
def hbL2 (n : Nat) (f i z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r2, m2) => if r2 = 1 then some (1, m2) else hbGoW n m2 (f - 1) (i + 1) z
end

section hbArms
variable (n : Nat) (m m1 m2 : Mem) (f i i2 h g x y z r r1 r2 w : Word) (v fr rs : List Word)
theorem hbGoW_zeroF (hf : f = 0) : hbGoW (n + 1) m f i h = none := by simp [hbGoW, hf]
theorem hbGoW_succ (hf : f ≠ 0) : hbGoW (n + 1) m f i h = hbK1 n f i h (bvbW n m h (f - 1)) := by
  simp [hbGoW, hf]
theorem hbK1_some_le (hle : w ≤ i) : hbK1 n f i h (some (w, m1)) = some (0, m1) := by
  simp only [hbK1]; rw [ite_eq_left hle]
theorem hbK1_some_gt (hle : ¬ w ≤ i) :
    hbK1 n f i h (some (w, m1)) = hbK2 n f m1 i h (eViewW m1 h) := by
  simp only [hbK1]; rw [ite_eq_right hle]
theorem hbK2_bvar (hv : v ≠ []) (hg : v.headD 0 = 0) :
    hbK2 n f m i h v = some (if i = v.tail.headD 0 then 1 else 0, m) := by
  simp only [hbK2]; rw [ite_eq_right hv, ite_eq_left hg]
theorem hbK2_leaf (hv : v ≠ []) (hg0 : ¬ v.headD 0 = 0)
    (hg : v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8) :
    hbK2 n f m i h v = some (0, m) := by
  simp only [hbK2]; rw [ite_eq_right hv, ite_eq_right hg0, ite_eq_left hg]
theorem hbK2_big (hv : v ≠ []) (hg0 : ¬ v.headD 0 = 0)
    (hg : ¬ (v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8)) (hi : 4294967296 ≤ i) :
    hbK2 n f m i h v = none := by
  simp only [hbK2]; rw [ite_eq_right hv, ite_eq_right hg0, ite_eq_right hg, ite_eq_left hi]
theorem hbK2_node (hv : v ≠ []) (hg0 : ¬ v.headD 0 = 0)
    (hg : ¬ (v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8)) (hi : ¬ 4294967296 ≤ i) :
    hbK2 n f m i h v = hbK3 n f m i h v (mfindG hbSch m h i) := by
  simp only [hbK2]; rw [ite_eq_right hv, ite_eq_right hg0, ite_eq_right hg, ite_eq_right hi]
theorem hbK3_abort (hr : fr = []) : hbK3 n f m i h v fr = none := by simp [hbK3, hr]
theorem hbK3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    hbK3 n f m i h v fr = some (rdW (m.arr64 HBM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [hbK3]; rw [ite_eq_right hr, ite_eq_left hh]
theorem hbK3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    hbK3 n f m i h v fr = hbK4 h i (hbNodeW n f m i (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
      (v.tail.tail.tail.headD 0)) := by
  simp only [hbK3]; rw [ite_eq_right hr, ite_eq_right hh]
theorem hbK4_some : hbK4 h i (some (r, m1)) = hbInsW m1 h i r := by rw [hbK4]
theorem hbNodeW_4 (hg : g = 4) : hbNodeW n f m i g x y z = hbO1 n f i y (hbGoW n m (f - 1) i x) := by
  simp [hbNodeW, hg]
theorem hbNodeW_56 (hg : g = 5 ∨ g = 6) : hbNodeW n f m i g x y z =
    hbO1 n f (i + 1) y (hbGoW n m (f - 1) i x) := by
  have : ¬ g = 4 := by rcases hg with e | e <;> (rw [e]; decide)
  simp only [hbNodeW]; rw [ite_eq_right this, ite_eq_left hg]
theorem hbNodeW_7 (hg : g = 7) : hbNodeW n f m i g x y z = hbL1 n f i y z (hbGoW n m (f - 1) i x) := by
  simp [hbNodeW, hg]
theorem hbNodeW_9 (hg1 : g ≠ 4) (hg2 : ¬ (g = 5 ∨ g = 6)) (hg3 : g ≠ 7) :
    hbNodeW n f m i g x y z = hbGoW n m (f - 1) i z := by
  simp only [hbNodeW]; rw [ite_eq_right hg1, ite_eq_right hg2, ite_eq_right hg3]
theorem hbO1_one (hr : r1 = 1) : hbO1 n f i2 y (some (r1, m1)) = some (1, m1) := by simp [hbO1, hr]
theorem hbO1_ne (hr : ¬ r1 = 1) : hbO1 n f i2 y (some (r1, m1)) = hbGoW n m1 (f - 1) i2 y := by
  simp [hbO1, hr]
theorem hbL1_one (hr : r1 = 1) : hbL1 n f i y z (some (r1, m1)) = some (1, m1) := by simp [hbL1, hr]
theorem hbL1_ne (hr : ¬ r1 = 1) :
    hbL1 n f i y z (some (r1, m1)) = hbL2 n f i z (hbGoW n m1 (f - 1) i y) := by simp [hbL1, hr]
theorem hbL2_one (hr : r2 = 1) : hbL2 n f i z (some (r2, m2)) = some (1, m2) := by simp [hbL2, hr]
theorem hbL2_ne (hr : ¬ r2 = 1) : hbL2 n f i z (some (r2, m2)) = hbGoW n m2 (f - 1) (i + 1) z := by
  simp [hbL2, hr]
end hbArms

attribute [ind_grind] hbGoW_zeroF hbGoW_succ hbK1_some_le hbK1_some_gt hbK2_bvar hbK2_leaf hbK2_big
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
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceEqDiff, reduceIte] at *)
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

def HbGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (f i h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "has_loose_b_var_b_go" [f, i, h]
    ⦃fun r s' => LocEq s' s₀ ∧ hbGoW n s₀.mem f i h = some (r.headD 0, s'.mem); ⊤⦄

set_option maxHeartbeats 4000000 in
include hv hf hput hins hgo hbp in
theorem hbGo_step (n : Nat) (ih : HbGoSpec p n) : HbGoSpec p (n + 1) := by
  unfold HbGoSpec at ih
  intro s₀ f i h
  rw [invoke_eq _ hgo]
  simp only [callFn, hasLooseBVarBGoL]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64_rd_spec,
    bvarBL_spec p hbp n, eView_spec p hv n, memoFindG_spec hbSch p _ hf n,
    hbIns_spec p hf hput hins n, ih]
  all_goals subst_vars
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    beq_iff_eq, bne_iff_ne, ne_eq, Cond.pval, Expr.pval, Bool.or_eq_true, decide_eq_true_eq] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind]

include hv hf hput hins hgo hbp in
theorem hbGo_spec (n : Nat) : HbGoSpec p n := by
  induction n with
  | zero =>
    intro s₀ f i h; rw [invoke_eq _ hgo]; simp only [callFn, hasLooseBVarBGoL]; vcgen [exec] <;> grind
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

/-- The post of the `has_loose_b_var_b_go` walk from `m`. -/
abbrev HbQ (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (r : Word)
    (x : Bool × Std.HashMap (EIdx × Nat) Bool) (m' : Mem) (a' : AState) : Prop :=
  r = (if x.1 then 1 else 0) ∧ hbMR m' x.2 ∧ StageR dn vis fe m' a' ∧ IWGrow m m'

/-- `HbQ` for an arm whose twin result is `ins` of the walk's (the memo insertion). -/
abbrev HbQi (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (ins : Bool × Std.HashMap (EIdx × Nat) Bool → Bool × Std.HashMap (EIdx × Nat) Bool) (m : Mem)
    (r : Word) (y : Bool × Std.HashMap (EIdx × Nat) Bool) (m' : Mem) (a' : AState) : Prop :=
  ∃ x, y = ins x ∧ HbQ dn vis fe m r x m' a'

/-- `HbOK n`: the word model at depth `n` and fuel word `f` refines the twin at fuel `f.toNat`. -/
def HbOK (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (f i h : Word) (mp : Std.HashMap (EIdx × Nat) Bool),
    StageR dn vis fe m a → H h → hbMR m mp →
    Sim (hbGoW n m f i h) (ConRon.Arena.hasLooseBVarBGo mp i.toNat f.toNat (decE h)) a
      (HbQ dn vis fe m)

theorem word_toNat_add_one {i : Word} (hi : ¬ 4294967296 ≤ i) : (i + 1).toNat = i.toNat + 1 := by
  have : i.toNat < 4294967296 :=
    Nat.lt_of_not_ge (fun hc => hi (UInt64.le_iff_toNat_le.mpr (by simpa using hc)))
  rw [UInt64.toNat_add]; simp; omega

/-- A last callee whose result the twin maps by `g`. -/
theorem Sim.bindRet {β α δ : Type} {mo : Option (β × Mem)} {op : AM α} {g : α → δ} {a : AState}
    {Q : β → α → Mem → AState → Prop} {R : β → δ → Mem → AState → Prop} (h : Sim mo op a Q)
    (hq : ∀ r x m a', Q r x m a' → R r (g x) m a') : Sim mo (op >>= fun x => pure (g x)) a R :=
  fun r m' e => by
    obtain ⟨x, a', h1, h2⟩ := h r m' e
    exact ⟨g x, a', by simp only [StateT.run_bind, h1]; rfl, hq _ _ _ _ h2⟩

/-- A continuation of the model only (the twin's step already done in `op`). -/
theorem Sim.bindM {β γ α : Type} {K : Option (β × Mem) → Option (γ × Mem)}
    {body : β → Mem → Option (γ × Mem)} {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} {R : γ → α → Mem → AState → Prop}
    (hn : K Option.none = Option.none) (hs : ∀ r m₁, K (some (r, m₁)) = body r m₁)
    (h1 : Sim mo op a Q) (h2 : ∀ r x m₁ a₁, Q r x m₁ a₁ → ∀ r' m', body r m₁ = some (r', m') →
      R r' x m' a₁) : Sim (K mo) op a R := by
  intro r m' e
  rcases hmo : mo with _ | ⟨r₁, m₁⟩
  · rw [hmo, hn] at e; cases e
  rw [hmo, hs] at e
  obtain ⟨x, a₁, hr1, hQ⟩ := h1 r₁ m₁ hmo
  exact ⟨x, a₁, hr1, h2 _ _ _ _ hQ _ _ e⟩

theorem hbL2_eq (n : Nat) (f i z : Word) (o : Option (Word × Mem)) :
    hbL2 n f i z o = hbO1 n f (i + 1) z o := by
  rcases o with _ | ⟨_, _⟩ <;> simp only [hbL2, hbO1]

/-- `or`-shaped arms: the first call, then (on `false`) the second; `ins` is the memo insertion
that follows (pushed into the branches by the twin's `do`). -/
theorem hbOr_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat)
    (ih : HbOK dn vis fe n) (m : Mem) (a : AState) (i i2 x y f : Word)
    (mp : Std.HashMap (EIdx × Nat) Bool) (hx : H x) (hy : H y)
    (ins : Bool × Std.HashMap (EIdx × Nat) Bool → Bool × Std.HashMap (EIdx × Nat) Bool)
    (hS : StageR dn vis fe m a) (hM : hbMR m mp) :
    Sim (hbO1 n f i2 y (hbGoW n m (f - 1) i x)) (do
        match ← ConRon.Arena.hasLooseBVarBGo mp i.toNat (f - 1).toNat (decE x) with
        | (true, memo) => pure (ins (true, memo))
        | (false, memo) => do
          let r ← ConRon.Arena.hasLooseBVarBGo memo i2.toNat (f - 1).toNat (decE y)
          pure (ins r) : AM (Bool × Std.HashMap (EIdx × Nat) Bool)) a (HbQi dn vis fe ins m) := by
  refine Sim.bindK (by rw [hbO1]) (fun _ _ => rfl) (ih m a _ i x mp hS hx hM) ?_
  rintro r1 ⟨_ | _, mp1⟩ m1 a1 ⟨rfl, hM1, hS1, hg1⟩
  · rw [hbO1_ne (hr := by simp)]
    exact Sim.bindRet (ih m1 a1 _ i2 y mp1 hS1 hy hM1)
      fun _ x _ _ ⟨h1, h2, h3, h4⟩ => ⟨x, rfl, h1, h2, h3, hg1.trans h4⟩
  · rw [hbO1_one (hr := by simp)]
    exact Sim.ret ⟨_, rfl, rfl, hM1, hS1, hg1⟩

theorem hbNode_arm {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat)
    (ih : HbOK dn vis fe k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v) (hnv : HNodeV v)
    (m : Mem) (a : AState) (i : Word) (hE : EIdx) (f : Word) (mp : Std.HashMap (EIdx × Nat) Bool)
    (hi : ¬ 4294967296 ≤ i) (hS : StageR dn vis fe m a) (hM : hbMR m mp) :
    Sim (hbNodeW k f m i (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0)) (hbArm mp i.toNat (f - 1).toNat hE v) a
      (HbQi dn vis fe (ConRon.Arena.hasLooseBVarBIns hE i.toNat) m) := by
  cases v with
  | app f0 x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, rfl, hy, rfl⟩ := hvr
    rw [hbNodeW_4 (hg := hg)]
    exact hbOr_ok k ih m a i i _ _ f mp hx hy _ hS hM
  | lam f0 x' | forallE f0 x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, rfl, hy, rfl⟩ := hvr
    rw [hbNodeW_56 (hg := by first | exact Or.inl hg | exact Or.inr hg)]
    have := hbOr_ok k ih m a i (i + 1) _ _ f mp hx hy (ConRon.Arena.hasLooseBVarBIns hE i.toNat) hS hM
    rw [word_toNat_add_one hi] at this
    exact this
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, rfl, hy, rfl, hz, rfl⟩ := hvr
    rw [hbNodeW_7 (hg := hg)]
    refine Sim.bindK (by rw [hbL1]) (fun _ _ => rfl) (ih m a _ i _ mp hS hx hM) ?_
    rintro r1 ⟨_ | _, mp1⟩ m1 a1 ⟨rfl, hM1, hS1, hg1⟩
    · rw [hbL1_ne (hr := by simp), hbL2_eq]
      have := hbOr_ok k ih m1 a1 i (i + 1) _ _ f mp1 hy hz
        (ConRon.Arena.hasLooseBVarBIns hE i.toNat) hS1 hM1
      rw [word_toNat_add_one hi] at this
      exact this.mono fun _ _ _ _ ⟨x, e, h1, h2, h3, h4⟩ => ⟨x, e, h1, h2, h3, hg1.trans h4⟩
    · rw [hbL1_one (hr := by simp)]
      exact Sim.ret ⟨_, rfl, rfl, hM1, hS1, hg1⟩
  | proj s idx e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, -, hz, rfl⟩ := hvr
    rw [hbNodeW_9 (hg1 := by rw [hg]; decide) (hg2 := by rw [hg]; decide) (hg3 := by rw [hg]; decide)]
    exact Sim.bindRet (ih m a _ i _ mp hS hz hM) fun _ x _ _ h => ⟨x, rfl, h⟩
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ => exact False.elim hnv

theorem hbGo_nodeCase {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (j : Nat)
    (ih : HbOK dn vis fe j) (m : Mem) (a : AState) (i h f : Word)
    (mp : Std.HashMap (EIdx × Nat) Bool)
    (vl : List Word) (v : ENodeView) (hvr : ViewR vl v) (hnv : HNodeV v)
    (hv : a.store.view (decE h) = some v) (hvl : vl ≠ [])
    (hg0 : ¬ vl.headD 0 = 0)
    (hgl : ¬ (vl.headD 0 = 1 ∨ vl.headD 0 = 2 ∨ vl.headD 0 = 3 ∨ vl.headD 0 = 8))
    (hS : StageR dn vis fe m a) (hh : H h) (hM : hbMR m mp) :
    Sim (hbK2 j f m i h vl) (hbRestT mp i.toNat (f - 1).toNat (decE h)) a (HbQ dn vis fe m) := by
  by_cases hi : 4294967296 ≤ i
  · rw [hbK2_big j m f i h vl hvl hg0 hgl hi]; exact Sim.of_none
  rw [hbK2_node j m f i h vl hvl hg0 hgl hi]
  refine Sim.ofRun (hbTwin_node _ _ _ _ a v hv hnv) ?_
  by_cases hfr : mfindG hbSch m h i = []
  · rw [hbK3_abort j m f i h vl _ hfr]; exact Sim.of_none
  have hk : lfKey.ok h i := hh
  by_cases hhit : (mfindG hbSch m h i).headD 0 ≠ 0
  · rw [hbK3_hit j m f i h vl _ hfr hhit]
    obtain ⟨b, hb1, hb2⟩ := memoRV_hit hbSch lfKey hbVR m mp hM h i hfr hhit hk
    change mp[(decE h, i.toNat)]? = _ at hb1
    simp only [hb1]
    exact Sim.ret ⟨hb2, hM, hS, IWGrow.refl _⟩
  rw [hbK3_miss j m f i h vl _ hfr hhit]
  have hmiss := memoRV_miss hbSch lfKey hbVR m mp hM h i hk hfr (by simpa using hhit)
  change mp[(decE h, i.toNat)]? = _ at hmiss
  simp only [hmiss]
  refine Sim.bindM (by rw [hbK4]) (fun _ _ => rfl)
    (hbNode_arm j ih vl v hvr hnv m a i (decE h) f mp hi hS hM) ?_
  rintro rn _ m1 a1 ⟨⟨bb, mp1⟩, rfl, hbb, hM1, hS1, hg1⟩ r' m' hb
  obtain ⟨hr', hM2, hfr2⟩ := hbIns_ok hh hbb hM1 (by rw [← hbK4_some]; exact hb)
  obtain ⟨hS2, hg2⟩ := StageR.frame_hi hS1 hfr2 (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp at hx; subst hx; decide) (by decide) (by decide)
  exact ⟨by rw [hr']; exact hbb, hM2, hS2, hg1.trans hg2⟩

theorem hbGo_step_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (j : Nat)
    (ih : ∀ k, k < j + 1 → HbOK dn vis fe k) : HbOK dn vis fe (j + 1) := by
  intro m a f i h mp hS hh hM
  by_cases hf0 : f = 0
  · rw [hbGoW_zeroF j m f i h hf0]; exact Sim.of_none
  have hF : f.toNat = (f - 1).toNat + 1 := by
    have : f.toNat ≠ 0 := fun e => hf0 (UInt64.toNat_inj.mp (by simpa using e))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  rw [hbGoW_succ j m f i h hf0, hF, hasLooseBVarBGo_succ']
  refine Sim.bindD (by rw [hbK1]) (fun _ _ => rfl) (Sim.ofD fun w m1 hst =>
    bvbW_stageW dn vis fe hS j _ (f - 1) (.inl (Nat.le_refl _)) h w hh hst) ?_
  rintro w m1 a1 ⟨hS1, hg1, hfr⟩
  have hM1 : hbMR m1 mp := memoRV_frame hbSch hbSch_wf lfKey hbVR _ _ (by simp [hbSch, HBM, BMEMO])
    (by simp [hbSch]) m m1 hfr (fun _ _ h => h) mp hM
  by_cases hle : w ≤ i
  · rw [hbK1_some_le (hle := hle), ite_eq_left (UInt64.le_iff_toNat_le.mp hle)]
    exact Sim.ret ⟨rfl, hM1, hS1, hg1⟩
  rw [hbK1_some_gt (hle := hle), ite_eq_right fun c => hle (UInt64.le_iff_toNat_le.mpr c)]
  cases hvl : eViewW m1 h with
  | nil => simp only [hbK2, ite_true]; exact Sim.of_none
  | cons g vt =>
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m1 a1 hS1.1.arena.1 h (by rw [hvl]; simp)
    rw [hvl] at hvr
    cases v with
    | bvar i' =>
      have hg0 : (g :: vt).headD 0 = 0 := by simpa [ViewR] using hvr.1
      have hi' : ((g :: vt).tail.headD 0).toNat = i' := by rw [← getD1_eq']; exact hvr.2
      rw [hbK2_bvar j m1 f i h _ (by simp) hg0]
      unfold hbRestT
      refine Sim.bind_twin (view_run _ a1 _ hv) (Sim.ret ⟨?_, hM1, hS1, hg1⟩)
      generalize (g :: vt).tail.headD 0 = xx at hi' ⊢
      by_cases e : i = xx
      · have : i.toNat = i' := by rw [← hi', e]
        simp [e, hi']
      · have : i.toNat ≠ i' := fun c => e (UInt64.toNat_inj.mp (c.trans hi'.symm))
        simp [e, this]
    | fvar _ _ | sort _ | const _ _ | lit _ =>
      have hg0 : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 8 := by
        simp only [ViewR, List.headD_cons] at hvr; first | simp [hvr.1] | simp [hvr]
      rw [hbK2_leaf j m1 f i h _ (by simp) (by rcases hg0 with e | e | e | e <;> simp [e])
        (by simpa using hg0)]
      unfold hbRestT
      exact Sim.bind_twin (view_run _ a1 _ hv) (Sim.ret ⟨rfl, hM1, hS1, hg1⟩)
    | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ | proj _ _ _ =>
      have hgs : g = 4 ∨ g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 9 := by
        have := hvr.1; simp only [List.headD_cons] at this; simp [this]
      refine (hbGo_nodeCase j (ih j (by omega)) m1 a1 i h f mp _ _ hvr trivial hv (by simp)
        (by rcases hgs with e | e | e | e | e <;> simp [e])
        (by rcases hgs with e | e | e | e | e <;> simp [e]) hS1 hh hM1).mono
        fun _ _ _ _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hg1.trans h4⟩

theorem hbGoOK {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    HbOK dn vis fe n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro m a f i h mp; simp only [hbGoW]; exact fun _ _ _ => Sim.of_none
    | succ j => exact hbGo_step_ok j (fun k hk => ih k (by omega))

/-! ## `has_loose_b_var_b_fast` -/

def hbFastW (n : Nat) (m : Mem) (i e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) hbSch.cs + 2 = 0 then none else hbGoW n (mclearG hbSch m) CWF i e

theorem hbFastW_eq (n : Nat) (m : Mem) (i e : Word) (h0 : rdW (m.arr64 CTL) hbSch.cs + 2 ≠ 0) :
    hbFastW n m i e = hbGoW n (mclearG hbSch m) CWF i e := by simp [hbFastW, h0]
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
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Nat.reduceEqDiff, reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, ind_grind]

theorem hbFastW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat)
    (m m' : Mem) (a : AState) (i e r : Word) (mp0 : Std.HashMap (EIdx × Nat) Bool)
    (hh : H e) (hS : StageR dn vis fe m a) (hM : hbMR m mp0)
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
  obtain ⟨⟨b, mp1⟩, a', hrun, hb, hM1, hS1, hg⟩ := hbGoOK n _ a CWF i e ∅ key.1 hh hM0 _ _ hm
  refine ⟨b, a', ?_, hb, ⟨mp1, hM1⟩, hS1, key.2.trans hg⟩
  simp only [ConRon.Arena.hasLooseBVarBFast, StateT.run_bind]
  rw [CWF_eq] at hrun
  rw [hrun]
  rfl

end L.Ind
end
