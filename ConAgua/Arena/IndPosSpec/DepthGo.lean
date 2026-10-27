import ConAgua.Arena.IndPosSpec.InstW
import ConAgua.Arena.IndPosSpec.PcrK3
import ConAgua.Arena.IndPosSpec.PosmemoRxMfr
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# DepthGo: `ConRon.Arena.depthGo`, `ConRon.Arena.depth`, `ConRon.Arena.nestPhs`, `ConRon.Arena.whnfWalkFuel`

The refinement theorems `depthGo_refines`, `depth_refines`, `whnfWalkFuel_refines`, `nestPhs_refines` and the lemmas only they use.
-/

section


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (f f1 h g x y z d1 d2 d3 r : Word) (v fr : List Word)
theorem dpGoW_abort (hf : f = 0) : dpGoW (n + 1) m f h = none := by simp [dpGoW, hf]
theorem dpGoW_view (hf : f ≠ 0) : dpGoW (n + 1) m f h = dpG1 n m f h (eViewW m h) := by simp [dpGoW, hf]
theorem dpG1_leaf (hv : v ≠ [])
    (hg : v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8) :
    dpG1 n m f h v = some (1, m) := by simp only [dpG1]; rw [ite_eq_right hv, ite_eq_left hg]
theorem dpG1_node (hv : v ≠ [])
    (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8)) :
    dpG1 n m f h v = dpG3 n m f h v (mfindG dpSch m h 0) := by
  simp only [dpG1]; rw [ite_eq_right hv, ite_eq_right hg]
theorem dpG3_abort (hr : fr = []) : dpG3 n m f h v fr = none := by simp [dpG3, hr]
theorem dpG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    dpG3 n m f h v fr = some (rdW (m.arr64 DPM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [dpG3]; rw [ite_eq_right hr, ite_eq_left hh]
theorem dpG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    dpG3 n m f h v fr = dpG4 h (dpNodeW n m (f - 1) (v.headD 0) (v.tail.headD 0)
      (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [dpG3]; rw [ite_eq_right hr, ite_eq_right hh]
theorem dpG4_some : dpG4 h (some (r, m1)) = dpG5 r (msetG dpSch m1 h 0 r) := by rw [dpG4]
theorem dpG5_some : dpG5 r (some m2) = some (r, m2) := by rw [dpG5]
theorem dpNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) :
    dpNodeW (n + 1) m f1 g x y z = dpB1 n f1 y (dpGoW n m f1 x) := by
  simp only [dpNodeW]; rw [ite_eq_left hg]
theorem dpNodeW_let (hg : g = 7) : dpNodeW (n + 1) m f1 g x y z = dpL1 n f1 y z (dpGoW n m f1 x) := by
  have : ¬ (g = 4 ∨ g = 5 ∨ g = 6) := by
    intro e; rcases e with e | e | e <;> (rw [hg] at e; exact absurd e (by decide))
  simp only [dpNodeW]; rw [ite_eq_right this, ite_eq_left hg]
theorem dpNodeW_proj (hg2 : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (hg3 : g ≠ 7) :
    dpNodeW (n + 1) m f1 g x y z = dpP1 (dpGoW n m f1 z) := by
  simp only [dpNodeW]; rw [ite_eq_right hg2, ite_eq_right hg3]
theorem dpB1_some : dpB1 n f1 y (some (d1, m1)) = dpB2 d1 (dpGoW n m1 f1 y) := by rw [dpB1]
theorem dpB2_some : dpB2 d1 (some (d2, m2)) = dpFin (maxW d1 d2) m2 := by rw [dpB2]
theorem dpL1_some : dpL1 n f1 y z (some (d1, m1)) = dpL2 n f1 z d1 (dpGoW n m1 f1 y) := by rw [dpL1]
theorem dpL2_some : dpL2 n f1 z d1 (some (d2, m2)) = dpL3 d1 d2 (dpGoW n m2 f1 z) := by rw [dpL2]
theorem dpL3_some : dpL3 d1 d2 (some (d3, m3)) = dpFin (maxW (maxW d1 d2) d3) m3 := by rw [dpL3]
theorem dpP1_some : dpP1 (some (d1, m1)) = dpFin d1 m1 := by rw [dpP1]
theorem dpFin_big (hb : 4294967295 ≤ d1) : dpFin d1 m = none := by simp [dpFin, hb]
theorem dpFin_ok (hb : ¬ 4294967295 ≤ d1) : dpFin d1 m = some (d1 + 1, m) := by simp [dpFin, hb]
end arms
attribute [ind_grind] dpGoW_abort dpGoW_view dpG1_leaf dpG1_node dpG3_abort dpG3_hit dpG3_miss
  dpG4_some dpG5_some dpNodeW_bin dpNodeW_let dpNodeW_proj dpB1_some dpB2_some dpL1_some dpL2_some
  dpL3_some dpP1_some dpFin_big dpFin_ok

section spec
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "dp_find" = some (memoFindG dpSch)) (hput : p.lookup "dp_put" = some (memoPutG dpSch))
  (hgo : p.lookup "depth_go" = some depthGo) (hnode : p.lookup "depth_node" = some depthNode)

def DpGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "depth_go" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ dpGoW n s₀.mem f h = some (r.headD 0, s'.mem); ⊤⦄

def DpNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (f1 g x y z : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "depth_node" [f1, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ dpNodeW n s₀.mem f1 g x y z = some (r.headD 0, s'.mem); ⊤⦄

include hv hf hput hgo in
theorem dpGo_step (n : Nat) (ih : DpNodeSpec p n) : DpGoSpec p (n + 1) := by
  unfold DpNodeSpec at ih
  intro s₀ f h
  simp only [invoke_eq _ hgo, callFn, depthGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p hv n, memoFindG_spec dpSch p _ hf n, memoPutG_spec dpSch p _ hput n, ih] <;>
    finish (gen := 20)

include hnode in
theorem dpNode_step (n : Nat) (ih : DpGoSpec p n) : DpNodeSpec p (n + 1) := by
  unfold DpGoSpec at ih
  intro s₀ f1 g x y z
  simp only [invoke_eq _ hnode, callFn, depthNode]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
    finish (gen := 20) [maxW]

include hv hf hput hgo hnode in
theorem dpGo_spec (n : Nat) : DpGoSpec p n ∧ DpNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ f h; rw [invoke_eq _ hgo]; simp only [callFn, depthGo]; vcgen [exec] <;> grind
    · intro s₀ f1 g x y z; rw [invoke_eq _ hnode]; simp only [callFn, depthNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨dpGo_step p hv hf hput hgo n ih.2, dpNode_step p hnode n ih.1⟩

end spec

/-! ### The relational side -/

def dpArm (memo : Std.HashMap EIdx Nat) (fuel : Nat) : ENodeView → AM (Nat × Std.HashMap EIdx Nat)
  | .app f a => do
    let (d1, m) ← ConRon.Arena.depthGo memo fuel f
    let (d2, m2) ← ConRon.Arena.depthGo m fuel a
    pure (max d1 d2 + 1, m2)
  | .lam ty body => do
    let (d1, m) ← ConRon.Arena.depthGo memo fuel ty
    let (d2, m2) ← ConRon.Arena.depthGo m fuel body
    pure (max d1 d2 + 1, m2)
  | .forallE ty body => do
    let (d1, m) ← ConRon.Arena.depthGo memo fuel ty
    let (d2, m2) ← ConRon.Arena.depthGo m fuel body
    pure (max d1 d2 + 1, m2)
  | .letE ty val body => do
    let (d1, m) ← ConRon.Arena.depthGo memo fuel ty
    let (d2, m2) ← ConRon.Arena.depthGo m fuel val
    let (d3, m3) ← ConRon.Arena.depthGo m2 fuel body
    pure (max (max d1 d2) d3 + 1, m3)
  | .proj _ _ x => do
    let (d, m) ← ConRon.Arena.depthGo memo fuel x
    pure (d + 1, m)
  | _ => pure (1, memo)

def NodeVd : ENodeView → Prop
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => True
  | _ => False

theorem depthGo_succ' (memo : Std.HashMap EIdx Nat) (fuel : Nat) (h : EIdx) :
    ConRon.Arena.depthGo memo (fuel + 1) h = (do
      let v ← view h
      match v with
      | .bvar _ => pure (1, memo)
      | .fvar _ _ => pure (1, memo)
      | .sort _ => pure (1, memo)
      | .const _ _ => pure (1, memo)
      | .lit _ => pure (1, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← dpArm memo fuel v
          pure (r, m.insert h r)) := by
  rw [ConRon.Arena.depthGo.eq_2]
  congr 1
  funext v
  cases v <;> first | rfl | (simp only [dpArm, bind_assoc, pure_bind]; rfl)

theorem dpTwin_node (memo : Std.HashMap EIdx Nat) (fuel : Nat) (h : EIdx) (a : AState) (v : ENodeView)
    (hv : a.store.view h = some v) (hnv : NodeVd v) :
    (ConRon.Arena.depthGo memo (fuel + 1) h).run a =
      ((match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← dpArm memo fuel v
          pure (r, m.insert h r) : AM (Nat × Std.HashMap EIdx Nat)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | (rw [depthGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind])

theorem dpFrame_arena {m m' : Mem} {a : AState} (hf : MemFrame [DPM] [207] m m') (hR : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame (fun b hb => by simp at hb; subst hb; simp [arenaArrs, storeArrs, memoArrs, DPM])
    (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf hR

def DpGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (f h r : Word) (mp : Std.HashMap EIdx Nat),
    dpGoW n m f h = some (r, m') → ArenaR m a → H h → dpMR m mp →
    ∃ d mp', (ConRon.Arena.depthGo mp f.toNat (decE h)).run a = .ok ((d, mp'), a) ∧ r.toNat = d ∧
      dpMR m' mp' ∧ MemFrame [DPM] [207] m m'

theorem fin_toNat {d : Word} (hb : ¬ 4294967295 ≤ d) : (d + 1).toNat = d.toNat + 1 := by
  have : d.toNat < 4294967295 := by
    have e : (4294967295 : Word).toNat = 4294967295 := by decide
    have : ¬ (4294967295 : Word).toNat ≤ d.toNat := fun hh => hb (UInt64.le_iff_toNat_le.mpr hh)
    omega
  rw [UInt64.toNat_add]; simp; omega

theorem dpNodeBin_ok (n : Nat) (ih : DpGoOK n) (m m' : Mem) (a : AState) (f1 g x y z r : Word)
    (mp : Std.HashMap EIdx Nat) (hg : g = 4 ∨ g = 5 ∨ g = 6) (hx : H x) (hy : H y)
    (hn : dpNodeW (n + 1) m f1 g x y z = some (r, m')) (hA : ArenaR m a) (hM : dpMR m mp) :
    ∃ d mp', (do
        let (d1, mm) ← ConRon.Arena.depthGo mp f1.toNat (decE x)
        let (d2, m2) ← ConRon.Arena.depthGo mm f1.toNat (decE y)
        pure (max d1 d2 + 1, m2) : AM (Nat × Std.HashMap EIdx Nat)).run a = .ok ((d, mp'), a) ∧
      r.toNat = d ∧ dpMR m' mp' ∧ MemFrame [DPM] [207] m m' := by
  rw [dpNodeW_bin n m f1 g x y z hg] at hn
  rcases h1 : dpGoW n m f1 x with _ | ⟨d1w, m1⟩ <;> rw [h1] at hn; · simp [dpB1] at hn
  rw [dpB1_some] at hn
  rcases h2 : dpGoW n m1 f1 y with _ | ⟨d2w, m2⟩ <;> rw [h2] at hn; · simp [dpB2] at hn
  rw [dpB2_some] at hn
  by_cases hb : 4294967295 ≤ maxW d1w d2w
  · rw [dpFin_big _ _ hb] at hn; simp at hn
  rw [dpFin_ok _ _ hb] at hn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
  obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a f1 x d1w mp h1 hA hx hM
  obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m2 a f1 y d2w mp1 h2 (dpFrame_arena hf1 hA) hy hM1
  refine ⟨max c1 c2 + 1, mp2, ?_, ?_, hM2, hf1.trans hf2⟩
  · simp only [StateT.run_bind]
    simp only [hr1, except_ok_bind, hr2]
    rfl
  · rw [fin_toNat hb, maxW_toNat, hb1, hb2]

theorem dpNodeLet_ok (n : Nat) (ih : DpGoOK n) (m m' : Mem) (a : AState) (f1 x y z r : Word)
    (mp : Std.HashMap EIdx Nat) (hx : H x) (hy : H y) (hz : H z)
    (hn : dpNodeW (n + 1) m f1 7 x y z = some (r, m')) (hA : ArenaR m a) (hM : dpMR m mp) :
    ∃ d mp', (do
        let (d1, mm) ← ConRon.Arena.depthGo mp f1.toNat (decE x)
        let (d2, m2) ← ConRon.Arena.depthGo mm f1.toNat (decE y)
        let (d3, m3) ← ConRon.Arena.depthGo m2 f1.toNat (decE z)
        pure (max (max d1 d2) d3 + 1, m3) : AM (Nat × Std.HashMap EIdx Nat)).run a = .ok ((d, mp'), a) ∧
      r.toNat = d ∧ dpMR m' mp' ∧ MemFrame [DPM] [207] m m' := by
  rw [dpNodeW_let n m f1 7 x y z rfl] at hn
  rcases h1 : dpGoW n m f1 x with _ | ⟨d1w, m1⟩ <;> rw [h1] at hn; · simp [dpL1] at hn
  rw [dpL1_some] at hn
  rcases h2 : dpGoW n m1 f1 y with _ | ⟨d2w, m2⟩ <;> rw [h2] at hn; · simp [dpL2] at hn
  rw [dpL2_some] at hn
  rcases h3 : dpGoW n m2 f1 z with _ | ⟨d3w, m3⟩ <;> rw [h3] at hn; · simp [dpL3] at hn
  rw [dpL3_some] at hn
  by_cases hb : 4294967295 ≤ maxW (maxW d1w d2w) d3w
  · rw [dpFin_big _ _ hb] at hn; simp at hn
  rw [dpFin_ok _ _ hb] at hn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
  obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a f1 x d1w mp h1 hA hx hM
  obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m2 a f1 y d2w mp1 h2 (dpFrame_arena hf1 hA) hy hM1
  obtain ⟨c3, mp3, hr3, hb3, hM3, hf3⟩ := ih m2 m3 a f1 z d3w mp2 h3
    (dpFrame_arena (hf1.trans hf2) hA) hz hM2
  refine ⟨max (max c1 c2) c3 + 1, mp3, ?_, ?_, hM3, (hf1.trans hf2).trans hf3⟩
  · simp only [StateT.run_bind]
    simp only [hr1, except_ok_bind, hr2, hr3]
    rfl
  · rw [fin_toNat hb, maxW_toNat, maxW_toNat, hb1, hb2, hb3]

theorem dpNodeProj_ok (n : Nat) (ih : DpGoOK n) (m m' : Mem) (a : AState) (f1 g x y z r : Word)
    (mp : Std.HashMap EIdx Nat) (hg2 : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (hg3 : g ≠ 7) (hz : H z)
    (hn : dpNodeW (n + 1) m f1 g x y z = some (r, m')) (hA : ArenaR m a) (hM : dpMR m mp) :
    ∃ d mp', (do
        let (d, mm) ← ConRon.Arena.depthGo mp f1.toNat (decE z)
        pure (d + 1, mm) : AM (Nat × Std.HashMap EIdx Nat)).run a = .ok ((d, mp'), a) ∧
      r.toNat = d ∧ dpMR m' mp' ∧ MemFrame [DPM] [207] m m' := by
  rw [dpNodeW_proj n m f1 g x y z hg2 hg3] at hn
  rcases h1 : dpGoW n m f1 z with _ | ⟨d1w, m1⟩ <;> rw [h1] at hn; · simp [dpP1] at hn
  rw [dpP1_some] at hn
  by_cases hb : 4294967295 ≤ d1w
  · rw [dpFin_big _ _ hb] at hn; simp at hn
  rw [dpFin_ok _ _ hb] at hn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
  obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a f1 z d1w mp h1 hA hz hM
  refine ⟨c1 + 1, mp1, ?_, ?_, hM1, hf1⟩
  · simp only [StateT.run_bind]
    simp only [hr1, except_ok_bind]
    rfl
  · rw [fin_toNat hb, hb1]

theorem dpNode_arm (k : Nat) (ih : DpGoOK k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVd v) (m m' : Mem) (a : AState) (f1 r : Word) (mp : Std.HashMap EIdx Nat)
    (hn : dpNodeW (k + 1) m f1 (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0) = some (r, m'))
    (hA : ArenaR m a) (hM : dpMR m mp) :
    ∃ d mp', (dpArm mp f1.toNat v).run a = .ok ((d, mp'), a) ∧ r.toNat = d ∧ dpMR m' mp' ∧
      MemFrame [DPM] [207] m m' := by
  cases v with
  | app f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := dpNodeBin_ok k ih m m' a f1 _ _ _ _ r mp (Or.inl hg) hx hy hn hA hM
    rw [hdx, hdy] at this
    simp only [dpArm]; exact this
  | lam f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := dpNodeBin_ok k ih m m' a f1 _ _ _ _ r mp (Or.inr (Or.inl hg)) hx hy hn hA hM
    rw [hdx, hdy] at this
    simp only [dpArm]; exact this
  | forallE f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := dpNodeBin_ok k ih m m' a f1 _ _ _ _ r mp (Or.inr (Or.inr hg)) hx hy hn hA hM
    rw [hdx, hdy] at this
    simp only [dpArm]; exact this
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := dpNodeLet_ok k ih m m' a f1 _ _ _ r mp hx hy hz hn hA hM
    rw [hdx, hdy, hdz] at this
    simp only [dpArm]; exact this
  | proj s i e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, -, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := dpNodeProj_ok k ih m m' a f1 9 _ _ _ r mp (by decide) (by decide) hz hn hA hM
    rw [hdz] at this
    simp only [dpArm]; exact this
  | bvar _ => exact False.elim hnv
  | sort _ => exact False.elim hnv
  | const _ _ => exact False.elim hnv
  | lit _ => exact False.elim hnv
  | fvar _ _ => exact False.elim hnv

theorem dpGo_nodeCase (j : Nat) (ih : ∀ k, k + 1 < j + 1 → DpGoOK k) (m m' : Mem) (a : AState)
    (f h r : Word) (mp : Std.HashMap EIdx Nat) (F : Nat)
    (hF : f.toNat = F + 1) (hf0 : f ≠ 0) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVd v) (hv : a.store.view (decE h) = some v) (hvl : vl ≠ [])
    (hgs : vl.headD 0 = 4 ∨ vl.headD 0 = 5 ∨ vl.headD 0 = 6 ∨ vl.headD 0 = 7 ∨ vl.headD 0 = 9)
    (hb : dpG1 j m f h vl = some (r, m')) (hA : ArenaR m a) (hh : H h) (hM : dpMR m mp) :
    ∃ d mp', (ConRon.Arena.depthGo mp (F + 1) (decE h)).run a = .ok ((d, mp'), a) ∧ r.toNat = d ∧
      dpMR m' mp' ∧ MemFrame [DPM] [207] m m' := by
  have hnl : ¬ (vl.headD 0 = 0 ∨ vl.headD 0 = 1 ∨ vl.headD 0 = 2 ∨ vl.headD 0 = 3 ∨ vl.headD 0 = 8) := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  rw [dpG1_node j m f h vl hvl hnl] at hb
  rw [dpTwin_node _ _ _ a v hv hnv]
  by_cases hfr : mfindG dpSch m h 0 = []
  · rw [dpG3_abort j m f h vl _ hfr] at hb; simp at hb
  by_cases hhit : (mfindG dpSch m h 0).headD 0 ≠ 0
  · rw [dpG3_hit j m f h vl _ hfr hhit] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    have hmem := memoRG_hit dpSch bmKey (fun w : Word => w.toNat) m mp hM h 0 hfr hhit ⟨hh, rfl⟩
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmem
    refine ⟨_, mp, ?_, rfl, hM, MemFrame.refl _ _ _⟩
    simp only [hmem]; rfl
  · rw [dpG3_miss j m f h vl _ hfr hhit] at hb
    have hmiss := memoRG_miss dpSch bmKey (fun w : Word => w.toNat) m mp hM h 0 ⟨hh, rfl⟩ hfr (by simpa using hhit)
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmiss
    cases j with
    | zero => simp [dpNodeW, dpG4] at hb
    | succ k =>
      rcases hnode : dpNodeW (k + 1) m (f - 1) (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
          (vl.tail.tail.tail.headD 0) with _ | ⟨rn, m1⟩; · rw [hnode] at hb; simp [dpG4] at hb
      rw [hnode, dpG4_some] at hb
      rcases hset : msetG dpSch m1 h 0 rn with _ | m2 <;> rw [hset] at hb; · simp [dpG5] at hb
      rw [dpG5_some] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have hF1 : (f - 1).toNat = F := by rw [toNat_sub_one' hf0, hF]; rfl
      obtain ⟨d, mp1, hr1, hbb, hM1, hfr1⟩ := dpNode_arm k (ih k (by omega)) vl v hvr hnv m m1 a (f - 1) rn mp
        hnode hA hM
      rw [hF1] at hr1
      have hset' := memoRG_set dpSch dpSch_wf bmKey (fun w : Word => w.toNat) m1 mp1 hM1 h 0 rn ⟨hh, rfl⟩ m2 hset
      have hfs : MemFrame [DPM] [dpSch.cs + 1] m1 m2 := msetG_frame dpSch dpSch_wf m1 m2 h 0 rn hset
      refine ⟨d, mp1.insert (decE h) d, ?_, hbb, ?_, hfr1.trans hfs⟩
      · rw [hmiss]
        simp only [StateT.run_bind, hr1, except_ok_bind]
        rfl
      · rw [← hbb]; exact hset'

theorem dpGo_step_ok (j : Nat) (ih : ∀ k, k + 1 < j + 1 → DpGoOK k) : DpGoOK (j + 1) := by
  intro m m' a f h r mp hb hA hh hM
  by_cases hf0 : f = 0
  · rw [dpGoW_abort j m f h hf0] at hb; simp at hb
  rw [dpGoW_view j m f h hf0] at hb
  obtain ⟨F, hF⟩ : ∃ F, f.toNat = F + 1 := ⟨f.toNat - 1, by have := toNat_ne_zero' hf0; omega⟩
  cases hvl : eViewW m h with
  | nil => rw [hvl] at hb; simp [dpG1] at hb
  | cons g vt =>
    have hne : eViewW m h ≠ [] := by rw [hvl]; simp
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m (a) hA h hne
    rw [hvl] at hvr hb
    have leaf : ∀ (hg : (g :: vt).headD 0 = 0 ∨ (g :: vt).headD 0 = 1 ∨ (g :: vt).headD 0 = 2 ∨
        (g :: vt).headD 0 = 3 ∨ (g :: vt).headD 0 = 8),
        (match v with | .bvar _ | .sort _ | .lit _ | .fvar _ _ | .const _ _ => True | _ => False) →
        ∃ d mp', (ConRon.Arena.depthGo mp f.toNat (decE h)).run a = .ok ((d, mp'), a) ∧ r.toNat = d ∧
          dpMR m' mp' ∧ MemFrame [DPM] [207] m m' := by
      intro hg hv'
      rw [dpG1_leaf j m f h _ (by simp) hg] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      refine ⟨1, mp, ?_, rfl, hM, MemFrame.refl _ _ _⟩
      rw [hF, depthGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      cases v <;> first | rfl | exact False.elim hv'
    cases v with
    | bvar i =>
      have hg0 : (g :: vt).headD 0 = 0 := by simpa [ViewR] using hvr.1
      exact leaf (Or.inl hg0) trivial
    | fvar i ty =>
      have hg0 : (g :: vt).headD 0 = 1 := hvr.1
      exact leaf (Or.inr (Or.inl hg0)) trivial
    | sort u =>
      have hg0 : (g :: vt).headD 0 = 2 := by simpa [ViewR] using hvr.1
      exact leaf (Or.inr (Or.inr (Or.inl hg0))) trivial
    | const nn us =>
      have hg0 : (g :: vt).headD 0 = 3 := hvr.1
      exact leaf (Or.inr (Or.inr (Or.inr (Or.inl hg0)))) trivial
    | lit l =>
      have hg0 : (g :: vt).headD 0 = 8 := by simpa [ViewR] using hvr
      exact leaf (Or.inr (Or.inr (Or.inr (Or.inr hg0)))) trivial
    | app f' x' =>
      rw [hF]
      exact dpGo_nodeCase j ih m m' a f h r mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inl hvr.1) hb hA hh hM
    | lam f' x' =>
      rw [hF]
      exact dpGo_nodeCase j ih m m' a f h r mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inl hvr.1)) hb hA hh hM
    | forallE f' x' =>
      rw [hF]
      exact dpGo_nodeCase j ih m m' a f h r mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inr (Or.inl hvr.1))) hb hA hh hM
    | letE t v' b' =>
      rw [hF]
      exact dpGo_nodeCase j ih m m' a f h r mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inr (Or.inr (Or.inl hvr.1)))) hb hA hh hM
    | proj s i e =>
      rw [hF]
      exact dpGo_nodeCase j ih m m' a f h r mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inr (Or.inr (Or.inr hvr.1)))) hb hA hh hM

theorem dpGoOK (n : Nat) : DpGoOK n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro m m' a f h r mp hb; simp [dpGoW] at hb
    | succ j => exact dpGo_step_ok j (fun k hk => ih k (by omega))

def dpConstW (n : Nat) (m : Mem) (e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) dpSch.cs + 2 = 0 then none else dpClrK (dpGoW n (mclearG dpSch m) CWF e)

theorem dpConstW_eq (n : Nat) (m : Mem) (e : Word) (h0 : rdW (m.arr64 CTL) dpSch.cs + 2 ≠ 0) :
    dpConstW n m e = dpClrK (dpGoW n (mclearG dpSch m) CWF e) := by simp [dpConstW, h0]
theorem dpClrK_some (r : Word) (m1 : Mem) (h0 : rdW (m1.arr64 CTL) dpSch.cs + 2 ≠ 0) :
    dpClrK (some (r, m1)) = some (r, mclearG dpSch m1) := by simp [dpClrK, h0]
attribute [ind_grind] dpConstW_eq dpClrK_some

def wfW (n : Nat) (m : Mem) (e : Word) : Option (Word × Mem) :=
  match dpConstW n m e with
  | none => none
  | some (d, m1) => if 4294967296 ≤ d then none else some (d + 1024, m1)

section spec2
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "dp_find" = some (memoFindG dpSch)) (hput : p.lookup "dp_put" = some (memoPutG dpSch))
  (hgo : p.lookup "depth_go" = some depthGo) (hnode : p.lookup "depth_node" = some depthNode)
  (hcl : p.lookup "dp_clear" = some (memoClearG dpSch))
  (hd : p.lookup "depth" = some depth)

include hv hf hput hgo hnode hcl hd in
theorem depth_spec (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "depth" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ dpConstW n s₀.mem e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (dpGo_spec p hv hf hput hgo hnode n).1
  unfold DpGoSpec at ih
  simp only [invoke_eq _ hd, callFn, depth]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec dpSch p _ hcl n, ih] <;>
    finish

include hv hf hput hgo hnode hcl hd in
theorem whnfWalkFuel_spec (hw : p.lookup "whnf_walk_fuel" = some whnfWalkFuel) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "whnf_walk_fuel" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ wfW n s₀.mem e = some (r.headD 0, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hw, callFn, whnfWalkFuel]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, depth_spec p hv hf hput hgo hnode hcl hd n] <;>
    finish (gen := 20) [wfW]

end spec2

theorem dpConstW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (e r : Word) (mp0 : Std.HashMap EIdx Nat)
    (hb : dpConstW n m e = some (r, m')) (hS : StageR dn vis fe m a) (he : H e) (hM : dpMR m mp0) :
    ∃ d, (ConRon.Arena.depth (decE e)).run a = .ok (d, a) ∧ r.toNat = d ∧ dpMR m' ∅ ∧
      StageR dn vis fe m' a ∧ IWGrow m m' ∧ MFr [DPM] [206, 207] m m' := by
  by_cases h0 : rdW (m.arr64 CTL) dpSch.cs + 2 = 0
  · simp [dpConstW, h0] at hb
  rw [dpConstW_eq n m e h0] at hb
  have hf0 := mclearG_frame dpSch m
  have hM0 := memoRG_clear dpSch dpSch_wf bmKey (fun w : Word => w.toNat) m mp0 hM h0
  have hA0 : ArenaR (mclearG dpSch m) a :=
    ArenaR.frame (A := []) (C := [dpSch.cs, dpSch.cs + 1]) (fun b hb => by simp at hb)
      (fun x hx => by simp [dpSch] at hx; rcases hx with rfl | rfl <;> exact not_mem_arenaCtl _ (by decide)) hf0
      hS.1.arena.1
  rcases hg : dpGoW n (mclearG dpSch m) CWF e with _ | ⟨r1, m1⟩ <;> rw [hg] at hb; · simp [dpClrK] at hb
  by_cases h1 : rdW (m1.arr64 CTL) dpSch.cs + 2 = 0
  · simp [dpClrK, h1] at hb
  rw [dpClrK_some r1 m1 h1] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  obtain ⟨d, mp1, hrun, hbb, hM1, hfr1⟩ := dpGoOK n _ _ a CWF e r1 ∅ hg hA0 he hM0
  rw [CWF_eq] at hrun
  have hM2 := memoRG_clear dpSch dpSch_wf bmKey (fun w : Word => w.toNat) m1 mp1 hM1 h1
  have hf2 := mclearG_frame dpSch m1
  have hfall : MemFrame [DPM] [dpSch.cs, dpSch.cs + 1] m (mclearG dpSch m1) :=
    ((hf0.mono (by simp) (by simp)).trans (hfr1.mono (by simp) (by simp [dpSch]))).trans
      (hf2.mono (by simp) (by simp))
  obtain ⟨hS', hg'⟩ := StageR.frame_hi hS hfall (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp [dpSch] at hx; rcases hx with rfl | rfl <;> decide) (by decide)
    (by simp [dpSch])
  refine ⟨d, ?_, hbb, hM2, hS', hg', ⟨_, _, hfall, by simp, fun x hx => .inr (.inr (by simpa [dpSch] using hx))⟩⟩
  simp only [ConRon.Arena.depth, StateT.run_bind, hrun]
  rfl

theorem wfW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (e r : Word) (mp0 : Std.HashMap EIdx Nat)
    (hb : wfW n m e = some (r, m')) (hS : StageR dn vis fe m a) (he : H e) (hM : dpMR m mp0) :
    ∃ d, (ConRon.Arena.whnfWalkFuel (decE e)).run a = .ok (d, a) ∧ r.toNat = d ∧ dpMR m' ∅ ∧
      StageR dn vis fe m' a ∧ IWGrow m m' ∧ MFr [DPM] [206, 207] m m' := by
  unfold wfW at hb
  rcases hc : dpConstW n m e with _ | ⟨d, m1⟩ <;> rw [hc] at hb; · simp at hb
  by_cases hbig : 4294967296 ≤ d
  · simp [hbig] at hb
  simp only [hbig, ite_false, Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨dd, hrun, hdd, hM', hS', hg, hf⟩ := dpConstW_ok n dn fe vis m m1 a e d mp0 hc hS he hM
  have hlt : d.toNat < 2 ^ 32 := by
    have e1 : (4294967296 : Word).toNat = 4294967296 := by decide
    have : ¬ (4294967296 : Word).toNat ≤ d.toNat := fun hh => hbig (UInt64.le_iff_toNat_le.mpr hh)
    omega
  refine ⟨dd + 1024, ?_, ?_, hM', hS', hg, hf⟩
  · simp only [ConRon.Arena.whnfWalkFuel, StateT.run_bind]
    simp only [hrun, except_ok_bind]
    show (pure (dd + fuelSlack) : AM Nat).run a = _
    rfl
  · rw [UInt64.toNat_add, hdd]
    have e2 : (1024 : Word).toNat = 1024 := by decide
    rw [e2]
    have h64 : dd < 2 ^ 32 := by rw [← hdd]; exact hlt
    exact Nat.mod_eq_of_lt (by simp; omega)

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "dp_find" = some (memoFindG dpSch)) (hput : p.lookup "dp_put" = some (memoPutG dpSch))
  (hgo : p.lookup "depth_go" = some depthGo) (hnode : p.lookup "depth_node" = some depthNode)
  (hcl : p.lookup "dp_clear" = some (memoClearG dpSch))
  (hd : p.lookup "depth" = some depth) (hw : p.lookup "whnf_walk_fuel" = some whnfWalkFuel)

include hv hf hput hgo hnode in
/-- **`depth_go` (with `depth_node`) refines `depthGo`**, from a memo related to the twin's. -/
@[refines ConRon.Arena.depthGo]
theorem depthGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis f h : Word) (mp : Std.HashMap EIdx Nat) (hh : H h)
    (hS : StageR dn vis fe s₀.mem a₀) (hM : dpMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "depth_go" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.depthGo mp f.toNat (decE h)) a₀ ∧
      AM.st (ConRon.Arena.depthGo mp f.toNat (decE h)) a₀ = a₀ ∧
      (r.headD 0).toNat = (AM.res (ConRon.Arena.depthGo mp f.toNat (decE h)) a₀).1 ∧
      dpMR s'.mem (AM.res (ConRon.Arena.depthGo mp f.toNat (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post ((dpGo_spec p hv hf hput hgo hnode n).1 s₀ f h) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨d, mp', hrun, hb, hM', hfr⟩ := dpGoOK n _ _ a₀ f h _ mp hm hS.1.arena.1 hh hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  obtain ⟨hS', hg⟩ := StageR.frame_hi hS hfr (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp at hx; subst hx; decide) (by decide) (by decide)
  refine ⟨hl, hok, hst, by rw [hres]; exact hb, by rw [hres]; exact hM', hS', hg⟩

include hv hf hput hgo hnode hcl hd in
/-- **`depth` refines `depth`**: one memoised DAG walk between two clears. -/
@[refines ConRon.Arena.depth]
theorem depth_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis e : Word) (mp0 : Std.HashMap EIdx Nat) (he : H e)
    (hS : StageR dn vis fe s₀.mem a₀) (hM : dpMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "depth" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.depth (decE e)) a₀ ∧
      AM.st (ConRon.Arena.depth (decE e)) a₀ = a₀ ∧
      (r.headD 0).toNat = AM.res (ConRon.Arena.depth (decE e)) a₀ ∧
      dpMR s'.mem ∅ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (depth_spec p hv hf hput hgo hnode hcl hd n s₀ e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨d, hrun, hb, hM', hS', hg, -⟩ := dpConstW_ok n dn fe vis _ _ a₀ e _ mp0 hm hS he hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hst, by rw [hres]; exact hb, hM', hS', hg⟩

include hv hf hput hgo hnode hcl hd hw in
/-- **`whnf_walk_fuel` refines `whnfWalkFuel`**: the depth plus the slack. -/
@[refines ConRon.Arena.whnfWalkFuel]
theorem whnfWalkFuel_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis e : Word) (mp0 : Std.HashMap EIdx Nat) (he : H e)
    (hS : StageR dn vis fe s₀.mem a₀) (hM : dpMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "whnf_walk_fuel" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.whnfWalkFuel (decE e)) a₀ ∧
      AM.st (ConRon.Arena.whnfWalkFuel (decE e)) a₀ = a₀ ∧
      (r.headD 0).toNat = AM.res (ConRon.Arena.whnfWalkFuel (decE e)) a₀ ∧
      dpMR s'.mem ∅ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (whnfWalkFuel_spec p hv hf hput hgo hnode hcl hd hw n s₀ e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨d, hrun, hb, hM', hS', hg, -⟩ := wfW_ok n dn fe vis _ _ a₀ e _ mp0 hm hS he hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hst, by rw [hres]; exact hb, hM', hS', hg⟩

end census

section arms
variable (k : Nat) (m m1 m2 : Mem) (q n i z s v : Word)
theorem phsGoW_done (h : n ≤ i) : phsGoW (k + 1) m q n i = some m := by simp [phsGoW, h]
theorem phsGoW_step (h : ¬ n ≤ i) : phsGoW (k + 1) m q n i = phsK1 k m q n i (pinWordV m 53) := by
  simp [phsGoW, h]
theorem phsK1_big (h : 4294967296 ≤ z) : phsK1 k m q n i (some z) = none := by simp [phsK1, h]
theorem phsK1_ok (h : ¬ 4294967296 ≤ z) : phsK1 k m q n i (some z) = phsK2 k q n i (sointernW m z) := by
  simp only [phsK1]; rw [ite_eq_right h]
theorem phsK2_big (h : 4294967296 ≤ s) : phsK2 k q n i (some (s, m1)) = none := by simp [phsK2, h]
theorem phsK2_ok (h : ¬ 4294967296 ≤ s) : phsK2 k q n i (some (s, m1)) = phsK3 k q n i (fvinternW m1 i s) := by
  simp only [phsK2]; rw [ite_eq_right h]
theorem phsK3_big (h : 4294967296 ≤ v) : phsK3 k q n i (some (v, m2)) = none := by simp [phsK3, h]
theorem phsK3_ok (h : ¬ 4294967296 ≤ v) :
    phsK3 k q n i (some (v, m2)) = phsGoW k (m2.set64 IW (q + i) v) q n (i + 1) := by
  simp only [phsK3]; rw [ite_eq_right h]
end arms
attribute [ind_grind] phsGoW_done phsGoW_step phsK1_big phsK1_ok phsK2_big phsK2_ok phsK3_big phsK3_ok

section spec
variable (p : Prog) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hp : p.lookup "nest_phs_go" = some nestPhsGo)
include hpw hsf hsp his hff hfp hif hp

theorem nestPhsGo_spec (k : Nat) : ∀ (s₀ : St) (q n i : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_phs_go" [q, n, i]
    ⦃fun _ s' => LocEq s' s₀ ∧ phsGoW k s₀.mem q n i = some s'.mem; ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ q n i
    rw [invoke_eq _ hp]; simp only [callFn, nestPhsGo]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ q n i
    simp only [invoke_eq _ hp, callFn, nestPhsGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        pinWord_specV p hpw k, internSort_spec p hsf hsp his k, internFVar_spec p hff hfp hif k, ih] <;>
      finish (gen := 20)

end spec

theorem phsB_some (q nn : Word) (m2 : Mem) : phsB q nn (some m2) = some ([q, nn], m2) := rfl
theorem phsA_some (k : Nat) (nn q : Word) (m1 : Mem) : phsA k nn (some (q, m1)) = phsB q nn (phsGoW k m1 q nn 0) := rfl
attribute [ind_grind] phsB_some phsA_some

section spec2
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hg : p.lookup "nest_phs_go" = some nestPhsGo) (hp : p.lookup "nest_phs" = some nestPhs)
include ha hpw hsf hsp his hff hfp hif hg hp

theorem nestPhs_spec (k : Nat) (s₀ : St) (nn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_phs" [nn]
    ⦃fun r s' => LocEq s' s₀ ∧ phsW k s₀.mem nn = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestPhs]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      iwAlloc_specW p ha k, nestPhsGo_spec p hpw hsf hsp his hff hfp hif hg k] <;>
    finish (gen := 20) [phsW]

end spec2

/-- The pool outside `[q, q + n)`, its top and size, the constant records: unchanged. -/
def KeepIW (q n : Word) (m m' : Mem) : Prop :=
  (∀ idx, (idx < q.toNat ∨ q.toNat + n.toNat ≤ idx) → (m'.arr64 IW)[idx]? = (m.arr64 IW)[idx]?) ∧
  iwTop m' = iwTop m ∧ erTop m' = erTop m ∧ (m'.arr64 IW).size = (m.arr64 IW).size ∧
  m'.arr64 EREC = m.arr64 EREC

theorem KeepIW.refl (q n : Word) (m : Mem) : KeepIW q n m m := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem KeepIW.trans {q n : Word} {m₁ m₂ m₃ : Mem} (h₁ : KeepIW q n m₁ m₂) (h₂ : KeepIW q n m₂ m₃) :
    KeepIW q n m₁ m₃ :=
  ⟨fun idx hi => (h₂.1 idx hi).trans (h₁.1 idx hi), h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.trans h₁.2.2.2.2⟩

theorem KeepIW.of_low {q n : Word} {m m' : Mem} (h : LowFr m m') : KeepIW q n m m' := by
  obtain ⟨A, C, hf, hA, hC⟩ := h
  have hI : m'.arr64 IW = m.arr64 IW := hf.1 IW (fun hh => by have := hA _ hh; simp [IW] at this) (by decide)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (fun hh => by have := hA _ hh; simp [EREC] at this) (by decide)
  have h200 : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hf.2.1 200 (fun hh => by have := hC _ hh; simp at this)
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 129 (fun hh => by have := hC _ hh; simp at this)
  exact ⟨fun _ _ => by rw [hI], by simp only [iwTop, h200], by simp only [erTop, h129], by rw [hI], hE⟩

theorem KeepIW.set {q n i v : Word} (m : Mem) (hi : i.toNat < n.toNat) (hqi : (q + i).toNat = q.toNat + i.toNat) :
    KeepIW q n m (m.set64 IW (q + i) v) := by
  have hC : (m.set64 IW (q + i) v).arr64 CTL = m.arr64 CTL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hE : (m.set64 IW (q + i) v).arr64 EREC = m.arr64 EREC := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨fun idx hidx => ?_, by simp only [iwTop, hC], by simp only [erTop, hC], (set64IW_frame m _ _).2.2.1 IW, hE⟩
  rw [set64IW_get, ite_eq_right (by omega)]

theorem lowFr_iw {m m' : Mem} (h : LowFr m m') : m'.arr64 IW = m.arr64 IW := by
  obtain ⟨A, C, hf, hA, hC⟩ := h
  exact hf.1 IW (fun hh => by have := hA _ hh; simp [IW] at this) (by decide)

def phF (i : Nat) : AM EIdx := do
  let z ← zeroLevel
  let s ← internSortE z
  internFVarE i s

theorem nestPhs_eq (n : Nat) : ConRon.Arena.nestPhs n = (List.range' 0 n).mapM phF := by
  simp only [ConRon.Arena.nestPhs, List.range_eq_range']
  rfl

theorem range'_mapM_succ (i k : Nat) :
    (List.range' i (k + 1)).mapM phF = (do
      let x ← phF i
      let xs ← (List.range' (i + 1) k).mapM phF
      pure (x :: xs)) := by
  rw [List.range'_succ, List.mapM_cons]

theorem phsGoW_ok (k : Nat) : ∀ (m m' : Mem) (a : AState) (q n i : Word) (ws : List EIdx)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word),
    phsGoW k m q n i = some m' → StageR dn vis fe m a → i.toNat ≤ n.toNat →
    q.toNat + n.toNat ≤ (m.arr64 IW).size → (m.arr64 IW).size < 2 ^ 64 →
    decHL m q.toNat i.toNat = some ws →
    ∃ phs a', ((List.range' i.toNat (n.toNat - i.toNat)).mapM phF).run a = .ok (phs, a') ∧
      StageR dn vis fe m' a' ∧ KeepIW q n m m' ∧ decHL m' q.toNat n.toNat = some (ws ++ phs) := by
  induction k with
  | zero => intro m m' a q n i ws dn fe vis h; simp [phsGoW] at h
  | succ k ih =>
    intro m m' a q n i ws dn fe vis h hS hi hq hsz hdec
    by_cases hd : n ≤ i
    · rw [phsGoW_done k m q n i hd] at h
      simp only [Option.some.injEq] at h
      subst h
      have hin : n.toNat - i.toNat = 0 := by
        have := UInt64.le_iff_toNat_le.mp hd; omega
      have hien : i.toNat = n.toNat := by
        have := UInt64.le_iff_toNat_le.mp hd; omega
      refine ⟨[], a, ?_, hS, KeepIW.refl _ _ _, ?_⟩
      · rw [hin]; rfl
      · rw [← hien]; simpa using hdec
    · rw [phsGoW_step k m q n i hd] at h
      have hlt : i.toNat < n.toNat := by
        have : ¬ n.toNat ≤ i.toNat := fun hh => hd (UInt64.le_iff_toNat_le.mpr hh)
        omega
      rcases hpw : pinWordV m 53 with _ | z <;> rw [hpw] at h; · simp [phsK1] at h
      by_cases hzb : 4294967296 ≤ z
      · rw [phsK1_big _ _ _ _ _ _ hzb] at h; simp at h
      rw [phsK1_ok _ _ _ _ _ _ hzb] at h
      have hzlt := lt_of_notbig hzb
      have hpne : rdW (m.arr64 PINS) 0 ≠ 0 := by
        intro h0; simp [pinWordV, h0] at hpw
      have hz : z = pinW m 53 := by
        simp only [pinWordV, hpne, ite_false, Option.some.injEq] at hpw
        rw [← hpw]; simp [pinW, rdW]
      have hpin0 : pinW m 0 ≠ 0 := by simpa [pinW, rdW] using hpne
      have hfull := hS.1.pins.full hpin0
      rcases hso : sointernW m z with _ | ⟨s1, m1⟩ <;> rw [hso] at h; · simp [phsK2] at h
      by_cases hsb : 4294967296 ≤ s1
      · rw [phsK2_big _ _ _ _ _ _ hsb] at h; simp at h
      rw [phsK2_ok _ _ _ _ _ _ hsb] at h
      have hs1lt := lt_of_notbig hsb
      rcases hfv : fvinternW m1 i s1 with _ | ⟨v, m2⟩ <;> rw [hfv] at h; · simp [phsK3] at h
      by_cases hvb : 4294967296 ≤ v
      · rw [phsK3_big _ _ _ _ _ _ hvb] at h; simp at h
      rw [phsK3_ok _ _ _ _ _ _ hvb] at h
      have hvlt := lt_of_notbig hvb
      obtain ⟨a1, hr1, hS1, hg1⟩ := internSort_stage hS z hzlt hso
      obtain ⟨a2, hr2, hS2, hg2⟩ := internFVar_stage hS1 i s1 hs1lt hfv
      have hlow : LowFr m m2 := (sointernW_low hso).trans (fvinternW_low hfv)
      have hI2 := lowFr_iw hlow
      have hqi : (q + i).toNat = q.toNat + i.toNat := by
        rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hdec2 : decHL m2 q.toNat i.toNat = some ws := by
        rw [← hdec]; simp only [decHL, iwA, hI2]
      have hdec3 := decHL_write m2 q i v ws hvlt (by rw [hI2]; exact hsz) (by rw [hI2]; omega) hdec2
      have hS3 := hS2.set_iw (q + i) v
      have hi1 : (i + 1).toNat = i.toNat + 1 := toNat_add_one' (by omega)
      obtain ⟨phs, a3, hrun, hS4, hK, hdecF⟩ := ih (m2.set64 IW (q + i) v) m' a2 q n (i + 1) (ws ++ [decI v]) dn fe vis h
        hS3 (by rw [hi1]; omega) (by rw [(set64IW_frame m2 (q + i) v).2.2.1 IW, hI2]; exact hq)
        (by rw [(set64IW_frame m2 (q + i) v).2.2.1 IW, hI2]; exact hsz) (by rw [hi1]; exact hdec3)
      have hn1 : n.toNat - i.toNat = (n.toNat - (i.toNat + 1)) + 1 := by omega
      refine ⟨decE v :: phs, a3, ?_, hS4, ?_, ?_⟩
      · rw [hn1, range'_mapM_succ]
        simp only [StateT.run_bind]
        have hzl : zeroLevel.run a = .ok (decI z, a) := by
          rw [hz]; exact pinZeroLevel_run hfull
        have e1 : (phF i.toNat).run a = .ok (decE v, a2) := by
          simp only [phF, StateT.run_bind, hzl, except_ok_bind, ConRon.Arena.internSortE, ConRon.Arena.internFVarE, hr1]
          exact hr2
        simp only [e1, except_ok_bind]
        rw [hi1] at hrun
        rw [hrun]
        rfl
      · exact ((KeepIW.of_low hlow).trans (KeepIW.set m2 (by omega) hqi)).trans hK
      · simp only [List.append_assoc, List.singleton_append] at hdecF; exact hdecF

theorem phsW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (nn : Word) (r : List Word)
    (h : phsW k m nn = some (r, m')) (hS : StageR dn vis fe m a) :
    ∃ phs a', (ConRon.Arena.nestPhs nn.toNat).run a = .ok (phs, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some phs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  unfold phsW at h
  rcases hal : allocW m nn with _ | ⟨q, m1⟩ <;> rw [hal] at h; · simp [phsA] at h
  rw [phsA_some] at h
  obtain ⟨hS1, hg1, hqd, hroom, htop1⟩ := hS.alloc hal
  rcases hl : phsGoW k m1 q nn 0 with _ | m2 <;> rw [hl] at h; · simp [phsB] at h
  rw [phsB_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := hS1.2.2.2.1
  have hroom1 : q.toNat + nn.toNat ≤ (m1.arr64 IW).size := by
    have := hS1.2.1; simp only [iwTop] at htop1 this; omega
  obtain ⟨phs, a', hrun, hS2, hK, hdec⟩ := phsGoW_ok k m1 m2 a q nn 0 [] dn fe vis hl hS1
    (by simp) hroom1 hsz1 (by simp [decHL, hslice?])
  refine ⟨phs, a', ?_, hS2, ?_, by simpa using hdec, ?_⟩
  · rw [nestPhs_eq]
    simpa using hrun
  · obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hK
    refine ⟨?_, ?_, fun idx hidx => ?_, fun idx hidx => ?_⟩
    · rw [hK2]; exact hg1.1
    · rw [hK3]; exact hg1.2.1
    · have hq : idx < q.toNat := by
        have : q.toNat = iwTop m := by simp only [iwTop, hqd]
        omega
      rw [hK1 idx (Or.inl hq)]; exact hg1.2.2.1 idx hidx
    · rw [hK5]; exact hg1.2.2.2 idx hidx
  · show q.toNat + nn.toNat ≤ iwTop m2
    rw [hK.2.1, htop1]; exact Nat.le_refl _

section census
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hg : p.lookup "nest_phs_go" = some nestPhsGo) (hp : p.lookup "nest_phs" = some nestPhs)
include ha hpw hsf hsp his hff hfp hif hg hp

/-- **`nest_phs` refines `nestPhs`**: the canonical parameter variables as a new `IW` slice. -/
@[refines ConRon.Arena.nestPhs]
theorem nestPhs_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis nn : Word) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_phs" [nn]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestPhs nn.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestPhs nn.toNat) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat = some (AM.res (ConRon.Arena.nestPhs nn.toNat) a₀); ⊤⦄ := by
  refine triple_post (nestPhs_spec p ha hpw hsf hsp his hff hfp hif hg hp k s₀ nn) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨phs, a', hrun, hS', hgr, hdec, -⟩ := phsW_ok k dn fe vis _ _ a₀ nn r hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hgr, by rw [hres]; exact hdec⟩

end census

def pccB (k : Nat) (no nl us nn : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else pccC 0 (rpConstW k m2 no nl us 0 nn (r2.tail.headD 0))

def pccA (k : Nat) (no nl us nn cty : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => pccB k no nl us nn (instW (k + 1) m1 (r1.headD 0) (r1.tail.headD 0) cty)

def pccW (k : Nat) (m : Mem) (no nl us nn cty : Word) : Option (List Word × Mem) :=
  pccA k no nl us nn cty (phsW k m nn)

theorem pccC_big (r3 : Word) (r : Word) (m3 : Mem) (h : 4294967296 ≤ r) : pccC r3 (some (r, m3)) = none := by
  simp [pccC, h]
theorem pccC_some (r3 : Word) (r : Word) (m3 : Mem) (h : ¬ 4294967296 ≤ r) :
    pccC r3 (some (r, m3)) = some ([1, r], m3) := by simp only [pccC]; rw [ite_eq_right h]
theorem pccB_zero (k : Nat) (no nl us nn : Word) (r2 : List Word) (m2 : Mem) (h : r2.headD 0 = 0) :
    pccB k no nl us nn (some (r2, m2)) = some ([0, 0], m2) := by simp only [pccB]; rw [ite_eq_left h]
theorem pccB_ok (k : Nat) (no nl us nn : Word) (r2 : List Word) (m2 : Mem) (h : ¬ r2.headD 0 = 0) :
    pccB k no nl us nn (some (r2, m2)) = pccC 0 (rpConstW k m2 no nl us 0 nn (r2.tail.headD 0)) := by
  simp only [pccB]; rw [ite_eq_right h]
theorem pccA_some (k : Nat) (no nl us nn cty : Word) (r1 : List Word) (m1 : Mem) :
    pccA k no nl us nn cty (some (r1, m1)) = pccB k no nl us nn (instW (k + 1) m1 (r1.headD 0) (r1.tail.headD 0) cty) := rfl
attribute [ind_grind] pccC_big pccC_some pccB_zero pccB_ok pccA_some

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (hl : AhLook p) (hk : MkLook p)
  (hng : p.lookup "nest_phs_go" = some nestPhsGo) (hnp : p.lookup "nest_phs" = some nestPhs)
  (hip : p.lookup "inst_pis_with" = some instPisWith)
  (hf : p.lookup "ra_find" = some (memoFindG raSch)) (hput : p.lookup "ra_put" = some (memoPutG raSch))
  (hgo : p.lookup "replace_apps_go" = some replaceAppsGo)
  (hnode : p.lookup "replace_apps_node" = some replaceAppsNode)
  (hcl : p.lookup "ra_clear" = some (memoClearG raSch))
  (hra : p.lookup "replace_apps" = some replaceApps)
  (hp : p.lookup "nest_canon_crest" = some nestCanonCrest)
include ha hl hk hng hnp hip hf hput hgo hnode hcl hra hp

theorem nestCanonCrest_spec (n : Nat) (s₀ : St) (no nl us nn cty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "nest_canon_crest" [no, nl, us, nn, cty]
    ⦃fun r s' => LocEq s' s₀ ∧ pccW n s₀.mem no nl us nn cty = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCanonCrest]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      nestPhs_spec p ha hl.hpw hl.hsf hl.hsp hl.his hl.hff hl.hfp hl.hif hng hnp n,
      instPisWith_spec p hl.hv hip hl.hi1 (n + 1),
      replaceApps_spec p hl hk hf hput hgo hnode hcl hra n] <;>
    finish (gen := 20) [pccW, St.setLocs_mem']

end spec

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Memo frames of the pieces (lane `indproofs2`, helper `posmemo`)

`MFr S T` (`IndPosSpec/RpGoStep`): the writers below leave every per-call memo outside `S` alone; the
banked memo's `RfFr` is a corollary (`RfFr.of_mfr`). -/

theorem RfFr.of_mfr {S : List ArrId} {T : List Word} {m m' : Mem} (h : MFr S T m m') (hS : RFM ∉ S)
    (hT : (208 : Word) ∉ T ∧ (218 : Word) ∉ T ∧ (219 : Word) ∉ T) : RfFr m m' := by
  obtain ⟨A, C, f, a, c⟩ := h
  refine ⟨A, C, f, fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · rcases a _ hm with h | h | h
    · simp [RFM] at h
    · simp [RFM] at h
    · exact hS h
  all_goals rcases c _ hm with h | h | h
  all_goals first | (simp at h; done) | skip
  · exact hT.1 h
  · exact hT.2.1 h
  · exact hT.2.2 h

theorem posmemo_copyW_iw : ∀ (n : Nat) (m m' : Mem) (d s l : Word), copyW n m d s l = some m' →
    MemFrame [IW] [200] m m'
  | 0, _, _, _, _, _, h => by simp [copyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [copyW_nil n m d s l hl] at h; cases h; exact MemFrame.refl _ _ _
    · rw [copyW_step n m d s l hl] at h
      exact (set64IW_frame _ _ _).trans (posmemo_copyW_iw n _ _ _ _ _ h)

theorem phsGoW_mfr (k : Nat) : ∀ (m m' : Mem) (q n i : Word), phsGoW k m q n i = some m' → MFr [] [] m m' := by
  induction k with
  | zero => intro m m' q n i h; simp [phsGoW] at h
  | succ k ih =>
    intro m m' q n i h
    simp only [phsGoW, phsK1.eq_def, phsK2.eq_def, phsK3.eq_def] at h
    mfr_auto h [fun h => MFr.of_low (sointernW_low h), fun h => MFr.of_low (fvinternW_low h),
      fun h => (MFr.set_iw _ _ _).trans (ih _ _ _ _ _ h)]

theorem phsW_mfr {k : Nat} {m m' : Mem} {nn : Word} {r : List Word} (h : phsW k m nn = some (r, m')) : MFr [] [] m m' := by
  simp only [phsW, phsA.eq_def, phsB.eq_def] at h
  mfr_auto h [allocW_mfr, phsGoW_mfr k _ _ _ _ _]

theorem rpGoW_mfr (n : Nat) :
    (∀ (m m' : Mem) (no nl us b nn f h r : Word), rpGoW n m no nl us b nn f h = some (r, m') → MFr [RAM] [210, 211] m m') ∧
    (∀ (m m' : Mem) (no nl us b nn f1 h g x y z r : Word),
      rpNodeW n m no nl us b nn f1 h g x y z = some (r, m') → MFr [RAM] [210, 211] m m') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ _ h => by simp [rpGoW] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [rpNodeW] at h⟩
  | succ j =>
  have ahF : ∀ {m m' : Mem} {no nl us b nn e : Word} {rr : List Word},
      ahWf j m no nl us b nn e = some (rr, m') → MFr [] [] m m' := by
    intro m m' no nl us b nn e rr h
    cases j with
    | zero => simp [ahWf] at h
    | succ i => exact MFr.of_low (ahW_low h)
  have ndF : ∀ {m m' : Mem} {no nl us b nn f1 h g x y z r : Word},
      rpNodeW j m no nl us b nn f1 h g x y z = some (r, m') → MFr [RAM] [210, 211] m m' := by
    intro m m' no nl us b nn f1 h g x y z r hn
    cases j with
    | zero => simp [rpNodeW] at hn
    | succ i => exact (ih (i + 1) (by omega)).2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn
  refine ⟨fun m m' no nl us b nn f h r hg => ?_, fun m m' no nl us b nn f1 h g x y z r hn => ?_⟩
  · simp only [rpGoW] at hg
    split at hg; · cases hg
    simp only [rpG1] at hg
    split at hg; · cases hg
    split at hg; · rw [← (Prod.mk.inj (Option.some.inj hg)).2]; exact MFr.refl _ _ _
    split at hg
    · rcases ha : ahWf j m no nl us b nn h with _ | ⟨rr, m1⟩ <;> rw [ha] at hg; · cases hg
      rw [rpH_some] at hg; rw [← (Prod.mk.inj (Option.some.inj hg)).2]; exact (ahF ha).up
    simp only [rpG3] at hg
    split at hg; · cases hg
    split at hg; · rw [← (Prod.mk.inj (Option.some.inj hg)).2]; exact MFr.refl _ _ _
    simp only [rpG4.eq_def, rpG5.eq_def] at hg
    split at hg; · cases hg
    rename_i hn; split at hg; · cases hg
    rename_i hs; rw [← (Prod.mk.inj (Option.some.inj hg)).2]
    exact (ndF hn).trans ⟨_, _, msetG_frame raSch raSch_wf _ _ _ _ _ hs, by simp [raSch, RAM], by simp [raSch]⟩
  · simp only [rpNodeW, rpA1.eq_def, rpB1.eq_def, rpB2.eq_def, rpL1.eq_def, rpL2.eq_def, rpL3.eq_def,
      rpP1.eq_def] at hn
    have ihG := (ih j (by omega)).1
    mfr_auto hn [ahF, ihG _ _ _ _ _ _ _ _ _ _, rpMkW_mfr]

theorem rpConstW_mfr {n : Nat} {m m' : Mem} {no nl us b nn e r : Word}
    (h : rpConstW n m no nl us b nn e = some (r, m')) : MFr [RAM] [210, 211] m m' := by
  simp only [rpConstW, rpClrK.eq_def] at h
  split at h; · cases h
  split at h; · cases h
  rename_i hg; split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
  exact (MFr.trans ⟨_, _, mclearG_frame raSch m, by simp, by simp [raSch]⟩
    ((rpGoW_mfr n).1 _ _ _ _ _ _ _ _ _ _ hg)).trans ⟨_, _, mclearG_frame raSch _, by simp, by simp [raSch]⟩

theorem pccW_mfr {k : Nat} {m m' : Mem} {no nl us nn cty : Word} {r : List Word}
    (h : pccW k m no nl us nn cty = some (r, m')) : MFr [RAM] [210, 211] m m' := by
  simp only [pccW, pccA.eq_def, pccB.eq_def, pccC.eq_def] at h
  mfr_auto h [phsW_mfr, instW_mfr _ _ _ _ _ _ _, rpConstW_mfr]

theorem pccW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl us nn cty : Word) (names : List NIdx) (r : List Word)
    (h : pccW k m no nl us nn cty = some (r, m')) (hS : StageR dn vis fe m a) (hcty : H cty) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hnn : nn.toNat + names.length < 2 ^ 64)
    (mp0 : Std.HashMap EIdx EIdx) (hM : rpMR m mp0) :
    ∃ x a', (ConRon.Arena.nestCanonCrest names (decI us) nn.toNat (decI cty)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decOE m' r x ∧ ∃ mp, rpMR m' mp := by
  unfold pccW at h
  rcases hph : phsW k m nn with _ | ⟨r1, m1⟩ <;> rw [hph] at h; · simp [pccA] at h
  rw [pccA_some] at h
  obtain ⟨phs, a1, hrun1, hS1, hg1, hdec1, hbd1⟩ := phsW_ok k dn fe vis m m1 a nn r1 hph hS
  have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
    have : iwTop m1 < 2 ^ 64 := (rdW (m1.arr64 CTL) 200).toNat_lt
    omega
  rcases hin : instW (k + 1) m1 (r1.headD 0) (r1.tail.headD 0) cty with _ | ⟨r2, m2⟩ <;> rw [hin] at h; · simp [pccB] at h
  obtain ⟨x, a2, hrun2, hS2, hg2, hout2⟩ := instW_ok (k + 1) dn fe vis m1 m2 a1 (r1.headD 0) (r1.tail.headD 0)
    cty phs r2 hin hS1 hcty hdec1 hb1 hbd1
  have hM2 : rpMR m2 mp0 :=
    rpMR_mfr ((phsW_mfr hph).trans (instW_mfr _ _ _ _ _ _ _ hin)) (by decide) (by decide) hM
  by_cases hz : r2.headD 0 = 0
  · rw [pccB_zero k no nl us nn r2 m2 hz] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    cases x with
    | none =>
      refine ⟨none, a2, ?_, hS2, hg1.trans hg2, rfl, mp0, hM2⟩
      simp only [ConRon.Arena.nestCanonCrest, StateT.run_bind, hrun1, except_ok_bind, hrun2]
      rfl
    | some t => simp only [decOE] at hout2; rw [hz] at hout2; simp at hout2
  · rw [pccB_ok k no nl us nn r2 m2 hz] at h
    cases x with
    | none => exact absurd hout2 hz
    | some t =>
      simp only [decOE, decW0E] at hout2
      obtain ⟨-, htlt, htd⟩ := hout2
      rcases hrc : rpConstW k m2 no nl us 0 nn (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> rw [hrc] at h; · simp [pccC] at h
      by_cases hb3 : 4294967296 ≤ r3
      · rw [pccC_big _ _ _ hb3] at h; simp at h
      rw [pccC_some _ _ _ hb3] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hg12 := hg1.trans hg2
      have hdec2 : decHL m2 no.toNat nl.toNat = some names := by rw [decHL_grow hg12 hit]; exact hdec
      obtain ⟨a3, hrun3, hM3, hS3, hg3⟩ := rpConstW_ok k dn fe vis m2 m3 a2 no nl us 0 nn (r2.tail.headD 0) r3
        nn.toNat names mp0 hrc hS2 htlt hus hdec2 hno (by have := hg12.1; omega) rfl hnn
        (by simp; omega) hM2
      refine ⟨some (decE r3), a3, ?_, hS3, hg12.trans hg3, ?_, ∅, hM3⟩
      · simp only [ConRon.Arena.nestCanonCrest, StateT.run_bind]
        simp only [hrun1, except_ok_bind, StateT.run_bind, hrun2]
        have h3 : StateT.run (ConRon.Arena.replaceApps names (decI us) 0 nn.toNat (decI (r2.tail.headD 0))) a2 = .ok (decE r3, a3) := hrun3
        rw [← htd, h3]
        rfl
      · simp only [decOE, decW0E]
        exact ⟨rfl, lt_of_notbig hb3, rfl⟩

end L.Ind

namespace L.Ind

open L.Arena

def pcrK2 (k : Nat) (c : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (f, m2) => pcrK3 (rxW (k + 2) m2 f c)
section arms
variable (k : Nat) (m1 m2 m3 : Mem) (dO dL hO hL c f r : Word) (r1 : List Word)
theorem pcrK3_some : pcrK3 (some (r, m3)) = some ([1, r], m3) := rfl
theorem pcrK2_some : pcrK2 k c (some (f, m2)) = pcrK3 (rxW (k + 2) m2 f c) := rfl
end arms
attribute [ind_grind] pcrK3_some pcrK2_some

end L.Ind

end

end
