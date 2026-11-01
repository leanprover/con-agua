module

public import ConAgua.Arena.WalkLeaves
public import ConAgua.Arena.WalkScopeRefine
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.FVarRangeRefine
import ConAgua.Arena.LiftRefine
import ConAgua.Arena.View

@[expose] public section

/-!
# `leaf_guard` refines `leafGuard` (lane `whnf3`)

The three walks of `WalkLeaves.lean` against the twin's `fvarLeavesGo`, `leafMem`, `leavesSubGo`,
`leafGuard`, under `ArenaD` and the memo relations of their walk-local maps (`seen`: `MemoRG flSch
bmKey`, unit values; the subset memo: `MemoRG lsbSch bmKey decBW`). The accumulator is `LeafR m k acc`:
`acc` is the first `k` leaves of `LVS`, newest first, each annotation a handle word.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## The leaf list -/

/-- Leaf `j` of the word array. -/
def lvsAt (a : Array Word) (j : Nat) : Nat × EIdx :=
  ((rdW a (UInt64.ofNat j * 2)).toNat, decE (rdW a (UInt64.ofNat j * 2 + 1)))

/-- The first `k` leaves, newest (`k - 1`) first: the twin's consed accumulator. -/
def lvsList (a : Array Word) : Nat → List (Nat × EIdx)
  | 0 => []
  | j + 1 => lvsAt a j :: lvsList a j

/-- **The accumulator relation.** -/
structure LeafR (m : Mem) (k : Word) (acc : List (Nat × EIdx)) : Prop where
  eq : acc = lvsList (m.arr64 LVS) k.toNat
  hw : ∀ j, j < k.toNat → (rdW (m.arr64 LVS) (UInt64.ofNat j * 2 + 1)).toNat < 2 ^ 32
  cap : k.toNat * 2 ≤ (m.arr64 LVS).size
  small : k.toNat < 2 ^ 63

theorem lvsList_congr (a b : Array Word) (k : Nat)
    (h : ∀ j, j < k → rdW b (UInt64.ofNat j * 2) = rdW a (UInt64.ofNat j * 2) ∧
      rdW b (UInt64.ofNat j * 2 + 1) = rdW a (UInt64.ofNat j * 2 + 1)) :
    lvsList b k = lvsList a k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [lvsList, lvsAt, (h k (by omega)).1, (h k (by omega)).2]
    rw [ih (fun j hj => h j (by omega))]

theorem LeafR.frame {m m' : Mem} {k : Word} {acc : List (Nat × EIdx)} (h : LeafR m k acc)
    (he : m'.arr64 LVS = m.arr64 LVS) : LeafR m' k acc :=
  ⟨he ▸ h.eq, fun j hj => he ▸ h.hw j hj, he ▸ h.cap, h.small⟩

theorem LeafR.zero (m : Mem) : LeafR m 0 [] := ⟨rfl, fun j hj => by simp at hj, by simp, by decide⟩

/-- Small word arithmetic: indices below `2^63` do not wrap. -/
theorem ofNat_mul2_toNat (j : Nat) (hj : j < 2 ^ 63) : (UInt64.ofNat j * 2).toNat = j * 2 := by
  rw [UInt64.toNat_mul, UInt64.toNat_ofNat']; simp; omega

theorem ofNat_mul2_add1_toNat (j : Nat) (hj : j < 2 ^ 63) : (UInt64.ofNat j * 2 + 1).toNat = j * 2 + 1 := by
  rw [UInt64.toNat_add, ofNat_mul2_toNat j hj]; simp; omega

/-- **A push extends the accumulator.** -/
theorem LeafR.push {m : Mem} {k : Word} {acc : List (Nat × EIdx)} (h : LeafR m k acc) (x y : Word)
    (hl : ¬ m.len64 LVS >>> 1 ≤ k) (hy : y.toNat < 2 ^ 32) :
    LeafR (lvsPush m k x y) (k + 1) ((x.toNat, decE y) :: acc) := by
  have hl' : k.toNat < (m.arr64 LVS).size % 2 ^ 64 / 2 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hl)
    rw [UInt64.toNat_shiftRight] at this
    simpa [Mem.len64, Nat.shiftRight_eq_div_pow] using this
  have hsz : k.toNat * 2 + 2 ≤ (m.arr64 LVS).size := by
    have := Nat.mod_le (m.arr64 LVS).size (2 ^ 64)
    omega
  have hk62 : k.toNat + 1 < 2 ^ 63 := by
    have := Nat.mod_lt (m.arr64 LVS).size (show 0 < 2 ^ 64 by decide)
    omega
  have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have h2k : (k * 2).toNat = k.toNat * 2 := by rw [UInt64.toNat_mul]; simp; omega
  have h2k1 : (k * 2 + 1).toNat = k.toNat * 2 + 1 := by rw [UInt64.toNat_add, h2k]; simp; omega
  have hofk : UInt64.ofNat k.toNat = k := by simp
  -- reads of the pushed array
  have rd : ∀ i : Word, rdW ((lvsPush m k x y).arr64 LVS) i =
      if k * 2 + 1 = i then y else if k * 2 = i then x else rdW (m.arr64 LVS) i := by
    intro i
    simp only [lvsPush, rdW_set64, size_set64]
    have e1 : (k * 2 + 1).toNat < (m.arr64 LVS).size := by omega
    have e2 : (k * 2).toNat < (m.arr64 LVS).size := by omega
    simp only [e1, e2, and_true, true_and]
  have hsize : ((lvsPush m k x y).arr64 LVS).size = (m.arr64 LVS).size := by
    simp only [lvsPush, size_set64]
  have old : ∀ j, j < k.toNat → rdW ((lvsPush m k x y).arr64 LVS) (UInt64.ofNat j * 2) =
      rdW (m.arr64 LVS) (UInt64.ofNat j * 2) ∧ rdW ((lvsPush m k x y).arr64 LVS) (UInt64.ofNat j * 2 + 1) =
      rdW (m.arr64 LVS) (UInt64.ofNat j * 2 + 1) := by
    intro j hj
    have a1 := ofNat_mul2_toNat j (by omega)
    have a2 := ofNat_mul2_add1_toNat j (by omega)
    rw [rd, rd]
    have n1 : k * 2 + 1 ≠ UInt64.ofNat j * 2 := fun e => by have := congrArg UInt64.toNat e; omega
    have n2 : k * 2 ≠ UInt64.ofNat j * 2 := fun e => by have := congrArg UInt64.toNat e; omega
    have n3 : k * 2 + 1 ≠ UInt64.ofNat j * 2 + 1 := fun e => by have := congrArg UInt64.toNat e; omega
    have n4 : k * 2 ≠ UInt64.ofNat j * 2 + 1 := fun e => by have := congrArg UInt64.toNat e; omega
    simp only [n1, n2, n3, n4, ↓reduceIte, and_self]
  have new0 : rdW ((lvsPush m k x y).arr64 LVS) (UInt64.ofNat k.toNat * 2) = x := by
    rw [hofk, rd]
    have : k * 2 + 1 ≠ k * 2 := fun e => by have := congrArg UInt64.toNat e; omega
    simp [this]
  have new1 : rdW ((lvsPush m k x y).arr64 LVS) (UInt64.ofNat k.toNat * 2 + 1) = y := by
    rw [hofk, rd]; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hk1, lvsList, lvsAt, new0, new1, lvsList_congr _ _ _ old, h.eq]
  · intro j hj
    rw [hk1] at hj
    by_cases e : j = k.toNat
    · subst e; rw [new1]; exact hy
    · rw [(old j (by omega)).2]; exact h.hw j (by omega)
  · rw [hk1, hsize]; omega
  · rw [hk1]; exact hk62

theorem lvsPush_frame (m : Mem) (k x y : Word) : MemFrame [LVS] [] m (lvsPush m k x y) :=
  (MemFrame.set64 m LVS (by decide) (k * 2) x).trans
    (MemFrame.set64 (m.set64 LVS (k * 2) x) LVS (by decide) (k * 2 + 1) y)

/-! ## `leaf_mem` -/

theorem lfmW_ok (a : Array Word) (x y : Word) (hy : y.toNat < 2 ^ 32) :
    ∀ (kn : Nat) (k : Word), k.toNat = kn → kn < 2 ^ 63 →
      (∀ j, j < kn → (rdW a (UInt64.ofNat j * 2 + 1)).toNat < 2 ^ 32) →
      lfmW a x y k = if leafMem (lvsList a kn) x.toNat (decE y) then 1 else 0 := by
  intro kn
  induction kn with
  | zero =>
    intro k hk _ _
    have : k = 0 := UInt64.toNat_inj.mp (by simpa using hk)
    subst this; rw [lfmW_zero]; rfl
  | succ kn ih =>
    intro k hk hk62 hw
    have hk0 : k ≠ 0 := fun e => by subst e; simp at hk
    have hkm : (k - 1).toNat = kn := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    have hof : UInt64.ofNat kn = k - 1 := by rw [← hkm]; simp
    have hrest := ih (k - 1) hkm (by omega) (fun j hj => hw j (by omega))
    have hwk := hw kn (by omega)
    rw [hof] at hwk
    simp only [lvsList, lvsAt, leafMem, hof]
    by_cases hh : rdW a ((k - 1) * 2) = x ∧ rdW a ((k - 1) * 2 + 1) = y
    · rw [lfmW_hit a x y k hk0 hh, hh.1, hh.2]; simp
    · rw [lfmW_next a x y k hk0 hh, hrest]
      have : ((rdW a ((k - 1) * 2)).toNat == x.toNat && decE (rdW a ((k - 1) * 2 + 1)) == decE y) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        by_cases h1 : rdW a ((k - 1) * 2) = x
        · right; intro e
          exact hh ⟨h1, by rw [← word_decE _ hwk, ← word_decE y hy, e]⟩
        · left; intro e; exact h1 (UInt64.toNat_inj.mp e)
      rw [this, Bool.false_or]

/-! ## `fl_go` refines `fvarLeavesGo` -/

/-- The unit-valued decoder of the `seen` set. -/
def decU (_ : Word) : Unit := ()

theorem flSch_wf : flSch.WF := ⟨by decide, by decide⟩
theorem lsbSch_wf : lsbSch.WF := ⟨by decide, by decide⟩

/-- The leaves walk's frame. -/
abbrev FlFrame (m m' : Mem) : Prop := MemFrame [FLM, LVS] [154, 155] m m'

theorem FlFrame.arenaD {m m' : Mem} {a : AState} (hf : FlFrame m m') (h : ArenaD m a) : ArenaD m' a :=
  ArenaD.frame64 hf (fun b hb => by simp at hb; rcases hb with rfl | rfl <;> decide)
    (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> decide) h

/-- The arms of `fvarLeavesGo` on a view, named. -/
def flArm (acc : List (Nat × EIdx)) (seen : Std.HashMap EIdx Unit) (F : Nat) :
    ENodeView → AM (List (Nat × EIdx) × Std.HashMap EIdx Unit)
  | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (acc, seen)
  | .fvar idx ty => fvarLeavesGo ((idx, ty) :: acc) seen F ty
  | .app f a => fvarLeavesGoArmApp acc seen F f a
  | .lam ty body | .forallE ty body => fvarLeavesGoArmBind acc seen F ty body
  | .letE ty val body => fvarLeavesGoArmLet acc seen F ty val body
  | .proj _ _ sub => fvarLeavesGo acc seen F sub

def flNodeA (acc : List (Nat × EIdx)) (seen : Std.HashMap EIdx Unit) (F : Nat) (h : EIdx) :
    AM (List (Nat × EIdx) × Std.HashMap EIdx Unit) := do
  let v ← view h
  flArm acc seen F v

theorem fvarLeavesGo_succ' (acc : List (Nat × EIdx)) (seen : Std.HashMap EIdx Unit) (F : Nat)
    (h : EIdx) :
    fvarLeavesGo acc seen (F + 1) h = (do
      if (fvarOfData (← derivedE h)).toNat == 0 then pure (acc, seen)
      else
        match seen[h]? with
        | some _ => pure (acc, seen)
        | none => flNodeA acc (seen.insert h ()) F h) := by
  rw [fvarLeavesGo_succ]
  congr 1

theorem flNodeA_run (acc : List (Nat × EIdx)) (seen : Std.HashMap EIdx Unit) (F : Nat) (h : EIdx)
    (a : AState) (v : ENodeView) (hv : a.store.view h = some v) :
    (flNodeA acc seen F h).run a = (flArm acc seen F v).run a := by
  simp only [flNodeA, StateT.run_bind, view_run h a v hv]; rfl

def FlGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (seen : Std.HashMap EIdx Unit) (acc : List (Nat × EIdx))
    (h k c k' : Word), ArenaD m a → MemoRG flSch bmKey decU m seen → LeafR m k acc →
    h.toNat < 2 ^ 32 → flW n m h k c = some (k', m') →
    ∃ acc' seen', (fvarLeavesGo acc seen c.toNat (decE h)).run a = .ok ((acc', seen'), a) ∧
      MemoRG flSch bmKey decU m' seen' ∧ LeafR m' k' acc' ∧ FlFrame m m'

def FlNodeOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (seen : Std.HashMap EIdx Unit) (acc : List (Nat × EIdx))
    (h k c k' : Word), ArenaD m a → MemoRG flSch bmKey decU m seen → LeafR m k acc →
    h.toNat < 2 ^ 32 → flNodeW n m h k c = some (k', m') →
    ∃ acc' seen', (flNodeA acc seen c.toNat (decE h)).run a = .ok ((acc', seen'), a) ∧
      MemoRG flSch bmKey decU m' seen' ∧ LeafR m' k' acc' ∧ FlFrame m m'

theorem flGoOK_succ (n : Nat) (ih : FlNodeOK n) : FlGoOK (n + 1) := by
  intro m m' a seen acc h k c k' hD hM hL hh hb
  have hc : ¬ c = 0 := fun hc => by rw [flW.abort1 n m h k c hc] at hb; cases hb
  rw [ctrW_toNat c hc, fvarLeavesGo_succ', StateT.run_bind, derivedE_run, except_ok_bind]
  rw [← derFW_ok m a hD.1 hD.2 h hh]
  by_cases hf : derFW m h = 0
  · rw [flW.arm1 n m h k c hc hf] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact ⟨acc, seen, by rw [hf]; rfl, hM, hL, MemFrame.refl _ _ _⟩
  have hf' : ((derFW m h).toNat == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; exact hf (UInt64.toNat_inj.mp (by simpa using e))
  rw [hf']
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hr : ¬ mfindG flSch m h 0 = [] := fun hr => by rw [flW.abort2 n m h k c hc hf hr] at hb; cases hb
  have hk : bmKey.ok h 0 := ⟨hh, rfl⟩
  by_cases hh0 : (mfindG flSch m h 0).headD 0 ≠ 0
  · rw [flW.arm2 n m h k c hc hf hr hh0] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    have e := memoRG_hit flSch bmKey decU m seen hM h 0 hr hh0 hk
    simp only [bmKey] at e
    rw [e]
    exact ⟨acc, seen, rfl, hM, hL, MemFrame.refl _ _ _⟩
  · simp only [ne_eq, Decidable.not_not] at hh0
    rw [flW.arm3 n m h k c hc hf hr hh0, ← msetG_eq flSch m h 0 0 hr] at hb
    have e := memoRG_miss flSch bmKey decU m seen hM h 0 hk hr hh0
    simp only [bmKey] at e
    rw [e]
    cases hs : msetG flSch m h 0 0 with
    | none => rw [hs, flW.k_fl_put.none] at hb; cases hb
    | some m₁ =>
      rw [hs, flW.k_fl_put.arm1] at hb
      have hf₁ := msetG_frame flSch flSch_wf m m₁ h 0 0 hs
      have hM₁ := memoRG_set flSch flSch_wf bmKey decU m seen hM h 0 0 hk m₁ hs
      simp only [bmKey, decU] at hM₁
      have hD₁ : ArenaD m₁ a := FlFrame.arenaD (hf₁.mono (by simp) (by simp)) hD
      have hL₁ : LeafR m₁ k acc := hL.frame (hf₁.arr LVS (by decide) (by decide))
      obtain ⟨acc', seen', ha, hM', hL', hf'⟩ := ih m₁ m' a _ acc h k (c - 1) k' hD₁ hM₁ hL₁ hh hb
      exact ⟨acc', seen', ha, hM', hL', (hf₁.mono (by simp) (by simp)).trans hf'⟩

theorem flNodeW.k_fl_go_3_eq (n : Nat) (c b : Word) (o : Option (Word × Mem)) :
    flNodeW.k_fl_go_3 n c b o = flNodeW.k_fl_go n c b o := by
  rcases o with _ | ⟨x, m₁⟩
  · rw [flNodeW.k_fl_go_3.none, flNodeW.k_fl_go.none]
  · rw [flNodeW.k_fl_go_3.arm1, flNodeW.k_fl_go.arm1]

/-- Two children in a row. -/
theorem flSeq_ok (n : Nat) (ih : FlGoOK n) (m m' : Mem) (a : AState) (seen : Std.HashMap EIdx Unit)
    (acc : List (Nat × EIdx)) (hD : ArenaD m a) (hM : MemoRG flSch bmKey decU m seen) (k : Word)
    (hL : LeafR m k acc) (fw bw c k' : Word) (hf : fw.toNat < 2 ^ 32) (hb' : bw.toNat < 2 ^ 32)
    (hb : flNodeW.k_fl_go n c bw (flW n m fw k c) = some (k', m')) :
    ∃ acc' seen', (do
        let (acc, seen) ← fvarLeavesGo acc seen c.toNat (decE fw)
        fvarLeavesGo acc seen c.toNat (decE bw) :
          AM (List (Nat × EIdx) × Std.HashMap EIdx Unit)).run a = .ok ((acc', seen'), a) ∧
      MemoRG flSch bmKey decU m' seen' ∧ LeafR m' k' acc' ∧ FlFrame m m' := by
  rcases h1 : flW n m fw k c with _ | ⟨k₁, m₁⟩
  · rw [h1, flNodeW.k_fl_go.none] at hb; cases hb
  rw [h1, flNodeW.k_fl_go.arm1] at hb
  obtain ⟨acc₁, seen₁, ha₁, hM₁, hL₁, hf₁⟩ := ih m m₁ a seen acc fw k c k₁ hD hM hL hf h1
  obtain ⟨acc₂, seen₂, ha₂, hM₂, hL₂, hf₂⟩ := ih m₁ m' a seen₁ acc₁ bw k₁ c k' (hf₁.arenaD hD) hM₁ hL₁ hb' hb
  exact ⟨acc₂, seen₂, by simp only [StateT.run_bind, ha₁, except_ok_bind]; exact ha₂, hM₂, hL₂,
    hf₁.trans hf₂⟩

theorem flNodeOK_succ (n : Nat) (ih : FlGoOK n) : FlNodeOK (n + 1) := by
  intro m m' a seen acc h k c k' hD hM hL hh hb
  have hR := hD.1
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [flNodeW.abort1 n m h k c hs] at hb; cases hb
  have vok : ∀ c, ¬ tcnt m c (tierW h) ≤ idxW h → viewOK m h c :=
    fun c hc => ⟨hs, UInt64.not_le.mp hc⟩
  have leaf : ∀ v, a.store.view (decE h) = some v → flArm acc seen c.toNat v = pure (acc, seen) →
      flNodeW (n + 1) m h k c = some (k, m) →
      ∃ acc' seen', (flNodeA acc seen c.toNat (decE h)).run a = .ok ((acc', seen'), a) ∧
        MemoRG flSch bmKey decU m' seen' ∧ LeafR m' k' acc' ∧ FlFrame m m' := by
    intro v hv hx e; rw [e] at hb; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact ⟨acc, seen, by rw [flNodeA_run _ _ _ _ a _ hv, hx]; rfl, hM, hL, MemFrame.refl _ _ _⟩
  by_cases g0 : tagW h = 0
  · have hvo := vok BVAR fun hc => by rw [flNodeW.abort2 n m h k c hs  g0 hc] at hb; cases hb
    exact leaf _ (view_bvar m a hR h hh hvo g0) rfl (flNodeW.arm1 n m h k c hs g0 (UInt64.not_le.mpr hvo.2))
  by_cases g1 : tagW h = 1
  · have hvo := vok FVAR fun hc => by rw [flNodeW.abort3 n m h k c hs g0 g1 hc] at hb; cases hb
    have hl : ¬ m.len64 LVS >>> 1 ≤ k := fun hl => by
      rw [flNodeW.abort4 n m h k c hs g0 g1 (UInt64.not_le.mpr hvo.2) hl] at hb; cases hb
    obtain ⟨hv, hty⟩ := view_fvar_idx m a hR h hh hvo g1
    rw [flNodeW.arm2 n m h k c hs g0 g1 (UInt64.not_le.mpr hvo.2) hl] at hb
    have hfp : FlFrame m (lvsPush m k (tfld m FVAR (tierW h) (idxW h) 0)
        (tfld m FVAR (tierW h) (idxW h) 1)) :=
      (lvsPush_frame m k (tfld m FVAR (tierW h) (idxW h) 0)
        (tfld m FVAR (tierW h) (idxW h) 1)).mono (by simp) (by simp)
    have hL₁ := hL.push (tfld m FVAR (tierW h) (idxW h) 0) _ hl hty
    obtain ⟨acc', seen', ha, hM', hL', hf'⟩ :=
      ih _ m' a seen _ _ (k + 1) c k' (hfp.arenaD hD)
        (memoRG_frame flSch flSch_wf bmKey decU [LVS] [] (by decide) (by decide) _ _
          (lvsPush_frame m k (tfld m FVAR (tierW h) (idxW h) 0)
            (tfld m FVAR (tierW h) (idxW h) 1)) seen hM)
        hL₁ hty hb
    exact ⟨acc', seen', by rw [flNodeA_run _ _ _ _ a _ hv]; exact ha, hM', hL', hfp.trans hf'⟩
  by_cases g4 : tagW h = 4
  · have hvo : viewOKA m h := ⟨hs, UInt64.not_le.mp fun hc => by rw [flNodeW.abort5 n m h k c hs g0 g1 g4 hc] at hb; cases hb⟩
    obtain ⟨hv, hf, ha⟩ := view_app m a hR h hh hvo g4
    rw [flNodeW.arm3 n m h k c hs g0 g1 g4 (UInt64.not_le.mpr hvo.2)] at hb
    obtain ⟨acc', seen', h1, h2⟩ := flSeq_ok n ih m m' a seen acc hD hM k hL _ _ c k' hf ha hb
    exact ⟨acc', seen', (flNodeA_run _ _ _ _ a _ hv).trans
      (by simp only [flArm, fvarLeavesGoArmApp]; exact h1), h2⟩
  by_cases g5 : tagW h = 5
  · have hvo := vok LAM fun hc => by rw [flNodeW.abort6 n m h k c hs g0 g1 g4 g5 hc] at hb; cases hb
    obtain ⟨hv, hf, ha⟩ := view_lam m a hR h hh hvo g5
    rw [flNodeW.arm4 n m h k c hs g0 g1 g4 g5 (UInt64.not_le.mpr hvo.2)] at hb
    obtain ⟨acc', seen', h1, h2⟩ := flSeq_ok n ih m m' a seen acc hD hM k hL _ _ c k' hf ha hb
    exact ⟨acc', seen', (flNodeA_run _ _ _ _ a _ hv).trans
      (by simp only [flArm, fvarLeavesGoArmBind]; exact h1), h2⟩
  by_cases g6 : tagW h = 6
  · have hvo := vok FORALL fun hc => by rw [flNodeW.abort7 n m h k c hs g0 g1 g4 g5 g6 hc] at hb; cases hb
    obtain ⟨hv, hf, ha⟩ := view_forall m a hR h hh hvo g6
    rw [flNodeW.arm5 n m h k c hs g0 g1 g4 g5 g6 (UInt64.not_le.mpr hvo.2)] at hb
    obtain ⟨acc', seen', h1, h2⟩ := flSeq_ok n ih m m' a seen acc hD hM k hL _ _ c k' hf ha hb
    exact ⟨acc', seen', (flNodeA_run _ _ _ _ a _ hv).trans
      (by simp only [flArm, fvarLeavesGoArmBind]; exact h1), h2⟩
  by_cases g7 : tagW h = 7
  · have hvo := vok LET fun hc => by rw [flNodeW.abort9 n m h k c hs g0 g1 g4 g5 g6 (fun e => absurd (g7.symm.trans e) (by decide)) g7 hc] at hb; cases hb
    obtain ⟨hv, ht, hv', hb'⟩ := view_let m a hR h hh hvo g7
    rw [flNodeW.arm7 n m h k c hs g0 g1 g4 g5 g6 (fun e => absurd (g7.symm.trans e) (by decide)) g7
      (UInt64.not_le.mpr hvo.2)] at hb
    rw [flNodeA_run _ _ _ _ a _ hv]
    simp only [flArm, fvarLeavesGoArmLet]
    rcases h1 : flW n m (tfld m LET (tierW h) (idxW h) 0) k c with _ | ⟨k₁, m₁⟩
    · rw [h1, flNodeW.k_fl_go_2.none] at hb; cases hb
    rw [h1, flNodeW.k_fl_go_2.arm1, flNodeW.k_fl_go_3_eq] at hb
    obtain ⟨acc₁, seen₁, ha₁, hM₁, hL₁, hf₁⟩ := ih m m₁ a seen acc _ k c k₁ hD hM hL ht h1
    obtain ⟨acc₂, seen₂, ha₂, hM₂, hL₂, hf₂⟩ :=
      flSeq_ok n ih m₁ m' a seen₁ acc₁ (hf₁.arenaD hD) hM₁ k₁ hL₁ _ _ c k' hv' hb' hb
    exact ⟨acc₂, seen₂, by simp only [StateT.run_bind, ha₁, except_ok_bind]; exact ha₂, hM₂, hL₂,
      hf₁.trans hf₂⟩
  by_cases g9 : tagW h = 9
  · have hvo := vok PROJ fun hc => by rw [flNodeW.abort8 n m h k c hs g0 g1 g4 g5 g6 g9 hc] at hb; cases hb
    obtain ⟨hv, -, he⟩ := view_proj m a hR h hh hvo g9
    rw [flNodeW.arm6 n m h k c hs g0 g1 g4 g5 g6 g9 (UInt64.not_le.mpr hvo.2)] at hb
    obtain ⟨acc', seen', h1, h2⟩ := ih m m' a seen acc _ k c k' hD hM hL he hb
    exact ⟨acc', seen', (flNodeA_run _ _ _ _ a _ hv).trans h1, h2⟩
  by_cases g2 : tagW h = 2
  · have hvo := vok SORT fun hc => by rw [flNodeW.abort10 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 hc] at hb; cases hb
    obtain ⟨_, hv⟩ := view_sort m a hR h hh hvo g2
    exact leaf _ hv rfl (flNodeW.arm8 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 (UInt64.not_le.mpr hvo.2))
  by_cases g3 : tagW h = 3
  · have hvo := vok CONST fun hc => by rw [flNodeW.abort11 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 g3 hc] at hb; cases hb
    obtain ⟨_, _, hv⟩ := view_const m a hR h hh hvo g3
    exact leaf _ hv rfl (flNodeW.arm9 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 g3 (UInt64.not_le.mpr hvo.2))
  by_cases g8 : tagW h = 8
  · have hvo := vok LIT fun hc => by rw [flNodeW.abort12 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 g3 g8 hc] at hb; cases hb
    obtain ⟨_, hv⟩ := view_lit m a hR h hh hvo g8
    exact leaf _ hv rfl (flNodeW.arm10 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 g3 g8 (UInt64.not_le.mpr hvo.2))
  rw [flNodeW.abort13 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 g3 g8] at hb; cases hb

theorem flGoOK (n : Nat) : FlGoOK n ∧ FlNodeOK n := by
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ hb => by simp [flW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ hb => by simp [flNodeW] at hb⟩
  | succ n ih => exact ⟨flGoOK_succ n ih.2, flNodeOK_succ n ih.1⟩

/-! ## `lsb_go` refines `leavesSubGo` -/

/-- The subset walk's frame. -/
abbrev LsbFrame (m m' : Mem) : Prop := MemFrame [LSM] [156, 157] m m'

theorem LsbFrame.arenaD {m m' : Mem} {a : AState} (hf : LsbFrame m m') (h : ArenaD m a) : ArenaD m' a :=
  ArenaD.frame64 hf (fun b hb => by simp at hb; subst hb; decide)
    (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> decide) h

theorem LsbFrame.lvs {m m' : Mem} (hf : LsbFrame m m') : m'.arr64 LVS = m.arr64 LVS :=
  hf.1 LVS (by decide) (by decide)

def lsbArm (bl : List (Nat × EIdx)) (memo : Std.HashMap EIdx Bool) (F : Nat) :
    ENodeView → AM (Bool × Std.HashMap EIdx Bool)
  | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (true, memo)
  | .fvar idx ty => if leafMem bl idx ty then leavesSubGo bl memo F ty else pure (false, memo)
  | .app f a => leavesSubArmApp bl memo F f a
  | .lam ty body | .forallE ty body => leavesSubArmBind bl memo F ty body
  | .letE ty val body => leavesSubArmLet bl memo F ty val body
  | .proj _ _ sub => leavesSubGo bl memo F sub

def lsbNodeA (bl : List (Nat × EIdx)) (memo : Std.HashMap EIdx Bool) (F : Nat) (h : EIdx) :
    AM (Bool × Std.HashMap EIdx Bool) := do
  let v ← view h
  lsbArm bl memo F v

theorem leavesSubGo_succ' (bl : List (Nat × EIdx)) (memo : Std.HashMap EIdx Bool) (F : Nat) (h : EIdx) :
    leavesSubGo bl memo (F + 1) h = (do
      if (fvarOfData (← derivedE h)).toNat == 0 then pure (true, memo)
      else
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, memo') ← lsbNodeA bl memo F h
          pure (r, memo'.insert h r)) := by
  rw [leavesSubGo_succ]
  congr 1; funext x
  by_cases hx : ((fvarOfData x).toNat == 0) = true
  · simp only [hx, ↓reduceIte]
  · simp only [hx, Bool.false_eq_true, ↓reduceIte]
    cases memo[h]? with
    | some r => rfl
    | none =>
      simp only [lsbNodeA, bind_assoc]
      congr 1; funext v
      cases v <;> simp only [lsbArm, pure_bind] <;> (try split) <;> simp only [pure_bind]

theorem lsbNodeA_run (bl : List (Nat × EIdx)) (memo : Std.HashMap EIdx Bool) (F : Nat) (h : EIdx)
    (a : AState) (v : ENodeView) (hv : a.store.view h = some v) :
    (lsbNodeA bl memo F h).run a = (lsbArm bl memo F v).run a := by
  simp only [lsbNodeA, StateT.run_bind, view_run h a v hv]; rfl

def LsbGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (memo : Std.HashMap EIdx Bool) (bl : List (Nat × EIdx)) (h k c r : Word),
    ArenaD m a → MemoRG lsbSch bmKey decBW m memo → LeafR m k bl → h.toNat < 2 ^ 32 →
    lsbW n m h k c = some (r, m') →
    ∃ memo', (leavesSubGo bl memo c.toNat (decE h)).run a = .ok ((r != 0, memo'), a) ∧
      MemoRG lsbSch bmKey decBW m' memo' ∧ r ≤ 1 ∧ LsbFrame m m'

def LsbNodeOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (memo : Std.HashMap EIdx Bool) (bl : List (Nat × EIdx)) (h k c r : Word),
    ArenaD m a → MemoRG lsbSch bmKey decBW m memo → LeafR m k bl → h.toNat < 2 ^ 32 →
    lsbNodeW n m h k c = some (r, m') →
    ∃ memo', (lsbNodeA bl memo c.toNat (decE h)).run a = .ok ((r != 0, memo'), a) ∧
      MemoRG lsbSch bmKey decBW m' memo' ∧ r ≤ 1 ∧ LsbFrame m m'

theorem lsbW_hit' (n : Nat) (m : Mem) (h k c : Word) (hc : c ≠ 0) (hf : derFW m h ≠ 0)
    (hr : mfindG lsbSch m h 0 ≠ []) (hh : (mfindG lsbSch m h 0).headD 0 ≠ 0) :
    lsbW (n + 1) m h k c =
      some (if rdW (m.arr64 LSM) ((mfindG lsbSch m h 0).tail.headD 0 * 4 + 3) ≠ 0 then 1 else 0, m) := by
  by_cases hv : rdW (m.arr64 LSM) ((mfindG lsbSch m h 0).tail.headD 0 * 4 + 3) = 0
  · rw [lsbW.arm2 n m h k c hc hf hr hh hv]; simp only [ne_eq, hv, not_true_eq_false, ↓reduceIte]
  · rw [lsbW.arm3 n m h k c hc hf hr hh hv]; simp only [ne_eq, hv, not_false_eq_true, ↓reduceIte]

theorem lsbNodeW.k_lsb_go_3_eq (n : Nat) (k c b : Word) (o : Option (Word × Mem)) :
    lsbNodeW.k_lsb_go_3 n k c b o = lsbNodeW.k_lsb_go n k c b o := by
  rcases o with _ | ⟨x, m₁⟩
  · rw [lsbNodeW.k_lsb_go_3.none, lsbNodeW.k_lsb_go.none]
  · by_cases hx : x = 0
    · rw [lsbNodeW.k_lsb_go_3.arm1 _ _ _ _ _ _ hx, lsbNodeW.k_lsb_go.arm1 _ _ _ _ _ _ hx]
    · rw [lsbNodeW.k_lsb_go_3.arm2 _ _ _ _ _ _ hx, lsbNodeW.k_lsb_go.arm2 _ _ _ _ _ _ hx]

theorem lsbGoOK_succ (n : Nat) (ih : LsbNodeOK n) : LsbGoOK (n + 1) := by
  intro m m' a memo bl h k c r hD hM hL hh hb
  have hc : ¬ c = 0 := fun hc => by rw [lsbW.abort1 n m h k c hc] at hb; cases hb
  rw [ctrW_toNat c hc, leavesSubGo_succ', StateT.run_bind, derivedE_run, except_ok_bind]
  rw [← derFW_ok m a hD.1 hD.2 h hh]
  by_cases hf : derFW m h = 0
  · rw [lsbW.arm1 n m h k c hc hf] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    refine ⟨memo, by rw [hf]; rfl, hM, by decide, MemFrame.refl _ _ _⟩
  have hf' : ((derFW m h).toNat == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; exact hf (UInt64.toNat_inj.mp (by simpa using e))
  rw [hf']
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hr : ¬ mfindG lsbSch m h 0 = [] := fun hr => by rw [lsbW.abort2 n m h k c hc hf hr] at hb; cases hb
  have hk : bmKey.ok h 0 := ⟨hh, rfl⟩
  by_cases hh0 : (mfindG lsbSch m h 0).headD 0 ≠ 0
  · rw [lsbW_hit' n m h k c hc hf hr hh0] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    have e := memoRG_hit lsbSch bmKey decBW m memo hM h 0 hr hh0 hk
    simp only [bmKey] at e
    rw [e]
    refine ⟨memo, ?_, hM, by split <;> decide, MemFrame.refl _ _ _⟩
    simp only [decBW, mvG]
    split <;> rename_i hv
    · have : (rdW (m.arr64 LSM) ((mfindG lsbSch m h 0).tail.headD 0 * 4 + 3) != 0) = true := by
        simpa using hv
      simp only [this]; rfl
    · have : rdW (m.arr64 LSM) ((mfindG lsbSch m h 0).tail.headD 0 * 4 + 3) = 0 := by simpa using hv
      simp only [this]; rfl
  · simp only [ne_eq, Decidable.not_not] at hh0
    rw [lsbW.arm4 n m h k c hc hf hr hh0] at hb
    have e := memoRG_miss lsbSch bmKey decBW m memo hM h 0 hk hr hh0
    simp only [bmKey] at e
    rw [e]
    rcases hn : lsbNodeW n m h k (c - 1) with _ | ⟨r₁, m₁⟩
    · rw [hn, lsbW.k_lsb_node.none] at hb; cases hb
    rw [hn] at hb
    have hr₁ : ¬ mfindG lsbSch m₁ h 0 = [] := fun hr₁ => by
      rw [lsbW.k_lsb_node.abort1 h r₁ m₁ hr₁] at hb; cases hb
    rw [lsbW.k_lsb_node.arm1 h r₁ m₁ hr₁, ← msetG_eq lsbSch m₁ h 0 r₁ hr₁] at hb
    cases hs : msetG lsbSch m₁ h 0 r₁ with
    | none => rw [hs, lsbW.k_lsb_put.none] at hb; cases hb
    | some m₂ =>
      rw [hs, lsbW.k_lsb_put.arm1] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      obtain ⟨memo₁, ha₁, hM₁, hle, hf₁⟩ := ih m m₁ a memo bl h k (c - 1) r₁ hD hM hL hh hn
      refine ⟨memo₁.insert (decE h) (r₁ != 0), ?_, ?_, hle, ?_⟩
      · simp only [StateT.run_bind, ha₁, except_ok_bind]; rfl
      · have := memoRG_set lsbSch lsbSch_wf bmKey decBW m₁ memo₁ hM₁ h 0 r₁ hk m₂ hs
        simpa [bmKey, decBW] using this
      · exact hf₁.trans ((msetG_frame lsbSch lsbSch_wf m₁ m₂ h 0 r₁ hs).mono (by simp) (by simp))

theorem lsbAnd_ok (n : Nat) (ih : LsbGoOK n) (m m' : Mem) (a : AState) (memo : Std.HashMap EIdx Bool)
    (bl : List (Nat × EIdx)) (hD : ArenaD m a) (hM : MemoRG lsbSch bmKey decBW m memo) (k : Word)
    (hL : LeafR m k bl) (fw bw c r : Word) (hf : fw.toNat < 2 ^ 32) (hb' : bw.toNat < 2 ^ 32)
    (hb : lsbNodeW.k_lsb_go n k c bw (lsbW n m fw k c) = some (r, m')) :
    ∃ memo', (do
        let (rf, memo) ← leavesSubGo bl memo c.toNat (decE fw)
        if rf then leavesSubGo bl memo c.toNat (decE bw) else pure (false, memo) :
          AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((r != 0, memo'), a) ∧
      MemoRG lsbSch bmKey decBW m' memo' ∧ r ≤ 1 ∧ LsbFrame m m' := by
  cases h1 : lsbW n m fw k c with
  | none => rw [h1, lsbNodeW.k_lsb_go.none] at hb; cases hb
  | some q =>
    obtain ⟨x, m₁⟩ := q
    obtain ⟨memo₁, ha₁, hM₁, hx, hf₁⟩ := ih m m₁ a memo bl fw k c x hD hM hL hf h1
    rw [h1] at hb
    by_cases hx0 : x = 0
    · subst hx0
      rw [lsbNodeW.k_lsb_go.arm1 _ _ _ _ _ _ rfl] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact ⟨memo₁, by simp only [StateT.run_bind, ha₁, except_ok_bind]; rfl, hM₁, by decide, hf₁⟩
    · rw [lsbNodeW.k_lsb_go.arm2 _ _ _ _ _ _ hx0] at hb
      obtain ⟨memo₂, ha₂, hM₂, hle, hf₂⟩ :=
        ih m₁ m' a memo₁ bl bw k c r (hf₁.arenaD hD) hM₁ (hL.frame hf₁.lvs) hb' hb
      refine ⟨memo₂, ?_, hM₂, hle, hf₁.trans hf₂⟩
      have : (x != 0) = true := by simpa using hx0
      simp only [StateT.run_bind, ha₁, except_ok_bind, this, ↓reduceIte]
      exact ha₂

theorem lsbNodeOK_succ (n : Nat) (ih : LsbGoOK n) : LsbNodeOK (n + 1) := by
  intro m m' a memo bl h k c r hD hM hL hh hb
  have hR := hD.1
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [lsbNodeW.abort1 n m h k c hs] at hb; cases hb
  have vok : ∀ c, ¬ tcnt m c (tierW h) ≤ idxW h → viewOK m h c :=
    fun c hc => ⟨hs, UInt64.not_le.mp hc⟩
  have one : ∀ v, a.store.view (decE h) = some v → lsbArm bl memo c.toNat v = pure (true, memo) →
      lsbNodeW (n + 1) m h k c = some (1, m) →
      ∃ memo', (lsbNodeA bl memo c.toNat (decE h)).run a = .ok ((r != 0, memo'), a) ∧
        MemoRG lsbSch bmKey decBW m' memo' ∧ r ≤ 1 ∧ LsbFrame m m' := by
    intro v hv hx e; rw [e] at hb; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact ⟨memo, by rw [lsbNodeA_run _ _ _ _ a _ hv, hx]; rfl, hM, by decide, MemFrame.refl _ _ _⟩
  have hk62 : k.toNat < 2 ^ 63 := hL.small
  by_cases g0 : tagW h = 0
  · have hvo := vok BVAR fun hc => by rw [lsbNodeW.abort2 n m h k c hs  g0 hc] at hb; cases hb
    exact one _ (view_bvar m a hR h hh hvo g0) rfl (lsbNodeW.arm1 n m h k c hs g0 (UInt64.not_le.mpr hvo.2))
  by_cases g1 : tagW h = 1
  · have hvo := vok FVAR fun hc => by rw [lsbNodeW.abort3 n m h k c hs g0 g1 hc] at hb; cases hb
    obtain ⟨hv, hty⟩ := view_fvar_idx m a hR h hh hvo g1
    have hlm := lfmW_ok (m.arr64 LVS) (tfld m FVAR (tierW h) (idxW h) 0)
      (tfld m FVAR (tierW h) (idxW h) 1) hty k.toNat k rfl hk62 hL.hw
    rw [← hL.eq] at hlm
    rw [lsbNodeA_run _ _ _ _ a _ hv]
    simp only [lsbArm]
    by_cases hin : leafMem bl (tfld m FVAR (tierW h) (idxW h) 0).toNat
        (decE (tfld m FVAR (tierW h) (idxW h) 1)) = true
    · rw [hin] at hlm
      rw [lsbNodeW.arm3 n m h k c hs g0 g1 (UInt64.not_le.mpr hvo.2) (by rw [hlm]; decide)] at hb
      simp only [hin, ↓reduceIte]
      exact ih m m' a memo bl _ k c r hD hM hL hty hb
    · simp only [hin, Bool.false_eq_true, ↓reduceIte] at hlm
      rw [lsbNodeW.arm2 n m h k c hs g0 g1 (UInt64.not_le.mpr hvo.2) hlm] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      simp only [hin, Bool.false_eq_true, ↓reduceIte]
      exact ⟨memo, rfl, hM, by decide, MemFrame.refl _ _ _⟩
  by_cases g4 : tagW h = 4
  · have hvo : viewOKA m h := ⟨hs, UInt64.not_le.mp fun hc => by rw [lsbNodeW.abort4 n m h k c hs g0 g1 g4 hc] at hb; cases hb⟩
    obtain ⟨hv, hf, ha⟩ := view_app m a hR h hh hvo g4
    rw [lsbNodeW.arm4 n m h k c hs g0 g1 g4 (UInt64.not_le.mpr hvo.2)] at hb
    obtain ⟨memo', h1, h2⟩ := lsbAnd_ok n ih m m' a memo bl hD hM k hL _ _ c r hf ha hb
    exact ⟨memo', (lsbNodeA_run _ _ _ _ a _ hv).trans (by simp only [lsbArm, leavesSubArmApp]; exact h1), h2⟩
  by_cases g5 : tagW h = 5
  · have hvo := vok LAM fun hc => by rw [lsbNodeW.abort5 n m h k c hs g0 g1 g4 g5 hc] at hb; cases hb
    obtain ⟨hv, hf, ha⟩ := view_lam m a hR h hh hvo g5
    rw [lsbNodeW.arm5 n m h k c hs g0 g1 g4 g5 (UInt64.not_le.mpr hvo.2)] at hb
    obtain ⟨memo', h1, h2⟩ := lsbAnd_ok n ih m m' a memo bl hD hM k hL _ _ c r hf ha hb
    exact ⟨memo', (lsbNodeA_run _ _ _ _ a _ hv).trans (by simp only [lsbArm, leavesSubArmBind]; exact h1), h2⟩
  by_cases g6 : tagW h = 6
  · have hvo := vok FORALL fun hc => by rw [lsbNodeW.abort6 n m h k c hs g0 g1 g4 g5 g6 hc] at hb; cases hb
    obtain ⟨hv, hf, ha⟩ := view_forall m a hR h hh hvo g6
    rw [lsbNodeW.arm6 n m h k c hs g0 g1 g4 g5 g6 (UInt64.not_le.mpr hvo.2)] at hb
    obtain ⟨memo', h1, h2⟩ := lsbAnd_ok n ih m m' a memo bl hD hM k hL _ _ c r hf ha hb
    exact ⟨memo', (lsbNodeA_run _ _ _ _ a _ hv).trans (by simp only [lsbArm, leavesSubArmBind]; exact h1), h2⟩
  by_cases g7 : tagW h = 7
  · have hvo := vok LET fun hc => by rw [lsbNodeW.abort8 n m h k c hs g0 g1 g4 g5 g6 (fun e => absurd (g7.symm.trans e) (by decide)) g7 hc] at hb; cases hb
    obtain ⟨hv, ht, hv', hb'⟩ := view_let m a hR h hh hvo g7
    rw [lsbNodeW.arm8 n m h k c hs g0 g1 g4 g5 g6 (fun e => absurd (g7.symm.trans e) (by decide)) g7
      (UInt64.not_le.mpr hvo.2)] at hb
    rw [lsbNodeA_run _ _ _ _ a _ hv]
    simp only [lsbArm, leavesSubArmLet]
    cases h1 : lsbW n m (tfld m LET (tierW h) (idxW h) 0) k c with
    | none => rw [h1, lsbNodeW.k_lsb_go_2.none] at hb; cases hb
    | some q =>
      obtain ⟨x, m₁⟩ := q
      obtain ⟨memo₁, ha₁, hM₁, hx, hf₁⟩ := ih m m₁ a memo bl _ k c x hD hM hL ht h1
      rw [h1] at hb
      by_cases hx0 : x = 0
      · subst hx0
        rw [lsbNodeW.k_lsb_go_2.arm1 _ _ _ _ _ _ _ rfl] at hb
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
        exact ⟨memo₁, by simp only [StateT.run_bind, ha₁, except_ok_bind]; rfl, hM₁, by decide, hf₁⟩
      · rw [lsbNodeW.k_lsb_go_2.arm2 _ _ _ _ _ _ _ hx0, lsbNodeW.k_lsb_go_3_eq] at hb
        obtain ⟨memo₂, ha₂, hM₂, hle, hf₂⟩ :=
          lsbAnd_ok n ih m₁ m' a memo₁ bl (hf₁.arenaD hD) hM₁ k (hL.frame hf₁.lvs) _ _ c r hv' hb' hb
        refine ⟨memo₂, ?_, hM₂, hle, hf₁.trans hf₂⟩
        have : (x != 0) = true := by simpa using hx0
        simp only [StateT.run_bind, ha₁, except_ok_bind, this, ↓reduceIte]
        exact ha₂
  by_cases g9 : tagW h = 9
  · have hvo := vok PROJ fun hc => by rw [lsbNodeW.abort7 n m h k c hs g0 g1 g4 g5 g6 g9 hc] at hb; cases hb
    obtain ⟨hv, -, he⟩ := view_proj m a hR h hh hvo g9
    rw [lsbNodeW.arm7 n m h k c hs g0 g1 g4 g5 g6 g9 (UInt64.not_le.mpr hvo.2)] at hb
    obtain ⟨memo', h1, h2⟩ := ih m m' a memo bl _ k c r hD hM hL he hb
    exact ⟨memo', (lsbNodeA_run _ _ _ _ a _ hv).trans h1, h2⟩
  by_cases g2 : tagW h = 2
  · have hvo := vok SORT fun hc => by rw [lsbNodeW.abort9 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 hc] at hb; cases hb
    obtain ⟨_, hv⟩ := view_sort m a hR h hh hvo g2
    exact one _ hv rfl (lsbNodeW.arm9 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 (UInt64.not_le.mpr hvo.2))
  by_cases g3 : tagW h = 3
  · have hvo := vok CONST fun hc => by rw [lsbNodeW.abort10 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 g3 hc] at hb; cases hb
    obtain ⟨_, _, hv⟩ := view_const m a hR h hh hvo g3
    exact one _ hv rfl (lsbNodeW.arm10 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 g3 (UInt64.not_le.mpr hvo.2))
  by_cases g8 : tagW h = 8
  · have hvo := vok LIT fun hc => by rw [lsbNodeW.abort11 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 g3 g8 hc] at hb; cases hb
    obtain ⟨_, hv⟩ := view_lit m a hR h hh hvo g8
    exact one _ hv rfl (lsbNodeW.arm11 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 g3 g8 (UInt64.not_le.mpr hvo.2))
  rw [lsbNodeW.abort12 n m h k c hs g0 g1 g4 g5 g6 g9 g7 g2 g3 g8] at hb; cases hb

theorem lsbGoOK (n : Nat) : LsbGoOK n ∧ LsbNodeOK n := by
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ hb => by simp [lsbW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ hb => by simp [lsbNodeW] at hb⟩
  | succ n ih => exact ⟨lsbGoOK_succ n ih.2, lsbNodeOK_succ n ih.1⟩

/-! ## The entry -/

/-- The leaf guard's two memos are well formed (at some maps): what the entry's clears need. -/
def LgMemoOK (m : Mem) : Prop :=
  (∃ mp : Std.HashMap EIdx Unit, MemoRG flSch bmKey decU m mp) ∧
    (∃ mp : Std.HashMap EIdx Bool, MemoRG lsbSch bmKey decBW m mp)

/-- The leaf guard's frame. -/
abbrev LgFrame (m m' : Mem) : Prop := MemFrame [FLM, LSM, LVS] [154, 155, 156, 157] m m'

/-- **The model of `leaf_guard` refines `leafGuard coreWalkFuel`.** -/
theorem lgW_ok (n : Nat) (m m' : Mem) (a : AState) (hD : ArenaD m a) (hM : LgMemoOK m)
    (fab base r : Word) (hfab : fab.toNat < 2 ^ 32) (hbase : base.toNat < 2 ^ 32)
    (hb : lgW (n + 1) m fab base = some (r, m')) :
    (leafGuard coreWalkFuel (decE fab) (decE base)).run a = .ok (r != 0, a) ∧ LgMemoOK m' ∧ r ≤ 1 ∧
      LgFrame m m' := by
  obtain ⟨⟨sp, hsp⟩, ⟨lp, hlp⟩⟩ := hM
  have hd := derFW_ok m a hD.base hD.der fab hfab
  by_cases hf : derFW m fab = 0
  · rw [lgW.arm1 n m fab base hf] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    refine ⟨?_, ⟨⟨sp, hsp⟩, ⟨lp, hlp⟩⟩, by decide, MemFrame.refl _ _ _⟩
    simp only [leafGuard, StateT.run_bind, derivedE_run, except_ok_bind, ← hd, hf]; rfl
  have h0 : ¬ rdW (m.arr64 CTL) 154 + 2 = 0 := fun h0 => by
    rw [lgW.abort1 n m fab base hf h0] at hb; cases hb
  rw [lgW.arm2 n m fab base hf h0] at hb
  have hc₁ : FlFrame m (mclearG flSch m) := (mclearG_frame flSch m).mono (by simp) (by simp)
  have hD₀ : ArenaD (mclearG flSch m) a := hc₁.arenaD hD
  have hS₀ := memoRG_clear flSch flSch_wf bmKey decU m sp hsp h0
  have hL₀ : LeafR (mclearG flSch m) 0 [] := LeafR.zero _
  cases hfl : flW n (mclearG flSch m) base 0 4000000000 with
  | none => rw [hfl, lgW.k_fl_go.none] at hb; cases hb
  | some q =>
    obtain ⟨k, m₁⟩ := q
    obtain ⟨bl, seen', ha₁, hS₁, hL₁, hf₁⟩ := (flGoOK n).1 _ _ a ∅ [] base 0 4000000000 k hD₀ hS₀ hL₀ hbase hfl
    rw [coreWalkFuel_toNat] at ha₁
    have h1 : ¬ rdW (m₁.arr64 CTL) 156 + 2 = 0 := fun h1 => by
      rw [hfl, lgW.k_fl_go.abort1 n fab k m₁ h1] at hb; cases hb
    rw [hfl, lgW.k_fl_go.arm1 n fab k m₁ h1] at hb
    have hf01 : FlFrame m m₁ := hc₁.trans hf₁
    have hlp₁ : MemoRG lsbSch bmKey decBW m₁ lp :=
      memoRG_frame lsbSch lsbSch_wf bmKey decBW _ _ (by decide) (by decide) m m₁ hf01 lp hlp
    have hc₂ : LsbFrame m₁ (mclearG lsbSch m₁) := (mclearG_frame lsbSch m₁).mono (by simp) (by simp)
    have hD₁ : ArenaD m₁ a := hf01.arenaD hD
    have hD₂ : ArenaD (mclearG lsbSch m₁) a := hc₂.arenaD hD₁
    have hT₂ := memoRG_clear lsbSch lsbSch_wf bmKey decBW m₁ lp hlp₁ h1
    have hL₂ : LeafR (mclearG lsbSch m₁) k bl := hL₁.frame hc₂.lvs
    obtain ⟨memo', ha₂, hT', hle, hf₂⟩ := (lsbGoOK n).1 _ _ a ∅ bl fab k 4000000000 r hD₂ hT₂ hL₂ hfab hb
    rw [coreWalkFuel_toNat] at ha₂
    have hf12 : LsbFrame m₁ m' := hc₂.trans hf₂
    have hS' : MemoRG flSch bmKey decU m' seen' :=
      memoRG_frame flSch flSch_wf bmKey decU _ _ (by decide) (by decide) m₁ m' hf12 seen' hS₁
    refine ⟨?_, ⟨⟨seen', hS'⟩, ⟨memo', hT'⟩⟩, hle,
      (hf01.mono (by simp) (by simp)).trans (hf12.mono (by simp) (by simp))⟩
    have hf' : ((fvarOfData (a.store.derived (decE fab))).toNat == 0) = false := by
      rw [← hd]; simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; exact hf (UInt64.toNat_inj.mp (by simpa using e))
    simp only [leafGuard, fvarLeavesFast, StateT.run_bind, derivedE_run, except_ok_bind, hf',
      Bool.false_eq_true, ↓reduceIte, ha₁, StateT.run_pure]
    simp only [pure_bind, ha₂]
    rfl

end L.Arena
