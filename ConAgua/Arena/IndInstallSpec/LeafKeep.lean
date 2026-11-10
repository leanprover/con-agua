module

public import ConAgua.Arena.IndInstallSpec.PartsAt
public import ConAgua.Arena.IndSumSpec.StructUsedHb
import ConAgua.Arena.IndPosSpec.MentionsAnyGo
public import ConAgua.Arena.LeafFrame
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndPos

@[expose] public section

/-!
# Memory properties across write sets with trusted leaves

The inductive arm's write-set facts (`Checker/IndArmClosed.lean`) leave out the callees whose own
closure writes a memo the arm carries: `struct_used_later` (the `hb` walk) and
`mentions_any_const` (the `mentions_any` walk). `closedAL p A C fs L` checks the rest; a property
`P` that every frame of `A`/`C` keeps then survives every call of `f ∈ fs` when every call of a
leaf keeps it (`callW_keepL`, through `invoke_frameL`).

The leaves' own facts, at any arguments and fuel: `mentions_any_const` keeps a well-formed
`mentions_any` memo (`maGoW_keep`: every key it stores is a handle below `2^32`, its last act is a
clear; `maLeaf_keep`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## A property kept by a write set with leaves -/

section keep
variable {p : Prog} {A : List TieredArray} {C : List Word} {fs L : List FnName} {P : Mem → Prop}

/-- A property every frame of `A`/`C` keeps, as a frame relation. -/
theorem keep_wframe (hP : ∀ m m', MemFrame A C m m' → P m → P m') :
    WFrame CTL A C (fun m₀ m => P m₀ → P m) where
  refl _ h := h
  st64 m₀ m a i v h ha h0 := by
    rcases ha with ⟨hc, ha⟩ | ⟨rfl, hi⟩
    · exact hP _ _ ((MemFrame.set64 m a hc i v).mono (by simpa using ha) (by simp)) (h h0)
    · exact hP _ _ ((MemFrame.setCtl m i v).mono (by simp) (by simpa using hi)) (h h0)
  setG _ m g v h h0 :=
    hP _ _ ((⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩ : MemFrame [] [] m (m.setG g v)).mono
      (by simp) (by simp)) (h h0)

/-- A function whose every returning call keeps `P`, as the triple `invoke_frameL` takes. -/
theorem keep_leaf {g : FnName}
    (hg : ∀ n vs m r m', callW p n g vs m = some (r, m') → P m → P m') (n : Nat) (m₀ : Mem)
    (vs : List Word) :
    ⦃fun s => P m₀ → P s.mem⦄ invoke p (exec p n) g vs ⦃fun _ s => P m₀ → P s.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨-, hc⟩ := M.of_run (P := fun t => t = s) rfl hrun (callW_spec p n g vs s)
  exact fun h0 => hg _ _ _ _ _ hc (hs h0)

/-- **A call of a function of a set closed with leaves keeps `P`**, when every frame of the set's
write set keeps it and every call of a leaf does. -/
theorem callW_keepL (hcl : closedAL p A C fs L = true) (hP : ∀ m m', MemFrame A C m m' → P m → P m')
    (hL : ∀ g ∈ L, ∀ n vs m r m', callW p n g vs m = some (r, m') → P m → P m')
    {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word} {m' : Mem}
    (h : callW p n f vs m = some (r, m')) (h0 : P m) : P m' := by
  obtain ⟨s', hs', hk⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (invoke_frameL p hcl (keep_wframe hP) (fun g hg n m₀ vs => keep_leaf (hL g hg) n m₀ vs) n f hf vs _) h
  exact hs' ▸ hk h0

end keep

/-! ## `mentions_any_const` keeps its memo well formed, at any memory -/

/-- **The `mentions_any` walk keeps a well-formed memo**, at any memory (its node arms too). -/
theorem ma_keep (n : Nat) :
    (∀ m m' no nl f h r, maGoW n m no nl f h = some (r, m') → (∃ mp, maMR m mp) → ∃ mp, maMR m' mp) ∧
    (∀ m m' no nl f1 g x y z r, maNodeW n m no nl f1 g x y z = some (r, m') → (∃ mp, maMR m mp) →
      ∃ mp, maMR m' mp) := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ hh _ => by simp [maGoW] at hh,
      fun _ _ _ _ _ _ _ _ _ _ hh _ => by simp [maNodeW] at hh⟩
  | succ n ih =>
    obtain ⟨igo, inode⟩ := ih
    refine ⟨fun m m' no nl f h r hh hM => ?_, fun m m' no nl f1 g x y z r hh hM => ?_⟩
    · by_cases hf0 : f = 0
      · rw [maGoW_abort n m no nl f h hf0] at hh; cases hh
      rw [maGoW_view n m no nl f h hf0] at hh
      generalize hv : eViewW m h = v at hh
      by_cases hv0 : v = []
      · subst hv0; simp [maG1] at hh
      have hH : H h := eViewW_H (by rw [hv]; exact hv0)
      by_cases hg : v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8
      · rw [maG1_leaf n m no nl f h v hv0 hg] at hh
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh); exact hM
      by_cases h3 : v.headD 0 = 3
      · rw [maG1_const n m no nl f h v hv0 hg h3] at hh
        cases hc : containsW n m no nl (v.tail.headD 0) with
        | none => rw [hc] at hh; simp [maC] at hh
        | some b =>
          rw [hc, maC_some] at hh
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh); exact hM
      rw [maG1_node n m no nl f h v hv0 hg h3] at hh
      by_cases hfr : mfindG maSch m h 0 = []
      · rw [maG3_abort n m no nl f h v _ hfr] at hh; cases hh
      by_cases hhit : (mfindG maSch m h 0).headD 0 ≠ 0
      · rw [maG3_hit n m no nl f h v _ hfr hhit] at hh
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh); exact hM
      rw [maG3_miss n m no nl f h v _ hfr hhit] at hh
      rcases h2 : maNodeW n m no nl (f - 1) (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
        (v.tail.tail.tail.headD 0) with _ | ⟨r2, m2⟩
      · rw [h2] at hh; simp [maG4] at hh
      rw [h2, maG4_some] at hh
      obtain ⟨mp2, hM2⟩ := inode _ _ _ _ _ _ _ _ _ _ h2 hM
      cases hm : msetG maSch m2 h 0 r2 with
      | none => rw [hm] at hh; simp [maG5] at hh
      | some m3 =>
        rw [hm, maG5_some] at hh
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
        exact ⟨_, memoRG_set maSch maSch_wf bmKey (fun w : Word => w != 0) m2 mp2 hM2 h 0 r2
          ⟨hH, rfl⟩ m3 hm⟩
    · by_cases g1 : g = 1
      · rw [maNodeW_fvar n m no nl f1 g x y z g1] at hh; exact igo _ _ _ _ _ _ _ hh hM
      by_cases gb : g = 4 ∨ g = 5 ∨ g = 6
      · rw [maNodeW_bin n m no nl f1 g x y z gb] at hh
        rcases h1 : maGoW n m no nl f1 x with _ | ⟨b1, m1⟩
        · rw [h1] at hh; simp [maB1] at hh
        rw [h1, maB1_some] at hh
        rcases h2 : maGoW n m1 no nl f1 y with _ | ⟨b2, m2⟩
        · rw [h2] at hh; simp [maB2] at hh
        rw [h2, maB2_some] at hh
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
        exact igo _ _ _ _ _ _ _ h2 (igo _ _ _ _ _ _ _ h1 hM)
      by_cases g7 : g = 7
      · rw [maNodeW_let n m no nl f1 g x y z g7] at hh
        rcases h1 : maGoW n m no nl f1 x with _ | ⟨b1, m1⟩
        · rw [h1] at hh; simp [maL1] at hh
        rw [h1, maL1_some] at hh
        rcases h2 : maGoW n m1 no nl f1 y with _ | ⟨b2, m2⟩
        · rw [h2] at hh; simp [maL2] at hh
        rw [h2, maL2_some] at hh
        rcases h3 : maGoW n m2 no nl f1 z with _ | ⟨b3, m3⟩
        · rw [h3] at hh; simp [maL3] at hh
        rw [h3, maL3_some] at hh
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
        exact igo _ _ _ _ _ _ _ h3 (igo _ _ _ _ _ _ _ h2 (igo _ _ _ _ _ _ _ h1 hM))
      rw [maNodeW_proj n m no nl f1 g x y z g1 gb g7] at hh
      rcases h1 : maGoW n m no nl f1 z with _ | ⟨b1, m1⟩
      · rw [h1] at hh; simp [maP1] at hh
      rw [h1, maP1_some] at hh
      cases hc : containsW n m1 no nl x with
      | none => rw [hc] at hh; simp [maP2] at hh
      | some b2 =>
        rw [hc, maP2_some] at hh
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
        exact igo _ _ _ _ _ _ _ h1 hM

/-- **`mentions_any_const`'s model keeps a well-formed memo**, at any memory. -/
theorem maConstW_keep {n : Nat} {m m' : Mem} {no nl e r : Word} (h : maConstW n m no nl e = some (r, m'))
    (hM : ∃ mp, maMR m mp) : ∃ mp, maMR m' mp := by
  obtain ⟨mp, hM⟩ := hM
  by_cases h0 : rdW (m.arr64 CTL) maSch.cs + 2 = 0
  · simp [maConstW, h0] at h
  rw [maConstW_eq n m no nl e h0] at h
  rcases h1 : maGoW n (mclearG maSch m) no nl CWF e with _ | ⟨r1, m1⟩
  · rw [h1] at h; simp [maClrK] at h
  rw [h1] at h
  obtain ⟨mp1, hM1⟩ := (ma_keep n).1 _ _ _ _ _ _ _ h1
    ⟨_, memoRG_clear maSch maSch_wf bmKey _ m mp hM h0⟩
  by_cases h2 : rdW (m1.arr64 CTL) maSch.cs + 2 = 0
  · simp [maClrK, h2] at h
  rw [maClrK_some r1 m1 h2] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨_, memoRG_clear maSch maSch_wf bmKey _ m1 mp1 hM1 h2⟩

/-- `mentions_any_const`'s model at any argument list. -/
theorem mentionsAnyConst_specV {p : Prog} (hM : MaProg p) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "mentions_any_const" vs
    ⦃fun r s' => LocEq s' s₀ ∧
      maConstW n s₀.mem (vs.getD 0 0) (vs.getD 1 0) (vs.getD 2 0) = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (maGo_spec p hM.view hM.cont hM.find hM.put hM.go hM.node n).1
  unfold MaGoSpec at ih
  simp only [invoke_eq _ hM.ma, callFn, mentionsAnyConst]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      memoClearG_spec maSch p _ hM.clr n, ih] <;>
    finish [Locals.init]

/-- **`mentions_any_const` keeps a well-formed `mentions_any` memo**, at any arguments and fuel. -/
theorem maLeaf_keep {p : Prog} (hM : MaProg p) :
    ∀ n vs m r m', callW p n "mentions_any_const" vs m = some (r, m') →
      (∃ mp, maMR m mp) → ∃ mp, maMR m' mp := by
  intro n vs m r m' hc h0
  obtain ⟨s'', hm, -, hu⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (mentionsAnyConst_specV hM n _ vs) (callW_mono hc (Nat.le_add_right n 1))
  rw [hm] at hu
  exact maConstW_keep hu h0

end L.Ind

end
