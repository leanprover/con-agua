import ConAgua.Arena.InstLPWalkStep
import ConAgua.Arena.InstLPLevel2
import ConAgua.Arena.InstLPWalkGo
import ConAgua.Arena.InstLPWalkArms

/-!
# The `instLP` walk refines `instLPGo`: the arms

By induction on the L fuel (`ILWGoOK p n`: `lp_go` at fuel `n` refines `instLPGo` at the counter's
fuel), each compound arm at `n + 1` from the walk at `n`: the memo probe (`instLPGet`), the
children (the walk), the rebuild (`internRebuilt*`: the node itself when every child came back
equal, else the node maker, `InstLPWalkStep.lean`), the memo write (`instLPSet`). The dispatcher
is `InstLPWalkGo2.lean`.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- The walk's program: the level arms' and the interning callees'. -/
structure ILWAllProg (p : Prog) : Prop where
  lev : ILWLevProg p
  mkp : ILWMkProg p

theorem ilw_beq {x y : Word} (hx : HW x) (hy : HW y) : (decE x == decE y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · have : decE x ≠ decE y := fun e => h (decE_inj x y hx hy e)
    simp [h, this]

/-- **`lp_go` at L fuel `n` refines `instLPGo`** at the counter's fuel, under the walk's
invariants. -/
def ILWGoOK (p : Prog) (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb h ko kc vo vc fu : Word) (ks : List Name) (us : List LIdx) (vs : List Level)
    (rs : List Word),
    CoreS dn m a vis fe M eb → ILWMemo m a → ILWEnv m a ko kc vo vc ks us vs → HW h →
    callW p n "lp_go" [h, ko, kc, vo, vc, fu] m = some (rs, m') →
    ILWStep (instLPGo ks vs fu.toNat (decE h)) a dn m m' vis fe M eb (rs.headD 0)

section arms
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {eb : Word}

/-- A step that changes nothing. -/
theorem ILWStep.refl {T : AM EIdx} {a : AState} {m : Mem} {M : ModeMaps} {r : Word}
    (hT : T.run a = .ok (decE r, a)) (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a) (hr : HW r) :
    ILWStep T a dn m m vis fe M eb r :=
  ⟨a, hT, ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, hM, ILWGrow.refl a, hr⟩

/-- **The memo probe hits**: the stored value. -/
theorem ilw_hit {m : Mem} {a : AState} (hM : ILWMemo m a) (h : Word) (hh : HW h)
    (hr : mfindG lpSch m h 0 ≠ []) (hhit : (mfindG lpSch m h 0).headD 0 ≠ 0) :
    a.memos.instLPC[(decE h, 0)]? =
        some (decE (rdW (m.arr64 LPMEMO) ((mfindG lpSch m h 0).tail.headD 0 * 4 + 3))) ∧
      HW (rdW (m.arr64 LPMEMO) ((mfindG lpSch m h 0).tail.headD 0 * 4 + 3)) := by
  obtain ⟨v, hv, hvv, hvl⟩ := memoRV_hit lpSch lfKey VH m _ hM.lp h 0 hr hhit hh
  exact ⟨hv.trans (congrArg some hvv), hvl⟩

/-- **The memo probe misses.** -/
theorem ilw_miss {m : Mem} {a : AState} (hM : ILWMemo m a) (h : Word) (hh : HW h)
    (hr : mfindG lpSch m h 0 ≠ []) (hm : ¬ (mfindG lpSch m h 0).headD 0 ≠ 0) :
    a.memos.instLPC[(decE h, 0)]? = none :=
  memoRV_miss lpSch lfKey VH m _ hM.lp h 0 hh hr (by simpa using hm)

/-- **The memo write** (`find; put` of `instLPC`): `instLPSet`. -/
theorem ilw_set {m m' : Mem} {a : AState} {M : ModeMaps} (hS : CoreS dn m a vis fe M eb)
    (hM : ILWMemo m a) (h r : Word) (hh : HW h) (hr : HW r) (hs : msetG lpSch m h 0 r = some m') :
    CoreS dn m' { a with memos := { a.memos with
        instLPC := a.memos.instLPC.insert (decE h, 0) (decE r) } } vis fe M eb ∧ StackKept m m' ∧
      ILWMemo m' { a with memos := { a.memos with
        instLPC := a.memos.instLPC.insert (decE h, 0) (decE r) } } := by
  have hf := msetG_frame lpSch lpSch_wf m m' h 0 r hs
  have hf' : MemFrame [lpSch.arr] [lpSch.cs, lpSch.cs + 1] m m' := hf.mono (by simp) (by simp)
  obtain ⟨hS', hk⟩ := CoreS.frameLP lpSch (.inl rfl) hS hf'
    (hS.memos.frameLP hf' (hM.setLP h r hh hr hs).lpMemos (by decide) (by simp [lpSch, lplSch, lplsSch]))
  exact ⟨hS'.lpMemos _ a.memos.instLPLC a.memos.instLPLsC, hk, hM.setLP h r hh hr hs⟩

/-- `internRebuilt*`: the node itself when every child came back equal (`c`), else the interning. -/
def ilwRbT (c : Bool) (h : EIdx) (x : AM EIdx) : AM EIdx := if c then pure h else x

/-- An arm of the twin's walk: the memo probe, else the body and the memo write. -/
def ilwArmT (h : EIdx) (body : AM EIdx) : AM EIdx := do
  match ← instLPGet (h, 0) with
  | some r => pure r
  | none => do
    let r ← body
    instLPSet (h, 0) r
    pure r

/-- **An arm from its body**: the probe hits (the stored value) or misses, then the body's step and
the memo write. -/
theorem ilw_arm {m m' : Mem} {a : AState} {M : ModeMaps} {h r : Word} {body : AM EIdx}
    {Y : Option (Word × Mem)}
    (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a) (hh : HW h)
    (hW : ilwProbe m h (ilwSetK h Y) = some (r, m'))
    (hbody : ∀ r₃ m₃, a.memos.instLPC[(decE h, 0)]? = none → Y = some (r₃, m₃) →
      ILWStep body a dn m m₃ vis fe M eb r₃) :
    ILWStep (ilwArmT (decE h) body) a dn m m' vis fe M eb r := by
  unfold ilwProbe at hW
  by_cases hr0 : mfindG lpSch m h 0 = []
  · simp [hr0] at hW
  rw [if_neg hr0] at hW
  by_cases hh0 : (mfindG lpSch m h 0).headD 0 ≠ 0
  · rw [if_pos hh0] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨hget, hw⟩ := ilw_hit hM h hh hr0 hh0
    exact ILWStep.refl (by simp only [ilwArmT, StateT.run_bind, instLPGet_run, except_ok_bind, hget]; rfl)
      hS hM hw
  rw [if_neg hh0] at hW
  have hmiss := ilw_miss hM h hh hr0 hh0
  rcases hY : Y with _ | ⟨r₃, m₃⟩ <;> rw [hY] at hW
  · simp [ilwSetK] at hW
  rw [ilwSetK_some] at hW
  rcases h4 : msetG lpSch m₃ h 0 r₃ with _ | m₄ <;> rw [h4] at hW
  · cases hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨a₃, r3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hM₃, hg₃, hr⟩ := hbody r₃ m₃ hmiss hY
  obtain ⟨hS₄, hSt₄, hM₄⟩ := ilw_set hS₃ hM₃ h r₃ hh hr h4
  refine ⟨_, ?_, ⟨M₃, hS₄, hK₃, hSt₃.trans hSt₄⟩, hM₄, hg₃.trans (ILWGrow.of_lss rfl), hr⟩
  simp only [ilwArmT, StateT.run_bind, instLPGet_run, except_ok_bind, hmiss, r3, instLPSet_run]
  rfl

/-- A step's twin side up to its run. -/
theorem ILWStep.congr {T T' : AM EIdx} {a : AState} {m m' : Mem} {M : ModeMaps} {r : Word}
    (e : T.run a = T'.run a) (h : ILWStep T' a dn m m' vis fe M eb r) : ILWStep T a dn m m' vis fe M eb r := by
  obtain ⟨a', hr, rest⟩ := h
  exact ⟨a', e.trans hr, rest⟩

/-- **Two steps in a row.** -/
theorem ILWStep.bind {A : AM EIdx} {f : EIdx → AM EIdx} {a : AState} {m m₁ m₂ : Mem} {M : ModeMaps}
    {x y : Word} (h₁ : ILWStep A a dn m m₁ vis fe M eb x)
    (h₂ : ∀ a₁ M₁, A.run a = .ok (decE x, a₁) → CoreS dn m₁ a₁ vis fe M₁ eb → ILWMemo m₁ a₁ →
      ILWGrow a a₁ → StackKept m m₁ → HW x → ILWStep (f (decE x)) a₁ dn m₁ m₂ vis fe M₁ eb y) :
    ILWStep (A >>= f) a dn m m₂ vis fe M eb y := by
  obtain ⟨a₁, r1, ⟨M₁, hS₁, hK, hSt⟩, hM₁, hg, hx⟩ := h₁
  obtain ⟨a₂, r2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hM₂, hg₂, hy⟩ := h₂ a₁ M₁ r1 hS₁ hM₁ hg hSt hx
  exact ⟨a₂, by simp only [StateT.run_bind, r1, except_ok_bind]; exact r2,
    ⟨M₂, hS₂, hK.trans hK₂, hSt.trans hSt₂⟩, hM₂, hg.trans hg₂, hy⟩

/-- **A rebuild**: `h` when every child came back equal (`hsame`), else the node maker's step. -/
theorem ilw_rebuild {c : Bool} {I : AM EIdx} {a : AState} {m m' : Mem} {M : ModeMaps} {h r : Word}
    {Y : Option (Word × Mem)} {Yn : Option (List Word × Mem)}
    (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a) (hh : HW h)
    (hY : Y = if c then some (h, m) else ilwChk Yn) (hYr : Y = some (r, m'))
    (hnew : c = false → ∀ zs, Yn = some (zs, m') → HW (zs.headD 0) →
      ILWStep I a dn m m' vis fe M eb (zs.headD 0)) :
    ILWStep (ilwRbT c (decE h) I) a dn m m' vis fe M eb r := by
  cases c with
  | true =>
    rw [hYr] at hY; simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hY
    obtain ⟨rfl, rfl⟩ := hY
    exact ILWStep.refl rfl hS hM hh
  | false =>
    show ILWStep I _ _ _ _ _ _ _ _ _
    rw [hYr] at hY; simp only [Bool.false_eq_true, ↓reduceIte] at hY
    rcases h5 : Yn with _ | ⟨zs, m₅⟩ <;> simp only [h5, ilwChk, reduceCtorEq] at hY
    by_cases hb : 4294967296 ≤ zs.headD 0
    · rw [if_pos hb] at hY; cases hY
    rw [if_neg hb] at hY
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hY)
    have hz : HW (zs.headD 0) := by
      unfold HW; have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hb); simpa using this
    exact hnew rfl zs h5 hz

end arms

end L.Arena
