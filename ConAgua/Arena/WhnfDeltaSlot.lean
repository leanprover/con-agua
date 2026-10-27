import ConAgua.Arena.WhnfDelta
import ConAgua.Arena.WhnfCoreSlot
import ConAgua.L.ModelGen

/-!
# The knot's `whnf` slot and the `whnf` loop

`whnf(mode, vis, d, e)` (`WhnfDelta.lean`) refines the `whnf` slot of `coreKnot mode fe id (F + 1)`:
a stuck tag (`sort`/`fvar`/`lam`/`forallE`/`lit`, `whnfStuckTag`) answers `e` without touching the
memo or the store, a memo hit (`whnfC`, array 98, at the current generation) answers the entry, a
miss runs `whnf_loop` (the body, `whnfBody … (coreKnot … F)`), records it and answers it.

Exactly the pattern of `WhnfCoreSlot.lean`'s `whnf_core`/`whnf_core_loop`, but simpler: one memo
(no cheap/full split) and one callee (`whnf_step`, no spine arms). `whnf_step`'s own spec
(`WhnfStepSpec`, `WhnfDelta.lean`) is taken as a hypothesis at every L-fuel up to the knot's
(`WhnfStepUpTo`), since L has no fuel-monotonicity lemma (the same reason `KnotUpTo` wraps
`KnotOK`): a loop induction needs it at every fuel the loop's remaining steps run at, not just the
outer one.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Tags -/

/-- `whnfStuckTag` off the handle word: `sort` (2), `fvar` (1), `lam` (5), `forallE` (6), `lit` (8). -/
theorem whnfStuck_iff (e : Word) (he : HW e) :
    whnfStuckTag (decE e) =
      decide (e >>> 28 = 2 ∨ e >>> 28 = 1 ∨ e >>> 28 = 5 ∨ e >>> 28 = 6 ∨ e >>> 28 = 8) := by
  have h := shr28_lt e he
  simp only [whnfStuckTag, decE_tag e he, ETag.sort, ETag.fvar, ETag.lam, ETag.forallE, ETag.lit]
  rw [show (2 : UInt32) = (2 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (1 : UInt32) = (1 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (5 : UInt32) = (5 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (6 : UInt32) = (6 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (8 : UInt32) = (8 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  by_cases h2 : e >>> 28 = 2 <;> by_cases h1 : e >>> 28 = 1 <;> by_cases h5 : e >>> 28 = 5 <;>
    by_cases h6 : e >>> 28 = 6 <;> by_cases h8 : e >>> 28 = 8 <;> simp_all

/-! ## The model -/

/-- **The model of `whnf`**, the loop through its run. -/
def whnfW (p : Prog) (n : Nat) (m : Mem) (mode vis d e : Word) : Option (Word × Mem) :=
  if e >>> 28 = 2 ∨ e >>> 28 = 1 ∨ e >>> 28 = 5 ∨ e >>> 28 = 6 ∨ e >>> 28 = 8 then some (e, m)
  else memoSlotW whSch m e (ebKey mode) (callW p n "whnf_loop" [mode, vis, d, e] m)

theorem whnfW_stuck (p : Prog) (n : Nat) (m : Mem) (mode vis d e : Word)
    (h : e >>> 28 = 2 ∨ e >>> 28 = 1 ∨ e >>> 28 = 5 ∨ e >>> 28 = 6 ∨ e >>> 28 = 8) :
    whnfW p n m mode vis d e = some (e, m) := by
  unfold whnfW; rw [ite_eq_left h]

theorem whnfW_run (p : Prog) (n : Nat) (m : Mem) (mode vis d e : Word)
    (h : ¬ (e >>> 28 = 2 ∨ e >>> 28 = 1 ∨ e >>> 28 = 5 ∨ e >>> 28 = 6 ∨ e >>> 28 = 8)) :
    whnfW p n m mode vis d e =
      memoSlotW whSch m e (ebKey mode) (callW p n "whnf_loop" [mode, vis, d, e] m) := by
  unfold whnfW; rw [ite_eq_right h]

/-! ## The L spec for `whnf` -/

section spec
variable (p : Prog) (hp : WhnfDeltaProg p)

include hp in
theorem whnf_spec (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ whnfW p n s₀.mem mode vis d e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.whnf]
  simp only [callFn, whnfL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec whSch p _ hp.whFind n, memoPutG_spec whSch p _ hp.whPut n,
      callW_spec p n "whnf_loop"] <;>
    finish [whnfW_stuck, whnfW_run, memoSlotW_hit, memoSlotW_miss, mvG, ebKey]

end spec

/-! ## The relation across the `whnf` memo's `find; put` -/

/-- A memo's relation across a write of one other core memo (array `A`, stamp word `C`). -/
theorem MemoRV.frame1 {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey κ}
    {VR : Mem → Word → ν → Prop} {m m' : Mem} {mp : Std.HashMap κ ν} {A : ArrId} {C : Word}
    (hf : MemFrame [A] [C] m m') (h : MemoRV S K VR m mp)
    (hV : ∀ w v, VR m w v → VR m' w v := by exact fun _ _ h => h)
    (hS : S.WF := by exact coreSch_wf _ _ (by decide) (by decide)) (hA : S.arr ≠ A := by decide)
    (hC : S.cs ≠ C := by decide) : MemoRV S K VR m' mp :=
  memoRV_frame S hS K VR [A] [C] (by simpa using hA) (by simpa using hC) m m' hf hV mp h

/-- A mode memo's relation across a write of one other core memo. -/
theorem ModeR.frame1 {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
    {VR : Mem → Word → ν → Prop} {m m' : Mem} {M : Std.HashMap (κ × Word) ν} {eb : Word}
    {t te : Std.HashMap κ ν} {A : ArrId} {C : Word} (hf : MemFrame [A] [C] m m')
    (h : ModeR S K VR m M eb t te) (hV : VConst VR := by exact fun _ _ _ _ h => h)
    (hS : S.WF := by exact coreSch_wf _ _ (by decide) (by decide)) (hA : S.arr ≠ A := by decide)
    (hC : S.cs ≠ C := by decide) : ModeR S K VR m' M eb t te :=
  h.frame hS hV (by simpa using hA) (by simpa using hC) hf

/-- **`CoreS` across a write of one core memo** (array `A` and stamp word `C` in 96‥127), the core
tier at the new caches and maps given (the readback caches unchanged). -/
theorem CoreS.set_core {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M M' : ModeMaps} {eb : Word} {c : Caches} {A : ArrId} {C : Word}
    (hS : CoreS dn m a vis fe M eb) (hf : MemFrame [A] [C] m m') (hcore : CoreRM m' c M' eb)
    (h1 : c.readLC = a.caches.readLC) (h2 : c.readLsC = a.caches.readLsC)
    (h3 : c.readNC = a.caches.readNC) (hA : 96 ≤ A ∧ A < 128 := by decide)
    (hC : 96 ≤ C.toNat ∧ C.toNat < 128 := by decide) :
    CoreS dn m' { a with caches := c } vis fe M' eb ∧ StackKept m m' := by
  have nA : ∀ b : ArrId, (b < 96 ∨ 128 ≤ b) → b ∉ [A] := fun b hb h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; simp only [ArrId] at hA hb; omega
  have nC : ∀ x : Word, (x.toNat < 96 ∨ 128 ≤ x.toNat) → x ∉ [C] := fun x hx h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; omega
  have gA : ∀ b ∈ [A], 64 ≤ b ∧ b < 256 := fun b h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; simp only [ArrId] at hA ⊢; omega
  have gC : ∀ x ∈ [C], 64 ≤ x.toNat := fun x h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; omega
  have eA : AvoidA 129 144 [A] := fun b h => .inl (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; simp only [ArrId] at hA ⊢; omega)
  have eA2 : AvoidA 385 388 [A] := fun b h => .inl (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; simp only [ArrId] at hA ⊢; omega)
  have eC : AvoidC 128 136 [C] := fun x h => .inl (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; omega)
  have lf : LvlFree [C] := fun x hx => nC _ (by
    simp only [lvlCtlW, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [A] [C] gA gC m m' hf a hS.arena.1),
      DerR.of_store _ _ _ (DerR.frameM [A] [C] m m' hf
        (fun b hb => by have := gA b hb; simp only [ArrId] at this ⊢; omega) a hS.arena.2) rfl⟩,
      hcore, hS.pins.congr (hf.1 PINS (nA _ (by decide)) (by decide)),
      hS.env.frame eA eC hf eA2,
      fun h l e => hS.readL h l (h1 ▸ e), fun h l e => hS.readLs h l (h2 ▸ e), hS.nwf,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn,
      hS.memos.frame hf ⟨nA _ (by decide), nA _ (by decide)⟩ ⟨nC _ (by decide), nC _ (by decide)⟩
        ⟨nA _ (by decide), nA _ (by decide), nA _ (by decide)⟩
        ⟨nC _ (by decide), nC _ (by decide), nC _ (by decide)⟩
        ⟨nA _ (by decide), nA _ (by decide), nA _ (by decide)⟩
        ⟨nC _ (by decide), nC _ (by decide), nC _ (by decide)⟩, hf.2.2.1 145 ▸ hS.bstk,
      (hS.den.frameE (hf.1 EREC (nA _ (by decide)) (by decide))).caches rfl rfl h3,
      hS.mode.frame hf (nC _ (by decide)) (nC _ (by decide))⟩,
    StackKept.of_frame hf ⟨nA _ (by decide), nA _ (by decide), nA _ (by decide)⟩
      ⟨nC _ (by decide), nC _ (by decide), nC _ (by decide)⟩ lf (nA _ (by decide)) (nA _ (by decide))⟩

/-- `whnfC` gains an entry (at `whSch`: array 98, `CTL` 100/101). -/
theorem CoreS.set_wh {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (e x : Word)
    (he : HW e) (hx : HW x) (hs : msetG whSch m e (genW 0 eb) x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        whnfC := a.caches.whnfC.insert (decE e) (decE x) } } vis fe
      { M with wh := M.wh.insert (decE e, eb) (decE x) } eb ∧ StackKept m m' := by
  have hf : MemFrame [98] [101] m m' := msetG_frame whSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  have c := hS.core
  exact hS.set_core hf ⟨c.wc.frame1 hf, c.wk.frame1 hf,
    c.wh.setE (coreSch_wf _ _ (by decide) (by decide)) c.eb1 e x he hx m' hs, c.inf.frame1 hf,
    c.io.frame1 hf, c.de.frame1 hf, c.eb1, c.ct.frame1 hf, c.cv.frame1 hf, c.rr.frame1 hf,
    c.lq.frame1 hf, c.lsq.frame1 hf⟩ rfl rfl rfl

/-- `Kept0` across an insert in the eager bank `eb ≠ 0`. -/
theorem Kept0.insert {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] {M M' : Std.HashMap (κ × Word) ν}
    {eb : Word} (h : Kept0 M M') (h0 : eb ≠ 0) (k : κ) (v : ν) : Kept0 M (M'.insert (k, eb) v) :=
  fun k' => by
    rw [Std.HashMap.getElem?_insert]
    have : ¬ ((k, eb) == (k', (0 : Word))) = true := by simp [h0]
    simp only [this, Bool.false_eq_true, ↓reduceIte]; exact h k'

/-- `KeptAll` across a `whnf` memo insert. -/
theorem KeptAll.wh {M M' : ModeMaps} {eb : Word} (h : KeptAll M M' eb) (k : EIdx) (v : EIdx) :
    KeptAll M { M' with wh := M'.wh.insert (k, eb) v } eb := fun h0 =>
  let ⟨a1, b1, c1, d1, e1, f1⟩ := h h0; ⟨a1, b1, c1.insert h0 k v, d1, e1, f1⟩

/-! ## The twin's `whnf` slot -/

section twin
variable (mode : ConLeche.CheckMode) (fe : IFEnv) (F : Nat) (d : Nat) (e : EIdx) (a : AState)

theorem knot_whnf_stuck (h : whnfStuckTag e = true) :
    ((coreKnot mode fe id (F + 1)).whnf d e).run a = .ok (e, a) := by
  simp [coreKnot, h]; rfl

theorem knot_whnf_hit (h : whnfStuckTag e = false) (x : EIdx)
    (hm : a.caches.whnfC[e]? = some x) :
    ((coreKnot mode fe id (F + 1)).whnf d e).run a = .ok (x, a) := by
  simp [coreKnot, h, hm]; rfl

theorem knot_whnf_miss (h : whnfStuckTag e = false)
    (hm : a.caches.whnfC[e]? = none) (x : EIdx) (a₁ : AState)
    (hb : (whnfBody (coreKnot mode fe id F) fe d e).run a = .ok (x, a₁)) :
    ((coreKnot mode fe id (F + 1)).whnf d e).run a =
      .ok (x, { a₁ with caches := { a₁.caches with
        whnfC := a₁.caches.whnfC.insert e x } }) := by
  simp [coreKnot, h, hm, StateT.run_bind, hb, whnfSet]; rfl

end twin

/-! ## The loop -/

/-- **`whnf_loop` is its model `whnfLoopW`** (generated; the loop is `whnfLoopW.loop1`: each
iteration is a run of `whnf_step` (`callW`), done on `(0, v)`, continuing on `(1, e')`). -/
l_model whnfLoop_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.whnfLoop ↦ whnfLoopW]
  specs [callW_spec p n "whnf_step"]
  grind [arena_grind] simp []

/-! ## The loop's twin runs -/

theorem whnfLoop_done (r : CoreFnsA) (fe : IFEnv) (d K : Nat) (e v : EIdx) (a a₁ : AState)
    (hs : (whnfStep r fe d e).run a = .ok (.done v, a₁)) :
    (whnfLoop r fe d (K + 1) e).run a = .ok (v, a₁) := by
  simp only [whnfLoop, StateT.run_bind, hs, except_ok_bind]; rfl

theorem whnfLoop_cont (r : CoreFnsA) (fe : IFEnv) (d K : Nat) (e e' : EIdx) (a a₁ : AState)
    (hs : (whnfStep r fe d e).run a = .ok (.cont e', a₁)) :
    (whnfLoop r fe d (K + 1) e).run a = (whnfLoop r fe d K e').run a₁ := by
  simp only [whnfLoop, StateT.run_bind, hs, except_ok_bind]

/-! ## `whnf_step`'s spec at every fuel up to `n` -/

/-- `whnf_step`'s spec at every L-fuel up to `n`: the family a loop induction needs (L has no
fuel-monotonicity lemma, the same reason `KnotUpTo` wraps `KnotOK`). -/
def WhnfStepUpTo (p : Prog) (n : Nat) : Prop := ∀ j, j ≤ n → WhnfStepSpec p j

/-- **The model of the loop refines `whnfLoop` at every twin loop fuel `K ≥ k`.** -/
theorem whnfLoopW_ok (p : Prog) (N : Nat) (hk : KnotUpTo p N) (hws : WhnfStepUpTo p N) (F : Nat)
    (hF : N ≤ F) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d : Word)
    (hmode : mode < 4) :
    ∀ k, k ≤ N + 1 → ∀ K, k ≤ K → ∀ (m m' : Mem) (a : AState) (MM : ModeMaps) (eb e v : Word),
      CoreS dn m a vis fe MM eb → eb = (mode >>> 1) &&& 1 → HW e →
      whnfLoopW.loop1 p k m mode vis d e = some (v, m') →
      CoreRef (whnfLoop (coreKnot (decMode mode) fe id F) fe d.toNat K (decE e)) a decH dn m vis fe
        MM eb [v] m' := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [whnfLoopW.loop1] at h
  | succ k ih =>
    intro hkn K hK m m' a MM eb e v hS heb he h
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [whnfLoopW.loop1.arm1 (hc1 := rfl)] at h
    rcases hc : callW p k "whnf_step" [mode, vis, d, e] m with _ | ⟨r, m₁⟩
    · rw [hc, whnfLoopW.k_whnf_step.none] at h; cases h
    rw [hc] at h
    have hstep := hws k (by omega) F ⟨m, Locals.init []⟩ a dn vis fe MM eb mode d e (by omega)
      ⟨hS, hmode, heb⟩ he (hk.mono (by omega))
    obtain ⟨hok, hA, hres, hrw⟩ := CoreSpec.of_callW hstep hc
    have hsr := AM.run_of_ok _ _ hok
    rw [hres] at hsr
    by_cases h0 : r.headD 0 = 0
    · rw [whnfLoopW.k_whnf_step.arm1 (hc1 := h0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      simp only [decStep, h0, ↓reduceIte] at hsr
      have hrun := whnfLoop_done (coreKnot (decMode mode) fe id F) fe d.toNat K' (decE e) _ a _ hsr
      obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
      exact ⟨hok', hst' ▸ hA, hres', hrw.2⟩
    · rw [whnfLoopW.k_whnf_step.arm2 (hc1 := h0)] at h
      simp only [decStep, h0, ↓reduceIte] at hsr
      have hrun := whnfLoop_cont (coreKnot (decMode mode) fe id F) fe d.toNat K' (decE e) _ a _ hsr
      obtain ⟨M', hS₁, hK₁, hSt₁⟩ := hA
      obtain ⟨hok₂, hA₂, hres₂, hrw₂⟩ := ih (by omega) K' (by omega) m₁ m' _ M' eb _ v hS₁ heb hrw.2 h
      rw [AM.run_of_ok _ _ hok₂] at hrun
      obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
      refine ⟨hok', ?_, hres'.trans hres₂, hrw₂⟩
      rw [hst']
      exact CoreAfter.comp hK₁ hSt₁ hA₂

/-! ## `whnf_loop` refines `whnfLoop` -/

section loopRef
variable (p : Prog) (hwd : WhnfDeltaProg p)

include hwd in
/-- **`whnf_loop` refines `whnfLoop`.** -/
@[refines ConRon.Arena.whnfBody]
theorem whnfLoop_refines (n : Nat) (hws : WhnfStepUpTo p n) : WhnfLoopSpec p n := by
  intro F K s₀ a₀ dn vis fe MM eb mode d e hF hK hs he hk
  cases n with
  | zero =>
    unfold CoreSpec
    rw [invoke_eq _ hwd.whnfLoop]
    simp only [callFn, whnfLoopL]
    vcgen [exec] <;> grind
  | succ n' =>
    apply L.M.triple_of_run
    intro s r s' hs0 hrun
    obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s0 => s0 = s₀) hs0 hrun
      (whnfLoop_spec p hwd (n' + 1) s₀ mode vis d e)
    subst hs0
    refine ⟨hloc, ?_⟩
    rw [whnfLoopW.arm1] at hW
    have hbr := whnfLoopW_ok p n' (hk.mono (by omega)) (fun j hj => hws j (by omega)) F (by omega)
      dn vis fe mode d hs.mode4
    exact hbr (n' + 1) (Nat.le_refl _) K hK s.mem s'.mem a₀ MM eb e (r.headD 0) hs.rel hs.eb_mode he
      hW

end loopRef

/-! ## `whnf` refines the knot's `whnf` slot -/

section slot
variable (p : Prog) (hwd : WhnfDeltaProg p)

include hwd in
/-- **`whnf` refines the knot's `whnf` slot**: `WhnfSlot p (n + 1)` (`WhnfBase.lean`), from
`whnf_loop`'s spec at L-fuel `n` (`WhnfLoopSpec`, taken as a hypothesis or from `whnfLoop_refines`
above) and `KnotUpTo p n`. -/
theorem whnf_refines (n : Nat) (hn : n ≤ 2 ^ 62) (hk : KnotUpTo p n) (hloop : WhnfLoopSpec p n) :
    WhnfSlot p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hs he
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (whnf_spec p hwd n s₀ mode vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hkey : ebKey mode = genW 0 eb := ebKey_eq mode eb hs.eb_mode
  by_cases hst : e >>> 28 = 2 ∨ e >>> 28 = 1 ∨ e >>> 28 = 5 ∨ e >>> 28 = 6 ∨ e >>> 28 = 8
  · rw [whnfW_stuck _ _ _ _ _ _ _ hst] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have ht : whnfStuckTag (decE e) = true := by rw [whnfStuck_iff e he]; simpa using hst
    obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _ (knot_whnf_stuck _ fe F' d.toNat _ a₀ ht)
    refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact he⟩
    rw [hst', ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
  have ht : whnfStuckTag (decE e) = false := by rw [whnfStuck_iff e he]; simpa using hst
  rw [whnfW_run _ _ _ _ _ _ _ hst, hkey] at hW
  unfold memoSlotW at hW
  obtain ⟨h0, hW⟩ := of_ite_none hW
  have hf := hS.core.wh.findE hS.core.eb1 e he h0
  by_cases h1 : (mfindG whSch s.mem e (genW 0 eb)).headD 0 ≠ 0
  · rw [ite_eq_left h1] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _
      (knot_whnf_hit _ fe F' d.toNat _ a₀ ht _ (hf.1 h1).1)
    refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact (hf.1 h1).2⟩
    rw [hst', ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
  rw [ite_eq_right h1] at hW
  have hmiss := hf.2 (by simpa using h1)
  rcases hcall : callW p n "whnf_loop" [mode, vis, d, e] s.mem with _ | ⟨r₁, m₁⟩ <;> simp only [hcall, reduceCtorEq] at hW
  have hbody : CoreSpec p n "whnf_loop" [mode, vis, d, e]
      (whnfBody (coreKnot (decMode mode) fe id F') fe d.toNat (decE e)) decH s a₀ dn vis fe MM eb :=
    hloop F' whnfLoopFuel s a₀ dn vis fe MM eb mode d e (by omega)
      (by simp only [whnfLoopFuel]; omega) hs he hk
  obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW hbody hcall
  rcases hset : msetG whSch m₁ e (genW 0 eb) (r₁.headD 0) with _ | m₂ <;> simp only [hset, reduceCtorEq] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hS₂, hSt₂⟩ := hS₁.set_wh e (r₁.headD 0) he hrw hset
  have hrun := knot_whnf_miss _ fe F' d.toNat _ a₀ ht hmiss _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok', ?_, by rw [hres', hres]; simp only [decH, hr],
    by unfold ResH; rw [← hr]; exact hrw⟩
  rw [hst', ← hm, hres]
  exact ⟨_, hS₂, hK₁.wh _ _, hSt₁.trans hSt₂⟩

end slot

end L.Arena
