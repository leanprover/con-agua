module

public import ConAgua.Arena.DefEqStuckTail
import ConAgua.Arena.DefEqMidLazy2
public import ConAgua.Arena.LdRd
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.DefEqMidLazy
public import ConAgua.Verdict.WhnfNatE
public import ConAgua.Arena.DefEqCtor

@[expose] public section

/-!
# `defeq_body` refines `defeqBody`; the knot's `defeq` slot one level up (lane `defeq`)

The callW pattern (`DefEqStuckTail.lean`): a word model of `defeq_body` (`DefEqModels.lean`) with
its callees through their runs (`dbW`), the L spec by `vcgen` + `simp_all`, the refinement from the
callees' specs (`is_bool_true`, `has_fvar`, `bool_true_shortcut`, `quick_defeq` twice, `prop_irrel`,
the cheap `whnf_core` slot twice, `lazy_delta_reduction`, `defeq_tail`), threaded through the twin's
`do` block by `coreRef_bind`. `DefeqBodySpec p n` (`KnotSlot.lean`) is then a theorem
(`defeqBody_refines`), and with `defeq_refines` the slot step `defeqSlot_step`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- What `defeq_body`'s spec needs of a program. -/
structure DefeqBodyProg (p : Prog) : Prop where
  stuck : StuckProg p
  iota : IotaProg' p
  lazy : LazyProg p
  knot : KnotProg p
  body : p.lookup "defeq_body" = some defeqBodyL
  lazyF : p.lookup "defeq_lazy" = some defeqLazyL
  ctor : CtorProg p

/-- The callees `defeq_body`'s refinement assumes. -/
structure DefeqBodyCallees (p : Prog) : Prop where
  stuck : StuckCallees p
  lazy : LazyCallees p

/-- **What `defeq_body`'s errors claim from**: the knot's slots, the verdict closure, and the whnf
family's claims its callees' refinements take (`reduce_nat`, `proof_irrel`, `defeq_lst`,
`reduce_proj_core`). -/
structure BodyG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  nv : closedNV p L.Checker.nvFns = true
  reduceNat : ReduceNatE p
  pirr : ProofIrrelWE p
  lst : DefeqLstWE p
  rpc : ReduceProjCoreE p

theorem BodyG.mono {p : Prog} {n n' : Nat} (h : BodyG p n) (hn : n' ≤ n) : BodyG p n' :=
  ⟨h.knot.mono hn, h.nv, h.reduceNat, h.pirr, h.lst, h.rpc⟩

/-! ## The twin side -/

/-- **`defeqLazy`**, copied with its tail as `defeqTailT` (`defeqLazy_eq`). -/
def defeqLazyT (mode : ConLeche.CheckMode) (eager : Bool) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (a b : EIdx) : AM Bool := do
  match ← quickDefEq mode r depth a b with
  | some v => pure v
  | none =>
  if ← propIrrel r fe depth a b then pure true else do
  let a' ← r.whnfCore true depth a
  let b' ← r.whnfCore true depth b
  match ← quickDefEq mode r depth a' b' with
  | some v => pure v
  | none =>
  match ← lazyDeltaReduction mode eager r fe depth defeqLoopFuel a' b' with
  | .verdict v => pure v
  | .unknown a₁ b₁ => defeqTailT mode r fe depth a₁ b₁

theorem defeqLazy_eq (mode : ConLeche.CheckMode) (eager : Bool) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (a b : EIdx) : defeqLazy mode eager r fe depth a b = defeqLazyT mode eager r fe depth a b := rfl

theorem depth_lt_of_shr (d : Word) (h : d >>> 63 = 0) : d.toNat < 2 ^ 63 := by
  have h' := congrArg UInt64.toNat h
  rw [UInt64.toNat_shiftRight] at h'
  simp only [UInt64.toNat_zero, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod,
    Nat.reducePow] at h'
  have := d.toNat_lt
  omega

/-! ## `defeq_lazy` -/

section body
variable (p : Prog) (hq : DefeqBodyProg p) (hc : DefeqBodyCallees p)

include hq hc in
/-- **`defeq_lazy` refines `defeqLazy`, both outcomes**: the errors are its callees'. -/
theorem dlz_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d x y : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hx : HW x) (hy : HW y)
    (hd : d.toNat < 2 ^ 63) :
    RefE (BodyG p n) (lazyE p n s₀.mem mode vis d x y)
      (defeqLazy (decMode mode) (decEager mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat
        (decE x) (decE y)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ n =>
  cases n with
  | zero => simp only [lazyE]; exact RefE.callE_zero fun _ => rfl
  | succ k =>
  simp only [lazyE]
  rw [defeqLazy_eq]
  unfold defeqLazyT
  have hS := hs.rel
  have hk' : KnotUpTo p k := hk.mono (by omega)
  have hK := hk (k + 1) (by omega)
  have hSP : ∀ {m : Mem} {st : AState} {M : ModeMaps}, CoreS dn m st vis fe M eb →
      SlotPre ⟨m, Locals.init []⟩ st dn vis fe M eb mode := fun h => ⟨h, hs.mode4, hs.eb_mode⟩
  have hQ := quickUpTo hq.lazy hc.lazy hk (k + 1) (by omega)
  refine RefE.bind_callE (fun _ => rfl) (hQ F s₀ a₀ dn vis fe M eb mode d x y
    (by omega) (by omega) hs hx hy hd) (fun (hG : BodyG p (k + 1 + 1)) => quickWEUpTo hq.lazy
      hc.lazy hk ⟨hG.knot, hG.nv⟩ (k + 1) (by omega) F s₀ a₀ dn vis fe M eb mode d x y
      (by omega) (by omega) hs hx hy hd)
    fun r₄ m₄ _ h₄ => RefE.after_core (w := id) h₄ fun M₄ hS₄ _ => ?_
  dsimp only [lazyE.k_quick_defeq]
  by_cases hq4 : r₄.headD 0 ≠ 0
  · rw [ite_eq_left hq4]
    simp only [decOB, ite_eq_right hq4]
    exact RefE.ret rfl (CorePost.ret hS₄ rfl h₄.resOk.2)
  rw [ite_eq_right hq4]
  simp only [decOB, ite_eq_left (show r₄.headD 0 = 0 by simpa using hq4)]
  refine RefE.bind_callE (fun _ => rfl) (propIrrel_refines p hq.stuck hc.stuck k hk' F ⟨m₄, Locals.init []⟩
    _ dn vis fe M₄ eb mode d x y (by omega) (by omega) (hSP hS₄) hx hy)
    (fun (hG : BodyG p (k + 1 + 1)) => RefE.coreSpecE (piE_spec p hq.stuck.propIrrel (k + 1)
      ⟨m₄, Locals.init []⟩ mode vis d x y) hG.nv ⟨hG.knot.mono (by omega), hG.pirr⟩
      (pi_ref p hc.stuck k hk' F ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode d x y (by omega)
        (by omega) (hSP hS₄) hx hy)) fun r₅ m₅ _ h₅ => RefE.after_core (w := id) h₅ fun M₅ hS₅ _ => ?_
  dsimp only [lazyE.k_prop_irrel]
  by_cases hp5 : r₅.headD 0 ≠ 0
  · rw [ite_eq_left hp5, L.Arena.decBool_true_of hp5]
    exact RefE.ret rfl (CorePost.ret hS₅ rfl hw1)
  rw [ite_eq_right hp5, L.Arena.decBool_false_of (by simpa using hp5)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine RefE.bind_callE (fun _ => rfl) (hK.whnfCore F ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode 1 d x
    (by omega) (by omega) (hSP hS₅) hx) (fun (hG : BodyG p (k + 1 + 1)) => (hG.knot (k + 1) (by omega)).whnfCore
      F ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode 1 d x (by omega) (by omega) (hSP hS₅) hx)
    fun r₆ m₆ _ h₆ => RefE.after_core (w := id) h₆ fun M₆ hS₆ _ => ?_
  dsimp only [lazyE.k_whnf_core]
  refine RefE.bind_callE (fun _ => rfl) (hK.whnfCore F ⟨m₆, Locals.init []⟩ _ dn vis fe M₆ eb mode 1 d y
    (by omega) (by omega) (hSP hS₆) hy) (fun (hG : BodyG p (k + 1 + 1)) => (hG.knot (k + 1) (by omega)).whnfCore
      F ⟨m₆, Locals.init []⟩ _ dn vis fe M₆ eb mode 1 d y (by omega) (by omega) (hSP hS₆) hy)
    fun r₇ m₇ _ h₇ => RefE.after_core (w := id) h₇ fun M₇ hS₇ _ => ?_
  dsimp only [lazyE.k_whnf_core_2]
  refine RefE.bind_callE (fun _ => rfl) (hQ F ⟨m₇, Locals.init []⟩ _ dn vis fe M₇ eb mode d _ _
    (by omega) (by omega) (hSP hS₇) h₆.resOk h₇.resOk hd) (fun (hG : BodyG p (k + 1 + 1)) => quickWEUpTo
      hq.lazy hc.lazy hk ⟨hG.knot, hG.nv⟩ (k + 1) (by omega) F ⟨m₇, Locals.init []⟩ _ dn vis fe M₇ eb mode
      d _ _ (by omega) (by omega) (hSP hS₇) h₆.resOk h₇.resOk hd)
    fun r₈ m₈ _ h₈ => RefE.after_core (w := id) h₈ fun M₈ hS₈ _ => ?_
  dsimp only [lazyE.k_quick_defeq_2]
  by_cases hq8 : r₈.headD 0 ≠ 0
  · rw [ite_eq_left hq8]
    simp only [decOB, ite_eq_right hq8]
    exact RefE.ret rfl (CorePost.ret hS₈ rfl h₈.resOk.2)
  rw [ite_eq_right hq8]
  simp only [decOB, ite_eq_left (show r₈.headD 0 = 0 by simpa using hq8)]
  refine RefE.bind_callE (fun _ => rfl) (lazyDeltaReduction_refines p hq.lazy hc.lazy k hk' F (by omega)
    (by omega) ⟨m₈, Locals.init []⟩ _ dn vis fe M₈ eb mode d _ _ (hSP hS₈) h₆.resOk h₇.resOk hd)
    (fun (hG : BodyG p (k + 1 + 1)) => RefE.coreSpecE (lazyDeltaReduction_specE p hq.lazy.red (k + 1)
      ⟨m₈, Locals.init []⟩ mode vis d _ _) trivial ⟨⟨hG.knot.mono (by omega), hG.nv⟩, hG.reduceNat⟩
      (lazyDeltaReduction_ref p hq.lazy hc.lazy k hk' F (by omega) (by omega) ⟨m₈, Locals.init []⟩ _
        dn vis fe M₈ eb mode d _ _ (hSP hS₈) h₆.resOk h₇.resOk hd))
    fun r₉ m₉ _ h₉ => RefE.after_core (w := id) h₉ fun M₉ hS₉ _ => ?_
  dsimp only [lazyE.k_lazy_delta_reduction]
  obtain ⟨g0, g1, g2⟩ := h₉.resOk
  by_cases l0 : r₉.headD 0 = 0
  · rw [ite_eq_left l0]
    simp only [decLR, ite_eq_left l0]
    exact RefE.ret rfl (CorePost.ret hS₉ rfl hw0)
  rw [ite_eq_right l0]
  by_cases l1 : r₉.headD 0 = 1
  · rw [ite_eq_left l1]
    simp only [decLR, ite_eq_right l0, ite_eq_left l1]
    exact RefE.ret rfl (CorePost.ret hS₉ rfl hw1)
  rw [ite_eq_right l1]
  simp only [decLR, ite_eq_right l0, ite_eq_right l1]
  rcases c10 : callE p (k + 1) "defeq_tail" [mode, vis, d, r₉.tail.headD 0, r₉.tail.tail.headD 0] m₉
    with e | ⟨r₁₀, m₁₀⟩
  · exact fun hG => RefE.run_err (dtE_spec p hq.stuck.defeqTail hq.stuck.projPair hq.stuck.ldpr
      hq.stuck.defeqStuck hq.stuck.stuckStr hq.stuck.stuckApp hq.stuck.stuckAppCong hq.stuck.stuckRest
      hq.stuck.stuckIrrel hq.stuck.toCertProg hq.stuck.etaCert
      hq.stuck.etaCertBody hq.stuck.etaCertTy (k + 1) ⟨m₉, Locals.init []⟩ mode vis d _ _) hG.nv
      ⟨⟨fun j hj F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd =>
          RefE.coreSpecE (ldsE_spec p hq.lazy.step hq.lazy.both hq.lazy.mid.tupa hq.lazy.left
            hq.lazy.right hq.lazy.same hq.lazy.unfold2 hq.lazy.mid.dq hq.lazy.spine.sp hq.lazy.spine.sp2
            hq.lazy.spine.cmp hq.lazy.spine.rev (j + 1) s₀ mode vis d a b) hG.nv
            ⟨hG.knot.mono (by omega), hG.nv⟩
            (lds_ref p hq.lazy hc.lazy j (hk'.mono hj) F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb
              hd),
        hG.knot.mono (by omega), hG.rpc⟩, hG.pirr, hG.lst⟩
      (dt_ref p hq.stuck hq.iota hc.stuck k hk' F ⟨m₉, Locals.init []⟩ _ dn vis fe M₉ eb mode d _ _
        (by omega) (by omega) (hSP hS₉) g1 g2 hd) c10
  obtain ⟨hrun, hP⟩ := (CoreSpec.of_callW (s₀ := ⟨m₉, Locals.init []⟩)
    (defeqTail_refines p hq.stuck hq.iota hc.stuck k hk' F _ _ dn vis fe M₉ eb mode d _ _
      (by omega) (by omega) (hSP hS₉) g1 g2 hd) (callW_of_callE c10)).post
  simp only [lazyE.k_defeq_tail]
  exact RefE.ret hrun ⟨hP.after, hP.res, hP.valid⟩

include hq hc in
/-- **`defeq_lazy` refines `defeqLazy`** (`dlz_ref`'s ok half). -/
@[refines ConRon.Arena.defeqLazy]
theorem defeqLazy_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d x y : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hx : HW x) (hy : HW y)
    (hd : d.toNat < 2 ^ 63) :
    CoreSpec p n "defeq_lazy" [mode, vis, d, x, y]
      (defeqLazy (decMode mode) (decEager mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat
        (decE x) (decE y)) decBool s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (lazyE_spec p hq.lazyF n s₀ mode vis d x y)
    (dlz_ref p hq hc n hk F s₀ a₀ dn vis fe M eb mode d x y hF hn hs hx hy hd)

include hq hc in
/-- **A tail call of `defeq_lazy`**, both outcomes: the caller's continuation passes its error on
and re-lists its result. -/
theorem lazy_tail (k : Nat) (hk : KnotUpTo p (k + 1)) (F : Nat) (m : Mem) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d x y : Word)
    (hF : k + 1 ≤ F) (hn : k + 1 ≤ 2 ^ 62) (hs : SlotPre ⟨m, Locals.init []⟩ a₀ dn vis fe M eb mode)
    (hx : HW x) (hy : HW y) (hd : d.toNat < 2 ^ 63)
    {K : Except Err (List Word × Mem) → Except Err (List Word × Mem)} (hK : ∀ e, K (.error e) = .error e)
    (hK' : ∀ r m', K (.ok (r, m')) = .ok ([r.headD 0], m')) :
    RefE (BodyG p (k + 1 + 1)) (K (callE p (k + 1) "defeq_lazy" [mode, vis, d, x, y] m))
      (defeqLazy (decMode mode) (decEager mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat
        (decE x) (decE y)) a₀
      (CorePost decBool dn m vis fe M eb ResH) := by
  rcases c : callE p (k + 1) "defeq_lazy" [mode, vis, d, x, y] m with e | ⟨r, m'⟩
  · rw [hK]
    exact fun hG => RefE.run_err (lazyE_spec p hq.lazyF (k + 1) ⟨m, Locals.init []⟩ mode vis d x y) hG.nv
      (hG.mono (by omega)) (dlz_ref p hq hc (k + 1) hk F ⟨m, Locals.init []⟩ a₀ dn vis fe M eb mode d x y hF hn hs
        hx hy hd) c
  rw [hK']
  obtain ⟨hrun, hP⟩ := (CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
    (defeqLazy_refines p hq hc (k + 1) hk F _ a₀ dn vis fe M eb mode d x y hF hn hs hx hy hd)
    (callW_of_callE c)).post
  exact RefE.ret hrun ⟨hP.after, hP.res, hP.valid⟩

/-! ## `defeq_body` -/

include hq hc in
/-- **`defeq_body` refines `defeqBody`, both outcomes**: the fast path, the depth guard, the
constructor shortcut (`ctf_ref`, the `whnf` slot, `cha_ref`), `defeq_lazy` (`lazy_tail`). -/
theorem body_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d x y : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hx : HW x) (hy : HW y) :
    RefE (BodyG p n) (bodyE p n s₀.mem mode vis d x y)
      (defeqBody (decMode mode) (decEager mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE x) (decE y)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ n =>
  have hS := hs.rel
  unfold defeqBody
  simp only [bodyE]
  rw [L.Arena.decE_beq_eq _ _ hx hy]
  by_cases hxy : x = y
  · rw [ite_eq_left hxy]
    simp only [hxy, decide_true, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS rfl hw1)
  rw [ite_eq_right hxy]
  simp only [hxy, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine RefE.abort0 (by rfl) fun hd0 => ?_
  have hd := depth_lt_of_shr d (by simpa using hd0)
  cases n with
  | zero => exact RefE.callE_zero fun _ => rfl
  | succ k =>
  have hk' : KnotUpTo p (k + 1) := hk.mono (by omega)
  have hK := hk (k + 1) (by omega)
  have hSP : ∀ {m : Mem} {st : AState} {M : ModeMaps}, CoreS dn m st vis fe M eb →
      SlotPre ⟨m, Locals.init []⟩ st dn vis fe M eb mode := fun h => ⟨h, hs.mode4, hs.eb_mode⟩
  have heager := L.Arena.mode_eager_bit mode hs.mode4
  -- the readers' specs at the call's memory
  have ctfS : ∀ (m : Mem) (st : AState) (M : ModeMaps) (o e : Word), CoreS dn m st vis fe M eb → HW o →
      HW e → CoreSpec p (k + 1) "ctor_target_for" [mode, vis, o, e]
        (ctorTargetFor fe (decEager mode) (decE o) (decE e)) decCT ⟨m, Locals.init []⟩ st dn vis fe M eb
        ResCT := fun m st M o e h ho he =>
    RefE.coreSpec (G := True) (ctfE_spec p hq.ctor.ctf hq.ctor.ct (k + 1) ⟨m, Locals.init []⟩ mode vis o e)
      (ctf_ref p hq.ctor hc.stuck.defeq.hasFvar (k + 1) m st dn vis fe M eb mode o e _ heager h ho he)
  have ctfE' : ∀ (m : Mem) (st : AState) (M : ModeMaps) (o e : Word), CoreS dn m st vis fe M eb → HW o →
      HW e → BodyG p (k + 1 + 1) → CoreSpecE p (k + 1) "ctor_target_for" [mode, vis, o, e]
        (ctorTargetFor fe (decEager mode) (decE o) (decE e)) ⟨m, Locals.init []⟩ st :=
    fun m st M o e h ho he hG =>
    RefE.coreSpecE (ctfE_spec p hq.ctor.ctf hq.ctor.ct (k + 1) ⟨m, Locals.init []⟩ mode vis o e) hG.nv trivial
      (ctf_ref (G := True) p hq.ctor hc.stuck.defeq.hasFvar (k + 1) m st dn vis fe M eb mode o e _ heager h ho he)
  have chaS : ∀ (m : Mem) (st : AState) (M : ModeMaps) (c w : Word), CoreS dn m st vis fe M eb →
      c.toNat < 2 ^ 32 → HW w → CoreSpec p (k + 1) "ctor_head_against" [vis, c, w]
        (ctorHeadAgainst fe (decI c) (decE w)) decCHA ⟨m, Locals.init []⟩ st dn vis fe M eb
        (fun _ => True) := fun m st M c w h hcw hw =>
    RefE.coreSpec (G := True) (chaE_spec p hq.ctor.cha (k + 1) ⟨m, Locals.init []⟩ vis c w)
      (cha_ref p hq.ctor (k + 1) m st dn vis fe M eb c w h hcw hw)
  have chaE' : ∀ (m : Mem) (st : AState) (M : ModeMaps) (c w : Word), CoreS dn m st vis fe M eb →
      c.toNat < 2 ^ 32 → HW w → BodyG p (k + 1 + 1) → CoreSpecE p (k + 1) "ctor_head_against" [vis, c, w]
        (ctorHeadAgainst fe (decI c) (decE w)) ⟨m, Locals.init []⟩ st := fun m st M c w h hcw hw hG =>
    RefE.coreSpecE (chaE_spec p hq.ctor.cha (k + 1) ⟨m, Locals.init []⟩ vis c w) hG.nv trivial
      (cha_ref (G := True) p hq.ctor (k + 1) m st dn vis fe M eb c w h hcw hw)
  refine RefE.bind_callE (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl) (ctfS s₀.mem a₀ M x y hS hx hy) (ctfE' s₀.mem a₀ M x y hS hx hy)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [bodyE.k_ctor_target_for]
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_right (fun h => h h0), show decCT r₁ = none by unfold decCT; exact ite_eq_left h0]
    refine RefE.bind_callE (s₀ := ⟨m₁, Locals.init []⟩) (fun _ => rfl) (ctfS m₁ _ M₁ y x hS₁ hy hx)
      (ctfE' m₁ _ M₁ y x hS₁ hy hx) fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
    dsimp only [bodyE.k_ctor_target_for_2]
    by_cases g0 : r₂.headD 0 = 0
    · rw [ite_eq_right (fun h => h g0), show decCT r₂ = none by unfold decCT; exact ite_eq_left g0]
      exact lazy_tail p hq hc k hk' F m₂ _ dn vis fe M₂ eb mode d x y (by omega) (by omega) (hSP hS₂) hx hy hd
        (fun _ => rfl) (fun _ _ => rfl)
    rw [ite_eq_left g0, show decCT r₂ = some (decI (r₂.tail.headD 0)) by unfold decCT; exact ite_eq_right g0]
    dsimp only
    refine RefE.bind_callE (s₀ := ⟨m₂, Locals.init []⟩) (fun _ => rfl)
      (hK.whnf F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d y (by omega) (by omega) (hSP hS₂) hy)
      (fun (hG : BodyG p (k + 1 + 1)) => (hG.knot (k + 1) (by omega)).whnf F ⟨m₂, Locals.init []⟩ _ dn vis fe
        M₂ eb mode d y (by omega) (by omega) (hSP hS₂) hy)
      fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
    dsimp only [bodyE.k_whnf_2]
    refine RefE.bind_callE (s₀ := ⟨m₃, Locals.init []⟩) (fun _ => rfl)
      (chaS m₃ _ M₃ _ _ hS₃ h₂.resOk h₃.resOk) (chaE' m₃ _ M₃ _ _ hS₃ h₂.resOk h₃.resOk)
      fun r₄ m₄ _ h₄ => RefE.after_core (w := id) h₄ fun M₄ hS₄ _ => ?_
    dsimp only [bodyE.k_ctor_head_against_2]
    by_cases f0 : r₄.headD 0 = 0
    · rw [ite_eq_left f0, show decCHA r₄ = none by unfold decCHA; exact ite_eq_left f0]
      exact lazy_tail p hq hc k hk' F m₄ _ dn vis fe M₄ eb mode d x y (by omega) (by omega) (hSP hS₄) hx hy hd
        (fun _ => rfl) (fun _ _ => rfl)
    rw [ite_eq_right f0]
    by_cases v0 : r₄.tail.headD 0 = 0
    · rw [ite_eq_left v0, show decCHA r₄ = some false by unfold decCHA; rw [ite_eq_right f0, v0]; rfl]
      exact RefE.ret rfl (CorePost.ret hS₄ rfl hw0)
    rw [ite_eq_right v0, show decCHA r₄ = some true by
    unfold decCHA; rw [ite_eq_right f0]; exact congrArg some (bne_iff_ne.mpr v0)]
    exact lazy_tail p hq hc k hk' F m₄ _ dn vis fe M₄ eb mode d x (r₃.headD 0) (by omega) (by omega) (hSP hS₄)
      hx h₃.resOk hd (fun _ => rfl) (fun _ _ => rfl)
  rw [ite_eq_left h0, show decCT r₁ = some (decI (r₁.tail.headD 0)) by unfold decCT; exact ite_eq_right h0]
  dsimp only
  refine RefE.bind_callE (s₀ := ⟨m₁, Locals.init []⟩) (fun _ => rfl)
    (hK.whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d x (by omega) (by omega) (hSP hS₁) hx)
    (fun (hG : BodyG p (k + 1 + 1)) => (hG.knot (k + 1) (by omega)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe
      M₁ eb mode d x (by omega) (by omega) (hSP hS₁) hx)
    fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
  dsimp only [bodyE.k_whnf]
  refine RefE.bind_callE (s₀ := ⟨m₃, Locals.init []⟩) (fun _ => rfl)
    (chaS m₃ _ M₃ _ _ hS₃ h₁.resOk h₃.resOk) (chaE' m₃ _ M₃ _ _ hS₃ h₁.resOk h₃.resOk)
    fun r₄ m₄ _ h₄ => RefE.after_core (w := id) h₄ fun M₄ hS₄ _ => ?_
  dsimp only [bodyE.k_ctor_head_against]
  by_cases f0 : r₄.headD 0 = 0
  · rw [ite_eq_left f0, show decCHA r₄ = none by unfold decCHA; exact ite_eq_left f0]
    exact lazy_tail p hq hc k hk' F m₄ _ dn vis fe M₄ eb mode d x y (by omega) (by omega) (hSP hS₄) hx hy hd
      (fun _ => rfl) (fun _ _ => rfl)
  rw [ite_eq_right f0]
  by_cases v0 : r₄.tail.headD 0 = 0
  · rw [ite_eq_left v0, show decCHA r₄ = some false by unfold decCHA; rw [ite_eq_right f0, v0]; rfl]
    exact RefE.ret rfl (CorePost.ret hS₄ rfl hw0)
  rw [ite_eq_right v0, show decCHA r₄ = some true by
    unfold decCHA; rw [ite_eq_right f0]; exact congrArg some (bne_iff_ne.mpr v0)]
  exact lazy_tail p hq hc k hk' F m₄ _ dn vis fe M₄ eb mode d (r₃.headD 0) y (by omega) (by omega) (hSP hS₄)
    h₃.resOk hy hd (fun _ => rfl) (fun _ _ => rfl)

include hq hc in
/-- **`defeq_body` refines `defeqBody`** at the knot one level down: `DefeqBodySpec p n`
(`body_ref`'s ok half). -/
@[refines ConRon.Arena.defeqBody]
theorem defeqBody_refines (n : Nat) : DefeqBodySpec p n :=
  fun F s₀ a₀ dn vis fe M eb mode d x y hF hn hs hx hy hk =>
    RefE.coreSpec (bodyE_spec p hq.body n s₀ mode vis d x y)
      (body_ref p hq hc n hk F s₀ a₀ dn vis fe M eb mode d x y hF hn hs hx hy)

include hq hc in
/-- **The knot's `defeq` slot one level up**, from the body. -/
@[refines_part ConRon.Arena.coreKnot "defeq (step)"]
theorem defeqSlot_step (n : Nat) (hk : KnotUpTo p n) : DefeqSlot p (n + 1) :=
  defeq_refines p hq.knot n hk (defeqBody_refines p hq hc n)

end body

end L.Arena
