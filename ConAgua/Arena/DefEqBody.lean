module

public import ConAgua.Arena.DefEqStuckTail
import ConAgua.Arena.DefEqMidLazy2
public import ConAgua.Arena.LdRd
import ConAgua.Arena.DefEqStuckEta
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.DefEqMidLazy
public import ConAgua.Verdict.WhnfNatE

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

/-- **`defeqBody` past the `Bool.true` shortcut**, copied (`defeqBody_eq`). -/
def defeqBodyRestT (mode : ConLeche.CheckMode) (eager : Bool) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
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

theorem defeqBody_eq (mode : ConLeche.CheckMode) (eager : Bool) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (a b : EIdx) :
    defeqBody mode eager r fe depth a b =
      (if a == b then pure true else do
        let x ← isBoolTrue b
        let y ← hasFvarFast coreWalkFuel a
        let sc ← if x && (eager || !y) then boolTrueShortcut r depth a else pure false
        if sc then pure true else defeqBodyRestT mode eager r fe depth a b) := by rfl

theorem decMode_eager (mode : Word) (h : mode < 4) :
    decEager mode = decide ((mode >>> 1) &&& 1 ≠ 0) := by
  rcases mode_cases mode h with rfl | rfl | rfl | rfl <;> decide

theorem depth_lt_of_shr (d : Word) (h : d >>> 63 = 0) : d.toNat < 2 ^ 63 := by
  have h' := congrArg UInt64.toNat h
  rw [UInt64.toNat_shiftRight] at h'
  simp only [UInt64.toNat_zero, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod,
    Nat.reducePow] at h'
  have := d.toNat_lt
  omega

/-! ## The refinement -/

section body
variable (p : Prog) (hq : DefeqBodyProg p) (hc : DefeqBodyCallees p)

include hq hc in
/-- **`defeq_body` refines `defeqBody`, both outcomes**: the errors are its callees'. -/
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
  rw [defeqBody_eq, decE_beq hx hy]
  simp only [bodyE]
  by_cases hxy : x = y
  · rw [ite_eq_left hxy]
    simp only [hxy, decide_true, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS rfl hw1)
  rw [ite_eq_right hxy]
  simp only [hxy, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine RefE.abort0 (by rfl) fun hd0 => ?_
  have hd := depth_lt_of_shr d (by simpa using hd0)
  cases n with
  | zero => rw [callW_zero, liftE_none, bodyE.k_is_bool_true.none]; exact RefE.of_cls0 (by simp)
  | succ k =>
  have hk' : KnotUpTo p k := hk.mono (by omega)
  refine RefE.bind_callW (fun _ => rfl) (isBoolTrue_refines p hq.stuck.leaf k s₀ a₀ dn vis fe M eb y hS hy)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [bodyE.k_is_bool_true]
  refine RefE.bind_callW (fun _ => rfl) (hc.stuck.defeq.hasFvar (k + 1) ⟨m₁, Locals.init []⟩ _ dn vis fe M₁
    eb x hS₁ hx) fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  dsimp only [bodyE.k_has_fvar]
  have hSP : ∀ {m : Mem} {st : AState} {M : ModeMaps}, CoreS dn m st vis fe M eb →
      SlotPre ⟨m, Locals.init []⟩ st dn vis fe M eb mode := fun h => ⟨h, hs.mode4, hs.eb_mode⟩
  have hK := hk (k + 1) (by omega)
  -- the rest past the shortcut, from any state related at `m₃`
  have rest : ∀ (sc : Word) (st : AState) (m₃ : Mem) (M₃ : ModeMaps), CoreS dn m₃ st vis fe M₃ eb →
      RefE (BodyG p (k + 1 + 1)) (bodyE.j1 p (k + 1) mode vis d x y sc m₃)
        (if (sc != 0) = true then pure true else
          defeqBodyRestT (decMode mode) (decEager mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE x) (decE y))
        st (CorePost decBool dn m₃ vis fe M₃ eb ResH) := by
    intro sc st m₃ M₃ hS₃
    simp only [bodyE.j1]
    by_cases hsc : sc ≠ 0
    · rw [ite_eq_left hsc]
      simp only [hsc, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte]
      exact RefE.ret rfl (CorePost.ret hS₃ rfl hw1)
    rw [ite_eq_right hsc]
    have hsc' : sc = 0 := by simpa using hsc
    simp only [hsc', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    unfold defeqBodyRestT
    have hQ := quickUpTo hq.lazy hc.lazy hk (k + 1) (by omega)
    refine RefE.bind_callE (fun _ => rfl) (hQ F ⟨m₃, Locals.init []⟩ st dn vis fe M₃ eb mode d x y
      (by omega) (by omega) (hSP hS₃) hx hy hd) (fun (hG : BodyG p (k + 1 + 1)) => quickWEUpTo hq.lazy
        hc.lazy hk ⟨hG.knot, hG.nv⟩ (k + 1) (by omega) F ⟨m₃, Locals.init []⟩ st dn vis fe M₃ eb mode d x y
        (by omega) (by omega) (hSP hS₃) hx hy hd)
      fun r₄ m₄ _ h₄ => RefE.after_core (w := id) h₄ fun M₄ hS₄ _ => ?_
    dsimp only [bodyE.k_quick_defeq]
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
    dsimp only [bodyE.k_prop_irrel]
    by_cases hp5 : r₅.headD 0 ≠ 0
    · rw [ite_eq_left hp5, decBool_true_of hp5]
      exact RefE.ret rfl (CorePost.ret hS₅ rfl hw1)
    rw [ite_eq_right hp5, decBool_false_of (by simpa using hp5)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine RefE.bind_callE (fun _ => rfl) (hK.whnfCore F ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode 1 d x
      (by omega) (by omega) (hSP hS₅) hx) (fun (hG : BodyG p (k + 1 + 1)) => (hG.knot (k + 1) (by omega)).whnfCore
        F ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode 1 d x (by omega) (by omega) (hSP hS₅) hx)
      fun r₆ m₆ _ h₆ => RefE.after_core (w := id) h₆ fun M₆ hS₆ _ => ?_
    dsimp only [bodyE.k_whnf_core]
    refine RefE.bind_callE (fun _ => rfl) (hK.whnfCore F ⟨m₆, Locals.init []⟩ _ dn vis fe M₆ eb mode 1 d y
      (by omega) (by omega) (hSP hS₆) hy) (fun (hG : BodyG p (k + 1 + 1)) => (hG.knot (k + 1) (by omega)).whnfCore
        F ⟨m₆, Locals.init []⟩ _ dn vis fe M₆ eb mode 1 d y (by omega) (by omega) (hSP hS₆) hy)
      fun r₇ m₇ _ h₇ => RefE.after_core (w := id) h₇ fun M₇ hS₇ _ => ?_
    dsimp only [bodyE.k_whnf_core_2]
    refine RefE.bind_callE (fun _ => rfl) (hQ F ⟨m₇, Locals.init []⟩ _ dn vis fe M₇ eb mode d _ _
      (by omega) (by omega) (hSP hS₇) h₆.resOk h₇.resOk hd) (fun (hG : BodyG p (k + 1 + 1)) => quickWEUpTo
        hq.lazy hc.lazy hk ⟨hG.knot, hG.nv⟩ (k + 1) (by omega) F ⟨m₇, Locals.init []⟩ _ dn vis fe M₇ eb mode
        d _ _ (by omega) (by omega) (hSP hS₇) h₆.resOk h₇.resOk hd)
      fun r₈ m₈ _ h₈ => RefE.after_core (w := id) h₈ fun M₈ hS₈ _ => ?_
    dsimp only [bodyE.k_quick_defeq_2]
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
    dsimp only [bodyE.k_lazy_delta_reduction]
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
        hq.stuck.stuckIrrel hq.stuck.setCert hq.stuck.setWith hq.stuck.setWtb hq.stuck.setGo
        hq.stuck.setTail hq.stuck.sunit hq.stuck.suHead hq.stuck.suTail hq.stuck.etaCert
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
    simp only [bodyE.k_defeq_tail]
    exact RefE.ret hrun ⟨hP.after, hP.res, hP.valid⟩
  by_cases hb : r₁.headD 0 ≠ 0 ∧ ((mode >>> 1) &&& 1 ≠ 0 ∨ r₂.headD 0 = 0)
  · rw [ite_eq_left hb.1, ite_eq_left hb.2]
    have hcond : (decBool r₁ && (decEager mode || !decBool r₂)) = true := by
      rw [decMode_eager mode hs.mode4, decBool_true_of hb.1]
      rcases hb.2 with h | h
      · simp [h]
      · simp [decBool_false_of h]
    rw [hcond]
    simp only [↓reduceIte]
    refine RefE.bind_callE (fun _ => rfl) (boolTrueShortcut_refines p hq.lazy.mid k hk' F ⟨m₂, Locals.init []⟩
      _ dn vis fe M₂ eb mode d x (by omega) (by omega) (hSP hS₂) hx)
      (fun (hG : BodyG p (k + 1 + 1)) => RefE.coreSpecE (btsE_spec p hq.lazy.mid.bts (k + 1)
        ⟨m₂, Locals.init []⟩ mode vis d x) hG.nv (hG.knot.mono (by omega))
        (bts_ref p hq.lazy.mid k hk' F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d x (by omega)
          (by omega) (hSP hS₂) hx)) fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
    dsimp only [bodyE.k_bool_true_shortcut]
    exact rest (r₃.headD 0) _ _ _ hS₃
  have hW2 : ∀ z : Except Err (List Word × Mem), (if r₁.headD 0 ≠ 0 then
      (if (mode >>> 1 &&& 1 ≠ 0 ∨ r₂.headD 0 = 0) then z else bodyE.j1 p (k + 1) mode vis d x y 0 m₂)
      else bodyE.j1 p (k + 1) mode vis d x y 0 m₂) = bodyE.j1 p (k + 1) mode vis d x y 0 m₂ := by
    intro z
    by_cases h1 : r₁.headD 0 = 0
    · rw [ite_eq_right (fun h => h h1)]
    · rw [ite_eq_left h1, ite_eq_right (fun h => hb ⟨h1, h⟩)]
  rw [hW2]
  have hcond : (decBool r₁ && (decEager mode || !decBool r₂)) = false := by
    rw [decMode_eager mode hs.mode4]
    by_cases h1 : r₁.headD 0 = 0
    · simp [decBool_false_of h1]
    · have h2 : ¬ ((mode >>> 1) &&& 1 ≠ 0 ∨ r₂.headD 0 = 0) := fun h => hb ⟨h1, h⟩
      simp only [not_or, ne_eq, Decidable.not_not] at h2
      simp [h2.1, decBool_true_of h2.2]
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact RefE.bind_right rfl (rest 0 _ _ _ hS₂)

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
