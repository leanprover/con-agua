import ConAgua.Arena.DefEqStuckTail
import ConAgua.Arena.DefEqMidLazy2
import ConAgua.Census.Attr

/-!
# `defeq_body` refines `defeqBody`; the knot's `defeq` slot one level up (lane `defeq`)

The callW pattern (`DefEqStuckTail.lean`): a word model of `defeq_body` with its callees through
their runs (`dbW`), the L spec by `vcgen` + `simp_all`, the refinement from the callees' specs
(`is_bool_true`, `has_fvar`, `bool_true_shortcut`, `quick_defeq` twice, `prop_irrel`, the cheap
`whnf_core` slot twice, `lazy_delta_reduction`, `defeq_tail`), threaded through the twin's `do`
block by `coreRef_bind`. `DefeqBodySpec p n` (`KnotSlot.lean`) is then a theorem
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

/-! ## The model -/

section dbK
variable (p : Prog) (n : Nat) (mode vis d a b : Word)

/-- Past `lazy_delta_reduction`'s run. -/
def dbK7 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, m)
    else if r.headD 0 = 1 then some (1, m)
    else call1W p n "defeq_tail" [mode, vis, d, r.tail.headD 0, r.tail.tail.headD 0] m

/-- Past the second `quick_defeq`'s run. -/
def dbK6 (a1 b1 : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then some (r.tail.headD 0, m)
    else dbK7 p n mode vis d (callW p n "lazy_delta_reduction" [mode, vis, d, a1, b1] m)

/-- Past the second cheap `whnf_core`'s run. -/
def dbK5 (a1 : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    dbK6 p n mode vis d a1 (r.headD 0) (callW p n "quick_defeq" [mode, vis, d, a1, r.headD 0] m)

/-- Past the first cheap `whnf_core`'s run. -/
def dbK4 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => dbK5 p n mode vis d (r.headD 0) (callW p n "whnf_core" [mode, 1, vis, d, b] m)

/-- Past `prop_irrel`'s run. -/
def dbK3 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then some (1, m)
    else dbK4 p n mode vis d b (callW p n "whnf_core" [mode, 1, vis, d, a] m)

/-- Past the first `quick_defeq`'s run. -/
def dbK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then some (r.tail.headD 0, m)
    else dbK3 p n mode vis d a b (callW p n "prop_irrel" [mode, vis, d, a, b] m)

/-- Past the `Bool.true` shortcut (`sc` its verdict word). -/
def dbKsc (sc : Word) (m : Mem) : Option (Word × Mem) :=
  if sc ≠ 0 then some (1, m)
  else dbK2 p n mode vis d a b (callW p n "quick_defeq" [mode, vis, d, a, b] m)

/-- Past `has_fvar`'s run (`bt` is `is_bool_true`'s word). -/
def dbK1b (bt : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if bt ≠ 0 ∧ ((mode >>> 1) &&& 1 ≠ 0 ∨ r.headD 0 = 0) then
      match callW p n "bool_true_shortcut" [mode, vis, d, a] m with
      | none => none
      | some (r', m') => dbKsc p n mode vis d a b (r'.headD 0) m'
    else dbKsc p n mode vis d a b 0 m

/-- Past `is_bool_true`'s run. -/
def dbK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => dbK1b p n mode vis d a b (r.headD 0) (callW p n "has_fvar" [a] m)

/-- **The model of `defeq_body`.** -/
def dbW (m : Mem) : Option (Word × Mem) :=
  if a = b then some (1, m)
  else if d >>> 63 ≠ 0 then none
  else dbK1 p n mode vis d a b (callW p n "is_bool_true" [b] m)

variable (r : List Word) (m : Mem) (bt a1 : Word)
theorem dbK1_some : dbK1 p n mode vis d a b (some (r, m)) =
    dbK1b p n mode vis d a b (r.headD 0) (callW p n "has_fvar" [a] m) := rfl
theorem dbK2_some : dbK2 p n mode vis d a b (some (r, m)) =
    if r.headD 0 ≠ 0 then some (r.tail.headD 0, m)
    else dbK3 p n mode vis d a b (callW p n "prop_irrel" [mode, vis, d, a, b] m) := rfl
theorem dbK4_some : dbK4 p n mode vis d b (some (r, m)) =
    dbK5 p n mode vis d (r.headD 0) (callW p n "whnf_core" [mode, 1, vis, d, b] m) := rfl
theorem dbK5_some : dbK5 p n mode vis d a1 (some (r, m)) =
    dbK6 p n mode vis d a1 (r.headD 0) (callW p n "quick_defeq" [mode, vis, d, a1, r.headD 0] m) := rfl

end dbK

theorem defeqBody_spec (p : Prog) (hp : DefeqBodyProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_body" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ dbW p n mode vis d a b s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.body]
  simp only [callFn, defeqBodyL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "is_bool_true",
      callW_spec p n "has_fvar", callW_spec p n "bool_true_shortcut", callW_spec p n "quick_defeq",
      callW_spec p n "prop_irrel", callW_spec p n "whnf_core", callW_spec p n "lazy_delta_reduction",
      callW_spec p n "defeq_tail"] <;>
  simp_all [dbW, dbK1, dbK1b, dbKsc, dbK2, dbK3, dbK4, dbK5, dbK6, dbK7, call1W, LocEq, BinOp.eval,
    St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-! ## The twin side -/

/-- **`defeqBody` past the `Bool.true` shortcut**, copied (`defeqBody_eq`). -/
def defeqBodyRestT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
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
  match ← lazyDeltaReduction mode r fe depth defeqLoopFuel a' b' with
  | .verdict v => pure v
  | .unknown a₁ b₁ => defeqTailT mode r fe depth a₁ b₁

theorem defeqBody_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (a b : EIdx) :
    defeqBody mode r fe depth a b =
      (if a == b then pure true else do
        let x ← isBoolTrue b
        let y ← hasFvarFast coreWalkFuel a
        let sc ← if x && (mode.eager || !y) then boolTrueShortcut r depth a else pure false
        if sc then pure true else defeqBodyRestT mode r fe depth a b) := rfl

theorem decMode_eager (mode : Word) (h : mode < 4) :
    (decMode mode).eager = decide ((mode >>> 1) &&& 1 ≠ 0) := by
  rcases mode_cases mode h with rfl | rfl | rfl | rfl <;> decide

theorem depth_lt_of_shr (d : Word) (h : d >>> 63 = 0) : d.toNat < 2 ^ 63 := by
  have h' := congrArg UInt64.toNat h
  rw [UInt64.toNat_shiftRight] at h'
  simp only [UInt64.toNat_zero, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod,
    Nat.reducePow] at h'
  have := d.toNat_lt
  omega

/-- A verdict word answered as it is: the twin's `pure (w != 0)`. -/
theorem coreRef_word {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word} {m' : Mem} {w : Word}
    (hS : CoreS dn m a vis fe M eb) (hw : HW w) (hW : some (w, m) = some (r.headD 0, m')) :
    CoreRef (pure (w != 0) : AM Bool) a decBool dn m vis fe M eb r m' := by
  obtain ⟨hr, hm⟩ := some_pair_inj hW
  rw [← hm]
  exact coreRef_pure hS rfl (by simp only [decBool, hr]) (by unfold ResH; rw [← hr]; exact hw)

/-! ## The refinement -/

section body
variable (p : Prog) (hq : DefeqBodyProg p) (hc : DefeqBodyCallees p)

include hq hc in
/-- **`defeq_body` refines `defeqBody`** at the knot one level down: `DefeqBodySpec p n`. -/
@[refines ConRon.Arena.defeqBody]
theorem defeqBody_refines (n : Nat) : DefeqBodySpec p n := by
  intro F s₀ a₀ dn vis fe M eb mode d x y hF hn hs hx hy hk
  cases n with
  | zero => exact CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqBody_spec p hq n s₀ mode vis d x y)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  rw [defeqBody_eq, decE_beq hx hy]
  unfold dbW at hW
  by_cases hxy : x = y
  · rw [ite_eq_left hxy] at hW
    simp only [hxy, decide_true, ↓reduceIte]
    exact coreRef_true hS hW
  rw [ite_eq_right hxy] at hW
  simp only [hxy, decide_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hd0, hW⟩ := of_ite_none hW
  have hd := depth_lt_of_shr d (by simpa using hd0)
  obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
  obtain ⟨k, rfl⟩ := callW_succ hc1
  have hk' : KnotUpTo p k := hk.mono (by omega)
  have h₁ := CoreSpec.of_callW (isBoolTrue_refines p hq.stuck.leaf k s a₀ dn vis fe M eb y hS hy) hc1
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  rw [dbK1_some] at hW1
  obtain ⟨r₂, m₂, hc2, hW2⟩ := callW_cases rfl hW1
  have h₂ := CoreSpec.of_callW
    (hc.stuck.defeq.hasFvar (k + 1) ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb x hS₁ hx) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  simp only [dbK1b] at hW2
  -- the rest past the shortcut, from any state related at `m₃`
  have rest : ∀ (sc : Word) (st : AState) (m₃ : Mem) (M₃ : ModeMaps),
      CoreS dn m₃ st vis fe M₃ eb → dbKsc p (k + 1) mode vis d x y sc m₃ = some (r.headD 0, s'.mem) →
      CoreRef (if (sc != 0) = true then pure true else
        defeqBodyRestT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE x) (decE y))
        st decBool dn m₃ vis fe M₃ eb r s'.mem := by
    intro sc st m₃ M₃ hS₃ hW3
    unfold dbKsc at hW3
    by_cases hsc : sc ≠ 0
    · rw [ite_eq_left hsc] at hW3
      simp only [hsc, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte]
      exact coreRef_true hS₃ hW3
    rw [ite_eq_right hsc] at hW3
    have hsc' : sc = 0 := by simpa using hsc
    simp only [hsc', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    unfold defeqBodyRestT
    have hSP : ∀ {m : Mem} {st : AState} {M : ModeMaps}, CoreS dn m st vis fe M eb →
        SlotPre ⟨m, Locals.init []⟩ st dn vis fe M eb mode := fun h => ⟨h, hs.mode4, hs.eb_mode⟩
    have hQ := quickUpTo hq.lazy hc.lazy hk (k + 1) (by omega)
    obtain ⟨r₄, m₄, hc4, hW4⟩ := callW_cases rfl hW3
    have h₄ := CoreSpec.of_callW (hQ F ⟨m₃, Locals.init []⟩ st dn vis fe M₃ eb mode d x y
      (by omega) (by omega) (hSP hS₃) hx hy hd) hc4
    refine coreRef_bind h₄ (fun M₄ hS₄ => ?_)
    rw [dbK2_some] at hW4
    by_cases hq4 : r₄.headD 0 ≠ 0
    · rw [ite_eq_left hq4] at hW4
      simp only [decOB, ite_eq_right hq4]
      exact coreRef_word hS₄ h₄.2.2.2.2 hW4
    rw [ite_eq_right hq4] at hW4
    simp only [decOB, ite_eq_left (show r₄.headD 0 = 0 by simpa using hq4)]
    obtain ⟨r₅, m₅, hc5, hW5⟩ := callW_cases rfl hW4
    have h₅ := CoreSpec.of_callW (propIrrel_refines p hq.stuck hc.stuck k hk' F ⟨m₄, Locals.init []⟩
      _ dn vis fe M₄ eb mode d x y (by omega) (by omega) (hSP hS₄) hx hy) hc5
    refine coreRef_bind h₅ (fun M₅ hS₅ => ?_)
    simp only [dbK3] at hW5
    by_cases hp5 : r₅.headD 0 ≠ 0
    · rw [ite_eq_left hp5] at hW5
      rw [decBool_true_of hp5]; exact coreRef_true hS₅ hW5
    rw [ite_eq_right hp5] at hW5
    rw [decBool_false_of (by simpa using hp5)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hK := hk (k + 1) (by omega)
    obtain ⟨r₆, m₆, hc6, hW6⟩ := callW_cases rfl hW5
    have h₆ := CoreSpec.of_callW (hK.whnfCore F ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode 1 d x
      (by omega) (by omega) (hSP hS₅) hx) hc6
    rw [show ((1 : Word) != 0) = true from rfl] at h₆
    refine coreRef_bind h₆ (fun M₆ hS₆ => ?_)
    rw [dbK4_some] at hW6
    obtain ⟨r₇, m₇, hc7, hW7⟩ := callW_cases rfl hW6
    have h₇ := CoreSpec.of_callW (hK.whnfCore F ⟨m₆, Locals.init []⟩ _ dn vis fe M₆ eb mode 1 d y
      (by omega) (by omega) (hSP hS₆) hy) hc7
    rw [show ((1 : Word) != 0) = true from rfl] at h₇
    refine coreRef_bind h₇ (fun M₇ hS₇ => ?_)
    rw [dbK5_some] at hW7
    obtain ⟨r₈, m₈, hc8, hW8⟩ := callW_cases rfl hW7
    have h₈ := CoreSpec.of_callW (hQ F ⟨m₇, Locals.init []⟩ _ dn vis fe M₇ eb mode d _ _
      (by omega) (by omega) (hSP hS₇) h₆.2.2.2 h₇.2.2.2 hd) hc8
    refine coreRef_bind h₈ (fun M₈ hS₈ => ?_)
    simp only [dbK6] at hW8
    by_cases hq8 : r₈.headD 0 ≠ 0
    · rw [ite_eq_left hq8] at hW8
      simp only [decOB, ite_eq_right hq8]
      exact coreRef_word hS₈ h₈.2.2.2.2 hW8
    rw [ite_eq_right hq8] at hW8
    simp only [decOB, ite_eq_left (show r₈.headD 0 = 0 by simpa using hq8)]
    obtain ⟨r₉, m₉, hc9, hW9⟩ := callW_cases rfl hW8
    have h₉ := CoreSpec.of_callW (lazyDeltaReduction_refines p hq.lazy hc.lazy k hk' F (by omega)
      (by omega) ⟨m₈, Locals.init []⟩ _ dn vis fe M₈ eb mode d _ _ (hSP hS₈) h₆.2.2.2 h₇.2.2.2 hd) hc9
    refine coreRef_bind h₉ (fun M₉ hS₉ => ?_)
    simp only [dbK7] at hW9
    obtain ⟨g0, g1, g2⟩ := h₉.2.2.2
    by_cases l0 : r₉.headD 0 = 0
    · rw [ite_eq_left l0] at hW9
      simp only [decLR, ite_eq_left l0]
      exact coreRef_word (w := 0) hS₉ hw0 hW9
    rw [ite_eq_right l0] at hW9
    by_cases l1 : r₉.headD 0 = 1
    · rw [ite_eq_left l1] at hW9
      simp only [decLR, ite_eq_right l0, ite_eq_left l1]
      exact coreRef_word (w := 1) hS₉ hw1 hW9
    rw [ite_eq_right l1] at hW9
    simp only [decLR, ite_eq_right l0, ite_eq_right l1]
    exact CoreSpec.of_call1W (s₀ := ⟨m₉, Locals.init []⟩)
      (defeqTail_refines p hq.stuck hq.iota hc.stuck k hk' F _ _ dn vis fe M₉ eb mode d _ _
        (by omega) (by omega) (hSP hS₉) g1 g2 hd) (fun r r' h => by simp only [decBool, h]) hW9
  by_cases hb : r₁.headD 0 ≠ 0 ∧ ((mode >>> 1) &&& 1 ≠ 0 ∨ r₂.headD 0 = 0)
  · rw [ite_eq_left hb] at hW2
    have hcond : (decBool r₁ && ((decMode mode).eager || !decBool r₂)) = true := by
      rw [decMode_eager mode hs.mode4, decBool_true_of hb.1]
      rcases hb.2 with h | h
      · simp [h]
      · simp [decBool_false_of h]
    rw [hcond]
    simp only [↓reduceIte]
    obtain ⟨r₃, m₃, hc3, hW3⟩ := callW_cases (K := fun res => match res with
      | none => none | some (r', m') => dbKsc p (k + 1) mode vis d x y (r'.headD 0) m') rfl hW2
    have h₃ := CoreSpec.of_callW (boolTrueShortcut_refines p hq.lazy.mid k hk' F ⟨m₂, Locals.init []⟩
      _ dn vis fe M₂ eb mode d x (by omega) (by omega) ⟨hS₂, hs.mode4, hs.eb_mode⟩ hx) hc3
    refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
    exact rest _ _ _ _ hS₃ hW3
  rw [ite_eq_right hb] at hW2
  have hcond : (decBool r₁ && ((decMode mode).eager || !decBool r₂)) = false := by
    rw [decMode_eager mode hs.mode4]
    by_cases h1 : r₁.headD 0 = 0
    · simp [decBool_false_of h1]
    · have h2 : ¬ ((mode >>> 1) &&& 1 ≠ 0 ∨ r₂.headD 0 = 0) := fun h => hb ⟨h1, h⟩
      simp only [not_or, ne_eq, Decidable.not_not] at h2
      simp [h2.1, decBool_true_of h2.2]
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine coreRef_bind (r₁ := [0]) (coreRef_ret (dec := decBool) (ok := ResH) hS₂ rfl hw0)
    (fun M₃ hS₃ => ?_)
  exact rest 0 _ _ _ hS₃ hW2

include hq hc in
/-- **The knot's `defeq` slot one level up**, from the body. -/
@[refines_part ConRon.Arena.coreKnot "defeq (step)"]
theorem defeqSlot_step (n : Nat) (hk : KnotUpTo p n) : DefeqSlot p (n + 1) :=
  defeq_refines p hq.knot n hk (defeqBody_refines p hq hc n)

end body

end L.Arena
