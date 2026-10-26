import ConAgua.Arena.StrLitTy

/-!
# `char_of_nat_ty_ok`, `string_of_list_ty_ok` under `CoreS` (helper `defeq2-str-sup`)

Each test is `str_cv`, the level-parameter count, a run of pin reads and interning that builds the
expected domain and codomain (the twin's tail `cnTail`/`slTail`), then the `∀` comparison
`faEqW`/`faEqT` (`StrLitTy.lean`). The tail's refinement chains the leaves with `coreRef_bind`; a
pin read is a pure step (`pin_step`, `pinWord_step`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Steps -/

/-- Only the result's head word counts for a `Bool` result. -/
theorem strHead_ref {T : AM Bool} {a : AState} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r r' : List Word}
    (he : r.headD 0 = r'.headD 0) (h : CoreRef T a decBool dn m vis fe M eb r' m') :
    CoreRef T a decBool dn m vis fe M eb r m' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, by rw [h3]; unfold decBool; rw [he], by unfold ResH; rw [he]; exact h4⟩

section steps
variable (p : Prog) (hp : StrLitProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
  {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
include hp

/-- **A `pin_at` read, then the rest**: the twin's `pinAt` reads the same name. -/
theorem pin_step {β : Type} [Inhabited β] {f : NIdx → AM β} {dec : List Word → β}
    {ok : List Word → Prop} (hS : CoreS dn m a vis fe M eb) {i : Word} {rp : List Word} {mp : Mem}
    (hc : callW p n "pin_at" [i] m = some (rp, mp))
    (h : CoreRef (f (decI (rp.headD 0))) a dec dn m vis fe M eb r m' ok) :
    CoreRef (pinAt i.toNat >>= f) a dec dn m vis fe M eb r m' ok := by
  obtain ⟨-, -, hi, hr⟩ := callW_pinAt p hp.pinAt n m i rp mp hc
  refine coreRef_congr ?_ h
  rw [StateT.run_bind, pinAt_run hS.pins _ hi, except_ok_bind, hr]

/-- **A `pin_word(53)` read, then the rest**: the twin's `pinZeroLevel`. -/
theorem pinWord_step {β : Type} [Inhabited β] {f : LIdx → AM β} {dec : List Word → β}
    {ok : List Word → Prop} (hS : CoreS dn m a vis fe M eb) {rp : List Word} {mp : Mem}
    (hc : callW p n "pin_word" [53] m = some (rp, mp))
    (h : CoreRef (f (decI (rp.headD 0))) a dec dn m vis fe M eb r m' ok) :
    CoreRef (pinZeroLevel >>= f) a dec dn m vis fe M eb r m' ok := by
  obtain ⟨-, -, hr⟩ := callW_pinWord p hp.pinWord n m 53 rp mp hc
  refine coreRef_congr ?_ h
  rw [StateT.run_bind, pinZeroLevel_run hS.pins, except_ok_bind, hr]; rfl

/-- **The `∀` tail as the last step.** -/
theorem faEq_step (hS : CoreS dn m a vis fe M eb) {ty X Y w : Word} (hty : HW ty) (hX : HW X)
    (hY : HW Y) (h : faEqW p n m ty X Y = some (w, m')) (hr : r.headD 0 = w) :
    CoreRef (faEqT (decI ty) (decE X) (decE Y)) a decBool dn m vis fe M eb r m' := by
  obtain ⟨hrun, rfl, hw⟩ := faEqW_ok hp.eView hS.arena.1 hty hX hY h
  exact cref_run hrun (coreAfter_refl hS) (by unfold decBool; rw [hr])
    (by unfold ResH; rw [hr]; exact hw)

end steps

/-! ## `char_of_nat_ty_ok` -/

/-- The twin's tail of `charOfNatTyOk`: `Nat`, `Char`, then the `∀` comparison. -/
def cnTail (ty : EIdx) : AM Bool := do
  let nt ← pinNat
  let nc ← constE nt
  let ch ← pinChar
  let cc ← constE ch
  faEqT ty nc cc

/-- `e_view`'s answer compared, as in `faEqW`. -/
def faE (X Y : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (g, m₁) => some (if g.tail.headD 0 = X ∧ g.tail.tail.headD 0 = Y then 1 else 0, m₁)

theorem faEqW_eq (p : Prog) (n : Nat) (m : Mem) (ty X Y : Word) :
    faEqW p n m ty X Y =
      if ty >>> 28 ≠ 6 then some (0, m) else faE X Y (callW p n "e_view" [ty] m) := by
  unfold faEqW faE; rfl

/-! The model of `char_of_nat_ty_ok`, one block per call. -/

def cnK4 (p : Prog) (n : Nat) (ty X : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (cc, m₄) => faEqW p n m₄ ty X (cc.headD 0)

def cnK3 (p : Prog) (n : Nat) (ty X : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (ch, m₃) => cnK4 p n ty X (callW p n "const_e" [ch.headD 0] m₃)

def cnK2 (p : Prog) (n : Nat) (ty : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (nc, m₂) => cnK3 p n ty (nc.headD 0) (callW p n "pin_at" [10] m₂)

def cnK1 (p : Prog) (n : Nat) (ty : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (nt, m₁) => cnK2 p n ty (callW p n "const_e" [nt.headD 0] m₁)

/-- The model of `char_of_nat_ty_ok`'s tail. -/
def cnTailW (p : Prog) (n : Nat) (m : Mem) (ty : Word) : Option (Word × Mem) :=
  cnK1 p n ty (callW p n "pin_at" [1] m)

def cnK0 (p : Prog) (n : Nat) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (c, m₁) => if c.tail.headD 0 ≠ 0 then some (0, m₁) else cnTailW p n m₁ (c.tail.tail.headD 0)

/-- The model of `char_of_nat_ty_ok`. -/
def cnW (p : Prog) (n : Nat) (m : Mem) (found q : Word) : Option (Word × Mem) :=
  if found = 0 then some (0, m) else cnK0 p n (callW p n "str_cv" [q] m)

theorem charOfNatTyOk_spec (p : Prog) (hp : p.lookup "char_of_nat_ty_ok" = some charOfNatTyOkL)
    (n : Nat) (s₀ : St) (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "char_of_nat_ty_ok" [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ cnW p n s₀.mem found q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, charOfNatTyOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "str_cv", callW_spec p n "pin_at", callW_spec p n "const_e",
      callW_spec p n "e_view"] <;>
    -- depth: `ty` (local 4) reaches the tail through five frames
    finish (gen := 20) [cnW, cnK0, cnTailW, cnK1, cnK2, cnK3, cnK4, faEqW_eq, faE]

/-! ## `string_of_list_ty_ok` -/

/-- The twin's tail of `stringOfListTyOk`: `List.{0} Char`, `String`, then the `∀` comparison. -/
def slTail (ty : EIdx) : AM Bool := do
  let z ← zeroLevel
  let zs ← internLsNode [z]
  let li ← pinList
  let lc ← internE (.const li zs)
  let ch ← pinChar
  let cc ← constE ch
  let dom ← internE (.app lc cc)
  let st ← pinString
  let sc ← constE st
  faEqT ty dom sc

/-! The model of `string_of_list_ty_ok`, one block per call. -/

def slK9 (p : Prog) (n : Nat) (ty dom : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (sc, m₉) => faEqW p n m₉ ty dom (sc.headD 0)

def slK8 (p : Prog) (n : Nat) (ty dom : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (st, m₈) => slK9 p n ty dom (callW p n "const_e" [st.headD 0] m₈)

def slK7 (p : Prog) (n : Nat) (ty : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (dom, m₇) => slK8 p n ty (dom.headD 0) (callW p n "pin_at" [5] m₇)

def slK6 (p : Prog) (n : Nat) (ty lc : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (cc, m₆) => slK7 p n ty (callW p n "mk_app" [lc, cc.headD 0] m₆)

def slK5 (p : Prog) (n : Nat) (ty lc : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (ch, m₅) => slK6 p n ty lc (callW p n "const_e" [ch.headD 0] m₅)

def slK4 (p : Prog) (n : Nat) (ty : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (lc, m₄) => slK5 p n ty (lc.headD 0) (callW p n "pin_at" [10] m₄)

def slK3 (p : Prog) (n : Nat) (ty zs : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (li, m₃) => slK4 p n ty (callW p n "intern_const" [li.headD 0, zs] m₃)

def slK2 (p : Prog) (n : Nat) (ty : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (zs, m₂) => slK3 p n ty (zs.headD 0) (callW p n "pin_at" [7] m₂)

def slK1 (p : Prog) (n : Nat) (ty : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (zl, m₁) => slK2 p n ty (callW p n "str_ls1" [zl.headD 0] m₁)

/-- The model of `string_of_list_ty_ok`'s tail. -/
def slTailW (p : Prog) (n : Nat) (m : Mem) (ty : Word) : Option (Word × Mem) :=
  slK1 p n ty (callW p n "pin_word" [53] m)

def slK0 (p : Prog) (n : Nat) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (c, m₁) => if c.tail.headD 0 ≠ 0 then some (0, m₁) else slTailW p n m₁ (c.tail.tail.headD 0)

/-- The model of `string_of_list_ty_ok`. -/
def solW (p : Prog) (n : Nat) (m : Mem) (found q : Word) : Option (Word × Mem) :=
  if found = 0 then some (0, m) else slK0 p n (callW p n "str_cv" [q] m)

set_option maxHeartbeats 2000000 in
theorem stringOfListTyOk_spec (p : Prog)
    (hp : p.lookup "string_of_list_ty_ok" = some stringOfListTyOkL) (n : Nat) (s₀ : St)
    (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "string_of_list_ty_ok" [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ solW p n s₀.mem found q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, stringOfListTyOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "str_cv", callW_spec p n "pin_word", callW_spec p n "str_ls1",
      callW_spec p n "pin_at", callW_spec p n "intern_const", callW_spec p n "const_e",
      callW_spec p n "mk_app", callW_spec p n "e_view"] <;>
    -- depth: `ty` (local 4) reaches the tail through ten frames
    finish (gen := 20) [solW, slK0, slTailW, slK1, slK2, slK3, slK4, slK5, slK6, slK7, slK8, slK9,
      faEqW_eq, faE]

section calls
variable (p : Prog) (hp : StrLitProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
  {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
include hp

theorem cnTail_ref (hS : CoreS dn m a vis fe M eb) {ty w : Word} (hty : HW ty)
    (h : cnTailW p n m ty = some (w, m')) (hr : r.headD 0 = w) :
    CoreRef (cnTail (decI ty)) a decBool dn m vis fe M eb r m' := by
  unfold cnTailW at h
  cases h1 : callW p n "pin_at" [1] m with
  | none => rw [h1] at h; cases h
  | some q₁ =>
  obtain ⟨nt, m₁⟩ := q₁
  rw [h1] at h; simp only [cnK1, cnK2, cnK3, cnK4] at h
  obtain ⟨hmq, -, -, hnt⟩ := callW_pinAt p hp.pinAt n m 1 nt m₁ h1
  subst m₁
  have hnt' : HW (nt.headD 0) := by rw [hnt]; exact hS.pins.names_lt _ (by decide)
  cases h2 : callW p n "const_e" [nt.headD 0] m with
  | none => rw [h2] at h; cases h
  | some q₂ =>
  obtain ⟨nc, m₂⟩ := q₂
  rw [h2] at h; simp only at h
  refine pin_step p hp hS h1 (coreRef_bind (constE_call p hp hS hnt' h2) fun M₂ hS₂ => ?_)
  cases h3 : callW p n "pin_at" [10] m₂ with
  | none => rw [h3] at h; cases h
  | some q₃ =>
  obtain ⟨ch, m₃⟩ := q₃
  rw [h3] at h; simp only at h
  obtain ⟨hmq, -, -, hch⟩ := callW_pinAt p hp.pinAt n m₂ 10 ch m₃ h3
  subst m₃
  have hch' : HW (ch.headD 0) := by rw [hch]; exact hS₂.pins.names_lt _ (by decide)
  cases h4 : callW p n "const_e" [ch.headD 0] m₂ with
  | none => rw [h4] at h; cases h
  | some q₄ =>
  obtain ⟨cc, m₄⟩ := q₄
  rw [h4] at h; simp only at h
  have hnc := (constE_call p hp hS hnt' h2).2.2.2
  refine pin_step p hp hS₂ h3 (coreRef_bind (constE_call p hp hS₂ hch' h4) fun M₄ hS₄ => ?_)
  have hcc := (constE_call p hp hS₂ hch' h4).2.2.2
  exact faEq_step p hp hS₄ hty hnc hcc h hr

/-- The twins' common prefix: the constant's value, no level parameters; then the tail `T`. -/
def noLpT (T : EIdx → AM Bool) : Option IConstantInfo → AM Bool
  | some ci => do
    let cv := ci.toConstantVal
    if !cv.levelParams.isEmpty then pure false else T cv.type
  | none => pure false

/-- **The common prefix of the two tests refines the twins'**, given the tail's refinement. -/
theorem noLp_call (hS : CoreS dn m a vis fe M eb) {found q : Word}
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP m) dn q.toNat = some ci)
    {K0 : Option (List Word × Mem) → Option (Word × Mem)} {TW : Mem → Word → Option (Word × Mem)}
    {T : EIdx → AM Bool} (hn : K0 none = none)
    (hK : ∀ c m₁, K0 (some (c, m₁)) =
      if c.tail.headD 0 ≠ 0 then some (0, m₁) else TW m₁ (c.tail.tail.headD 0))
    (hW : (if found = 0 then some (0, m) else K0 (callW p n "str_cv" [q] m)) = some (r.headD 0, m'))
    (htail : ∀ m₁ a₁ M₁ ty, CoreS dn m₁ a₁ vis fe M₁ eb → HW ty → TW m₁ ty = some (r.headD 0, m') →
      CoreRef (T (decI ty)) a₁ decBool dn m₁ vis fe M₁ eb r m') :
    CoreRef (noLpT T (decFound dn m found q)) a decBool dn m vis fe M eb r m' := by
  by_cases hf0 : found = 0
  · rw [ite_eq_left hf0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    simp only [decFound, hf0, ↓reduceIte]
    exact cref_run (v := false) rfl (coreAfter_refl hS) (by rw [decBool, ← hr]; rfl)
      (by unfold ResH HW; rw [← hr]; decide)
  rw [ite_eq_right hf0] at hW
  obtain ⟨ci, hci⟩ := hdec hf0
  rw [show decFound dn m found q = some ci by simp only [decFound, hf0, ↓reduceIte, hci]]
  rcases h1 : callW p n "str_cv" [q] m with _ | ⟨c, m₁⟩
  · rw [h1, hn] at hW; cases hW
  rw [h1, hK] at hW
  obtain ⟨hm₁, -, hlen, hty, hhw⟩ := cv_call p hp hS hci h1
  subst m₁
  dsimp only [noLpT]
  generalize ci.toConstantVal = cv at hlen hty
  by_cases hll : c.tail.headD 0 ≠ 0
  · rw [ite_eq_left hll] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, rfl⟩ := hW
    have he : cv.levelParams.isEmpty = false := by
      rcases hl : cv.levelParams with _ | ⟨x, xs⟩
      · rw [hl] at hlen; exact absurd (UInt64.toNat_inj.mp (by rw [← hlen]; rfl)) hll
      · rfl
    rw [he]
    exact coreRef_ret hS (by unfold decBool; rw [← hr]; rfl) (by unfold ResH HW; rw [← hr]; decide)
  rw [ite_eq_right hll] at hW
  have he : cv.levelParams.isEmpty = true := by
    rcases hl : cv.levelParams with _ | ⟨x, xs⟩
    · rfl
    · rw [hl] at hlen; simp only [List.length_cons] at hlen
      have : c.tail.headD 0 = 0 := by simpa using hll
      rw [this] at hlen; simp at hlen
  simp only [he, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hty]
  exact htail _ _ _ _ hS hhw hW

/-- **`char_of_nat_ty_ok` refines `charOfNatTyOk`.** -/
@[refines ConRon.Arena.charOfNatTyOk]
theorem charOfNatTyOk_call (hS : CoreS dn m a vis fe M eb) {found q : Word}
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP m) dn q.toNat = some ci)
    (h : callW p n "char_of_nat_ty_ok" [found, q] m = some (r, m')) :
    CoreRef (charOfNatTyOk (decFound dn m found q)) a decBool dn m vis fe M eb r m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (charOfNatTyOk_spec p hp.charOfNatTyOk n _ found q) h
  exact noLp_call (K0 := cnK0 p n) p hp hS hdec rfl (fun _ _ => rfl) hW
    fun _ _ _ _ hS₁ hhw hW => cnTail_ref p hp hS₁ hhw hW rfl

theorem slTail_ref (hS : CoreS dn m a vis fe M eb) {ty w : Word} (hty : HW ty)
    (h : slTailW p n m ty = some (w, m')) (hr : r.headD 0 = w) :
    CoreRef (slTail (decI ty)) a decBool dn m vis fe M eb r m' := by
  unfold slTailW at h
  cases h1 : callW p n "pin_word" [53] m with
  | none => rw [h1] at h; cases h
  | some q₁ =>
  obtain ⟨zl, m₁⟩ := q₁
  rw [h1] at h; simp only [slK1, slK2, slK3, slK4, slK5, slK6, slK7, slK8, slK9] at h
  obtain ⟨hmq, -, hzl⟩ := callW_pinWord p hp.pinWord n m 53 zl m₁ h1
  subst m₁
  have hzl' : HW (zl.headD 0) := by rw [hzl]; exact hS.pins.lv_lt.2.1
  cases h2 : callW p n "str_ls1" [zl.headD 0] m with
  | none => rw [h2] at h; cases h
  | some q₂ =>
  obtain ⟨zs, m₂⟩ := q₂
  rw [h2] at h; simp only at h
  have hzs := (ls1_call p hp hS hzl' (zero_den hS hzl) h2).2.2.2
  refine pinWord_step p hp hS h1 (coreRef_bind (ls1_call p hp hS hzl' (zero_den hS hzl) h2) fun M₂ hS₂ => ?_)
  cases h3 : callW p n "pin_at" [7] m₂ with
  | none => rw [h3] at h; cases h
  | some q₃ =>
  obtain ⟨li, m₃⟩ := q₃
  rw [h3] at h; simp only at h
  obtain ⟨hmq, -, -, hli⟩ := callW_pinAt p hp.pinAt n m₂ 7 li m₃ h3
  subst m₃
  have hli' : HW (li.headD 0) := by rw [hli]; exact hS₂.pins.names_lt _ (by decide)
  cases h4 : callW p n "intern_const" [li.headD 0, zs.headD 0] m₂ with
  | none => rw [h4] at h; cases h
  | some q₄ =>
  obtain ⟨lc, m₄⟩ := q₄
  rw [h4] at h; simp only at h
  have hzd := ls1_den p hp hS hzl' h2 (zero_den hS hzl)
  refine pin_step p hp hS₂ h3 (coreRef_bind (const_call p hp hS₂ hli' hzs h4 hzd) fun M₄ hS₄ => ?_)
  cases h5 : callW p n "pin_at" [10] m₄ with
  | none => rw [h5] at h; cases h
  | some q₅ =>
  obtain ⟨ch, m₅⟩ := q₅
  rw [h5] at h; simp only at h
  obtain ⟨hmq, -, -, hch⟩ := callW_pinAt p hp.pinAt n m₄ 10 ch m₅ h5
  subst m₅
  have hch' : HW (ch.headD 0) := by rw [hch]; exact hS₄.pins.names_lt _ (by decide)
  cases h6 : callW p n "const_e" [ch.headD 0] m₄ with
  | none => rw [h6] at h; cases h
  | some q₆ =>
  obtain ⟨cc, m₆⟩ := q₆
  rw [h6] at h; simp only at h
  refine pin_step p hp hS₄ h5 (coreRef_bind (constE_call p hp hS₄ hch' h6) fun M₆ hS₆ => ?_)
  cases h7 : callW p n "mk_app" [lc.headD 0, cc.headD 0] m₆ with
  | none => rw [h7] at h; cases h
  | some q₇ =>
  obtain ⟨dom, m₇⟩ := q₇
  rw [h7] at h; simp only at h
  have hdom := (app_call p hp hS₆ h7).2.2.2
  refine coreRef_bind (app_call p hp hS₆ h7) fun M₇ hS₇ => ?_
  cases h8 : callW p n "pin_at" [5] m₇ with
  | none => rw [h8] at h; cases h
  | some q₈ =>
  obtain ⟨st, m₈⟩ := q₈
  rw [h8] at h; simp only at h
  obtain ⟨hmq, -, -, hst⟩ := callW_pinAt p hp.pinAt n m₇ 5 st m₈ h8
  subst m₈
  have hst' : HW (st.headD 0) := by rw [hst]; exact hS₇.pins.names_lt _ (by decide)
  cases h9 : callW p n "const_e" [st.headD 0] m₇ with
  | none => rw [h9] at h; cases h
  | some q₉ =>
  obtain ⟨sc, m₉⟩ := q₉
  rw [h9] at h; simp only at h
  refine pin_step p hp hS₇ h8 (coreRef_bind (constE_call p hp hS₇ hst' h9) fun M₉ hS₉ => ?_)
  have hsc := (constE_call p hp hS₇ hst' h9).2.2.2
  exact faEq_step p hp hS₉ hty hdom hsc h hr

/-- **`string_of_list_ty_ok` refines `stringOfListTyOk`.** -/
@[refines ConRon.Arena.stringOfListTyOk]
theorem stringOfListTyOk_call (hS : CoreS dn m a vis fe M eb) {found q : Word}
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP m) dn q.toNat = some ci)
    (h : callW p n "string_of_list_ty_ok" [found, q] m = some (r, m')) :
    CoreRef (stringOfListTyOk (decFound dn m found q)) a decBool dn m vis fe M eb r m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (stringOfListTyOk_spec p hp.stringOfListTyOk n _ found q) h
  exact noLp_call (K0 := slK0 p n) p hp hS hdec rfl (fun _ _ => rfl) hW
    fun _ _ _ _ hS₁ hhw hW => slTail_ref p hp hS₁ hhw hW rfl

end calls

end L.Arena
