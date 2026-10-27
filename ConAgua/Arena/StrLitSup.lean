import ConAgua.Arena.StrLitChar
import ConAgua.Arena.StrLitList
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# `str_lit_supported` under `CoreS` (helper `defeq2-str-sup`)

`str_lit_supported(vis)` is the `Nat` literal guard, then `str_sup_1` … `str_sup_7`, one function
per tested declaration. Each `str_sup_k` is a suffix of the twin's chain `strLitSupported`
(`strSupkT`): `pin_at(i)` and `env_find` (`callW_pinFind`), the declaration's test, and, when it
passes, the next stage. One stage lemma (`sup_stage`) covers the six guarded stages, from the
test's refinement and the next stage's; `sup7_stage` the last one, `guard_ref` the `if` step they
share with `str_lit_supported` itself.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin's suffixes -/

/-- `strLitSupported` from `Char.ofNat` on. -/
def strSup7T (fe : IFEnv) : AM Bool := do
  let co ← pinCharOfNat
  charOfNatTyOk (fe.find? co)

/-- `strLitSupported` from `charTyOk`'s declaration on. -/
def strSup6T (fe : IFEnv) : AM Bool := do
  let x ← pinChar
  if !(← charTyOk (fe.find? x)) then pure false else strSup7T fe

/-- `strLitSupported` from `listConsTyOk`'s declaration on. -/
def strSup5T (fe : IFEnv) : AM Bool := do
  let x ← pinListCons
  if !(← listConsTyOk (fe.find? x)) then pure false else strSup6T fe

/-- `strLitSupported` from `listNilTyOk`'s declaration on. -/
def strSup4T (fe : IFEnv) : AM Bool := do
  let x ← pinListNil
  if !(← listNilTyOk (fe.find? x)) then pure false else strSup5T fe

/-- `strLitSupported` from `listTyOk`'s declaration on. -/
def strSup3T (fe : IFEnv) : AM Bool := do
  let x ← pinList
  if !(← listTyOk (fe.find? x)) then pure false else strSup4T fe

/-- `strLitSupported` from `stringOfListTyOk`'s declaration on. -/
def strSup2T (fe : IFEnv) : AM Bool := do
  let x ← pinStringOfList
  if !(← stringOfListTyOk (fe.find? x)) then pure false else strSup3T fe

/-- `strLitSupported` from `stringTyOk`'s declaration on. -/
def strSup1T (fe : IFEnv) : AM Bool := do
  let x ← pinString
  if !(← stringTyOk (fe.find? x)) then pure false else strSup2T fe

theorem strLitSupported_eq (fe : IFEnv) :
    strLitSupported fe = (do if !(← natLitSupported fe) then pure false else strSup1T fe) := rfl

/-! ## The models, one block per call -/

/-- A call's result, as the caller returns it. -/
def nextK (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => some (r.headD 0, m)

/-- A test's result: `0`, or the next stage. -/
def guardK (p : Prog) (n : Nat) (vis : Word) (nx : FnName) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m₃) => if r.headD 0 = 0 then some (0, m₃) else nextK (callW p n nx [vis] m₃)

def checkK (p : Prog) (n : Nat) (vis : Word) (c nx : FnName) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (fq, m₂) => guardK p n vis nx (callW p n c [fq.headD 0, fq.tail.headD 0] m₂)

def findK (p : Prog) (n : Nat) (vis : Word) (c nx : FnName) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (x, m₁) => checkK p n vis c nx (callW p n "env_find" [x.headD 0, vis] m₁)

/-- The model of a guarded stage `str_sup_k` (`k ≤ 6`): pin `i`, test `c`, next stage `nx`. -/
def supW (p : Prog) (n : Nat) (m : Mem) (vis i : Word) (c nx : FnName) : Option (Word × Mem) :=
  findK p n vis c nx (callW p n "pin_at" [i] m)

def check7K (p : Prog) (n : Nat) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (fq, m₂) => nextK (callW p n "char_of_nat_ty_ok" [fq.headD 0, fq.tail.headD 0] m₂)

def find7K (p : Prog) (n : Nat) (vis : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (x, m₁) => check7K p n (callW p n "env_find" [x.headD 0, vis] m₁)

/-- The model of `str_sup_7`. -/
def sup7W (p : Prog) (n : Nat) (m : Mem) (vis : Word) : Option (Word × Mem) :=
  find7K p n vis (callW p n "pin_at" [12] m)

/-- The model of `str_lit_supported`. -/
def litW (p : Prog) (n : Nat) (m : Mem) (vis : Word) : Option (Word × Mem) :=
  guardK p n vis "str_sup_1" (callW p n "nat_lit_supported" [vis] m)

/-! ## The specs -/

theorem strSup7_spec (p : Prog) (hp : p.lookup "str_sup_7" = some strSup7L) (n : Nat) (s₀ : St)
    (vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_sup_7" [vis]
    ⦃fun r s' => LocEq s' s₀ ∧ sup7W p n s₀.mem vis = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strSup7L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "pin_at", callW_spec p n "env_find", callW_spec p n "char_of_nat_ty_ok"] <;>
    finish [sup7W, find7K, check7K, nextK]

theorem strSup1_spec (p : Prog) (hp : p.lookup "str_sup_1" = some strSup1L) (n : Nat) (s₀ : St)
    (vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_sup_1" [vis]
    ⦃fun r s' => LocEq s' s₀ ∧
      supW p n s₀.mem vis 5 "string_ty_ok" "str_sup_2" = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strSup1L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "pin_at", callW_spec p n "env_find", callW_spec p n "string_ty_ok",
      callW_spec p n "str_sup_2"] <;>
    finish [supW, findK, checkK, guardK, nextK]

theorem strSup2_spec (p : Prog) (hp : p.lookup "str_sup_2" = some strSup2L) (n : Nat) (s₀ : St)
    (vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_sup_2" [vis]
    ⦃fun r s' => LocEq s' s₀ ∧
      supW p n s₀.mem vis 6 "string_of_list_ty_ok" "str_sup_3" = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strSup2L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "pin_at", callW_spec p n "env_find", callW_spec p n "string_of_list_ty_ok",
      callW_spec p n "str_sup_3"] <;>
    finish [supW, findK, checkK, guardK, nextK]

theorem strSup3_spec (p : Prog) (hp : p.lookup "str_sup_3" = some strSup3L) (n : Nat) (s₀ : St)
    (vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_sup_3" [vis]
    ⦃fun r s' => LocEq s' s₀ ∧
      supW p n s₀.mem vis 7 "list_ty_ok" "str_sup_4" = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strSup3L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "pin_at", callW_spec p n "env_find", callW_spec p n "list_ty_ok",
      callW_spec p n "str_sup_4"] <;>
    finish [supW, findK, checkK, guardK, nextK]

theorem strSup4_spec (p : Prog) (hp : p.lookup "str_sup_4" = some strSup4L) (n : Nat) (s₀ : St)
    (vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_sup_4" [vis]
    ⦃fun r s' => LocEq s' s₀ ∧
      supW p n s₀.mem vis 8 "list_nil_ty_ok" "str_sup_5" = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strSup4L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "pin_at", callW_spec p n "env_find", callW_spec p n "list_nil_ty_ok",
      callW_spec p n "str_sup_5"] <;>
    finish [supW, findK, checkK, guardK, nextK]

theorem strSup5_spec (p : Prog) (hp : p.lookup "str_sup_5" = some strSup5L) (n : Nat) (s₀ : St)
    (vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_sup_5" [vis]
    ⦃fun r s' => LocEq s' s₀ ∧
      supW p n s₀.mem vis 9 "list_cons_ty_ok" "str_sup_6" = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strSup5L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "pin_at", callW_spec p n "env_find", callW_spec p n "list_cons_ty_ok",
      callW_spec p n "str_sup_6"] <;>
    finish [supW, findK, checkK, guardK, nextK]

theorem strSup6_spec (p : Prog) (hp : p.lookup "str_sup_6" = some strSup6L) (n : Nat) (s₀ : St)
    (vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_sup_6" [vis]
    ⦃fun r s' => LocEq s' s₀ ∧
      supW p n s₀.mem vis 10 "char_ty_ok" "str_sup_7" = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strSup6L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "pin_at", callW_spec p n "env_find", callW_spec p n "char_ty_ok",
      callW_spec p n "str_sup_7"] <;>
    finish [supW, findK, checkK, guardK, nextK]

theorem strLitSupported_spec (p : Prog) (hp : p.lookup "str_lit_supported" = some strLitSupportedL)
    (n : Nat) (s₀ : St) (vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_lit_supported" [vis]
    ⦃fun r s' => LocEq s' s₀ ∧ litW p n s₀.mem vis = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strLitSupportedL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "nat_lit_supported", callW_spec p n "str_sup_1"] <;>
    finish [litW, guardK, nextK]

/-! ## The stages -/

section stages
variable (p : Prog) (hp : StrLitProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
  {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}

/-- A test's refinement, at every state (`string_ty_ok`, …). -/
def TestRef (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb : Word)
    (c : FnName) (C : Option IConstantInfo → AM Bool) : Prop :=
  ∀ {m m' : Mem} {a : AState} {M : ModeMaps} {r : List Word} {found q : Word},
    CoreS dn m a vis fe M eb → (found ≠ 0 → ∃ ci, decCI (erecP m) dn q.toNat = some ci) →
    (∀ ci, decFound dn m found q = some ci → ∃ x, fe.find? x = some ci) →
    callW p n c [found, q] m = some (r, m') →
    CoreRef (C (decFound dn m found q)) a decBool dn m vis fe M eb r m'

/-- A stage's refinement, at every state (`str_sup_k`). -/
def StageRef (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb : Word)
    (nx : FnName) (N : AM Bool) : Prop :=
  ∀ {m m' : Mem} {a : AState} {M : ModeMaps} {r : List Word},
    CoreS dn m a vis fe M eb → callW p n nx [vis] m = some (r, m') →
    CoreRef N a decBool dn m vis fe M eb r m'

/-- **The `if` step on a verdict**: `false`, or the next stage. -/
theorem guard_tail {N : AM Bool} {nx : FnName} {rc : List Word} {m₃ : Mem} {w : Word}
    (hS₃ : CoreS dn m₃ a vis fe M eb) (hN : StageRef p n dn vis fe eb nx N)
    (h : guardK p n vis nx (some (rc, m₃)) = some (w, m')) (hr : r.headD 0 = w) :
    CoreRef (if !(decBool rc) then pure false else N) a decBool dn m₃ vis fe M eb r m' := by
  simp only [guardK] at h
  by_cases hc : rc.headD 0 = 0
  · rw [ite_eq_left hc] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [decBool_f hc]
    exact coreRef_ret hS₃ (by unfold decBool; rw [hr]; rfl) (by unfold ResH; rw [hr]; exact hw0)
  rw [ite_eq_right hc] at h
  rw [decBool_t hc]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases h4 : callW p n nx [vis] m₃ with
  | none => rw [h4] at h; cases h
  | some q₄ =>
  obtain ⟨r', m₄⟩ := q₄
  rw [h4] at h
  simp only [nextK, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hr', rfl⟩ := h
  exact strHead_ref (hr.trans hr'.symm) (hN hS₃ h4)

/-- **The `if` step**: a test's verdict, then `false` or the next stage. -/
theorem guard_ref {T N : AM Bool} {nx : FnName} {rc : List Word} {m₃ : Mem} {w : Word}
    (h₁ : CoreRef T a decBool dn m vis fe M eb rc m₃) (hN : StageRef p n dn vis fe eb nx N)
    (h : guardK p n vis nx (some (rc, m₃)) = some (w, m')) (hr : r.headD 0 = w) :
    CoreRef (do if !(← T) then pure false else N) a decBool dn m vis fe M eb r m' :=
  coreRef_bind h₁ fun _ hS₃ => guard_tail p hS₃ hN h hr

include hp

/-- **`pin_at(i)` and `env_find`, then the test**: the twin reads the pin and looks it up. -/
theorem find_ref {i : Word} (hi : i.toNat < 51) {c : FnName} {C : Option IConstantInfo → AM Bool}
    {β : Type} [Inhabited β] {g : Bool → AM β} {dec : List Word → β}
    (hC : TestRef p n dn vis fe eb c C) (hS : CoreS dn m a vis fe M eb)
    {x fq rc : List Word} {m₁ m₂ m₃ : Mem}
    (h1 : callW p n "pin_at" [i] m = some (x, m₁))
    (h2 : callW p n "env_find" [x.headD 0, vis] m₁ = some (fq, m₂))
    (h3 : callW p n c [fq.headD 0, fq.tail.headD 0] m₂ = some (rc, m₃))
    (hk : ∀ M₃, CoreS dn m₃ (AM.st (C (decFound dn m (fq.headD 0) (fq.tail.headD 0))) a) vis fe M₃ eb →
      CoreRef (g (decBool rc)) (AM.st (C (decFound dn m (fq.headD 0) (fq.tail.headD 0))) a) dec dn
        m₃ vis fe M₃ eb r m') :
    CoreRef (do let x ← pinAt i.toNat; g (← C (fe.find? x))) a dec dn m vis fe M eb r m' := by
  obtain ⟨hm1, hm2, hfind, hdec⟩ := callW_pinFind p hp.toWhnfDeltaProg' i hi n m vis ⟨M, eb, hS⟩
    x m₁ fq m₂ h1 h2
  subst m₁ m₂
  refine coreRef_congr (T' := C (decFound dn m (fq.headD 0) (fq.tail.headD 0)) >>= g) ?_
    (coreRef_bind (hC hS hdec (fun ci h => ⟨_, hfind.trans h⟩) h3) hk)
  simp only [StateT.run_bind, pinAt_run hS.pins _ hi, except_ok_bind, hfind]

/-- **A guarded stage** `str_sup_k`. -/
theorem sup_stage {i : Word} (hi : i.toNat < 51) {c nx : FnName}
    {C : Option IConstantInfo → AM Bool} {N : AM Bool}
    (hC : TestRef p n dn vis fe eb c C) (hN : StageRef p n dn vis fe eb nx N)
    (hS : CoreS dn m a vis fe M eb) {w : Word} (h : supW p n m vis i c nx = some (w, m'))
    (hr : r.headD 0 = w) :
    CoreRef (do let x ← pinAt i.toNat; if !(← C (fe.find? x)) then pure false else N) a decBool
      dn m vis fe M eb r m' := by
  unfold supW at h
  cases h1 : callW p n "pin_at" [i] m with
  | none => rw [h1] at h; cases h
  | some q₁ =>
  obtain ⟨x, m₁⟩ := q₁
  rw [h1] at h; simp only [findK] at h
  cases h2 : callW p n "env_find" [x.headD 0, vis] m₁ with
  | none => rw [h2] at h; cases h
  | some q₂ =>
  obtain ⟨fq, m₂⟩ := q₂
  rw [h2] at h; simp only [checkK] at h
  cases h3 : callW p n c [fq.headD 0, fq.tail.headD 0] m₂ with
  | none => rw [h3] at h; cases h
  | some q₃ =>
  obtain ⟨rc, m₃⟩ := q₃
  rw [h3] at h
  exact find_ref p hp hi hC hS h1 h2 h3 fun _ hS₃ => guard_tail p hS₃ hN h hr

/-- **The last stage** `str_sup_7`. -/
theorem sup7_stage (hS : CoreS dn m a vis fe M eb) {w : Word} (h : sup7W p n m vis = some (w, m'))
    (hr : r.headD 0 = w) : CoreRef (strSup7T fe) a decBool dn m vis fe M eb r m' := by
  unfold sup7W at h
  cases h1 : callW p n "pin_at" [12] m with
  | none => rw [h1] at h; cases h
  | some q₁ =>
  obtain ⟨x, m₁⟩ := q₁
  rw [h1] at h; simp only [find7K] at h
  cases h2 : callW p n "env_find" [x.headD 0, vis] m₁ with
  | none => rw [h2] at h; cases h
  | some q₂ =>
  obtain ⟨fq, m₂⟩ := q₂
  rw [h2] at h; simp only [check7K] at h
  cases h3 : callW p n "char_of_nat_ty_ok" [fq.headD 0, fq.tail.headD 0] m₂ with
  | none => rw [h3] at h; cases h
  | some q₃ =>
  obtain ⟨rc, m₃⟩ := q₃
  rw [h3] at h
  simp only [nextK, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hr', rfl⟩ := h
  obtain ⟨hm1, hm2, hfind, hdec⟩ := callW_pinFind p hp.toWhnfDeltaProg' 12 (by decide) n m vis
    ⟨M, eb, hS⟩ x m₁ fq m₂ h1 h2
  subst m₁ m₂
  refine strHead_ref (hr.trans hr'.symm) (coreRef_congr ?_ (charOfNatTyOk_call p hp hS hdec h3))
  simp only [strSup7T, pinCharOfNat, StateT.run_bind, pinAt_run hS.pins _ (by decide : PIN_CHAR_OF_NAT < 51),
    except_ok_bind]
  rw [← hfind]; rfl

end stages

/-! ## The stages as calls -/

section calls
variable (p : Prog) (hp : StrLitProg p)
include hp

theorem strSup7_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {eb : Word} : StageRef p n dn vis fe eb "str_sup_7" (strSup7T fe) := by
  intro m m' a M r hS h
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (strSup7_spec p hp.strSup7 n _ vis) h
  exact sup7_stage p hp hS hW rfl

theorem strSup6_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {eb : Word} : StageRef p n dn vis fe eb "str_sup_6" (strSup6T fe) := by
  intro m m' a M r hS h
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (strSup6_spec p hp.strSup6 n _ vis) h
  exact sup_stage p hp (i := 10) (by decide) (fun hS hdec _ h => charTyOk_call p hp hS hdec h)
    (strSup7_call p hp) hS hW rfl

theorem strSup5_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {eb : Word} : StageRef p n dn vis fe eb "str_sup_5" (strSup5T fe) := by
  intro m m' a M r hS h
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (strSup5_spec p hp.strSup5 n _ vis) h
  exact sup_stage p hp (i := 9) (by decide) (fun hS hdec hfe h => listConsTyOk_call p hp hS hdec hfe h)
    (strSup6_call p hp) hS hW rfl

theorem strSup4_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {eb : Word} : StageRef p n dn vis fe eb "str_sup_4" (strSup4T fe) := by
  intro m m' a M r hS h
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (strSup4_spec p hp.strSup4 n _ vis) h
  exact sup_stage p hp (i := 8) (by decide) (fun hS hdec hfe h => listNilTyOk_call p hp hS hdec hfe h)
    (strSup5_call p hp) hS hW rfl

theorem strSup3_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {eb : Word} : StageRef p n dn vis fe eb "str_sup_3" (strSup3T fe) := by
  intro m m' a M r hS h
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (strSup3_spec p hp.strSup3 n _ vis) h
  exact sup_stage p hp (i := 7) (by decide) (fun hS hdec hfe h => listTyOk_call p hp hS hdec hfe h)
    (strSup4_call p hp) hS hW rfl

theorem strSup2_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {eb : Word} : StageRef p n dn vis fe eb "str_sup_2" (strSup2T fe) := by
  intro m m' a M r hS h
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (strSup2_spec p hp.strSup2 n _ vis) h
  exact sup_stage p hp (i := 6) (by decide) (fun hS hdec _ h => stringOfListTyOk_call p hp hS hdec h)
    (strSup3_call p hp) hS hW rfl

theorem strSup1_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {eb : Word} : StageRef p n dn vis fe eb "str_sup_1" (strSup1T fe) := by
  intro m m' a M r hS h
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (strSup1_spec p hp.strSup1 n _ vis) h
  exact sup_stage p hp (i := 5) (by decide) (fun hS hdec _ h => stringTyOk_call p hp hS hdec h)
    (strSup2_call p hp) hS hW rfl

/-- **`str_lit_supported` as a call.** -/
theorem strLitSupported_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {eb : Word} : StageRef p n dn vis fe eb "str_lit_supported" (strLitSupported fe) := by
  intro m m' a M r hS h
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (strLitSupported_spec p hp.strLitSupported n _ vis) h
  unfold litW at hW
  cases h1 : callW p n "nat_lit_supported" [vis] m with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨rn, m₁⟩ := q₁
  rw [h1] at hW
  rw [strLitSupported_eq]
  exact guard_ref p (callW_natLitSupported p hp.toWhnfDeltaProg' n ⟨m, Locals.init []⟩ a dn vis fe M
    eb hS rn m₁ h1).core (strSup1_call p hp) hW rfl

/-- **`str_lit_supported(vis)` refines `strLitSupported fe`.** -/
@[refines ConRon.Arena.strLitSupported]
theorem strLitSupported_core : StrLitSupportedOK p := fun _ _ _ _ _ _ _ _ hS =>
  CoreSpec.of_call fun _ _ h => strLitSupported_call p hp hS h

end calls

end L.Arena
