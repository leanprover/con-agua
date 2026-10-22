import ConAgua.Arena.StrLitTy
import ConAgua.Arena.StrLitUtf8
import ConAgua.Arena.StrLitKeep

/-!
# `str_lit_ctor` refines `strLitToConstructor` (helper `defeq2-str`)

* `str_ctor_pre()`: the literal-independent prefix (`ctorPreT`), a chain of twelve calls.
* `str_cons_spine(cons, ofNat, nilE, k, e)`: `strLitConsSpine` over the characters whose UTF-8
  bytes are the pool words `[k, e)` (`charWords`), by induction on the characters; one character
  is decoded by `str_utf8_char` (`strUtf8Char_callW`, `StrLitUtf8.lean`).
* `str_lit_ctor(h)`: the prefix, the literal's record at the memory after it (the twin's store
  still views `h` as the literal: `VMono`, `StrLitKeep.lean`), the spine, `String.ofList`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace L.Arena

/-- One call of a word model's chain: split on the callee's run. -/
macro "wstep " hW:ident ", " h:ident " : " e:term " => " r:ident ", " m:ident : tactic =>
  `(tactic| (rcases $h:ident : $e with _ | ⟨$r, $m⟩ <;> rw [$h:ident] at $hW:ident <;>
    dsimp only at $hW:ident <;> try (cases $hW:ident; done)))

/-! ## The twin, in the L code's pieces -/

/-- The literal-independent prefix of `strLitToConstructor`. -/
def ctorPreT : AM (EIdx × EIdx × EIdx) := do
  let z ← zeroLevel
  let zs ← internLsNode [z]
  let chN ← pinChar
  let chC ← constE chN
  let lnN ← pinListNil
  let ln ← internE (.const lnN zs)
  let nilE ← internE (.app ln chC)
  let lcN ← pinListCons
  let lc ← internE (.const lcN zs)
  let cons ← internE (.app lc chC)
  let coN ← pinCharOfNat
  let ofNat ← constE coN
  pure (cons, ofNat, nilE)

/-- The rest of `strLitToConstructor`. -/
def ctorRestT (cons ofNat nilE : EIdx) (s : String) : AM EIdx := do
  let spine ← strLitConsSpine cons ofNat nilE s.toList
  let slN ← pinStringOfList
  let sl ← constE slN
  internE (.app sl spine)

theorem strLitToConstructor_eq (s : String) :
    strLitToConstructor s = ctorPreT >>= fun t => ctorRestT t.1 t.2.1 t.2.2 s := by
  simp only [strLitToConstructor, ctorPreT, ctorRestT, bind_assoc, pure_bind]

theorem vmono_ctorPreT : VMono ctorPreT := by
  unfold ctorPreT zeroLevel pinChar pinListNil pinListCons pinCharOfNat
  refine VMono.bind vmono_pinZeroLevel fun _ => VMono.bind (vmono_internLsNode _) fun _ =>
    VMono.bind (vmono_pinAt _) fun _ => VMono.bind (vmono_constE _) fun _ =>
    VMono.bind (vmono_pinAt _) fun _ => VMono.bind (vmono_internE _) fun _ =>
    VMono.bind (vmono_internE _) fun _ => VMono.bind (vmono_pinAt _) fun _ =>
    VMono.bind (vmono_internE _) fun _ => VMono.bind (vmono_internE _) fun _ =>
    VMono.bind (vmono_pinAt _) fun _ => VMono.bind (vmono_constE _) fun _ => VMono.pure _

theorem VMono.run {α : Type} {op : AM α} (h : VMono op) {a a' : AState} {r : α}
    (hr : op.run a = .ok (r, a')) {i : EIdx} {v : ENodeView} (hv : a.store.view i = some v) :
    a'.store.view i = some v := by
  unfold VMono at h; exact h a r a' hr i v hv

/-! ## Pin reads as calls -/

/-- The three handles of `str_ctor_pre`. -/
def dec3 (r : List Word) : EIdx × EIdx × EIdx :=
  (decE (r.headD 0), decE (r.tail.headD 0), decE (r.tail.tail.headD 0))

section pins
variable (p : Prog) (hp : StrLitProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
  {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
include hp

theorem pinAt_call (hS : CoreS dn m a vis fe M eb) {w : Word} {k : Nat} (hw : w.toNat = k)
    (h : callW p n "pin_at" [w] m = some (r, m')) :
    CoreRef (pinAt k) a (fun r => decI (r.headD 0)) dn m vis fe M eb r m' := by
  obtain ⟨rfl, -, hk, hr⟩ := callW_pinAt p hp.pinAt n m w r m' h
  rw [hw] at hk hr
  exact cref_run (pinAt_run hS.pins k hk) (coreAfter_refl hS) (by rw [hr])
    (by unfold ResH; rw [hr]; exact hS.pins.names_lt k hk)

theorem pinZero_call (hS : CoreS dn m a vis fe M eb)
    (h : callW p n "pin_word" [53] m = some (r, m')) :
    CoreRef zeroLevel a (fun r => decI (r.headD 0)) dn m vis fe M eb r m' := by
  obtain ⟨rfl, -, hr⟩ := callW_pinWord p hp.pinWord n m 53 r m' h
  exact cref_run (pinZeroLevel_run hS.pins) (coreAfter_refl hS) (by rw [hr]; rfl)
    (by unfold ResH; rw [hr]; exact hS.pins.lv_lt.2.1)

end pins

/-! ## `str_ctor_pre` -/

/-- The model of `str_ctor_pre`. -/
def preW (p : Prog) (n : Nat) (m : Mem) : Option (List Word × Mem) :=
  match callW p n "pin_word" [53] m with
  | none => none
  | some (r₁, m₁) =>
  match callW p n "str_ls1" [r₁.headD 0] m₁ with
  | none => none
  | some (r₂, m₂) =>
  match callW p n "pin_at" [10] m₂ with
  | none => none
  | some (r₃, m₃) =>
  match callW p n "const_e" [r₃.headD 0] m₃ with
  | none => none
  | some (r₄, m₄) =>
  match callW p n "pin_at" [8] m₄ with
  | none => none
  | some (r₅, m₅) =>
  match callW p n "intern_const" [r₅.headD 0, r₂.headD 0] m₅ with
  | none => none
  | some (r₆, m₆) =>
  match callW p n "mk_app" [r₆.headD 0, r₄.headD 0] m₆ with
  | none => none
  | some (r₇, m₇) =>
  match callW p n "pin_at" [9] m₇ with
  | none => none
  | some (r₈, m₈) =>
  match callW p n "intern_const" [r₈.headD 0, r₂.headD 0] m₈ with
  | none => none
  | some (r₉, m₉) =>
  match callW p n "mk_app" [r₉.headD 0, r₄.headD 0] m₉ with
  | none => none
  | some (r₁₀, m₁₀) =>
  match callW p n "pin_at" [12] m₁₀ with
  | none => none
  | some (r₁₁, m₁₁) =>
  match callW p n "const_e" [r₁₁.headD 0] m₁₁ with
  | none => none
  | some (r₁₂, m₁₂) => some ([r₁₀.headD 0, r₁₂.headD 0, r₇.headD 0], m₁₂)

theorem strCtorPre_spec (p : Prog) (hp : p.lookup "str_ctor_pre" = some strCtorPreL) (n : Nat)
    (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_ctor_pre" []
    ⦃fun r s' => LocEq s' s₀ ∧ preW p n s₀.mem = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strCtorPreL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "pin_word", callW_spec p n "str_ls1", callW_spec p n "pin_at",
      callW_spec p n "const_e", callW_spec p n "intern_const", callW_spec p n "mk_app"] <;>
    finish (gen := 30) [preW]

section pre
variable (p : Prog) (hp : StrLitProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
  {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
include hp

theorem pre_call (hS : CoreS dn m a vis fe M eb)
    (h : callW p n "str_ctor_pre" [] m = some (r, m')) :
    CoreRef ctorPreT a dec3 dn m vis fe M eb r m' Res3 := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (strCtorPre_spec p hp.strCtorPre n _) h
  unfold preW at hW
  wstep hW, h1 : callW p n "pin_word" [53] m => r₁, m₁
  wstep hW, h2 : callW p n "str_ls1" [r₁.headD 0] m₁ => r₂, m₂
  wstep hW, h3 : callW p n "pin_at" [10] m₂ => r₃, m₃
  wstep hW, h4 : callW p n "const_e" [r₃.headD 0] m₃ => r₄, m₄
  wstep hW, h5 : callW p n "pin_at" [8] m₄ => r₅, m₅
  wstep hW, h6 : callW p n "intern_const" [r₅.headD 0, r₂.headD 0] m₅ => r₆, m₆
  wstep hW, h7 : callW p n "mk_app" [r₆.headD 0, r₄.headD 0] m₆ => r₇, m₇
  wstep hW, h8 : callW p n "pin_at" [9] m₇ => r₈, m₈
  wstep hW, h9 : callW p n "intern_const" [r₈.headD 0, r₂.headD 0] m₈ => r₉, m₉
  wstep hW, h10 : callW p n "mk_app" [r₉.headD 0, r₄.headD 0] m₉ => r₁₀, m₁₀
  wstep hW, h11 : callW p n "pin_at" [12] m₁₀ => r₁₁, m₁₁
  wstep hW, h12 : callW p n "const_e" [r₁₁.headD 0] m₁₁ => r₁₂, m₁₂
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, hm⟩ := hW
  rw [← hm]
  have c1 := pinZero_call p hp hS h1
  refine coreRef_bind c1 fun M₁ hS₁ => ?_
  have c2 := ls1_call p hp hS₁ c1.2.2.2 h2
  refine coreRef_bind c2 fun M₂ hS₂ => ?_
  have c3 := pinAt_call p hp hS₂ (k := 10) rfl h3
  refine coreRef_bind c3 fun M₃ hS₃ => ?_
  have c4 := constE_call p hp hS₃ c3.2.2.2 h4
  refine coreRef_bind c4 fun M₄ hS₄ => ?_
  have c5 := pinAt_call p hp hS₄ (k := 8) rfl h5
  refine coreRef_bind c5 fun M₅ hS₅ => ?_
  have c6 := const_call p hp hS₅ c5.2.2.2 c2.2.2.2 h6
  refine coreRef_bind c6 fun M₆ hS₆ => ?_
  have c7 := app_call p hp hS₆ h7
  refine coreRef_bind c7 fun M₇ hS₇ => ?_
  have c8 := pinAt_call p hp hS₇ (k := 9) rfl h8
  refine coreRef_bind c8 fun M₈ hS₈ => ?_
  have c9 := const_call p hp hS₈ c8.2.2.2 c2.2.2.2 h9
  refine coreRef_bind c9 fun M₉ hS₉ => ?_
  have c10 := app_call p hp hS₉ h10
  refine coreRef_bind c10 fun M₁₀ hS₁₀ => ?_
  have c11 := pinAt_call p hp hS₁₀ (k := 12) rfl h11
  refine coreRef_bind c11 fun M₁₁ hS₁₁ => ?_
  have c12 := constE_call p hp hS₁₁ c11.2.2.2 h12
  refine coreRef_bind c12 fun M₁₂ hS₁₂ => ?_
  exact coreRef_ret hS₁₂ rfl ⟨c10.2.2.2, c12.2.2.2, c7.2.2.2⟩

end pre

end L.Arena
