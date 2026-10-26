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
  obtain ⟨hm1, -, hr1⟩ := callW_pinWord p hp.pinWord n m 53 r₁ m₁ h1
  have c2 := ls1_call p hp hS₁ c1.2.2.2 (zero_den hS₁ (by rw [hr1, hm1])) h2
  refine coreRef_bind c2 fun M₂ hS₂ => ?_
  have c3 := pinAt_call p hp hS₂ (k := 10) rfl h3
  refine coreRef_bind c3 fun M₃ hS₃ => ?_
  have c4 := constE_call p hp hS₃ c3.2.2.2 h4
  refine coreRef_bind c4 fun M₄ hS₄ => ?_
  have c5 := pinAt_call p hp hS₄ (k := 8) rfl h5
  refine coreRef_bind c5 fun M₅ hS₅ => ?_
  have hd2 := ls1_den p hp hS₁ c1.2.2.2 h2 (zero_den hS₁ (by rw [hr1, hm1]))
  have hd5 := lss_den (op := pinListNil) (lss_den (lss_den (op := pinChar) hd2 (keeps_cpl_pinAt _)
    c3 rfl) (keeps_cpl_constE _) c4 rfl) (keeps_cpl_pinAt _) c5 rfl
  have c6 := const_call p hp hS₅ c5.2.2.2 c2.2.2.2 h6 hd5
  refine coreRef_bind c6 fun M₆ hS₆ => ?_
  have c7 := app_call p hp hS₆ h7
  refine coreRef_bind c7 fun M₇ hS₇ => ?_
  have c8 := pinAt_call p hp hS₇ (k := 9) rfl h8
  refine coreRef_bind c8 fun M₈ hS₈ => ?_
  have t8 := lss_den (op := pinListCons) (lss_den (op := internE (.app (decH r₆) (decH r₄)))
    (lss_den (op := internE (.const (decI (r₅.headD 0)) (decLs r₂))) hd5 (keeps_cpl_internConst _ _)
      c6 rfl) (keeps_cpl_internApp _ _) c7 rfl) (keeps_cpl_pinAt _) c8 rfl
  have c9 := const_call p hp hS₈ c8.2.2.2 c2.2.2.2 h9 t8
  refine coreRef_bind c9 fun M₉ hS₉ => ?_
  have c10 := app_call p hp hS₉ h10
  refine coreRef_bind c10 fun M₁₀ hS₁₀ => ?_
  have c11 := pinAt_call p hp hS₁₀ (k := 12) rfl h11
  refine coreRef_bind c11 fun M₁₁ hS₁₁ => ?_
  have c12 := constE_call p hp hS₁₁ c11.2.2.2 h12
  refine coreRef_bind c12 fun M₁₂ hS₁₂ => ?_
  exact coreRef_ret hS₁₂ rfl ⟨c10.2.2.2, c12.2.2.2, c7.2.2.2⟩

end pre

/-! ## `str_cons_spine` -/

/-- The model of `str_cons_spine`. -/
def spineW (p : Prog) (n : Nat) (m : Mem) (cons ofNat nilE k e : Word) : Option (Word × Mem) :=
  if e ≤ k then some (nilE, m)
  else match callW p n "str_utf8_char" [k, e] m with
  | none => none
  | some (cl, m₁) =>
  if cl.tail.headD 0 = 0 then none
  else match callW p n "str_cons_spine" [cons, ofNat, nilE, k + cl.tail.headD 0, e] m₁ with
  | none => none
  | some (rr, m₂) =>
  match callW p n "rom_lit" [cl.headD 0] m₂ with
  | none => none
  | some (lt, m₃) =>
  match callW p n "mk_app" [ofNat, lt.headD 0] m₃ with
  | none => none
  | some (ch, m₄) =>
  match callW p n "mk_app" [cons, ch.headD 0] m₄ with
  | none => none
  | some (f, m₅) =>
  match callW p n "mk_app" [f.headD 0, rr.headD 0] m₅ with
  | none => none
  | some (r, m₆) => some (r.headD 0, m₆)

theorem strConsSpine_spec (p : Prog) (hp : p.lookup "str_cons_spine" = some strConsSpineL)
    (n : Nat) (s₀ : St) (cons ofNat nilE k e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_cons_spine" [cons, ofNat, nilE, k, e]
    ⦃fun r s' => LocEq s' s₀ ∧ spineW p n s₀.mem cons ofNat nilE k e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strConsSpineL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "str_utf8_char", callW_spec p n "str_cons_spine", callW_spec p n "rom_lit",
      callW_spec p n "mk_app"] <;>
    finish (gen := 20) [spineW]

theorem sliceL_drop (q : Array Word) (o a b : Nat) :
    (sliceL q o (a + b)).drop a = sliceL q (o + a) b := by
  apply List.ext_getElem
  · simp [sliceL_length]
  · intro i h1 h2
    simp [sliceL, Nat.add_assoc]

theorem charWords_drop (c : Char) (cs : List Char) :
    (charWords (c :: cs)).drop c.utf8Size = charWords cs := by
  rw [charWords_cons, List.drop_append_of_le_length (by simp)]
  simp

section spine
variable (p : Prog) (hp : StrLitProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {eb : Word}
include hp

/-- **`str_cons_spine` refines `strLitConsSpine`** on the characters whose bytes are the pool
words `[k, e)`. -/
@[refines ConRon.Arena.strLitConsSpine]
theorem spine_call (cons ofNat nilE : Word) (hn : HW nilE) :
    ∀ (cs : List Char) (n : Nat) (m m' : Mem) (a : AState) (M : ModeMaps) (k e : Word)
      (r : List Word), CoreS dn m a vis fe M eb →
      sliceL (vpool m) k.toNat (e.toNat - k.toNat) = charWords cs → k.toNat ≤ e.toNat →
      e.toNat ≤ pcap m → e.toNat + 4 < 2 ^ 64 →
      callW p n "str_cons_spine" [cons, ofNat, nilE, k, e] m = some (r, m') →
      CoreRef (strLitConsSpine (decE cons) (decE ofNat) (decE nilE) cs) a decH dn m vis fe M eb
        r m' := by
  intro cs
  induction cs with
  | nil =>
    intro n m m' a M k e r hS hs hke he he4 h
    cases n with
    | zero => rw [callW_zero] at h; cases h
    | succ n =>
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (strConsSpine_spec p hp.strConsSpine n _ cons ofNat nilE k e) h
    have hlen := congrArg List.length hs
    rw [sliceL_length, charWords_nil] at hlen
    have hle : e ≤ k := UInt64.le_iff_toNat_le.mpr (by simp at hlen; omega)
    simp only [spineW, hle, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    exact cref_run (v := decE nilE) rfl (coreAfter_refl hS) (by rw [decH, ← hr])
      (by unfold ResH; rw [← hr]; exact hn)
  | cons c cs ih =>
    intro n m m' a M k e r hS hs hke he he4 h
    cases n with
    | zero => rw [callW_zero] at h; cases h
    | succ n =>
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (strConsSpine_spec p hp.strConsSpine n _ cons ofNat nilE k e) h
    have hlen := congrArg List.length hs
    rw [sliceL_length, charWords_length_cons] at hlen
    have hu1 := Char.utf8Size_pos c
    have hu4 := Char.utf8Size_le_four c
    have hnle : ¬ e ≤ k := fun h' => by
      have := UInt64.le_iff_toNat_le.mp h'; omega
    simp only [spineW, hnle, ↓reduceIte] at hW
    wstep hW, h1 : callW p n "str_utf8_char" [k, e] m => cl, m₁
    obtain ⟨hm1, hc0, hc1⟩ := strUtf8Char_callW p hp.strUtf8Char n m k e c cs
      (by rw [sliceL_tpool m _ _ (by have := pcap_ge m; have := pcap_eq m (by have := hS.arena.1.lit.1.2.2.1; omega); omega)]; exact hs) hke
      (by rw [tpool_size]; exact Nat.le_of_lt e.toNat_lt) he4 cl m₁ h1
    rw [hm1] at hW
    have hne : ¬ cl.tail.headD 0 = 0 := by
      rw [hc1]; intro h0
      have := congrArg UInt64.toNat h0
      simp [UInt64.toNat_ofNat_of_lt' (show c.utf8Size < 2 ^ 64 by omega)] at this; omega
    simp only [hne, ↓reduceIte] at hW
    wstep hW, h2 : callW p n "str_cons_spine" [cons, ofNat, nilE, k + cl.tail.headD 0, e] m => rr, m₂
    wstep hW, h3 : callW p n "rom_lit" [cl.headD 0] m₂ => lt, m₃
    wstep hW, h4 : callW p n "mk_app" [ofNat, lt.headD 0] m₃ => ch, m₄
    wstep hW, h5 : callW p n "mk_app" [cons, ch.headD 0] m₄ => fw, m₅
    wstep hW, h6 : callW p n "mk_app" [fw.headD 0, rr.headD 0] m₅ => r₆, m₆
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    have hk' : (k + cl.tail.headD 0).toNat = k.toNat + c.utf8Size := by
      rw [hc1, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (show c.utf8Size < 2 ^ 64 by omega)]
      omega
    have hs' : sliceL (vpool m) (k + cl.tail.headD 0).toNat
        (e.toNat - (k + cl.tail.headD 0).toNat) = charWords cs := by
      rw [hk', ← charWords_drop, ← hs, ← sliceL_drop]
      congr 2; omega
    have c2 := ih n m m₂ a M _ e rr hS hs' (by rw [hk']; omega) he he4 h2
    have hcn : (cl.headD 0).toNat = c.toNat := by
      rw [hc0, UInt32.toNat_toUInt64]; rfl
    rw [strLitConsSpine]
    refine coreRef_bind c2 fun M₂ hS₂ => ?_
    have c3 := romLit_call p hp hS₂ h3
    rw [hcn] at c3
    refine coreRef_bind c3 fun M₃ hS₃ => ?_
    have c4 := app_call p hp hS₃ h4
    refine coreRef_bind c4 fun M₄ hS₄ => ?_
    have c5 := app_call p hp hS₄ h5
    refine coreRef_bind c5 fun M₅ hS₅ => ?_
    have c6 := app_call p hp hS₅ h6
    refine ⟨c6.1, c6.2.1, ?_, by unfold ResH; rw [← hr]; exact c6.2.2.2⟩
    have := c6.2.2.1
    simp only [decH] at this ⊢
    rw [this, ← hr]

end spine

/-! ## `str_lit_ctor` -/

/-- The model of `str_lit_ctor` (`o`, `cnt`: the literal's record, read after the prefix). -/
def strCtorW (p : Prog) (n : Nat) (m : Mem) (h : Word) : Option (Word × Mem) :=
  match callW p n "str_ctor_pre" [] m with
  | none => none
  | some (t, m₁) =>
  if h >>> 28 ≠ 8 then none
  else if tierW h ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0 then none
  else if tcnt m₁ LIT (tierW h) ≤ idxW h then none
  else if tfld m₁ LIT (tierW h) (idxW h) 0 ≠ 1 then none
  else match callW p n "str_cons_spine" [t.headD 0, t.tail.headD 0, t.tail.tail.headD 0,
      tfld m₁ LIT (tierW h) (idxW h) 1,
      tfld m₁ LIT (tierW h) (idxW h) 1 +
        tfld m₁ LIT (tierW h) (idxW h) 2] m₁ with
  | none => none
  | some (sp, m₂) =>
  match callW p n "pin_at" [6] m₂ with
  | none => none
  | some (q, m₃) =>
  match callW p n "const_e" [q.headD 0] m₃ with
  | none => none
  | some (sl, m₄) =>
  match callW p n "mk_app" [sl.headD 0, sp.headD 0] m₄ with
  | none => none
  | some (r, m₅) => some (r.headD 0, m₅)

theorem strLitCtor_spec (p : Prog) (hp : p.lookup "str_lit_ctor" = some strLitCtorL) (n : Nat)
    (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_lit_ctor" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ strCtorW p n s₀.mem h = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strLitCtorL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "str_ctor_pre", callW_spec p n "str_cons_spine", callW_spec p n "pin_at",
      callW_spec p n "const_e", callW_spec p n "mk_app", evalE_tld, tld, evalE_cnt, tcntM,
        evalE_tierE, evalE_idxE] <;>
    finish (gen := 20) [strCtorW, tierW, idxW]

section ctor
variable (p : Prog) (hp : StrLitProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
  {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
include hp

theorem ctor_call (hS : CoreS dn m a vis fe M eb) {h : Word} (hh : HW h) {s : String}
    (hv : a.store.view (decE h) = some (.lit (.strVal s)))
    (hc : callW p n "str_lit_ctor" [h] m = some (r, m')) :
    CoreRef (strLitToConstructor s) a decH dn m vis fe M eb r m' := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (strLitCtor_spec p hp.strLitCtor n _ h) hc
  unfold strCtorW at hW
  wstep hW, h1 : callW p n "str_ctor_pre" [] m => t, m₁
  by_cases g8 : h >>> 28 ≠ 8
  · rw [if_pos g8] at hW; cases hW
  rw [if_neg g8] at hW
  by_cases gs : tierW h ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0
  · rw [if_pos gs] at hW; cases hW
  rw [if_neg gs] at hW
  by_cases gb : tcnt m₁ LIT (tierW h) ≤ idxW h
  · rw [if_pos gb] at hW; cases hW
  rw [if_neg gb] at hW
  by_cases gk : tfld m₁ LIT (tierW h) (idxW h) 0 ≠ 1
  · rw [if_pos gk] at hW; cases hW
  rw [if_neg gk] at hW
  wstep hW, h2 : callW p n "str_cons_spine" [t.headD 0, t.tail.headD 0, t.tail.tail.headD 0,
      tfld m₁ LIT (tierW h) (idxW h) 1,
      tfld m₁ LIT (tierW h) (idxW h) 1 +
        tfld m₁ LIT (tierW h) (idxW h) 2] m₁ => sp, m₂
  wstep hW, h3 : callW p n "pin_at" [6] m₂ => q, m₃
  wstep hW, h4 : callW p n "const_e" [q.headD 0] m₃ => sl, m₄
  wstep hW, h5 : callW p n "mk_app" [sl.headD 0, sp.headD 0] m₄ => r₅, m₅
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [← hm, strLitToConstructor_eq]
  have c1 := pre_call p hp hS h1
  refine coreRef_bind c1 fun M₁ hS₁ => ?_
  -- the literal is still there, and its record gives the bytes
  have hv₁ : (AM.st ctorPreT a).store.view (decE h) = some (.lit (.strVal s)) :=
    vmono_ctorPreT.run (AM.run_of_ok _ _ c1.1) hv
  have g8' : h >>> 28 = 8 := by simpa using g8
  have hvOK : viewOK m₁ h LIT := ⟨gs, by simpa using gb⟩
  obtain ⟨htop, -, hstr⟩ := lit_rec m₁ _ hS₁.arena.1 h hh hvOK g8' _ hv₁
  obtain ⟨-, hsl⟩ := hstr s rfl
  have hpool := hS₁.arena.1.lit.1
  have hsize := hpool.2.2.1
  have htop' := hpool.2.2.2
  have hoc : (tfld m₁ LIT (tierW h) (idxW h) 1 +
      tfld m₁ LIT (tierW h) (idxW h) 2).toNat =
      (tfld m₁ LIT (tierW h) (idxW h) 1).toNat +
      (tfld m₁ LIT (tierW h) (idxW h) 2).toNat := by
    rw [UInt64.toNat_add]; omega
  unfold ctorRestT
  have c2 := spine_call p hp (t.headD 0) (t.tail.headD 0) (t.tail.tail.headD 0) c1.2.2.2.2.2
    s.toList n m₁ m₂ _ M₁ _ _ sp hS₁ (by rw [hoc, Nat.add_sub_cancel_left, hsl, strWords_eq])
    (by rw [hoc]; omega) (by rw [hoc]; omega) (by rw [hoc]; omega) h2
  refine coreRef_bind c2 fun M₂ hS₂ => ?_
  have c3 := pinAt_call p hp hS₂ (k := 6) rfl h3
  refine coreRef_bind c3 fun M₃ hS₃ => ?_
  have c4 := constE_call p hp hS₃ c3.2.2.2 h4
  refine coreRef_bind c4 fun M₄ hS₄ => ?_
  have c5 := app_call p hp hS₄ h5
  refine ⟨c5.1, c5.2.1, ?_, by unfold ResH; rw [← hr]; exact c5.2.2.2⟩
  have := c5.2.2.1
  simp only [decH] at this ⊢
  rw [this, ← hr]

end ctor

/-- **`str_lit_ctor` refines `strLitToConstructor`** at a string literal, from the program's
lookups. -/
@[refines ConRon.Arena.strLitToConstructor]
theorem strLitCtor_core (p : Prog) (hp : StrLitProg p) : StrLitCtorOK p := by
  intro n s₀ a₀ dn vis fe M eb h s hS hh hv
  exact CoreSpec.of_call fun r m' hc => ctor_call p hp hS hh hv hc

end L.Arena
