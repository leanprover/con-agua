module

public import ConAgua.L.Logic
public import ConAgua.L.Blocks

@[expose] public section

/-!
# What every L run keeps: the byte arrays (without byte stores) and the array sizes

L arrays have fixed lengths (`Mem`), and a program without `st8` never writes a byte array. So a
run keeps `Keep m m'`: the same byte arrays, and every word array of the same size. A driver that
calls a function in a loop can carry facts about the input buffer and the arrays' sizes through
the calls without the callee's spec mentioning them (`Triple.keep`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L

/-- No byte store in a statement. -/
def Stmt.noSt8 : Stmt → Bool
  | .st8 .. => false
  | .seq s t => s.noSt8 && t.noSt8
  | .ite _ s t => s.noSt8 && t.noSt8
  | .while _ s => s.noSt8
  | _ => true

/-- No byte store in any function of a program. -/
def Prog.noSt8 (p : Prog) : Bool := p.all fun f => f.2.body.noSt8

/-- The byte arrays are the same and every word array has the same size. -/
def Keep (m m' : Mem) : Prop := m'.bytes = m.bytes ∧ ∀ a, (m'.arr64 a).size = (m.arr64 a).size

@[simp] theorem St.setLocs_mem' (s : St) (xs : List Var) (vs : List Word) :
    (s.setLocs xs vs).mem = s.mem := by
  induction xs generalizing s vs with
  | nil => rfl
  | cons x xs ih => simp only [St.setLocs]; rw [ih]; rfl

theorem Keep.refl (m : Mem) : Keep m m := ⟨rfl, fun _ => rfl⟩

theorem Keep.trans {m₁ m₂ m₃ : Mem} (h₁ : Keep m₁ m₂) (h₂ : Keep m₂ m₃) : Keep m₁ m₃ :=
  ⟨h₂.1.trans h₁.1, fun a => (h₂.2 a).trans (h₁.2 a)⟩

theorem Keep.arr8 {m m' : Mem} (h : Keep m m') (a : ArrId) : m'.arr8 a = m.arr8 a := by
  simp only [Mem.arr8, h.1]
theorem Keep.size {m m' : Mem} (h : Keep m m') (a : ArrId) : (m'.arr64 a).size = (m.arr64 a).size :=
  h.2 a
grind_pattern [lang_grind] Keep.arr8 => Keep m m', m'.arr8 a
grind_pattern [lang_grind] Keep.size => Keep m m', m'.arr64 a

theorem Keep.set64 {m m' : Mem} (h : Keep m m') (a : ArrId) (i v : Word) : Keep m (m'.set64 a i v) := by
  refine ⟨h.1, fun b => ?_⟩
  rw [← h.2 b]
  simp only [Mem.set64, Mem.arr64]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases hb : a = b
  · subst hb
    by_cases ha : a < m'.words.size <;> simp [ha]
  · simp [hb]

theorem Keep.copy64 {m m' : Mem} (h : Keep m m') (d : ArrId) (di : Word) (s : ArrId) (si : Word)
    (n : Nat) : Keep m (m'.copy64 d di s si n) := by
  induction n generalizing m' di si with
  | zero => exact h
  | succ n ih => exact ih (h.set64 _ _ _) _ _

theorem Keep.copy8w {m m' : Mem} (h : Keep m m') (d : ArrId) (di : Word) (b : Array UInt8) (si : Word)
    (n : Nat) : Keep m (m'.copy8w d di b si n) := by
  induction n generalizing m' di si with
  | zero => exact h
  | succ n ih => exact ih (h.set64 _ _ _) _ _

theorem Keep.setG {m m' : Mem} (h : Keep m m') (g : GVar) (v : Word) : Keep m (m'.setG g v) := h

theorem Prog.noSt8_lookup {p : Prog} (hp : p.noSt8 = true) {f : FnName} {fd : FunDecl}
    (h : p.lookup f = some fd) : fd.body.noSt8 = true := by
  induction p with
  | nil => simp at h
  | cons x xs ih =>
    obtain ⟨g, d⟩ := x
    simp only [Prog.noSt8, List.all_cons, Bool.and_eq_true] at hp
    by_cases hg : f = g
    · subst hg; simp at h; subst h; exact hp.1
    · have : (List.lookup f ((g, d) :: xs)) = List.lookup f xs := by
        simp [List.lookup, show (f == g) = false by simpa using hg]
      rw [this] at h
      exact ih hp.2 h

/-! ## Expressions do not change the state -/

theorem evalE_same (e : Expr) (s₀ : St) : ⦃fun s => s = s₀⦄ evalE e ⦃fun _ s => s = s₀; ⊤⦄ := by
  induction e with
  | const w => vcgen [evalE] <;> grind
  | var x => vcgen [evalE] <;> grind
  | bin op a b iha ihb => vcgen [evalE, iha, ihb] <;> grind
  | ld8 a i ih => vcgen [evalE, ih, ld8] <;> grind
  | ld64 a i ih => vcgen [evalE, ih, ld64] <;> grind
  | len8 a => vcgen [evalE] <;> grind
  | len64 a => vcgen [evalE] <;> grind
  | cmpw c a b iha ihb => vcgen [evalE, iha, ihb] <;> grind
  | ldc d i ih => vcgen [evalE, ih, ldc] <;> grind
  | glob g => vcgen [evalE] <;> grind
  | ld64t a t i iht ihi => vcgen [evalE, iht, ihi, ld64] <;> grind
  | len64t a t ih => vcgen [evalE, ih] <;> grind
  | ld8x8 b i ih => vcgen [evalE, ih, ld8x8] <;> grind

theorem warr_same (w : WArr) (s₀ : St) : ⦃fun s => s = s₀⦄ warr w ⦃fun _ s => s = s₀; ⊤⦄ := by
  cases w with
  | plain a => vcgen [warr] <;> grind
  | tier a t => vcgen [warr, evalE_same t] <;> grind

theorem evalC_same (c : Cond) (s₀ : St) : ⦃fun s => s = s₀⦄ evalC c ⦃fun _ s => s = s₀; ⊤⦄ := by
  induction c with
  | cmp c a b => vcgen [evalC, evalE_same a, evalE_same b] <;> grind
  | and p q ihp ihq => vcgen [evalC, ihp, ihq] <;> grind
  | or p q ihp ihq => vcgen [evalC, ihp, ihq] <;> grind
  | not p ih => vcgen [evalC, ih] <;> grind

theorem evalArgs_same (es : List Expr) (s₀ : St) :
    ⦃fun s => s = s₀⦄ evalArgs es ⦃fun _ s => s = s₀; ⊤⦄ := by
  induction es generalizing s₀ with
  | nil => vcgen [evalArgs] <;> grind
  | cons e es ih => vcgen [evalArgs, evalE_same e, ih] <;> grind

/-! ## Statements keep `Keep` -/

/-- A continuation that keeps `Keep` on statements without byte stores. -/
def KeepK (k : Stmt → M Sig) : Prop :=
  ∀ st, st.noSt8 = true → ∀ m₀, ⦃fun s => Keep m₀ s.mem⦄ k st ⦃fun _ s => Keep m₀ s.mem; ⊤⦄

theorem invoke_keep (p : Prog) (hp : p.noSt8 = true) (k : Stmt → M Sig) (hk : KeepK k)
    (f : FnName) (m₀ : Mem) (vs : List Word) :
    ⦃fun s => Keep m₀ s.mem⦄ invoke p k f vs ⦃fun _ s => Keep m₀ s.mem; ⊤⦄ := by
  cases h : p.lookup f with
  | none => simp only [invoke, lookupFn, h]; vcgen <;> grind
  | some fd =>
    rw [invoke_eq _ h]
    have hb := Prog.noSt8_lookup hp h
    simp only [callFn]
    vcgen [hk fd.body hb m₀] <;> grind

theorem step_keep (p : Prog) (hp : p.noSt8 = true) (k : Stmt → M Sig) (hk : KeepK k) :
    KeepK (step p k) := by
  intro st hst m₀
  induction st with
  | skip => vcgen [step] <;> grind
  | set x e => vcgen [step, setLoc, evalE_same e] <;> grind [St.setLoc_mem]
  | st8 a i e => simp [Stmt.noSt8] at hst
  | st64 a i e =>
    vcgen [step, st64, evalE_same i, evalE_same e] <;> grind [Keep.set64]
  | seq s t ihs iht =>
    simp only [Stmt.noSt8, Bool.and_eq_true] at hst
    vcgen [step, ihs hst.1, iht hst.2] <;> grind
  | ite c s t ihs iht =>
    simp only [Stmt.noSt8, Bool.and_eq_true] at hst
    vcgen [step, evalC_same c, ihs hst.1, iht hst.2] <;> grind
  | «while» c s ih =>
    vcgen [step, evalC_same c, ih hst, hk (.while c s) hst m₀] <;> grind
  | brk => vcgen [step] <;> grind
  | ret es => vcgen [step, evalArgs_same es] <;> grind
  | call xs f args =>
    vcgen [step, setLocs, evalArgs_same args, invoke_keep p hp k hk f m₀] <;> grind [St.setLocs_mem']
  | abort e => vcgen [step, evalE_same e] <;> grind
  | gset g e => vcgen [step, setG, evalE_same e] <;> grind [Keep.setG, St.setG_mem]
  | st64t a t i e =>
    vcgen [step, st64, evalE_same t, evalE_same i, evalE_same e] <;> grind [Keep.set64]
  | copy64 d di s si n =>
    vcgen [step, warr_same d, warr_same s, evalE_same di, evalE_same si, evalE_same n] <;>
      grind [Keep.copy64]
  | copy8w d di s si n =>
    vcgen [step, warr_same d, evalE_same di, evalE_same si, evalE_same n] <;> grind [Keep.copy8w]
  | scan8 x s i e c => vcgen [step, setLoc, evalE_same i, evalE_same e] <;> grind [St.setLoc_mem]

theorem exec_keep (p : Prog) (hp : p.noSt8 = true) (n : Nat) : KeepK (exec p n) := by
  induction n with
  | zero => intro st _ m₀; vcgen [exec] <;> grind
  | succ n ih => exact step_keep p hp (exec p n) ih

/-- Every program satisfies the trivial post. -/
theorem Triple.triv {α : Type} (x : M α) : ⦃fun _ => True⦄ x ⦃fun _ _ => True; ⊤⦄ := by
  apply M.triple_of_run
  intro _ _ _ _ _
  trivial

/-- A call restores the caller's locals. -/
theorem invoke_loc (p : Prog) (k : Stmt → M Sig) (f : FnName) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p k f vs ⦃fun _ s => LocEq s s₀; ⊤⦄ := by
  cases h : p.lookup f with
  | none => simp only [invoke, lookupFn, h]; vcgen <;> grind
  | some fd =>
    rw [invoke_eq _ h]
    simp only [callFn]
    vcgen [Triple.triv (k fd.body)] <;> grind [LocEq]

/-- **A callee spec, with `Keep`**: a triple about `invoke p (exec p n) f vs` from `s₀` also
keeps the byte arrays and the array sizes, and the caller's locals. -/
theorem Triple.keep {p : Prog} (hp : p.noSt8 = true) {n : Nat} {f : FnName} {vs : List Word}
    {s₀ : St} {Q : List Word → St → Prop}
    (h : ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun r s => Q r s; ⊤⦄) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs
    ⦃fun r s => Q r s ∧ Keep s₀.mem s.mem ∧ LocEq s s₀; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  refine ⟨M.of_run (P := fun s => s = s₀) hs hrun h, ?_,
    M.of_run (P := fun s => s = s₀) (Q := fun _ s => LocEq s s₀) hs hrun
      (invoke_loc p _ f vs s₀)⟩
  subst hs
  exact M.of_run (P := fun t => Keep s.mem t.mem) (Keep.refl _) hrun
    (invoke_keep p hp _ (exec_keep p hp n) f s.mem vs)

end L
