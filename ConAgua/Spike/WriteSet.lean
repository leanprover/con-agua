import ConAgua.Front.Preserve
import ConAgua.Arena.Frame

/-!
# Spike (lane `scale`): frames from the program text

`Preserve.lean` proves once that a program without `st8` keeps the byte arrays and the sizes.
The same induction gives `MemFrame A C` for every function of a *call-closed* set `fs` whose bodies
store only into arrays of `A` and into `CTL` words of `C` (a `CTL` index must be a literal `k`, or
`k + (e &&& 1)`, which can only be `k` or `k + 1`). The check is a `Bool` function of the program
text, so a concrete program's write set is `by decide`. Not imported by `ConAgua`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Spike

open L.Arena

/-- The `CTL` words a store index can name, if the text bounds it. -/
def ctlIdx : Expr → Option (List Word)
  | .const k => some [k]
  | .bin .add (.const k) (.bin .and _ (.const 1)) => some [k, k + 1]
  | _ => none

/-- Stores only into `A` (never `CTL`) and into `CTL` words of `C`; calls only into `fs`. -/
def _root_.L.Stmt.okW (A : List ArrId) (C : List Word) (fs : List FnName) : Stmt → Bool
  | .st8 .. => false
  | .st64 a i _ =>
    if a = CTL then (match ctlIdx i with | some ws => ws.all (· ∈ C) | none => false)
    else a ∈ A
  | .seq s t => s.okW A C fs && t.okW A C fs
  | .ite _ s t => s.okW A C fs && t.okW A C fs
  | .while _ s => s.okW A C fs
  | .call _ f _ => f ∈ fs
  | _ => true

/-- Every function of `fs` that `p` defines satisfies `okW`. -/
def closedW (p : Prog) (A : List ArrId) (C : List Word) (fs : List FnName) : Bool :=
  fs.all fun f => match p.lookup f with
    | some fd => fd.body.okW A C fs
    | none => true

theorem closedW_lookup {p : Prog} {A : List ArrId} {C : List Word} {fs : List FnName}
    (hp : closedW p A C fs = true) {f : FnName} (hf : f ∈ fs) {fd : FunDecl}
    (h : p.lookup f = some fd) : fd.body.okW A C fs = true := by
  simp only [closedW, List.all_eq_true] at hp
  have := hp f hf
  simp only [h] at this
  exact this

/-- The frame plus the byte arrays. -/
def WFr (A : List ArrId) (C : List Word) (m₀ m : Mem) : Prop := MemFrame A C m₀ m ∧ m.bytes = m₀.bytes

theorem WFr.refl (A : List ArrId) (C : List Word) (m : Mem) : WFr A C m m := ⟨MemFrame.refl _ _ _, rfl⟩

theorem and_one_cases (x : Word) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  have h : (x &&& 1).toNat < 2 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have : (x &&& 1).toNat = 0 ∨ (x &&& 1).toNat = 1 := by omega
  rcases this with h0 | h1
  · left; exact UInt64.toNat_inj.mp (by simpa using h0)
  · right; exact UInt64.toNat_inj.mp (by simpa using h1)

theorem and_one_mem (k x : Word) : k + (x &&& 1) ∈ [k, k + 1] := by
  rcases and_one_cases x with h | h <;> simp [h]

theorem ctlIdx_sound (e : Expr) (ws : List Word) (he : ctlIdx e = some ws) :
    ∀ s₀ : St, ⦃fun s => s = s₀⦄ evalE e ⦃fun j s => s = s₀ ∧ j ∈ ws; ⊤⦄ := by
  unfold ctlIdx at he
  split at he
  · cases he; intro s₀; vcgen [evalE] <;> grind
  · rename_i k x
    cases he; intro s₀
    vcgen [evalE, evalE_same x] <;> grind [and_one_mem, BinOp.eval]
  · cases he

theorem WFr.st64 {A : List ArrId} {C : List Word} {m₀ m : Mem} (h : WFr A C m₀ m) (a : ArrId)
    (i v : Word) (ha : (a ≠ CTL ∧ a ∈ A) ∨ (a = CTL ∧ i ∈ C)) : WFr A C m₀ (m.set64 a i v) := by
  refine ⟨?_, h.2⟩
  rcases ha with ⟨hc, ha⟩ | ⟨rfl, hi⟩
  · exact MemFrame.trans h.1 (MemFrame.mono (MemFrame.set64 m a hc i v) (by simpa using ha) (by simp))
  · exact MemFrame.trans h.1 (MemFrame.mono (MemFrame.setCtl m i v) (by simp) (by simpa using hi))

/-- A continuation that keeps the frame on `okW` statements. -/
def FrK (A : List ArrId) (C : List Word) (fs : List FnName) (k : Stmt → M Sig) : Prop :=
  ∀ st, st.okW A C fs = true → ∀ m₀, ⦃fun s => WFr A C m₀ s.mem⦄ k st ⦃fun _ s => WFr A C m₀ s.mem; ⊤⦄

theorem invoke_fr (p : Prog) (A : List ArrId) (C : List Word) (fs : List FnName)
    (hp : closedW p A C fs = true) (k : Stmt → M Sig) (hk : FrK A C fs k)
    (f : FnName) (hf : f ∈ fs) (m₀ : Mem) (vs : List Word) :
    ⦃fun s => WFr A C m₀ s.mem⦄ invoke p k f vs ⦃fun _ s => WFr A C m₀ s.mem; ⊤⦄ := by
  cases h : p.lookup f with
  | none => simp only [invoke, lookupFn, h]; vcgen <;> grind
  | some fd =>
    rw [invoke_eq _ h]
    have hb := closedW_lookup hp hf h
    simp only [callFn]
    vcgen [hk fd.body hb m₀] <;> grind

theorem st64_fr (A : List ArrId) (C : List Word) (m₀ : Mem) (a : ArrId) (j v : Word) :
    ⦃fun s => WFr A C m₀ s.mem ∧ ((a ≠ CTL ∧ a ∈ A) ∨ (a = CTL ∧ j ∈ C))⦄ L.st64 a j v
    ⦃fun _ s => WFr A C m₀ s.mem; ⊤⦄ := by
  vcgen [L.st64] <;> grind [WFr.st64]

theorem step_fr (p : Prog) (A : List ArrId) (C : List Word) (fs : List FnName)
    (hp : closedW p A C fs = true) (k : Stmt → M Sig) (hk : FrK A C fs k) :
    FrK A C fs (step p k) := by
  intro st hst m₀
  induction st with
  | «skip» => vcgen [step] <;> grind
  | set x e => vcgen [step, setLoc, evalE_same e] <;> grind [St.setLoc_mem]
  | st8 a i e => simp [Stmt.okW] at hst
  | st64 a i e =>
    by_cases hc : a = CTL
    · subst hc
      simp only [Stmt.okW, ite_true] at hst
      split at hst
      · rename_i ws hws
        simp only [List.all_eq_true, decide_eq_true_eq] at hst
        vcgen [step, ctlIdx_sound i ws hws, evalE_same e, st64_fr A C m₀] <;> grind
      · simp at hst
    · simp only [Stmt.okW, hc, ite_false, decide_eq_true_eq] at hst
      vcgen [step, evalE_same i, evalE_same e, st64_fr A C m₀] <;> grind
  | seq s t ihs iht =>
    simp only [Stmt.okW, Bool.and_eq_true] at hst
    vcgen [step, ihs hst.1, iht hst.2] <;> grind
  | ite c s t ihs iht =>
    simp only [Stmt.okW, Bool.and_eq_true] at hst
    vcgen [step, evalC_same c, ihs hst.1, iht hst.2] <;> grind
  | «while» c s ih =>
    vcgen [step, evalC_same c, ih hst, hk (.while c s) hst m₀] <;> grind
  | brk => vcgen [step] <;> grind
  | ret es => vcgen [step, evalArgs_same es] <;> grind
  | «call» xs f args =>
    simp only [Stmt.okW, decide_eq_true_eq] at hst
    vcgen [step, setLocs, evalArgs_same args, invoke_fr p A C fs hp k hk f hst m₀] <;>
      grind [St.setLocs_mem']
  | «abort» => vcgen [step] <;> grind

theorem exec_fr (p : Prog) (A : List ArrId) (C : List Word) (fs : List FnName)
    (hp : closedW p A C fs = true) (n : Nat) : FrK A C fs (exec p n) := by
  induction n with
  | zero => intro st _ m₀; vcgen [exec] <;> grind
  | succ n ih => exact step_fr p A C fs hp (exec p n) ih

/-- **The frame of a run, from the text**: a run of `f ∈ fs` changes only arrays of `A` and `CTL`
words of `C`, keeps the sizes and the byte arrays. -/
theorem run_frame (p : Prog) (A : List ArrId) (C : List Word) (fs : List FnName)
    (hp : closedW p A C fs = true) (f : FnName) (hf : f ∈ fs) (n : Nat) (vs : List Word) (m : Mem)
    (rs : List Word) (m' : Mem) (h : run p n f vs m = .ok (rs, m')) : MemFrame A C m m' := by
  simp only [run] at h
  cases hr : (invoke p (exec p n) f vs).run { mem := m, loc := Locals.init [] } with
  | error e => simp [hr, Except.map] at h
  | ok r =>
    obtain ⟨r, s'⟩ := r
    simp only [hr, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact (M.of_run (P := fun s => WFr A C m s.mem) (WFr.refl A C m) hr
      (invoke_fr p A C fs hp _ (exec_fr p A C fs hp n) f hf m vs)).1

end L.Spike
