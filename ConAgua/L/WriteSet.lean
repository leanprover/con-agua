module

public import ConAgua.Front.Preserve

@[expose] public section

/-!
# Write sets from the program text

`Preserve.lean` proves once that a program without `st8` keeps the byte arrays and the sizes.
The same induction gives a frame for every function of a *call-closed* set `fs` whose bodies
store only into word arrays of `A` and into words of the control array `ctl` listed in `C`. A
`ctl` index must be a literal `k`, or `k + (e &&& 1)`, which can only be `k` or `k + 1` (the
tier-indexed counts of the stores, `CTL[k + (t & 1)]`). The check `closedW` is a `Bool` function
of the text, so a concrete program's write set is `by decide +kernel`.

The frame itself is abstract here (`WFrame`): any reflexive relation on memories closed under
the allowed stores. `Arena/Frame.lean` instantiates it with `MemFrame` (the arena's layout:
`CTL` is array 1). Lane `scale`'s spike, made layout-agnostic (DESIGN.md, "The relation's architecture").
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L

/-- The control-array words a store index can name, if the text bounds it. -/
def ctlIdx : Expr → Option (List Word)
  | .const k => some [k]
  | .bin .add (.const k) (.bin .and _ (.const 1)) => some [k, k + 1]
  | _ => none

/-- Stores only into word arrays of `A` (never `ctl`) and into `ctl` words of `C`, no byte
stores; calls only into `fs`. -/
def Stmt.okW (ctl : ArrId) (A : List ArrId) (C : List Word) (fs : List FnName) : Stmt → Bool
  | .st8 .. => false
  | .st64 a i _ =>
    if a = ctl then (match ctlIdx i with | some ws => ws.all (· ∈ C) | none => false)
    else a ∈ A
  | .seq s t => s.okW ctl A C fs && t.okW ctl A C fs
  | .ite _ s t => s.okW ctl A C fs && t.okW ctl A C fs
  | .while _ s => s.okW ctl A C fs
  | .call _ f _ => f ∈ fs
  | _ => true

/-- **The write set of a call-closed function set**: every function of `fs` that `p` defines
satisfies `okW`. -/
def closedW (ctl : ArrId) (p : Prog) (A : List ArrId) (C : List Word) (fs : List FnName) : Bool :=
  fs.all fun f => match p.lookup f with
    | some fd => fd.body.okW ctl A C fs
    | none => true

theorem closedW_lookup {ctl : ArrId} {p : Prog} {A : List ArrId} {C : List Word}
    {fs : List FnName} (hp : closedW ctl p A C fs = true) {f : FnName} (hf : f ∈ fs) {fd : FunDecl}
    (h : p.lookup f = some fd) : fd.body.okW ctl A C fs = true := by
  simp only [closedW, List.all_eq_true] at hp
  have := hp f hf
  simp only [h] at this
  exact this

/-- `closedW` reads only the lookups of `fs`: a program that agrees with a concrete one on them
has its write set. This is how a program predicate (`LiftProg p`, …) gets its write set from the
concrete program's, which is `by decide +kernel`. -/
theorem closedW_of_agree {ctl : ArrId} {p q : Prog} {A : List ArrId} {C : List Word}
    {fs : List FnName} (hq : closedW ctl q A C fs = true)
    (hpq : ∀ f ∈ fs, p.lookup f = q.lookup f) : closedW ctl p A C fs = true := by
  simp only [closedW, List.all_eq_true] at hq ⊢
  intro f hf
  rw [hpq f hf]
  exact hq f hf

/-- A frame relation for the write set `(A, C)` of control array `ctl`: reflexive, and closed under
every word store the check allows. -/
structure WFrame (ctl : ArrId) (A : List ArrId) (C : List Word) (Fr : Mem → Mem → Prop) : Prop where
  refl : ∀ m, Fr m m
  st64 : ∀ m₀ m a i v, Fr m₀ m → (a ≠ ctl ∧ a ∈ A) ∨ (a = ctl ∧ i ∈ C) → Fr m₀ (m.set64 a i v)

theorem and_one_cases (x : Word) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  have h : (x &&& 1).toNat < 2 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have : (x &&& 1).toNat = 0 ∨ (x &&& 1).toNat = 1 := by omega
  rcases this with h0 | h1
  · left; exact UInt64.toNat_inj.mp (by simpa using h0)
  · right; exact UInt64.toNat_inj.mp (by simpa using h1)

theorem and_one_mem (k x : Word) : k + (x &&& 1) ∈ [k, k + 1] := by
  rcases and_one_cases x with h | h <;> simp [h]

/-- A tier word `t ≤ 1` is its own low bit: `CTL[k + (t & 1)]` is `CTL[k + t]`. -/
theorem and_one_of_le (t : Word) (h : t ≤ 1) : t &&& 1 = t := by
  have : t.toNat ≤ 1 := h
  rcases (show t.toNat = 0 ∨ t.toNat = 1 by omega) with h | h
  · rw [UInt64.toNat_inj.mp (h.trans UInt64.toNat_zero.symm)]; decide
  · rw [UInt64.toNat_inj.mp (h.trans UInt64.toNat_one.symm)]; decide

theorem ctlIdx_sound (e : Expr) (ws : List Word) (he : ctlIdx e = some ws) :
    ∀ s₀ : St, ⦃fun s => s = s₀⦄ evalE e ⦃fun j s => s = s₀ ∧ j ∈ ws; ⊤⦄ := by
  unfold ctlIdx at he
  split at he
  · cases he; intro s₀; vcgen [evalE] <;> grind
  · rename_i k x
    cases he; intro s₀
    vcgen [evalE, evalE_same x] <;> grind [and_one_mem, BinOp.eval]
  · cases he

section frame
variable {ctl : ArrId} {A : List ArrId} {C : List Word} {fs : List FnName} {Fr : Mem → Mem → Prop}

/-- A continuation that keeps the frame on `okW` statements. -/
def FrK (ctl : ArrId) (A : List ArrId) (C : List Word) (fs : List FnName) (Fr : Mem → Mem → Prop)
    (k : Stmt → M Sig) : Prop :=
  ∀ st, st.okW ctl A C fs = true → ∀ m₀, ⦃fun s => Fr m₀ s.mem⦄ k st ⦃fun _ s => Fr m₀ s.mem; ⊤⦄

theorem invoke_fr (p : Prog) (hp : closedW ctl p A C fs = true) (k : Stmt → M Sig)
    (hk : FrK ctl A C fs Fr k) (f : FnName) (hf : f ∈ fs) (m₀ : Mem) (vs : List Word) :
    ⦃fun s => Fr m₀ s.mem⦄ invoke p k f vs ⦃fun _ s => Fr m₀ s.mem; ⊤⦄ := by
  cases h : p.lookup f with
  | none => simp only [invoke, lookupFn, h]; vcgen <;> grind
  | some fd =>
    rw [invoke_eq _ h]
    have hb := closedW_lookup hp hf h
    simp only [callFn]
    vcgen [hk fd.body hb m₀] <;> grind

theorem st64_fr (hW : WFrame ctl A C Fr) (m₀ : Mem) (a : ArrId) (j v : Word) :
    ⦃fun s => Fr m₀ s.mem ∧ ((a ≠ ctl ∧ a ∈ A) ∨ (a = ctl ∧ j ∈ C))⦄ L.st64 a j v
    ⦃fun _ s => Fr m₀ s.mem; ⊤⦄ := by
  have := hW.st64
  vcgen [L.st64] <;> grind

theorem step_fr (p : Prog) (hp : closedW ctl p A C fs = true) (hW : WFrame ctl A C Fr)
    (k : Stmt → M Sig) (hk : FrK ctl A C fs Fr k) : FrK ctl A C fs Fr (step p k) := by
  intro st hst m₀
  induction st with
  | «skip» => vcgen [step] <;> grind
  | set x e => vcgen [step, setLoc, evalE_same e] <;> grind [St.setLoc_mem]
  | st8 a i e => simp [Stmt.okW] at hst
  | st64 a i e =>
    by_cases hc : a = ctl
    · subst hc
      simp only [Stmt.okW, ite_true] at hst
      split at hst
      · rename_i ws hws
        simp only [List.all_eq_true, decide_eq_true_eq] at hst
        vcgen [step, ctlIdx_sound i ws hws, evalE_same e, st64_fr hW m₀] <;> grind
      · simp at hst
    · simp only [Stmt.okW, hc, ite_false, decide_eq_true_eq] at hst
      vcgen [step, evalE_same i, evalE_same e, st64_fr hW m₀] <;> grind
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
    vcgen [step, setLocs, evalArgs_same args, invoke_fr p hp k hk f hst m₀] <;>
      grind [St.setLocs_mem']
  | «abort» => vcgen [step] <;> grind

theorem exec_fr (p : Prog) (hp : closedW ctl p A C fs = true) (hW : WFrame ctl A C Fr) (n : Nat) :
    FrK ctl A C fs Fr (exec p n) := by
  induction n with
  | zero => intro st _ m₀; vcgen [exec] <;> grind
  | succ n ih => exact step_fr p hp hW (exec p n) ih

/-- **The frame of a call, from the text**, as a triple: a call of `f ∈ fs` from `s₀` ends in a
memory that is a frame of `s₀`'s. -/
theorem invoke_frame (p : Prog) (hp : closedW ctl p A C fs = true) (hW : WFrame ctl A C Fr)
    (n : Nat) (f : FnName) (hf : f ∈ fs) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun _ s => Fr s₀.mem s.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  subst hs
  exact M.of_run (P := fun t => Fr s.mem t.mem) (hW.refl _) hrun
    (invoke_fr p hp _ (exec_fr p hp hW n) f hf s.mem vs)

/-- **The frame of a run, from the text**: a run of `f ∈ fs` ends in a frame of its start. -/
theorem run_frame (p : Prog) (hp : closedW ctl p A C fs = true) (hW : WFrame ctl A C Fr)
    (f : FnName) (hf : f ∈ fs) (n : Nat) (vs : List Word) (m : Mem) (rs : List Word) (m' : Mem)
    (h : run p n f vs m = .ok (rs, m')) : Fr m m' := by
  simp only [run] at h
  cases hr : (invoke p (exec p n) f vs).run { mem := m, loc := Locals.init [] } with
  | error e => simp [hr, Except.map] at h
  | ok r =>
    obtain ⟨r, s'⟩ := r
    simp only [hr, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact M.of_run (P := fun s => Fr m s.mem) (hW.refl m) hr
      (invoke_fr p hp _ (exec_fr p hp hW n) f hf m vs)

end frame

end L
