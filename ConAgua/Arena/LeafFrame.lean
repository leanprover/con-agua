import ConAgua.Compiler.WriteSetSplit
import ConAgua.Arena.Pool
import ConAgua.Front.Preserve

/-!
# Write sets with trusted leaves (lane `indproofs4`, helper `lm`)

`closedW ctl p A C fs` (`L/WriteSet.lean`) asks every function of the call-closed set `fs` to
store only into `A`/`C`. `closedWL ctl p A C fs L` relaxes the closure: the bodies of `fs` may
also call the *leaves* `L`, whose bodies are not checked. A frame relation `Fr` (`WFrame`) then
survives every call of `f ∈ fs` when every call of a leaf keeps it (`invoke_frameL`): what the
loop uses to carry a memory invariant across callees whose only writer of the invariant's words
is a leaf with its own lemma (`consts_resolve_ffast` and its memo, `IndMemos`).

`closedWL_of_all` decides it for a large program one function at a time, like
`closedW_of_all` (`Compiler/WriteSetSplit.lean`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L

/-- **The write set of `fs` with the leaves `L`**: every function of `fs` that `p` defines stores
only into `A`/`C` and calls only into `fs` and `L`. -/
def closedWL (ctl : ArrId) (p : Prog) (A : List ArrId) (C : List Word) (fs L : List FnName) : Bool :=
  fs.all fun f => match p.lookup f with
    | some fd => fd.body.okW ctl A C (fs ++ L)
    | none => true

section frameL
variable {ctl : ArrId} {A : List ArrId} {C : List Word} {fs L : List FnName}
  {Fr : Mem → Mem → Prop}

theorem closedWL_lookup {p : Prog} (hp : closedWL ctl p A C fs L = true) {f : FnName}
    (hf : f ∈ fs) {fd : FunDecl} (h : p.lookup f = some fd) :
    fd.body.okW ctl A C (fs ++ L) = true := by
  simp only [closedWL, List.all_eq_true] at hp
  have := hp f hf
  simp only [h] at this
  exact this

/-- `step_fr` with the callees' frames as a hypothesis. -/
theorem step_frI (p : Prog) (gs : List FnName) (hW : WFrame ctl A C Fr) (k : Stmt → M Sig)
    (hk : FrK ctl A C gs Fr k)
    (hinv : ∀ f ∈ gs, ∀ m₀ vs, ⦃fun s => Fr m₀ s.mem⦄ invoke p k f vs ⦃fun _ s => Fr m₀ s.mem; ⊤⦄) :
    FrK ctl A C gs Fr (step p k) := by
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
  | st64t a t i e =>
    simp only [Stmt.okW, Bool.and_eq_true, decide_eq_true_eq] at hst
    have := tierA_cases a
    vcgen [step, evalE_same t, evalE_same i, evalE_same e, st64_fr hW m₀] <;> grind
  | copy64 d di s si n =>
    simp only [Stmt.okW] at hst
    have h1 : ∀ m a di s si n, Fr m₀ m → a ≠ ctl ∧ a ∈ A → Fr m₀ (m.copy64 a di s si n) :=
      fun _ _ _ _ _ _ h ha => hW.copy64 h ha _ _ _ _
    vcgen [step, warr_okW d hst, warr_same s, evalE_same di, evalE_same si, evalE_same n] <;> grind
  | copy8w d di s si n =>
    simp only [Stmt.okW] at hst
    have h1 : ∀ m a di b si n, Fr m₀ m → a ≠ ctl ∧ a ∈ A → Fr m₀ (m.copy8w a di b si n) :=
      fun _ _ _ _ _ _ h ha => hW.copy8w h ha _ _ _ _
    vcgen [step, warr_okW d hst, evalE_same di, evalE_same si, evalE_same n] <;> grind
  | scan8 x s i e c => vcgen [step, setLoc, evalE_same i, evalE_same e] <;> grind [St.setLoc_mem]
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
    vcgen [step, setLocs, evalArgs_same args, hinv f hst m₀] <;>
      grind [St.setLocs_mem']
  | «abort» e => vcgen [step, evalE_same e] <;> grind
  | gset g e =>
    have := hW.setG
    vcgen [step, setG, evalE_same e] <;> grind [St.setG_mem]

/-- A call of a function of `fs` keeps the frame, given the body's continuation does. -/
theorem invoke_frL (p : Prog) (hp : closedWL ctl p A C fs L = true) (k : Stmt → M Sig)
    (hk : FrK ctl A C (fs ++ L) Fr k) (f : FnName) (hf : f ∈ fs) (m₀ : Mem) (vs : List Word) :
    ⦃fun s => Fr m₀ s.mem⦄ invoke p k f vs ⦃fun _ s => Fr m₀ s.mem; ⊤⦄ := by
  cases h : p.lookup f with
  | none => simp only [invoke, lookupFn, h]; vcgen <;> grind
  | some fd =>
    rw [invoke_eq _ h]
    have hb := closedWL_lookup hp hf h
    simp only [callFn]
    vcgen [hk fd.body hb m₀] <;> grind

/-- **The interpreter keeps the frame** on the statements of `fs ++ L`, at every fuel, when every
call of a leaf keeps it. -/
theorem exec_frL (p : Prog) (hp : closedWL ctl p A C fs L = true) (hW : WFrame ctl A C Fr)
    (hL : ∀ g ∈ L, ∀ n m₀ vs,
      ⦃fun s => Fr m₀ s.mem⦄ invoke p (exec p n) g vs ⦃fun _ s => Fr m₀ s.mem; ⊤⦄) (n : Nat) :
    FrK ctl A C (fs ++ L) Fr (exec p n) := by
  induction n with
  | zero => intro st _ m₀; vcgen [exec] <;> grind
  | succ n ih =>
    refine step_frI p (fs ++ L) hW (exec p n) ih fun f hf m₀ vs => ?_
    rcases List.mem_append.mp hf with hf | hf
    · exact invoke_frL p hp (exec p n) ih f hf m₀ vs
    · exact hL f hf n m₀ vs

/-- **The frame of a call, from the text with trusted leaves**: a call of `f ∈ fs` from `s₀` ends
in a memory that is a frame of `s₀`'s, when every call of a leaf keeps the frame. -/
theorem invoke_frameL (p : Prog) (hp : closedWL ctl p A C fs L = true) (hW : WFrame ctl A C Fr)
    (hL : ∀ g ∈ L, ∀ n m₀ vs,
      ⦃fun s => Fr m₀ s.mem⦄ invoke p (exec p n) g vs ⦃fun _ s => Fr m₀ s.mem; ⊤⦄)
    (n : Nat) (f : FnName) (hf : f ∈ fs) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun _ s => Fr s₀.mem s.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  subst hs
  exact M.of_run (P := fun t => Fr s.mem t.mem) (hW.refl _) hrun
    (invoke_frL p hp _ (exec_frL p hp hW hL n) f hf s.mem vs)

end frameL

end L

namespace L.Compiler

open L

/-- One function's check with leaves: not in the set `t`, or its body passes `okWB` with the
callees in `tc` (the set and the leaves). -/
def wsChkL (ctl : ArrId) (pa : ArrId → Bool) (pc : Word → Bool) (t tc : NTree)
    (x : FnName × FunDecl) : Bool :=
  !(t.find (nameCode x.1)).isSome || x.2.body.okWB ctl pa pc tc

/-- **A write set with leaves from per-function checks** (`closedW_of_all` with the callee tree
of `fs ++ L`). -/
theorem closedWL_of_all {ctl : ArrId} {p : Prog} {A : List ArrId} {C : List Word}
    {fs L : List FnName} {t tc : NTree} {pa : ArrId → Bool} {pc : Word → Bool}
    (ht : namesTree fs = some t) (htc : namesTree (fs ++ L) = some tc)
    (hpa : ∀ a, pa a = true → a ∈ A) (hpc : ∀ w, pc w = true → w ∈ C)
    (h : ∀ x ∈ p, wsChkL ctl pa pc t tc x = true) :
    closedWL ctl p A C fs L = true := by
  simp only [closedWL, List.all_eq_true]
  intro f hf
  split
  · rename_i fd hfd
    obtain ⟨_, _, hp, -⟩ := List.lookup_eq_some_iff.mp hfd
    have hx := h _ (hp ▸ List.mem_append_right _ List.mem_cons_self)
    simp only [wsChkL, namesTree_spec ht, hf, decide_true, Bool.not_true, Bool.false_or] at hx
    exact Stmt.okW_of_okWB htc hpa hpc hx
  · rfl

end L.Compiler

namespace L.Arena

/-- The write set of `fs` with the leaves `L` at the arena's control array `CTL`. -/
abbrev closedAL (p : Prog) (A : List ArrId) (C : List Word) (fs L : List FnName) : Bool :=
  closedWL CTL p A C fs L

end L.Arena
