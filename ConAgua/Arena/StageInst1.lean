import ConAgua.Arena.CallF
import ConAgua.Arena.Inst1Refine
import ConAgua.Arena.WriteSets
import ConAgua.Arena.StripTeleSpec
import ConAgua.Checker.Entry
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# `instantiate1_fast` under the stage relation (lane `indproofs3`, helper `stubs`)

`instantiate1_fast(fuel, e, v, d)` is the adapter `L.Checker.instantiate1FastA` (`Checker/Entry.lean`):
it ignores the fuel word and calls `inst_entry(e, v, d)`, lane `exprops4`'s walk, which refines
`instantiate1Fast coreWalkFuel` under `ArenaD` (`instEntry_refines`). Every caller of the stage
passes `CWF` (= `coreWalkFuel`), so the twin side is the stub contract's
`instantiate1Fast CWF.toNat`.

* **The model** `i1F m args` is `callF i1Prog "instantiate1_fast"` (`CallF.lean`): the adapter and
  the walk's program `instProg` are call-closed (`i1Prog_closed`, by the text), so every call in a
  program with `I1Prog p` returns it (`i1F_spec`), at any fuel; it does not depend on `p`.
* **The relational lemma** `i1F_ok`: from `StageR`, a returning model run is a twin run with
  `KeepPost … decW0E` after, as the stub contract `instantiate1Fast_spec` said. No hypothesis beyond
  `StageR` and the handle bound: the walk's memo (`IMEMO`) is part of `ArenaR`, cleared at entry
  and exit on both sides; the walk writes only the expression tables and its memo (`instA`,
  `instC`, all below array 64 and `CTL[64]`), and the twin keeps caches and pins
  (`keeps_inst1Fast`), so `StageR.of_walk` gives the stage relation after.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The adapter and the `instantiate1` walk. -/
def i1Prog : Prog := ("instantiate1_fast", L.Checker.instantiate1FastA) :: instProg

/-- All of `i1Prog`'s names. -/
def i1Fns : List FnName := i1Prog.map (·.1)

theorem i1Prog_closed : closedA i1Prog instA instC i1Fns = true := by decide +kernel

/-- The program bundle: `p` binds the adapter and the walk as `i1Prog` does. -/
def I1Prog (p : Prog) : Prop := ProgHas p i1Prog

theorem lookup_isSome_of_mem {l : Prog} {f : FnName} (h : f ∈ l.map (·.1)) : (l.lookup f).isSome := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    simp only [List.map_cons, List.mem_cons] at h
    simp only [List.lookup]
    split
    · rfl
    · rename_i hne
      rcases h with h | h
      · subst h; simp at hne
      · exact ih h

theorem I1Prog.agree {p : Prog} (hp : I1Prog p) : ∀ g ∈ i1Fns, p.lookup g = i1Prog.lookup g := by
  intro g hg
  obtain ⟨fd, e⟩ := Option.isSome_iff_exists.mp (lookup_isSome_of_mem hg)
  rw [e, hp g fd e]

/-- **The model of `instantiate1_fast`** (program- and fuel-free). -/
noncomputable def i1F (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF i1Prog "instantiate1_fast" m args

/-- **`instantiate1_fast(f, e, v, d)` returns its model.** -/
theorem i1F_spec (p : Prog) (hp : I1Prog p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "instantiate1_fast" args
    ⦃fun r s' => LocEq s' s₀ ∧ i1F s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec i1Prog_closed hp.agree (List.mem_cons_self ..) n s₀ args

/-- What the adapter returns of `inst_entry`'s run: its first word. -/
def fwd1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

theorem fwd1_some (r : List Word) (m : Mem) : fwd1 (some (r, m)) = some ([r.headD 0], m) := rfl

/-- The adapter forwards to `inst_entry`. -/
theorem i1Adapter_spec (n : Nat) (s₀ : St) (f e v d : Word) :
    ⦃fun s => s = s₀⦄ invoke i1Prog (exec i1Prog (n + 1)) "instantiate1_fast" [f, e, v, d]
    ⦃fun r s' => LocEq s' s₀ ∧ fwd1 (callW i1Prog n "inst_entry" [e, v, d] s₀.mem) =
      some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (show i1Prog.lookup "instantiate1_fast" = some L.Checker.instantiate1FastA from rfl)]
  simp only [callFn, L.Checker.instantiate1FastA]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec i1Prog n "inst_entry"] <;>
    finish [fwd1_some]

theorem run_of_callW {P : Prog} {n : Nat} {f : FnName} {vs : List Word} {m m' : Mem}
    {r : List Word} (h : callW P n f vs m = some (r, m')) : run P n f vs m = .ok (r, m') := by
  simp only [callW] at h
  simp only [run]
  cases hr : (invoke P (exec P n) f vs).run { mem := m, loc := Locals.init [] } with
  | error e => rw [hr] at h; cases h
  | ok q => rw [hr] at h; simp only [Option.some.injEq] at h; simp [Except.map, h]

theorem instA_lt : ∀ b ∈ instA, b < 64 ∨ (256 ≤ b ∧ b < 320) := by
  simp only [instA, liftA]; decide

theorem instC_lt : ∀ x ∈ instC, x.toNat < 64 := by
  intro x hx; simp only [instC, liftC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- **`instantiate1_fast` refines `instantiate1Fast coreWalkFuel` under the stage relation**
(replaces `IndStubs.instantiate1Fast_spec`). -/
theorem i1F_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (e v d : Word)
    (he : H e) :
    RelW i1F [CWF, e, v, d] (StageR dn vis fe)
      (instantiate1Fast CWF.toNat (decI e) (decI v) d.toNat) (KeepPost dn vis fe decW0E) := by
  intro m m' a r h hS
  obtain ⟨n, hc⟩ := callF_run h
  have hfr : MemFrame instA instC m m' :=
    (run_memFrame i1Prog_closed (List.mem_cons_self ..) (run_of_callW hc)).1
  match n, hc with
  | 0, hc => rw [callW_zero] at hc; cases hc
  | n + 1, hc =>
  obtain ⟨s', hs', -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (i1Adapter_spec n _ CWF e v d) hc
  cases hi : callW i1Prog n "inst_entry" [e, v, d] m with
  | none => rw [hi] at hm; cases hm
  | some x =>
  obtain ⟨rI, mI⟩ := x
  rw [hi] at hm
  simp only [fwd1, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, hmI⟩ := hm
  rw [hs'] at hmI
  subst hmI
  match n, hi with
  | 0, hi => rw [callW_zero] at hi; cases hi
  | k + 1, hi =>
  have hip : L.Arena.InstProg i1Prog :=
    ⟨by unfold LiftProg liftProgFns; repeat (first | exact ProgHas.nil | refine ProgHas.cons rfl ?_),
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨s'', hs'', -, hok, hD, hres, hlt⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (instEntry_refines i1Prog hip rfl k _ a hS.1.arena e v d he) hi
  rw [hs''] at hD
  have hrun := AM.run_of_ok _ a hok
  have hcp : cp (AM.st (instantiate1Fast coreWalkFuel (decE e) (decE v) d.toNat) a) = cp a :=
    (keeps_inst1Fast _ _ _ _).run hrun
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hD hfr instA_lt instC_lt hcp
  refine ⟨_, _, by rw [CWF_eq]; exact hrun, hS', hg, ?_⟩
  exact ⟨hlt, hres.symm⟩

end L.Ind
