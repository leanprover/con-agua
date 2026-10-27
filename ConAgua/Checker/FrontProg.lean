import ConAgua.Checker.FrontProgAgree
import ConAgua.Front.ChunkBridge
import ConAgua.Census.Attr

/-!
# The frontend's refinement at the checker's program (lane `pipeline`)

`frontRun_checker`: `L.Front.frontAll_refines` with `frontAllProg` replaced by `checkerProg`, and
`frontRun_checker_chunks`: `frontAll_refines_chunks`'s statement (`parseChunks [b]`) at
`checkerProg`.

`checkerProg` does not satisfy `frontRun_refines`'s lookup bundles: it binds no `validate`,
`str_put` or `apply_ind_line` (nothing reachable from `check` calls them; `FrontLookups`,
`IndLineLookups` and the single `str_put` lookup name them). So instead of instantiating the
parametric theorem, the run itself is transferred: the two programs agree on the functions
reachable from `front_run` (`checkerProg_frontAgree`, `FrontProgAgree.lean`), that set is
call-closed in `checkerProg` (`checkerProg_frontClosed`, one kernel check per chunk of functions,
`prog_all`), and the interpreter on a call-closed set reads only its lookups (`exec_agree`), so
`front_run` runs identically in both (`checkerProg_front_run`).
-/

namespace L.Checker

open L L.Compiler

/-! `checkerProg_noSt8`: `Checker/RomProg0.lean`. -/

/-! ## Runs read only the lookups of a call-closed set -/

/-- Every call of the statement is to a function `P` holds of. -/
def _root_.L.Stmt.callsP (P : FnName → Bool) : Stmt → Bool
  | .seq s t => s.callsP P && t.callsP P
  | .ite _ s t => s.callsP P && t.callsP P
  | .while _ s => s.callsP P
  | .call _ f _ => P f
  | _ => true

section agree
variable {p q : Prog} {P : FnName → Bool}
  (hpq : ∀ f, P f = true → p.lookup f = q.lookup f)
  (hcl : ∀ f fd, P f = true → p.lookup f = some fd → fd.body.callsP P = true)
include hpq hcl

theorem invoke_agree {k k' : Stmt → M Sig} (hk : ∀ s, s.callsP P = true → k s = k' s)
    {f : FnName} (hf : P f = true) : invoke p k f = invoke q k' f := by
  funext vs
  unfold invoke lookupFn
  rw [← hpq f hf]
  cases h : p.lookup f with
  | none => rfl
  | some fd =>
    have e : callFn k fd vs = callFn k' fd vs := by
      unfold callFn; rw [hk fd.body (hcl f fd hf h)]
    simp only [pure_bind, e]

theorem step_agree {k k' : Stmt → M Sig} (hk : ∀ s, s.callsP P = true → k s = k' s) :
    ∀ s, s.callsP P = true → step p k s = step q k' s := by
  intro s hs
  induction s with
  | seq s t ihs iht =>
    simp only [Stmt.callsP, Bool.and_eq_true] at hs
    simp only [step]; rw [ihs hs.1, iht hs.2]
  | ite c s t ihs iht =>
    simp only [Stmt.callsP, Bool.and_eq_true] at hs
    simp only [step]; rw [ihs hs.1, iht hs.2]
  | «while» c s ih =>
    have hw := hs
    simp only [Stmt.callsP] at hs
    simp only [step]; rw [ih hs, hk _ hw]
  | «call» xs f args =>
    simp only [Stmt.callsP] at hs
    simp only [step]; rw [invoke_agree hpq hcl hk hs]
  | _ => rfl

theorem exec_agree (n : Nat) : ∀ s, s.callsP P = true → exec p n s = exec q n s := by
  induction n with
  | zero => intro s _; rfl
  | succ n ih => intro s hs; exact step_agree hpq hcl ih s hs

/-- **A call into a call-closed set runs the same in both programs.** -/
theorem invoke_exec_agree (n : Nat) {f : FnName} (hf : P f = true) :
    invoke p (exec p n) f = invoke q (exec q n) f :=
  invoke_agree hpq hcl (exec_agree hpq hcl n) hf

end agree

/-! ## `front_run` in `checkerProg` -/

/-- The functions reachable from `front_run`, as a tree of name codes. -/
names_tree frontTree : frontFns

/-- Membership in `frontFns`, by the tree. -/
def inFront (f : FnName) : Bool := (frontTree.find (nameCode f)).isSome

theorem inFront_iff (f : FnName) : inFront f = true ↔ f ∈ frontFns := by
  rw [inFront, namesTree_spec frontTree.eq f]; exact decide_eq_true_iff

/-- Every function of `frontFns` calls only into `frontFns`, per chunk of functions. -/
prog_all checkerProg_frontClosedAll : checkerProg (fun x => !inFront x.1 || x.2.body.callsP inFront)

theorem checkerProg_frontClosed (f : FnName) (fd : FunDecl) (hf : inFront f = true)
    (h : checkerProg.lookup f = some fd) : fd.body.callsP inFront = true := by
  obtain ⟨l₁, l₂, hp, -⟩ := List.lookup_eq_some_iff.mp h
  have hx := checkerProg_frontClosedAll (f, fd) (hp ▸ List.mem_append_right _ List.mem_cons_self)
  simpa [hf] using hx

/-- **`front_run` runs in `checkerProg` as in `frontAllProg`.** -/
theorem checkerProg_front_run (n : Nat) :
    invoke checkerProg (exec checkerProg n) "front_run" =
      invoke L.Front.frontAllProg (exec L.Front.frontAllProg n) "front_run" :=
  invoke_exec_agree (P := inFront)
    (fun f hf => checkerProg_frontAgree f ((inFront_iff f).1 hf))
    checkerProg_frontClosed n (by decide)

/-! ## The refinements -/

open scoped Lean.Order
open Std.WP L.Arena L.Front ConRon.Arena ConRon.Arena.Frontend

/-- **`front_run` of the checker's program refines the twin's streaming parse of one chunk**
(`parseChunks [b]`, the checker statement's form). -/
@[refines ConRon.Arena.Frontend.parseChunks]
theorem frontRun_checker_chunks (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data)
    (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem StateD.blank) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke checkerProg (exec checkerProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseChunks [b]).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem st'; ⊤⦄ := by
  rw [checkerProg_front_run n]
  exact ConAgua.Front.ChunkBridge.frontAll_refines_chunks b h64 hsize n s₀ hm hpool a₀ hA hD hok
    hoff hpins hmode

end L.Checker
