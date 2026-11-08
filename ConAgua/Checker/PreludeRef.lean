module

import ConAgua.Verdict.FrontPreSimE
import ConAgua.Verdict.FrontSafeE
import ConAgua.Front.FrontRunRef
import ConAgua.Checker.FrontReset
import ConAgua.Checker.PrepProgHoist
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.Verdict
public import ConAgua.Checker.NoVerdictFns
public import ConAgua.Checker.PipePrelude
import all ConAgua.Checker.Prelude

@[expose] public section

/-!
# The prelude, both outcomes: `builtin_prelude`

One unified model and one refinement (`docs/design/unifiede.md`). `builtin_prelude()` is
`pre_front_run()` (the frontend on the prelude's bytes), then `CTL[240] := DECL[0]`, then
`front_reset()` (lifted). `pre_front_run` is read through its run: both of its halves are
`front_run`'s on the prelude's bytes (`preSim_triple`, `preFrontRun_errSim`), whose refinement is
`frontRun_ref` (`frontRunOK_checker`, `frontRun_errClaim`). So `builtinPrelude_ref` is a `RefC`:
an ok run ends in `BP3` (the twin's `builtinPreludeE` accepted, the records in `DECL`, the id
tables empty), a failure of class `≠ 0` claims that `builtinPreludeE` fails with that class. Its
`G` is `True`: the closure and `SafeLink preludeText` are theorems at `checkerProg`.
-/

open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend

/-- **`builtin_prelude`'s unified model**: `pre_front_run` through its run, `front_reset` (outside
the verdict closure) lifted. -/
l_model builtinPrelude_specE (p : Prog) (hf : p.lookup "builtin_prelude" = some builtinPreludeL)
  fns [hf ↦ builtinPreludeLE]
  specs [callW_spec p n "front_reset"]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE] unified nv [closedNV p nvFns = true, nv_mem]

/-- A failing call is a failing run from the call's start. -/
theorem run_of_callE_err {p : Prog} {k : Nat} {f : FnName} {vs : List Word} {m : Mem} {e : Err}
    (h : callE p k f vs m = .error e) :
    (invoke p (exec p k) f vs).run ⟨m, Locals.init []⟩ = .error e := by
  unfold callE at h
  cases hr : (invoke p (exec p k) f vs).run ⟨m, Locals.init []⟩ with
  | error e' => rw [hr] at h; cases h; rfl
  | ok v => rw [hr] at h; cases h

/-- The prelude's parse failing is the prelude failing. -/
theorem builtinPreludeE_fails {a : AState} {c : L.Word}
    (h : TwinFailsV (parseBytes preludeText) a c) : TwinFailsV builtinPreludeE a c := by
  rcases h with ⟨ce, hce, hc⟩ | ⟨ce, i, a', hce, hc⟩
  · refine .inl ⟨ce, ?_, hc⟩
    show (do let x ← (parseBytes preludeText).run a; _) = _
    rw [hce]; rfl
  · refine .inr ⟨ce, i, a', ?_, hc⟩
    show (do let x ← (parseBytes preludeText).run a; _) = _
    rw [hce]; rfl

set_option maxRecDepth 100000 in
/-- **`builtin_prelude` refines `builtinPreludeE`, both outcomes**: from `BP0`, an ok run ends in
`BP3`; a failure of class `≠ 0` is `pre_front_run`'s, which is `front_run`'s on the prelude's
bytes, whose claim is the prelude's parse failing. -/
theorem builtinPrelude_ref (h64 : System.Platform.numBits = 64) (a : AState) (n : Nat) {m : Mem}
    (h0 : BP0 a m) :
    RefC True (builtinPreludeLE checkerProg n m) (fun x => BP3 a x.2)
      (ErrClaimV builtinPreludeE a) := by
  sorry

/-- **`builtin_prelude` refines `builtinPreludeE`**, on the parse state and the arena
(`builtinPrelude_ref`'s ok half). -/
@[refines ConRon.Arena.Frontend.builtinPreludeE]
theorem builtinPrelude_checker (h64 : System.Platform.numBits = 64) (a : AState) :
    StageSpec checkerProg "builtin_prelude" (BP0 a) fun _ => BP3 a := by
  intro n _hn s₀
  refine M.triple_of_run fun s r s' hs hr => ?_
  obtain ⟨hl, hx⟩ := M.of_run' (P := fun s => s = s₀) hs hr
    (builtinPrelude_specE checkerProg checkerProg_builtin n s₀)
  refine ⟨hl, fun h0 => ?_⟩
  have h := builtinPrelude_ref h64 a n h0
  rw [hx] at h
  exact h

end L.Checker
