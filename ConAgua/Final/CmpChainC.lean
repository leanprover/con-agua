module

import ConAgua.Checker.CheckARun
import all ConAgua.Checker.Entry
public import ConAgua.Final.Statement
import ConAgua.Checker.RomProg0
public import ConAgua.Checker.Prog

@[expose] public section

/-!
# The compared run's L runs accept ⇒ the twin's compared run accepts (lane compare)

* `run_check_bytes`: entry 2 (`check`) keeps the input bytes.
* `high_ne_accept`: `2^63 + k` (`k < 2^63`) is not `ACCEPT`.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena L.Rom
open ConRon.Arena

/-- A run of `check` keeps the bytes (the checker stores no byte). -/
theorem run_check_bytes {N : Nat} {m : Mem} {rs : List Word} {m' : Mem}
    (h : L.run checkerProg N "check" [] m = .ok (rs, m')) : m'.bytes = m.bytes := by
  have t := Triple.keep checkerProg_noSt8 (n := N) (f := "check") (vs := [])
    (s₀ := ⟨m, Locals.init []⟩) (Q := fun _ _ => True)
    (M.triple_of_run fun _ _ _ _ _ => trivial)
  have hk := run_post (Q := fun _ m'' => L.Keep m m'') h (by
    apply M.triple_of_run
    intro s r s' hs' hrun
    exact (M.of_run (P := fun x => x = _) hs' hrun t).2.1)
  exact hk.1

/-- `2^63 + k` for `k < 2^63` is not `ACCEPT`. -/
theorem high_ne_accept {k : Word} (hk : k.toNat < 2 ^ 63) : (9223372036854775808 : Word) + k ≠ ACCEPT := by
  intro e
  have e2 := congrArg UInt64.toNat e
  rw [UInt64.toNat_add] at e2
  simp only [ACCEPT, UInt64.reduceToNat] at e2
  omega

end ConAgua.Final
