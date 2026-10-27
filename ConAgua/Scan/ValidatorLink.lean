module

public import ConAgua.Scan.Validator
public import ConAgua.Scan.LineLink
import ConAgua.Census.Attr

@[expose] public section

/-!
# The Stage B validator's line scan against con-leche

Partial correctness of the L program `valProg`'s `scan_line` on a buffer `b` (under
`numBits = 64` and `b.size < 2 ^ 63`), `scanLine_run`: whenever `scan_line(i)` returns, it returns
`(1, next)` exactly when con-leche's `scanLineFwd b i` is `.ok _ next`, and `(0, 0)` exactly when it
is `.err _`. ("Whenever it returns": an L run can also end in an error, which the compiler maps to
the harness's `exhausted`/`error` outcomes, never to an answer.)
-/

namespace ConAgua.Scan.ValidatorLink

open L L.Scan.Line L.Scan.Validator ConAgua.Scan.LineLink

variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- One line: the L `scan_line` decides what con-leche's `scanLineFwd` decides. -/
@[refines_part ConLeche.Frontend.scanLineFwd "validity"]
theorem scanLine_run (fuel : Nat) (i : USize) (hi : i.toNat ≤ b.size) (r : List Word) (m' : Mem)
    (h : run valProg fuel "scan_line" [i.toUInt64] { bytes := #[b.data] } = .ok (r, m')) :
    r = [(encLine (ConLeche.Frontend.scanLineFwd b i)).1, (encLine (ConLeche.Frontend.scanLineFwd b i)).2] := by
  rw [lineFwd_link b h64 hsize i]
  simp only [run] at h
  cases hr : (invoke valProg (exec valProg fuel) "scan_line" [i.toUInt64]).run
      { mem := { bytes := #[b.data] }, loc := Locals.init [] } with
  | error e => simp [hr, Except.map] at h
  | ok rs =>
    simp only [hr, Except.map] at h
    injection h with h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have hi' : i.toUInt64.toNat ≤ b.data.size := by simpa using hi
    have := M.of_run (P := fun s => s = { mem := { bytes := #[b.data] }, loc := Locals.init [] }) rfl hr
      (scanLine_spec valProg b.data hsize rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl fuel _ rfl i.toUInt64 hi')
    exact this.2

end ConAgua.Scan.ValidatorLink
