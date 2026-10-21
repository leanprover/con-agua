module

public import ConAgua.Scan.Validator
public import ConAgua.Scan.DriverLink

@[expose] public section

/-!
# The Stage B validator against con-leche, end to end

Partial correctness of the L program `valProg` on a buffer `b` (under `numBits = 64` and
`b.size < 2 ^ 63`):

* `scanLine_run`: whenever `scan_line(i)` returns, it returns `(1, next)` exactly when
  con-leche's `scanLineFwd b i` is `.ok _ next`, and `(0, 0)` exactly when it is `.err _`;
* `validate_run'`: whenever `validate()` returns `r`, `r` is `scanDriver b 0 0` (con-leche's
  `scanLineFwd` run over the buffer as `parseBytes` runs it, without applying the lines): `0` if
  every line scans, else the number of the first line that does not; so `r = 0` whenever
  con-leche's `parseBytes b` succeeds, and for `r ≠ 0` `parseBytes b` fails at line `r` or
  earlier.

"Whenever it returns": an L run can also end in an error (out of fuel, an out-of-bounds read);
the compiler maps those to the harness's `exhausted`/`error` outcomes, never to an answer.
-/

namespace ConAgua.Scan.ValidatorLink

open L L.Scan.Line L.Scan.Validator ConAgua.Scan.LineLink ConAgua.Scan.DriverLink

variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- One line: the L `scan_line` decides what con-leche's `scanLineFwd` decides. -/
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
      (scanLine_spec valProg b.data hsize rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl fuel _ rfl i.toUInt64 hi')
    exact this.2

/-- The whole buffer: `validate` returns con-leche's verdict. -/
theorem validate_run' (fuel : Nat) (r : List Word) (m' : Mem)
    (h : run valProg fuel "validate" [] { bytes := #[b.data] } = .ok (r, m')) :
    r = [UInt64.ofNat (scanDriver b 0 0)] := by
  rw [← validN_zero b h64 hsize]
  exact (validate_run b.data hsize fuel r m' h).1

/-- If con-leche parses the buffer, the validator (when it returns) accepts it. -/
theorem validate_accepts (fuel : Nat) (r : List Word) (m' : Mem)
    (h : run valProg fuel "validate" [] { bytes := #[b.data] } = .ok (r, m'))
    (res : ConLeche.Frontend.ParseResultD) (hp : ConLeche.Frontend.parseBytes b = .ok res) :
    r = [0] := by
  rw [(validate_run b.data hsize fuel r m' h).1, validN_of_parseBytes_ok b h64 hsize res hp]

/-- If the validator rejects at line `n`, con-leche's parse fails at line `n` or before. -/
theorem validate_rejects (fuel : Nat) (n : Word) (m' : Mem)
    (h : run valProg fuel "validate" [] { bytes := #[b.data] } = .ok ([n], m')) (hn : n ≠ 0) :
    ∃ c k, ConLeche.Frontend.parseBytes b = .error (c, k) ∧ k ≤ n.toNat := by
  have := (validate_run b.data hsize fuel [n] m' h).1
  simp only [List.cons.injEq, and_true] at this
  exact parseBytes_error_of_validN b h64 hsize n this.symm hn

end ConAgua.Scan.ValidatorLink
