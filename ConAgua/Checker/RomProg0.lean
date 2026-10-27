import ConAgua.Checker.Prog
import ConAgua.Rom.Stage
import ConAgua.Compiler.WFFast
import ConAgua.Compiler.WriteSetSplit
import ConAgua.Arena.LevelIntern
import ConAgua.Arena.LevelSubstLP

/-!
# The checker's program under the pin-data substitution: the tools (lane `pipeline`)

`checkerProg` has no `st8` at all (so none to `PB`), and a function of it that reads no pin data
is unchanged by `Prog.subPB bs` (`lookup_subPB_noPB`). The lookups themselves are one `rfl` each
(`RomProgA.lean`, `RomProgB.lean`); `RomProg.lean` assembles the ROM stages' program hypotheses.
-/

namespace L.Checker

open L L.Rom L.Arena L.Compiler

/-- Every function of `checkerProg` is free of byte stores (one kernel check per chunk). -/
prog_all checkerProg_noSt8_all : checkerProg (fun x => x.2.body.noSt8)

/-- No function of `checkerProg` stores to `PB` (one kernel check per chunk). -/
prog_all checkerProg_noSt8PB_all : checkerProg (fun x => x.2.body.noSt8PB)

theorem checkerProg_noSt8 : Prog.noSt8 checkerProg = true := by
  unfold Prog.noSt8; exact List.all_eq_true.2 checkerProg_noSt8_all

/-- **`checkerProg` never stores to the pin-data buffer.** -/
theorem checkerProg_noSt8PB : Prog.noSt8PB checkerProg = true := by
  unfold Prog.noSt8PB; exact List.all_eq_true.2 checkerProg_noSt8PB_all

theorem _root_.L.Stmt.noSt8_subPB (bs : List UInt8) (s : Stmt) : (s.subPB bs).noSt8 = s.noSt8 := by
  induction s <;> simp_all [Stmt.subPB, Stmt.noSt8]

theorem _root_.L.Prog.noSt8_subPB (bs : List UInt8) (p : Prog) : (Prog.subPB bs p).noSt8 = p.noSt8 := by
  simp only [Prog.noSt8, Prog.subPB, List.all_map]
  congr 1; funext d; simp [FunDecl.subPB, Stmt.noSt8_subPB]

theorem checkerProg_subPB_noSt8 (bs : List UInt8) : (Prog.subPB bs checkerProg).noSt8 = true := by
  rw [Prog.noSt8_subPB]; exact checkerProg_noSt8

/-- A function of `checkerProg` that reads no pin data, in the substituted program. -/
theorem lkN (bs : List UInt8) {f : FnName} {fd : FunDecl} (h : checkerProg.lookup f = some fd)
    (hn : fd.body.noPB = true) : (Prog.subPB bs checkerProg).lookup f = some fd :=
  lookup_subPB_noPB bs h hn

/-- A pin-data reader of `checkerProg`, in the substituted program. -/
theorem lkR (bs : List UInt8) {f : FnName} {fd g : FunDecl} (h : checkerProg.lookup f = some fd)
    (he : fd.subPB bs = g) : (Prog.subPB bs checkerProg).lookup f = some g := by
  rw [lookup_subPB, h, ← he]; rfl

end L.Checker
