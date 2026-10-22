import ConAgua.Arena.Checker
import ConAgua.Arena.DeclArms
import ConAgua.Arena.DeclCvg

/-!
# Every declaration-loop module (lane `decls3`)

Imports every module of the declaration loop's proofs, so one build checks them together and
lemma-name clashes between files surface here (as `IndAll.lean` does for the inductive stage).
-/
import ConAgua.Arena.DeclValSpec
import ConAgua.Arena.DeclValRef
