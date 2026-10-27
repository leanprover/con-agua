import ConAgua.Arena.Checker
import ConAgua.Arena.PromoteCITags
-- Every module of the declaration loop's proofs (lane decls3): one build checks them together and
-- lemma-name clashes between files surface here, as IndAll.lean does for the inductive stage.
-- Imports only: append new modules at the end.

/-!
# Every declaration-loop module (lane `decls3`)

Imports every module of the declaration loop's proofs, so one build checks them together and
lemma-name clashes between files surface here (as `IndAll.lean` does for the inductive stage).
-/
