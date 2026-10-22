-- Every module of the declaration loop's proofs (lane decls3): one build checks them together and
-- lemma-name clashes between files surface here, as IndAll.lean does for the inductive stage.
-- Imports only: append new modules at the end.
import ConAgua.Arena.Checker
import ConAgua.Arena.DeclArms
import ConAgua.Arena.DeclCvg
import ConAgua.Arena.DeclValSpec
import ConAgua.Arena.DeclValRef
import ConAgua.Arena.DeclBasisSpec
import ConAgua.Arena.DeclRomStubs
import ConAgua.Arena.DeclReduceSpec
import ConAgua.Arena.DeclArmLoop
import ConAgua.Arena.DeclCheckLoop
import ConAgua.Arena.DeclMasterStage
import ConAgua.Arena.DeclCanonSpec
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclBasisSpec2
import ConAgua.Arena.DeclReduceSpec2
import ConAgua.Arena.DeclReducePin
import ConAgua.Arena.DeclArmOpaque
import ConAgua.Arena.DeclAxiomSpec
import ConAgua.Arena.DeclCanonSpec2
import ConAgua.Arena.DeclAxiomSpec2
import ConAgua.Arena.DeclAxiomSpec3
import ConAgua.Arena.DeclAxiomSpec4
import ConAgua.Arena.DeclArmQuot
