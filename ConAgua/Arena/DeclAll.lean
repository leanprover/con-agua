import ConAgua.Arena.Checker
import ConAgua.Arena.DeclArms
import ConAgua.Arena.DeclCvg
import ConAgua.Arena.DeclMasterStage
import ConAgua.Arena.DeclCanonSpec
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclCanonSpec2
import ConAgua.Arena.DeclCanonView
import ConAgua.Arena.DeclCanonView2
import ConAgua.Arena.DeclCanonLvl
import ConAgua.Arena.DeclCanonExpr
import ConAgua.Arena.DeclCanonExpr2
import ConAgua.Arena.DeclCanonNames
import ConAgua.Arena.DeclCanonConst
import ConAgua.Arena.DeclCanonRules

/-!
# Every declaration-loop module (lane `decls3`)

Imports every module of the declaration loop's proofs, so one build checks them together and
lemma-name clashes between files surface here (as `IndAll.lean` does for the inductive stage).
-/
