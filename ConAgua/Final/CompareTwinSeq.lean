module

public import ConAgua.Final.CompareTwinThr

@[expose] public section

/-!
# The sequential compared run's twin: the challenge has a model (lane compare2)

`TwinComparesAccepts` (`Final/CompareTwin.lean`): after the stages up to the challenge's index
build (`sI`), the solution's jobs run in order from `sI.worker` and end in `sJ`, and the
challenge's jobs (with the solution) run in order from `sJ`. It is the threaded run with one
worker (`TwinComparesAccepts.pooled`), so its conclusions are the threaded ones
(`Final/CompareTwinThr.lean`).
-/

namespace ConAgua.Final

open ConLeche

universe w

/-- **The challenge of a sequentially compared run has a model**: con-leche's parser reads the
challenge, and its prepared records, each hole the axiom of its statement, have a model in every
set theory. Nothing is concluded about the solution. -/
theorem twinComparesAccepts_model (V : Type w) [SetTheory V] {bC bS : ByteArray}
    (h : TwinComparesAccepts bC bS) :
    ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
      ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      Nonempty (Model V (ConLeche.streamEnv
        ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord))) :=
  twinComparesAcceptsPooled_model V h.pooled

/-- **No `False` in the challenge of a sequentially compared run**: a challenge file that declares
a theorem of type `False` is not accepted, whatever the solution. -/
theorem twinComparesAccepts_no_False (V : Type w) [SetTheory V] {bC bS : ByteArray}
    (hfalse : jsonWithTheoremFalse [bC]) (h : TwinComparesAccepts bC bS) : False :=
  twinComparesAcceptsPooled_no_False V hfalse h.pooled

/-- info: 'ConAgua.Final.twinComparesAccepts_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms twinComparesAccepts_model

/-- info: 'ConAgua.Final.twinComparesAccepts_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms twinComparesAccepts_no_False

end ConAgua.Final
