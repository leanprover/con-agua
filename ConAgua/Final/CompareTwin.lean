module

public import ConAgua.Final.Twin
public import ConRon.Bridge.Compare.Stages
public import ConRon.Arena.Justify
public import ConRon.Arena.Pooled
import ConRon.Bridge.Inductives.Decl
import ConLeche.Model.OfEnvModelM
import ConRon.Bridge.Specs

@[expose] public section

/-!
# The twin's compared run, from the start state to con-leche

con-ron's `--compare -- C S` on two lean4export files (its `driver/compare_json.rs`, its
capstones `model_exists_compare` and `no_False_compare`) at the twin's level, as `Final/Twin.lean`
states the flat run:

* `SeqAcceptsJ mode pins J ds s I s'`: the stream index of `ds` (`buildIndex`, ending in `s'`), then
  every record's job in fold order on one worker made from `s'`, with the solution `J`, accepted.
  `SeqAccepts` (`Final/Twin.lean`) is its `J = none`.
* `TwinComparesAccepts bC bS`: the stages from the twin's start state: the reserved pins, the
  prelude, the challenge's parse, then the solution's into the same store, the solution's
  preparation, the pins, the solution's check phase (no solution), the challenge's preparation from
  the state the solution's index build left, its side records (each hole the axiom of its
  statement), and its check phase with the solution `solutionOf IS recsC` (the solution's index
  and the challenge's record mates).
* `twinComparesAccepts_model`: then con-leche's parser reads the challenge, and its prepared
  records, each hole the axiom of its statement (`ConLeche.Cached.sideRecord`), have a model in
  every set theory (con-ron's `stagesC_model`, twin-side half of `model_exists_compare`).
  Nothing is concluded about the solution.
* `twinComparesAccepts_no_False`: a challenge file that declares a theorem of type `False` is not
  accepted, whatever the solution (con-ron's `stagesC_no_False`).
-/

namespace ConAgua.Final

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend

universe w

/-- **The x64 checker's check phase with a solution**: the stream index built (`buildIndex`, ending
in `s'`), then every record's job in fold order on one worker made from `s'`, with the solution
`J`, accepted. -/
def SeqAcceptsJ (mode : CheckMode) (pins : List INatOpPinSet) (J : Option ISolution)
    (ds : Array IDeclaration) (s : AState) (I : IStreamIndex) (s' : AState) : Prop :=
  ∃ s'' : AState, buildIndex ds s = .ok (.ok I, s') ∧
    checkJobList mode pins J I ds (List.range ds.size) s'.worker = .ok (.ok (), s'')

/-- **The twin accepts the comparison of the challenge `bC` with the solution `bS`** (con-ron's
`compare_json`): the stages from the twin's start state, both files parsed into the one store,
the solution's records prepared and checked (one worker), the challenge's records prepared from
the state the solution's index build left, read with the solution (`sideRecordsGo`) and checked
with it (one worker), at some pin list. -/
def TwinComparesAccepts (bC bS : ByteArray) : Prop :=
  ∃ (pins : List NatOpPinSet) (sA sB sC sC' sD sE sF sG sH sI : AState) (pre : PreludeIx)
    (rC rS : ParseResultD) (dsS dsC : Array IDeclaration) (recsC : List IDeclaration)
    (ipins : List INatOpPinSet) (IS IC : IStreamIndex),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧
    parseChunks [bC] sB = .ok (.ok rC, sC) ∧
    parseChunks [bS] sC = .ok (.ok rS, sC') ∧
    preparePrelude pre rS.decls sC' = .ok (dsS, sD) ∧
    internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE) ∧
    SeqAcceptsJ .verified ipins none dsS sE IS sF ∧
    preparePrelude pre rC.decls sF = .ok (dsC, sG) ∧
    sideRecordsGo [] dsC.toList sG = .ok (recsC, sH) ∧
    SeqAcceptsJ .verified ipins (some (solutionOf IS recsC)) recsC.toArray sH IC sI

/-- One worker is a pool, at any solution. -/
theorem pooled_of_seqJ {mode : CheckMode} {pins : List INatOpPinSet} {J : Option ISolution}
    {ds : Array IDeclaration} {s : AState} {I : IStreamIndex} {s' : AState}
    (h : SeqAcceptsJ mode pins J ds s I s') :
    ∃ (parts : List (List Nat)), buildIndex ds s = .ok (.ok I, s') ∧
      (∀ t < ds.size, ∃ w ∈ parts, t ∈ w) ∧ (∀ w ∈ parts, ∀ t ∈ w, t < ds.size) ∧
      (∀ w ∈ parts, w.Pairwise (· < ·)) ∧
      (∀ w ∈ parts, ∃ s'', checkJobList mode pins J I ds w s'.worker = .ok (.ok (), s'')) := by
  obtain ⟨s'', hI, hJ⟩ := h
  refine ⟨[List.range ds.size], hI, fun t ht => ⟨_, List.mem_singleton_self _, List.mem_range.mpr ht⟩,
    fun w hw t ht => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · rw [List.mem_singleton] at hw; subst hw; exact List.mem_range.mp ht
  · rw [List.mem_singleton] at hw; subst hw; exact List.pairwise_lt_range
  · rw [List.mem_singleton] at hw; subst hw; exact ⟨s'', hJ⟩

/-- **The twin accepts the comparison with both check phases as con-ron's pool** (`--jobs`): as
`TwinComparesAccepts`, the solution's check phase `PooledAccepts` (no solution) and the
challenge's `PooledAcceptsJ` with the solution (`ConRon/Arena/Pooled.lean`): each a family of job
lists, one per worker, covering every record position, each increasing, each accepted from the
index state's worker. -/
def TwinComparesAcceptsPooled (bC bS : ByteArray) : Prop :=
  ∃ (pins : List NatOpPinSet) (sA sB sC sC' sD sE sF sG sH sI : AState) (pre : PreludeIx)
    (rC rS : ParseResultD) (dsS dsC : Array IDeclaration) (recsC : List IDeclaration)
    (ipins : List INatOpPinSet) (IS IC : IStreamIndex),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧
    parseChunks [bC] sB = .ok (.ok rC, sC) ∧
    parseChunks [bS] sC = .ok (.ok rS, sC') ∧
    preparePrelude pre rS.decls sC' = .ok (dsS, sD) ∧
    internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE) ∧
    PooledAccepts .verified ipins dsS sE IS sF ∧
    preparePrelude pre rC.decls sF = .ok (dsC, sG) ∧
    sideRecordsGo [] dsC.toList sG = .ok (recsC, sH) ∧
    PooledAcceptsJ .verified ipins (some (solutionOf IS recsC)) recsC.toArray sH IC sI

/-- The sequential comparison is the pool with one worker per phase. -/
theorem TwinComparesAccepts.pooled {bC bS : ByteArray} (h : TwinComparesAccepts bC bS) :
    TwinComparesAcceptsPooled bC bS := by
  obtain ⟨pins, sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, pre, rC, rS, dsS, dsC, recsC, ipins, IS, IC,
    hA, hB, hC, hCS, hDS, hE, hFS, hDC, hside, hFC⟩ := h
  exact ⟨pins, sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, pre, rC, rS, dsS, dsC, recsC, ipins, IS, IC,
    hA, hB, hC, hCS, hDS, hE, pooledAccepts_of_seq hFS, hDC, hside, pooled_of_seqJ hFC⟩

/-- con-ron: proof/ConRon/MainTheorem/Stages.lean model_exists_compare — **the challenge of a
pooled comparison has a model** (`twinComparesAccepts_model` for the pool). -/
theorem twinComparesAcceptsPooled_model (V : Type w) [SetTheory V] {bC bS : ByteArray}
    (h : TwinComparesAcceptsPooled bC bS) :
    ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
      ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      Nonempty (Model V (ConLeche.streamEnv
        ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord))) := by
  obtain ⟨pins, sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, pre, rC, rS, dsS, dsC, recsC, ipins, IS, IC,
    hA, hB, hC, hCS, hDS, hE, hFS, hDC, hside, hFC⟩ := h
  have hk : CoreSpec ConRon.Arena.checkFuel := CoreSpec.of_core
  have hind : IndSpec := ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨-, rcC, preC, dsP, hclC, rfl, -, ⟨hmod⟩⟩ :=
    ConRon.Bridge.stagesC_model V hk hind hA hB hC hCS hDS hE hFS hDC hside hFC
  exact ⟨rcC, preC, hclC, ⟨ConLeche.Model.Model.ofEnvModelM hmod⟩⟩

/-- con-ron: proof/ConRon/MainTheorem/Stages.lean no_False_compare — **no `False` in the challenge
of a pooled comparison** (`twinComparesAccepts_no_False` for the pool). -/
theorem twinComparesAcceptsPooled_no_False (V : Type w) [SetTheory V] {bC bS : ByteArray}
    (hfalse : jsonWithTheoremFalse [bC]) (h : TwinComparesAcceptsPooled bC bS) : False := by
  obtain ⟨pins, sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, pre, rC, rS, dsS, dsC, recsC, ipins, IS, IC,
    hA, hB, hC, hCS, hDS, hE, hFS, hDC, hside, hFC⟩ := h
  have hk : CoreSpec ConRon.Arena.checkFuel := CoreSpec.of_core
  have hind : IndSpec := ConRon.Bridge.Inductives.indSpec_of_bridge
  exact ConRon.Bridge.stagesC_no_False V hk hind hfalse hA hB hC hCS hDS hE hFS hDC hside hFC

/-- con-ron: proof/ConRon/MainTheorem/Stages.lean model_exists_compare — **the challenge has a
model**: con-leche's parser reads the challenge, and its prepared records, each hole the axiom of
its statement, denote a stream whose environment has a model in every set theory. Nothing is
concluded about the solution. -/
theorem twinComparesAccepts_model (V : Type w) [SetTheory V] {bC bS : ByteArray}
    (h : TwinComparesAccepts bC bS) :
    ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
      ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      Nonempty (Model V (ConLeche.streamEnv
        ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord))) := by
  obtain ⟨pins, sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, pre, rC, rS, dsS, dsC, recsC, ipins, IS, IC,
    hA, hB, hC, hCS, hDS, hE, hFS, hDC, hside, hFC⟩ := h
  have hk : CoreSpec ConRon.Arena.checkFuel := CoreSpec.of_core
  have hind : IndSpec := ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨-, rcC, preC, dsP, hclC, rfl, -, ⟨hmod⟩⟩ :=
    ConRon.Bridge.stagesC_model V hk hind hA hB hC hCS hDS hE
      (pooledAccepts_of_seq hFS) hDC hside (pooled_of_seqJ hFC)
  exact ⟨rcC, preC, hclC, ⟨ConLeche.Model.Model.ofEnvModelM hmod⟩⟩

/-- con-ron: proof/ConRon/MainTheorem/Stages.lean no_False_compare — **no `False` in an accepted
challenge**: the twin does not accept a comparison whose challenge file declares a theorem of type
`False` (in `jsonWithTheoremFalse`'s shape), whatever the solution. -/
theorem twinComparesAccepts_no_False (V : Type w) [SetTheory V] {bC bS : ByteArray}
    (hfalse : jsonWithTheoremFalse [bC]) (h : TwinComparesAccepts bC bS) : False := by
  obtain ⟨pins, sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, pre, rC, rS, dsS, dsC, recsC, ipins, IS, IC,
    hA, hB, hC, hCS, hDS, hE, hFS, hDC, hside, hFC⟩ := h
  have hk : CoreSpec ConRon.Arena.checkFuel := CoreSpec.of_core
  have hind : IndSpec := ConRon.Bridge.Inductives.indSpec_of_bridge
  exact ConRon.Bridge.stagesC_no_False V hk hind hfalse hA hB hC hCS hDS hE
    (pooledAccepts_of_seq hFS) hDC hside (pooled_of_seqJ hFC)

/-- info: 'ConAgua.Final.twinComparesAccepts_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms twinComparesAccepts_model

/-- info: 'ConAgua.Final.twinComparesAccepts_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms twinComparesAccepts_no_False

/-- info: 'ConAgua.Final.twinComparesAcceptsPooled_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms twinComparesAcceptsPooled_model

/-- info: 'ConAgua.Final.twinComparesAcceptsPooled_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms twinComparesAcceptsPooled_no_False

end ConAgua.Final
