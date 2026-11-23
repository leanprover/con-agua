module

public import ConRon.Bridge.Specs
public import ConRon.Bridge.Frontend.Chunks
import ConRon.Bridge.Frontend.Capstone
public import ConRon.Arena.Frontend.Prepare
public import ConRon.Arena.Frontend.Prelude
import ConRon.Bridge.Checker.Pins
public import ConRon.Bridge.Frontend.Prepare
import ConLeche.Verify.Frontend.Prepare
public import ConRon.Bridge.Stages
public import ConLeche.Verify.Cached.DeclPushes
import ConRon.Bridge.Inductives.Decl
import ConLeche.Model.Denotes
import ConLeche.Model.OfEnvModelM
import ConLeche.Model.Fold
import ConLeche.Verify.Frontend.FileFalse
import all ConRon.Bridge.Frontend.Prepare
public import ConLeche.Accepts
public import ConLeche.Denotes
public import ConRon.Arena.Pooled
public import ConRon.Bridge.Checker.Decl

@[expose] public section

/-!
# The twin's pipeline, from the start state to con-leche

con-ron's `ConRon/Capstone.lean` composes its Theorem 2 (Aeneas Rust ⇄ twin) with Theorem 1 (twin ⇒
con-leche's pure fold). It imports `ConRon.Refine2` (Aeneas), which is not built here. Its twin-side
glue (`stages_frame`, `stages_model`, `stages_false_mem`, `stages_no_False`) uses only `Bridge`
lemmas; this file restates it on top of the vendored `ConRonBridge`, for the x64 checker's single
worker:

* `SeqAccepts`: the stream index (`buildIndex`) and then every record's job, in fold order, as ONE
  `checkJobList` from the index state's worker, as the twin's own `checkStream`. It is
  `PooledAccepts` with one part (`pooledAccepts_of_seq`).
* `TwinAccepts chunks`: the six stages from `AState.init EStore.empty`, the last `SeqAccepts`, at
  some pin list. This is what an accepting run of the driver must produce (`drv_twinAccepts`,
  `ConAgua/Checker/ParDriverTwin.lean`).
* `twinAccepts_pure`: then con-leche's own parser reads the chunks, and con-leche's pure fold
  accepts the parsed records prepared with some prelude, at the same pin list. As con-ron's
  Theorem 1 at the check phase (`Arena.pooledAccepts_bridge`): each prefix's environment is well
  formed by con-leche's model-free `foldlM_checkDecl_envWF`. `twinAccepts_model`,
  `twinAccepts_no_False`: the model, and no theorem of type `False`.

The prelude is free: `builtinPreludeE_run` gives *some* con-leche prelude `preC` the twin's prelude
denotes, and con-leche's `preparePrelude` puts its records into the checked stream, so soundness
holds whatever the prelude bytes are. The pins are free for the same reason as in con-leche.
-/

namespace ConAgua.Final

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend

universe w

/-- **The x64 checker's check phase**: the stream index built (`buildIndex`, ending in `s'`), then
every record's job in fold order on one worker made from `s'`, accepted. -/
def SeqAccepts (mode : CheckMode) (pins : List INatOpPinSet) (ds : Array IDeclaration)
    (s : AState) (I : IStreamIndex) (s' : AState) : Prop :=
  ∃ s'' : AState, buildIndex ds s = .ok (.ok I, s') ∧
    checkJobList mode pins none I ds (List.range ds.size) s'.worker = .ok (.ok (), s'')

/-- One worker is a pool. -/
theorem pooledAccepts_of_seq {mode : CheckMode} {pins : List INatOpPinSet}
    {ds : Array IDeclaration} {s : AState} {I : IStreamIndex} {s' : AState}
    (h : SeqAccepts mode pins ds s I s') : ConRon.Arena.PooledAccepts mode pins ds s I s' := by
  obtain ⟨s'', hI, hJ⟩ := h
  refine ⟨[List.range ds.size], hI, fun t ht => ⟨_, List.mem_singleton_self _, List.mem_range.mpr ht⟩,
    fun w hw t ht => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · rw [List.mem_singleton] at hw; subst hw; exact List.mem_range.mp ht
  · rw [List.mem_singleton] at hw; subst hw; exact List.pairwise_lt_range
  · rw [List.mem_singleton] at hw; subst hw; exact ⟨s'', hJ⟩

/-- **The twin accepts `chunks`**: the stages con-ron's binary runs, from the twin's start state
`AState.init EStore.empty`, at some pin list, the check phase on one worker. -/
def TwinAccepts (chunks : List ByteArray) : Prop :=
  ∃ (pins : List NatOpPinSet) (sA sB sC sD sE sF : AState) (pre : PreludeIx) (r : ParseResultD)
    (ds : Array IDeclaration) (ipins : List INatOpPinSet) (I : IStreamIndex),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧
    parseChunks chunks sB = .ok (.ok r, sC) ∧
    preparePrelude pre r.decls sC = .ok (ds, sD) ∧
    internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE) ∧
    SeqAccepts .verified ipins ds sE I sF

/-- **What the twin's accept means, in con-leche's terms**: con-leche's parser reads the chunks, and
con-leche's pure fold accepts the parsed records prepared with some prelude, at the twin's pin
list. con-ron's `stages_frame`, then Theorem 1 at the check phase (`Arena.pooledAccepts_bridge`,
with its two tier specs discharged by `CoreSpec.of_core` and `indSpec_of_bridge`). -/
theorem twinAccepts_pure {chunks : List ByteArray}
    (h : TwinAccepts chunks) :
    ∃ (pins : List NatOpPinSet) (preC : ConLeche.Frontend.PreludeIx)
      (rc : ConLeche.Frontend.ParseResultD) (F : Nat),
      ConLeche.Frontend.parseChunks chunks = .ok rc ∧
      checkDeclsPure .verified (fueledOps .verified F) pins
        (ConLeche.Frontend.preparePrelude preC rc.decls).toList =
        .ok (ConLeche.streamEnv (ConLeche.Frontend.preparePrelude preC rc.decls).toList) := by
  obtain ⟨pins, sA, sB, sC, sD, sE, sF, pre, r, ds, ipins, I, hA, hB, hC, hD, hE, hF⟩ := h
  have hk : CoreSpec ConRon.Arena.checkFuel := CoreSpec.of_core
  have hind : IndSpec := ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpd, rc, preC, hrc, hden⟩ :=
    ConRon.Bridge.stages_frame hA hB hC hD hE
  obtain ⟨F, hpure⟩ :=
    ConRon.Bridge.Arena.pooledAccepts_bridge hk hind hst hoff hpp hpps hipins hpd hden
      (pooledAccepts_of_seq hF)
  exact ⟨pins, preC, rc, F, hrc, hpure⟩

/-- con-ron: proof/ConRon/Capstone.lean model_exists — **the model**: the environment the pure fold
accepts on the twin's stream has a model in every set theory. -/
theorem twinAccepts_model (V : Type w) [SetTheory V] {chunks : List ByteArray}
    (h : TwinAccepts chunks) :
    ∃ (pins : List NatOpPinSet) (preC : ConLeche.Frontend.PreludeIx)
      (rc : ConLeche.Frontend.ParseResultD) (F : Nat) (env : Env),
      ConLeche.Frontend.parseChunks chunks = .ok rc ∧
      checkDeclsPure .verified (fueledOps .verified F) pins
        (ConLeche.Frontend.preparePrelude preC rc.decls).toList = .ok env ∧
      Nonempty (Model V env) := by
  obtain ⟨pins, preC, rc, F, hrc, hpure⟩ := twinAccepts_pure h
  obtain ⟨m⟩ := ConLeche.Model.checkDeclsPure_sound_of (V := V) (pins := pins) hpure
  exact ⟨pins, preC, rc, F, _, hrc, hpure, ⟨ConLeche.Model.Model.ofEnvModelM m⟩⟩

/-- con-ron: proof/ConRon/Capstone.lean no_False_declaration — **no `False`**: the twin does not
accept a file that declares a theorem of type `False` (in `jsonWithTheoremFalse`'s shape).
con-leche's parse of such chunks holds a theorem record of type `False`
(`parseChunks_jsonWithTheoremFalse`), the preparation keeps it (`mem_preparePrelude`), and the pure
fold never accepts it (`no_False_theorem_accepted_pure`). -/
theorem twinAccepts_no_False (V : Type w) [SetTheory V] {chunks : List ByteArray}
    (hfalse : jsonWithTheoremFalse chunks) (h : TwinAccepts chunks) : False := by
  obtain ⟨pins, preC, rc, F, hrc, hpure⟩ := twinAccepts_pure h
  obtain ⟨cv, vl, hty, hmem⟩ := ConLeche.Frontend.parseChunks_jsonWithTheoremFalse hfalse hrc
  exact no_False_theorem_accepted_pure V
    (by simpa using ConLeche.Frontend.mem_preparePrelude (pre := preC) hmem) hty hpure

end ConAgua.Final
