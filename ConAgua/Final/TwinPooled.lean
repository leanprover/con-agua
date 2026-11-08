module

public import ConAgua.Final.Twin
import ConLeche.Model.Denotes
import ConLeche.Model.Fold
import ConLeche.Verify.Frontend.FileFalse
import ConLeche.Verify.Frontend.Prepare
import ConRon.Bridge.Stages
import ConRon.Bridge.Frontend.Capstone
import ConRon.Bridge.Inductives.Decl

@[expose] public section

/-!
# The twin's pipeline with phase B as con-ron's pool (lane parmode)

The threaded mode checks the pending groups on several workers; what its accept means on the twin
side is con-ron's `PooledAccepts` (`ConRon/Arena/Pooled.lean`): phase A accepted, and a family of
group lists covering every pending group, each accepted by `checkPendingList` from the phase-A
state's worker. `TwinAcceptsPooled` is `TwinAccepts` with that phase B; `TwinAccepts` is the pool
with one part (`TwinAccepts.pooled`). Its consequences (con-leche's pure fold, the model, no
theorem of type `False`) are `Twin.lean`'s, through Theorem 1 for the pool
(`Arena.pooledAccepts_bridge`), which is what `twinAccepts_pure` already uses.
(Lane parallel's `Twin.lean` changes, as a separate file.)
-/

namespace ConAgua.Final

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend

universe w

/-- **The twin accepts `chunks` with the check phase as con-ron's pool.** -/
def TwinAcceptsPooled (chunks : List ByteArray) : Prop :=
  ∃ (pins : List NatOpPinSet) (sA sB sC sD sE sF : AState) (pre : PreludeIx) (r : ParseResultD)
    (ds : Array IDeclaration) (ipins : List INatOpPinSet) (I : IStreamIndex),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧
    parseChunks chunks sB = .ok (.ok r, sC) ∧
    preparePrelude pre r.decls sC = .ok (ds, sD) ∧
    internAllPins pins sD = .ok (ipins, sE) ∧
    ConRon.Arena.PooledAccepts .verified ipins ds sE I sF

theorem TwinAccepts.pooled {chunks : List ByteArray} (h : TwinAccepts chunks) :
    TwinAcceptsPooled chunks := by
  obtain ⟨pins, sA, sB, sC, sD, sE, sF, pre, r, ds, ipins, I, hA, hB, hC, hD, hE, hF⟩ := h
  exact ⟨pins, sA, sB, sC, sD, sE, sF, pre, r, ds, ipins, I, hA, hB, hC, hD, hE, pooledAccepts_of_seq hF⟩

/-- **What the pooled accept means, in con-leche's terms**: con-leche's parser reads the chunks and
its pure fold accepts the parsed records prepared with some prelude (Theorem 1 at the check
phase takes a set theory, `Arena.pooledAccepts_bridge`). -/
theorem twinAcceptsPooled_pure (V : Type w) [SetTheory V] {chunks : List ByteArray}
    (h : TwinAcceptsPooled chunks) :
    ∃ (pins : List NatOpPinSet) (preC : ConLeche.Frontend.PreludeIx)
      (rc : ConLeche.Frontend.ParseResultD) (F : Nat),
      ConLeche.Frontend.parseChunks chunks = .ok rc ∧
      checkDeclsPure .verified (fueledOps .verified F) pins
        (ConLeche.Frontend.preparePrelude preC rc.decls).toList =
        .ok (ConLeche.Cached.streamEnv (ConLeche.Frontend.preparePrelude preC rc.decls).toList) := by
  obtain ⟨pins, sA, sB, sC, sD, sE, sF, pre, r, ds, ipins, I, hA, hB, hC, hD, hE, hF⟩ := h
  have hk : CoreSpec ConRon.Arena.checkFuel := CoreSpec.of_core
  have hind : IndSpec := ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpd, rc, preC, hrc, hden⟩ :=
    ConRon.Bridge.stages_frame hA hB hC hD hE
  obtain ⟨F, hpure⟩ :=
    ConRon.Bridge.Arena.pooledAccepts_bridge V hk hind hst hoff hpp hpps hipins hpd hden hF
  exact ⟨pins, preC, rc, F, hrc, hpure⟩

/-- **The model** of what the pool accepts. -/
theorem twinAcceptsPooled_model (V : Type w) [SetTheory V] {chunks : List ByteArray}
    (h : TwinAcceptsPooled chunks) :
    ∃ (pins : List NatOpPinSet) (preC : ConLeche.Frontend.PreludeIx)
      (rc : ConLeche.Frontend.ParseResultD) (F : Nat) (env : Env),
      ConLeche.Frontend.parseChunks chunks = .ok rc ∧
      checkDeclsPure .verified (fueledOps .verified F) pins
        (ConLeche.Frontend.preparePrelude preC rc.decls).toList = .ok env ∧
      Nonempty (Model V env) := by
  obtain ⟨pins, preC, rc, F, hrc, hpure⟩ := twinAcceptsPooled_pure V h
  obtain ⟨m⟩ := ConLeche.Model.checkDeclsPure_sound_of (V := V) (pins := pins) hpure
  exact ⟨pins, preC, rc, F, _, hrc, hpure, ⟨ConLeche.Model.Model.ofEnvModelM m⟩⟩

/-- **No `False`** under the pool's accept. -/
theorem twinAcceptsPooled_no_False (V : Type w) [SetTheory V] {chunks : List ByteArray}
    (hfalse : jsonWithTheoremFalse chunks) (h : TwinAcceptsPooled chunks) : False := by
  obtain ⟨pins, preC, rc, F, hrc, hpure⟩ := twinAcceptsPooled_pure V h
  obtain ⟨cv, vl, hty, hmem⟩ := ConLeche.Frontend.parseChunks_jsonWithTheoremFalse hfalse hrc
  exact no_False_theorem_accepted_pure V
    (by simpa using ConLeche.Frontend.mem_preparePrelude (pre := preC) hmem) hty hpure

end ConAgua.Final
