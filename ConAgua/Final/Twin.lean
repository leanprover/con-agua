import ConRon.Bridge.Frontend.Capstone
import ConRon.Bridge.Checker.Phased
import ConRon.Bridge.Inductives.Decl
import ConLeche.Model.Denotes
import ConLeche.Model.Fold
import ConLeche.Verify.Frontend.FileFalse

/-!
# The twin's pipeline, from the start state to con-leche

con-ron's `ConRon/Capstone.lean` composes its Theorem 2 (Aeneas Rust ⇄ twin) with Theorem 1 (twin ⇒
con-leche's pure fold). It imports `ConRon.Refine2` (Aeneas), which is not built here. Its twin-side
glue (`stages_frame`, `stages_model`, `stages_false_mem`, `stages_no_False`) uses only `Bridge`
lemmas; this file restates it on top of the vendored `ConRonBridge`, for the x64 checker's single
worker:

* `SeqAccepts`: phase A (`installFold`) and then phase B as ONE `checkPendingList` over every pending
  record from the phase-A state's worker, as con-ron's sequential `check_decls_phased`. It is
  `PooledAccepts` with one part (`pooledAccepts_of_seq`).
* `TwinAccepts chunks`: the six stages from `AState.init EStore.empty`, the last `SeqAccepts`, at
  some pin list. This is what an accepting run of the driver must produce (`drv_twinAccepts`,
  `ConAgua/Checker/ParDriverTwin.lean`).
* `twinAccepts_pure`: then con-leche's own parser reads the chunks, and con-leche's pure fold
  accepts the parsed records prepared with some prelude, at the same pin list. `twinAccepts_model`,
  `twinAccepts_no_False`: the model, and no theorem of type `False`.

The prelude is free: `builtinPreludeE_run` gives *some* con-leche prelude `preC` the twin's prelude
denotes, and con-leche's `preparePrelude` puts its records into the checked stream, so soundness
holds whatever the prelude bytes are. The pins are free for the same reason as in con-leche.
-/

namespace ConAgua.Final

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend

universe w

/-- **The x64 checker's fold**: phase A accepted with environment `fe` and pending records `pend`,
ending in `s'`; phase B, every pending record in order on one worker made from `s'`, accepted. -/
def SeqAccepts (mode : CheckMode) (pins : List INatOpPinSet) (ds : Array IDeclaration)
    (s : AState) (fe : IFEnv) (s' : AState) : Prop :=
  ∃ (n : Nat) (pend : Array PendingCheck) (s'' : AState),
    installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList s = .ok (.ok (n, fe, pend), s') ∧
    checkPendingList mode fe pend.toList s'.worker = .ok (.ok (), s'')

/-- One worker is a pool. -/
theorem pooledAccepts_of_seq {mode : CheckMode} {pins : List INatOpPinSet}
    {ds : Array IDeclaration} {s : AState} {fe : IFEnv} {s' : AState}
    (h : SeqAccepts mode pins ds s fe s') : ConRon.Arena.PooledAccepts mode pins ds s fe s' := by
  obtain ⟨n, pend, s'', hA, hB⟩ := h
  refine ⟨n, pend, [pend.toList], hA, fun pc hpc => ⟨_, List.mem_singleton_self _, hpc⟩,
    fun w hw pc hpc => ?_, fun w hw => ?_⟩
  · rw [List.mem_singleton] at hw; subst hw; exact hpc
  · rw [List.mem_singleton] at hw; subst hw; exact ⟨s'', hB⟩

/-- **The twin accepts `chunks`**: the stages con-ron's binary runs, from the twin's start state
`AState.init EStore.empty`, at some pin list, the fold on one worker. -/
def TwinAccepts (chunks : List ByteArray) : Prop :=
  ∃ (pins : List NatOpPinSet) (sA sB sC sD sE sF : AState) (pre : PreludeIx) (r : ParseResultD)
    (ds : Array IDeclaration) (ipins : List INatOpPinSet) (fe : IFEnv),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧
    parseChunks chunks sB = .ok (.ok r, sC) ∧
    preparePrelude pre r.decls sC = .ok (ds, sD) ∧
    internAllPins pins sD = .ok (ipins, sE) ∧
    SeqAccepts .verified ipins ds sE fe sF

/-- con-ron: proof/ConRon/Capstone.lean stages_frame — **the stages' frame, up to the fold**: after
the first five stages from the twin's start state the fold's start invariant holds, the pins denote,
and the prepared stream denotes con-leche's parse of the chunks prepared with some prelude `preC`.
(con-ron's version ends in `∃ dsP, denoteDecls … = some dsP`; this one names `dsP`.) -/
theorem stages_frame {chunks : List ByteArray} {pins : List NatOpPinSet}
    {sA sB sC sD sE : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunks sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE)) :
    sE.store.scratchOn = false ∧
      FoldOK .verified Env.empty (mkIFEnv IEnv.empty) sE ∧
      PinsDenote sE.store ipins pins ∧ PersPinSets ipins ∧
      (∀ x ∈ ds.toList, PersDecl x) ∧
      ∃ preC rc, ConLeche.Frontend.parseChunks chunks = .ok rc ∧
        denoteDecls sE.store ds.toList
          = some (ConLeche.Frontend.preparePrelude preC rc.decls).toList := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  have hc0 : (AState.init EStore.empty).caches = Caches.empty := rfl
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, hcachesA⟩ :=
    internReservedPins_run hok0 hoff0 hA
  obtain ⟨hstep1, hpersPre, preC, hrelPre⟩ :=
    builtinPreludeE_run hokA hoffA hpinsA hB
  obtain ⟨hstep2, hpersR, rc, hclR, hrelR⟩ :=
    parseChunks_run hstep1.ok
      (by rw [hstep1.scratch, hoffA]) (hpinsA.mono hstep1.ext hstep1.pins) hC
  obtain ⟨hstep3, hpersDs, hclPrep⟩ :=
    preparePrelude_run (preC := preC) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoffA])
      (hpinsA.mono (hstep1.trans hstep2).ext (hstep1.trans hstep2).pins)
      (denoteDeclArray_ext hstep2.ext hrelPre) hpersPre
      hrelR.decls hpersR hD
  have hoff3 : sD.store.scratchOn = false := by
    rw [hstep3.scratch, hstep2.scratch, hstep1.scratch]; exact hoffA
  obtain ⟨hokP, hxP, hpinsP, hppP, hipins, hpps, hoffP, hcachesP, -⟩ :=
    internAllPins_run hstep3.ok
      (hpinsA.mono ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
        (by rw [hstep3.pins, hstep2.pins, hstep1.pins]))
      (hppA.mono (by rw [hstep3.pins, hstep2.pins, hstep1.pins])) hoff3 hE
  refine ⟨hoffP, FoldOK_of_start hokP hpinsP hppP
      (((CacheOK.of_empty (s := sA) (by rw [hcachesA]; exact hc0)).monoF
            ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
            ((hstep1.cframe.trans hstep2.cframe).trans hstep3.cframe)).mono
        hxP hcachesP),
    hipins, hpps, fun x hx => hpersDs x (by simpa using hx), preC, rc, hclR,
    denoteDeclArray_iff.mp (denoteDeclArray_ext hxP hclPrep)⟩

/-- **What the twin's accept means, in con-leche's terms**: con-leche's parser reads the chunks, and
con-leche's pure fold accepts the parsed records prepared with some prelude, at the twin's pin
list. `stages_frame`, then Theorem 1 (`Arena.pooledAccepts_bridge`, with its two tier specs
discharged by `CoreSpec.of_core` and `indSpec_of_bridge`). -/
theorem twinAccepts_pure {chunks : List ByteArray} (h : TwinAccepts chunks) :
    ∃ (pins : List NatOpPinSet) (preC : ConLeche.Frontend.PreludeIx)
      (rc : ConLeche.Frontend.ParseResultD) (F : Nat) (env : Env),
      ConLeche.Frontend.parseChunks chunks = .ok rc ∧
      checkDeclsPure .verified (fueledOps .verified F) pins
        (ConLeche.Frontend.preparePrelude preC rc.decls).toList = .ok env := by
  obtain ⟨pins, sA, sB, sC, sD, sE, sF, pre, r, ds, ipins, fe, hA, hB, hC, hD, hE, hF⟩ := h
  have hk : CoreSpec .verified ConRon.Arena.checkFuel := CoreSpec.of_core rfl
  have hind : IndSpec .verified := ConRon.Bridge.Inductives.indSpec_of_bridge rfl hk
  obtain ⟨-, hfold, hipins, hpps, hpd, preC, rc, hrc, hden⟩ := stages_frame hA hB hC hD hE
  obtain ⟨env, F, -, hpure⟩ :=
    ConRon.Bridge.Arena.pooledAccepts_bridge rfl hk hind hpps hfold hipins hpd hden (pooledAccepts_of_seq hF)
  exact ⟨pins, preC, rc, F, env, hrc, hpure⟩

/-- con-ron: proof/ConRon/Capstone.lean stages_model — **the model**: the environment the pure fold
accepts on the twin's stream has a model in every set theory. -/
theorem twinAccepts_model (V : Type w) [SetTheory V] {chunks : List ByteArray}
    (h : TwinAccepts chunks) :
    ∃ (pins : List NatOpPinSet) (preC : ConLeche.Frontend.PreludeIx)
      (rc : ConLeche.Frontend.ParseResultD) (F : Nat) (env : Env),
      ConLeche.Frontend.parseChunks chunks = .ok rc ∧
      checkDeclsPure .verified (fueledOps .verified F) pins
        (ConLeche.Frontend.preparePrelude preC rc.decls).toList = .ok env ∧
      Nonempty (Model V env) := by
  obtain ⟨pins, preC, rc, F, env, hrc, hpure⟩ := twinAccepts_pure h
  obtain ⟨m⟩ := ConLeche.Model.checkDeclsPure_sound_of (V := V) (pins := pins) rfl hpure
  exact ⟨pins, preC, rc, F, env, hrc, hpure, ⟨ConLeche.Model.Model.ofEnvModelM m⟩⟩

/-- con-ron: proof/ConRon/Capstone.lean stages_false_mem, stages_no_False — **no `False`**: the twin
does not accept a file that declares a theorem of type `False` (in `jsonWithTheoremFalse`'s shape).
con-leche's parse of such chunks holds a theorem record of type `False`
(`parseChunks_jsonWithTheoremFalse`), the preparation keeps it (`mem_preparePrelude`), and the pure
fold never accepts it (`no_False_theorem_accepted_pure`). -/
theorem twinAccepts_no_False (V : Type w) [SetTheory V] {chunks : List ByteArray}
    (hfalse : jsonWithTheoremFalse chunks) (h : TwinAccepts chunks) : False := by
  obtain ⟨pins, preC, rc, F, env, hrc, hpure⟩ := twinAccepts_pure h
  obtain ⟨cv, vl, hty, hmem⟩ := ConLeche.Frontend.parseChunks_jsonWithTheoremFalse hfalse hrc
  exact no_False_theorem_accepted_pure V rfl
    (by simpa using ConLeche.Frontend.mem_preparePrelude (pre := preC) hmem) hty hpure

end ConAgua.Final
