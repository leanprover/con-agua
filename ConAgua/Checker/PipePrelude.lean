module

public import ConAgua.Checker.PipeStages
public import ConAgua.Checker.HoistRefBase
public import ConAgua.Front.DeclsPre
import ConRon.Bridge.Frontend.Prepare
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Checker.PreludeSimProg
public import ConAgua.Checker.PreludeSim

@[expose] public section

/-!
# The stage `builtin_prelude` at `checkerProg` (lane `pipeline`)

`builtin_prelude()` is `pre_front_run()` (the frontend on the prelude's bytes, `preSim`), then
`CTL[240] := DECL[0]`, then `front_reset()`. Here: the memory predicates before and after it
(`BP0`, `BP3`; they hide the twin's states) and the facts its refinement (`builtinPrelude_ref`,
`PreludeRef.lean`) reads.
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-! ## The twin's prelude, from the frontend's -/

theorem builtinPreludeE_of {a a' : AState} {st : StateD}
    (h : (parseBytes preludeText).run a = .ok (.ok (.ofState st), a')) :
    builtinPreludeE a = .ok (.ok ⟨st.decls⟩, a') := by
  simp only [builtinPreludeE, bind, StateT.bind]
  change (do let x ← (parseBytes preludeText).run a; _) = _
  rw [h]; rfl

/-- The twin's facts after its prelude. -/
theorem TwinFacts.prelude {a a' : AState} {pre : PreludeIx} (h : TwinFacts a)
    (hr : builtinPreludeE a = .ok (.ok pre, a')) : TwinFacts a' := by
  obtain ⟨hstep, -, -, -⟩ := ConRon.Bridge.Frontend.builtinPreludeE_run h.ok h.off h.pins hr
  exact ⟨hstep.ok, by rw [hstep.scratch]; exact h.off, h.pins.mono hstep.ext hstep.pins,
    h.pers.mono hstep.pins, by simp only [PinsReadyP, hstep.pins]; exact h.ready⟩

/-! ## The memory predicates of the parts -/

/-- The records' word bounds (`prepare_prelude`'s hypotheses). -/
def RecsOK (m : Mem) (ds : Array IDeclaration) : Prop :=
  ∀ x < ds.size, RecOK (m.arr64 DECL) (m.arr64 DLP) x

theorem RecsOK.frame {A : List TieredArray} {C : List Word} {m m' : Mem} {ds : Array IDeclaration}
    (h : RecsOK m ds) (hf : MemFrame A C m m') (hD : (DECL : TieredArray) ∉ A) (hP : (DLP : TieredArray) ∉ A) : RecsOK m' ds := by
  rw [RecsOK, hf.arr _ hD (by decide), hf.arr _ hP (by decide)]; exact h

/-- Before: the arena and the blank parse state. -/
def BP0 (a : AState) (m : Mem) : Prop :=
  ArenaD m a ∧ StateDR m StateD.blank ∧ TwinFacts a ∧ 240 < (m.arr64 CTL).size ∧ ModeOK m

/-- After `front_reset`. -/
def BP3 (a : AState) (m : Mem) : Prop :=
  ∃ (st : StateD) (a' : AState), builtinPreludeE a = .ok (.ok ⟨st.decls⟩, a') ∧ ArenaD m a' ∧
    StateDR m (StateD.blank.pre st.decls) ∧ TwinFacts a' ∧ (rdW (m.arr64 CTL) 240).toNat = st.decls.size ∧
    RecsOK m st.decls ∧ ModeOK m

theorem setIn_frame (m : Mem) (x : Array UInt8) : MemFrame [] [] m (m.setIn x) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem setIn_frame' (m : Mem) (x : Array UInt8) : MemFrame [] [] (m.setIn x) m :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem preIn_eq : preIn = preludeText.data := by
  simp only [preIn, preludeBytes_eq, Array.toArray_toList]

set_option maxRecDepth 100000 in
theorem preludeBytes_len : preludeBytes.length < 2 ^ 63 := by decide +kernel

theorem preludeText_size : preludeText.size < 2 ^ 63 := by
  have h := preludeBytes_len
  rw [preludeBytes_eq] at h
  simpa using h

theorem isCopied_front_run : isCopied preTree "front_run" = true := by
  rw [← inT_preCT]; decide

set_option maxRecDepth 100000 in
theorem checkerProg_builtin : checkerProg.lookup "builtin_prelude" = some builtinPreludeL := rfl

end L.Checker
