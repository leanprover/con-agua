import ConAgua.Checker.PipeStages
import ConAgua.Checker.PrepProgChecker
import ConAgua.Checker.FrontReset
import ConAgua.Front.FrontPreOK
import ConRon.Bridge.Frontend.Prepare
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

/-!
# The stage `builtin_prelude` at `checkerProg` (lane `pipeline`)

`builtin_prelude()` is `pre_front_run()` (the frontend on the prelude's bytes, `preSim`), then
`CTL[240] := DECL[0]`, then `front_reset()`. `builtin_of_parts` composes the three as
implications between memory predicates (as `checkA_of_stages` does); the predicates hide the
twin's states.
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-- **`builtin_prelude` from its parts.** -/
theorem builtin_of_parts {p : Prog} (hp : p.lookup "builtin_prelude" = some builtinPreludeL)
    {P0 P1 P2 P3 : Mem → Prop}
    (h1 : StageSpec p "pre_front_run" P0 fun r m => r.headD 0 = 0 → P1 m)
    (h2 : ∀ m, P1 m → 240 < (m.arr64 CTL).size → P2 (m.set64 CTL 240 (rdW (m.arr64 L.Front.DECL) 0)))
    (h3 : StageSpec p "front_reset" P2 fun _ => P3) :
    StageSpec p "builtin_prelude" P0 fun _ => P3 := by
  intro n hn s₀
  rw [invoke_eq _ hp]
  simp only [callFn, builtinPreludeL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hn' : n ≤ 2 ^ 62 := by omega
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ld64, (h1 n hn' ·), (h3 n hn' ·)]
    all_goals grind [lang_grind, arena_grind]

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

theorem RecsOK.frame {A : List ArrId} {C : List Word} {m m' : Mem} {ds : Array IDeclaration}
    (h : RecsOK m ds) (hf : MemFrame A C m m') (hD : DECL ∉ A) (hP : DLP ∉ A) : RecsOK m' ds := by
  rw [RecsOK, hf.1 DECL hD (by decide), hf.1 DLP hP (by decide)]; exact h

/-- Before: the arena and the blank parse state. -/
def BP0 (a : AState) (m : Mem) : Prop :=
  ArenaD m a ∧ StateDR m StateD.blank ∧ TwinFacts a ∧ (m.arr64 POOL).size < 2 ^ 63 ∧
    0 < m.bytes.size ∧ ModeOK m

/-- After `pre_front_run`. -/
def BP1 (a : AState) (m : Mem) : Prop :=
  ∃ (st : StateD) (a' : AState), builtinPreludeE a = .ok (.ok ⟨st.decls⟩, a') ∧ ArenaD m a' ∧ StateDR m st ∧ TwinFacts a' ∧
    RecsOK m st.decls ∧ ModeOK m

/-- After `CTL[240] := DECL[0]`. -/
def BP2 (a : AState) (m : Mem) : Prop :=
  ∃ (st : StateD) (a' : AState), builtinPreludeE a = .ok (.ok ⟨st.decls⟩, a') ∧ ArenaD m a' ∧ StateDR m st ∧
    TwinFacts a' ∧ (rdW (m.arr64 CTL) 240).toNat = st.decls.size ∧ RecsOK m st.decls ∧ ModeOK m

/-- After `front_reset`. -/
def BP3 (a : AState) (m : Mem) : Prop :=
  ∃ (st : StateD) (a' : AState), builtinPreludeE a = .ok (.ok ⟨st.decls⟩, a') ∧ ArenaD m a' ∧
    StateDR m (StateD.blank.pre st.decls) ∧ TwinFacts a' ∧ (rdW (m.arr64 CTL) 240).toNat = st.decls.size ∧
    RecsOK m st.decls ∧ ModeOK m

theorem setIn_arr8_zero (m : Mem) (x : Array UInt8) (h : 0 < m.bytes.size) : (m.setIn x).arr8 0 = x := by
  simp [Mem.setIn, Mem.arr8, Array.getD_eq_getD_getElem?, h]

theorem setIn_frame (m : Mem) (x : Array UInt8) : MemFrame [] [] m (m.setIn x) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩

theorem setIn_frame' (m : Mem) (x : Array UInt8) : MemFrame [] [] (m.setIn x) m :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩

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

theorem blank_pre_empty : StateD.blank.pre #[] = StateD.blank := by
  simp [StateD.pre, StateD.blank]

theorem pre_empty (st : StateD) : st.pre #[] = st := by
  cases st; simp [StateD.pre]

theorem bp_h1 (h64 : System.Platform.numBits = 64) (a : AState) :
    StageSpec checkerProg "pre_front_run" (BP0 a) fun r m => r.headD 0 = 0 → BP1 a m := by
  intro n _hn s₀
  apply M.triple_of_run
  intro s r s' hs hrun
  refine ⟨hs ▸ (L.Front.invoke_loc hrun).1, fun ⟨hA, hD, ht, hpool, h0, hmo⟩ hr0 => ?_⟩
  subst hs
  have hQ := L.Front.frontRunOK_checker #[] preludeText h64 preludeText_size n (s.setIn preIn)
    (by show (s.mem.setIn preIn).arr8 0 = _; rw [setIn_arr8_zero _ _ h0, preIn_eq]) hpool a
    (ArenaD.frameHi (setIn_frame _ _) (by simp) (by simp) hA)
    (by rw [blank_pre_empty]; exact hD.frame (setIn_frame _ _) (by simp) (by simp)) ht.ok ht.off
    ht.pins (fun x hx => absurd hx (by simp)) (ModeOK.frame hmo (setIn_frame _ _) (by simp) (by simp))
  obtain ⟨hpost, -⟩ := M.of_run (P := fun x => x = s) rfl hrun
    (preSim_triple checkerProg_preSim n "front_run" isCopied_front_run [] s h0 hQ)
  obtain ⟨st, a', hp, hA', hD', -, hM', hR⟩ := hpost hr0
  rw [pre_empty] at hD'
  have hb := builtinPreludeE_of hp
  exact ⟨st, a', hb, ArenaD.frameHi (setIn_frame' _ _) (by simp) (by simp) hA',
    hD'.frame (setIn_frame' _ _) (by simp) (by simp), ht.prelude hb,
    fun x hx => hR x (by simpa using hx), ModeOK.frame hM' (setIn_frame' _ _) (by simp) (by simp)⟩

theorem bp_h2 (a : AState) : ∀ m, BP1 a m → 240 < (m.arr64 CTL).size →
    BP2 a (m.set64 CTL 240 (rdW (m.arr64 L.Front.DECL) 0)) := by
  intro m ⟨st, a', hb, hA, hD, ht, hok, hmo⟩ hc
  have hf := MemFrame.setCtl m 240 (rdW (m.arr64 L.Front.DECL) 0)
  refine ⟨st, a', hb, ArenaD.frameHi hf (by simp) (by simp) hA, hD.frame hf (by simp) (by simp),
    ht, ?_, hok.frame hf (by simp) (by simp), ModeOK.frame hmo hf (by decide) (by decide)⟩
  rw [rdW_set64, ite_eq_left ⟨rfl, rfl, hc⟩]
  have := hD.decls.count
  simpa [rdW] using this

theorem bp_h3 (a : AState) : StageSpec checkerProg "front_reset" (BP2 a) fun _ => BP3 a := by
  intro n _hn s₀
  refine triple_post (frontReset_spec checkerProg checkerProg_prepProg n s₀)
    fun _ s' ⟨hl, hok, hm⟩ => ⟨hl, fun ⟨st, a', hb, hA, hD, ht, h240, hrk, hmo⟩ => ?_⟩
  have hf := resetM_frame s₀.mem
  rw [hm]
  refine ⟨st, a', hb, ArenaD.frameHi hf (by simp) ?_ hA, frontReset_stateDR hD hok, ht, ?_,
    hrk.frame hf (by simp) (by simp), ModeOK.frame hmo hf (by decide) (by decide)⟩
  · intro x hx; simp only [idCtl, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hf.2.1 240 (by decide)]; exact h240

/-- **`builtin_prelude` refines `builtinPreludeE`**, on the parse state and the arena. -/
@[refines ConRon.Arena.Frontend.builtinPreludeE]
theorem builtinPrelude_checker (h64 : System.Platform.numBits = 64) (a : AState) :
    StageSpec checkerProg "builtin_prelude" (BP0 a) fun _ => BP3 a :=
  builtin_of_parts checkerProg_builtin (bp_h1 h64 a) (bp_h2 a) (bp_h3 a)

end L.Checker
