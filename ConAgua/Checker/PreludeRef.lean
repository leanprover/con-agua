module

import ConAgua.Verdict.FrontPreSimE
import ConAgua.Verdict.FrontSafeE
import ConAgua.Front.FrontRunRef
import ConAgua.Checker.FrontReset
import ConAgua.Checker.PrepProgHoist
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.Verdict
public import ConAgua.Checker.NoVerdictFns
public import ConAgua.Checker.PipePrelude
import all ConAgua.Checker.Prelude

@[expose] public section

/-!
# The prelude, both outcomes: `builtin_prelude`

One unified model and one refinement (`docs/design/unifiede.md`). `builtin_prelude()` is
`pre_front_run()` (the frontend on the prelude's bytes), then `CTL[240] := DECL[0]`, then
`front_reset()` (lifted). `pre_front_run` is read through its run: both of its halves are
`front_run`'s on the prelude's bytes (`preSim_triple`, `preFrontRun_errSim`), whose refinement is
`frontRun_ref` (`frontRunOK_checker`, `frontRun_errClaim`). So `builtinPrelude_ref` is a `RefC`:
an ok run ends in `BP3` (the twin's `builtinPreludeE` accepted, the records in `DECL`, the id
tables empty), a failure of class `≠ 0` claims that `builtinPreludeE` fails with that class. Its
`G` is `True`: the closure and `SafeLink preludeText` are theorems at `checkerProg`.
-/

open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend

/-- **`builtin_prelude`'s unified model**: `pre_front_run` through its run, `front_reset` (outside
the verdict closure) lifted. -/
l_model builtinPrelude_specE (p : Prog) (hf : p.lookup "builtin_prelude" = some builtinPreludeL)
  fns [hf ↦ builtinPreludeLE]
  specs [callW_spec p n "front_reset"]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE] unified nv [closedNV p nvFns = true, nv_mem]

/-- A failing call is a failing run from the call's start. -/
theorem run_of_callE_err {p : Prog} {k : Nat} {f : FnName} {vs : List Word} {m : Mem} {e : Err}
    (h : callE p k f vs m = .error e) :
    (invoke p (exec p k) f vs).run ⟨m, Locals.init []⟩ = .error e := by
  unfold callE at h
  cases hr : (invoke p (exec p k) f vs).run ⟨m, Locals.init []⟩ with
  | error e' => rw [hr] at h; cases h; rfl
  | ok v => rw [hr] at h; cases h

/-- The prelude's parse failing is the prelude failing. -/
theorem builtinPreludeE_fails {a : AState} {c : L.Word}
    (h : TwinFailsV (parseBytes preludeText) a c) : TwinFailsV builtinPreludeE a c := by
  rcases h with ⟨ce, hce, hc⟩ | ⟨ce, i, a', hce, hc⟩
  · refine .inl ⟨ce, ?_, hc⟩
    show (do let x ← (parseBytes preludeText).run a; _) = _
    rw [hce]; rfl
  · refine .inr ⟨ce, i, a', ?_, hc⟩
    show (do let x ← (parseBytes preludeText).run a; _) = _
    rw [hce]; rfl

set_option maxRecDepth 100000 in
/-- **`builtin_prelude` refines `builtinPreludeE`, both outcomes**: from `BP0`, an ok run ends in
`BP3`; a failure of class `≠ 0` is `pre_front_run`'s, which is `front_run`'s on the prelude's
bytes, whose claim is the prelude's parse failing. -/
theorem builtinPrelude_ref (h64 : System.Platform.numBits = 64) (a : AState) (n : Nat) {m : Mem}
    (h0 : BP0 a m) :
    RefC True (builtinPreludeLE checkerProg n m) (fun x => BP3 a x.2)
      (ErrClaimV builtinPreludeE a) := by
  obtain ⟨hA, hD, ht, hctl, hmo⟩ := h0
  have hin : (m.setIn preIn).arr8 IN = preludeText.data := by rw [Mem.arr8_setIn_zero, preIn_eq]
  have h₀ : (m.setIn preIn).arr8 IN = preludeText.data ∧ ArenaD (m.setIn preIn) a ∧
      StateDR (m.setIn preIn) (StateD.blank.pre #[]) ∧ ConRon.Bridge.StateOK a ∧
      a.store.scratchOn = false ∧ ConRon.Bridge.PinsOK a ∧
      (∀ x < (#[] : Array IDeclaration).size,
        L.Checker.RecOK ((m.setIn preIn).arr64 DECL) ((m.setIn preIn).arr64 DLP) x) ∧
      ModeOK (m.setIn preIn) :=
    ⟨hin, L.Arena.ArenaD.frameHi (setIn_frame _ _) (by simp) (by simp) hA,
      by rw [blank_pre_nil]; exact hD.frame (setIn_frame _ _) (by simp) (by simp),
      ht.ok, ht.off, ht.pins, fun x hx => absurd hx (by simp),
      ModeOK.frame hmo (setIn_frame _ _) (by simp) (by simp)⟩
  cases n with
  | zero => exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n =>
  simp only [builtinPreludeLE]
  rcases h1 : callE checkerProg n "pre_front_run" [] m with e1 | ⟨r1, m1⟩
  · -- `pre_front_run` fails as `front_run` on the prelude's bytes
    rw [builtinPreludeLE.k_pre_front_run.none]
    intro _ hk
    have hsim := preFrontRun_errSim n ⟨m, Locals.init []⟩ e1 (run_of_callE_err h1)
      hk
    have hc := L.Front.callE_of_run_err hsim
    simp only [St.setIn_mem] at hc
    exact builtinPreludeE_fails (frontRun_errClaim #[] preludeText h64 preludeText_size
      (safeLink h64 _ preludeText_size) n (m.setIn preIn) a h₀ hc hk)
  -- an ok run of `pre_front_run` is `front_run`'s on the prelude's bytes
  obtain ⟨s1, hs1, hpost, -⟩ := triple_of_callE (preSim_triple checkerProg_preSim n "front_run"
    isCopied_front_run [] ⟨m, Locals.init []⟩ (frontRunOK_checker #[] preludeText h64
      preludeText_size n _ h₀.1 a h₀.2.1 h₀.2.2.1 ht.ok ht.off ht.pins h₀.2.2.2.2.2.2.1
      h₀.2.2.2.2.2.2.2)) h1
  obtain ⟨sk, hsk, -, hkp, -⟩ := triple_of_callE (Triple.keep checkerProg_noSt8
    (M.triple_of_run (P := fun s => s = ⟨m, Locals.init []⟩) (Q := fun _ _ => True)
      fun _ _ _ _ _ => trivial)) h1
  have hctl1 : 240 < (m1.arr64 CTL).size := by rw [← hsk, hkp.size]; exact hctl
  by_cases hr : r1.headD 0 = 0
  rotate_left
  · simp only [builtinPreludeLE.k_pre_front_run, ite_eq_left hr]
    exact fun _ hk => absurd (by decide) hk
  rw [builtinPreludeLE.k_pre_front_run.arm1 _ _ _ _ hr]
  obtain ⟨st, a', hp, hA', hD', -, hM', hR⟩ := hpost hr
  rw [pre_nil] at hD'
  have hb := builtinPreludeE_of hp
  simp only [St.setIn_mem, hs1] at hA' hD' hM' hR
  have hA1 := L.Arena.ArenaD.frameHi (setIn_frame' m1 preIn) (by simp) (by simp) hA'
  have hD1 := hD'.frame (setIn_frame' m1 preIn) (by simp) (by simp)
  have hM1 := ModeOK.frame hM' (setIn_frame' m1 preIn) (by simp) (by simp)
  have hR1 : RecsOK m1 st.decls := fun x hx => hR x (by simpa using hx)
  -- `CTL[240] := DECL[0]`
  have hf := MemFrame.setCtl m1 240 (rdW (m1.arr64 L.Front.DECL) 0)
  generalize hm2 : m1.set64 CTL 240 (rdW (m1.arr64 L.Front.DECL) 0) = m2 at hf
  have hD2 := hD1.frame hf (by simp) (by simp)
  have h240 : (rdW (m2.arr64 CTL) 240).toNat = st.decls.size := by
    rw [← hm2, rdW_set64, ite_eq_left ⟨rfl, rfl, hctl1⟩]
    have := hD1.decls.count
    simpa [rdW] using this
  -- `front_reset`
  rcases h3 : callW checkerProg n "front_reset" [] m2 with _ | ⟨r3, m3⟩
  · rw [liftE_none, builtinPreludeLE.k_front_reset.none]; exact fun _ hk => absurd (by simp) hk
  rw [liftE_some, builtinPreludeLE.k_front_reset.arm1]
  obtain ⟨s3, rfl, -, hok, hm3⟩ :=
    triple_of_callW (frontReset_spec checkerProg checkerProg_prepProg n ⟨m2, Locals.init []⟩) h3
  have hf3 := resetM_frame m2
  dsimp only at hm3 hok ⊢
  rw [hm3]
  refine ⟨st, a', hb, L.Arena.ArenaD.frameHi hf3 (by simp) ?_ (L.Arena.ArenaD.frameHi hf (by simp) (by simp) hA1),
    frontReset_stateDR hD2 hok, ht.prelude hb, ?_,
    (hR1.frame hf (by simp) (by simp)).frame hf3 (by simp) (by simp),
    ModeOK.frame (ModeOK.frame hM1 hf (by decide) (by decide)) hf3 (by decide) (by decide)⟩
  · intro x hx; simp only [idCtl, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hf3.ctl 240 (by decide)]; exact h240

/-- **`builtin_prelude` refines `builtinPreludeE`**, on the parse state and the arena
(`builtinPrelude_ref`'s ok half). -/
@[refines ConRon.Arena.Frontend.builtinPreludeE]
theorem builtinPrelude_checker (h64 : System.Platform.numBits = 64) (a : AState) :
    StageSpec checkerProg "builtin_prelude" (BP0 a) fun _ => BP3 a := by
  intro n _hn s₀
  refine M.triple_of_run fun s r s' hs hr => ?_
  obtain ⟨hl, hx⟩ := M.of_run' (P := fun s => s = s₀) hs hr
    (builtinPrelude_specE checkerProg checkerProg_builtin n s₀)
  refine ⟨hl, fun h0 => ?_⟩
  have h := builtinPrelude_ref h64 a n h0
  rw [hx] at h
  exact h

end L.Checker
