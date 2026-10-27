import ConAgua.Verdict.FrontValidE
import ConAgua.Verdict.FrontSafeE
import ConAgua.Verdict.FrontPreSimE
import ConAgua.Checker.VerdictEntry1
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# The frontend's two stages' error specs: `builtin_prelude`, `front_run` (lane `verdicts-b`,
helper `f2`)

`Entry1StagesE.prelude` and `.front` (`Checker/VerdictEntry1.lean`), from the frontend's error
claim at `frontAllProg` (`frontRunE_claim`, `FrontRunE.lean`): `front_run` runs in `checkerProg`
as in `frontAllProg` (`callE_frontAll`); `builtin_prelude` fails only where `pre_front_run` does,
which fails as `front_run` on the prelude's bytes (`preFrontRun_errSim`).
-/

open ConRon.Arena
open ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order
open L.Arena L.Front ConAgua.Final

set_option experimental.vcgen true

namespace L.Checker

l_model builtinPrelude_specE (p : Prog) (hf : p.lookup "builtin_prelude" = some builtinPreludeL)
  fns [hf ↦ builtinPreludeLE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] errors

/-- The extra twin facts `X` the frontend's error claim takes hold of every state `front_run`
reaches (`TwinOK`), at any prefix of records. -/
def XOfTwin (X : StateD → AState → Prop) : Prop :=
  ∀ (D : Array IDeclaration) (a : AState) (st : StateD), TwinOK a st → X (st.pre D) a

/-- **`front_run`'s error spec at the checker's stage relation** (`Entry1StagesE.front`'s
statement), from `validate_ind_d`'s claim (`ValidateClaim`), the twin facts it takes (`XOfTwin`),
and the scanner's `safety` converse (`SafeLink`). -/
theorem frontStageE {X : StateD → AState → Prop} (hV : L.Front.Ind.ValidateClaim frontAllProg X)
    (hXT : XOfTwin X)
    (hSL : System.Platform.numBits = 64 → ∀ b : ByteArray, b.size < 2 ^ 63 → SafeLink b) :
    ∀ b pb s8 s64, InputsOK b pb s64 →
      StageSpecE checkerProg "front_run" [] (Q4 b (checkerRels b pb s8 s64)) (TwinVerdict [b]) := by
  intro b pb s8 s64 hin n _hn s₀
  refine M.triple_of_run' (fun _ _ _ _ _ => trivial) fun s e hs hr hQ hk => ?_
  subst hs
  obtain ⟨sA, pre, sB, hA, hB, h4⟩ := hQ
  have h4 : R4 (loadMem b pb s8 s64) s.mem pb pre sB := h4
  have hm : s.mem.arr8 IN = b.data := by rw [h4.since.keep.arr8]; exact loadMem_in b pb s8 s64
  have hc := callE_of_run_err hr
  rw [← callE_frontAll (by decide) n [] s.mem] at hc
  have hE := triple_of_callE_err (frontRun_specE frontAllProg rfl n ⟨s.mem, Locals.init []⟩) hc
    (Err.code_ne_of_cls hk)
  have hf := frontRunE_claim pre.decls b hin.1 hin.2.1 hV (hXT pre.decls) (hSL hin.1 b hin.2.1) n s.mem sB hm
    h4.arena h4.sdr h4.twin.ok h4.twin.off h4.twin.pins h4.rok h4.mode e hE hk
  have hu : b.size < USize.size := by
    rw [show USize.size = 2 ^ 64 by simp [USize.size, hin.1]]; have := hin.2.1; omega
  refine TwinVerdict.front hA hB ?_
  rw [ConAgua.Front.ChunkBridge.parseChunks_single b hu]
  exact hf

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

/-- **`builtin_prelude`'s error spec at the checker's stage relation** (`Entry1StagesE.prelude`'s
statement): it fails (class `≠ 0`) only where `pre_front_run` does, which fails as `front_run` on
the prelude's bytes (`preFrontRun_errSim`), so the twin's `parseBytes preludeText` fails. -/
theorem preludeStageE {X : StateD → AState → Prop} (hV : L.Front.Ind.ValidateClaim frontAllProg X)
    (hXT : XOfTwin X)
    (hSL : System.Platform.numBits = 64 → ∀ b : ByteArray, b.size < 2 ^ 63 → SafeLink b) :
    ∀ b pb s8 s64, InputsOK b pb s64 →
      StageSpecE checkerProg "builtin_prelude" [] (Q3 b (checkerRels b pb s8 s64)) (TwinVerdict [b]) := by
  intro b pb s8 s64 hin n _hn s₀
  refine M.triple_of_run' (fun _ _ _ _ _ => trivial) fun s e hs hr hQ hk => ?_
  subst hs
  obtain ⟨sA, hA, h3⟩ := hQ
  have h3 : R3 (loadMem b pb s8 s64) s.mem pb sA := h3
  have hcap := CapsOK.keep h3.since.keep h3.since.caps
  have h0 : 0 < s.mem.bytes.size := bytes_pos h3.since (loadMem_bytes b pb s8 s64)
  have hpool : (s.mem.arr64 POOL).size < 2 ^ 63 := by have := hcap.pool; omega
  have hc := callE_of_run_err hr
  have hE := triple_of_callE_err (builtinPrelude_specE checkerProg checkerProg_builtin n
    ⟨s.mem, Locals.init []⟩) hc (Err.code_ne_of_cls hk)
  refine TwinVerdict.prelude hA (builtinPreludeE_fails ?_)
  cases n with
  | zero => simp only [builtinPreludeLE] at hE; cases hE; exact absurd rfl hk
  | succ n =>
  rw [builtinPreludeLE.arm1] at hE
  cases h1 : callE checkerProg n "pre_front_run" [] s.mem with
  | ok q1 =>
    obtain ⟨r1, m₁⟩ := q1
    rw [h1] at hE
    simp only [builtinPreludeLE.k_pre_front_run] at hE
    split at hE
    · cases hE; exact absurd (by decide) hk
    · cases h2 : callE checkerProg n "front_reset" [] (m₁.set64 CTL 240 (rdW (m₁.arr64 L.Front.DECL) 0)) with
      | error e2 =>
        rw [h2] at hE; simp only [builtinPreludeLE.k_front_reset] at hE; cases hE
        exact absurd (callE_nv checkerProg_nv (by decide +kernel) _ _ _ h2) hk
      | ok q2 => rw [h2] at hE; simp only [builtinPreludeLE.k_front_reset] at hE; cases hE
  | error e1 =>
  rw [h1] at hE
  simp only [builtinPreludeLE.k_pre_front_run] at hE
  cases hE
  have hrun := run_of_callE_err h1
  have hsim := preFrontRun_errSim n ⟨s.mem, Locals.init []⟩ e h0 hrun (Err.code_ne_of_cls hk)
  have hc' := callE_of_run_err hsim
  simp only [St.setIn_mem] at hc'
  rw [← callE_frontAll (by decide) n [] _] at hc'
  have hE' := triple_of_callE_err (frontRun_specE frontAllProg rfl n ⟨_, Locals.init []⟩) hc'
    (Err.code_ne_of_cls hk)
  have hD0 : StateDR (s.mem.setIn preIn) (StateD.blank.pre #[]) := by
    rw [blank_pre_empty]; exact h3.sdr.frame (setIn_frame _ _) (by simp) (by simp)
  exact frontRunE_claim #[] preludeText hin.1 preludeText_size hV (hXT #[]) (hSL hin.1 _ preludeText_size) n
    (s.mem.setIn preIn) sA (by rw [setIn_arr8_zero _ _ h0, preIn_eq])
    (L.Rom.ArenaD.frameHi (setIn_frame _ _) (by simp) (by simp) h3.arena) hD0 h3.twin.ok h3.twin.off
    h3.twin.pins (fun x hx => absurd hx (by simp))
    (ModeOK.frame h3.mode (setIn_frame _ _) (by simp) (by simp)) e hE' hk

/-! ## The two stages, discharged -/

/-- **`Entry1StagesE.prelude`'s statement.** -/
theorem checker_preludeStageE : ∀ b pb s8 s64, InputsOK b pb s64 →
    StageSpecE checkerProg "builtin_prelude" [] (Q3 b (checkerRels b pb s8 s64)) (TwinVerdict [b]) :=
  preludeStageE L.Front.Ind.validateClaim_frontAll L.Front.Ind.xOfTwin
    (fun h64 b hs => L.Front.safeLink h64 b hs)

/-- **`Entry1StagesE.front`'s statement.** -/
theorem checker_frontStageE : ∀ b pb s8 s64, InputsOK b pb s64 →
    StageSpecE checkerProg "front_run" [] (Q4 b (checkerRels b pb s8 s64)) (TwinVerdict [b]) :=
  frontStageE L.Front.Ind.validateClaim_frontAll L.Front.Ind.xOfTwin
    (fun h64 b hs => L.Front.safeLink h64 b hs)

end L.Checker

