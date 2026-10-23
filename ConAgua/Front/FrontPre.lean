import ConAgua.Front.FrontRun
import ConAgua.Front.ChunkBridge
import ConAgua.Front.DeclsPre

/-!
# The frontend after the prelude: records already in `DECL` (lane `pipeline`)

The checker parses the stream with the prelude's records still in `DECL[0‥P)`
(`Checker/Prelude.lean`): `front_run` starts from a memory related to the blank parse state
prefixed by them (`StateD.blank.pre D`, `Front/DeclsPre.lean`). The twin's parse only pushes to
`decls` (`applyLine_pre`), so the frontend's own refinement carries over: the memory after is
related to the twin's final parse state prefixed by `D` (`frontAll_refines_pre`,
`frontAll_refines_chunks_pre`).
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open ConLeche.Frontend hiding StateD RecordVerdict applyLine parseBytes ParseResultD parseChunks
open ConRon.Arena ConRon.Arena.Frontend

namespace L.Front

section pre
variable (D : Array IDeclaration)

theorem applyLine_pre_ok {st : StateD} {r : LineRec} {a : AState} :
    AM.ok (applyLine (st.pre D) r) a ↔ AM.ok (applyLine st r) a := by
  simp only [AM.ok, applyLine_pre_run]
  cases (applyLine st r).run a <;> rfl

theorem applyLine_pre_st {st : StateD} {r : LineRec} {a : AState} :
    AM.st (applyLine (st.pre D) r) a = AM.st (applyLine st r) a := by
  simp only [AM.st, applyLine_pre_run]
  cases (applyLine st r).run a <;> rfl

theorem applyLine_pre_res {st : StateD} {r : LineRec} {a : AState} (h : AM.ok (applyLine st r) a) :
    AM.res (applyLine (st.pre D) r) a = preL D (AM.res (applyLine st r) a) := by
  simp only [AM.res, AM.ok, applyLine_pre_run] at h ⊢
  revert h
  cases (applyLine st r).run a with
  | error e => simp
  | ok v => intro _; rfl

/-- The driver's invariant after the prelude: as `FrontInv`, the memory related to the twin's
parse state prefixed by `D`, con-ron's bridge invariant of the twin's own. -/
def FrontInvP (b : ByteArray) (m : Mem) (a : AState) (st : StateD) : Prop :=
  m.arr8 IN = b.data ∧ ArenaD m a ∧ StateDR m (st.pre D) ∧ TwinOK a st

section refine
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem lineKW_step_pre (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (i : USize) (ok nx : Word) (st : StateD)
    (a : AState) (hI : FrontInvP D b m a st) (_hi : i < b.usize)
    (h : lineKW p b.data m i.toUInt64 = some (ok, nx, m'))
    (hok : ok ≠ 0) : LineStepI (FrontInvP D b) b i nx st a m' := by
  unfold lineKW at h
  split at h
  · cases h
  rename_i r m₁ hW
  split at h
  · rename_i hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rcases frontLineW_shape _ _ _ _ _ _ hW with hr | hr
    · rw [hr] at hok; exact absurd rfl hok
    rw [hr] at hW
    obtain ⟨r', q, st', h1, h2, h3, h4, h5, h6⟩ :=
      frontLineW_refines b h64 hsize p hFI hAI hII hXI m m₁ hI.1 i a (st.pre D) hI.2.1 hI.2.2.1
        hI.2.2.2.1 _ hW
    have h3' := (applyLine_pre_ok D).mp h3
    rw [applyLine_pre_res D h3'] at h4
    rw [applyLine_pre_st D] at h5
    cases hres : AM.res (applyLine st r') a with
    | inr v => rw [hres] at h4; cases h4
    | inl st₀ =>
      rw [hres] at h4
      simp only [preL, Sum.map_inl, Sum.inl.injEq] at h4
      subst h4
      exact ⟨r', q, st₀, h1, h2, h3', hres, ⟨hk.trans hI.1, h5, h6, hI.2.2.2.line h3' hres⟩⟩
  · cases h

end refine

section init
variable (m m' : Mem) (a : AState) (hR : ArenaD m a) (hD : StateDR m (StateD.blank.pre D))

include hR hD in
theorem frontInitW_refines_pre (h : frontInitW m = some m') :
    AM.ok ConRon.Arena.Frontend.StateD.init a ∧ ArenaD m' (AM.st ConRon.Arena.Frontend.StateD.init a) ∧
      StateDR m' ((AM.res ConRon.Arena.Frontend.StateD.init a).pre D) := by
  simp only [frontInitW] at h
  cases h1 : putK NID 0 (nainternW m) with
  | none => rw [h1] at h; simp [initK] at h
  | some m₂ =>
    rw [h1, initK_some] at h
    obtain ⟨w₁, m₁, hI1, hw1, hp1⟩ := putK_eq h1
    obtain ⟨w₂, m₃, hI2, hw2, hp2⟩ := putK_eq h
    obtain ⟨ok1, R1, res1, hf1⟩ := nanon_A m a hR w₁ m₁ hI1
    have R2 := ArenaD.putT _ _ _ R1 NID (.inl rfl) 0 w₁ hp1
    obtain ⟨ok2, R3, res2, hf2⟩ := zero_A _ _ R2 w₂ m₃ hI2
    have hX : ConRon.Arena.Frontend.StateD.init = (internNNode .anonymous >>= fun n0 => internLNode .zero >>= fun l0 =>
        pure ({ names := IdTable.singleton n0, levels := IdTable.singleton l0 } : StateD)) := rfl
    let n0 := AM.res (internNNode .anonymous) a
    obtain ⟨okI, stI, resI⟩ := AM.bind_pure (internLNode .zero)
      (fun l0 => ({ names := IdTable.singleton n0, levels := IdTable.singleton l0 } : StateD))
      (AM.st (internNNode .anonymous) a) ok2
    have okX : AM.ok ConRon.Arena.Frontend.StateD.init a := by rw [hX, AM.ok_bind]; exact ⟨ok1, okI⟩
    have D1 : StateDR m₂
        { names := IdTable.singleton (decI w₁), levels := {}, decls := D } :=
      hD.putName hf1 (by tapart) (by tapart) 0 w₁ hp1 hw1 _
        (fun j => by simp [IdTable.get?_singleton, StateD.blank, StateD.pre, IdTable.get?_empty])
        rfl (by simp [StateD.blank, StateD.pre])
    refine ⟨okX, ?_, ?_⟩
    · rw [hX] at okX ⊢
      rw [AM.st_bind _ _ _ okX, stI]
      exact ArenaD.putT _ _ _ R3 LID (.inr (.inl rfl)) _ _ hp2
    · rw [hX, AM.res_bind _ _ _ ok1, resI, res2]
      simp only [n0, res1]
      exact D1.putLevel hf2 (by tapart) (by tapart) 0 w₂ hp2 hw2 _
        (fun j => by simp [IdTable.get?_singleton, IdTable.get?_empty]) rfl
        (by simp [StateD.pre])

end init

section refine2
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- **The driver's model refines `parseBytes`, after the prelude.** -/
theorem frontRunW_refines_pre (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (a₀ : AState) (hm : m.arr8 IN = b.data)
    (hA : ArenaD m a₀) (hD : StateDR m (StateD.blank.pre D)) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀)
    (h : runI (lineKW p b.data) b.size (initKW m) = some (0, m')) :
    ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧ FrontInvP D b m' a' st' := by
  refine runI_refines (FrontInvP D b) b h64 hsize (lineKW p b.data)
    (lineKW_step_pre D b h64 hsize p hFI hAI hII hXI)
    (fun m a => m.arr8 IN = b.data ∧ ArenaD m a ∧ StateDR m (StateD.blank.pre D) ∧
      ConRon.Bridge.StateOK a ∧ a.store.scratchOn = false ∧ ConRon.Bridge.PinsOK a) initKW ?_ m m' a₀
    ⟨hm, hA, hD, hok, hoff, hpins⟩ h
  intro m m₁ a ⟨hm, hA, hD, hok, hoff, hpins⟩ hi
  unfold initKW at hi
  split at hi
  · cases hi
  rename_i m₂ hW
  split at hi
  · rename_i hk
    cases hi
    obtain ⟨h1, h2, h3⟩ := frontInitW_refines_pre D m m₁ a hA hD hW
    have hr := AM.run_of_ok _ _ h1
    exact ⟨AM.res ConRon.Arena.Frontend.StateD.init a, AM.st ConRon.Arena.Frontend.StateD.init a, hr, hk.trans hm, h2, h3,
      TwinOK.init hok hoff hpins hr⟩
  · cases hi

end refine2

/-- **Bytes → stores after the prelude, for the frontend's program**: `frontAll_refines` from a
memory whose `DECL` already holds the records `D` (and empty id tables). -/
theorem frontAll_refines_pre (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data)
    (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem (StateD.blank.pre D)) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀) :
    ⦃fun s => s = s₀⦄
    invoke frontAllProg (exec frontAllProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem (st'.pre D) ∧ TwinOK a' st'; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun h0
  have hW := M.of_run (P := fun s => s = s₀) hs hrun
    (frontRun_spec frontAllProg (lineKW frontAllProg b.data) b.data _
      (fun n s₀ i hm hz hi => frontLineK_spec frontAllProg frontAllProg_scan frontAllProg_front rfl
        rfl rfl rfl rfl rfl rfl frontAllProg_expr rfl frontAllProg_dfields frontAllProg_decl rfl
        b.data hsize _ hpool n s₀ i hm hz hi)
      initKW (fun n s₀ _ _ => frontInitK_spec frontAllProg frontAllProg_front frontAllProg_expr rfl
        n s₀) rfl n s₀ hm rfl)
  rw [h0] at hW
  obtain ⟨st', a', h1, -, h2, h3, h4⟩ :=
    frontRunW_refines_pre D b h64 hsize frontAllProg frontAllProg_indFields frontAllProg_indApply
      frontAllProg_indInstall frontAllProg_indLine s₀.mem s'.mem a₀ hm hA hD hok hoff hpins hW
  exact ⟨st', a', h1, h2, h3, h4⟩

/-- **The streaming form** (`parseChunks [b]`), after the prelude. -/
theorem frontAll_refines_chunks_pre (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data)
    (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem (StateD.blank.pre D)) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀) :
    ⦃fun s => s = s₀⦄
    invoke frontAllProg (exec frontAllProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseChunks [b]).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem (st'.pre D) ∧ TwinOK a' st'; ⊤⦄ := by
  have hu : b.size < USize.size := by
    rw [show USize.size = 2 ^ 64 by simp [USize.size, h64]]; omega
  rw [ConAgua.Front.ChunkBridge.parseChunks_single b hu]
  exact frontAll_refines_pre D b h64 hsize n s₀ hm hpool a₀ hA hD hok hoff hpins

end pre

end L.Front
