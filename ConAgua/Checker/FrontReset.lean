import ConAgua.Checker.Prelude
import ConAgua.Front.DeclsPre
import ConAgua.Front.StateDR
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic

/-!
# `front_reset()`: the id tables emptied (lane `pipeline`)

`builtin_prelude` ends with `front_reset`: the three id tables' dense sizes `CTL[70‥72] := 0` and
their sparse maps cleared (`memoClearG (spS b)`). The declaration records stay. From the parse
state relation at the prelude's final state `st`, it gives the relation at the blank state with
the prelude's records (`StateD.blank.pre st.decls`, `frontReset_stateDR`), which is where the
stream's `front_run` starts (`Front/FrontPre.lean`).
-/

namespace L.Checker

open L L.Arena L.Front
open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-- The dense sizes zeroed. -/
def resetM0 (m : Mem) : Mem := ((m.set64 CTL 70 0).set64 CTL 71 0).set64 CTL 72 0

/-- After the first clear. -/
def resetM1 (m : Mem) : Mem := mclearG (spS NID) (resetM0 m)
/-- After the second clear. -/
def resetM2 (m : Mem) : Mem := mclearG (spS LID) (resetM1 m)
/-- **The memory after `front_reset()`**. -/
def resetM (m : Mem) : Mem := mclearG (spS EID) (resetM2 m)

/-- What `front_reset` checks: the three stamps can be bumped. -/
def ResetOK (m : Mem) : Prop :=
  rdW ((resetM0 m).arr64 CTL) (spS NID).cs + 2 ≠ 0 ∧ rdW ((resetM1 m).arr64 CTL) (spS LID).cs + 2 ≠ 0 ∧
    rdW ((resetM2 m).arr64 CTL) (spS EID).cs + 2 ≠ 0

theorem frontReset_spec (p : Prog) (hp : PrepProg p) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "front_reset" []
    ⦃fun _ s' => LocEq s' s₀ ∧ ResetOK s₀.mem ∧ s'.mem = resetM s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "front_reset")]
  simp only [callFn, frontResetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64,
        memoClearG_spec (spS NID) p "nid_sp_clear" (hp.get "nid_sp_clear") n,
        memoClearG_spec (spS LID) p "lid_sp_clear" (hp.get "lid_sp_clear") n,
        memoClearG_spec (spS EID) p "eid_sp_clear" (hp.get "eid_sp_clear") n] <;>
      finish [ResetOK, resetM, resetM2, resetM1, resetM0]

/-! ## The parse state after -/

theorem resetM0_frame (m : Mem) : MemFrame [] idCtl m (resetM0 m) :=
  (((MemFrame.setCtl m 70 0).mono (by simp) (by simp [idCtl])).trans
    ((MemFrame.setCtl _ 71 0).mono (by simp) (by simp [idCtl]))).trans
    ((MemFrame.setCtl _ 72 0).mono (by simp) (by simp [idCtl]))

theorem clear_frame (b : ArrId) (hb : TblIx b) (m : Mem) : MemFrame [] idCtl m (mclearG (spS b) m) :=
  (mclearG_frame (spS b) m).mono (by simp) (by
    rcases hb with rfl | rfl | rfl <;> simp [spS, idCtl] <;> decide)

theorem resetM_frame (m : Mem) : MemFrame [] idCtl m (resetM m) :=
  (((resetM0_frame m).trans (clear_frame NID (.inl rfl) _)).trans
    (clear_frame LID (.inr (.inl rfl)) _)).trans (clear_frame EID (.inr (.inr rfl)) _)

/-- A memo of table `b` survives a frame that leaves its stamp word alone. -/
theorem tblMemo_frame {k : IdxKind} {b : ArrId} (hb : TblIx b) {C : List Word} {m m' : Mem}
    (hf : MemFrame [] C m m') (hC : (spS b).cs ∉ C) {sp : Std.HashMap Nat (Idx k)}
    (h : MemoRV (spS b) idKey hVR m sp) : MemoRV (spS b) idKey hVR m' sp :=
  memoRV_frame (spS b) (spS_wf b hb) idKey hVR [] C (by simp) hC m m' hf (fun _ _ h => h) sp h

/-- The dense size after the reset. -/
theorem resetM_szW (m : Mem) (b : ArrId) (hb : TblIx b) (hc : (szC b).toNat < (m.arr64 CTL).size) :
    szW (resetM m) b = 0 := by
  rcases hb with rfl | rfl | rfl <;>
  simp [resetM, resetM2, resetM1, resetM0, mclearG, szW, szC, spS, rdW_set64, size_set64, NID, LID,
    EID] at hc ⊢ <;> omega

theorem resetM0_frame' (m : Mem) : MemFrame [] [70, 71, 72] m (resetM0 m) :=
  (((MemFrame.setCtl m 70 0).mono (by simp) (by simp)).trans
    ((MemFrame.setCtl _ 71 0).mono (by simp) (by simp))).trans
    ((MemFrame.setCtl _ 72 0).mono (by simp) (by simp))

/-- A table whose dense size is `0` and whose sparse memo is empty represents the empty table. -/
theorem _root_.L.Front.TblR.empty {k : IdxKind} {m m' : Mem} {b : ArrId} {t : ConLeche.Frontend.IdTable (Idx k)} (h : TblR m b t)
    (hf : MemFrame [] idCtl m m') (hz : szW m' b = 0)
    (hsp : MemoRV (spS b) idKey hVR m' (∅ : Std.HashMap Nat (Idx k))) :
    TblR m' b ({} : ConLeche.Frontend.IdTable (Idx k)) where
  size := by rw [hf.2.2.1 b]; exact h.size
  ctl := by rw [hf.2.2.1 CTL]; exact h.ctl
  sz := by rw [hz]; simp
  dense := fun i hi => by rw [hz] at hi; exact absurd hi (UInt64.not_lt_zero)
  sparse := ⟨∅, hsp, fun i _ => by simp [IdTable.get?_empty]⟩

/-- **`front_reset` empties the id tables**, keeping the records. -/
theorem frontReset_stateDR {m : Mem} {st : StateD} (h : StateDR m st) (hok : ResetOK m) :
    StateDR (resetM m) (StateD.blank.pre st.decls) := by
  have hf := resetM_frame m
  have f0 := resetM0_frame' m
  have fN := mclearG_frame (spS NID) (resetM0 m)
  have fL := mclearG_frame (spS LID) (resetM1 m)
  have fE := mclearG_frame (spS EID) (resetM2 m)
  obtain ⟨spN, hN, -⟩ := h.names.sparse
  obtain ⟨spL, hL, -⟩ := h.levels.sparse
  obtain ⟨spE, hE, -⟩ := h.exprs.sparse
  have nN : MemoRV (spS NID) idKey hVR (resetM m) (∅ : Std.HashMap Nat NIdx) :=
    tblMemo_frame (.inl rfl) fE (by decide) (tblMemo_frame (.inl rfl) fL (by decide)
      (memoRV_clear (spS NID) (spS_wf _ (.inl rfl)) idKey hVR _ spN
        (tblMemo_frame (.inl rfl) f0 (by decide) hN) hok.1))
  have nL : MemoRV (spS LID) idKey hVR (resetM m) (∅ : Std.HashMap Nat LIdx) :=
    tblMemo_frame (.inr (.inl rfl)) fE (by decide)
      (memoRV_clear (spS LID) (spS_wf _ (.inr (.inl rfl))) idKey hVR _ spL
        (tblMemo_frame (.inr (.inl rfl)) fN (by decide)
          (tblMemo_frame (.inr (.inl rfl)) f0 (by decide) hL)) hok.2.1)
  have nE : MemoRV (spS EID) idKey hVR (resetM m) (∅ : Std.HashMap Nat EIdx) :=
    memoRV_clear (spS EID) (spS_wf _ (.inr (.inr rfl))) idKey hVR _ spE
      (tblMemo_frame (.inr (.inr rfl)) fL (by decide)
        (tblMemo_frame (.inr (.inr rfl)) fN (by decide)
          (tblMemo_frame (.inr (.inr rfl)) f0 (by decide) hE))) hok.2.2
  refine ⟨h.names.empty hf (resetM_szW m NID (.inl rfl) h.names.ctl) nN,
    h.levels.empty hf (resetM_szW m LID (.inr (.inl rfl)) h.levels.ctl) nL,
    h.exprs.empty hf (resetM_szW m EID (.inr (.inr rfl)) h.exprs.ctl) nE, ?_, ?_⟩
  · simp only [StateD.pre_decls, StateD.blank, Array.append_empty]
    rw [hf.1 DECL (by simp) (by decide), hf.1 DLP (by simp) (by decide)]
    exact h.decls
  · rw [hf.2.2.1, hf.2.2.1]; exact h.ifs

end L.Checker
