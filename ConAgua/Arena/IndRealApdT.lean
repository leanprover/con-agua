import ConAgua.Arena.DeclApdRef
import ConAgua.Arena.MemoRekey
import ConAgua.Arena.StageTLift

/-!
# `all_level_params_defined`'s model and its refinement under `StageT` (lane `indproofs4`, helper `wkt`)

The program- and fuel-free model `apdF := callF apdP "all_level_params_defined"` (`IndReal.lean`'s
recipe) over the walk's program `apdP` (lane `decls3`'s `apdFns` with the reads it calls); it
writes only its memo, array `APDM` (151) and `CTL[152‥153]`.

Lane `decls3`'s `allLevelParamsDefined_refines` (`DeclApdRef.lean`) under `StageT`: the twin side's
`ApdEnv` is `TwinOK`'s (`StoreDen`, `NStoreWF`); the walk's memo shares its array and epoch word
with the core's `wscopedBFast` memo (`coreWsSch`), which `TwinOK` carries well formed, so the
entry's clear starts the walk from the empty memo, and the walk's memo after it is the core's
memo under its own key codec (`memoRV_rekey`): `TwinOK` holds after. The parameters' names read
back is the caller's (`lps = []`: trivially). Replaced
`IndStubsT.allLevelParamsDefinedT_spec` (deleted): the callers' models call `apdF` (see the note there).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `all_level_params_defined`'s functions and the reads it calls. -/
def apdP : Prog := apdFns ++ [("e_view", eView), ("ls_node", lsNode), ("lv_node", lvNode)]

/-- The functions `all_level_params_defined` reaches. -/
def apdPFns : List FnName :=
  ["all_level_params_defined", "alpd_go", "alpd_ls", "apd_find", "apd_put", "apd_clear", "lv_apd",
    "lv_mem", "e_view", "ls_node", "lv_node"]

theorem apdP_closed : closedA apdP [APDM] [152, 153] apdPFns = true := by decide +kernel

/-- The program bundle. -/
abbrev ApdF (p : Prog) : Prop := ProgHas p apdP

/-- **The model of `all_level_params_defined`** (program- and fuel-free). -/
noncomputable def apdF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF apdP "all_level_params_defined" m args

/-- `all_level_params_defined` writes only its memo. -/
theorem apdF_frame {m m' : Mem} {args r : List Word} (h : apdF m args = some (r, m')) :
    ApdFr m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame apdP_closed (by decide) (run_of_callW hc)).1

/-- **A program's call of `all_level_params_defined` is the model's** (`realCall p`'s reading). -/
theorem apdF_of_callW {p : Prog} (hp : ApdF p) {n : Nat} {args r : List Word} {m m' : Mem}
    (h : callW p n "all_level_params_defined" args m = some (r, m')) :
    apdF m args = some (r, m') :=
  callF_of_callW (by rw [← callW_agree apdP_closed (hp.agree apdPFns) n (by decide)]; exact h)

theorem apdP_prog : ApdProg apdP := by
  constructor <;> rfl

/-! ## The core's `wscopedBFast` memo and the walk's -/

/-- The walk's memo is the core's under the core's key codec (keys `(h, 0)`, values `≠ 0`). -/
theorem apdMR_ws {m : Mem} {mp : Std.HashMap EIdx Bool} (h : apdMR m mp) :
    ∃ mp' : Std.HashMap (EIdx × Nat) Bool, MemoRG coreWsSch lfKey (fun w => w != 0) m mp' :=
  memoRV_rekey apdSch bmKey lfKey apdVR _ (fun e => (e, 0))
    (fun _ _ h => by simp only [Prod.mk.injEq] at h; exact h.1) id
    (fun k1 k2 hk => by
      obtain ⟨hk1, rfl⟩ := hk
      exact ⟨hk1, rfl⟩)
    (fun _ => rfl) (fun _ => rfl)
    (fun w v hv => by subst hv; cases v <;> rfl) h

/-- The entry's clear of the core's memo is the walk's empty memo. -/
theorem apdMR_clear {m : Mem} (h : WalkMemos m) (h0 : rdW (m.arr64 CTL) apdSch.cs + 2 ≠ 0) :
    apdMR (mclearG apdSch m) ∅ :=
  let ⟨mp, hm⟩ := h.1
  memoRV_empty_rekey apdSch lfKey bmKey _ apdVR
    (memoRV_clear coreWsSch coreWsSch_wf lfKey _ m mp hm h0)

/-- **`TwinOK` across the walk**: its memo is the core's (`apdMR_ws`), the rest is framed. -/
theorem _root_.L.Arena.TwinOK.apd {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {m m' : Mem}
    {a : AState} (h : TwinOK dn m a fe) (hf : ApdFr m m') {mp : Std.HashMap EIdx Bool}
    (hM : apdMR m' mp) : TwinOK dn m' a fe := by
  obtain ⟨hIl, hAb, -, ⟨mf, hfl⟩, ⟨ml, hlsb⟩, hLP⟩ := h.memos
  refine ⟨h.readL, h.readLs, h.nwf, by rw [hf.2.2.1]; exact h.erec, by rw [hf.2.2.1]; exact h.spn,
    ⟨?_, ?_, apdMR_ws hM, ⟨mf, ?_⟩, ⟨ml, ?_⟩, hLP.frame hf (by decide) (by decide)⟩,
    by rw [hf.2.2.1]; exact h.bstk, h.den.mem m'⟩
  · obtain ⟨mp, hm⟩ := hIl
    exact ⟨mp, memoRG_frame coreIlSch coreIlSch_wf lfKey _ _ _ (by decide) (by decide) m m' hf mp hm⟩
  · obtain ⟨mp, hm⟩ := hAb
    exact ⟨mp, memoRG_frame coreAbSch coreAbSch_wf lfKey _ _ _ (by decide) (by decide) m m' hf mp hm⟩
  · exact memoRG_frame coreFlSch coreFlSch_wf bmKey _ _ _ (by decide) (by decide) m m' hf mf hfl
  · exact memoRG_frame coreLsbSch coreLsbSch_wf bmKey _ _ _ (by decide) (by decide) m m' hf ml hlsb

/-! ## The refinement under `StageT` -/

/-- **`all_level_params_defined` refines `allLevelParamsDefined` under `StageT`**: `(o, l)` an
`IW` slice decoding to the handles `lps` whose names read back, `e` a handle. -/
theorem apdF_okT (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (o l e : Word)
    (he : H e) (lps : List NIdx) :
    RelW apdF [o, l, e]
      (fun m a => StageT dn vis fe m a ∧ decHL m o.toNat l.toNat = some lps ∧
        ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks)
      (allLevelParamsDefined lps (decI e)) (KeepPostT dn vis fe decW0B) := by
  intro m m' a r h ⟨hT, hdec, ks, hks⟩
  obtain ⟨n, hc⟩ := callF_run h
  rcases n with _ | n
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (allLevelParamsDefined_spec_raw apdP apdP_prog.eview apdP_prog.lsnode apdP_prog.find
      apdP_prog.put apdP_prog.clear apdP_prog.lmem apdP_prog.lnode apdP_prog.lapd apdP_prog.ls
      apdP_prog.go apdP_prog.entry n ⟨m, Locals.init []⟩ o l e) hc
  subst hs'
  obtain ⟨b, hrun, hr, hS', hg, mp, hM⟩ := apdEntry_ok n hT.stage
    (ApdEnv.of_den hT.twin.den hT.twin.nwf) o l e _ lps ks hks hdec he
    (apdMR_clear hT.twin.memos.2.2) hm
  have hf := apdF_frame h
  refine ⟨b, a, ?_, ⟨hS', hT.twin.apd hf hM, ?_⟩, hg, apd_decW0B hr⟩
  · exact hrun
  · rw [pinW_frame hf (by decide)]; exact hT.flag

end L.Ind
