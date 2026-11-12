module

public import ConAgua.Arena.ProjGuardRowsGo
public import ConAgua.Arena.ProjGuardRef
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.WhnfCoreRefine
public import ConAgua.Arena.StrLitExt
import all ConAgua.Arena.Infer
import ConAgua.Arena.ProjGuardRowsCI
import ConAgua.Arena.IndSumSpec.StructUsedHb
public import ConAgua.Arena.IndTwin

@[expose] public section

/-!
# `proj_guard_rows` refines `projGuardRows` under `CoreS` (`pgr_ok`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind (IW)

/-- **`proj_guard_rows`' word model** (its callees lifted). -/
l_model pgrW_spec (p : Prog) (hf : p.lookup "proj_guard_rows" = some projGuardRowsL)
  fns [hf ↦ pgrW list]
  specs [callW_spec p n "env_find", callW_spec p n "const_ty_at",
    callW_spec p n "opf_go", callW_spec p n "proj_guard_rows_at"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]


end L.Arena

namespace L.Ind

open L.Arena

/-- **The guard rows on the stack**: row `i` at `ro + 2 i` (its depth) and `ro + 2 i + 1` (its
term). (`RowsAt` of `ProjGuardRef.lean`.) -/
def GRows (m : Mem) (ro : Word) (rows : Array (Nat × EIdx)) : Prop :=
  ∀ (i : Word) (h : i.toNat < rows.size), (spW m (ro + 2 * i)).toNat = (rows[i.toNat]'h).1 ∧
    HW (spW m (ro + 2 * i + 1)) ∧ decE (spW m (ro + 2 * i + 1)) = (rows[i.toNat]'h).2

/-! ## `proj_guard_rows` -/

/-- A table record's parameter count (word `q + 5`) and constructor (word `q + 6`). -/
theorem decTbl_npc {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {tbl : IProjTable} (h : decTbl R q.toNat = some tbl) :
    tbl.numParams = (rd (q + 5)).toNat ∧ HW (rd (q + 6)) ∧ tbl.ctor = decI (rd (q + 6)) := by
  unfold decTbl at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨sn, -, lp, -, np, hnp, ct, hct, nf, -, bs, -, rfl⟩ := h
  obtain ⟨w, hw, hw32, rfl⟩ := hd?_some hct
  have e : rd (q + 6) = w := hR.offN (k := 6) hw (by decide)
  simp only [nat?, Option.map_eq_some_iff] at hnp
  obtain ⟨v, hv, rfl⟩ := hnp
  have e5 : rd (q + 5) = v := hR.offN (k := 5) hv (by decide)
  rw [e, e5]
  exact ⟨rfl, hw32, rfl⟩

/-- A constant record's name (word `q + 1`). -/
theorem decCV_nameRd {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {cv : IConstantVal} (h : decCV R (q.toNat + 1) = some cv) :
    HW (rd (q + 1)) ∧ cv.name = decI (rd (q + 1)) := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨nm, hn, ls, -, ty, -, hc⟩ := h
  cases hc
  obtain ⟨w, hw, hl, rfl⟩ := hd?_some hn
  have e : rd (q + 1) = w := hR.offN (k := 1) hw (by decide)
  rw [e]; exact ⟨hl, rfl⟩

theorem cv_eta (cv : IConstantVal) : cv = ⟨cv.name, cv.levelParams, cv.type⟩ := rfl

/-- What `proj_guard_rows`' refinement needs of a program. -/
structure PgrProg (p : Prog) : Prop where
  pgr : p.lookup "proj_guard_rows" = some projGuardRowsL
  pgra : p.lookup "proj_guard_rows_at" = some projGuardRowsAtL
  envFind : p.lookup "env_find" = some envFindL
  envRowGet : p.lookup "env_row_get" = some envRowGetL
  baseRowGet : p.lookup "base_row_get" = some baseRowGetL
  ftd : p.lookup "fvar_type_d" = some fvarTypeDL
  eView : p.lookup "e_view" = some eView
  us : UsF p
  opf : OpfF p
  cl : CoreStageClosed p


/-! ## `constTyAt` only extends the store (`EMono`) -/

section emono
open L.Arena

theorem emono_internNNode (v : NNodeView) : EMono (internNNode v) := by
  unfold EMono; intro a r a' h
  simp only [internNNode, StateT.run_bind, StateT.run_get, pure_bind] at h
  emono_close (EStore.internName_ext _ _)

theorem emono_internName : ∀ n : ConLeche.Name, EMono (internName n)
  | .anonymous => by simp only [internName]; exact emono_internNNode _
  | .str p s => by simp only [internName]; exact EMono.bind (emono_internName p) fun _ => emono_internNNode _
  | .num p k => by simp only [internName]; exact EMono.bind (emono_internName p) fun _ => emono_internNNode _

theorem emono_internLevel : ∀ u : ConLeche.Level, EMono (internLevel u)
  | .zero => by simp only [internLevel]; exact emono_internLNode _
  | .succ u => by simp only [internLevel]; exact EMono.bind (emono_internLevel u) fun _ => emono_internLNode _
  | .max u v => by
    simp only [internLevel]
    exact EMono.bind (emono_internLevel u) fun _ => EMono.bind (emono_internLevel v) fun _ =>
      emono_internLNode _
  | .imax u v => by
    simp only [internLevel]
    exact EMono.bind (emono_internLevel u) fun _ => EMono.bind (emono_internLevel v) fun _ =>
      emono_internLNode _
  | .param n => by simp only [internLevel]; exact EMono.bind (emono_internName n) fun _ => emono_internLNode _

theorem emono_internLevelList : ∀ us : List ConLeche.Level, EMono (internLevelList us)
  | [] => by simp only [internLevelList]; exact EMono.pure _
  | u :: us => by
    simp only [internLevelList]
    exact EMono.bind (emono_internLevel u) fun _ => EMono.bind (emono_internLevelList us) fun _ =>
      EMono.pure _

theorem emono_internLevels (us : List ConLeche.Level) : EMono (internLevels us) := by
  unfold internLevels
  exact EMono.bind (emono_internLevelList us) fun _ => emono_internLsNode _

theorem emono_derivedE (h : EIdx) : EMono (derivedE h) := EMono.of_keeps (keeps_derivedE h)
/-- A primitive that reads the state and writes back only its caches or memos. -/
macro "prim_keeps' " d:ident : tactic => `(tactic| (
  unfold Keeps; intro a r a' h
  simp only [$d:ident, StateT.run_bind, StateT.run_get, pure_bind] at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | (simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind] at h; cases h; rfl)
    | (exfalso; revert h; simp [ConRon.Arena.fail, failDanglingLs, throwThe, MonadExceptOf.throw, throw,
        StateT.run, StateT.lift, bind, Except.bind, Functor.map, Except.map]; done)))

theorem emono_readLevelM (h : LIdx) : EMono (readLevelM h) := EMono.of_keeps (by prim_keeps' readLevelM)
theorem emono_readNameM (h : NIdx) : EMono (readNameM h) := EMono.of_keeps (by prim_keeps' readNameM)
theorem emono_readLevelsM (h : LsIdx) : EMono (readLevelsM h) :=
  EMono.of_keeps (by prim_keeps' readLevelsM)
theorem emono_readNamesM : ∀ hs : List NIdx, EMono (readNamesM hs)
  | [] => by simp only [readNamesM]; exact EMono.pure _
  | h :: hs => by
    simp only [readNamesM]
    exact EMono.bind (emono_readNameM h) fun _ => EMono.bind (emono_readNamesM hs) fun _ => EMono.pure _
theorem emono_instLPGet (k : EIdx × Nat) : EMono (instLPGet k) := EMono.of_keeps (by prim_keeps instLPGet)
theorem emono_instLPSet (k : EIdx × Nat) (r : EIdx) : EMono (instLPSet k r) :=
  EMono.of_keeps (by prim_keeps instLPSet)
theorem emono_instLPClear : EMono instLPClear := EMono.of_keeps (by prim_keeps instLPClear)
theorem emono_instLPLGet (k : LIdx) : EMono (instLPLGet k) := EMono.of_keeps (by prim_keeps instLPLGet)
theorem emono_instLPLSet (k r : LIdx) : EMono (instLPLSet k r) := EMono.of_keeps (by prim_keeps instLPLSet)
theorem emono_instLPLsGet (k : LsIdx) : EMono (instLPLsGet k) :=
  EMono.of_keeps (by prim_keeps instLPLsGet)
theorem emono_instLPLsSet (k r : LsIdx) : EMono (instLPLsSet k r) :=
  EMono.of_keeps (by prim_keeps instLPLsSet)

theorem emono_substLMemoAt (ks : List ConLeche.Name) (us : List ConLeche.Level) (u : LIdx) :
    EMono (substLMemoAt ks us u) := by
  unfold substLMemoAt
  refine EMono.bind (emono_instLPLGet _) fun o => ?_
  split
  · exact EMono.pure _
  · exact EMono.bind (emono_readLevelM _) fun _ => EMono.bind (emono_internLevel _) fun _ =>
      EMono.bind (emono_instLPLSet _ _) fun _ => EMono.pure _

theorem emono_substLsMemoAt (ks : List ConLeche.Name) (us : List ConLeche.Level) (vs : LsIdx) :
    EMono (substLsMemoAt ks us vs) := by
  unfold substLsMemoAt
  refine EMono.bind (emono_instLPLsGet _) fun o => ?_
  split
  · exact EMono.pure _
  · exact EMono.bind (emono_readLevelsM _) fun _ => EMono.bind (emono_internLevels _) fun _ =>
      EMono.bind (emono_instLPLsSet _ _) fun _ => EMono.pure _

/-- One step of `instLPGo`'s `succ` case. -/
macro "emono_lp" " using " ih:term : tactic => `(tactic| (
  repeat' (first
    | exact EMono.pure _ | exact EMono.fail _ | exact $ih _
    | exact emono_view _ | exact emono_derivedE _ | exact emono_internE _
    | exact emono_internLamE _ _ | exact emono_internForallEE _ _
    | exact emono_instLPGet _ | exact emono_instLPSet _ _
    | exact emono_substLMemoAt _ _ _ | exact emono_substLsMemoAt _ _ _
    | (unfold internRebuiltSort) | (unfold internRebuiltConst) | (unfold internRebuiltFVar)
    | (unfold internRebuiltApp) | (unfold internRebuiltLam) | (unfold internRebuiltForallE)
    | (unfold internRebuiltLetE) | (unfold internRebuiltProj)
    | (unfold internSortE) | (unfold internConstE) | (unfold internFVarE) | (unfold internAppE)
    | (unfold internLetEE) | (unfold internProjE)
    | (unfold instLPArmFVar) | (unfold instLPArmApp) | (unfold instLPArmLam)
    | (unfold instLPArmForallE) | (unfold instLPArmLet) | (unfold instLPArmProj)
    | with_reducible apply EMono.bind | apply EMono.ite | intro _ | split | (dsimp only))))

theorem emono_instLPGo (ks : List ConLeche.Name) (us : List ConLeche.Level) (F : Nat) :
    ∀ h, EMono (instLPGo ks us F h) := by
  induction F with
  | zero => intro h; rw [instLPGo_zero]; exact EMono.fail _
  | succ F ih =>
    intro h; rw [instLPGo_succ]
    emono_lp using ih

theorem emono_instLPFast (F : Nat) (ks : List NIdx) (us : LsIdx) (e : EIdx) :
    EMono (instLPFast F ks us e) := by
  unfold instLPFast
  refine EMono.bind (emono_derivedE _) fun d => ?_
  split
  · exact EMono.pure _
  · exact EMono.bind (emono_readNamesM _) fun _ => EMono.bind (emono_readLevelsM _) fun _ =>
      EMono.bind emono_instLPClear fun _ => EMono.bind (emono_instLPGo _ _ _ _) fun _ =>
      EMono.bind emono_instLPClear fun _ => EMono.pure _

theorem emono_constTyAt (cv : IConstantVal) (us : LsIdx) : EMono (constTyAt cv us) := by
  unfold constTyAt
  refine EMono.bind (EMono.of_keeps (by unfold Keeps; intro a r a' h; cases h; rfl)) fun s => ?_
  split
  · exact EMono.pure _
  · refine EMono.bind (emono_instLPFast _ _ _ _) fun r => ?_
    unfold EMono; intro a x a' h
    simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind, StateT.run_pure] at h
    cases h; exact Ext.refl _

/-- **`constTyAt` keeps every level readback** (it only extends the store). -/
theorem constTyAt_lkept (cv : IConstantVal) (us : LsIdx) : LKept (constTyAt cv us) := by
  intro a x a' h l u hd
  have he := emono_constTyAt cv us
  unfold EMono at he
  exact (he a x a' h).lss.ls.lvl l u hd

end emono

theorem pgrT_none (fe : IFEnv) (entry : IProjEntry) (us : LsIdx) (a : AState)
    (h : fe.find? entry.ctor = none) : (projGuardRows fe entry us).run a = .ok (none, a) := by
  simp [projGuardRows, h]; rfl

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {eb : Word}

/-- **`proj_guard_rows` refines `projGuardRows` under `CoreS`** (the pool's `IWOK` and the `hb` memo
at entry; the L code aborts where the parameter count plus field index wraps; `constTyAt_lkept` for the level
readbacks): `env_find`, `const_ty_at` (`ConstTyAtOK`), `open_pis_at_fvars_f` (`opfF_okC`),
`proj_guard_rows_at` (`pgra_ok`). -/
theorem pgr_okH (p : Prog) (hP : PgrProg p) (hCT : ConstTyAtOK p)
    (n : Nat) (m m' : Mem) (a : AState) (M : ModeMaps) (q i us : Word) (tbl : IProjTable)
    (r : List Word) (hS : CoreS dn m a vis fe M eb) (hI : IWOK m) (hM : ∃ mp, hbMR m mp)
    (hq : decTbl (erecP m) q.toNat = some tbl) (hus : HW us)
    (h : callW p n "proj_guard_rows" [vis, q, i, us] m = some (r, m')) :
    ∃ y a', (projGuardRows fe (tbl.entry i.toNat) (decI us)).run a = .ok (y, a') ∧
      CoreAfterG dn m m' a' vis fe M eb ∧
      (∀ h l, denoteL a.store.ls h = some l → denoteL a'.store.ls h = some l) ∧ PgrRes m m' r y ∧
      IWOK m' ∧ IWGrow m m' ∧ ∃ mp, hbMR m' mp := by
  sorry

end

end L.Ind
