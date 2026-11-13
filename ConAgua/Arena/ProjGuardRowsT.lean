module

public import ConAgua.Arena.ProjGuardRowsGo
import ConAgua.Arena.RecLayout.TblDec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.WhnfCoreRefine
public import ConAgua.Arena.StrLitExt
import all ConAgua.Arena.Infer
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
structure PgrProg (p : Prog) : Prop extends PgraProg p where
  pgr : p.lookup "proj_guard_rows" = some projGuardRowsL
  envFind : p.lookup "env_find" = some envFindL
  envRowGet : p.lookup "env_row_get" = some envRowGetL
  baseRowGet : p.lookup "base_row_get" = some baseRowGetL
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
at entry; `constTyAt_lkept` and the guard's `Keeps cpl` for the level readbacks): `env_find`,
`const_ty_at` (`ConstTyAtOK`), `opf_go` (`opfGo_okC`: the substitution on the stack at the old top,
the twin's `acc`), `proj_guard_rows_at` (`pgra_okC`: the rows above it). -/
theorem pgr_okH (p : Prog) (hP : PgrProg p) (hCT : ConstTyAtOK p)
    (n : Nat) (m m' : Mem) (a : AState) (M : ModeMaps) (q i us : Word) (tbl : IProjTable)
    (r : List Word) (hS : CoreS dn m a vis fe M eb) (hI : IWOK m) (hM : ∃ mp, hbMR m mp)
    (hq : decTbl (erecP m) q.toNat = some tbl) (hus : HW us)
    (h : callW p n "proj_guard_rows" [vis, q, i, us] m = some (r, m')) :
    ∃ y a', (projGuardRows fe (tbl.entry i.toNat) (decI us)).run a = .ok (y, a') ∧
      CoreAfterG dn m m' a' vis fe M eb ∧
      (∀ h l, denoteL a.store.ls h = some l → denoteL a'.store.ls h = some l) ∧ PgrRes m m' r y ∧
      IWOK m' ∧ IWGrow m m' ∧ ∃ mp, hbMR m' mp := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pgrW_spec p hP.pgr n _ vis q i us) h
  rw [hs'] at hW
  clear h hs'
  rcases n with _ | n
  · cases hW
  obtain ⟨-, -, -, hnp, hct32, hct, -⟩ := decTbl_rd (erRdOK m) hq
  simp only [pgrW] at hW
  rw [erRd_congr rfl rfl, erRd_congr rfl rfl] at hW
  rcases c1 : callW p n "env_find" [erRd m (q + ProjTbl.ctor), vis] m with _ | ⟨r1, m1⟩
  · rw [c1, pgrW.k_env_find.none] at hW; cases hW
  rw [c1] at hW
  obtain ⟨s1, hs1, hm1, -, hfind, hdec⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_refines p hP.envRowGet hP.baseRowGet hP.envFind n _ vis _ hS.env hct32) c1
  have hm1' : m1 = m := hs1 ▸ hm1
  subst hm1'
  have hctor : (tbl.entry i.toNat).ctor = decI (erRd m1 (q + ProjTbl.ctor)) := hct
  by_cases g1 : r1.headD 0 = 0
  · rw [pgrW.k_env_find.arm1 _ _ _ _ _ _ _ g1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hn : fe.find? (tbl.entry i.toNat).ctor = none := by
      rw [hctor, hfind]; simp only [envFound, g1, ↓reduceIte]
    exact ⟨none, a, pgrT_none _ _ _ _ hn, ⟨M, hS, KeptAll.refl _ _, StackGrew.refl _⟩,
      fun _ _ h => h, rfl, hI, IWGrow.refl _, hM⟩
  obtain ⟨ci, hci⟩ := hdec g1
  have hfind' : fe.find? (tbl.entry i.toNat).ctor = some ci := by
    rw [hctor, hfind]; simp only [envFound, g1, ↓reduceIte]; exact hci
  rw [pgrW.k_env_find.arm2 _ _ _ _ _ _ _ g1] at hW
  generalize hc : r1.tail.headD 0 = c at hW hci
  have hcv := decCI_cvA hci
  obtain ⟨hlps, -, hty, hty32⟩ := L.Arena.decCV_rd (erRdOK m1) hcv
  obtain ⟨hnn32, hnn⟩ := decCV_nameRd (erRdOK m1) hcv
  simp only [erRd_congr rfl rfl] at hW
  -- `const_ty_at`
  rcases c2 : callW p n "const_ty_at" [erRd m1 (c + 1), erRd m1 (c + 2), erRd m1 (c + 3),
      erRd m1 (c + 4), us] m1 with _ | ⟨r2, m2⟩
  · rw [c2] at hW; cases hW
  rw [c2] at hW
  simp only [pgrW.k_const_ty_at] at hW
  have h2 := CoreSpec.of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (hCT n ⟨m1, Locals.init []⟩ a dn vis fe M eb _ _ _ _ us _ hS hnn32 hty32 hus hlps) c2
  have hcvE : ci.toConstantVal = ⟨decI (erRd m1 (c + 1)), ci.toConstantVal.levelParams,
      decE (erRd m1 (c + 4))⟩ := by
    rw [cv_eta ci.toConstantVal, hnn, hty]; rfl
  have hrun2 : (constTyAt ci.toConstantVal (decI us)).run a =
      .ok (decE (r2.headD 0), AM.st (constTyAt ci.toConstantVal (decI us)) a) := by
    rw [hcvE, AM.run_of_ok _ _ h2.run, h2.res]; rfl
  obtain ⟨M2, hS2, hK2, hSt2⟩ := h2.after
  rw [← hcvE] at hS2
  have hr2 : HW (r2.headD 0) := h2.resOk
  have hfr2 := callW_coreFrame hP.cl (mem_stageCoreFns (List.mem_append_right _ (coreFn_of (by decide))) (by simp [coreLeafOnly])) c2
  obtain ⟨-, hg2⟩ := hfr2.2 hI
  generalize ha2 : AM.st (constTyAt ci.toConstantVal (decI us)) a = a2 at hrun2 hS2
  have hlk2 : ∀ h l, denoteL a.store.ls h = some l → denoteL a2.store.ls h = some l :=
    fun h l hd => constTyAt_lkept _ _ a _ a2 hrun2 h l hd
  -- the stack top's capacity
  generalize hco : rdW (m2.arr64 CTL) 136 = co at hW
  by_cases gl : m2.len64 SPN < co
  · rw [ite_eq_left gl] at hW; cases hW
  rw [ite_eq_right gl] at hW
  have hsp2 := hS2.spn
  have hcob : co.toNat ≤ (m2.arr64 SPN).size := by
    have h' := UInt64.not_lt.mp gl
    rw [UInt64.le_iff_toNat_le, Mem.len64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at h'
    exact h'
  have htop2 : spTop m2 = co := hco
  have ht12 : spTop m2 = spTop m1 := hSt2.top
  -- `opf_go`: the parameters opened, the substitution on the stack at `co`
  rcases c3 : callW p n "opf_go" [erRd m1 (q + ProjTbl.numParams), r2.headD 0, 0, co, 0] m2 with _ | ⟨r3, m3⟩
  · rw [c3] at hW; cases hW
  rw [c3] at hW
  simp only [pgrW.k_opf_go] at hW
  obtain ⟨hfr3, hg3, hbk3, hpl3⟩ := pg_frame hP.toPgraProg (f := "opf_go") (h := c3)
  rw [callW_opfP hP.opf] at c3
  obtain ⟨x3, a3, M3, hrun3, hS3, hK3, hsz3, hkb3, hO, hacc⟩ := opfGo_okC n m2 m3 a2 M2 _ _ 0 co 0 #[] r3 c3
    hS2 hr2 (by simpa using L.Arena.SpineR.nil_at m2 _ hcob) (by rw [hco]; simp) (by simp; omega)
  have hlk3 : a3.store.lss = a2.store.lss := by
    have := (keepsW_opfRawGo _ _ _ _).run hrun3; simp only [cpl, Prod.mk.injEq] at this; exact this.2.2
  have hnpE : (tbl.entry i.toNat).numParams = (erRd m1 (q + ProjTbl.numParams)).toNat := hnp
  have hrunT : ∀ (y : Option (Array (Nat × EIdx))) (a4 : AState),
      (match x3 with
        | some (_, acc, rr) => projGuardRowsAt (tbl.entry i.toNat) acc rr
        | none => pure none).run a3 = .ok (y, a4) →
      (projGuardRows fe (tbl.entry i.toNat) (decI us)).run a = .ok (y, a4) := by
    intro y a4 h4
    simp only [projGuardRows, hfind', StateT.run_bind, hrun2, except_ok_bind]
    rw [hnpE]; simp only [UInt64.toNat_zero] at hrun3; rw [hrun3]; simp only [except_ok_bind]
    cases x3 with
    | none => exact h4
    | some t => obtain ⟨_, _, _⟩ := t; exact h4
  cases x3 with
  | none =>
    have g3 : r3.headD 0 = 0 := hO
    rw [ite_eq_left g3] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hfc := MemFrame.setCtl m3 136 co
    have hS4 := hS3.frame_stk hfc (by simp) (by simp)
    have htop4 : spTop (m3.set64 CTL 136 co) = co := by
      simp only [spTop]; rw [L.Arena.rdW_set64, ite_eq_left ⟨rfl, rfl, by have := hS3.ctl136; simpa using this⟩]
    have hspn4 : (m3.set64 CTL 136 co).arr64 SPN = m3.arr64 SPN := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    refine ⟨none, a3, hrunT none a3 rfl, ⟨M3, hS4, hK2.trans hK3, ?_⟩,
      fun h l hd => by have := hlk2 h l hd; simp only [EStore.ls] at this ⊢; rw [hlk3]; exact this,
      rfl, hS4.iw, hg2.trans (hg3.trans (IWGrow.of_keep hfc ⟨by decide, by decide, by decide⟩
        ⟨by decide, by decide, by decide⟩)), hS4.memos.hb⟩
    refine hSt2.toGrew.trans ⟨by rw [htop4, ← htop2]; exact UInt64.le_refl _, by rw [hspn4, hsz3],
      fun w hw => ?_, hbk3.trans (BKept.of_frame hfc (by decide) (by decide)),
      hpl3.trans (PoolGrew.of_frame hfc (by decide) (by decide))⟩
    simp only [spW, hspn4]
    exact hkb3 w (by rw [htop2] at hw; simpa [UInt64.lt_iff_toNat_lt] using hw)
  | some t =>
    obtain ⟨fvs, acc, rr⟩ := t
    obtain ⟨g3, hrr, hdrr, htop3, hsl3, hbel3⟩ := hO
    have hacc' : acc = fvs.toArray := by simpa using hacc (fvs, acc, rr) rfl
    subst hacc'
    rw [ite_eq_right (by rw [g3]; decide)] at hW
    simp only [UInt64.add_zero] at htop3 hsl3 hbel3
    generalize hro : rdW (m3.arr64 CTL) 136 = ro at hW
    rcases c4 : callW p n "proj_guard_rows_at" [i, co, erRd m1 (q + ProjTbl.numParams), r3.tail.headD 0, ro] m3 with
      _ | ⟨r4, m4⟩
    · rw [c4] at hW; cases hW
    rw [c4] at hW
    simp only [pgrW.k_proj_guard_rows_at] at hW
    obtain ⟨-, hg4, hbk4, hpl4⟩ := pg_frame hP.toPgraProg (f := "proj_guard_rows_at") (h := c4)
    have hb3 := hsl3.bound
    have hsz32 : (m3.arr64 SPN).size = (m2.arr64 SPN).size := hsz3
    have hro' : ro.toNat = co.toNat + (erRd m1 (q + ProjTbl.numParams)).toNat := by
      rw [← hro, htop3, UInt64.toNat_add]; omega
    obtain ⟨y, a4, M4, hrun4, hS4, hK4, hsz4, ht4, hkb4, hres4⟩ := pgra_okC hP.toPgraProg n
      (tbl.entry i.toNat) rfl hnpE c4 hS3 hrr hsl3 (by simp only [spTop]; rw [hro]; omega) hro
      (by simp only [spTop]; rw [hro]; omega)
    have hlk4 : a4.store.lss = a3.store.lss := by
      have := (keepsW_pgra _ _ _).run hrun4; simp only [cpl, Prod.mk.injEq] at this; exact this.2.2
    have hgrew : StackGrew m1 m4 := by
      refine hSt2.toGrew.trans ⟨?_, by rw [hsz4, hsz32], fun w hw => ?_, hbk3.trans hbk4, hpl3.trans hpl4⟩
      · rw [UInt64.le_iff_toNat_le, htop2]; simp only [spTop] at ht4 ⊢; rw [hro] at ht4; omega
      · rw [htop2, UInt64.lt_iff_toNat_lt] at hw
        rw [hkb4 w (by simp only [spTop]; rw [hro]; omega), hbel3 w hw]
    have hlk : ∀ h l, denoteL a.store.ls h = some l → denoteL a4.store.ls h = some l :=
      fun h l hd => by have := hlk2 h l hd; simp only [EStore.ls] at this ⊢; rw [hlk4, hlk3]; exact this
    have hIW : IWGrow m1 m4 := hg2.trans (hg3.trans hg4)
    cases y with
    | none =>
      have g4 : r4.headD 0 = 0 := hres4
      rw [ite_eq_left g4] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      exact ⟨none, a4, hrunT none a4 (by rw [hdrr] at hrun4; exact hrun4), ⟨M4, hS4, hK2.trans (hK3.trans hK4), hgrew⟩, hlk, rfl,
        hS4.iw, hIW, hS4.memos.hb⟩
    | some rows =>
      obtain ⟨g4, hsz, hrows, hbr⟩ := hres4
      rw [ite_eq_right (by rw [g4]; decide)] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨some rows, a4, hrunT _ a4 (by rw [hdrr] at hrun4; exact hrun4), ⟨M4, hS4, hK2.trans (hK3.trans hK4), hgrew⟩, hlk,
        ⟨by simp, ?_, by simpa using hsz, by simpa using hrows, by simpa using hbr⟩,
        hS4.iw, hIW, hS4.memos.hb⟩
      simp only [List.tail_cons, List.headD_cons]
      rw [← ht12, htop2, hro']; omega

end

end L.Ind
