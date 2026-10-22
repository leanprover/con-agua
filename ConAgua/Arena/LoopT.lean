import ConAgua.Arena.Checker
import ConAgua.Arena.IndTwin
import ConRon.Bridge.Promote.Walk

/-!
# The declaration loop with the core's invariants: `LoopT` (lane `loopt`)

The loop's relation `LoopR` (`DeclBase.lean`) carries the stage relation `StageR = CheckR ∧ IWOK`,
but not the twin-side invariants the core's refinements need (`TwinOK`, `DeclLvlStage.lean`) nor the
pin table's flag word, so no stage theorem stated under `StageT` (`IndTwin.lean`) can be called from
the loop. `LoopT` is `LoopR` with those two parts, by named components, a separate predicate
(`LoopR` keeps its shape and its uses):

* `loop` — `LoopR`,
* `twin` — `TwinOK` at the loop's environment,
* `flag` — the pin table is filled (`pinW m 0 ≠ 0`).

`LoopT.stageT` is the stage relation with the twin's invariants, so every `StageT` theorem applies
at a state in `LoopT`.

What is here: `LoopT` across the per-declaration bracket's L functions (`flush_caches`,
`scratch_enter`, the pending push), the view restriction of phase B, and a frame lemma for
`TwinOK` (a writer that leaves the core's memos, `EREC` and the pins alone keeps it).
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsR)

/-! ## The relation -/

/-- **The declaration loop's relation with the core's invariants**: `LoopR`, the twin's invariants
`TwinOK` at the loop's environment, and the pin table's flag. -/
structure LoopT (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState)
    (vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (ds : Array IDeclaration) : Prop where
  loop : LoopR pins dn m a vis fe pend ds
  twin : TwinOK dn m a fe
  flag : pinW m 0 ≠ 0

section rel
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState}
  {vis : Word} {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}

/-- **`LoopT` is the stage relation with the twin's invariants** (every `StageT` theorem applies). -/
theorem LoopT.stageT (h : LoopT pins dn m a vis fe pend ds) : StageT dn vis fe m a :=
  ⟨⟨h.loop.check, h.loop.iw⟩, h.twin, h.flag⟩

/-- `LoopT` is `CoreS` (at the eager bit `0`). -/
theorem LoopT.core (h : LoopT pins dn m a vis fe pend ds) : ∃ M, CoreS dn m a vis fe M 0 :=
  h.stageT.core

end rel

/-! ## `TwinOK` across memory writers -/

section frames
variable {dn : NIdx → Option ConLeche.Name} {fe : IFEnv}

/-- **`TwinOK` across a writer** that leaves `EREC`, the core memos (arrays 49, 50, 151‥153, `CTL`
48, 50, 152, 154, 156) alone; the twin state unchanged. -/
theorem TwinOK.frame {A : List ArrId} {C : List Word} {m m' : Mem} {a : AState}
    (hf : MemFrame A C m m') (hE : EREC ∉ A) (hA : (50 : ArrId) ∉ A ∧ (49 : ArrId) ∉ A)
    (hC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C)
    (hWA : (151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A)
    (hWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C)
    (h : TwinOK dn m a fe) : TwinOK dn m' a fe :=
  ⟨h.readL, h.readLs, h.nwf, by rw [hf.2.2.1]; exact h.erec, by rw [hf.2.2.1]; exact h.spn,
    h.memos.frame hf hA hC hWA hWC, by rw [hf.2.2.1]; exact h.bstk,
    h.den.frameE (hf.1 EREC hE (by decide))⟩

/-- `TwinOK` across a writer of `CTL` words below 128 other than 48 and 50 (the bracket's). -/
theorem TwinOK.frameLo {C : List Word} {m m' : Mem} {a : AState} (hf : MemFrame [] C m m')
    (hC : ∀ x ∈ C, x.toNat < 128) (h48 : (48 : Word) ∉ C) (h50 : (50 : Word) ∉ C)
    (h : TwinOK dn m a fe) : TwinOK dn m' a fe :=
  h.frame hf (by simp) ⟨by simp, by simp⟩ ⟨h50, h48⟩ ⟨by simp, by simp, by simp⟩
    ⟨fun h' => by have := hC _ h'; simp at this, fun h' => by have := hC _ h'; simp at this,
      fun h' => by have := hC _ h'; simp at this⟩

end frames

/-! ## The twin's side of the bracket's opening -/

section twin
variable {dn : NIdx → Option ConLeche.Name} {fe : IFEnv}

/-- The twin state after `flushCaches`. -/
theorem flushCaches_st (a : AState) : AM.st flushCaches a = { a with caches := Caches.empty } := rfl

/-- The twin state after `enterScratch`. -/
theorem enterScratch_st (a : AState) :
    AM.st enterScratch a = { store := a.store.enableScratch, memos := Memos.empty,
      caches := a.caches, pins := a.pins } := rfl

/-- **`TwinOK` after emptying the caches** (`flushCaches`): the readback caches hold nothing. -/
theorem TwinOK.flush {m : Mem} {a : AState} (h : TwinOK dn m a fe) :
    TwinOK dn m { a with caches := Caches.empty } fe := by
  refine ⟨fun k l hk => ?_, fun k l hk => ?_, h.nwf, h.erec, h.spn, h.memos, h.bstk, ?_⟩
  · simp [Caches.empty] at hk
  · simp [Caches.empty] at hk
  · exact h.den.mono (LsExt.refl _) rfl rfl (fun k x hk => by simp [Caches.empty] at hk) rfl
      (fun _ _ hv => hv) (fun _ _ _ hv => .inl hv) h.den.lvlAll h.den.lsAll

/-! ### Opening the scratch tier when it is off

With the scratch tier off, a well formed store's scratch tables are empty (`scrOff`), so
`enableScratch` only turns the four flags on: every handle has the view it had, and every
denotation is the one it had. -/

theorem denoteNAux_congr_view {st st' : NStore} (hv : ∀ i, st'.view i = st.view i) :
    ∀ f i, denoteNAux st' f i = denoteNAux st f i
  | 0, _ => rfl
  | f + 1, i => by
    simp only [denoteNAux, hv i]
    congr 1; funext v
    cases v <;> simp only [denoteNAux_congr_view hv f]

theorem denoteLAux_congr_view {st st' : LStore} (hv : ∀ i, st'.view i = st.view i)
    (hn : ∀ i, denoteN st'.ns i = denoteN st.ns i) :
    ∀ f i, denoteLAux st' f i = denoteLAux st f i
  | 0, _ => rfl
  | f + 1, i => by
    simp only [denoteLAux, hv i]
    congr 1; funext v
    cases v <;> simp only [denoteLAux_congr_view hv hn f, hn]

theorem denoteLList_congr {st st' : LStore} (hl : ∀ i, denoteL st' i = denoteL st i) :
    ∀ us, denoteLList st' us = denoteLList st us
  | [] => rfl
  | u :: us => by simp only [denoteLList, hl u, denoteLList_congr hl us]

/-- The four stores' views and node counts after `enableScratch`, from a store with the scratch
tier off and well formed. -/
theorem enable_views {st : EStore} (hwf : StoreWF st) (hoff : st.scratchOn = false) :
    (∀ i, st.enableScratch.view i = st.view i) ∧
    (∀ i, st.enableScratch.lss.view i = st.lss.view i) ∧
    (∀ i, st.enableScratch.ls.view i = st.ls.view i) ∧
    (∀ i, st.enableScratch.ns.view i = st.ns.view i) ∧
    st.enableScratch.ls.nodeCount = st.ls.nodeCount ∧
    st.enableScratch.ns.nodeCount = st.ns.nodeCount := by
  obtain ⟨rk, hw⟩ := hwf
  have hLs : LsWF st.lss := hw.lss
  obtain ⟨rkl, hL⟩ := hLs.ls
  obtain ⟨rkn, hN⟩ := hL.ns
  have o1 : st.lss.scratchOn = false := by rw [← hw.sync]; exact hoff
  have o2 : st.lss.ls.scratchOn = false := by rw [← hLs.sync]; exact o1
  have o3 : st.lss.ls.ns.scratchOn = false := by rw [← hL.sync]; exact o2
  have sE := hw.scrOff hoff
  have sLs := hLs.scrOff o1
  have sL := hL.scrOff o2
  have sN := hN.scrOff o3
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · simp only [EStore.view, EStore.enableScratch, hoff]
    split <;> simp [ETables.get_empty]
  · simp only [EStore.enableScratch, LsStore.view, LsStore.enableScratch, o1]
    split <;> simp [LsTables.get_empty]
  · simp only [EStore.ls, EStore.enableScratch, LsStore.enableScratch, LStore.view,
      LStore.enableScratch, o2]
    split <;> simp [LTables.get_empty]
  · simp only [EStore.ns, EStore.enableScratch, LsStore.enableScratch, LStore.enableScratch,
      NStore.view, NStore.enableScratch, o3]
    split <;> simp [NTables.get_empty]
  · simp only [EStore.ls, EStore.enableScratch, LsStore.enableScratch, LStore.enableScratch,
      LStore.nodeCount, LStore.persCount, LStore.scrCount, sL]
  · simp only [EStore.ns, EStore.enableScratch, LsStore.enableScratch, LStore.enableScratch,
      NStore.enableScratch, NStore.nodeCount, NStore.persCount, NStore.scrCount, sN]

/-- **Opening the scratch tier when it is off changes no denotation.** -/
theorem enable_denote {st : EStore} (hwf : StoreWF st) (hoff : st.scratchOn = false) :
    (∀ i, denoteN st.enableScratch.ns i = denoteN st.ns i) ∧
    (∀ i, denoteL st.enableScratch.ls i = denoteL st.ls i) ∧
    (∀ i, denoteLs st.enableScratch.lss i = denoteLs st.lss i) := by
  obtain ⟨-, hvs, hvl, hvn, hcl, hcn⟩ := enable_views hwf hoff
  have hN : ∀ i, denoteN st.enableScratch.ns i = denoteN st.ns i := fun i => by
    simp only [denoteN, hcn]; exact denoteNAux_congr_view hvn _ i
  have hL : ∀ i, denoteL st.enableScratch.ls i = denoteL st.ls i := fun i => by
    simp only [denoteL, hcl]; exact denoteLAux_congr_view hvl hN _ i
  refine ⟨hN, hL, fun i => ?_⟩
  simp only [denoteLs, hvs i]
  cases st.lss.view i with
  | none => rfl
  | some us => exact denoteLList_congr hL us

/-- **`TwinOK` after `enterScratch`** at a state whose store is well formed with the scratch tier
off (the loop head's: `TwinFold.stateOK`, and the last `dropScratch` turned it off). -/
theorem TwinOK.enter {m : Mem} {a : AState} (h : TwinOK dn m a fe) (hwf : StoreWF a.store)
    (hoff : a.store.scratchOn = false) :
    TwinOK dn m { store := a.store.enableScratch, memos := Memos.empty, caches := a.caches,
      pins := a.pins } fe := by
  obtain ⟨hvE, hvs, hvl, -, -, -⟩ := enable_views hwf hoff
  obtain ⟨hN, hL, hLs⟩ := enable_denote hwf hoff
  have hx : LsExt a.store.lss a.store.enableScratch.lss :=
    ⟨⟨⟨fun i x hd => by rw [show a.store.enableScratch.lss.ls.ns = a.store.enableScratch.ns from rfl,
        hN]; exact hd⟩, fun i x hd => by
        rw [show a.store.enableScratch.lss.ls = a.store.enableScratch.ls from rfl, hL]; exact hd⟩,
      fun i x hd => by rw [hLs]; exact hd⟩
  refine ⟨fun k l hk => ?_, fun k l hk => ?_, ?_, h.erec, h.spn, h.memos, h.bstk, ?_⟩
  · show denoteL a.store.enableScratch.ls k = some l
    rw [hL]; exact h.readL k l hk
  · show denoteLs a.store.enableScratch.lss k = some l
    rw [hLs]; exact h.readLs k l hk
  · obtain ⟨rk, hn⟩ := h.nwf
    exact ⟨rk, NStore.enableScratch_wfAt hn⟩
  · refine h.den.mono hx rfl rfl (fun k x hk => .inl hk) rfl
      (fun x u hv => by rw [← hvE x]; exact hv) (fun x c us hv => .inl (by rw [← hvE x]; exact hv))
      (fun u hu => ?_) (fun u hu => ?_)
    · have hu' : (a.store.ls.view u).isSome := by
        rw [← hvl u]; exact hu
      obtain ⟨l, hl⟩ := h.den.lvlAll u hu'
      exact ⟨l, by show denoteL a.store.enableScratch.ls u = some l; rw [hL]; exact hl⟩
    · have hu' : (a.store.lss.view u).isSome := by
        rw [← hvs u]; exact hu
      obtain ⟨l, hl⟩ := h.den.lsAll u hu'
      exact ⟨l, by show denoteLs a.store.enableScratch.lss u = some l; rw [hLs]; exact hl⟩

end twin

/-! ## The twin's half of `TwinOK` from the fold's invariant

Every part of `TwinOK` that speaks of the twin state alone follows from con-ron's fold invariant
(`FoldOK`, which `TwinFold` carries at every loop head): the readback caches from `CacheOK`, the name
store's well-formedness from `StateOK`, the stored levels' readbacks from the store's
well-formedness (a handle with a view denotes: con-ron's `denoteL_of_view`), the pins' from
`PinsOK`, the environment's level parameters and recursor levels from `IFEnvOK.hit`. What is left
is the memory's half (`TwinMem`: three sizes, the core's memos, the projection-table clause of
`StoreDen`, which reads `EREC`) and the record decoder's agreement with the name store (`dnN`). -/

/-- **The memory's half of `TwinOK`**, and the name decoder's agreement with the store. -/
structure TwinMem (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) : Prop where
  erec : (m.arr64 EREC).size < 2 ^ 63
  spn : (m.arr64 SPN).size < 2 ^ 63
  bstk : (m.arr64 145).size < 2 ^ 63
  memos : CoreMemos m
  proj : ∀ (q : Nat) (tbl : IProjTable), decTbl (m.arr64 EREC) q = some tbl →
    (∃ l, denoteL a.store.ls tbl.structSort = some l) ∧
    (∀ i, i < tbl.numFields → ∃ l, denoteL a.store.ls (tbl.guards.getD i default) = some l) ∧
    (∃ ks, tbl.levelParams.mapM (denoteN a.store.ns) = some ks)
  dnN : ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → denoteN a.store.ns k = some x

theorem denoteNList_mapM {st : NStore} :
    ∀ {l : List NIdx} {xs : List ConLeche.Name}, ConRon.Arena.Frontend.denoteNList st l = some xs →
      l.mapM (denoteN st) = some xs
  | [], xs, h => by simp [ConRon.Arena.Frontend.denoteNList] at h; subst h; rfl
  | c :: cs, xs, h => by
    simp only [ConRon.Arena.Frontend.denoteNList] at h
    cases h1 : denoteN st c with
    | none => rw [h1] at h; simp at h
    | some x =>
      cases h2 : ConRon.Arena.Frontend.denoteNList st cs with
      | none => rw [h1, h2] at h; simp at h
      | some ys =>
        rw [h1, h2] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [List.mapM_cons, h1, denoteNList_mapM h2]

theorem denoteCV_lps {st : EStore} {cv : IConstantVal} {c : ConLeche.ConstantVal}
    (h : ConRon.Arena.Frontend.denoteCV st cv = some c) :
    ∃ ks, cv.levelParams.mapM (denoteN st.ns) = some ks := by
  simp only [ConRon.Arena.Frontend.denoteCV] at h
  cases h2 : ConRon.Arena.Frontend.denoteNList st.ns cv.levelParams with
  | none => rw [h2] at h; split at h <;> simp_all
  | some ks => exact ⟨ks, denoteNList_mapM h2⟩

theorem denoteLList_mem {ls : LStore} :
    ∀ {us : List LIdx} {xs : List ConLeche.Level}, denoteLList ls us = some xs →
      ∀ u ∈ us, ∃ L, denoteL ls u = some L
  | [], _, _, u, hu => absurd hu (by simp)
  | v :: vs, xs, h, u, hu => by
    simp only [denoteLList, opt2_eq_some_iff] at h
    obtain ⟨a, b, ha, hb, -⟩ := h
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨a, ha⟩
    · exact denoteLList_mem hb u hu

theorem denoteRules_mem {st : EStore} :
    ∀ {rs : List IRecRule} {xs : List ConLeche.RecRule},
      ConRon.Arena.Frontend.denoteRules st rs = some xs →
      ∀ r ∈ rs, ∀ lvls pins, r.fire = .nested lvls pins → ∀ u ∈ lvls, ∃ L, denoteL st.ls u = some L
  | [], _, _, r, hr => absurd hr (by simp)
  | q :: qs, xs, h, r, hr, lvls, pins, hf, u, hu => by
    simp only [ConRon.Arena.Frontend.denoteRules] at h
    cases h1 : ConRon.Arena.Frontend.denoteRule st q with
    | none => rw [h1] at h; simp at h
    | some y =>
      cases h2 : ConRon.Arena.Frontend.denoteRules st qs with
      | none => rw [h1, h2] at h; simp at h
      | some ys =>
        rcases List.mem_cons.mp hr with rfl | hr
        · simp only [ConRon.Arena.Frontend.denoteRule, hf, ConRon.Arena.Frontend.denoteFire] at h1
          cases h3 : denoteLList st.ls lvls with
          | none => rw [h3] at h1; split at h1 <;> simp_all
          | some ls => exact denoteLList_mem h3 u hu
        · exact denoteRules_mem h2 r hr lvls pins hf u hu

/-- **`TwinOK` from the fold's invariant** and the memory's half. -/
theorem TwinOK.of_fold {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {fe : IFEnv}
    {env : ConLeche.Env} (hok : ConRon.Bridge.FoldOK .verified env fe a) (hm : TwinMem dn m a) :
    TwinOK dn m a fe := by
  have hwf := hok.check.state.wf
  obtain ⟨rk, hw⟩ := hwf
  have hw' : StoreWF' a.store := StoreWF'.of_wf ⟨rk, hw⟩
  obtain ⟨rk', hw''⟩ := hw'
  have hLs : LsStoreWF' a.store.lss := hw''.lss
  have hL : LStoreWF' a.store.ls := hLs.ls
  have hc := hok.check.caches
  have hp := hok.check.pins
  have hi := hok.check.ienv
  refine ⟨hc.readL, hc.readLs, hw.nsWF, hm.erec, hm.spn, hm.memos, hm.bstk, ?_⟩
  refine ⟨fun x u hv => ?_, fun x c us hv => ?_, ⟨_, hp.zeroLevel⟩, ⟨_, hp.emptyLevels⟩, hc.readN,
    fun c ci cv hf ht hcv => ?_, hm.proj, fun u hu => denoteL_of_view hL hu,
    fun us hus => ?_, hm.dnN, fun c cv mI rP rules hf r hr lvls pins hfi u hu => ?_⟩
  · exact denoteL_of_view hL (hw.lchildOK x _ hv u (by simp [ENodeView.lchildren])).1
  · have hs := (hw.lschildOK x _ hv us (by simp [ENodeView.lschildren])).1
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨xs, hxs⟩ := denoteLs_of_view hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · obtain ⟨-, d, -, hd, -⟩ := hi.hit c ci hf
    cases ci with
    | projInfo t => simp [IConstantInfo.isTowerEntry] at ht
    | axiomInfo v | thmInfo v | defnInfo v _ _ | indInfo v _ | ctorInfo v _ _ | recInfo v _ _ _ =>
      have e := hcv default
      simp only [IConstantInfo.toConstantVal] at e
      cases e
      simp only [ConRon.Arena.Frontend.denoteCI] at hd
      first
        | (cases h1 : ConRon.Arena.Frontend.denoteCV a.store v with
            | none => rw [h1] at hd; first | simp at hd | (split at hd <;> simp_all)
            | some y => exact denoteCV_lps h1)
  · obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hus
    obtain ⟨xs, hxs⟩ := denoteLs_of_view hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · obtain ⟨-, d, -, hd, -⟩ := hi.hit c _ hf
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    cases h2 : ConRon.Arena.Frontend.denoteRules a.store rules with
    | none => rw [h2] at hd; split at hd <;> simp_all
    | some ys => exact denoteRules_mem h2 r hr lvls pins hfi u hu

/-! ## `LoopT` from `LoopR`, the twin's fold invariant and the memory's half -/

/-- **`LoopT` at a loop head**: `LoopR`, the twin's fold invariant (`TwinFold`, lane `decls4`), the
memory's half of `TwinOK` and the pin table's flag. -/
theorem LoopT.of_fold {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m : Mem}
    {a : AState} {vis : Word} {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (hR : LoopR pins dn m a vis fe pend ds) (hT : TwinFold pins ds fe pend a) (hm : TwinMem dn m a)
    (hflag : pinW m 0 ≠ 0) : LoopT pins dn m a vis fe pend ds :=
  let ⟨_, hok, _⟩ := hT.fold
  ⟨hR, TwinOK.of_fold hok hm, hflag⟩

/-! ## `LoopT` across the bracket's L functions -/

theorem pinW_frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hP : PINS ∉ A) : pinW m' 0 = pinW m 0 := by
  simp only [pinW, hf.1 PINS hP (by decide)]

section bracket
variable (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration) (p : Prog)
  (hb : BracketProg p)
include hb

/-- **`flush_caches` keeps `LoopT`.** -/
theorem flush_loopT {pins : List INatOpPinSet} (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word)
    (fe : IFEnv) (pend : Array PendingCheck) (hR : LoopT pins dn s₀.mem a₀ vis fe pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "flush_caches" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok flushCaches a₀ ∧
      LoopT pins dn s'.mem (AM.st flushCaches a₀) vis fe pend ds; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hL⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (flush_loop dn ds p hb n s₀ a₀ vis fe pend hR.loop)
  obtain ⟨-, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun (flushCaches_spec p hb.fl n s₀)
  subst hs
  have hf : MemFrame [] flushCtl s.mem s'.mem := by rw [hm]; exact flushMem_frame _
  refine ⟨hloc, hok, hL, ?_, by rw [pinW_frame hf (by simp)]; exact hR.flag⟩
  rw [flushCaches_st]
  exact (hR.twin.frameLo hf flushCtl_lt (by simp [flushCtl]) (by simp [flushCtl])).flush

/-- **`scratch_enter` keeps `LoopT`** from a loop head (the store well formed, the scratch tier
off): the twin's `enterScratch` then changes no denotation. -/
theorem enter_loopT {pins : List INatOpPinSet} (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word)
    (fe : IFEnv) (pend : Array PendingCheck) (hR : LoopT pins dn s₀.mem a₀ vis fe pend ds)
    (hwf : StoreWF a₀.store) (hoff : a₀.store.scratchOn = false) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "scratch_enter" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok enterScratch a₀ ∧
      LoopT pins dn s'.mem (AM.st enterScratch a₀) vis fe pend ds; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hL⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (enter_loop dn ds p hb n s₀ a₀ vis fe pend hR.loop)
  obtain ⟨-, -, -, -, -, -, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchEnter_spec p hb.se hb.sr hb.bm hb.lf hb.im hb.fm n s₀)
  subst hs
  have hf : MemFrame [] (resetCtl ++ memoCtl) s.mem s'.mem := by rw [hm]; exact enterMem_frame _
  refine ⟨hloc, hok, hL, ?_, by rw [pinW_frame hf (by simp)]; exact hR.flag⟩
  rw [enterScratch_st]
  exact (hR.twin.frameLo hf (fun x h => Nat.lt_trans (resetCtl_lt x h) (by decide))
    (by simp [resetCtl, scratchCnts, memoCtl, SCB]) (by simp [resetCtl, scratchCnts, memoCtl, SCB])).enter
    hwf hoff

end bracket

/-- **Pushing a pending check keeps `LoopT`.** -/
theorem LoopT.pendPush {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m : Mem}
    {a : AState} {vis : Word} {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (h : LoopT pins dn m a vis fe pend ds) (g i v : Word) (vg : ValueGroup)
    (hg : decVG (erecP m) g.toNat = some vg)
    (hb : 3 * (rdW (m.arr64 CTL) 130).toNat + 2 < (m.arr64 PEND).size)
    (hc : 130 < (m.arr64 CTL).size) (h1 : (rdW (m.arr64 CTL) 130).toNat < 2 ^ 62) :
    LoopT pins dn (pendPushMem m g i v) a vis fe (pend.push ⟨vg, i.toNat, v.toNat⟩) ds := by
  have hf := pendPushMem_frame m g i v
  exact ⟨h.loop.pendPush g i v vg hg hb hc h1,
    h.twin.frame hf (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩,
    by rw [pinW_frame hf (by decide)]; exact h.flag⟩

/-- **`TwinOK` at a smaller view** (phase B checks a group at the view it was installed at): a hit of
the restricted environment is a hit of the whole one. -/
theorem TwinOK.restrict {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {fe : IFEnv}
    (h : TwinOK dn m a fe) {k : Nat} (hk : k ≤ fe.visibleBelow) : TwinOK dn m a (fe.restrictTo k) :=
  ⟨h.readL, h.readLs, h.nwf, h.erec, h.spn, h.memos, h.bstk,
    { h.den with
      constLps := fun c ci cv hf => h.den.constLps c ci cv (IFEnv.restrictTo_find?_le hk hf)
      recRules := fun c cv mI rP rules hf => h.den.recRules c cv mI rP rules
        (IFEnv.restrictTo_find?_le hk hf) }⟩

/-- **`LoopT` at a smaller view.** -/
theorem LoopT.restrict {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m : Mem}
    {a : AState} {vis : Word} {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (h : LoopT pins dn m a vis fe pend ds) (v : Word) (hv : v.toNat ≤ vis.toNat) :
    LoopT pins dn m a v (fe.restrictTo v.toNat) pend ds :=
  ⟨h.loop.restrict v, h.twin.restrict (by rw [h.loop.vis]; exact hv), h.flag⟩

end L.Arena
