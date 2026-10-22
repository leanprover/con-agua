import ConAgua.Arena.Checker
import ConAgua.Arena.IndTwin
import ConRon.Bridge.Promote.Walk
import ConAgua.Arena.IndPosMemo
import ConAgua.Arena.IndPos2SpecB
import ConAgua.Arena.RecCheckSpec7

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

/-! ## The inductive stage's per-call memos (a memory-only clause)

The stage's walks clear their memos on entry by an epoch bump (`mclearG`), whose lemma
(`memoRV_clear`) needs *some* well-formed memo beforehand and the epoch word below `2^64 − 2`.
`StageMemos m` says that of the eight stage memos (arrays 201‥208, `CTL` 202‥219): `nest_occ`,
`depth`, `replace_apps`, `has_loose_bvar_b`, the banked `replace_fvars` (`PosMR`), `mentions_any`
(`maMR`), `mentions_const` (`mcMR`), `target_abs` (`taMR`), and the epoch bound. Only the stage
writes these words (request of lane `indproofs3`), so across the loop it is a frame fact
(`StageMemos.frame`), and it holds of the zeroed memory (`StageMemos.zero`). -/

/-- The stage memos' epoch words. -/
def stageEpochs : List Word := [202, 204, 206, 208, 210, 212, 214, 216]

/-- **The inductive stage's per-call memos are well formed**, their epochs bounded. -/
structure StageMemos (m : Mem) : Prop where
  pos : PosMR m
  ma : ∃ mp, maMR m mp
  mc : ∃ mp, mcMR m mp
  ta : ∃ mp, taMR m mp
  ep : ∀ x ∈ stageEpochs, rdW (m.arr64 CTL) x + 2 ≠ 0

theorem memoRG_mfr0 {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} (hS : S.WF) {K : MemoKey κ}
    {dv : Word → ν} {m m' : Mem} (hf : MFr [] [] m m') (hb : 201 ≤ S.arr ∧ S.arr ≤ 208)
    (hx : 202 ≤ S.cs.toNat ∧ S.cs.toNat ≤ 219) {mp : Std.HashMap κ ν} (h : MemoRG S K dv m mp) :
    MemoRG S K dv m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := hf.memo S.arr S.cs hb hx (by simp) (by simp)
  exact memoRG_frame S hS K dv A C hA hC m m' f mp h

/-- **`StageMemos` across a writer outside arrays 201‥208 and `CTL` 202‥219.** -/
theorem StageMemos.frame {A : List ArrId} {C : List Word} {m m' : Mem} (h : StageMemos m)
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b < 201 ∨ 208 < b)
    (hC : ∀ x ∈ C, x.toNat < 202 ∨ 219 < x.toNat) : StageMemos m' := by
  have hM : MFr [] [] m m' := MFr.of_frame hf hA hC
  obtain ⟨hp, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, he⟩ := h
  refine ⟨hp.fr hM, ⟨a, memoRG_mfr0 maSch_wf hM (by decide) (by decide) ha⟩,
    ⟨b, memoRG_mfr0 mcSch_wf hM (by decide) (by decide) hb⟩,
    ⟨c, memoRG_mfr0 taSch_wf hM (by decide) (by decide) hc⟩, fun x hx => ?_⟩
  have hx' : x ∉ C := fun h' => by
    have := hC x h'; simp [stageEpochs] at hx; rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp at this
  rw [hf.2.1 x hx']; exact he x hx

/-- A memo whose stamps are all `0` at epoch word `0` is the empty memo. -/
theorem memoRV_zeroAt {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
    (S : MemoSch) (K : MemoKey κ) (VR : Mem → Word → ν → Prop) (m : Mem)
    (hctl : S.cs.toNat + 2 ≤ (m.arr64 CTL).size) (he : rdW (m.arr64 CTL) S.cs = 0)
    (hz : ∀ j, rdW (m.arr64 S.arr) j = 0) : MemoRV S K VR m (∅ : Std.HashMap κ ν) := by
  have hep : epG S m = 1 := by simp [epG, he]
  have hst : ∀ j, mstG S m j = 0 := fun j => hz _
  refine ⟨hctl, (by rw [hep]; decide), (fun j _ => by rw [hst, hep]; decide),
    (fun j _ h => by rw [hst, hep] at h; cases h), (fun j j' _ _ h => by rw [hst, hep] at h; cases h),
    (fun x v h => by simp at h)⟩

/-- **The zeroed memory has well-formed stage memos** (empty, epoch `0`). -/
theorem StageMemos.zero {m : Mem} (hsz : 220 ≤ (m.arr64 CTL).size)
    (hA : ∀ b : ArrId, 201 ≤ b → b ≤ 208 → ∀ j, rdW (m.arr64 b) j = 0)
    (hC : ∀ x : Word, 202 ≤ x.toNat → x.toNat ≤ 219 → rdW (m.arr64 CTL) x = 0) : StageMemos m := by
  have z : ∀ (S : MemoSch), 201 ≤ S.arr → S.arr ≤ 208 → 202 ≤ S.cs.toNat → S.cs.toNat ≤ 217 →
      ∀ {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ] (K : MemoKey κ)
        (VR : Mem → Word → ν → Prop), MemoRV S K VR m (∅ : Std.HashMap κ ν) :=
    fun S h1 h2 h3 h4 _ _ _ _ _ _ K VR =>
      memoRV_zeroAt S K VR m (by omega) (hC _ h3 (by omega)) (hA _ h1 h2)
  refine ⟨⟨⟨_, z noSch (by decide) (by decide) (by decide) (by decide) _ _⟩,
      ⟨_, z dpSch (by decide) (by decide) (by decide) (by decide) _ _⟩,
      ⟨_, z raSch (by decide) (by decide) (by decide) (by decide) _ _⟩,
      ⟨_, z hbSch (by decide) (by decide) (by decide) (by decide) _ _⟩,
      ⟨∅, 0, 0, z rfSch (by decide) (by decide) (by decide) (by decide) _ _,
        ⟨hC 218 (by decide) (by decide), hC 219 (by decide) (by decide), by decide, by decide,
          by simp; omega⟩, fun _ _ _ h => by simp at h⟩⟩,
    ⟨_, z maSch (by decide) (by decide) (by decide) (by decide) _ _⟩,
    ⟨_, z mcSch (by decide) (by decide) (by decide) (by decide) _ _⟩,
    ⟨_, z taSch (by decide) (by decide) (by decide) (by decide) _ _⟩, fun x hx => ?_⟩
  have : rdW (m.arr64 CTL) x = 0 := by
    simp [stageEpochs] at hx; rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact hC _ (by decide) (by decide)
  rw [this]; decide

/-! ## The relation -/

/-- **The declaration loop's relation with the core's invariants**: `LoopR`, the twin's invariants
`TwinOK` at the loop's environment, and the pin table's flag. -/
structure LoopT (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState)
    (vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (ds : Array IDeclaration) : Prop where
  loop : LoopR pins dn m a vis fe pend ds
  twin : TwinOK dn m a fe
  flag : pinW m 0 ≠ 0
  /-- The inductive stage's per-call memos (lane `indproofs3`'s request). -/
  memo : StageMemos m

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

/-- **`TwinOK` across a writer** that leaves `EREC` and the core memos (arrays 49, 50, 52‥54,
151‥153, `CTL` 48, 50, 54, 56, 58, 152, 154, 156) alone; the twin state unchanged. -/
theorem TwinOK.frame {A : List ArrId} {C : List Word} {m m' : Mem} {a : AState}
    (hf : MemFrame A C m m') (hE : EREC ∉ A) (hA : (50 : ArrId) ∉ A ∧ (49 : ArrId) ∉ A)
    (hC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C)
    (hWA : (151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A)
    (hWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C)
    (hLA : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A)
    (hLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C)
    (h : TwinOK dn m a fe) : TwinOK dn m' a fe :=
  ⟨h.readL, h.readLs, h.nwf, by rw [hf.2.2.1]; exact h.erec, by rw [hf.2.2.1]; exact h.spn,
    h.memos.frame hf hA hC hWA hWC hLA hLC, by rw [hf.2.2.1]; exact h.bstk,
    h.den.frameE (hf.1 EREC hE (by decide))⟩

/-- `TwinOK` across a writer of `CTL` words below 48 or in 60‥127 only (the bracket's). -/
theorem TwinOK.frameLo {C : List Word} {m m' : Mem} {a : AState} (hf : MemFrame [] C m m')
    (hC : ∀ x ∈ C, x.toNat < 48 ∨ (60 ≤ x.toNat ∧ x.toNat < 128))
    (h : TwinOK dn m a fe) : TwinOK dn m' a fe := by
  have n : ∀ k : Word, 48 ≤ k.toNat → k.toNat < 60 ∨ 128 ≤ k.toNat → k ∉ C := fun k h1 h2 hk => by
    have := hC k hk; omega
  exact h.frame hf (by simp) ⟨by simp, by simp⟩ ⟨n 50 (by decide) (by decide), n 48 (by decide) (by decide)⟩
    ⟨by simp, by simp, by simp⟩
    ⟨n 152 (by decide) (by decide), n 154 (by decide) (by decide), n 156 (by decide) (by decide)⟩
    ⟨by simp, by simp, by simp⟩
    ⟨n 54 (by decide) (by decide), n 56 (by decide) (by decide), n 58 (by decide) (by decide)⟩

end frames

/-! ## The twin's side of the bracket's opening -/

section twin
variable {dn : NIdx → Option ConLeche.Name} {fe : IFEnv}

/-- The twin state after `flushCaches`. -/
theorem flushCaches_st (a : AState) : AM.st flushCaches a = { a with caches := Caches.empty } := rfl

/-- The twin state after `enterScratch`. -/
theorem enterScratch_st (a : AState) :
    AM.st enterScratch a = { a with store := a.store.enableScratch, memos := Memos.empty } := rfl

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
    TwinOK dn m { a with store := a.store.enableScratch, memos := Memos.empty } fe := by
  obtain ⟨hvE, hvs, hvl, -, -, -⟩ := enable_views hwf hoff
  obtain ⟨hN, hL, hLs⟩ := enable_denote hwf hoff
  have hx : LsExt a.store.lss a.store.enableScratch.lss :=
    { ls := { ns := fun i x hd => by
                show denoteN a.store.enableScratch.ns i = some x
                rw [hN]; exact hd
              lvl := fun i x hd => by
                show denoteL a.store.enableScratch.ls i = some x
                rw [hL]; exact hd }
      lst := fun i x hd => by rw [hLs]; exact hd }
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
  | [], _, _, r, hr, _, _, _, _, _ => absurd hr (by simp)
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

theorem denoteCI_cv {st : EStore} {ci : IConstantInfo} {d : ConLeche.ConstantInfo}
    {cv : IConstantVal} {a : AState} (ht : ci.isTowerEntry = false)
    (hd : ConRon.Arena.Frontend.denoteCI st ci = some d)
    (hcv : ci.toConstantVal.run a = .ok (cv, a)) :
    ∃ y, ConRon.Arena.Frontend.denoteCV st cv = some y := by
  have key : ∀ v : IConstantVal, ci.toConstantVal.run a = .ok (v, a) → cv = v := fun v e => by
    rw [hcv] at e; cases e; rfl
  cases ci with
  | projInfo t => simp [IConstantInfo.isTowerEntry] at ht
  | axiomInfo v =>
    obtain rfl := key v rfl
    simp only [ConRon.Arena.Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨y, hy, -⟩ := hd; exact ⟨y, hy⟩
  | thmInfo v =>
    obtain rfl := key v rfl
    simp only [ConRon.Arena.Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨y, hy, -⟩ := hd; exact ⟨y, hy⟩
  | ctorInfo v _ _ =>
    obtain rfl := key v rfl
    simp only [ConRon.Arena.Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨y, hy, -⟩ := hd; exact ⟨y, hy⟩
  | defnInfo v _ _ =>
    obtain rfl := key v rfl
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    split at hd
    · rename_i y _ hy _; exact ⟨y, hy⟩
    · cases hd
  | indInfo v _ =>
    obtain rfl := key v rfl
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    split at hd
    · rename_i y _ hy _; exact ⟨y, hy⟩
    · cases hd
  | recInfo v _ _ _ =>
    obtain rfl := key v rfl
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    split at hd
    · rename_i y _ hy _; exact ⟨y, hy⟩
    · cases hd

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
    fun c ci cv hf ht hcv => ?_, hm.proj, fun u hu => ConRon.Bridge.denoteL_of_view hL hu,
    fun us hus => ?_, hm.dnN, fun c cv mI rP rules hf r hr lvls pins hfi u hu => ?_⟩
  · exact ConRon.Bridge.denoteL_of_view hL (hw.lchildOK x _ hv u (by simp [ENodeView.lchildren])).1
  · have hs := (hw.lschildOK x _ hv us (by simp [ENodeView.lschildren])).1
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨xs, hxs⟩ := ConRon.Bridge.denoteLs_of_view hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · obtain ⟨-, d, -, hd, -⟩ := hi.hit c ci hf
    obtain ⟨y, hy⟩ := denoteCI_cv ht hd (hcv a)
    exact denoteCV_lps hy
  · obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hus
    obtain ⟨xs, hxs⟩ := ConRon.Bridge.denoteLs_of_view hLs hvs
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
    (hflag : pinW m 0 ≠ 0) (hmemo : StageMemos m) : LoopT pins dn m a vis fe pend ds :=
  let ⟨_, hok, _⟩ := hT.fold
  ⟨hR, TwinOK.of_fold hok hm, hflag, hmemo⟩

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
  refine ⟨hloc, hok, hL, ?_, by rw [pinW_frame hf (by simp)]; exact hR.flag,
    hR.memo.frame hf (by simp) (fun x h => .inl (by
      simp [flushCtl] at h; rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide))⟩
  rw [flushCaches_st]
  exact (hR.twin.frameLo hf (fun x h => by simp [flushCtl] at h; rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)).flush

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
  refine ⟨hloc, hok, hL, ?_, by rw [pinW_frame hf (by simp)]; exact hR.flag,
    hR.memo.frame hf (by simp) (fun x h => .inl (Nat.lt_trans (resetCtl_lt x h) (by decide)))⟩
  rw [enterScratch_st]
  exact (hR.twin.frameLo hf (fun x h => by
    simp [resetCtl, scratchCnts, memoCtl, SCB] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      <;> decide)).enter hwf hoff

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
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩,
    by rw [pinW_frame hf (by decide)]; exact h.flag,
    h.memo.frame hf (by simp [PEND]) (by simp)⟩

/-- **`TwinOK` at a smaller view** (phase B checks a group at the view it was installed at): a hit of
the restricted environment is a hit of the whole one. -/
theorem TwinOK.restrict {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {fe : IFEnv}
    (h : TwinOK dn m a fe) {k : Nat} (hk : k ≤ fe.visibleBelow) : TwinOK dn m a (fe.restrictTo k) :=
  ⟨h.readL, h.readLs, h.nwf, h.erec, h.spn, h.memos, h.bstk,
    { h.den with
      constLps := fun c ci cv hf => h.den.constLps c ci cv (ConRon.Bridge.IFEnv.restrictTo_find?_le hk hf)
      recRules := fun c cv mI rP rules hf => h.den.recRules c cv mI rP rules
        (ConRon.Bridge.IFEnv.restrictTo_find?_le hk hf) }⟩

/-- **`LoopT` at a smaller view.** -/
theorem LoopT.restrict {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m : Mem}
    {a : AState} {vis : Word} {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (h : LoopT pins dn m a vis fe pend ds) (v : Word) (hv : v.toNat ≤ vis.toNat) :
    LoopT pins dn m a v (fe.restrictTo v.toNat) pend ds :=
  ⟨h.loop.restrict v, h.twin.restrict (by rw [h.loop.vis]; exact hv), h.flag, h.memo⟩

/-! ## A core call keeps `LoopT`

The core's write set from the program text, at the loop's granularity: no function the stage's
core entry points reach writes the pools, the pins, nor anything the loop keeps beside the stage
(the pending checks, the declaration records, the promotion memos, `CTL[130]`, `CTL[140‥147]`,
the pin variants' header `CTL[150]`, `CTL[151]`). Decided for the checker's program in
`ConAgua/Checker/LoopCore.lean`. A core call starts and ends in `CoreS` and writes no `EREC`, so
`TwinOK` (the projection clause included) comes back with it. -/

/-- The arrays a core function may write, at the loop's granularity. -/
def coreLoopA : List ArrId :=
  stepA.filter fun b => b ≠ EREC ∧ b ≠ IW ∧ b ≠ PINS ∧ (b < 201 ∨ 208 < b)

/-- The `CTL` words a core function may write, at the loop's granularity. -/
def coreLoopC : List Word :=
  stepC.filter fun x => x ≠ 129 ∧ x ≠ 200 ∧ (x.toNat < 202 ∨ 219 < x.toNat)

/-- **The program hypothesis**: the core leaves the loop's state alone. -/
def CoreLoopClosed (p : Prog) : Prop := closedA p coreLoopA coreLoopC stageCoreFns = true

theorem coreLoopA_erec : EREC ∉ coreLoopA := by simp [coreLoopA]
theorem coreLoopA_iw : IW ∉ coreLoopA := by simp [coreLoopA]
theorem coreLoopA_pins : PINS ∉ coreLoopA := by simp [coreLoopA]
theorem coreLoopC_129 : (129 : Word) ∉ coreLoopC := by simp [coreLoopC]
theorem coreLoopC_200 : (200 : Word) ∉ coreLoopC := by simp [coreLoopC]

/-- **After a core call**: the core's own post (`CoreS` after) and its write set give `LoopT` after
(the same view, environment, pending checks and records), the pools unchanged. -/
theorem LoopT.of_core {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration} {p : Prog}
    (hcl : CoreLoopClosed p) {f : FnName} (hf : f ∈ stageCoreFns) {n : Nat} {vs : List Word}
    {m m' : Mem} {r : List Word} {a a' : AState} {M : ModeMaps}
    (h : callW p n f vs m = some (r, m')) (hL : LoopT pins dn m a vis fe pend ds)
    (hC : CoreS dn m' a' vis fe M 0) : LoopT pins dn m' a' vis fe pend ds ∧ IWGrow m m' := by
  obtain ⟨hfr, -⟩ := run_memFrame hcl hf (run_of_callW h)
  have hI : m'.arr64 IW = m.arr64 IW := hfr.1 _ coreLoopA_iw (by decide)
  have hE : m'.arr64 EREC = m.arr64 EREC := hfr.1 _ coreLoopA_erec (by decide)
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hfr.2.1 _ coreLoopC_129
  have h200 : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hfr.2.1 _ coreLoopC_200
  obtain ⟨hCR, hT⟩ := hC.checkR
  have hS : StageR dn vis fe m' a' :=
    ⟨hCR, IWOK.frame hfr coreLoopA_iw coreLoopA_erec coreLoopC_129 coreLoopC_200 hL.loop.iw⟩
  have hst : MemFrame stepA stepC m m' :=
    hfr.mono (fun b hb => (List.mem_filter.mp hb).1) (fun x hx => (List.mem_filter.mp hx).1)
  refine ⟨⟨hL.loop.of_step hS hst (by rw [erecP_congr hE h129]; exact ArrExt.refl _), hT,
    by rw [pinW_frame hfr coreLoopA_pins]; exact hL.flag,
    hL.memo.frame hfr (fun b hb => (List.mem_filter.mp hb).2 |> fun h => by simp at h; exact h.2.2.2)
      (fun x hx => (List.mem_filter.mp hx).2 |> fun h => by simp at h; exact h.2.2)⟩, ?_⟩
  exact ⟨by simp [iwTop, h200], by simp [erTop, h129], fun i _ => by rw [hI], fun i _ => by rw [hE]⟩

/-- **A core entry point's refinement as a `Sim` under `LoopT`** (the loop-level twin of
`StageT.sim_core`). -/
theorem LoopT.sim_core {α : Type} [Inhabited α] {pins : List INatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {pend : Array PendingCheck}
    {ds : Array IDeclaration} {p : Prog} (hcl : CoreLoopClosed p) {f : FnName}
    (hf : f ∈ stageCoreFns) {n : Nat} {args : List Word} {T : AM α} {dec : List Word → α}
    {m : Mem} {a : AState} (hL : LoopT pins dn m a vis fe pend ds)
    (hspec : ∀ (s₀ : St) (M : ModeMaps), CoreS dn s₀.mem a vis fe M 0 →
      CoreSpec p n f args T dec s₀ a dn vis fe M 0) :
    Sim (callW p n f args m) T a (fun r x m' a' => LoopT pins dn m' a' vis fe pend ds ∧
      IWGrow m m' ∧ dec r = x ∧ ResH r) := by
  intro r m' e
  obtain ⟨M, hC⟩ := hL.core
  obtain ⟨s', rfl, -, hok, ⟨M', hC', -, -⟩, hres, hrh⟩ :=
    triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (hspec ⟨m, Locals.init []⟩ M hC) e
  obtain ⟨hT', hg⟩ := LoopT.of_core hcl hf e hL hC'
  exact ⟨_, _, partsRunOfOk hok, hT', hg, hres.symm, hrh⟩

/-! ### The entry points under `LoopT` -/

section entryL
variable (p : Prog) (hp : KnotEntryProg p) (hw : p.lookup "whnf_top" = some whnfTopL)
  (hK : ∀ n, KnotOK p n) (hcl : CoreLoopClosed p)
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {pend : Array PendingCheck} {ds : Array IDeclaration}

include hw hK hcl in
/-- **`whnf_top` under `LoopT`.** -/
theorem whnfTop_simL (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hL : LoopT pins dn m a vis fe pend ds) (dep e : Word) (he : H e) :
    Sim (callW p n "whnf_top" [vis, dep, e] m) (whnf .verified fe checkFuel dep.toNat (decI e)) a
      (fun r x m' a' => LoopT pins dn m' a' vis fe pend ds ∧ IWGrow m m' ∧ decW0E m' r x) := by
  rcases n with _ | k
  · intro r m' h; rw [callW_zero] at h; cases h
  refine Sim.mono (LoopT.sim_core hcl (by simp [stageCoreFns]) hL
    (fun s₀ M hC => whnfTop_core p hw hK k hn checkFuel (stage_fuel hn) s₀ a M dep e hC (hw_of_h he))) ?_
  rintro r x m' a' ⟨hT, hg, hd, hr⟩
  exact ⟨hT, hg, hr, by rw [← hd]; rfl⟩

include hp hK hcl in
/-- **`infer_type_core` under `LoopT`.** -/
theorem inferTypeCore_simL (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hL : LoopT pins dn m a vis fe pend ds) (dep e : Word) (he : H e) :
    Sim (callW p n "infer_type_core" [vis, dep, e] m)
      (inferTypeCore .verified fe checkFuel dep.toNat (decI e)) a
      (fun r x m' a' => LoopT pins dn m' a' vis fe pend ds ∧ IWGrow m m' ∧ decW0E m' r x) := by
  rcases n with _ | k
  · intro r m' h; rw [callW_zero] at h; cases h
  refine Sim.mono (LoopT.sim_core hcl (by simp [stageCoreFns]) hL
    (fun s₀ M hC => inferTypeCore_core p hp hK k hn checkFuel (stage_fuel hn) s₀ a M dep e hC
      (hw_of_h he))) ?_
  rintro r x m' a' ⟨hT, hg, hd, hr⟩
  exact ⟨hT, hg, hr, by rw [← hd]; rfl⟩

include hp hK hcl in
/-- **`is_def_eq_core` under `LoopT`.** -/
theorem isDefEqCore_simL (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hL : LoopT pins dn m a vis fe pend ds) (dep x y : Word) (hx : H x) (hy : H y) :
    Sim (callW p n "is_def_eq_core" [vis, dep, x, y] m)
      (isDefEqCore .verified fe checkFuel dep.toNat (decI x) (decI y)) a
      (fun r b m' a' => LoopT pins dn m' a' vis fe pend ds ∧ IWGrow m m' ∧ decBool r = b) := by
  rcases n with _ | k
  · intro r m' h; rw [callW_zero] at h; cases h
  refine Sim.mono (LoopT.sim_core (dec := decBool) hcl (by simp [stageCoreFns]) hL
    (fun s₀ M hC => isDefEqCore_refines p hp k (hK k).defeq checkFuel s₀ a dn vis fe M dep x y
      (stage_fuel hn) (by omega) hC (hw_of_h hx) (hw_of_h hy))) ?_
  rintro r b m' a' ⟨hT, hg, hd, -⟩
  exact ⟨hT, hg, hd⟩

include hp hK hcl in
/-- **`ensure_sort_core` under `LoopT`.** -/
theorem ensureSortCore_simL (hl : InferLeafProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem}
    {a : AState} (hL : LoopT pins dn m a vis fe pend ds) (dep t : Word) (ht : H t) :
    Sim (callW p n "ensure_sort_core" [vis, dep, t] m)
      (ensureSortCore .verified fe checkFuel dep.toNat (decI t)) a
      (fun r x m' a' => LoopT pins dn m' a' vis fe pend ds ∧ IWGrow m m' ∧ decW0L m' r x) := by
  rcases n with _ | _ | k
  · intro r m' h; rw [callW_zero] at h; cases h
  · intro r m' h
    obtain ⟨s', -, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (L.Arena.ensureSortCore_spec p hp 0 _ vis dep t) h
    simp [call1W, callW_zero] at hW
  refine Sim.mono (LoopT.sim_core hcl (by simp [stageCoreFns]) hL
    (fun s₀ M hC => ensureSortCore_refines p hl hp k (fun j _ => hK j) checkFuel s₀ a dn vis fe M
      dep t (stage_fuel (by omega)) (by omega) hC (hw_of_h ht))) ?_
  rintro r x m' a' ⟨hT, hg, hd, hr⟩
  exact ⟨hT, hg, hr, by rw [← hd]; rfl⟩

include hcl in
/-- **`lvl_eq_c` under `LoopT`**: the two handles' readbacks are the caller's (`StoreDen.lvlAll`,
`StoreDen.zero` of `hL.twin.den`). -/
theorem lvlEqC_simL (hL' : LvlCacheProg p) (hpc : p.lookup "lvl_eq_c" = some lvlEqCL) (n : Nat)
    {m : Mem} {a : AState} (hL : LoopT pins dn m a vis fe pend ds) (u v : Word) (hu : H u)
    (hv : H v) (lu lv : ConLeche.Level) (hdu : denoteL a.store.ls (decI u) = some lu)
    (hdv : denoteL a.store.ls (decI v) = some lv) :
    Sim (callW p n "lvl_eq_c" [u, v] m) (lvlEq? (decI u) (decI v)) a
      (fun r x m' a' => LoopT pins dn m' a' vis fe pend ds ∧ IWGrow m m' ∧
        decO (r.headD 0) = x ∧ H (r.headD 0)) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · intro r m' h; rw [lvlEqC_small p hpc n hn] at h; cases h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact Sim.mono (LoopT.sim_core hcl (by simp [stageCoreFns]) hL
    (fun s₀ M hC => lvlEqC_refines p hL' k s₀ a dn vis fe M 0 hC u v hu hv lu lv hdu hdv))
    fun r x m' a' ⟨hT, hg, hd, hr⟩ => ⟨hT, hg, hd, hr⟩

end entryL

end L.Arena
