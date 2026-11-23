module

public import ConAgua.Arena.IndexBuild
public import ConRon.Bridge.Checker.Pooled
public import ConRon.Bridge.Compare.Record
public import ConAgua.Arena.JustifyRef7
public import ConAgua.Arena.CmpVMates
import ConAgua.Census.Attr
import ConAgua.Arena.RefWalk
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.CheckerL

@[expose] public section

/-!
# The jobs: `record_job`, `check_jobs`

con-ron #143: every record's check is a job at the stream index's view of its position
(`recordJob`, `Arena/StreamIndex.lean`), a worker runs its jobs in order (`checkJobList`,
`Arena/Checker.lean`).

* `TwinOK.of_check` (`TwinStep.lean`): the twin's invariants `TwinOK` at an environment from con-ron's `CheckOK`
  there and the memory's half (`TwinMem`); a job's start has `CheckOK` at its view from
  `FoldOK` (con-ron's `view_foldOK`).
* `JobR`: what a worker's memory keeps between two jobs (the checker state without an
  environment: the stream index `IndexR`, the own rows below the stamp `OwnBelow`, the record
  pool's tier 1 empty).
* `recordJob_ref`: `record_job(k)` refines `recordJob` of record `k`, both outcomes, from `JobR`
  and `FoldOK` at the view of `k` (con-ron's `RecordSpec` takes the same).
* `checkJobs_ref`: `check_jobs(j, hi)` over the jobs `j‥hi - 1`, as a chain of jobs that each
  refine `recordJob` where `FoldOK` holds at their view: con-ron's `pooled_fold` turns such a
  chain into the pure fold's accept (the set theory supplies `FoldOK`, `view_foldOK`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

/-! ## `TwinOK` from con-ron's check invariant -/

/-- A level list whose members have views reads back. -/
theorem denoteLList_some {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) :
    ∀ (us : List LIdx), (∀ u ∈ us, (st.view u).isSome = true) → ∃ xs, denoteLList st us = some xs
  | [], _ => ⟨[], rfl⟩
  | u :: us, hu => by
    obtain ⟨x, hx⟩ := L.Arena.denoteL_of_viewR h _ u (Nat.lt_succ_self _) (hu u (by simp))
    obtain ⟨xs, hxs⟩ := denoteLList_some h us (fun v hv => hu v (by simp [hv]))
    exact ⟨x :: xs, by simp [denoteLList, hx, hxs, opt2]⟩

/-! ## `record_job`'s model -/

/-- **`record_job`'s unified model**: every callee through its run (the bracket and the leaves are
outside the verdict closure; `check_decl` is read through its run so that its write set applies to
the model's memory). -/
l_model recordJob_specE (p : Prog) (hf : p.lookup "record_job" = some recordJobL)
  fns [hf ↦ recordJobE]
  grind [arena_grind]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`check_jobs`' unified model**. -/
l_model checkJobs_specE (p : Prog) (hf : p.lookup "check_jobs" = some checkJobsL)
  fns [hf ↦ checkJobsE]
  grind [arena_grind]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  unified

/-! ## The run's solution in a job's memory -/

/-- **`SolR` across a frame whose record pool extends** (`SolR.growF` with the pool's extension
given as `ArrExt` of `erecP`: a job's frames empty tier 1 again, `JobM.ofDrop`). -/
theorem SolR.frameX {A : List TieredArray} {C : List Word} {m m' : Mem} {J : ISolution}
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b ∉ solArrs) (hC : ∀ x ∈ C, x ∉ solCtl)
    (hx : ArrExt (erecP m) (erecP m')) (h : SolR m J) : SolR m' J := by
  have he : ∀ b ∈ solArrs, m'.arr64 b = m.arr64 b := fun b hb =>
    hf.arr b (fun hm => hA b hm hb) (fun e => by subst e; revert hb; decide)
  have hc : ∀ x ∈ solCtl, rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x := fun x hx =>
    hf.ctl x (fun hm => hC x hm hx)
  have hr : ∀ w, solRow m' w = solRow m w := fun w => by simp only [solRow, he _ (six_mem _)]
  have ht : ∀ w, solTbl m' w = solTbl m w := fun w => by simp only [solTbl, he _ (stx_mem _)]
  have hm : ∀ w, matRow m' w = matRow m w := fun w => by simp only [matRow, he _ (mat_mem _)]
  have hl : ∀ w, matList m' w = matList m w := fun w => by
    unfold matList
    rw [hm]
    split
    · rfl
    · rename_i c
      obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp (h.mates_dec w c)
      unfold matList at hxs; simp only [c, ite_false] at hxs
      rw [hxs, hx.hslice? hxs]
  refine ⟨fun n => ?_, fun n => ?_, ?_, ?_, fun n => by rw [h.mates n, hl], fun w hw => ?_,
    fun w => by rw [hr, ht]; exact h.rows w⟩
  · have := h.base n; rw [hr]
    rw [this]; split
    · rfl
    · cases e : J.idx.base.idx[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_eq_right_of_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decCI this.2.symm]
  · have := h.btbl n; rw [ht]
    rw [this]; split
    · rfl
    · cases e : J.idx.base.tbls[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_eq_right_of_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decTbl this.2.symm]
  · rw [ctlW, hc _ (by decide)]; exact h.next
  · rw [ctlW, hc _ (by decide)]; exact h.size
  · rw [hl]; rw [hm] at hw; exact h.mates_dec w hw

/-- **The run's solution in a job's memory**: `OptSolR` (the flag `CTL[224]`, the solution's rows),
and with a solution the walks' memos (`WalkMem`) and the cone's fuel in range (the solution's
`next + 1` a word). -/
structure JSol (J : Option ISolution) (m : Mem) : Prop where
  sol : OptSolR m J
  walk : ∀ J', J = some J' → WalkMem m ∧ J'.idx.next + 1 < 2 ^ 64

/-- The flat run's: the flag is `0`. -/
theorem JSol.none {m : Mem} (h : rdW (m.arr64 CTL) 224 = 0) : JSol none m :=
  ⟨h, fun _ h => nomatch h⟩

/-- **`JSol` across a frame** that writes neither the solution's rows, nor its control words, nor
the walks' memos, and whose record pool extends. -/
theorem JSol.frameX {A : List TieredArray} {C : List Word} {m m' : Mem} {J : Option ISolution}
    (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b ∉ solArrs ∧ b ≠ (NDM : TieredArray) ∧ b ≠ (CSM : TieredArray))
    (hC : ∀ x ∈ C, x ∉ solCtl ∧ x ≠ 220 ∧ x ≠ 222)
    (hx : ArrExt (erecP m) (erecP m')) (h : JSol J m) : JSol J m' := by
  refine ⟨?_, fun J' e => ⟨(h.walk J' e).1.frame hf (fun hm => (hA _ hm).2.1 rfl)
    (fun hm => (hA _ hm).2.2 rfl) (fun hm => (hC _ hm).2.1 rfl) (fun hm => (hC _ hm).2.2 rfl),
    (h.walk J' e).2⟩⟩
  have h0 : rdW (m'.arr64 CTL) SOLC = rdW (m.arr64 CTL) SOLC :=
    hf.ctl _ (fun hm => (hC _ hm).1 (by decide))
  have h1 := h.sol
  cases J with
  | none => simp only [OptSolR, ctlW] at h1 ⊢; rw [h0, h1]
  | some J =>
    simp only [OptSolR, ctlW] at h1 ⊢
    exact ⟨by rw [h0, h1.1], h1.2.frameX hf (fun b hb => (hA b hb).1) (fun x hx => (hC x hx).1) hx⟩

/-! ## The twin's facts of a job's solution -/

open ConRon.Bridge (RecordSpec RecordSpecC IFEnvOK SolView MatesDen) in
/-- **What a job's twin side takes of the run's solution**, at the job's state `a`: without one,
con-ron's `RecordSpec`; with one, `RecordSpecC` against the solution's environment `envS` and the
mates `matesU`, whose index's view (`SolView`) and mates denote at every persistent extension of
`a` (con-ron's `job_specC` takes them from `solView_ok` and `MatesRel`), every mate handle denoting
(`CvMatesDen`, for the verdict: the cone's culprit reads back). -/
def JobSpec (pins : List INatOpPinSet) (pinsP : List ConLeche.NatOpPinSet) :
    Option ISolution → AState → Prop
  | none, _ => RecordSpec pins pinsP
  | some J, a => ∃ envS matesU, RecordSpecC pins pinsP J envS matesU ∧
      ∀ s : AState, ConRon.Bridge.StateOK s → ConRon.Bridge.PExt a.store s.store →
        IFEnvOK envS (SolView J) s ∧ MatesDen s.store J.mates matesU ∧
          ConRon.Bridge.CvMatesDen s.store J.mates

/-- `JobSpec` at a persistent extension. -/
theorem JobSpec.pmono {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
    {J : Option ISolution} {a a' : AState} (h : JobSpec pins pinsP J a)
    (hx : ConRon.Bridge.PExt a.store a'.store) : JobSpec pins pinsP J a' := by
  cases J with
  | none => exact h
  | some J =>
    obtain ⟨envS, matesU, hC, hall⟩ := h
    exact ⟨envS, matesU, hC, fun s hs hx' => hall s hs (hx.trans hx')⟩

/-! ## The job relation -/

open L.Front (DECL DLP DeclsF)

local notation "V" => ConLeche.CheckMode.verified

/-- **A record's check at a job's view, bridged** (`RecordSpec`/`RecordSpecC` by the solution):
an accepted `recordCheck` leaves the store invariant, an append and the pins. -/
theorem JobSpec.keep {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
    {J : Option ISolution} {a s s' : AState} (h : JobSpec pins pinsP J a)
    (hx : ConRon.Bridge.PExt a.store s.store) (hok : ConRon.Bridge.StateOK s)
    {env : ConLeche.Env} {I : IStreamIndex} {k : Nat} {pd : IDeclaration} {d : ConLeche.Declaration}
    (hF : ConRon.Bridge.FoldOK env (I.view k) s) (hPD : ConRon.Bridge.PinsDenote s.store pins pinsP)
    (hd : Frontend.denoteDecl s.store pd = some d)
    (hrc : recordCheck V pins J I k pd s = .ok ((), s')) :
    ConRon.Bridge.StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins := by
  cases J with
  | none => obtain ⟨h1, h2, h3, -⟩ := h hF hPD hd hrc; exact ⟨h1, h2, h3⟩
  | some J =>
    obtain ⟨envS, matesU, hC, hall⟩ := h
    obtain ⟨h1, h2, -⟩ := hall s hok hx
    obtain ⟨h1, h2, h3, -⟩ := hC hF hPD hd h1 h2 hrc
    exact ⟨h1, h2, h3⟩

/-- **The memory's half of the job relation**, against the worker's twin state `a` and the
stream index `I`: the checker state without an environment (the arena, the caches, the pins, the
mode), the stream index (`IndexR`), every own row below the stamp (`OwnBelow`, so the next job's
stamp bump empties the own layer), the front's records, the pools in bounds with tier 1 empty,
the pin variants, the memory's half of `TwinOK`, the pin flag, the inductive memos. -/
structure JobM (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (J : Option ISolution) (I : IStreamIndex) (m : Mem) (a : AState) : Prop where
  arena : ArenaD m a
  core : CoreR m a.caches
  pinsR : PinsR m a.pins
  mode : ModeOK m
  idx : IndexR m I
  below : OwnBelow m
  stamp : (stampW m).toNat < 2 ^ 32
  decls : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds
  iw : L.Ind.IWOK m
  top1 : rdW (m.arr64 CTL) 130 = 0
  pinsets : L.Rom.PinSetsR m pins
  mem : TwinMem dn m a
  flag : pinW m 0 ≠ 0
  memos : IndMemos m
  fsize : I.firsts.size = ds.size
  /-- The index is frozen: its literal names and thresholds in `CTL[162‥173]`. -/
  frozen : FrozenR m I
  /-- The run's solution (`CTL[224]`, the solution's rows, the walks' memos). -/
  jsol : JSol J m

/-- **What a worker's memory keeps between two jobs**: the memory's half (`JobM`), and on the
twin side the store well formed with the scratch tier off and the caches empty. -/
structure JobR (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (J : Option ISolution) (I : IStreamIndex) (m : Mem) (a : AState) : Prop extends JobM pins dn ds J I m a where
  state : ConRon.Bridge.StateOK a
  off : a.store.scratchOn = false
  caches : a.caches = Caches.empty

/-- What the jobs' error claims assume: `check_decl`'s (`CdG`), and the callees outside the
verdict closure claim nothing. -/
structure JobG (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
    (ds : Array IDeclaration) (p : Prog) : Prop where
  cd : CdG pins dn ds p
  nv : closedNV p L.Checker.nvFns = true

/-- What a job keeps, beside the relation: the store a persistent extension, the pins. -/
def JobPost (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (J : Option ISolution) (I : IStreamIndex) (a : AState) (m' : Mem) (a' : AState) : Prop :=
  JobR pins dn ds J I m' a' ∧ ConRon.Bridge.PExt a.store a'.store ∧ a'.pins = a.pins

/-! ## Frames of the job's memory -/

/-- Writing back a word read from the same place changes nothing. -/
theorem set64_rdW_self (m : Mem) (b : TieredArray) (i : Word) : m.set64 b i (rdW (m.arr64 b) i) = m := by
  obtain ⟨bytes, words, glob⟩ := m
  simp only [Mem.set64, Mem.arr64, Mem.mk.injEq, true_and, and_true]
  funext s
  split
  · subst s
    simp only [rdW, Array.set!_eq_setIfInBounds]
    by_cases h : i.toNat < (words b).size
    · simp [h, Array.setIfInBounds, Array.set_getElem_self]
    · simp [Array.setIfInBounds, h]
  · rfl

/-- The `CTL` words below `48` or in `60‥127` (the bracket's and the flush's). -/
def LoCtl (C : List Word) : Prop := ∀ x ∈ C, x.toNat < 48 ∨ (60 ≤ x.toNat ∧ x.toNat < 128)

/-- `PT0` and tier-1 arrays below `64` (the bracket's). -/
def LoArr (A : List TieredArray) : Prop := ∀ b ∈ A, (b = PT0 ∨ IsTier1 b) ∧ b.arr < 64

theorem loArr_scr : LoArr scrArrs := fun b hb => by
  refine ⟨?_, scrArrs_low b hb⟩
  rcases List.mem_cons.mp hb with h | h
  · exact .inl h
  · exact .inr (slot1Arrs_ge b h)

theorem loCtl_enter : LoCtl ((0 :: resetCtl) ++ memoCtl) := by
  intro x h
  simp [resetCtl, scratchCnts, memoCtl, SCB] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    <;> decide

theorem loCtl_drop : LoCtl (flushCtl ++ (0 :: resetCtl)) := by
  intro x h
  simp [resetCtl, scratchCnts, flushCtl, SCB] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    <;> decide

section lo
variable {A : List TieredArray} {C : List Word} {m m' : Mem}

theorem LoArr.not_hi (hA : LoArr A) {b : TieredArray} (h : 64 ≤ b.arr) : b ∉ A :=
  fun hb => by have := (hA b hb).2; omega

theorem LoArr.not_t0 (hA : LoArr A) {b : ArrId} (h : b ≠ PT0) : (b : TieredArray) ∉ A := fun hb => by
  rcases (hA _ hb).1 with e | e
  · exact h (TieredArray.t0_inj.mp e)
  · simp at e

theorem LoCtl.not_hi (hC : LoCtl C) {x : Word} (h : 128 ≤ x.toNat) : x ∉ C :=
  fun hx => by have := hC x hx; omega

theorem LoCtl.not_mid (hC : LoCtl C) {x : Word} (h1 : 48 ≤ x.toNat) (h2 : x.toNat < 60) : x ∉ C :=
  fun hx => by have := hC x hx; omega

theorem LoArr.arr (hA : LoArr A) (hf : MemFrame A C m m') {b : TieredArray} (h : 64 ≤ b.arr) :
    m'.arr64 b = m.arr64 b :=
  hf.arr b (hA.not_hi h) (fun e => by subst e; revert h; decide)

theorem LoCtl.ctl (hC : LoCtl C) (hf : MemFrame A C m m') {x : Word} (h : 128 ≤ x.toNat) :
    rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x :=
  hf.ctl x (hC.not_hi h)

theorem erecP_frameLo (hA : LoArr A) (hC : LoCtl C) (hf : MemFrame A C m m') : erecP m' = erecP m :=
  erecP_congr' (hA.arr hf (by decide)) (hA.arr hf (by decide)) (hC.ctl hf (by decide))
    (hC.ctl hf (by decide))

theorem IndexR.frameLo {I : IStreamIndex} (hA : LoArr A) (hC : LoCtl C) (hf : MemFrame A C m m')
    (h : IndexR m I) : IndexR m' I :=
  h.grow (fun b _ hb => hA.arr hf (by omega)) (hC.ctl hf (by decide))
    (by rw [erecP_frameLo hA hC hf]; exact fun _ _ h => h)

theorem FrozenR.frameLo {I : IStreamIndex} (hC : LoCtl C) (hf : MemFrame A C m m')
    (h : FrozenR m I) : FrozenR m' I :=
  h.frame (fun x hx => not_mem_frozenCtl (.inl (by have := hC x hx; omega))) hf

theorem OwnBelow.congr (he : ∀ b ∈ envArrs, m'.arr64 b = m.arr64 b)
    (h133 : rdW (m'.arr64 CTL) 133 = rdW (m.arr64 CTL) 133) (h : OwnBelow m) : OwnBelow m' := by
  intro w hw
  have e1 : ownRow m' w = ownRow m w := by simp only [ownRow, he _ (tierA_oix_mem _ _)]
  have e2 := he _ (tierA_otx_mem (rowTag w) (tierW w))
  simp only [stampW, h133, e1, e2]
  exact h w hw

theorem OwnBelow.frame (hA : ∀ b ∈ A, b ∉ envArrs) (h133 : (133 : Word) ∉ C) (hf : MemFrame A C m m')
    (h : OwnBelow m) : OwnBelow m' :=
  h.congr (fun b hb => hf.arr b (fun hm => hA b hm hb) (fun e => by subst e; revert hb; decide))
    (hf.ctl 133 h133)

theorem OwnBelow.frameLo (hA : LoArr A) (hC : LoCtl C) (hf : MemFrame A C m m') (h : OwnBelow m) :
    OwnBelow m' :=
  h.frame (fun b hb hm => by have := envArrs_arr hm; have := (hA b hb).2; omega)
    (hC.not_hi (by decide)) hf

theorem stampW_frameLo (hC : LoCtl C) (hf : MemFrame A C m m') : stampW m' = stampW m :=
  hC.ctl hf (by decide)

theorem declsF_frameLo {ds : Array IDeclaration} (hA : LoArr A) (hf : MemFrame A C m m')
    (h : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) : DeclsF (m'.arr64 DECL) (m'.arr64 DLP) ds := by
  rw [hA.arr hf (by decide), hA.arr hf (by decide)]; exact h

theorem iwOK_frameLo (hA : LoArr A) (hC : LoCtl C) (hf : MemFrame A C m m') (h : L.Ind.IWOK m) :
    L.Ind.IWOK m' :=
  IWOK.frame hf (hA.not_hi (by decide)) (hA.not_hi (by decide)) (hC.not_hi (by decide))
    (hC.not_hi (by decide)) h (hA.not_hi (by decide)) (hC.not_hi (by decide))

theorem pinSetsR_frameLo {pins : List INatOpPinSet} (hA : LoArr A) (hC : LoCtl C)
    (hf : MemFrame A C m m') (h : L.Rom.PinSetsR m pins) : L.Rom.PinSetsR m' pins :=
  PinSetsR.grow h (RecGrow.of_eq (hA.arr hf (by decide)) (hC.ctl hf (by decide)))
    (hC.ctl hf (by decide)) (hC.ctl hf (by decide))

theorem CoreMemos.frameLo (hA : LoArr A) (hC : LoCtl C) (hf : MemFrame A C m m') (h : CoreMemos m) :
    CoreMemos m' :=
  h.frame hf ⟨hA.not_t0 (by decide), hA.not_t0 (by decide)⟩
    ⟨hC.not_mid (by decide) (by decide), hC.not_mid (by decide) (by decide)⟩
    ⟨hA.not_t0 (by decide), hA.not_t0 (by decide), hA.not_t0 (by decide)⟩
    ⟨hC.not_hi (by decide), hC.not_hi (by decide), hC.not_hi (by decide)⟩
    ⟨hA.not_t0 (by decide), hA.not_t0 (by decide), hA.not_t0 (by decide)⟩
    ⟨hC.not_mid (by decide) (by decide), hC.not_mid (by decide) (by decide),
      hC.not_mid (by decide) (by decide)⟩ (hA.not_hi (by decide)) (hC.not_hi (by decide))

theorem IndMemos.frameLo (hA : LoArr A) (hC : LoCtl C) (hf : MemFrame A C m m') (h : IndMemos m) :
    IndMemos m' :=
  h.frame hf (fun b hb => by
      have h1 := hA b hb
      refine ⟨fun e => ?_, fun e => ?_, .inl (by omega)⟩ <;> subst e <;> revert h1 <;> decide)
    (fun x hx => by have := hC x hx; omega)

theorem TwinMem.frameLo {dn : NIdx → Option ConLeche.Name} {a a' : AState} (hA : LoArr A)
    (hC : LoCtl C) (hf : MemFrame A C m m') (h : TwinMem dn m a)
    (hN : ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → denoteN a'.store.ns k = some x) :
    TwinMem dn m' a' :=
  ⟨by rw [hf.size]; exact h.erec, by rw [hf.size]; exact h.spn, by rw [hf.size]; exact h.bstk,
    h.memos.frameLo hA hC hf, hN⟩

/-- **`JSol` across a low frame** (the bracket's, the flush's). -/
theorem JSol.frameLo {J : Option ISolution} (hA : LoArr A) (hC : LoCtl C) (hf : MemFrame A C m m')
    (h : JSol J m) : JSol J m' :=
  h.frameX hf
    (fun b hb => ⟨fun hs => hA.not_hi (by have := solArrs_arr hs; omega) hb,
      fun e => hA.not_hi (by rw [e]; decide) hb, fun e => hA.not_hi (by rw [e]; decide) hb⟩)
    (fun x hx => ⟨fun hs => by
        simp only [solCtl, SOLC, SNEXTC, SCNTC, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl <;> exact hC.not_hi (by decide) hx,
      fun e => hC.not_hi (by rw [e]; decide) hx, fun e => hC.not_hi (by rw [e]; decide) hx⟩)
    (by rw [erecP_frameLo hA hC hf]; exact fun _ _ h => h)

end lo

/-- The decoder names only persistent handles (its names survive the scratch bracket). -/
def DnPers (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → k.isPersistent = true

/-- **`scratch_enter` from the job relation**: the memory's half at the bracket's memory and the
twin's state with the scratch tier on. -/
theorem JobR.enter {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {J : Option ISolution} {I : IStreamIndex} {m : Mem} {a : AState}
    (hJ : JobR pins dn ds J I m a) (hdn : DnPers dn)
    (hlo : (rdW ((preMem m).arr64 CTL) SCB).toNat < 2 ^ 47 - 2 ^ 33)
    (h62 : SCB.toNat < ((preMem m).arr64 CTL).size)
    (c1 : rdW ((resetMem (preMem m) 1).arr64 CTL) bmSch.cs + 2 ≠ 0)
    (c2 : rdW ((mclearG bmSch (resetMem (preMem m) 1)).arr64 CTL) lfSch.cs + 2 ≠ 0)
    (c3 : rdW ((mclearG lfSch (mclearG bmSch (resetMem (preMem m) 1))).arr64 CTL) imSch.cs + 2 ≠ 0)
    (c4 : rdW ((mclearG imSch (mclearG lfSch (mclearG bmSch (resetMem (preMem m) 1)))).arr64 CTL)
      frSch.cs + 2 ≠ 0)
    (hpt : (resetMemA (preMem m) 1).top >>> 40 = 0 ∨ (1 : Word) = 0 → 0 < ((resetMemA (preMem m) 1).arr64 PT0).size) :
    JobM pins dn ds J I (enterMem m) (AM.st enterScratch a) := by
  have hf := enterMem_frame m
  have hA := loArr_scr
  have hC := loCtl_enter
  obtain ⟨-, hst, -⟩ := AM.of_run_ok _ _ _ _ (enterScratch_run a)
  have hx := ConRon.Bridge.PExt.enterScratch hJ.state.wf
  refine ⟨?_, ?_, ?_, modeOK_enterMem _ h62, hJ.idx.frameLo hA hC hf, hJ.below.frameLo hA hC hf,
    by rw [stampW_frameLo hC hf]; exact hJ.stamp, declsF_frameLo hA hf hJ.decls, iwOK_frameLo hA hC hf hJ.iw,
    by rw [hC.ctl hf (by decide)]; exact hJ.top1, pinSetsR_frameLo hA hC hf hJ.pinsets,
    hJ.mem.frameLo hA hC hf fun k x e => ?_, by rw [pinW_frame hf (hA.not_hi (by decide))]; exact hJ.flag,
    hJ.memos.frameLo hA hC hf, hJ.fsize, hJ.frozen.frameLo hC hf, hJ.jsol.frameLo hA hC hf⟩
  · rw [hst]; exact ArenaD.enter _ _ hJ.arena hlo h62 c1 c2 c3 c4 hpt
  · exact hJ.core.frame (.of_low scrArrs_low (by decide))
      (.of_lt (fun x h => resetCtl_lt x h) (by decide)) hf
  · exact hJ.pinsR.frame (.of_low scrArrs_low (by decide)) hf
  · rw [enterScratch_st]
    exact hx.lss.ls.ns k x (hdn k x e) (hJ.mem.dnN k x e)

/-! ## The job's start: the view of position `k`, a fresh own layer -/

/-- The memory after `iw_reset`'s `m₁` and the stamp bump: `CTL[133]` one up, `CTL[134]` the
record's first counter, `CTL[135]` its position. -/
def jobMem (m₁ : Mem) (k : Word) : Mem :=
  ((m₁.set64 CTL 133 (rdW (m₁.arr64 CTL) 133 + 1)).set64 CTL 134
    (rdW ((m₁.set64 CTL 133 (rdW (m₁.arr64 CTL) 133 + 1)).arr64 FIRSTS) k)).set64 CTL 135 k

theorem envArrs_ne_ctl : ∀ b ∈ envArrs, b ≠ CTL := by decide

/-- **What a job's callees start from**, at position `k` with the twin's state `a`: the stage
relation at the view of `k` and the memory's other job facts. -/
structure JobS (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (J : Option ISolution) (I : IStreamIndex) (k : Nat) (m : Mem) (a : AState) : Prop where
  stage : StageR 0 (I.view k) m a
  decls : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds
  pinsets : L.Rom.PinSetsR m pins
  mem : TwinMem dn m a
  flag : pinW m 0 ≠ 0
  memos : IndMemos m
  idx : IndexR m I
  frozen : FrozenR m I
  jsol : JSol J m

/-- **The job's start**: from the memory's half of the job relation (after the bracket's opening),
`iw_reset`, the stamp bump (the record's view: `CTL[134]` its first counter from `FIRSTS`,
`CTL[135]` its position) and the literal flags (`CTL[160]`, `CTL[161]`, `from_le` of the frozen
thresholds at the first counter) give the stage relation at the view of position `k`, with an
empty own layer (every row's stamp is below the new one). -/
theorem JobM.stage {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {J : Option ISolution} {I : IStreamIndex} {m : Mem} {a : AState} {k x y : Word}
    (h : JobM pins dn ds J I m a) (hk : k.toNat < ds.size)
    (hst : ¬ 4294967294 ≤ rdW ((m.set64 CTL 200 0).arr64 CTL) 133)
    (hx : (x != 0) = fromLe (optW (rdW (m.arr64 CTL) 172)) (rdW (m.arr64 FIRSTS) k).toNat)
    (hy : (y != 0) = fromLe (optW (rdW (m.arr64 CTL) 173)) (rdW (m.arr64 FIRSTS) k).toNat) :
    JobS pins dn ds J I k.toNat (flagsSet (jobMem (m.set64 CTL 200 0) k) x y) a ∧
      rdW ((flagsSet (jobMem (m.set64 CTL 200 0) k) x y).arr64 CTL) 130 = 0 := by
  have hsz : 200 < (m.arr64 CTL).size := h.iw.ctl
  generalize hm2 : m.set64 CTL 200 0 = m2 at hst
  have hf2 : MemFrame [] [200] m m2 := hm2 ▸ MemFrame.setCtl m 200 0
  have e2 : ∀ x : Word, x ≠ 200 → rdW (m2.arr64 CTL) x = rdW (m.arr64 CTL) x := fun x hx =>
    hf2.ctl x (by simpa using hx)
  generalize hst' : rdW (m2.arr64 CTL) 133 = st at hst
  generalize hm3' : jobMem m2 k = m3'
  generalize hm3 : flagsSet m3' x y = m3
  have hsz2 : (m2.arr64 CTL).size = (m.arr64 CTL).size := hf2.size CTL
  have hf3' : MemFrame [] [133, 134, 135] m2 m3' := by
    rw [← hm3']; unfold jobMem
    exact (((MemFrame.setCtl _ 133 _).mono (by simp) (by simp)).trans
      ((MemFrame.setCtl _ 134 _).mono (by simp) (by simp))).trans
      ((MemFrame.setCtl _ 135 _).mono (by simp) (by simp))
  have hf34 : MemFrame [] [160, 161] m3' m3 := hm3 ▸ flagsSet_frame m3' x y
  have hf3 : MemFrame [] [133, 134, 135, 160, 161] m2 m3 :=
    (hf3'.mono (by simp) (by simp)).trans (hf34.mono (by simp) (by simp))
  have hf : MemFrame [] [200, 133, 134, 135, 160, 161] m m3 :=
    (hf2.mono (by simp) (by simp)).trans (hf3.mono (by simp) (by simp))
  have hC : ∀ x ∈ ([200, 133, 134, 135, 160, 161] : List Word),
      x = 200 ∨ x = 133 ∨ x = 134 ∨ x = 135 ∨ x = 160 ∨ x = 161 := by
    simp
  have eA : ∀ b : TieredArray, b ≠ CTL → m3.arr64 b = m.arr64 b := fun b hb => hf.arr b (by simp) hb
  have eC : ∀ x : Word, x ≠ 200 → x ≠ 133 → x ≠ 134 → x ≠ 135 → x ≠ 160 → x ≠ 161 →
      rdW (m3.arr64 CTL) x = rdW (m.arr64 CTL) x := fun x h1 h2 h3 h4 h5 h6 =>
    hf.ctl x (by simp [h1, h2, h3, h4, h5, h6])
  -- the five words
  have hlt : ∀ x : Word, x.toNat ≤ 200 → x.toNat < (m2.arr64 CTL).size := fun x hx => by omega
  have e34 : ∀ x : Word, x ≠ 160 → x ≠ 161 → rdW (m3.arr64 CTL) x = rdW (m3'.arr64 CTL) x :=
    fun x h1 h2 => hf34.ctl x (by simp [h1, h2])
  have hsz3' : 161 < (m3'.arr64 CTL).size := by rw [hf3'.size, hsz2]; omega
  have v133 : rdW (m3.arr64 CTL) 133 = st + 1 := by
    rw [e34 _ (by decide) (by decide), ← hm3']; unfold jobMem
    rw [rdW_set_ctl _ 135 _ 133 (by decide), rdW_set_ctl _ 134 _ 133 (by decide),
      rdW_set64_self _ _ _ _ (hlt 133 (by decide)), hst']
  have v134 : rdW (m3.arr64 CTL) 134 = rdW (m.arr64 FIRSTS) k := by
    rw [e34 _ (by decide) (by decide), ← hm3']; unfold jobMem
    rw [rdW_set_ctl _ 135 _ 134 (by decide), rdW_set64_self _ _ _ _ (by rw [Mem.size_arr64_set64]; exact hlt 134 (by decide)),
      Mem.arr64_set64_ne _ _ _ _ _ (by decide), ← hm2, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have v135 : rdW (m3.arr64 CTL) 135 = k := by
    rw [e34 _ (by decide) (by decide), ← hm3']; unfold jobMem
    rw [rdW_set64_self _ _ _ _ (by simp only [Mem.size_arr64_set64]; exact hlt 135 (by decide))]
  have v160 : rdW (m3.arr64 CTL) 160 = x := by rw [← hm3]; exact flagsSet_rd160 _ _ _ hsz3'
  have v161 : rdW (m3.arr64 CTL) 161 = y := by rw [← hm3]; exact flagsSet_rd161 _ _ _ hsz3'
  have hFz3 : FrozenR m3 I := h.frozen.frame (fun x hx => by
    rcases hC x hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hf
  have hstN : st.toNat < 4294967294 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hst); simpa using this
  have hst1 : (st + 1).toNat = st.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hst0 : stampW m = st := by rw [← hst', e2 133 (by decide)]; rfl
  -- the own layer
  have hB2 := h.below
  have hrow : ∀ w, ownRow m3 w = ownRow m w := fun w => by
    simp only [ownRow, eA _ (envArrs_ne_ctl _ (tierA_oix_mem _ _))]
  have hotx : ∀ w, m3.arr64 (tierA (otxArr (rowTag w)) (tierW w)) =
      m.arr64 (tierA (otxArr (rowTag w)) (tierW w)) := fun w =>
    eA _ (envArrs_ne_ctl _ (tierA_otx_mem _ _))
  have hs3 : (stampW m3).toNat = st.toNat + 1 := by simp only [stampW, v133, hst1]
  have hB3 : OwnBelow m3 := fun w hw => by
    obtain ⟨h1, h2⟩ := hB2 w hw
    rw [hrow, hotx, hs3]; rw [hst0] at h1 h2; omega
  have hO3 : OwnEmpty m3 := OwnEmpty.of_below hB3 fun w hw => by
    obtain ⟨h1, h2⟩ := hB2 w hw
    rw [hrow, otxArrT, hotx, hs3]; rw [hst0] at h1 h2; omega
  -- the stream index
  have hx3 : erecP m3 = erecP m :=
    erecP_congr' (eA _ (by decide)) (eA _ (by decide)) (eC 129 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (eC 130 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hI3 : IndexR m3 I := h.idx.grow (fun b _ hb => eA b (fun e => by subst e; revert hb; decide))
    (eC 128 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by rw [hx3]; exact fun _ _ h => h)
  have h134 : (rdW (m3.arr64 CTL) 134).toNat = I.firsts.getD k.toNat I.next := by
    have hkf : k.toNat < I.firsts.size := by rw [h.fsize]; exact hk
    rw [v134, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hkf, Option.getD_some,
      ← h.idx.firsts _ hkf, UInt64.ofNat_toNat]
  have hE3 : EnvR m3 0 (I.view k.toNat) :=
    EnvR.ofIndex hI3 hFz3 hO3 hB3 (by rw [hs3]; omega) h134 (by rw [v135])
      (by rw [v160, hx, ← h134, v134, h.frozen.natFrom])
      (by rw [v161, hy, ← h134, v134, h.frozen.strFrom])
  have hCK : CheckR m3 a 0 (I.view k.toNat) :=
    ⟨h.arena.frameHi hf (by simp) (fun x hx => by rcases hC x hx with rfl|rfl|rfl|rfl|rfl|rfl <;> decide),
      h.core.frame (fun b hb => by simp at hb) (fun x hx => by
        rcases hC x hx with rfl|rfl|rfl|rfl|rfl|rfl <;> decide) hf,
      h.pinsR.frame (fun b hb => by simp at hb) hf, hE3,
      h.mode.frame hf (by decide) (by decide)⟩
  have hIW : L.Ind.IWOK m3 :=
    IWOK.frame hf3 (by simp) (by simp) (by decide) (by decide) (hm2 ▸ h.iw.reset) (by simp) (by decide)
  refine ⟨⟨⟨hCK, hIW⟩, by rw [eA _ (by decide), eA _ (by decide)]; exact h.decls, ?_, ?_,
    by rw [pinW_frame hf (by simp)]; exact h.flag, ?_, hI3, hFz3,
    h.jsol.frameX hf (fun b hb => by simp at hb)
      (fun x hx => by rcases hC x hx with rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rw [hx3]; exact fun _ _ h => h)⟩,
    by rw [eC 130 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.top1⟩
  · exact PinSetsR.grow h.pinsets (RecGrow.of_eq (eA _ (by decide))
      (eC 129 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
      (eC 150 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (eC 151 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact ⟨by rw [hf.size]; exact h.mem.erec, by rw [hf.size]; exact h.mem.spn,
      by rw [hf.size]; exact h.mem.bstk, h.mem.memos.frame hf (by simp) (by decide),
      h.mem.dnN⟩
  · exact h.memos.frame hf (by simp) (fun x hx => by rcases hC x hx with rfl|rfl|rfl|rfl|rfl|rfl <;> decide)

/-! ## The job's write sets

`and_pin_ok` (a leaf) leaves the front's records, the stream index, the pin variant list's header
and the inductive memos alone; `check_decl` leaves the stream index and the pin table alone. Both
are facts of the program text (`closedA`, by `decide +kernel` at the checker's program). -/

/-- The stream index's arrays: the base rows (`TIX*`, `EIX*`, tier 0) and `FIRSTS`. -/
def IdxArr (b : TieredArray) : Bool :=
  b.hi == false && ((decide (129 ≤ b.arr) && decide (b.arr ≤ 134)) || b.arr == 137)

/-- The arrays `and_pin_ok` may write. -/
def apP (b : TieredArray) : Bool :=
  b != DECL && b != DLP && !IdxArr b && b != ILFM && b != L.Stubs.CRM &&
    (decide (b.arr < 201) || decide (208 < b.arr)) && !(decide (210 ≤ b.arr) && decide (b.arr ≤ 222))

def apA : List TieredArray := leafA.filter apP

/-- The `CTL` words `and_pin_ok` may write. -/
def apQ (x : Word) : Bool :=
  (decide (x.toNat < 162) || decide (173 < x.toNat)) && x != 128 && x != 150 && x != 151 && x.toNat != 52 && x.toNat != 158 &&
    (decide (x.toNat < 202) || decide (228 < x.toNat))

def apC : List Word := leafC.filter apQ

/-- The solution's rows (`solArrs`: `210‥218`), as a test. -/
def SolArr (b : TieredArray) : Bool := b.hi == false && decide (210 ≤ b.arr) && decide (b.arr ≤ 218)

/-- The arrays `check_decl` (and `check_record_sol`) may write: all but the stream index, the pins and
the solution's rows. -/
def cdA : List TieredArray := checkerWordArrays.filter fun b => !IdxArr b && b != PINS && !SolArr b

/-- The `CTL` words `check_decl` (and `check_record_sol`) may write: all but the index's counter,
the frozen index's literal names and thresholds (`CTL[162‥173]`) and the solution's words
(`solCtl`: `CTL[224‥226]`). -/
def cdC : List Word :=
  ((List.range 1024).filter fun x => (decide (x < 162) || decide (173 < x)) && x != 128 &&
    x != 224 && x != 225 && x != 226).map UInt64.ofNat

theorem apA_mem {b : TieredArray} (h : b ∈ apA) : b ∈ leafA ∧ apP b = true := List.mem_filter.mp h
theorem apC_mem {x : Word} (h : x ∈ apC) : x ∈ leafC ∧ apQ x = true := List.mem_filter.mp h

theorem apA_idx {b : TieredArray} (h : b ∈ apA) : IdxArr b = false := by
  have := (apA_mem h).2; simp only [apP, Bool.and_eq_true, Bool.not_eq_true'] at this; exact this.1.1.1.1.2

theorem cdA_idx {b : TieredArray} (h : b ∈ cdA) : IdxArr b = false := by
  have := (List.mem_filter.mp h).2; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this.1.1

theorem cdA_pins : (PINS : TieredArray) ∉ cdA := fun h => by
  have := (List.mem_filter.mp h).2; simp at this

theorem apC_128 : (128 : Word) ∉ apC := fun h => by have := (apC_mem h).2; simp [apQ] at this

theorem cdC_128 : (128 : Word) ∉ cdC := fun h => by
  simp only [cdC, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨x, ⟨hx, h1⟩, e⟩ := h
  have : x = 128 := by
    have := congrArg UInt64.toNat e; simp at this; omega
  subst this; simp at h1

theorem apC_frozen {x : Word} (h : x ∈ apC) : x ∉ frozenCtl := by
  have := (apC_mem h).2
  simp only [apQ, Bool.and_eq_true] at this
  obtain ⟨⟨⟨⟨⟨⟨hn, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := this
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hn
  exact not_mem_frozenCtl (by omega)

theorem cdC_frozen {x : Word} (h : x ∈ cdC) : x ∉ frozenCtl := by
  simp only [cdC, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨y, ⟨hy, h1⟩, e⟩ := h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h1
  have : x.toNat = y := by rw [← e]; simp; omega
  exact not_mem_frozenCtl (by omega)

/-- `and_pin_ok` writes neither the solution's rows nor the walks' memos. -/
theorem apA_jsol {b : TieredArray} (h : b ∈ apA) :
    b ∉ solArrs ∧ b ≠ (NDM : TieredArray) ∧ b ≠ (CSM : TieredArray) := by
  have := (apA_mem h).2
  simp only [apP, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at this
  have hn : ¬ (210 ≤ b.arr ∧ b.arr ≤ 222) := by rcases this.2 with h | h <;> omega
  exact ⟨fun hs => hn (by have := solArrs_arr hs; omega), fun e => hn (by subst e; decide),
    fun e => hn (by subst e; decide)⟩

/-- `and_pin_ok` writes neither the solution's words nor the walks' memo stamps. -/
theorem apC_jsol {x : Word} (h : x ∈ apC) : x ∉ solCtl ∧ x ≠ 220 ∧ x ≠ 222 := by
  have := (apC_mem h).2
  simp only [apQ, Bool.and_eq_true] at this
  obtain ⟨-, hn⟩ := this
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hn
  refine ⟨fun hs => ?_, fun e => ?_, fun e => ?_⟩
  · simp only [solCtl, SOLC, SNEXTC, SCNTC, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> simp at hn
  · subst e; simp at hn
  · subst e; simp at hn

/-- `check_decl` writes no row of the solution. -/
theorem cdA_sol {b : TieredArray} (h : b ∈ cdA) : b ∉ solArrs := fun hs => by
  have := (List.mem_filter.mp h).2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  have h2 := solArrs_arr hs
  have h3 := this.2
  simp [SolArr, h2.1, h2.2.1, h2.2.2] at h3

/-- `check_decl` writes no word of the solution. -/
theorem cdC_sol {x : Word} (h : x ∈ cdC) : x ∉ solCtl := fun hs => by
  simp only [cdC, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨y, ⟨hy, h1⟩, e⟩ := h
  have : x.toNat = y := by rw [← e]; simp; omega
  simp only [solCtl, SOLC, SNEXTC, SCNTC, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> (simp at this; subst this; simp at h1)

/-- **The stream index across a writer that leaves its arrays and `CTL[128]` alone** and only
grows the record pool. -/
theorem IndexR.frameIdx {A : List TieredArray} {C : List Word} {m m' : Mem} {I : IStreamIndex}
    (hA : ∀ b ∈ A, IdxArr b = false) (h128 : (128 : Word) ∉ C) (hf : MemFrame A C m m')
    (hx : ArrExt (erecP m) (erecP m')) (h : IndexR m I) : IndexR m' I :=
  h.grow (fun b h0 h1 => hf.arr b (fun hb => by
      have := hA b hb; simp only [IdxArr, h0, beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff,
        Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at this
      omega) (fun e => by subst e; revert h1; decide))
    (hf.ctl _ h128) hx

/-- **`and_pin_ok(k)` at a job's start**: the twin's `andPinOk` runs to the call's result, the
store grows (con-ron's `andPinOk_run`), and the job's start relation holds after it (the
stage relation by the refinement, the rest by the leaf's write set). -/
theorem andPin_job {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {p : Prog} {J : Option ISolution} {I : IStreamIndex} (hap : AndPinIndProg p)
    (hrom : ∀ dn vis fe, L.Rom.RomAndPinRef p dn vis fe)
    (hW : ∃ F, "and_pin_ok" ∈ F ∧ closedA p apA apC F = true) (hFD : FrontDecls ds)
    {k : Word} (hk : k.toNat < ds.size) {m m' : Mem} {a : AState} {env : ConLeche.Env}
    {d : ConLeche.Declaration} (hS : JobS pins dn ds J I k.toNat m a) (hok : ConRon.Bridge.StateOK a)
    (hF : ConRon.Bridge.FoldOK env (I.view k.toNat) a)
    (hd : Frontend.denoteDecl a.store ds[k.toNat] = some d) {n : Nat} {r : List Word}
    (c : callW p n "and_pin_ok" [k] m = some (r, m')) :
    ∃ b a', (andPinOk ds[k.toNat]).run a = .ok (b, a') ∧ (r.headD 0 != 0) = b ∧
      JobS pins dn ds J I k.toNat m' a' ∧ L.Ind.IWGrow m m' ∧ MemFrame apA apC m m' ∧
      ConRon.Bridge.StateOK a' ∧ Ext a.store a'.store ∧ a'.caches = a.caches ∧ a'.pins = a.pins ∧
      ConRon.Bridge.FoldOK env (I.view k.toNat) a' := by
  obtain ⟨F, hF0, hcl⟩ := hW
  have hpre : StageR 0 (I.view k.toNat) m a ∧ L.Front.DeclAtF (m.arr64 DECL) (m.arr64 DLP) k.toNat ds[k.toNat] ∧
      (∀ b nP, ds[k.toNat] = .indDecl b nP → FrontBlock b) ∧ ConRon.Bridge.StateOK a ∧
      (m.arr64 DECL).size < 2 ^ 63 ∧ (m.arr64 DLP).size < 2 ^ 63 :=
    ⟨hS.stage, hS.decls.recs _ hk, fun b nP e => hFD _ hk b nP e, hok, hS.decls.dsize, hS.decls.psize⟩
  obtain ⟨s1, hs1, -, hok1, hKP, hgr, hdec⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (andPinOkF_refines hap (hrom dn 0 (I.view k.toNat)) k ds[k.toNat] n ⟨m, Locals.init []⟩ a hpre) c
  obtain ⟨s2, hs2, hfr, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (invoke_memFrame hcl n hF0 [k] ⟨m, Locals.init []⟩) c
  rw [hs1] at hKP hgr hdec; rw [hs2] at hfr
  have hrun := AM.run_of_ok _ _ hok1
  obtain ⟨hok', hext, hc, hpins⟩ := ConRon.Bridge.andPinOk_run hok hF.check.pins hd hrun
  refine ⟨_, _, hrun, hdec.1, ⟨hKP, ?_, ?_, ?_, ?_, ?_, ?_, hS.frozen.frame (fun x hx => apC_frozen hx) hfr, ?_⟩,
    hgr, hfr, hok', hext, hc, hpins,
    hF.step (hF.check.mono hok' hext hc hpins) hpins⟩
  · rw [hfr.arr _ (fun h => by have := (apA_mem h).2; simp [apP] at this) (by decide),
      hfr.arr _ (fun h => by have := (apA_mem h).2; simp [apP] at this) (by decide)]
    exact hS.decls
  · exact PinSetsR.grow hS.pinsets ⟨hgr.er, hgr.erGet⟩
      (hfr.ctl _ (fun h => by have := (apC_mem h).2; simp [apQ] at this))
      (hfr.ctl _ (fun h => by have := (apC_mem h).2; simp [apQ] at this))
  · refine ⟨by rw [hfr.size]; exact hS.mem.erec, by rw [hfr.size]; exact hS.mem.spn,
      by rw [hfr.size]; exact hS.mem.bstk, ?_, fun j x e => hext.lss.ls.ns j x (hS.mem.dnN j x e)⟩
    have nA := fun {b : TieredArray} (h : b ∉ leafA) => fun hb : b ∈ apA => h (apA_mem hb).1
    have nC := fun {x : Word} (h : x ∉ leafC) => fun hx : x ∈ apC => h (apC_mem hx).1
    exact hS.mem.memos.frame hfr ⟨nA leafA_memo.1, nA leafA_memo.2⟩ ⟨nC leafC_memo.1, nC leafC_memo.2⟩
      ⟨nA leafA_walk.1, nA leafA_walk.2.1, nA leafA_walk.2.2⟩
      ⟨nC leafC_walk.1, nC leafC_walk.2.1, nC leafC_walk.2.2⟩
      ⟨nA leafA_lp.1, nA leafA_lp.2.1, nA leafA_lp.2.2⟩
      ⟨nC leafC_lp.1, nC leafC_lp.2.1, nC leafC_lp.2.2⟩ (nA leafA_hb) (nC leafC_hb)
  · rw [pinW_frame hfr (fun h => leafA_pins (apA_mem h).1)]; exact hS.flag
  · refine hS.memos.frame hfr (fun b hb => ?_) (fun x hx => ?_)
    · have := (apA_mem hb).2; simp only [apP, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
        decide_eq_true_eq] at this
      exact ⟨this.1.1.1.2, this.1.1.2, this.1.2⟩
    · have := (apC_mem hx).2; simp only [apQ, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
        decide_eq_true_eq] at this
      exact ⟨this.1.1.2, this.1.2, this.2.imp id (fun h => by omega)⟩
  · exact hS.idx.frameIdx (fun b hb => apA_idx hb) apC_128 hfr hgr.ext
  · exact hS.jsol.frameX hfr (fun b hb => apA_jsol hb) (fun x hx => apC_jsol hx) hgr.ext

/-! ## The job's end -/

/-- Emptying tier 1 of the record pool keeps the pool's bounds. -/
theorem IWOK.set130 {m : Mem} (h : L.Ind.IWOK m) : L.Ind.IWOK (m.set64 CTL 130 0) := by
  have hne : ∀ b : TieredArray, b ≠ CTL → (m.set64 CTL 130 0).arr64 b = m.arr64 b :=
    fun b hb => Mem.arr64_set64_ne _ _ _ _ _ hb
  have := h.ctl
  grind [IWOK_iff, iwTop, erTop, erecTop1, rdW_set64, Mem.size_arr64_set64]

/-- **The job relation after the bracket's close**: from the relation `check_decl` leaves (at its
view `v` and environment `x`), the memos, and the stream index and the pool at the job's start
`m₀` (tier 1 of the record pool empty there; the job's callees leave the index alone and only grow
the pool), `scratch_drop`'s memory with tier 1 emptied (`CTL[130] := 0`) is the memory's half of
the job relation at the twin's state after `dropScratch`. -/
theorem JobM.ofDrop {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {J : Option ISolution} {I : IStreamIndex} {m₀ m m₁ : Mem} {a a' : AState} {v : Word} {x : IFEnv}
    (hR : LoopR pins m a v x ds) (hcm : CoreMemos m) (hIM : IndMemos m) (hfl : pinW m 0 ≠ 0)
    (hT : TwinMem dn m a') (hfs : I.firsts.size = ds.size)
    (hI : IndexR m₀ I) (hFz : FrozenR m₀ I) (h0 : rdW (m₀.arr64 CTL) 130 = 0)
    (hf0 : MemFrame (apA ++ cdA) (apC ++ cdC) m₀ m)
    (hg : L.Ind.IWGrow m₀ m) (hC : CheckR m₁ a' v x)
    (hf : MemFrame scrArrs (flushCtl ++ (0 :: resetCtl)) m m₁)
    (hS0 : OptSolR m₀ J) (hW : ∀ J', J = some J' → WalkMem m ∧ J'.idx.next + 1 < 2 ^ 64) :
    JobM pins dn ds J I (m₁.set64 CTL 130 0) a' := by
  have hA := loArr_scr
  have hCl := loCtl_drop
  have h7 : MemFrame [] [130] m₁ (m₁.set64 CTL 130 0) := MemFrame.setCtl _ _ _
  have e7 : ∀ x : Word, x ≠ 130 → rdW ((m₁.set64 CTL 130 0).arr64 CTL) x = rdW (m₁.arr64 CTL) x :=
    fun x hx => h7.ctl x (by simpa using hx)
  have eA7 : ∀ b : TieredArray, b ≠ CTL → (m₁.set64 CTL 130 0).arr64 b = m₁.arr64 b :=
    fun b hb => Mem.arr64_set64_ne _ _ _ _ _ hb
  have hiw : L.Ind.IWOK m₁ := iwOK_frameLo hA hCl hf hR.iw
  -- the stream index, from the job's start
  have hidx : ∀ b : TieredArray, b.hi = false → ((129 ≤ b.arr ∧ b.arr ≤ 134) ∨ b.arr = 137) →
      (m₁.set64 CTL 130 0).arr64 b = m₀.arr64 b := fun b h1 h2 => by
    have hb : b ≠ CTL := fun e => by subst e; revert h2; decide
    rw [eA7 b hb, hA.arr hf (by omega)]
    refine hf0.arr b (fun hm => ?_) hb
    have : IdxArr b = false := by
      rcases List.mem_append.mp hm with h | h
      · exact apA_idx h
      · exact cdA_idx h
    simp only [IdxArr, h1, beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff,
      Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at this
    omega
  have h128 : rdW ((m₁.set64 CTL 130 0).arr64 CTL) 128 = rdW (m₀.arr64 CTL) 128 := by
    rw [e7 _ (by decide), hCl.ctl hf (by decide)]
    exact hf0.ctl _ (fun hm => by
      rcases List.mem_append.mp hm with h | h
      · exact apC_128 h
      · exact cdC_128 h)
  have hE : (m₁.set64 CTL 130 0).arr64 EREC = m.arr64 EREC := by
    rw [eA7 _ (by decide), hA.arr hf (by decide)]
  have h129 : rdW ((m₁.set64 CTL 130 0).arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := by
    rw [e7 _ (by decide), hCl.ctl hf (by decide)]
  have hgrow : ErecGrow m₀ (m₁.set64 CTL 130 0) :=
    ⟨by have := hg.er; simp only [erTop] at this; simp only [erTop, h129]; exact this,
      fun i hi => by rw [hE]; exact hg.erGet i hi,
      by simp [erecTop1, h0], fun i hi => by simp [erecTop1, h0] at hi⟩
  have hI7 : IndexR (m₁.set64 CTL 130 0) I := hI.grow hidx h128 hgrow.ext
  -- the run's solution: its rows from the job's start, the walks' memos from `m`
  have hJS : JSol J (m₁.set64 CTL 130 0) := by
    have hF1 : MemFrame scrArrs (flushCtl ++ (0 :: resetCtl) ++ [130]) m (m₁.set64 CTL 130 0) :=
      (hf.mono (fun _ h => h) (fun _ h => List.mem_append_left _ h)).trans
        (h7.mono (by simp) (fun _ h => List.mem_append_right _ h))
    have hF0 : MemFrame (apA ++ cdA ++ scrArrs) (apC ++ cdC ++ (flushCtl ++ (0 :: resetCtl) ++ [130]))
        m₀ (m₁.set64 CTL 130 0) :=
      (hf0.mono (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h)).trans
        (hF1.mono (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h))
    have hlo : ∀ x ∈ flushCtl ++ (0 :: resetCtl) ++ [130], x.toNat < 200 := fun x hx => by
      rcases List.mem_append.mp hx with h | h
      · have := hCl x h; omega
      · simp only [List.mem_singleton] at h; subst h; decide
    refine ⟨?_, fun J' e => ⟨(hW J' e).1.frame hF1 (hA.not_hi (by decide)) (hA.not_hi (by decide))
      (fun h => by have := hlo _ h; simp at this) (fun h => by have := hlo _ h; simp at this), (hW J' e).2⟩⟩
    exact hS0.growF hF0 (fun b hb => by
        rcases List.mem_append.mp hb with h | h
        · rcases List.mem_append.mp h with h | h
          · exact (apA_jsol h).1
          · exact cdA_sol h
        · exact fun hs => hA.not_hi (by have := solArrs_arr hs; omega) h)
      (fun x hx => by
        rcases List.mem_append.mp hx with h | h
        · rcases List.mem_append.mp h with h | h
          · exact (apC_jsol h).1
          · exact cdC_sol h
        · intro hs; have := hlo x h
          simp only [solCtl, SOLC, SNEXTC, SCNTC, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl | rfl <;> simp at this)
      hgrow
  refine ⟨hC.arena.frameHi h7 (by simp) (by simp), hC.core.frame (by simp [AvoidA]) (by simp [AvoidC]) h7,
    hC.pins.frame (by simp [AvoidA]) h7, hC.mode.frame h7 (by decide) (by decide), hI7, ?_, ?_, ?_,
    IWOK.set130 hiw, ?_, ?_, ?_, ?_, ?_, hfs, ?_, hJS⟩
  · exact (hR.check.env.ownBelow.frameLo hA hCl hf).frame (fun b hb => by simp at hb) (by decide) h7
  · rw [stampW, e7 _ (by decide)]
    have := hR.check.env.stamp; rw [stampW] at this; rw [hCl.ctl hf (by decide)]; exact this
  · rw [eA7 _ (by decide), eA7 _ (by decide)]; exact declsF_frameLo hA hf hR.decls
  · rw [rdW_set64_self _ _ _ _ (by have := hiw.ctl; simp; omega)]
  · have h6 := pinSetsR_frameLo hA hCl hf hR.pinsets
    exact PinSetsR.grow h6 (RecGrow.of_eq (eA7 _ (by decide)) (e7 _ (by decide))) (e7 _ (by decide))
      (e7 _ (by decide))
  · refine ⟨?_, ?_, ?_, (hcm.frameLo hA hCl hf).frame h7 (by simp) (by decide), hT.dnN⟩ <;>
      rw [h7.size, hf.size]
    · exact hT.erec
    · exact hT.spn
    · exact hT.bstk
  · rw [pinW_frame h7 (by simp), pinW_frame hf (hA.not_hi (by decide))]; exact hfl
  · exact (hIM.frameLo hA hCl hf).setCtl 130 0 (by decide)
  · exact ((hFz.frame (fun x hx => (List.mem_append.mp hx).elim apC_frozen cdC_frozen) hf0).frameLo
      hCl hf).frame (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; decide) h7

/-- The program facts the jobs take. -/
structure JobProg (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
    (ds : Array IDeclaration) (p : Prog) : Prop where
  record_job : p.lookup "record_job" = some recordJobL
  check_jobs : p.lookup "check_jobs" = some checkJobsL
  cd : CdProg pins dn ds p
  /-- The bracket (`scratch_enter`, `scratch_drop` and their callees). -/
  br : BracketProg p
  iw_reset : p.lookup "iw_reset" = some L.Ind.iwReset
  /-- `and_pin_ok` and its inductive arm, `rom_and_pin` by its refinement. -/
  andPin : AndPinIndProg p
  rom : ∀ dn vis fe, L.Rom.RomAndPinRef p dn vis fe
  /-- The write sets of `and_pin_ok` and `check_decl`. -/
  apW : ∃ F, "and_pin_ok" ∈ F ∧ closedA p apA apC F = true
  cdW : ∃ F, "check_decl" ∈ F ∧ closedA p cdA cdC F = true
  fromLe : p.lookup "from_le" = some fromLeL

open ConRon.Bridge (IFEnvOK SolView MatesDen) in
/-- **What the jobs take of `check_record_sol`** (the `some` arm of the twin's `checkRecord`; lane
compare's helper H2b proves it at the checker's program): from `check_decl`'s context (`cd_ref`'s
hypotheses) with the solution in memory (`SolR`), the walks' memos (`WalkMem`) and the
solution's index and mates denoting on the twin's side, `check_record_sol(i, vis)` refines
`checkRecord` at the solution, with `check_decl`'s post and the walks' memos after it; and its call
closure writes only where `check_decl`'s may (`cdA`, `cdC`: not the solution's rows and words). -/
structure CrsSpec (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
    (ds : Array IDeclaration) (p : Prog) : Prop where
  ref : FrontDecls ds → DeclsLpsDn dn ds →
    ∀ {N : Nat}, N ≤ 2 ^ 62 + 1 → ∀ {m : Mem} {a : AState} {vis : Word} {fe : IFEnv} {i : Word}
      {J : ISolution} {envS : ConLeche.Env} {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)},
      i.toNat < ds.size → ConRon.Bridge.StateOK a → LoopR pins m a vis fe ds → StageT dn vis fe m a →
      (∃ env, ConRon.Bridge.FoldOK env fe a) →
      (∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x) →
      (∃ pinsP, ConRon.Bridge.PinsDenote a.store pins pinsP) → IndMemos m →
      SolR m J → WalkMem m → IFEnvOK envS (SolView J) a → MatesDen a.store J.mates matesU →
      J.idx.next + 1 < 2 ^ 64 →
      RefE (JobG pins dn ds p ∧ CrsG p J fe ds i a) (callE p N "check_record_sol" [i, vis] m)
        (checkRecord V pins (some J) fe (dsAt ds i)) a
        (fun v x a' => CdPost pins ds m (v.1.headD 0) x v.2 a' ∧ WalkMem v.2)
  wr : ∃ F, "check_record_sol" ∈ F ∧ closedA p cdA cdC F = true

/-- The jobs' `check_record_sol` facts, needed only with a solution. -/
def CrsFor (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
    (ds : Array IDeclaration) (p : Prog) (J : Option ISolution) : Prop :=
  J.isSome → CrsSpec pins dn ds p

/-- **What a job's error claims assume of the run's solution**, at the job's start `a` (nothing
without one): the justification's verdict context and no-verdict closure (`CrsG`), and at an axiom
record the twin's justification guard (`JwGuard`) at the state the `And` pin leaves after the
bracket's entry (the state `check_record_sol` starts from). -/
def JobGs (p : Prog) (J : Option ISolution) (I : IStreamIndex) (ds : Array IDeclaration) (k : Nat)
    (a : AState) : Prop :=
  match J with
  | none => True
  | some J => VerdictCtxU p ∧ closedNV p jfNvFns = true ∧
      ∀ cv, ds[k]? = some (.axiomDecl cv) → ∀ a₁ b a₄, enterScratch.run a = .ok ((), a₁) →
        (andPinOk (.axiomDecl cv)).run a₁ = .ok (b, a₄) →
        JwGuard J (I.view k) (.axiomDecl cv) cv a₄

/-- A job's error guard: the jobs' (`JobG`) and the solution's (`JobGs`). -/
abbrev JobGJ (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (p : Prog) (J : Option ISolution) (I : IStreamIndex) (k : Nat) (a : AState) : Prop :=
  JobG pins dn ds p ∧ JobGs p J I ds k a

/-- The jobs' loop's error guard: the solution's at every job. -/
abbrev JobGL (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (p : Prog) (J : Option ISolution) (I : IStreamIndex) : Prop :=
  JobG pins dn ds p ∧ ∀ k a, JobGs p J I ds k a

/-- The flat loop's guard is the jobs'. -/
theorem JobGL.none {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {p : Prog} {I : IStreamIndex} (h : JobG pins dn ds p) :
    JobGL pins dn ds p none I := ⟨h, fun _ _ => trivial⟩

/-- A weaker guard (the error branch's assumption) refines alike. -/
theorem RefE.jobsGuard {α β : Type} {G G' : Prop} {x : Except Err α} {T : AM β} {a : AState}
    {R : α → β → AState → Prop} (hG : G → G') (h : RefE G' x T a R) : RefE G x T a R := by
  cases x with
  | ok v => exact h
  | error e => exact fun g => h (hG g)

/-! ## `record_job` -/

/-- **`record_job`'s model refines `recordJob` of record `k`, both outcomes** (`recordJob_ref`
through the model's spec). -/
theorem recordJobE_ref {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} {p : Prog} {J : Option ISolution} {I : IStreamIndex}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) (hdn : DnPers dn)
    (hpp : ConRon.Bridge.PersPinSets pins)
    {N : Nat} (hN : N ≤ 2 ^ 62) {m : Mem} {a : AState} {k : Word} (hk : k.toNat < ds.size)
    (hJ : JobR pins dn ds J I m a) (hrec : JobSpec pins pinsP J a) (hcrs : CrsFor pins dn ds p J)
    (hF : ∃ env, ConRon.Bridge.FoldOK env (I.view k.toNat) (AM.st enterScratch a))
    (hden : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x ∧ ∃ d, Frontend.denoteDecl a.store x = some d)
    (hPD : ConRon.Bridge.PinsDenote a.store pins pinsP) :
    RefE (JobGJ pins dn ds p J I k.toNat a) (recordJobE p N m k) (recordJob V pins J I k.toNat ds[k.toNat])
      a (fun v _ a' => JobPost pins dn ds J I a v.2 a') := by
  rcases N with _ | n
  · exact RefE.of_cls0 Err.cls_outOfFuel
  have hnv : ∀ {f : FnName}, f ∈ L.Checker.nvFns → JobGJ pins dn ds p J I k.toNat a →
      ∀ {T : AM Unit} {b : AState}
      {vs : List Word} {m₀ : Mem} {e : Err}, callE p n f vs m₀ = .error e → ErrClaim T b e :=
    fun hf hG _ _ _ _ _ c => ErrClaim.of_callE_nv hG.1.nv hf c
  obtain ⟨hpd, d, hd⟩ := hden _ (Array.getElem_mem_toList hk)
  obtain ⟨env, hF1⟩ := hF
  have hx1 := ConRon.Bridge.PExt.enterScratch hJ.state.wf
  have hok1 : ConRon.Bridge.StateOK (AM.st enterScratch a) := by
    rw [enterScratch_st]; exact ⟨EStore.enableScratch_wf hJ.state.wf⟩
  have hd1 : Frontend.denoteDecl (AM.st enterScratch a).store ds[k.toNat] = some d := by
    rw [enterScratch_st]; exact ConRon.Bridge.denoteDecl_pext hx1 hpd hd
  have hPD1 : ConRon.Bridge.PinsDenote (AM.st enterScratch a).store pins pinsP := by
    rw [enterScratch_st]; exact ConRon.Bridge.PinsDenote.pmono hx1 pins pinsP hpp hPD
  show RefE _ (recordJobE.k_scratch_enter p n k (callE p n "scratch_enter" [] m))
    (enterScratch >>= fun _ => recordCheck V pins J I k.toNat ds[k.toNat] >>= fun _ => dropScratch) a _
  -- `scratch_enter`
  rcases c1 : callE p n "scratch_enter" [] m with e | ⟨r1, m1⟩
  · exact fun hG => ErrClaim.bind_left (hnv (_root_.L.Checker.nv_mem (by decide)) hG c1)
  obtain ⟨s1, hs1, -, hlo, h62, c₁, c₂, c₃, c₄, hpt, hm1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (scratchEnter_spec p hP.br.se hP.br.sr hP.br.bm hP.br.lf hP.br.im hP.br.fm n ⟨m, Locals.init []⟩)
    (callW_of_callE c1)
  rw [hs1] at hm1; subst hm1
  have hJ1 := hJ.enter hdn hlo h62 c₁ c₂ c₃ c₄ hpt
  obtain ⟨-, hst1, -⟩ := AM.of_run_ok _ _ _ _ (enterScratch_run a)
  refine RefE.bind_right (enterScratch_run a) ?_
  rw [hst1] at hJ1 hok1 hd1 hPD1 hF1
  have hx1' : ConRon.Bridge.PExt a.store (EStore.reset a.store true) := hx1
  generalize ha1 : ({ store := EStore.reset a.store true, memos := Memos.empty, caches := a.caches, pins := a.pins } : AState) = a1 at hJ1 hok1 hd1 hPD1 hF1
  have hpins1 : a1.pins = a.pins := by rw [← ha1]
  have hx1a : ConRon.Bridge.PExt a.store a1.store := by rw [← ha1]; exact hx1'
  -- `CTL[130] := 0` (tier 1 is empty already), `iw_reset`
  have e130 : (enterMem m).set64 CTL 130 0 = enterMem m := by
    conv => rhs; rw [← set64_rdW_self (enterMem m) CTL 130]
    rw [hJ1.top1]
  rw [recordJobE.k_scratch_enter.arm1]
  rw [e130]
  rcases c2 : callE p n "iw_reset" [] (enterMem m) with e | ⟨r2, m2⟩
  · exact fun hG => hnv (_root_.L.Checker.nv_mem (by decide)) hG c2
  obtain ⟨s2, hs2, -, e2⟩ := triple_of_callW (s₀ := ⟨enterMem m, Locals.init []⟩)
    (iwReset_specW p hP.iw_reset n ⟨enterMem m, Locals.init []⟩) (callW_of_callE c2)
  simp only [iwResetW, Option.some.injEq, Prod.mk.injEq] at e2
  obtain ⟨-, e2⟩ := e2
  have e2' : m2 = (enterMem m).set64 CTL 200 0 := hs2 ▸ e2.symm
  clear c2
  subst e2'
  -- the stamp bump and the view
  generalize hm2 : (enterMem m).set64 CTL 200 0 = m2
  by_cases g1 : 4294967294 ≤ rdW (m2.arr64 CTL) 133
  · rw [recordJobE.k_iw_reset.abort1 p n k r2 m2 g1]; exact RefE.of_cls0 (by decide)
  by_cases g2 : (m2.set64 CTL 133 (rdW (m2.arr64 CTL) 133 + 1)).len64 FIRSTS ≤ k
  · rw [recordJobE.k_iw_reset.abort2 p n k r2 m2 g1 g2]; exact RefE.of_cls0 (by decide)
  rw [recordJobE.k_iw_reset.arm1 p n k r2 m2 g1 g2]
  rw [show ((m2.set64 CTL 133 (rdW (m2.arr64 CTL) 133 + 1)).set64 CTL 134
    (rdW ((m2.set64 CTL 133 (rdW (m2.arr64 CTL) 133 + 1)).arr64 FIRSTS) k)).set64 CTL 135 k =
    jobMem m2 k from rfl]
  -- the literal flags (`from_le` of the frozen thresholds at the record's first counter)
  have hc0 : rdW ((m2.set64 CTL 133 (rdW (m2.arr64 CTL) 133 + 1)).arr64 FIRSTS) k =
      rdW ((enterMem m).arr64 FIRSTS) k := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), ← hm2, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  rw [hc0]
  have hjc : ∀ x : Word, x ≠ 133 → x ≠ 134 → x ≠ 135 → x ≠ 200 →
      rdW ((jobMem m2 k).arr64 CTL) x = rdW ((enterMem m).arr64 CTL) x := fun x h1 h2 h3 h4 => by
    rw [← hm2]; unfold jobMem
    rw [rdW_set_ctl _ 135 _ x (Ne.symm h3), rdW_set_ctl _ 134 _ x (Ne.symm h2),
      rdW_set_ctl _ 133 _ x (Ne.symm h1), rdW_set_ctl _ 200 _ x (Ne.symm h4)]
  rcases c3a : callE p n "from_le" [rdW ((jobMem m2 k).arr64 CTL) 172, rdW ((enterMem m).arr64 FIRSTS) k]
      (jobMem m2 k) with e | ⟨rx, mx⟩
  · exact fun hG => hnv (_root_.L.Checker.nv_mem (by decide)) hG c3a
  obtain ⟨sx, hsx, -, hmx, hrx⟩ := triple_of_callW (s₀ := ⟨jobMem m2 k, Locals.init []⟩)
    (fromLe_refines hP.fromLe n ⟨jobMem m2 k, Locals.init []⟩ _ _) (callW_of_callE c3a)
  have emx : mx = jobMem m2 k := by rw [← hsx, hmx]
  subst emx
  rw [recordJobE.k_from_le.arm1]
  rcases c3b : callE p n "from_le"
      [rdW (((jobMem m2 k).set64 CTL 160 (rx.headD 0)).arr64 CTL) 173, rdW ((enterMem m).arr64 FIRSTS) k]
      ((jobMem m2 k).set64 CTL 160 (rx.headD 0)) with e | ⟨ry, my⟩
  · exact fun hG => hnv (_root_.L.Checker.nv_mem (by decide)) hG c3b
  obtain ⟨sy, hsy, -, hmy, hry⟩ := triple_of_callW (s₀ := ⟨(jobMem m2 k).set64 CTL 160 (rx.headD 0), Locals.init []⟩)
    (fromLe_refines hP.fromLe n ⟨(jobMem m2 k).set64 CTL 160 (rx.headD 0), Locals.init []⟩ _ _)
    (callW_of_callE c3b)
  have emy : my = (jobMem m2 k).set64 CTL 160 (rx.headD 0) := by rw [← hsy, hmy]
  subst emy
  rw [recordJobE.k_from_le_2.arm1]
  rw [show ((jobMem m2 k).set64 CTL 160 (rx.headD 0)).set64 CTL 161 (ry.headD 0) =
    flagsSet (jobMem m2 k) (rx.headD 0) (ry.headD 0) from rfl]
  rw [hjc 172 (by decide) (by decide) (by decide) (by decide)] at hrx
  rw [rdW_set_ctl _ 160 _ 173 (by decide), hjc 173 (by decide) (by decide) (by decide) (by decide)] at hry
  obtain ⟨hS3, htop3⟩ := hJ1.stage hk (by rw [hm2]; exact g1) hrx hry
  rw [hm2] at hS3 htop3
  clear g1 g2
  generalize flagsSet (jobMem m2 k) (rx.headD 0) (ry.headD 0) = m3 at hS3 htop3 ⊢
  -- `and_pin_ok`
  show RefE _ _ ((andPinOk ds[k.toNat] >>= fun b => if b = true then
      (checkRecord V pins J (I.view k.toNat) ds[k.toNat] >>= fun _ => pure ())
      else fail (.invalid "`And` must be the standard `And`")) >>= fun _ => dropScratch) a1 _
  rw [bind_assoc]
  rcases c3 : callE p n "and_pin_ok" [k] m3 with e | ⟨r3, m4⟩
  · exact fun hG => hnv (_root_.L.Checker.nv_mem (by decide)) hG c3
  obtain ⟨b, a4, hrun4, hb, hS4, hgr4, hfr4, hok4, hext4, hc4, hpins4, hF4⟩ :=
    andPin_job hP.andPin hP.rom hP.apW hFD hk hS3 hok1 hF1 hd1 (callW_of_callE c3)
  refine RefE.bind_right hrun4 ?_
  by_cases hz : r3.headD 0 = 0
  · have hbf : b = false := by rw [← hb, hz]; rfl
    subst hbf
    rw [recordJobE.k_and_pin_ok.abort1 _ _ _ _ _ hz]
    exact fun _ => ErrClaim.bind_left
      (ErrClaim.ite_neg (by simp) (ErrClaim.fail_abort _ _ (by decide)))
  have hbt : b = true := by rw [← hb]; simpa using hz
  subst hbt
  simp only [ite_true, bind_assoc, pure_bind]
  have e0 : dsAt ds k = ds[k.toNat] := by simp [dsAt, Array.getD, hk]
  have hpx4 : ConRon.Bridge.PExt a.store a4.store := hx1a.trans (ConRon.Bridge.PExt.of_ext hext4)
  have hR4 : LoopR pins m4 a4 0 (I.view k.toNat) ds := ⟨hS4.stage.check, hS4.decls, hS4.stage.iw, hS4.pinsets⟩
  have hT4 : StageT dn 0 (I.view k.toNat) m4 a4 := ⟨hS4.stage, L.Arena.TwinOK.of_check hF4.check hS4.mem, hS4.flag⟩
  have hden4 : ∃ x, Frontend.denoteDecl a4.store (dsAt ds k) = some x :=
    ⟨d, by rw [e0]; exact ConRon.Bridge.denoteDecl_pext (ConRon.Bridge.PExt.of_ext hext4) hpd hd1⟩
  have hPD4 : ∃ pinsP, ConRon.Bridge.PinsDenote a4.store pins pinsP :=
    ⟨pinsP, ConRon.Bridge.PinsDenote.pmono hpx4 pins pinsP hpp hPD⟩
  -- after the record's check (`check_decl` or `check_record_sol`): `scratch_drop`
  have tail : ∀ (r5 : List Word) (m5 : Mem) (y : IFEnv) (a5 : AState),
      CdPost pins ds m4 (r5.headD 0) y m5 a5 → MemFrame cdA cdC m4 m5 →
      (∀ J', J = some J' → WalkMem m5 ∧ J'.idx.next + 1 < 2 ^ 64) →
      (checkRecord V pins J (I.view k.toNat) ds[k.toNat]).run a4 = .ok (y, a5) →
      RefE (JobGJ pins dn ds p J I k.toNat a) (recordJobE.k_check_record_sol p n (.ok (r5, m5))) dropScratch a5
        (fun v _ a' => JobPost pins dn ds J I a v.2 a') := by
    intro r5 m5 y a5 hP5 hfr5 hW5 hrun5
    -- the twin's record check, accepted
    have hrc : recordCheck V pins J I k.toNat ds[k.toNat] a1 = .ok ((), a5) := by
      show (andPinOk ds[k.toNat] >>= fun b => if b = true then
        (checkRecord V pins J (I.view k.toNat) ds[k.toNat] >>= fun _ => pure ())
        else fail (.invalid "`And` must be the standard `And`")).run a1 = _
      rw [StateT.run_bind, hrun4]
      show (checkRecord V pins J (I.view k.toNat) ds[k.toNat] >>= fun _ => pure ()).run a4 = _
      rw [StateT.run_bind, hrun5]; rfl
    obtain ⟨hst5, hext5, hp5⟩ := hrec.keep hx1a hok1 hF1 hPD1 hd1 hrc
    -- `scratch_drop`
    rw [recordJobE.k_check_record_sol.arm1, recordJobE.j1.arm1]
    rcases c6 : callE p n "scratch_drop" [] m5 with e | ⟨r6, m6⟩
    · exact fun hG => hnv (_root_.L.Checker.nv_mem (by decide)) hG c6
    obtain ⟨s6, hs6, -, -, hC6⟩ := triple_of_callW (s₀ := ⟨m5, Locals.init []⟩)
      (scratchDrop_refinesC p hP.br.sd hP.br.sr hP.br.fl a5 n ⟨m5, Locals.init []⟩ dn (r5.headD 0) y
        hP5.loop.check) (callW_of_callE c6)
    obtain ⟨s6', hs6', -, -, -, -, -, hm6⟩ := triple_of_callW (s₀ := ⟨m5, Locals.init []⟩)
      (scratchDrop_spec p hP.br.sd hP.br.sr hP.br.fl n ⟨m5, Locals.init []⟩) (callW_of_callE c6)
    rw [hs6] at hC6; rw [hs6'] at hm6
    have hf56 : MemFrame scrArrs (flushCtl ++ (0 :: resetCtl)) m5 m6 := by
      rw [hm6]
      exact ((flushMem_frame _).mono (by simp) (fun x h => List.mem_append_left _ h)).trans
        ((resetMemP_frame _ 0).mono (by simp) (fun x h => List.mem_append_right _ h))
    obtain ⟨-, hst6, -⟩ := AM.of_run_ok _ _ _ _ (dropScratch_run a5)
    rw [hst6] at hC6
    rw [recordJobE.k_scratch_drop.arm1]
    refine RefE.ret (dropScratch_run a5) ?_
    have hx6 : ConRon.Bridge.PExt a.store (EStore.reset a5.store false) :=
      (hx1a.trans (ConRon.Bridge.PExt.of_ext hext5)).trans (ConRon.Bridge.PExt.dropScratch hst5.wf)
    have hf35 : MemFrame (apA ++ cdA) (apC ++ cdC) m3 m5 :=
      (hfr4.mono (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h)).trans
        (hfr5.mono (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h))
    have hT5 : TwinMem dn m5 ({ store := EStore.reset a5.store false, memos := a5.memos, caches := Caches.empty, pins := a5.pins } : AState) :=
      ⟨by rw [hfr5.size]; exact hS4.mem.erec, by rw [hfr5.size]; exact hS4.mem.spn,
        by rw [hfr5.size]; exact hS4.mem.bstk, hP5.core,
        fun j x e => hx6.lss.ls.ns j x (hdn j x e) (hJ.mem.dnN j x e)⟩
    refine ⟨⟨JobM.ofDrop hP5.loop hP5.core hP5.ind
        (by rw [pinW_frame hfr5 cdA_pins]; exact hS4.flag) hT5 hJ.fsize hS3.idx hS3.frozen htop3 hf35
        (hgr4.trans hP5.grow) hC6 hf56 hS3.jsol.sol hW5, ⟨EStore.dropScratch_wf hst5.wf⟩, rfl, rfl⟩, hx6, ?_⟩
    show a5.pins = a.pins
    rw [hp5, hpins1]
  cases J with
  | none =>
    -- `check_decl` (the flag is `0`)
    have h224 : rdW (m4.arr64 CTL) 224 = 0 := hS4.jsol.sol
    rw [recordJobE.k_and_pin_ok.arm2 _ _ _ _ _ hz h224]
    have h1 := cd_ref hP.cd hFD hLD (N := n) (by omega) hk hok4 hR4 hT4 ⟨env, hF4⟩ hden4 hPD4 hS4.memos
    rw [e0] at h1
    refine RefE.bindRun (K := recordJobE.k_check_record_sol p n) (fun _ => rfl)
      (checkDecl_specE p hP.cd.cd.cd hP.cd.cd.ckd n ⟨m4, Locals.init []⟩ k 0) (fun hG => hG.1.nv)
      (fun hG => hG.1.cd) h1 ?_
    intro r5 s5 y a5 c5 _ hrun5 hP5
    obtain ⟨F, hF0, hcl⟩ := hP.cdW
    obtain ⟨s5', hs5', hfr5, -⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
      (invoke_memFrame hcl n hF0 [k, 0] ⟨m4, Locals.init []⟩) (callW_of_callE c5)
    rw [hs5'] at hfr5
    exact tail r5 s5.mem y a5 hP5 hfr5 (fun _ h => nomatch h) hrun5
  | some J =>
    -- `check_record_sol` (the flag is `1`)
    have hcs := hcrs rfl
    have h224 : rdW (m4.arr64 CTL) 224 ≠ 0 := by
      have := hS4.jsol.sol.1; simp only [ctlW, SOLC] at this; rw [this]; decide
    rw [recordJobE.k_and_pin_ok.arm1 _ _ _ _ _ hz h224]
    obtain ⟨envS, matesU, -, hall⟩ := hrec
    obtain ⟨hie, hmd, -⟩ := hall a4 hok4 hpx4
    obtain ⟨hWM4, hnx⟩ := hS4.jsol.walk J rfl
    have h1 := hcs.ref hFD hLD (N := n) (by omega) hk hok4 hR4 hT4 ⟨env, hF4⟩ hden4 hPD4 hS4.memos
      hS4.jsol.sol.2 hWM4 hie hmd hnx
    rw [e0] at h1
    -- the solution's guard at the `And` pin's state
    have he1 : enterScratch.run a = .ok ((), a1) := by rw [← ha1]; exact enterScratch_run a
    replace h1 := RefE.jobsGuard (G := JobGJ pins dn ds p (some J) I k.toNat a) (fun hG => by
      obtain ⟨hG1, hv, hjn, hjw⟩ := hG
      refine ⟨hG1, hv, hjn, fun cv hcv => ?_⟩
      have hcv' : ds[k.toNat] = .axiomDecl cv := by
        rw [Array.getElem?_eq_getElem hk] at hcv; exact Option.some.inj hcv
      rw [hcv'] at hrun4
      exact hjw cv hcv _ _ _ he1 hrun4) h1
    rcases c5 : callE p n "check_record_sol" [k, 0] m4 with e | ⟨r5, m5⟩
    · rw [c5] at h1; rw [recordJobE.k_check_record_sol.none]; exact RefE.bind_left h1
    rw [c5] at h1
    obtain ⟨y, a5, hrun5, hP5, hW5⟩ := h1
    obtain ⟨F, hF0, hcl⟩ := hcs.wr
    obtain ⟨s5', hs5', hfr5, -⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
      (invoke_memFrame hcl n hF0 [k, 0] ⟨m4, Locals.init []⟩) (callW_of_callE c5)
    rw [hs5'] at hfr5
    exact RefE.bind_right hrun5 (tail r5 m5 y a5 hP5 hfr5 (fun J' e => by cases e; exact ⟨hW5, hnx⟩) hrun5)

/-- **`record_job(k)` refines `recordJob` of record `k`, both outcomes**: from the job relation and
con-ron's fold invariant at the view of position `k` (as `RecordSpec` takes it), an ok run is the
twin's, with the job relation after it; a failing run claims the twin job's failure. -/
@[refines ConRon.Arena.IStreamIndex.view ConRon.Arena.recordCheck ConRon.Arena.recordJob]
theorem recordJob_ref {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} {p : Prog} {J : Option ISolution} {I : IStreamIndex}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) (hdn : DnPers dn)
    (hpp : ConRon.Bridge.PersPinSets pins)
    {N : Nat} (hN : N ≤ 2 ^ 62) {m : Mem} {a : AState} {k : Word} (hk : k.toNat < ds.size)
    (hJ : JobR pins dn ds J I m a) (hrec : JobSpec pins pinsP J a) (hcrs : CrsFor pins dn ds p J)
    (hF : ∃ env, ConRon.Bridge.FoldOK env (I.view k.toNat) (AM.st enterScratch a))
    (hden : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x ∧ ∃ d, Frontend.denoteDecl a.store x = some d)
    (hPD : ConRon.Bridge.PinsDenote a.store pins pinsP) :
    RefE (JobGJ pins dn ds p J I k.toNat a) (callE p N "record_job" [k] m) (recordJob V pins J I k.toNat ds[k.toNat])
      a (fun v _ a' => JobPost pins dn ds J I a v.2 a') := by
  have hM : RefE (JobGJ pins dn ds p J I k.toNat a) (recordJobE p N m k) (recordJob V pins J I k.toNat ds[k.toNat]) a
      (fun v _ a' => JobPost pins dn ds J I a v.2 a') :=
    recordJobE_ref hP hFD hLD hdn hpp hN hk hJ hrec hcrs hF hden hPD
  rcases c : callE p N "record_job" [k] m with e | ⟨r, m'⟩
  · exact fun hG => RefE.run_err (recordJob_specE p hP.record_job N ⟨m, Locals.init []⟩ k) hG.1.nv hG hM c
  · obtain ⟨s', rfl, -, y, a', hr, hR⟩ :=
      RefE.run_ok (recordJob_specE p hP.record_job N ⟨m, Locals.init []⟩ k) hM c
    exact ⟨y, a', hr, hR⟩

/-! ## `check_jobs` -/

/-- A job accepted at the head of a worker's list: the rest runs from the job's state. -/
theorem checkJobList_cons_ok {pins : List INatOpPinSet} {J : Option ISolution} {I : IStreamIndex} {ds : Array IDeclaration}
    {t : Nat} (ht : t < ds.size) {rest : List Nat} {a a₁ : AState}
    (h : recordJob V pins J I t ds[t] a = .ok ((), a₁)) :
    checkJobList V pins J I ds (t :: rest) a = checkJobList V pins J I ds rest a₁ := by
  simp only [checkJobList, runJob, Array.getElem?_eq_getElem ht, h]

/-- A job failing at the head of a worker's list fails the list. -/
theorem checkJobList_cons_err {pins : List INatOpPinSet} {J : Option ISolution} {I : IStreamIndex} {ds : Array IDeclaration}
    {t : Nat} (ht : t < ds.size) {rest : List Nat} {a : AState} {e : Err}
    (h : ErrClaim (recordJob V pins J I t ds[t]) a e) :
    ErrClaimV (checkJobList V pins J I ds (t :: rest)) a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h hk
  have hce' : recordJob V pins J I t ds[t] a = .error ce := hce
  exact .inr ⟨ce, t, AState.abandoned, by
    show checkJobList V pins J I ds (t :: rest) a = _
    simp only [checkJobList, runJob, Array.getElem?_eq_getElem ht, hce'], hc⟩

theorem range'_cons_word {j hi : Word} (h : j < hi) :
    List.range' j.toNat (hi.toNat - j.toNat) = j.toNat :: List.range' (j + 1).toNat (hi.toNat - (j + 1).toNat) := by
  have hl : j.toNat < hi.toNat := h
  have e : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; have := UInt64.toNat_lt hi; simp; omega
  rw [e, show hi.toNat - j.toNat = (hi.toNat - (j.toNat + 1)) + 1 by omega, List.range'_succ]

/-- **`check_jobs`' loop from job `j` refines `checkJobList` over the jobs `j‥hi - 1`, both
outcomes**, from the job relation, given con-ron's fold invariant at the view of every job the
twin's list reaches (the jobs before it accepted): an ok end is the twin's list accepting, with
the job relation after it; an error claims the list's failure. -/
theorem checkJobsLoop_ref {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} {p : Prog} {J : Option ISolution} {I : IStreamIndex}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) (hdn : DnPers dn)
    (hpp : ConRon.Bridge.PersPinSets pins)
    {a₀ : AState} (hden : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d)
    (hPD : ConRon.Bridge.PinsDenote a₀.store pins pinsP) (hrec : JobSpec pins pinsP J a₀)
    (hcrs : CrsFor pins dn ds p J) {hi : Word} (hhi : hi.toNat ≤ ds.size) :
    ∀ (n : Nat), n ≤ 2 ^ 62 + 1 → ∀ (m : Mem) (a : AState) (j : Word),
      JobPost pins dn ds J I a₀ m a →
      (∀ (t : Nat) (a' : AState), j.toNat ≤ t → t < hi.toNat →
        checkJobList V pins J I ds (List.range' j.toNat (t - j.toNat)) a = .ok (.ok (), a') →
        ∃ env, ConRon.Bridge.FoldOK env (I.view t) (AM.st enterScratch a')) →
      RefC (JobGL pins dn ds p J I) (checkJobsE.loop1 p n m j hi)
        (fun m' => ∃ a', checkJobList V pins J I ds (List.range' j.toNat (hi.toNat - j.toNat)) a =
          .ok (.ok (), a') ∧ JobPost pins dn ds J I a₀ m' a')
        (ErrClaimV (checkJobList V pins J I ds (List.range' j.toNat (hi.toNat - j.toNat))) a) := by
  intro n
  induction n with
  | zero =>
    intro _ m a j _ _
    rw [checkJobsE.loop1.eq_1]
    exact fun _ => ErrClaimV.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
    intro hn m a j hR hG
    by_cases g : j < hi
    · rw [checkJobsE.loop1.arm1 _ _ _ _ _ g]
      have hjt : j.toNat < hi.toNat := g
      have hjk : j.toNat < ds.size := by omega
      have e1 : (j + 1).toNat = j.toNat + 1 := by
        rw [UInt64.toNat_add]; have := UInt64.toNat_lt hi; simp; omega
      rw [range'_cons_word g]
      obtain ⟨hJ, hx, hp⟩ := hR
      have hden' : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x ∧ ∃ d, Frontend.denoteDecl a.store x = some d :=
        fun x hx' => by
          obtain ⟨h1, d, h2⟩ := hden x hx'
          exact ⟨h1, d, ConRon.Bridge.denoteDecl_pext hx h1 h2⟩
      have hPD' := ConRon.Bridge.PinsDenote.pmono hx pins pinsP hpp hPD
      have hF := hG j.toNat a (Nat.le_refl _) hjt (by simp; rfl)
      have hr := recordJob_ref hP hFD hLD hdn hpp (N := n) (by omega) hjk hJ (hrec.pmono hx) hcrs hF hden' hPD'
      cases hc : callE p n "record_job" [j] m with
      | error e =>
        rw [checkJobsE.k_record_job.none]
        rw [hc] at hr
        exact fun hg => checkJobList_cons_err hjk (hr ⟨hg.1, hg.2 _ _⟩)
      | ok q =>
        obtain ⟨r, m₁⟩ := q
        rw [checkJobsE.k_record_job.arm1]
        rw [hc] at hr
        obtain ⟨u, a₁, hrun, hJ₁, hx₁, hp₁⟩ := hr
        have hrun' : recordJob V pins J I j.toNat ds[j.toNat] a = .ok ((), a₁) := by cases u; exact hrun
        have hcons := fun rest => checkJobList_cons_ok (pins := pins) (I := I) hjk (rest := rest) hrun'
        have hR₁ : JobPost pins dn ds J I a₀ m₁ a₁ := ⟨hJ₁, hx.trans hx₁, hp₁.trans hp⟩
        have hG₁ : ∀ (t : Nat) (a' : AState), (j + 1).toNat ≤ t → t < hi.toNat →
            checkJobList V pins J I ds (List.range' (j + 1).toNat (t - (j + 1).toNat)) a₁ = .ok (.ok (), a') →
            ∃ env, ConRon.Bridge.FoldOK env (I.view t) (AM.st enterScratch a') := by
          intro t a' h1 h2 h3
          refine hG t a' (by omega) h2 ?_
          rw [show t - j.toNat = (t - (j.toNat + 1)) + 1 by omega, List.range'_succ, hcons, ← e1]
          exact h3
        refine RefC.mono (ih (by omega) m₁ a₁ (j + 1) hR₁ hG₁)
          (fun m' ⟨a', h1, h2⟩ => ⟨a', (hcons _).trans h1, h2⟩) (fun e _ hc hk => ?_)
        rcases hc hk with ⟨ce, h, hc'⟩ | ⟨ce, i, a', h, hc'⟩
        · exact .inl ⟨ce, (hcons _).trans h, hc'⟩
        · exact .inr ⟨ce, i, a', (hcons _).trans h, hc'⟩
    · rw [checkJobsE.loop1.arm2 _ _ _ _ _ g]
      have : hi.toNat - j.toNat = 0 := by have : ¬ j.toNat < hi.toNat := g; omega
      rw [this]
      exact ⟨a, rfl, hR⟩

/-- **An accepted `check_jobs` loop is the twin's list on every prefix whose views hold `FoldOK`**:
if the loop from job `j` returns, then for every `t` in `j‥hi`, given con-ron's fold invariant at
the views of the jobs `j‥t - 1` the twin's list reaches, the twin's list over `j‥t - 1` accepts
with the job relation after it. (The pool's induction over positions, `pooled_fold`, needs the
prefixes: a job's view holds `FoldOK` once every job below it is accepted.) -/
theorem checkJobsLoop_pre {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} {p : Prog} {J : Option ISolution} {I : IStreamIndex}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) (hdn : DnPers dn)
    (hpp : ConRon.Bridge.PersPinSets pins)
    {a₀ : AState} (hden : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d)
    (hPD : ConRon.Bridge.PinsDenote a₀.store pins pinsP) (hrec : JobSpec pins pinsP J a₀)
    (hcrs : CrsFor pins dn ds p J) {hi : Word} (hhi : hi.toNat ≤ ds.size) :
    ∀ (n : Nat), n ≤ 2 ^ 62 + 1 → ∀ (m : Mem) (a : AState) (j : Word) (q : Mem),
      JobPost pins dn ds J I a₀ m a → checkJobsE.loop1 p n m j hi = .ok q →
      ∀ t, j.toNat ≤ t → t ≤ hi.toNat →
      (∀ (t' : Nat) (a' : AState), j.toNat ≤ t' → t' < t →
        checkJobList V pins J I ds (List.range' j.toNat (t' - j.toNat)) a = .ok (.ok (), a') →
        ∃ env, ConRon.Bridge.FoldOK env (I.view t') (AM.st enterScratch a')) →
      ∃ m' a', checkJobList V pins J I ds (List.range' j.toNat (t - j.toNat)) a = .ok (.ok (), a') ∧
        JobPost pins dn ds J I a₀ m' a' := by
  intro n
  induction n with
  | zero =>
    intro _ m a j q _ hq
    rw [checkJobsE.loop1.eq_1] at hq; cases hq
  | succ n ih =>
    intro hn m a j q hR hq t hjt hth hG
    by_cases ht : t = j.toNat
    · subst ht; exact ⟨m, a, by simp; rfl, hR⟩
    have g : j < hi := UInt64.lt_iff_toNat_lt.mpr (by omega)
    rw [checkJobsE.loop1.arm1 _ _ _ _ _ g] at hq
    have hjt' : j.toNat < hi.toNat := g
    have hjk : j.toNat < ds.size := by omega
    have e1 : (j + 1).toNat = j.toNat + 1 := by
      rw [UInt64.toNat_add]; have := UInt64.toNat_lt hi; simp; omega
    obtain ⟨hJ, hx, hp⟩ := hR
    have hden' : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x ∧ ∃ d, Frontend.denoteDecl a.store x = some d :=
      fun x hx' => by
        obtain ⟨h1, d, h2⟩ := hden x hx'
        exact ⟨h1, d, ConRon.Bridge.denoteDecl_pext hx h1 h2⟩
    have hPD' := ConRon.Bridge.PinsDenote.pmono hx pins pinsP hpp hPD
    have hF := hG j.toNat a (Nat.le_refl _) (by omega) (by simp; rfl)
    have hr := recordJob_ref hP hFD hLD hdn hpp (N := n) (by omega) hjk hJ (hrec.pmono hx) hcrs hF hden' hPD'
    cases hc : callE p n "record_job" [j] m with
    | error e => rw [hc, checkJobsE.k_record_job.none] at hq; cases hq
    | ok q1 =>
      obtain ⟨r, m₁⟩ := q1
      rw [hc, checkJobsE.k_record_job.arm1] at hq
      rw [hc] at hr
      obtain ⟨u, a₁, hrun, hJ₁, hx₁, hp₁⟩ := hr
      have hrun' : recordJob V pins J I j.toNat ds[j.toNat] a = .ok ((), a₁) := by cases u; exact hrun
      have hcons := fun rest => checkJobList_cons_ok (pins := pins) (I := I) hjk (rest := rest) hrun'
      have hR₁ : JobPost pins dn ds J I a₀ m₁ a₁ := ⟨hJ₁, hx.trans hx₁, hp₁.trans hp⟩
      obtain ⟨m', a', h1, h2⟩ := ih (by omega) m₁ a₁ (j + 1) q hR₁ hq t (by omega) hth
        (fun t' a' h1 h2 h3 => hG t' a' (by omega) h2 (by
          rw [show t' - j.toNat = (t' - (j.toNat + 1)) + 1 by omega, List.range'_succ, hcons, ← e1]
          exact h3))
      refine ⟨m', a', ?_, h2⟩
      rw [show t - j.toNat = (t - (j.toNat + 1)) + 1 by omega, List.range'_succ, hcons, ← e1]
      exact h1

/-- **`check_jobs(j, hi)` refines `checkJobList` over the jobs `j‥hi - 1`, both outcomes**
(`checkJobsLoop_ref` through the function's model). -/
@[refines ConRon.Arena.checkJobList ConRon.Arena.runJob]
theorem checkJobs_ref {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} {p : Prog} {J : Option ISolution} {I : IStreamIndex}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) (hdn : DnPers dn)
    (hpp : ConRon.Bridge.PersPinSets pins)
    {a₀ : AState} (hden : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d)
    (hPD : ConRon.Bridge.PinsDenote a₀.store pins pinsP) (hrec : JobSpec pins pinsP J a₀)
    (hcrs : CrsFor pins dn ds p J) {hi : Word} (hhi : hi.toNat ≤ ds.size)
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {j : Word}
    (hR : JobPost pins dn ds J I a₀ m a)
    (hG : ∀ (t : Nat) (a' : AState), j.toNat ≤ t → t < hi.toNat →
        checkJobList V pins J I ds (List.range' j.toNat (t - j.toNat)) a = .ok (.ok (), a') →
        ∃ env, ConRon.Bridge.FoldOK env (I.view t) (AM.st enterScratch a')) :
    RefC (JobGL pins dn ds p J I) (checkJobsE p n m j hi)
      (fun v => ∃ a', checkJobList V pins J I ds (List.range' j.toNat (hi.toNat - j.toNat)) a =
        .ok (.ok (), a') ∧ JobPost pins dn ds J I a₀ v.2 a')
      (ErrClaimV (checkJobList V pins J I ds (List.range' j.toNat (hi.toNat - j.toNat))) a) := by
  rcases n with _ | n
  · exact fun _ => ErrClaimV.of_cls0 Err.cls_outOfFuel
  have h := checkJobsLoop_ref hP hFD hLD hdn hpp hden hPD hrec hcrs hhi (n + 1) (by omega) m a j hR hG
  show RefC _ (checkJobsE.k_loop1 p (checkJobsE.loop1 p (n + 1) m j hi)) _ _
  cases e : checkJobsE.loop1 p (n + 1) m j hi with
  | error ε => rw [e] at h; exact h
  | ok m' => rw [e] at h; exact h

end L.Arena
