module

public import ConAgua.Arena.DeclCheckT
public import ConAgua.Arena.IndexBuild
public import ConAgua.Arena.TwinStep
public import ConAgua.Arena.ScratchRefine
public import ConAgua.Arena.DeclPins
public import ConRon.Bridge.Checker.Pooled
import ConAgua.Census.Attr
import ConAgua.Arena.WalkScopeRefine
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

* `TwinOK.ofCheck`: the twin's invariants `TwinOK` at an environment from con-ron's `CheckOK`
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

/-- A name handle with a view reads back (well-formed name store). -/
theorem denoteN_some {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk) :
    ∀ (n : Nat) (i : NIdx), rk i < n → (st.view i).isSome = true → ∃ x, denoteN st i = some x := by
  intro n
  induction n with
  | zero => intro i hn; omega
  | succ n ih =>
    intro i hn hv
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
    rw [denoteN_unfold h hv']
    cases v with
    | anonymous => exact ⟨_, rfl⟩
    | str q t =>
      have hc := h.childOK i _ hv' q (by simp [NNodeView.children])
      obtain ⟨a, ha⟩ := ih q (by omega) hc.1
      exact ⟨_, by simp [denoteNView, ha]; rfl⟩
    | num q k =>
      have hc := h.childOK i _ hv' q (by simp [NNodeView.children])
      obtain ⟨a, ha⟩ := ih q (by omega) hc.1
      exact ⟨_, by simp [denoteNView, ha]; rfl⟩

/-- A level handle with a view reads back (well-formed level store). -/
theorem denoteL_some {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) :
    ∀ (n : Nat) (i : LIdx), rk i < n → (st.view i).isSome = true → ∃ x, denoteL st i = some x := by
  intro n
  induction n with
  | zero => intro i hn; omega
  | succ n ih =>
    intro i hn hv
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
    rw [denoteL_unfold h hv']
    cases v with
    | zero => exact ⟨_, rfl⟩
    | succ u =>
      have hc := h.childOK i _ hv' u (by simp [LNodeView.lchildren])
      obtain ⟨a, ha⟩ := ih u (by omega) hc.1
      exact ⟨_, by simp [denoteLView, ha]; rfl⟩
    | max u w =>
      have hc := h.childOK i _ hv' u (by simp [LNodeView.lchildren])
      have hc' := h.childOK i _ hv' w (by simp [LNodeView.lchildren])
      obtain ⟨a, ha⟩ := ih u (by omega) hc.1
      obtain ⟨b, hb⟩ := ih w (by omega) hc'.1
      exact ⟨_, by simp [denoteLView, ha, hb, opt2]; rfl⟩
    | imax u w =>
      have hc := h.childOK i _ hv' u (by simp [LNodeView.lchildren])
      have hc' := h.childOK i _ hv' w (by simp [LNodeView.lchildren])
      obtain ⟨a, ha⟩ := ih u (by omega) hc.1
      obtain ⟨b, hb⟩ := ih w (by omega) hc'.1
      exact ⟨_, by simp [denoteLView, ha, hb, opt2]; rfl⟩
    | param nm =>
      have hc := h.nchildOK i _ hv' nm (by simp [LNodeView.nchildren])
      obtain ⟨rkN, hN⟩ := h.ns
      obtain ⟨x, hx⟩ := denoteN_some hN _ nm (Nat.lt_succ_self _) hc.1
      exact ⟨_, by simp [denoteLView, hx]; rfl⟩

/-- A level list whose members have views reads back. -/
theorem denoteLList_some {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) :
    ∀ (us : List LIdx), (∀ u ∈ us, (st.view u).isSome = true) → ∃ xs, denoteLList st us = some xs
  | [], _ => ⟨[], rfl⟩
  | u :: us, hu => by
    obtain ⟨x, hx⟩ := denoteL_some h _ u (Nat.lt_succ_self _) (hu u (by simp))
    obtain ⟨xs, hxs⟩ := denoteLList_some h us (fun v hv => hu v (by simp [hv]))
    exact ⟨x :: xs, by simp [denoteLList, hx, hxs, opt2]⟩

/-- A denoting rule list's level-firing rules' levels read back. -/
theorem denoteRules_levels {st : EStore} :
    ∀ {rs : List IRecRule} {xs : List ConLeche.RecRule},
      ConRon.Arena.Frontend.denoteRules st rs = some xs →
      ∀ r ∈ rs, ∀ lvls, r.fire = .levels lvls → ∀ u ∈ lvls, ∃ L, denoteL st.ls u = some L
  | [], _, _, r, hr, _, _, _, _ => absurd hr (by simp)
  | q :: qs, xs, h, r, hr, lvls, hf, u, hu => by
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
          | none => rw [h3] at h1; simp at h1
          | some ls => exact denoteLList_mem h3 u hu
        · exact denoteRules_levels h2 r hr lvls hf u hu

/-- **`TwinOK` from con-ron's check invariant** (`CheckOK`: the store's well-formedness, the
caches, the pins, the environment index) and the memory's half. -/
theorem TwinOK.ofCheck {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {fe : IFEnv}
    {env : ConLeche.Env} (hok : ConRon.Bridge.CheckOK false env fe a) (hm : TwinMem dn m a) :
    TwinOK dn m a fe := by
  obtain ⟨rk, hw⟩ := hok.state.wf
  have hLs := hw.lss
  obtain ⟨rkL, hL⟩ := hLs.ls
  have hLA : ∀ u : LIdx, (a.store.ls.view u).isSome → ∃ l, denoteL a.store.ls u = some l :=
    fun u hu => denoteL_some hL _ u (Nat.lt_succ_self _) hu
  have hLsA : ∀ us : LsIdx, (a.store.lss.view us).isSome → ∃ ls, denoteLs a.store.lss us = some ls := by
    intro us hus
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hus
    obtain ⟨xs, hxs⟩ := denoteLList_some hL vs (fun c hc => (hLs.lchildOK us vs hvs c hc).1)
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  have hc := hok.caches
  have hp := hok.pins
  refine ⟨hc.readL, hc.readLs, ?_, hm.erec, hm.spn, hm.memos, hm.bstk, ?_⟩
  · exact hL.ns
  refine ⟨fun x u hv => hLA u (hw.lchildOK x _ hv u (by simp [ENodeView.lchildren])).1,
    fun x c us hv => hLsA us (hw.lschildOK x _ hv us (by simp [ENodeView.lschildren])).1,
    ⟨_, hp.zeroLevel⟩, ⟨_, hp.emptyLevels⟩, hc.readN, fun c ci hf => ?_, fun c tbl hf => ?_, hLA,
    hLsA, hm.dnN, fun c cv mI rP isK rules hf r hr lvls pins hfi u hu => ?_,
    fun c cv mI rP isK rules hf r hr lvls hfi u hu => ?_⟩
  · obtain ⟨-, d, -, hd, -⟩ := hok.ienv.hit c ci hf
    obtain ⟨y, hy⟩ := denoteCI_cv hd
    exact denoteCV_lps hy
  · obtain ⟨-, pt, -, hpt, -⟩ := hok.ienv.tblHit c tbl hf
    unfold ConRon.Arena.Frontend.denoteProjTable at hpt
    cases h2 : ConRon.Arena.Frontend.denoteNList a.store.ns tbl.levelParams with
    | some ks => exact ⟨ks, denoteNList_mapM h2⟩
    | none => rw [h2] at hpt; split at hpt <;> simp_all
  · obtain ⟨-, d, -, hd, -⟩ := hok.ienv.hit c _ hf
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    cases h2 : ConRon.Arena.Frontend.denoteRules a.store rules with
    | none => rw [h2] at hd; split at hd <;> simp_all
    | some ys => exact denoteRules_mem h2 r hr lvls pins hfi u hu
  · obtain ⟨-, d, -, hd, -⟩ := hok.ienv.hit c _ hf
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    cases h2 : ConRon.Arena.Frontend.denoteRules a.store rules with
    | none => rw [h2] at hd; split at hd <;> simp_all
    | some ys => exact denoteRules_levels h2 r hr lvls hfi u hu

/-! ## `record_job`'s model -/

/-- **`record_job`'s unified model**: the bracket and the leaves (outside the verdict closure)
through their runs, `check_decl` by its unified model. -/
l_model recordJob_specE (p : Prog) (hf : p.lookup "record_job" = some recordJobL)
    (hcd : p.lookup "check_decl" = some checkDeclL)
  fns [hf ↦ recordJobE] specs [checkDecl_specE p hcd n]
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

/-! ## The job relation -/

open L.Front (DECL DLP DeclsF)

local notation "V" => ConLeche.CheckMode.verified

/-- **The memory's half of the job relation**, against the worker's twin state `a` and the
stream index `I`: the checker state without an environment (the arena, the caches, the pins, the
mode), the stream index (`IndexR`), every own row below the stamp (`OwnBelow`, so the next job's
stamp bump empties the own layer), the front's records, the pools in bounds with tier 1 empty,
the pin variants, the memory's half of `TwinOK`, the pin flag, the inductive memos. -/
structure JobM (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (I : IStreamIndex) (m : Mem) (a : AState) : Prop where
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

/-- **What a worker's memory keeps between two jobs**: the memory's half (`JobM`), and on the
twin side the store well formed with the scratch tier off and the caches empty. -/
structure JobR (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (I : IStreamIndex) (m : Mem) (a : AState) : Prop extends JobM pins dn ds I m a where
  state : ConRon.Bridge.StateOK a
  off : a.store.scratchOn = false
  caches : a.caches = Caches.empty

/-- The program facts the jobs take. -/
structure JobProg (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
    (ds : Array IDeclaration) (p : Prog) : Prop where
  record_job : p.lookup "record_job" = some recordJobL
  check_jobs : p.lookup "check_jobs" = some checkJobsL
  cd : CdProg pins dn ds p

/-- What the jobs' error claims assume: `check_decl`'s (`CdG`), and the callees outside the
verdict closure claim nothing. -/
structure JobG (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
    (ds : Array IDeclaration) (p : Prog) : Prop where
  cd : CdG pins dn ds p
  nv : closedNV p L.Checker.nvFns = true

/-- What a job keeps, beside the relation: the store a persistent extension, the pins. -/
def JobPost (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (I : IStreamIndex) (a : AState) (m' : Mem) (a' : AState) : Prop :=
  JobR pins dn ds I m' a' ∧ ConRon.Bridge.PExt a.store a'.store ∧ a'.pins = a.pins

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
      hC.not_mid (by decide) (by decide)⟩

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

end lo

/-- The decoder names only persistent handles (its names survive the scratch bracket). -/
def DnPers (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → k.isPersistent = true

/-- **`scratch_enter` from the job relation**: the memory's half at the bracket's memory and the
twin's state with the scratch tier on. -/
theorem JobR.enter {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {I : IStreamIndex} {m : Mem} {a : AState}
    (hJ : JobR pins dn ds I m a) (hdn : DnPers dn)
    (hlo : (rdW ((preMem m).arr64 CTL) SCB).toNat < 2 ^ 47 - 2 ^ 33)
    (h62 : SCB.toNat < ((preMem m).arr64 CTL).size)
    (c1 : rdW ((resetMem (preMem m) 1).arr64 CTL) bmSch.cs + 2 ≠ 0)
    (c2 : rdW ((mclearG bmSch (resetMem (preMem m) 1)).arr64 CTL) lfSch.cs + 2 ≠ 0)
    (c3 : rdW ((mclearG lfSch (mclearG bmSch (resetMem (preMem m) 1))).arr64 CTL) imSch.cs + 2 ≠ 0)
    (c4 : rdW ((mclearG imSch (mclearG lfSch (mclearG bmSch (resetMem (preMem m) 1)))).arr64 CTL)
      frSch.cs + 2 ≠ 0)
    (hpt : (resetMemA (preMem m) 1).top >>> 40 = 0 ∨ (1 : Word) = 0 → 0 < ((resetMemA (preMem m) 1).arr64 PT0).size) :
    JobM pins dn ds I (enterMem m) (AM.st enterScratch a) := by
  have hf := enterMem_frame m
  have hA := loArr_scr
  have hC := loCtl_enter
  obtain ⟨-, hst, -⟩ := AM.of_run_ok _ _ _ _ (enterScratch_run a)
  have hx := ConRon.Bridge.PExt.enterScratch hJ.state.wf
  refine ⟨?_, ?_, ?_, modeOK_enterMem _ h62, hJ.idx.frameLo hA hC hf, hJ.below.frameLo hA hC hf,
    by rw [stampW_frameLo hC hf]; exact hJ.stamp, declsF_frameLo hA hf hJ.decls, iwOK_frameLo hA hC hf hJ.iw,
    by rw [hC.ctl hf (by decide)]; exact hJ.top1, pinSetsR_frameLo hA hC hf hJ.pinsets,
    hJ.mem.frameLo hA hC hf fun k x e => ?_, by rw [pinW_frame hf (hA.not_hi (by decide))]; exact hJ.flag,
    hJ.memos.frameLo hA hC hf, hJ.fsize⟩
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

/-- `iw_reset` keeps the pool's bounds (its top moves to `0`). -/
theorem IWOK.reset {m : Mem} (h : L.Ind.IWOK m) : L.Ind.IWOK (m.set64 CTL 200 0) := by
  have h := (IWOK_iff m).mp h
  have hne : ∀ b : TieredArray, b ≠ CTL → (m.set64 CTL 200 0).arr64 b = m.arr64 b :=
    fun b hb => Mem.arr64_set64_ne _ _ _ _ _ hb
  rw [IWOK_iff]
  simp only [iwTop, erTop, erecTop1, rdW_set_ctl m 200 0 129 (by decide),
    rdW_set_ctl m 200 0 130 (by decide), hne IW (by decide), hne EREC (by decide),
    hne (tier1 EREC) (by decide), Mem.size_arr64_set64]
  refine ⟨by rw [rdW_set64, if_pos ⟨rfl, rfl, by simpa using h.2.2.2.2.1⟩]; simp, h.2.1, h.2.2.1,
    h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem envArrs_ne_ctl : ∀ b ∈ envArrs, b ≠ CTL := by decide

/-- **What a job's callees start from**, at position `k` with the twin's state `a`: the stage
relation at the view of `k` and the memory's other job facts. -/
structure JobS (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (I : IStreamIndex) (k : Nat) (m : Mem) (a : AState) : Prop where
  stage : StageR 0 (I.view k) m a
  decls : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds
  pinsets : L.Rom.PinSetsR m pins
  mem : TwinMem dn m a
  flag : pinW m 0 ≠ 0
  memos : IndMemos m
  idx : IndexR m I
  top1 : rdW (m.arr64 CTL) 130 = 0

/-- **The job's start**: from the memory's half of the job relation (after the bracket's opening),
`iw_reset` and the stamp bump (the record's view: `CTL[134]` its first counter from `FIRSTS`,
`CTL[135]` its position) give the stage relation at the view of position `k`, with an empty own
layer (every row's stamp is below the new one). -/
theorem JobM.stage {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {I : IStreamIndex} {m : Mem} {a : AState} {k : Word}
    (h : JobM pins dn ds I m a) (hk : k.toNat < ds.size)
    (hst : ¬ 4294967294 ≤ rdW ((m.set64 CTL 200 0).arr64 CTL) 133) :
    JobS pins dn ds I k.toNat (jobMem (m.set64 CTL 200 0) k) a := by
  have hsz : 200 < (m.arr64 CTL).size := h.iw.ctl
  generalize hm2 : m.set64 CTL 200 0 = m2 at hst
  have hf2 : MemFrame [] [200] m m2 := hm2 ▸ MemFrame.setCtl m 200 0
  have e2 : ∀ x : Word, x ≠ 200 → rdW (m2.arr64 CTL) x = rdW (m.arr64 CTL) x := fun x hx =>
    hf2.ctl x (by simpa using hx)
  generalize hst' : rdW (m2.arr64 CTL) 133 = st at hst
  generalize hm3 : jobMem m2 k = m3
  have hsz2 : (m2.arr64 CTL).size = (m.arr64 CTL).size := hf2.size CTL
  have hf3 : MemFrame [] [133, 134, 135] m2 m3 := by
    rw [← hm3]; unfold jobMem
    exact (((MemFrame.setCtl _ 133 _).mono (by simp) (by simp)).trans
      ((MemFrame.setCtl _ 134 _).mono (by simp) (by simp))).trans
      ((MemFrame.setCtl _ 135 _).mono (by simp) (by simp))
  have hf : MemFrame [] [200, 133, 134, 135] m m3 :=
    (hf2.mono (by simp) (by simp)).trans (hf3.mono (by simp) (by simp))
  have hC : ∀ x ∈ ([200, 133, 134, 135] : List Word), x = 200 ∨ x = 133 ∨ x = 134 ∨ x = 135 := by
    simp
  have eA : ∀ b : TieredArray, b ≠ CTL → m3.arr64 b = m.arr64 b := fun b hb => hf.arr b (by simp) hb
  have eC : ∀ x : Word, x ≠ 200 → x ≠ 133 → x ≠ 134 → x ≠ 135 →
      rdW (m3.arr64 CTL) x = rdW (m.arr64 CTL) x := fun x h1 h2 h3 h4 =>
    hf.ctl x (by simp [h1, h2, h3, h4])
  -- the three words
  have hlt : ∀ x : Word, x.toNat ≤ 200 → x.toNat < (m2.arr64 CTL).size := fun x hx => by omega
  have v133 : rdW (m3.arr64 CTL) 133 = st + 1 := by
    rw [← hm3]; unfold jobMem
    rw [rdW_set_ctl _ 135 _ 133 (by decide), rdW_set_ctl _ 134 _ 133 (by decide),
      rdW_set64_self _ _ _ _ (hlt 133 (by decide)), hst']
  have v134 : rdW (m3.arr64 CTL) 134 = rdW (m.arr64 FIRSTS) k := by
    rw [← hm3]; unfold jobMem
    rw [rdW_set_ctl _ 135 _ 134 (by decide), rdW_set64_self _ _ _ _ (by rw [Mem.size_arr64_set64]; exact hlt 134 (by decide)),
      Mem.arr64_set64_ne _ _ _ _ _ (by decide), ← hm2, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have v135 : rdW (m3.arr64 CTL) 135 = k := by
    rw [← hm3]; unfold jobMem
    rw [rdW_set64_self _ _ _ _ (by simp only [Mem.size_arr64_set64]; exact hlt 135 (by decide))]
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
    erecP_congr' (eA _ (by decide)) (eA _ (by decide)) (eC 129 (by decide) (by decide) (by decide) (by decide))
      (eC 130 (by decide) (by decide) (by decide) (by decide))
  have hI3 : IndexR m3 I := h.idx.grow (fun b _ hb => eA b (fun e => by subst e; revert hb; decide))
    (eC 128 (by decide) (by decide) (by decide) (by decide)) (by rw [hx3]; exact fun _ _ h => h)
  have h134 : (rdW (m3.arr64 CTL) 134).toNat = I.firsts.getD k.toNat I.next := by
    have hkf : k.toNat < I.firsts.size := by rw [h.fsize]; exact hk
    rw [v134, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hkf, Option.getD_some,
      ← h.idx.firsts _ hkf, UInt64.ofNat_toNat]
  have hE3 : EnvR m3 0 (I.view k.toNat) :=
    EnvR.ofIndex hI3 hO3 hB3 (by rw [hs3]; omega) h134 (by rw [v135])
  have hCK : CheckR m3 a 0 (I.view k.toNat) :=
    ⟨h.arena.frame64 hf (by simp) (fun x hx => by rcases hC x hx with rfl|rfl|rfl|rfl <;> decide),
      h.core.frame (fun b hb => by simp at hb) (fun x hx => by
        rcases hC x hx with rfl|rfl|rfl|rfl <;> decide) hf,
      h.pinsR.frame (fun b hb => by simp at hb) hf, hE3,
      h.mode.frame hf (by decide) (by decide)⟩
  have hIW : L.Ind.IWOK m3 :=
    IWOK.frame hf3 (by simp) (by simp) (by decide) (by decide) (hm2 ▸ IWOK.reset h.iw) (by simp) (by decide)
  refine ⟨⟨hCK, hIW⟩, by rw [eA _ (by decide), eA _ (by decide)]; exact h.decls, ?_, ?_,
    by rw [pinW_frame hf (by simp)]; exact h.flag, ?_, hI3,
    by rw [eC 130 (by decide) (by decide) (by decide) (by decide)]; exact h.top1⟩
  · exact PinSetsR.grow h.pinsets (RecGrow.of_eq (eA _ (by decide))
      (eC 129 (by decide) (by decide) (by decide) (by decide)))
      (eC 150 (by decide) (by decide) (by decide) (by decide))
      (eC 151 (by decide) (by decide) (by decide) (by decide))
  · exact ⟨by rw [hf.size]; exact h.mem.erec, by rw [hf.size]; exact h.mem.spn,
      by rw [hf.size]; exact h.mem.bstk, h.mem.memos.frame hf (by simp) (by decide),
      h.mem.dnN⟩
  · exact h.memos.frame hf (by simp) (fun x hx => by rcases hC x hx with rfl|rfl|rfl|rfl <;> decide)

/-! ## `record_job` -/

/-- **`record_job(k)` refines `recordJob` of record `k`, both outcomes**: from the job relation and
con-ron's fold invariant at the view of position `k` (as `RecordSpec` takes it), an ok run is the
twin's, with the job relation after it; a failing run claims the twin job's failure. -/
@[refines ConRon.Arena.IStreamIndex.view ConRon.Arena.recordCheck ConRon.Arena.recordJob]
theorem recordJob_ref {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} {p : Prog} {I : IStreamIndex}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
    (hrec : ConRon.Bridge.RecordSpec pins pinsP) (hpp : ConRon.Bridge.PersPinSets pins)
    {N : Nat} (hN : N ≤ 2 ^ 62) {m : Mem} {a : AState} {k : Word} (hk : k.toNat < ds.size)
    (hJ : JobR pins dn ds I m a)
    (hF : ∃ env, ConRon.Bridge.FoldOK env (I.view k.toNat) (AM.st enterScratch a))
    (hden : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x ∧ ∃ d, Frontend.denoteDecl a.store x = some d)
    (hPD : ConRon.Bridge.PinsDenote a.store pins pinsP) :
    RefE (JobG pins dn ds p) (callE p N "record_job" [k] m) (recordJob V pins I k.toNat ds[k.toNat])
      a (fun v _ a' => JobPost pins dn ds I a v.2 a') := by
  sorry

/-! ## `check_jobs` -/

/-- A job accepted at the head of a worker's list: the rest runs from the job's state. -/
theorem checkJobList_cons_ok {pins : List INatOpPinSet} {I : IStreamIndex} {ds : Array IDeclaration}
    {t : Nat} (ht : t < ds.size) {rest : List Nat} {a a₁ : AState}
    (h : recordJob V pins I t ds[t] a = .ok ((), a₁)) :
    checkJobList V pins I ds (t :: rest) a = checkJobList V pins I ds rest a₁ := by
  simp only [checkJobList, runJob, Array.getElem?_eq_getElem ht, h]

/-- A job failing at the head of a worker's list fails the list. -/
theorem checkJobList_cons_err {pins : List INatOpPinSet} {I : IStreamIndex} {ds : Array IDeclaration}
    {t : Nat} (ht : t < ds.size) {rest : List Nat} {a : AState} {e : Err}
    (h : ErrClaim (recordJob V pins I t ds[t]) a e) :
    ErrClaimV (checkJobList V pins I ds (t :: rest)) a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h hk
  have hce' : recordJob V pins I t ds[t] a = .error ce := hce
  exact .inr ⟨ce, t, AState.abandoned, by
    show checkJobList V pins I ds (t :: rest) a = _
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
    {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} {p : Prog} {I : IStreamIndex}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
    (hrec : ConRon.Bridge.RecordSpec pins pinsP) (hpp : ConRon.Bridge.PersPinSets pins)
    {a₀ : AState} (hden : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d)
    (hPD : ConRon.Bridge.PinsDenote a₀.store pins pinsP) {hi : Word} (hhi : hi.toNat ≤ ds.size) :
    ∀ (n : Nat), n ≤ 2 ^ 62 + 1 → ∀ (m : Mem) (a : AState) (j : Word),
      JobPost pins dn ds I a₀ m a →
      (∀ (t : Nat) (a' : AState), j.toNat ≤ t → t < hi.toNat →
        checkJobList V pins I ds (List.range' j.toNat (t - j.toNat)) a = .ok (.ok (), a') →
        ∃ env, ConRon.Bridge.FoldOK env (I.view t) (AM.st enterScratch a')) →
      RefC (JobG pins dn ds p) (checkJobsE.loop1 p n m j hi)
        (fun m' => ∃ a', checkJobList V pins I ds (List.range' j.toNat (hi.toNat - j.toNat)) a =
          .ok (.ok (), a') ∧ JobPost pins dn ds I a₀ m' a')
        (ErrClaimV (checkJobList V pins I ds (List.range' j.toNat (hi.toNat - j.toNat))) a) := by
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
      have hr := recordJob_ref hP hFD hLD hrec hpp (N := n) (by omega) hjk hJ hF hden' hPD'
      cases hc : callE p n "record_job" [j] m with
      | error e =>
        rw [checkJobsE.k_record_job.none]
        rw [hc] at hr
        exact fun hg => checkJobList_cons_err hjk (hr hg)
      | ok q =>
        obtain ⟨r, m₁⟩ := q
        rw [checkJobsE.k_record_job.arm1]
        rw [hc] at hr
        obtain ⟨u, a₁, hrun, hJ₁, hx₁, hp₁⟩ := hr
        have hrun' : recordJob V pins I j.toNat ds[j.toNat] a = .ok ((), a₁) := by cases u; exact hrun
        have hcons := fun rest => checkJobList_cons_ok (pins := pins) (I := I) hjk (rest := rest) hrun'
        have hR₁ : JobPost pins dn ds I a₀ m₁ a₁ := ⟨hJ₁, hx.trans hx₁, hp₁.trans hp⟩
        have hG₁ : ∀ (t : Nat) (a' : AState), (j + 1).toNat ≤ t → t < hi.toNat →
            checkJobList V pins I ds (List.range' (j + 1).toNat (t - (j + 1).toNat)) a₁ = .ok (.ok (), a') →
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

/-- **`check_jobs(j, hi)` refines `checkJobList` over the jobs `j‥hi - 1`, both outcomes**
(`checkJobsLoop_ref` through the function's model). -/
@[refines ConRon.Arena.checkJobList ConRon.Arena.runJob]
theorem checkJobs_ref {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} {p : Prog} {I : IStreamIndex}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
    (hrec : ConRon.Bridge.RecordSpec pins pinsP) (hpp : ConRon.Bridge.PersPinSets pins)
    {a₀ : AState} (hden : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d)
    (hPD : ConRon.Bridge.PinsDenote a₀.store pins pinsP) {hi : Word} (hhi : hi.toNat ≤ ds.size)
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {j : Word}
    (hR : JobPost pins dn ds I a₀ m a)
    (hG : ∀ (t : Nat) (a' : AState), j.toNat ≤ t → t < hi.toNat →
        checkJobList V pins I ds (List.range' j.toNat (t - j.toNat)) a = .ok (.ok (), a') →
        ∃ env, ConRon.Bridge.FoldOK env (I.view t) (AM.st enterScratch a')) :
    RefC (JobG pins dn ds p) (checkJobsE p n m j hi)
      (fun v => ∃ a', checkJobList V pins I ds (List.range' j.toNat (hi.toNat - j.toNat)) a =
        .ok (.ok (), a') ∧ JobPost pins dn ds I a₀ v.2 a')
      (ErrClaimV (checkJobList V pins I ds (List.range' j.toNat (hi.toNat - j.toNat))) a) := by
  rcases n with _ | n
  · exact fun _ => ErrClaimV.of_cls0 Err.cls_outOfFuel
  have h := checkJobsLoop_ref hP hFD hLD hrec hpp hden hPD hhi (n + 1) (by omega) m a j hR hG
  show RefC _ (checkJobsE.k_loop1 p (checkJobsE.loop1 p (n + 1) m j hi)) _ _
  cases e : checkJobsE.loop1 p (n + 1) m j hi with
  | error ε => rw [e] at h; exact h
  | ok m' => rw [e] at h; exact h

end L.Arena
