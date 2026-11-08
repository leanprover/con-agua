module

public import ConAgua.Arena.DeclCheckT
public import ConAgua.Arena.IndexBuild
public import ConAgua.Arena.TwinStep
public import ConRon.Bridge.Checker.Pooled
import ConAgua.Census.Attr
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

/-- **What a worker's memory keeps between two jobs**, against the worker's twin state `a` and the
stream index `I`: the checker state without an environment (the arena, the caches, the pins, the
mode), the stream index (`IndexR`), every own row below the stamp (`OwnBelow`, so the next job's
stamp bump empties the own layer), the front's records, the pools in bounds with tier 1 empty,
the pin variants, the memory's half of `TwinOK`, the pin flag, the inductive memos; on the twin
side the store well formed with the scratch tier off and the caches empty. -/
structure JobR (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
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
