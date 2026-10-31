module

public import ConAgua.Arena.LoopT
public import ConAgua.Arena.PhaseWorker
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.Verdict.DeclValE

@[expose] public section

/-!
# Phase B under `StageT` (lane `loopt3`, items 12 and 12a)

Phase B runs `check_value_group` from `StageT` with the program's own core (`cvg_ref`,
`realCall p`; its `StageR` version through the stubs is gone). Per pending check:

* **The twin side** (`TwinPend`): con-ron's phase-B invariant (`Arena.checkPendingList_bridge`'s
  induction hypotheses): `FoldOK` at the final environment `env` (names unique), the remaining
  records related to their pure value groups (`PendRel`), the caches empty and the scratch tier
  off (each check ends with `dropScratch`). `TwinPend.step` is that induction's step
  (`Arena.checkPending_prefix`); `TwinPend.start` gets it from phase A's twin run
  (`Arena.installFold_bridge` from `TwinFold` at the loop's start).
* **`TwinOK` at the record's view**: con-ron's `CheckOK` at the prefix environment and the
  restricted index (`IFEnvOK_prefix`, the caches empty) and the memory's half (`LoopMem`,
  `CoreMemos`), `TwinOK.of_check`; the bracket's opening keeps it (`enter_loopB`, as
  `CheckerT.lean`'s `enter_loopW`); `check_value_group` from `StageT` (`checkValueGroup_specT`);
  `scratch_drop` is a leaf (`CoreMemos` by its frame, `drop_loopB`); `LoopMem` back by the
  loop's write set (`LoopClosed`) and the twin's `PExt`.
* **Item 12a** (`installFold_drop`): an accepting `installFold` from a state with empty caches
  (scratch tier off) ends with empty caches (scratch tier off): every step ends in `dropScratch`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open ConRon.Bridge (FoldOK PExt PendRel ListRel)

local notation "V" => ConLeche.CheckMode.verified

/-! ## The twin side -/

section twin

/-- An accepting `installStep` ends with empty caches and the scratch tier off (`dropScratch`
last on both arms; `installStep_off`'s pattern). -/
theorem installStep_drop {mode : ConLeche.CheckMode} {pins : List INatOpPinSet} {i : Nat}
    {fe : IFEnv} {pend : Array PendingCheck} {pd : IDeclaration} {s s' : AState}
    {x : IFEnv × Array PendingCheck} (h : installStep mode pins i fe pend pd s = .ok (x, s')) :
    s'.caches = Caches.empty ∧ s'.store.scratchOn = false ∧ s'.store.dropScratch = s'.store := by
  have hd : ∀ {t t' : AState} {u : Unit}, dropScratch t = .ok (u, t') →
      t'.caches = Caches.empty ∧ t'.store.scratchOn = false ∧ t'.store.dropScratch = t'.store :=
    fun h => by
      simp only [dropScratch, flushCaches, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure, Except.bind] at h
      cases h; exact ⟨rfl, rfl, rfl⟩
  simp only [installStep] at h
  obtain ⟨_, s1, -, h⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨_, s2, -, h⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨⟨fe', vg⟩, s3, -, h⟩ := ConRon.Bridge.AM.bind_ok h
  cases vg with
  | none =>
    obtain ⟨⟨_, _⟩, s4, -, h⟩ := ConRon.Bridge.AM.bind_ok h
    obtain ⟨_, s5, h5, h⟩ := ConRon.Bridge.AM.bind_ok h
    obtain ⟨-, rfl⟩ := ConRon.Bridge.AM.pure_ok h
    exact hd h5
  | some vg =>
    obtain ⟨⟨_, _⟩, s4, -, h⟩ := ConRon.Bridge.AM.bind_ok h
    obtain ⟨⟨_, _⟩, s5, -, h⟩ := ConRon.Bridge.AM.bind_ok h
    obtain ⟨_, s6, h6, h⟩ := ConRon.Bridge.AM.bind_ok h
    obtain ⟨-, rfl⟩ := ConRon.Bridge.AM.pure_ok h
    exact hd h6

/-- **Item 12a: an accepting `installFold` ends with empty caches** (and the scratch tier off)
when it starts so: a record either leaves the state alone (none) or ends in `dropScratch`. -/
theorem installFold_drop {mode : ConLeche.CheckMode} {pins : List INatOpPinSet} :
    ∀ (ds : List IDeclaration) (p q : Nat × IFEnv × Array PendingCheck) (s s' : AState),
      installFold mode pins p ds s = .ok (.ok q, s') →
      (s.caches = Caches.empty → s'.caches = Caches.empty) ∧
      (s.store.scratchOn = false → s'.store.scratchOn = false) := by
  intro ds
  induction ds with
  | nil =>
    intro p q s s' h
    simp only [installFold] at h
    obtain ⟨-, rfl⟩ := ConRon.Bridge.AM.pure_ok h
    exact ⟨id, id⟩
  | cons d ds ih =>
    intro p q s s' h
    simp only [installFold] at h
    obtain ⟨r, s1, h1, h⟩ := ConRon.Bridge.AM.bind_ok h
    cases r with
    | error e => obtain ⟨he, -⟩ := ConRon.Bridge.AM.pure_ok h; cases he
    | ok p' =>
      have hk := ih p' q s1 s' h
      simp only [installDeclStep] at h1
      cases hP : andPinOk d s with
      | error e => rw [hP] at h1; cases h1
      | ok w =>
        obtain ⟨b, s0⟩ := w
        cases b with
        | false => rw [hP] at h1; cases h1
        | true =>
          rw [hP] at h1
          simp only at h1
          cases hA : installStep mode pins p.1 p.2.1 p.2.2 d s0 with
          | error e => rw [hA] at h1; cases h1
          | ok v =>
            obtain ⟨x, s2⟩ := v
            rw [hA] at h1
            simp only [Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨-, rfl⟩ := h1
            have h2 := installStep_drop hA
            exact ⟨fun _ => hk.1 h2.1, fun _ => hk.2 h2.2.1⟩

/-- **Item 12a, from any start**: an accepting `installFold` ends with empty caches, or ran no
record (the state and the fold's tuple unchanged). The parse before the loop leaves the caches
non-empty (con-ron's `FoldOK_of_start` note), so phase B's start uses this form. -/
theorem installFold_cachesOr {mode : ConLeche.CheckMode} {pins : List INatOpPinSet} :
    ∀ (ds : List IDeclaration) (p q : Nat × IFEnv × Array PendingCheck) (s s' : AState),
      installFold mode pins p ds s = .ok (.ok q, s') →
      (s'.caches = Caches.empty ∧ s'.store.dropScratch = s'.store) ∨ (q = p ∧ s' = s) := by
  intro ds
  induction ds with
  | nil =>
    intro p q s s' h
    simp only [installFold] at h
    obtain ⟨he, rfl⟩ := ConRon.Bridge.AM.pure_ok h
    cases he; exact .inr ⟨rfl, rfl⟩
  | cons d ds ih =>
    intro p q s s' h
    simp only [installFold] at h
    obtain ⟨r, s1, h1, h⟩ := ConRon.Bridge.AM.bind_ok h
    cases r with
    | error e => obtain ⟨he, -⟩ := ConRon.Bridge.AM.pure_ok h; cases he
    | ok p' =>
      refine .inl ?_
      rcases ih p' q s1 s' h with hk | ⟨-, rfl⟩
      · exact hk
      simp only [installDeclStep] at h1
      cases hP : andPinOk d s with
      | error e => rw [hP] at h1; cases h1
      | ok w =>
        obtain ⟨b, s0⟩ := w
        cases b with
        | false => rw [hP] at h1; cases h1
        | true =>
          rw [hP] at h1
          simp only at h1
          cases hA : installStep mode pins p.1 p.2.1 p.2.2 d s0 with
          | error e => rw [hA] at h1; cases h1
          | ok v =>
            obtain ⟨x, s2⟩ := v
            rw [hA] at h1
            simp only [Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨-, rfl⟩ := h1
            exact ⟨(installStep_drop hA).1, (installStep_drop hA).2.2⟩

/-- **Phase B's twin invariant** before the records `pend` (the remaining ones): con-ron's
`FoldOK` at the final environment `env` (names unique), each remaining record related to its pure
value group at the store (`PendRel`), the caches empty and the scratch tier off. -/
structure TwinPend (fe : IFEnv) (pend : List PendingCheck) (a : AState) : Prop where
  fold : ∃ env pendP, FoldOK V env fe a ∧ ConLeche.NodupNames env ∧
    ListRel (PendRel a.store env) pend pendP
  /-- The caches are empty when a check is left (each check ends in `dropScratch`). -/
  caches : pend ≠ [] → a.caches = Caches.empty
  off : a.store.scratchOn = false
  /-- The scratch tier is dropped when a check is left (each check ends in `dropScratch`, which
  also empties the scratch tables): the store is its own `dropScratch`, so a worker
  (`AState.worker`) has the same store (lane parmode, `FreezeFresh.lean`). -/
  dropped : pend ≠ [] → a.store.dropScratch = a.store

/-- **`TwinPend` at phase B's start**, from `TwinFold` at the loop's start and phase A's
accepting twin run (`Arena.installFold_bridge`, `PhaseA.nodup`, `installFold_drop`,
`installFold_cachesOr`: a pending check exists only if some record ran). -/
theorem TwinPend.start {pins : List INatOpPinSet} {ds : Array IDeclaration} {a₀ a : AState}
    {k : Nat} {fe : IFEnv} {pend : Array PendingCheck}
    (hT : TwinFold pins ds (mkIFEnv IEnv.empty) #[] a₀)
    (hrun : installFold V pins (0, mkIFEnv IEnv.empty, #[]) ds.toList a₀ =
      .ok (.ok (k, fe, pend), a)) :
    TwinPend fe pend.toList a := by
  have hk : ConRon.Bridge.CoreSpec V ConRon.Arena.checkFuel := ConRon.Bridge.CoreSpec.of_core rfl
  have hind : ConRon.Bridge.IndSpec V := ConRon.Bridge.Inductives.indSpec_of_bridge rfl hk
  obtain ⟨env, hok, hnd⟩ := hT.fold
  obtain ⟨pinsP, hpins⟩ := hT.pinsD
  obtain ⟨dsP, hden⟩ := hT.den
  obtain ⟨env', pendP', hok', -, hA, hrel, -, -⟩ :=
    ConRon.Bridge.Arena.installFold_bridge rfl hk hind hT.pp ds.toList dsP env 0 k
      (mkIFEnv IEnv.empty) fe #[] pend [] a₀ a hok hnd hpins hT.pd hden .nil hrun
  have hd := installFold_drop ds.toList _ _ a₀ a hrun
  refine ⟨⟨env', pendP', hok', hA.nodup hnd, by simpa using hrel⟩, fun hne => ?_, hd.2 hT.off,
    fun hne => ?_⟩
  · rcases installFold_cachesOr ds.toList _ _ a₀ a hrun with h | ⟨he, -⟩
    · exact h.1
    · simp only [Prod.mk.injEq] at he
      exact absurd (by rw [he.2.2]) hne
  · rcases installFold_cachesOr ds.toList _ _ a₀ a hrun with h | ⟨he, -⟩
    · exact h.2
    · simp only [Prod.mk.injEq] at he
      exact absurd (by rw [he.2.2]) hne

/-- `TwinPend` at the `AM` form of phase A's run. -/
theorem TwinPend.startAM {pins : List INatOpPinSet} {ds : Array IDeclaration} {a₀ : AState}
    {k : Nat} {fe : IFEnv} {pend : Array PendingCheck}
    (hT : TwinFold pins ds (mkIFEnv IEnv.empty) #[] a₀)
    (hok : AM.ok (installFold V pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)
    (hres : AM.res (installFold V pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀ =
      .ok (k, fe, pend)) :
    TwinPend fe pend.toList (AM.st (installFold V pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) := by
  have hrun := AM.run_of_ok _ _ hok
  rw [hres] at hrun
  exact TwinPend.start hT hrun

/-- **con-ron's `CheckOK` at a record's view**: the prefix environment, the restricted index
(`IFEnvOK_prefix`), the caches empty. -/
theorem TwinPend.checkAt {fe : IFEnv} {pc : PendingCheck} {rest : List PendingCheck} {a : AState}
    (h : TwinPend fe (pc :: rest) a) :
    ∃ env, ConRon.Bridge.CheckOK V env (fe.restrictTo pc.vis) a := by
  obtain ⟨env, -, hok, hnd, -⟩ := h.fold
  exact ⟨env.prefixTo pc.vis,
    { state := hok.check.state
      caches := ConRon.Bridge.CacheOK.of_empty (h.caches (by simp))
      pins := hok.check.pins
      ienv := ConRon.Bridge.IFEnvOK_prefix hok hnd pc.vis }⟩

/-- **The theorem test's twin facts at a record's check** (`Arena.checkPending_prefix`'s opening):
after `enterScratch`, `CheckOK` at the record's prefix environment, the record's constant denoting,
its type in scope. -/
theorem TwinPend.enterThm {fe : IFEnv}
    {pc : PendingCheck} {rest : List PendingCheck} {a : AState}
    (h : TwinPend fe (pc :: rest) a) :
    pc.vg.kind = .thm → ∃ env cP, ConLeche.EnvWF env ∧
      ConRon.Bridge.CheckOK V env (fe.restrictTo pc.vis) (AM.st enterScratch a) ∧
      Frontend.denoteCV (AM.st enterScratch a).store pc.vg.cv = some cP ∧
      ConLeche.Expr.WScoped 0 cP.type := by
  intro _
  obtain ⟨env, pendP, hok, hnd, hrel⟩ := h.fold
  cases hrel with
  | cons hp _ =>
    have hwf := hok.check.state.wf
    have hx1 : PExt a.store a.store.enableScratch := ConRon.Bridge.PExt.enterScratch hwf
    refine ⟨_, _, hp.envWF, ?_, ?_, hp.wsty⟩
    · rw [enterScratch_st]
      exact
        { state := ⟨(EStore.enableScratch_spec hwf).1⟩
          caches := ConRon.Bridge.CacheOK.of_empty (h.caches (by simp))
          pins := hok.check.pins.pmono hok.persPins hx1 rfl
          ienv := ((ConRon.Bridge.IFEnvOK_prefix hok hnd pc.vis).congr_env hp.prefix_find?
              hp.prefix_findTable?).pmono
            ⟨hok.persEnv.env, hok.persEnv.idx, hok.persEnv.tables, hok.persEnv.tbls⟩ hx1 }
    · rw [enterScratch_st]
      exact ConRon.Bridge.denoteCV_pext hx1 hp.pers.cv hp.cv

theorem TwinPend.stateOK {fe : IFEnv} {pend : List PendingCheck} {a : AState}
    (h : TwinPend fe pend a) : ConRon.Bridge.StateOK a := by
  obtain ⟨env, -, hok, -⟩ := h.fold
  exact hok.check.state

/-- **Phase B's twin step** (`Arena.checkPending_prefix`): an accepting check of the first record
keeps the invariant for the rest, and the store grows on its persistent tier. -/
theorem TwinPend.step {fe : IFEnv} {pc : PendingCheck} {rest : List PendingCheck} {a a' : AState}
    (h : TwinPend fe (pc :: rest) a) (hrun : checkPending V fe pc a = .ok ((), a')) :
    TwinPend fe rest a' ∧ PExt a.store a'.store := by
  have hk : ConRon.Bridge.CoreSpec V ConRon.Arena.checkFuel := ConRon.Bridge.CoreSpec.of_core rfl
  obtain ⟨env, pendP, hok, hnd, hrel⟩ := h.fold
  cases hrel with
  | cons hp hrest =>
    obtain ⟨hok₁, hx₁, hc₁, -⟩ :=
      ConRon.Bridge.Arena.checkPending_prefix rfl hk hok hp.pers hnd (h.caches (by simp))
        hp.envWF hp.prefix_find? hp.prefix_findTable? hp.kind hp.cv hp.jv hp.wsty hp.wsjv hrun
    have hoff : a'.store.scratchOn = false ∧ a'.store.dropScratch = a'.store := by
      simp only [checkPending] at hrun
      obtain ⟨_, s1, -, r1⟩ := ConRon.Bridge.AM.bind_ok hrun
      obtain ⟨_, s2, -, r2⟩ := ConRon.Bridge.AM.bind_ok r1
      rw [ConRon.Bridge.dropScratch_run] at r2
      simp only [Except.ok.injEq, Prod.mk.injEq] at r2
      obtain ⟨-, rfl⟩ := r2
      exact ⟨rfl, rfl⟩
    exact ⟨⟨⟨env, _, hok₁, hnd, PendRel.listRel_mono hx₁ ⟨[], rfl⟩ (ConRon.Bridge.TblExt.of_eq rfl) hrest⟩, fun _ => hc₁, hoff.1,
      fun _ => hoff.2⟩, hx₁⟩

end twin

/-! ## The L side -/

/-- **The program hypotheses phase B under `StageT` takes**: the bracket, `check_value_group`'s
text, the core's entry points under `StageT`, the leaves' and the loop's write sets, and phase B's
three functions. -/
structure PhaseBProg (p : Prog) : Prop where
  bracket : BracketProg p
  cvg : CvgProg p
  knot : KnotStageProg p
  leaf : LeafClosed p
  loop : LoopClosed p
  cp : p.lookup "check_pending" = some checkPendingL
  cpg : p.lookup "check_pending_go" = some checkPendingGoL
  cpx : p.lookup "check_pending_next" = some checkPendingNextL
  /-- `all_level_params_defined`'s program and the `CrOK` threading (`consts_resolve_ffast`'s memo
  across phase B's calls): the value guards' walks under `StageT`. -/
  apd : L.Ind.ApdF p
  crk : CrKeep p

section bracket
variable (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration) (p : Prog)
  (hb : BracketProg p)
include hb

/-- **`scratch_enter` keeps `TwinOK`** from a loop head (the store well formed, the scratch tier
off), at any environment `fe'` (phase B's: the record's view). `CheckerT.lean`'s `enter_loopW`
with the two environments apart. -/
theorem enter_loopB (hkp : CrKeep p) {pins : List INatOpPinSet} (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word)
    (fe fe' : IFEnv) (pend : Array PendingCheck) (hwf : StoreWF a₀.store)
    (hoff : a₀.store.scratchOn = false) (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds)
    (hTw : TwinOK dn s₀.mem a₀ fe') (hfl : pinW s₀.mem 0 ≠ 0) (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "scratch_enter" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok enterScratch a₀ ∧
      LoopR pins dn s'.mem (AM.st enterScratch a₀) vis fe pend ds ∧
      TwinOK dn s'.mem (AM.st enterScratch a₀) fe' ∧ pinW s'.mem 0 ≠ 0 ∧ L.Stubs.CrOK s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  have hCr' := M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_crOK hkp.closed hkp.crf n (im_mem "scratch_enter" rfl) [] s₀)
  obtain ⟨hloc, hok, hL⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (enter_loop dn ds p hb n s₀ a₀ vis fe pend hR)
  obtain ⟨-, -, -, -, -, -, -, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchEnter_spec p hb.se hb.sr hb.bm hb.lf hb.im hb.fm n s₀)
  subst hs
  have hf : MemFrame scrArrs ((0 :: resetCtl) ++ memoCtl) s.mem s'.mem := by rw [hm]; exact enterMem_frame _
  refine ⟨hloc, hok, hL, ?_, by rw [pinW_frame hf (by decide)]; exact hfl, hCr' hCr⟩
  rw [enterScratch_st]
  exact (hTw.frameLo hf (by decide) (fun x h => by
    simp [resetCtl, scratchCnts, memoCtl, SCB] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      <;> decide)).enter hwf hoff

/-- **`scratch_drop` keeps the core's memos** (a leaf), beside the loop's relation. -/
theorem drop_loopB (hlc : LeafClosed p) (hkp : CrKeep p) {pins : List INatOpPinSet} (n : Nat) (s₀ : St)
    (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
    (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds) (hc : CoreMemos s₀.mem)
    (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "scratch_drop" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok dropScratch a₀ ∧
      LoopR pins dn s'.mem (AM.st dropScratch a₀) vis fe pend ds ∧ CoreMemos s'.mem ∧
      L.Stubs.CrOK s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  have hCr' := M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_crOK hkp.closed hkp.crf n (im_mem "scratch_drop" rfl) [] s₀)
  obtain ⟨hloc, hok, hL⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (drop_loop (pins := pins) dn ds p hb n s₀ a₀ vis fe pend hR)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_memFrame hlc n (leaf_mem "scratch_drop" rfl) [] s₀)
  subst hs
  exact ⟨hloc, hok, hL, hc.frame hf leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp,
    hCr' hCr⟩

end bracket

section specs
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-- **`check_value_group` refines `checkValueGroup` under `StageT`** (the program's own core,
`cvg_ref`'s ok half): from the loop's relation, `TwinOK` and the pin flag, the loop's relation and the
core's memos after it. -/
@[refines ConRon.Arena.checkValueGroup]
theorem checkValueGroup_specT (hm : mode = .verified) (hP : CvgProg p) (hq : KnotStageProg p)
    (hap : ApdF p) (hkp : CrKeep p) :
    ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
      (pend : Array PendingCheck) (g : Word) (vg : ValueGroup),
      decVG (erecP s₀.mem) g.toNat = some vg →
      (vg.kind = .thm → ∃ env cP, ConLeche.EnvWF env ∧ ConRon.Bridge.CheckOK V env fe a₀ ∧
        Frontend.denoteCV a₀.store vg.cv = some cP ∧ ConLeche.Expr.WScoped 0 cP.type) →
      LoopR pins dn s₀.mem a₀ vis fe pend ds → TwinOK dn s₀.mem a₀ fe → pinW s₀.mem 0 ≠ 0 →
      L.Stubs.CrOK s₀.mem →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_value_group" [vis, g]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (checkValueGroup mode fe vg) a₀ ∧
      LoopR pins dn s'.mem (AM.st (checkValueGroup mode fe vg) a₀) vis fe pend ds ∧
      CoreMemos s'.mem ∧ L.Stubs.CrOK s'.mem; ⊤⦄ := by
  intro n hn s₀ a₀ vis fe pend g vg hg hthm hR hTw hfl hCr
  subst hm
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, _, a', hrun', hS', hg', hCr'⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (RefE.triple (checkValueGroup_specE p hP n s₀ vis g) (cvg_ref hq hP hq.knot.lvc hap hkp n hn
      ⟨⟨hR.check, hR.iw⟩, hTw, hfl⟩ hg hCr hthm))
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hP.closed.memFrame n (f := "check_value_group") (by decide) [vis, g] s₀)
  subst hs
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok, hst ▸ hR.of_step hS'.stage hf ?_, hS'.twin.memos, hCr'⟩
  rw [← erecP_reset s.mem]
  exact IWGrow.erecPExt hg'

/-- `TwinOK` at a pending record's view, from phase B's twin invariant and the memory's half. -/
theorem TwinPend.twinOK {fe : IFEnv} {pc : PendingCheck} {rest : List PendingCheck} {a : AState}
    {m : Mem} (hT : TwinPend fe (pc :: rest) a) (hM : LoopMem dn m a) (hc : CoreMemos m) :
    TwinOK dn m a (fe.restrictTo pc.vis) := by
  obtain ⟨env, hck⟩ := hT.checkAt
  exact TwinOK.of_check hck ⟨hM.erec, hM.spn, hM.bstk, hc, fun k x e => (hM.dnP k x e).2⟩

/-- The record's two words read by `rdW` (the unified model's loads). -/
theorem pend_rdW (m : Mem) (pend : Array PendingCheck) (hP : PendR m pend) (j : Word)
    (hj : j.toNat < pend.size) (hj62 : j.toNat < 2 ^ 62) :
    decVG (erecP m) (rdW (m.arr64 PEND) (3 * j)).toNat = some (pdAt pend j).vg ∧
    (rdW (m.arr64 PEND) (3 * j + 2)).toNat = (pdAt pend j).vis := by
  have hr := hP.recs j.toNat hj
  have e0 : (3 * j).toNat = 3 * j.toNat := by rw [UInt64.toNat_mul]; simp; omega
  have e2 : (3 * j + 2).toNat = 3 * j.toNat + 2 := by rw [UInt64.toNat_add, e0]; simp; omega
  have hpd : pdAt pend j = pend[j.toNat] := by simp [pdAt, hj]
  simp only [decPend, nat?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at hr
  obtain ⟨g, ⟨w0, hw0, rfl⟩, vg, hvg, x, ⟨w1, hw1, rfl⟩, y, ⟨w2, hw2, rfl⟩, he⟩ := hr
  rw [hpd, ← Option.some.inj he]
  refine ⟨?_, ?_⟩
  · rw [rdW_of_get? e0.symm hw0]; exact hvg
  · rw [rdW_of_get? e2.symm hw2]

/-- **`check_pending`'s unified model**: the bracket's opening and drop (outside the verdict
closure) lifted, `check_value_group` through its run (its ok half reads the call's write set). -/
l_model checkPending_specE (p : Prog) (hf : p.lookup "check_pending" = some checkPendingL)
  fns [hf ↦ checkPendingE]
  specs [callW_spec p n "scratch_enter", callW_spec p n "scratch_drop"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `check_pending`'s error arms assume: the no-verdict closure (the bracket) and
`check_value_group`'s (`CvgCtx`). -/
structure CpG (p : Prog) : Prop where
  nv : closedNV p L.Checker.nvFns = true
  cvg : CvgCtx p

/-- What `check_pending` gives besides the twin's run: the loop's relation, the core's memos and
`consts_resolve_ffast`'s memo after it. -/
structure CpPost (vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (m' : Mem) (a' : AState) :
    Prop where
  loop : LoopR pins dn m' a' vis fe pend ds
  core : CoreMemos m'
  cr : L.Stubs.CrOK m'

/-- **`check_pending` refines `checkPending` under `StageT`, both outcomes**: the bracket's
opening keeps `TwinOK` at the record's view, `check_value_group` runs from `StageT` (`cvg_ref`'s
error half on its run), the drop is a leaf. -/
theorem cpd_ref (hm : mode = .verified) (hP : PhaseBProg p) {N : Nat} (hN : N ≤ 2 ^ 62 + 1)
    {m : Mem} {a₀ : AState} {j vis : Word} {fe : IFEnv} {pend : Array PendingCheck}
    (hj : j.toNat < pend.size) {rest : List PendingCheck}
    (hT : TwinPend fe (pdAt pend j :: rest) a₀) (hR : LoopR pins dn m a₀ vis fe pend ds)
    (hM : LoopMem dn m a₀) (hc : CoreMemos m) (hCr : L.Stubs.CrOK m) :
    RefE (CpG p) (checkPendingE p N m j vis) (checkPending mode fe (pdAt pend j)) a₀
      (fun v _ a' => CpPost pins dn ds vis fe pend v.2 a') := by
  subst hm
  have hb := hP.bracket
  have hTw := hT.twinOK dn hM hc
  have hthm := hT.enterThm
  rcases N with _ | n
  · rw [checkPendingE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hn' : n ≤ 2 ^ 62 := by omega
  by_cases g1 : 4611686018427387904 ≤ j
  · rw [checkPendingE.abort1 _ _ _ _ _ g1]; exact RefE.of_cls0 rfl
  rw [checkPendingE.arm1 _ _ _ _ _ g1]
  have h62 : j.toNat < 2 ^ 62 := by
    have : ¬ (4611686018427387904 : Word).toNat ≤ j.toNat := fun h => g1 (UInt64.le_iff_toNat_le.mpr h)
    simp at this; omega
  unfold checkPending
  refine RefE.onlySim (fun _ => checkPendingE.k_scratch_enter.none ..) (fun _ _ h => h) fun r1 m1 c1 => ?_
  rw [checkPendingE.k_scratch_enter.arm1]
  obtain ⟨s1, hs1, -, hok1, hR1, hT1, hfl1, hCr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (enter_loopB dn ds p hb hP.crk (pins := pins) n _ a₀ vis fe (fe.restrictTo (pdAt pend j).vis) pend
      hT.stateOK.wf hT.off hR hTw hM.flag hCr) c1
  subst hs1
  refine RefE.bind_right (AM.run_of_ok _ _ hok1) ?_
  obtain ⟨hg, hv⟩ := pend_rdW s1.mem pend hR1.pend j hj h62
  generalize rdW (s1.mem.arr64 PEND) (3 * j + 2) = v at hv ⊢
  generalize rdW (s1.mem.arr64 PEND) (3 * j) = g at hg ⊢
  have hR' := hR1.restrict v
  rw [hv] at hR'
  have hS : StageT dn v (fe.restrictTo (pdAt pend j).vis) s1.mem (AM.st enterScratch a₀) :=
    ⟨⟨hR'.check, hR'.iw⟩, hT1, hfl1⟩
  rcases c2 : callE p n "check_value_group" [v, g] s1.mem with e2 | ⟨r2, m2⟩
  · rw [checkPendingE.k_check_value_group.none]
    exact RefE.bind_left fun hG => RefE.run_err (s₀ := ⟨s1.mem, Locals.init []⟩)
      (checkValueGroup_specE p hP.cvg n _ v g) hG.nv hG.cvg
      (cvg_ref hP.knot hP.cvg hP.knot.knot.lvc hP.apd hP.crk n hn' hS hg hCr1 hthm) c2
  rw [checkPendingE.k_check_value_group.arm1]
  obtain ⟨s2, hs2, -, hok2, hR2, hcm2, hCr2⟩ := triple_of_callE (s₀ := ⟨s1.mem, Locals.init []⟩)
    (checkValueGroup_specT .verified pins dn ds p rfl hP.cvg hP.knot hP.apd hP.crk n hn' _
      (AM.st enterScratch a₀) v (fe.restrictTo (pdAt pend j).vis) pend g _ hg hthm hR' hT1 hfl1 hCr1) c2
  subst hs2
  refine RefE.bind_right (AM.run_of_ok _ _ hok2) ?_
  refine RefE.onlySim (fun _ => checkPendingE.k_scratch_drop.none ..) (fun _ _ h => h) fun r3 m3 c3 => ?_
  rw [checkPendingE.k_scratch_drop.arm1]
  obtain ⟨s3, hs3, -, hok3, hR3, hcm3, hCr3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (drop_loopB dn ds p hb hP.leaf hP.crk (pins := pins) n _ _ vis fe pend (hR2.unrestrict hR.vis)
      hcm2 hCr2) c3
  subst hs3
  exact RefE.ret (AM.run_of_ok _ _ hok3) ⟨hR3, hcm3, hCr3⟩

/-- **`check_pending` refines `checkPending` under `StageT`** (`cpd_ref`'s ok half). -/
@[refines ConRon.Arena.checkPending]
theorem checkPending_refinesT (hm : mode = .verified) (hP : PhaseBProg p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (j vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (hj : j.toNat < pend.size) (rest : List PendingCheck)
    (hT : TwinPend fe (pdAt pend j :: rest) a₀)
    (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds) (hM : LoopMem dn s₀.mem a₀)
    (hc : CoreMemos s₀.mem) (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_pending" [j, vis]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (checkPending mode fe (pdAt pend j)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (checkPending mode fe (pdAt pend j)) a₀) vis fe pend ds ∧
      CoreMemos s'.mem ∧ L.Stubs.CrOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (checkPending_specE p hP.cp n s₀ j vis)
    (cpd_ref mode pins dn ds p hm hP (by omega) hj hT hR hM hc hCr)) ?_
  rintro r s' ⟨hloc, _, a', hrun, hp⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hloc, hok, by rw [hst]; exact hp.loop, hp.core, hp.cr⟩

/-- `check_pending` is one of the loop's functions. -/
theorem checkPending_loop : "check_pending" ∈ loopFns := loop_mem _ rfl

/-- **`check_pending` under `StageT`, carrying phase B's invariants**: the twin's (`TwinPend`, for
the records after `j`), the memory's half (`LoopMem` by the loop's write set and the twin's
`PExt`, `CoreMemos`). -/
theorem checkPending_loopT (hm : mode = .verified) (hP : PhaseBProg p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (j vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (hj : j.toNat < pend.size)
    (hT : TwinPend fe (pend.toList.drop j.toNat) a₀)
    (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds) (hM : LoopMem dn s₀.mem a₀)
    (hc : CoreMemos s₀.mem) (hj62 : j.toNat < 2 ^ 62) (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_pending" [j, vis]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (checkPending mode fe (pdAt pend j)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (checkPending mode fe (pdAt pend j)) a₀) vis fe pend ds ∧
      CoreMemos s'.mem ∧ LoopMem dn s'.mem (AM.st (checkPending mode fe (pdAt pend j)) a₀) ∧
      TwinPend fe (pend.toList.drop (j + 1).toNat) (AM.st (checkPending mode fe (pdAt pend j)) a₀) ∧
      L.Stubs.CrOK s'.mem; ⊤⦄ := by
  have h1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [drop_cons_pdAt pend j hj h1] at hT
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨h0, ho, hL, hcm, hCr'⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (checkPending_refinesT mode pins dn ds p hm hP n hn s₀ a₀ j vis fe pend hj _ hT hR hM hc hCr)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_memFrame hP.loop n checkPending_loop [j, vis] s₀)
  subst hs hm
  have hrun' := AM.run_of_ok _ _ ho
  obtain ⟨hT', hx⟩ := TwinPend.step hT hrun'
  exact ⟨h0, ho, hL, hcm, hM.step hf hx, hT', hCr'⟩

end specs

/-! ## `check_pending_go` / `check_pending_next`: one model and one refinement -/

/-- **`check_pending_go`'s unified model** (`check_pending_next` through its run: the two are
mutually recursive). -/
l_model checkPendingGo_specE (p : Prog) (hf : p.lookup "check_pending_go" = some checkPendingGoL)
  fns [hf ↦ checkPendingGoE] grind [arena_grind] unified

/-- **`check_pending_next`'s unified model** (`check_pending` and `check_pending_go` through their
runs). -/
l_model checkPendingNext_specE (p : Prog)
  (hf : p.lookup "check_pending_next" = some checkPendingNextL)
  fns [hf ↦ checkPendingNextE] grind [arena_grind] unified

/-- A record's failure is the list's failure, as a value. -/
theorem checkPendingList_fails_head {mode : ConLeche.CheckMode} {fe : IFEnv} {pc : PendingCheck}
    {rest : List PendingCheck} {a : AState} {c : Word}
    (h : ∃ ce, (checkPending mode fe pc).run a = .error ce ∧ twinCls ce = c) :
    TwinFailsV (checkPendingList mode fe (pc :: rest)) a c := by
  obtain ⟨ce, hce, hc⟩ := h
  refine .inr ⟨ce, pc.pos, AState.abandoned, ?_, hc⟩
  show (match (checkPending mode fe pc).run a with
    | .ok ((), s') => checkPendingList mode fe rest s'
    | .error e => .ok (.error (e, pc.pos), AState.abandoned)) = _
  rw [hce]

/-- A record that checks ok: the list fails as the rest does. -/
theorem checkPendingList_fails_tail {mode : ConLeche.CheckMode} {fe : IFEnv} {pc : PendingCheck}
    {rest : List PendingCheck} {a : AState} {c : Word} (hok : AM.ok (checkPending mode fe pc) a)
    (h : TwinFailsV (checkPendingList mode fe rest) (AM.st (checkPending mode fe pc) a) c) :
    TwinFailsV (checkPendingList mode fe (pc :: rest)) a c := by
  have hrun := AM.run_of_ok _ _ hok
  have e : (checkPendingList mode fe (pc :: rest)).run a =
      (checkPendingList mode fe rest).run (AM.st (checkPending mode fe pc) a) := by
    show (match (checkPending mode fe pc).run a with
      | .ok ((), s') => checkPendingList mode fe rest s'
      | .error e => .ok (.error (e, pc.pos), AState.abandoned)) = _
    rw [hrun]; rfl
  unfold TwinFailsV at h ⊢
  rw [e]; exact h

section phaseB
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog) (fe : IFEnv) (pend : Array PendingCheck)

/-- What `check_pending_go` from check `k` ends with under `StageT`: `PendPost` (phase B over the
checks from `k` accepts, the loop's relation after), the core's memos and the memory's half
`LoopMem` after. -/
def PendPostT (m : Mem) (a : AState) (v : Word) (k : Nat) : Prop :=
  PendPost mode pins dn ds fe pend m a v k ∧ CoreMemos m ∧
    LoopMem dn m (AM.st (checkPendingList mode fe (pend.toList.drop k)) a) ∧ L.Stubs.CrOK m

/-- **`check_pending_go`'s refinement at fuel `n`, both outcomes**: from phase B's twin invariant
(`TwinPend`) at check `j`, the loop's relation and the memory's half, an ok value ends in
`PendPostT`; an error (under `check_pending`'s `CpG`) claims that phase B over the
checks from `j` fails (a record's failure, as a value). -/
def CPGoRef (n : Nat) : Prop :=
  ∀ (m : Mem) (a₀ : AState) (j cnt vis : Word), j.toNat ≤ pend.size → cnt.toNat = pend.size →
    TwinPend fe (pend.toList.drop j.toNat) a₀ →
    LoopR pins dn m a₀ vis fe pend ds → LoopMem dn m a₀ → CoreMemos m → L.Stubs.CrOK m →
    RefC (CpG p) (checkPendingGoE p n m j cnt vis)
      (fun v => PendPostT mode pins dn ds fe pend v.2 a₀ vis j.toNat)
      (ErrClaimV (checkPendingList mode fe (pend.toList.drop j.toNat)) a₀)

/-- `check_pending_next`'s, the same (`j` below the count). -/
def CPNextRef (n : Nat) : Prop :=
  ∀ (m : Mem) (a₀ : AState) (j cnt vis : Word), j.toNat < pend.size → cnt.toNat = pend.size →
    TwinPend fe (pend.toList.drop j.toNat) a₀ →
    LoopR pins dn m a₀ vis fe pend ds → LoopMem dn m a₀ → CoreMemos m → L.Stubs.CrOK m →
    RefC (CpG p) (checkPendingNextE p n m j cnt vis)
      (fun v => PendPostT mode pins dn ds fe pend v.2 a₀ vis j.toNat)
      (ErrClaimV (checkPendingList mode fe (pend.toList.drop j.toNat)) a₀)

/-- `check_pending_go`'s spec under `StageT` at fuel `n`. -/
def CPGoSpecT (n : Nat) : Prop :=
  ∀ (s₀ : St) (a₀ : AState) (j cnt vis : Word), j.toNat ≤ pend.size → cnt.toNat = pend.size →
    TwinPend fe (pend.toList.drop j.toNat) a₀ →
    LoopR pins dn s₀.mem a₀ vis fe pend ds → LoopMem dn s₀.mem a₀ → CoreMemos s₀.mem →
    L.Stubs.CrOK s₀.mem →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_pending_go" [j, cnt, vis]
    ⦃fun _ s' => LocEq s' s₀ ∧ PendPostT mode pins dn ds fe pend s'.mem a₀ vis j.toNat; ⊤⦄

/-- `check_pending_next`'s spec under `StageT` at fuel `n`. -/
def CPNextSpecT (n : Nat) : Prop :=
  ∀ (s₀ : St) (a₀ : AState) (j cnt vis : Word), j.toNat < pend.size → cnt.toNat = pend.size →
    TwinPend fe (pend.toList.drop j.toNat) a₀ →
    LoopR pins dn s₀.mem a₀ vis fe pend ds → LoopMem dn s₀.mem a₀ → CoreMemos s₀.mem →
    L.Stubs.CrOK s₀.mem →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_pending_next" [j, cnt, vis]
    ⦃fun _ s' => LocEq s' s₀ ∧ PendPostT mode pins dn ds fe pend s'.mem a₀ vis j.toNat; ⊤⦄

/-- **`check_pending`'s error claim** under `checkPending_loopT`'s hypotheses (the threads' error
chain reads it at each group). -/
def CPErrT : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState) (j vis : Word), j.toNat < pend.size →
    TwinPend fe (pend.toList.drop j.toNat) a₀ →
    LoopR pins dn s₀.mem a₀ vis fe pend ds → LoopMem dn s₀.mem a₀ → CoreMemos s₀.mem →
    j.toNat < 2 ^ 62 → L.Stubs.CrOK s₀.mem →
    CoreSpecE p n "check_pending" [j, vis] (checkPending mode fe (pdAt pend j)) s₀ a₀

section cp
variable (hP : PhaseBProg p) (hm : mode = .verified)
include hP hm

/-- **`check_pending_go` and `check_pending_next` refine `checkPendingList` from check `j` on, both
outcomes**, by one induction on the fuel over the two models: `check_pending`'s ok run is the twin's
step (`checkPending_loopT`), its failure the twin's value failure at the record (`cpd_ref`); the
rest's outcome is the induction hypothesis's. -/
theorem cp_ref (n : Nat) (hn : n ≤ 2 ^ 62) :
    CPGoRef mode pins dn ds p fe pend n ∧ CPNextRef mode pins dn ds p fe pend n := by
  induction n with
  | zero =>
    constructor <;> intro _ _ _ _ _ _ _ _ _ _ _ _ <;>
      simp only [checkPendingGoE, checkPendingNextE, RefC_error] <;>
      exact fun _ => ErrClaimV.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  have ih := ih (by omega)
  have hn' : n ≤ 2 ^ 62 := by omega
  constructor
  · intro m a₀ j cnt vis hj hc hT hR hM hcm hCr
    simp only [checkPendingGoE]
    by_cases g1 : j = cnt
    · rw [ite_eq_left g1]
      have e : pend.toList.drop j.toNat = [] := by simp [g1, hc]
      have := checkPendingList_nil_ok mode fe a₀
      simp only [RefC_ok, PendPostT, PendPost, e]
      exact ⟨⟨this.1, this.2.2, by rw [this.2.1]; exact hR⟩, hcm, by rw [this.2.1]; exact hM, hCr⟩
    rw [ite_eq_right g1]
    have hlt : j.toNat < pend.size := by
      have : j.toNat ≠ cnt.toNat := fun e => g1 (UInt64.toNat_inj.mp e)
      omega
    have hs := checkPendingNext_specE p hP.cpx n ⟨m, Locals.init []⟩ j cnt vis
    have hr := ih.2 m a₀ j cnt vis hlt hc hT hR hM hcm hCr
    cases h1 : callE p n "check_pending_next" [j, cnt, vis] m with
    | error e1 =>
      rw [checkPendingGoE.k_check_pending_next.none]
      exact fun hE => RefC.run_err hs (fun _ h0 => ErrClaimV.of_cls0 h0) trivial hE hr h1
    | ok q =>
      obtain ⟨r, m₁⟩ := q
      rw [checkPendingGoE.k_check_pending_next.arm1]
      obtain ⟨s', rfl, -, hpost⟩ := RefC.run_ok hs hr h1
      exact hpost
  · intro m a₀ j cnt vis hj hc hT hR hM hcm hCr
    simp only [checkPendingNextE]
    by_cases g1 : 4611686018427387904 ≤ j
    · rw [ite_eq_left g1]; exact fun _ => ErrClaimV.of_cls0 rfl
    rw [ite_eq_right g1]
    have h62 : j.toNat < 2 ^ 62 := by
      have : ¬ (4611686018427387904 : Word).toNat ≤ j.toNat := fun h => g1 (UInt64.le_iff_toNat_le.mpr h)
      simp at this; omega
    have h1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hd := drop_cons_pdAt pend j hj h1
    cases hc1 : callE p n "check_pending" [j, vis] m with
    | error e1 =>
      rw [checkPendingNextE.k_check_pending.none]
      intro hE hk0
      rw [hd] at hT ⊢
      exact checkPendingList_fails_head
        (RefE.run_err (checkPending_specE p hP.cp n ⟨m, Locals.init []⟩ j vis) hE.nv hE
          (cpd_ref mode pins dn ds p hm hP (by omega) hj hT hR hM hcm hCr) hc1 hk0)
    | ok q =>
    obtain ⟨r, m₁⟩ := q
    obtain ⟨s', hs', -, hok, hR', hcm', hM', hT', hCr'⟩ := triple_of_callE
      (checkPending_loopT mode pins dn ds p hm hP n hn' ⟨m, Locals.init []⟩ a₀ j vis fe pend hj hT hR
        hM hcm h62 hCr) hc1
    subst hs'
    simp only [checkPendingNextE.k_check_pending]
    have hs := checkPendingGo_specE p hP.cpg n ⟨s'.mem, Locals.init []⟩ (j + 1) cnt vis
    have hr := ih.1 s'.mem _ (j + 1) cnt vis (by omega) hc hT' hR' hM' hcm' hCr'
    cases hc2 : callE p n "check_pending_go" [j + 1, cnt, vis] s'.mem with
    | error e2 =>
      rw [checkPendingNextE.k_check_pending_go.none]
      intro hE hk0
      rw [hd]
      exact checkPendingList_fails_tail hok
        (RefC.run_err hs (fun _ h0 => ErrClaimV.of_cls0 h0) trivial hE hr hc2 hk0)
    | ok q2 =>
    obtain ⟨r2, m₂⟩ := q2
    rw [checkPendingNextE.k_check_pending_go.arm1]
    obtain ⟨s'', rfl, -, hp⟩ := RefC.run_ok hs hr hc2
    obtain ⟨⟨hp1, hp2, hp3⟩, hp4, hp5, hp6⟩ := hp
    have := checkPendingList_cons_ok mode fe (pdAt pend j) (pend.toList.drop (j + 1).toNat) a₀ hok hp1
    refine ⟨⟨?_, ?_, ?_⟩, hp4, ?_, hp6⟩
    · rw [hd]; exact this.1
    · rw [hd, this.2.2]; exact hp2
    · rw [hd, this.2.1]; exact hp3
    · rw [hd, this.2.1]; exact hp5

/-- **`check_pending_go` refines `checkPendingList` under `StageT`** from check `j` on (and
`check_pending_next` for one check and the rest): `cp_ref`'s ok halves as triples. -/
@[refines ConRon.Arena.checkPendingList]
theorem checkPendingGo_refinesT (n : Nat) (hn : n ≤ 2 ^ 62) :
    CPGoSpecT mode pins dn ds p fe pend n ∧ CPNextSpecT mode pins dn ds p fe pend n := by
  have h := cp_ref mode pins dn ds p fe pend hP hm n hn
  constructor
  · intro s₀ a₀ j cnt vis hj hc hT hR hM hcm hCr
    exact (RefC.triple (checkPendingGo_specE p hP.cpg n s₀ j cnt vis)
      (h.1 s₀.mem a₀ j cnt vis hj hc hT hR hM hcm hCr) :)
  · intro s₀ a₀ j cnt vis hj hc hT hR hM hcm hCr
    exact (RefC.triple (checkPendingNext_specE p hP.cpx n s₀ j cnt vis)
      (h.2 s₀.mem a₀ j cnt vis hj hc hT hR hM hcm hCr) :)

/-- **L's phase B under `StageT` refines phase B on the worker** (the second half of
`SeqAccepts`): a returning `check_pending_go(0, cnt, vis)` from phase A's memory (the twin's
caches are empty: `TwinPend.caches`) means the twin's phase B on `a₀.worker` accepts; beside it
`PendPostT` (the loop's relation, `CoreMemos`, `LoopMem` after phase B on `a₀`). -/
@[refines ConRon.Arena.AState.worker]
theorem checkPendingGo_workerT (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (cnt vis : Word) (hcnt : cnt.toNat = pend.size) (hT : TwinPend fe pend.toList a₀)
    (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds) (hM : LoopMem dn s₀.mem a₀)
    (hc : CoreMemos s₀.mem) (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_pending_go" [0, cnt, vis]
    ⦃fun _ s' => LocEq s' s₀ ∧
      (∃ s'', checkPendingList mode fe pend.toList a₀.worker = .ok (.ok (), s'')) ∧
      PendPostT mode pins dn ds fe pend s'.mem a₀ vis 0; ⊤⦄ := by
  refine triple_post ((checkPendingGo_refinesT mode pins dn ds p fe pend hP hm n hn).1
    s₀ a₀ 0 cnt vis (by simp) hcnt (by simpa using hT) hR hM hc hCr) ?_
  rintro r s' ⟨hl, hpost⟩
  refine ⟨hl, ?_, by simpa using hpost⟩
  obtain ⟨⟨hok, hres, -⟩, -⟩ := hpost
  have hrun := AM.run_of_ok _ _ hok
  simp only [UInt64.toNat_zero, List.drop_zero] at hrun hres
  rw [hres] at hrun
  exact checkPendingList_worker_ok hT.caches hrun

/-- `CPErrT` from `cpd_ref`. -/
theorem checkPending_errT (hG : CpG p) : CPErrT mode pins dn ds p fe pend := by
  intro n hn s₀ a₀ j vis hj hT hR hM hc hj62 hCr
  have h1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [drop_cons_pdAt pend j hj h1] at hT
  exact RefE.coreSpecE (checkPending_specE p hP.cp n s₀ j vis) hG.nv hG
    (cpd_ref mode pins dn ds p hm hP (by omega) hj hT hR hM hc hCr)

end cp
end phaseB

end L.Arena
