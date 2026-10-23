import ConAgua.Arena.LoopT
import ConAgua.Arena.DeclCvgT
import ConAgua.Arena.DeclArmT
import ConAgua.Arena.LeafFns
import ConAgua.Arena.PhaseWorker

/-!
# Phase B under `StageT` (lane `loopt3`, items 12 and 12a)

`Checker.lean`'s `checkPendingGo_refines` runs `check_value_group` through its stubs
(`checkValueGroup_spec`, `stubCall`). Here phase B runs it from `StageT` with the program's own
core (`cvgW_okT`, `realCall p`). Per pending check:

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
set_option linter.unusedSimpArgs false

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
    s'.caches = Caches.empty ∧ s'.store.scratchOn = false := by
  have hd : ∀ {t t' : AState} {u : Unit}, dropScratch t = .ok (u, t') →
      t'.caches = Caches.empty ∧ t'.store.scratchOn = false :=
    fun h => by
      simp only [dropScratch, flushCaches, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure, Except.bind] at h
      cases h; exact ⟨rfl, rfl⟩
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
            exact ⟨fun _ => hk.1 h2.1, fun _ => hk.2 h2.2⟩

/-- Item 12a in the `AM` form. -/
theorem installFold_cachesAM {mode : ConLeche.CheckMode} {pins : List INatOpPinSet}
    {ds : List IDeclaration} {p q : Nat × IFEnv × Array PendingCheck} {a : AState}
    (hc : a.caches = Caches.empty) (hok : AM.ok (installFold mode pins p ds) a)
    (hres : AM.res (installFold mode pins p ds) a = .ok q) :
    (AM.st (installFold mode pins p ds) a).caches = Caches.empty := by
  have hrun := AM.run_of_ok _ _ hok
  rw [hres] at hrun
  exact (installFold_drop ds p q a _ hrun).1 hc

/-- **Phase B's twin invariant** before the records `pend` (the remaining ones): con-ron's
`FoldOK` at the final environment `env` (names unique), each remaining record related to its pure
value group at the store (`PendRel`), the caches empty and the scratch tier off. -/
structure TwinPend (fe : IFEnv) (pend : List PendingCheck) (a : AState) : Prop where
  fold : ∃ env pendP, FoldOK V env fe a ∧ ConLeche.NodupNames env ∧
    ListRel (PendRel a.store env) pend pendP
  caches : a.caches = Caches.empty
  off : a.store.scratchOn = false

/-- **`TwinPend` at phase B's start**, from `TwinFold` at the loop's start (caches empty) and
phase A's accepting twin run (`Arena.installFold_bridge`, `PhaseA.nodup`, `installFold_drop`). -/
theorem TwinPend.start {pins : List INatOpPinSet} {ds : Array IDeclaration} {a₀ a : AState}
    {k : Nat} {fe : IFEnv} {pend : Array PendingCheck}
    (hT : TwinFold pins ds (mkIFEnv IEnv.empty) #[] a₀) (hc : a₀.caches = Caches.empty)
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
  exact ⟨⟨env', pendP', hok', hA.nodup hnd, by simpa using hrel⟩, hd.1 hc, hd.2 hT.off⟩

/-- `TwinPend` at the `AM` form of phase A's run. -/
theorem TwinPend.startAM {pins : List INatOpPinSet} {ds : Array IDeclaration} {a₀ : AState}
    {k : Nat} {fe : IFEnv} {pend : Array PendingCheck}
    (hT : TwinFold pins ds (mkIFEnv IEnv.empty) #[] a₀) (hc : a₀.caches = Caches.empty)
    (hok : AM.ok (installFold V pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)
    (hres : AM.res (installFold V pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀ =
      .ok (k, fe, pend)) :
    TwinPend fe pend.toList (AM.st (installFold V pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) := by
  have hrun := AM.run_of_ok _ _ hok
  rw [hres] at hrun
  exact TwinPend.start hT hc hrun

/-- **con-ron's `CheckOK` at a record's view**: the prefix environment, the restricted index
(`IFEnvOK_prefix`), the caches empty. -/
theorem TwinPend.checkAt {fe : IFEnv} {pc : PendingCheck} {rest : List PendingCheck} {a : AState}
    (h : TwinPend fe (pc :: rest) a) :
    ∃ env, ConRon.Bridge.CheckOK V env (fe.restrictTo pc.vis) a := by
  obtain ⟨env, -, hok, hnd, -⟩ := h.fold
  exact ⟨env.prefixTo pc.vis,
    { state := hok.check.state
      caches := ConRon.Bridge.CacheOK.of_empty h.caches
      pins := hok.check.pins
      ienv := ConRon.Bridge.IFEnvOK_prefix hok hnd pc.vis }⟩

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
    have hpre := hp.prefix
    obtain ⟨hok₁, hx₁, hc₁, -⟩ :=
      ConRon.Bridge.Arena.checkPending_prefix rfl hk hok hp.pers hnd h.caches
        (by rw [hpre]; exact hp.envWF) hp.kind hp.cv hp.jv hp.wsty hp.wsjv hrun
    have hoff : a'.store.scratchOn = false := by
      simp only [checkPending] at hrun
      obtain ⟨_, s1, -, r1⟩ := ConRon.Bridge.AM.bind_ok hrun
      obtain ⟨_, s2, -, r2⟩ := ConRon.Bridge.AM.bind_ok r1
      rw [ConRon.Bridge.dropScratch_run] at r2
      simp only [Except.ok.injEq, Prod.mk.injEq] at r2
      obtain ⟨-, rfl⟩ := r2
      rfl
    exact ⟨⟨⟨env, _, hok₁, hnd, PendRel.listRel_mono hx₁ ⟨[], rfl⟩ hrest⟩, hc₁, hoff⟩, hx₁⟩

end twin

end L.Arena
