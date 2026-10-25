import ConRon.Bridge.Checker.Split
import ConAgua.Arena.Refine
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Frontend.Shared
import ConRon.Bridge.Frontend.Capstone

/-!
# The twin's fold invariant, step by step (lane `decls4`)

The L side compares literal handles where the twin compares literal values (`canon_expr_eq`,
lane `decls3`'s `LitInj`), which is sound because the twin's store is well formed
(`StateOK`: con-ron's `EWFAt.view_inj`). The stage relation `StageR` relates memories to twin
states but says nothing about the twin state's own well-formedness, and no L-side relation can
give it. So the loop carries it on the twin side alone: `TwinFold` is con-ron's
`installFold_bridge` induction invariant (`FoldOK`, unique names, the pins and the records
denote, persistence), and `TwinFold.step` is that induction's step (`installStep_split`), applied
to the twin run the L step refines. From it, every state the step's arms start from is
`StateOK` (`TwinFold.stateOK`, `.andPin`, `.enter`).

Pure twin reasoning: no L, no memory.
-/

open ConLeche ConRon.Arena

namespace ConRon.Bridge

/-- A record of a denoting list denotes. -/
theorem denoteDecl_of_mem {st : EStore} :
    ∀ {ds : List IDeclaration} {xs : List Declaration}, denoteDecls st ds = some xs →
      ∀ d ∈ ds, ∃ x, Frontend.denoteDecl st d = some x
  | [], _, _, d, hd => absurd hd (by simp)
  | a :: as, xs, h, d, hd => by
    simp only [denoteDecls] at h
    cases ha : Frontend.denoteDecl st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : denoteDecls st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rcases List.mem_cons.mp hd with rfl | hd
        · exact ⟨x, ha⟩
        · exact denoteDecl_of_mem has d hd

/-- A well-formed store hash-conses: two handles with the same view are equal (con-ron's
`EWFAt.view_inj`). This is what makes L's comparison of literal handles the twin's comparison of
literal values (`LitInj`). -/
theorem StateOK.view_inj {a : AState} (h : StateOK a) {x y : EIdx} {v : ENodeView}
    (hx : a.store.view x = some v) (hy : a.store.view y = some v) : x = y := by
  obtain ⟨rk, hw⟩ := h.wf
  exact hw.view_inj hx hy

end ConRon.Bridge

namespace L.Arena

open ConRon.Bridge

/-- **The twin's fold invariant** at a loop head: the state `a`, the environment `fe`, the pending
records `pend`, for the pin list `pins` and the records `ds` (con-ron's `installFold_bridge`
hypotheses, the pending relation weakened to persistence). -/
structure TwinFold (pins : List INatOpPinSet) (ds : Array IDeclaration) (fe : IFEnv)
    (pend : Array PendingCheck) (a : AState) : Prop where
  fold : ∃ env, FoldOK .verified env fe a ∧ NodupNames env
  pinsD : ∃ pinsP, PinsDenote a.store pins pinsP
  pp : PersPinSets pins
  pd : ∀ x ∈ ds.toList, PersDecl x
  den : ∃ dsP, denoteDecls a.store ds.toList = some dsP
  pend : ∀ pc ∈ pend.toList, PersVG pc.vg
  /-- The scratch tier is off (every step ends in `dropScratch`): the bracket's `enterScratch`
  then changes no denotation (`TwinOK.enter`). -/
  off : a.store.scratchOn = false

/-- **A step ends with the scratch tier off** (`dropScratch` last on both arms). -/
theorem installStep_off {mode : CheckMode} {pins : List INatOpPinSet} {i : Nat} {fe : IFEnv}
    {pend : Array PendingCheck} {pd : IDeclaration} {s s' : AState}
    {x : IFEnv × Array PendingCheck} (h : installStep mode pins i fe pend pd s = .ok (x, s')) :
    s'.store.scratchOn = false := by
  have hd : ∀ {t t' : AState} {u : Unit}, dropScratch t = .ok (u, t') → t'.store.scratchOn = false :=
    fun h => by
      simp only [dropScratch, flushCaches, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure, Except.bind] at h
      cases h; rfl
  simp only [installStep] at h
  obtain ⟨_, s1, -, h⟩ := AM.bind_ok h
  obtain ⟨_, s2, -, h⟩ := AM.bind_ok h
  obtain ⟨⟨fe', vg⟩, s3, -, h⟩ := AM.bind_ok h
  cases vg with
  | none =>
    obtain ⟨⟨_, _⟩, s4, -, h⟩ := AM.bind_ok h
    obtain ⟨_, s5, h5, h⟩ := AM.bind_ok h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact hd h5
  | some vg =>
    obtain ⟨⟨_, _⟩, s4, -, h⟩ := AM.bind_ok h
    obtain ⟨⟨_, _⟩, s5, -, h⟩ := AM.bind_ok h
    obtain ⟨_, s6, h6, h⟩ := AM.bind_ok h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact hd h6

/-- **The fold's start, con-ron's `FoldOK` at the empty environment** (`FoldOK_of_start`), from the
twin facts the pipeline has before the fold: `StateOK`, `PinsOK`, `PersPins` and the
per-declaration caches empty. -/
theorem foldOK_start {s : AState} (hok : StateOK s) (hpins : PinsOK s) (hpp : PersPins s)
    (hc : s.caches = Caches.empty) :
    FoldOK .verified Env.empty (mkIFEnv IEnv.empty) s :=
  Frontend.FoldOK_of_start hok hpins hpp (CacheOK.of_empty hc)

/-- **`TwinFold` at the loop's start** (lane `loopt2`, for lane `pipeline`'s R7 → start lemma):
`foldOK_start`, the pins' and records' denotations and persistence, the scratch tier off. -/
theorem TwinFold.start {pins : List INatOpPinSet} {ds : Array IDeclaration} {s : AState}
    (hok : StateOK s) (hpins : PinsOK s) (hpp : PersPins s) (hc : s.caches = Caches.empty)
    (hpd : ∃ pinsP, PinsDenote s.store pins pinsP) (hps : PersPinSets pins)
    (hdp : ∀ x ∈ ds.toList, PersDecl x) (hden : ∃ dsP, denoteDecls s.store ds.toList = some dsP)
    (hoff : s.store.scratchOn = false) : TwinFold pins ds (mkIFEnv IEnv.empty) #[] s :=
  ⟨⟨Env.empty, foldOK_start hok hpins hpp hc, by simp [NodupNames, Env.empty]⟩, hpd, hps, hdp, hden,
    by simp, hoff⟩

namespace TwinFold

variable {pins : List INatOpPinSet} {ds : Array IDeclaration} {fe : IFEnv}
  {pend : Array PendingCheck} {a : AState}

theorem stateOK (h : TwinFold pins ds fe pend a) : StateOK a := by
  obtain ⟨env, hok, -⟩ := h.fold
  exact hok.check.state

theorem pinsOK (h : TwinFold pins ds fe pend a) : PinsOK a := by
  obtain ⟨env, hok, -⟩ := h.fold
  exact hok.check.pins

/-- Record `i` denotes. -/
theorem denote (h : TwinFold pins ds fe pend a) {i : Nat} (hi : i < ds.size) :
    ∃ x, Frontend.denoteDecl a.store ds[i] = some x := by
  obtain ⟨dsP, hd⟩ := h.den
  exact denoteDecl_of_mem hd _ (by simp)

/-- After the `And` pin's run, the state is `StateOK`. -/
theorem andPin (h : TwinFold pins ds fe pend a) {i : Nat} (hi : i < ds.size) {b : Bool}
    {a' : AState} (hrun : andPinOk ds[i] a = .ok (b, a')) : StateOK a' := by
  obtain ⟨x, hx⟩ := h.denote hi
  exact (andPinOk_run h.stateOK h.pinsOK hx hrun).1

/-- The bracket's opening keeps `StateOK`. -/
theorem enter {a a' : AState} (h : StateOK a) (hs : a'.store = a.store.enableScratch) :
    StateOK a' :=
  ⟨hs ▸ EStore.enableScratch_wf h.wf⟩

/-- **The fold's step**: an accepting `installDeclStep` on record `i` keeps the invariant, and the
store only grows on its persistent tier (`PExt`). -/
theorem step_pext (h : TwinFold pins ds fe pend a) {i : Nat} (hi : i < ds.size) {k : Nat}
    {fe' : IFEnv} {pend' : Array PendingCheck} {a' : AState}
    (hrun : installDeclStep .verified pins (i, fe, pend) ds[i] a = .ok (.ok (k, fe', pend'), a')) :
    TwinFold pins ds fe' pend' a' ∧ PExt a.store a'.store := by
  have hk : CoreSpec .verified ConRon.Arena.checkFuel := CoreSpec.of_core rfl
  have hind : IndSpec .verified := ConRon.Bridge.Inductives.indSpec_of_bridge rfl hk
  obtain ⟨env, hok, hnd⟩ := h.fold
  obtain ⟨pinsP, hpins⟩ := h.pinsD
  obtain ⟨dsP, hden⟩ := h.den
  obtain ⟨x, ha⟩ := h.denote hi
  have hmem : ds[i] ∈ ds.toList := by simp
  simp only [installDeclStep] at hrun
  cases hP : andPinOk ds[i] a with
  | error e => rw [hP] at hrun; simp at hrun
  | ok w =>
  obtain ⟨bA, s₀⟩ := w
  cases bA with
  | false => rw [hP] at hrun; simp at hrun
  | true =>
  rw [hP] at hrun
  simp only at hrun
  obtain ⟨hok0, hx0, hc0, hp0⟩ := andPinOk_run hok.check.state hok.check.pins ha hP
  have hok' : FoldOK .verified env fe s₀ := hok.step (hok.check.mono hok0 hx0 hc0 hp0) hx0 hp0
  have hx0' : PExt a.store s₀.store := PExt.of_ext hx0
  have hpins0 := PinsDenote.pmono hx0' _ _ h.pp hpins
  have ha0 : Frontend.denoteDecl s₀.store ds[i] = some x := denoteDecl_pext hx0' (h.pd _ hmem) ha
  cases hA : installStep .verified pins i fe pend ds[i] s₀ with
  | error e => rw [hA] at hrun; simp at hrun
  | ok v =>
  obtain ⟨⟨fe₁, pend₁⟩, s₁⟩ := v
  rw [hA] at hrun
  simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := hrun
  obtain ⟨env₁, hok₁, hx₁', -, hpend₁, -, -, -, hcase⟩ :=
    Arena.installStep_split rfl hk hind hok' hnd hpins0 h.pp h.pend (h.pd _ hmem) ha0 hA
  have hx₁ : PExt a.store s₁.store := hx0'.trans hx₁'
  have hnd₁ : NodupNames env₁ := by
    rcases hcase with ⟨-, F, hF⟩ | ⟨pc, gP, F, -, -, -, hsplit, -⟩
    · exact checkDecl_nodup hF hnd
    · exact hsplit.nodup hnd
  exact ⟨⟨⟨env₁, hok₁, hnd₁⟩, ⟨pinsP, PinsDenote.pmono hx₁ _ _ h.pp hpins⟩, h.pp, h.pd,
    ⟨dsP, denoteDecls_pext hx₁ _ _ h.pd hden⟩, hpend₁, installStep_off hA⟩, hx₁⟩

/-- **The fold's step**: an accepting `installDeclStep` on record `i` keeps the invariant. -/
theorem step (h : TwinFold pins ds fe pend a) {i : Nat} (hi : i < ds.size) {k : Nat}
    {fe' : IFEnv} {pend' : Array PendingCheck} {a' : AState}
    (hrun : installDeclStep .verified pins (i, fe, pend) ds[i] a = .ok (.ok (k, fe', pend'), a')) :
    TwinFold pins ds fe' pend' a' :=
  (h.step_pext hi hrun).1

/-! ## In the `AM.ok`/`AM.st` form the loop's theorems use -/

theorem andPinAM (h : TwinFold pins ds fe pend a) {i : Nat} (hi : i < ds.size)
    (hok : AM.ok (andPinOk ds[i]) a) : StateOK (AM.st (andPinOk ds[i]) a) :=
  h.andPin hi (AM.run_of_ok _ _ hok)

theorem enterAM {a : AState} (h : StateOK a) :
    StateOK (AM.st enterScratch (AM.st flushCaches a)) :=
  enter h rfl

theorem stepAM (h : TwinFold pins ds fe pend a) {i : Nat} (hi : i < ds.size) {k : Nat}
    {fe' : IFEnv} {pend' : Array PendingCheck}
    (hok : AM.ok (installDeclStep .verified pins (i, fe, pend) ds[i]) a)
    (hres : AM.res (installDeclStep .verified pins (i, fe, pend) ds[i]) a = .ok (k, fe', pend')) :
    TwinFold pins ds fe' pend' (AM.st (installDeclStep .verified pins (i, fe, pend) ds[i]) a) := by
  have := AM.run_of_ok _ _ hok
  rw [hres] at this
  exact h.step hi this

end TwinFold

end L.Arena
