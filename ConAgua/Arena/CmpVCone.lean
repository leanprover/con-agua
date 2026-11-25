module

public import ConRon.Bridge.Compare.Cone
public import ConAgua.Arena.CmpVMates
public import ConRon.Bridge.Modular.Roots
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.Canon

@[expose] public section

/-!
# The cone walk meets only names that read back (lane compare2, helper compare2-verdict)

The twin's rejection of an unjustified statement (`justifyWhy`, `checkJustified`) reads names back
(`readNameM`), which fails `.internal` (class `0`) on a name handle that does not denote. A
rejection of a compared run is a verdict only if those reads succeed. They do:

* `readNameM_ok`: a denoting handle reads back, the store kept;
* `entryNeeds_den`: every handle `entryNeeds` lists denotes (con-ron's `Bridge/Modular/Roots.lean` reads
  a constant's and a table's names back exactly; the recursors' names are interned from denoting
  ones; the mates denote by `CvMatesDen`);
* `coneEntry_den`, `coneGo_den`: from a work list of denoting handles, the walk's culprit denotes.

con-ron's `Bridge/Compare/Cone.lean` proves the walk's accept (`coneGo_run`); this is the reject.
-/

namespace ConRon.Bridge.CmpV

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge
open ConRon.Bridge.Modular (NSeen XRel names_exact const_exact table_exact)

/-- con-leche: none — every handle of the list denotes. -/
def AllDen (st : EStore) (hs : List NIdx) : Prop := ∀ h ∈ hs, ∃ nm, denoteN st.ns h = some nm

theorem AllDen.ext {st st' : EStore} {hs : List NIdx} (h : AllDen st hs) (hx : Ext st st') :
    AllDen st' hs := fun k hk => let ⟨nm, hd⟩ := h k hk; ⟨nm, denoteN_ext hd hx⟩

theorem allDen_of_denoteNList {st : EStore} {hs : List NIdx} {L : List ConLeche.Name}
    (h : Frontend.denoteNList st.ns hs = some L) : AllDen st hs := denoteNList_mem h

theorem denoteNList_of_allDen {st : EStore} :
    ∀ {hs : List NIdx}, AllDen st hs → ∃ L, Frontend.denoteNList st.ns hs = some L
  | [], _ => ⟨[], rfl⟩
  | h :: hs, H => by
    obtain ⟨x, hx⟩ := H h List.mem_cons_self
    obtain ⟨L, hL⟩ := denoteNList_of_allDen (hs := hs) (fun k hk => H k (List.mem_cons_of_mem _ hk))
    exact ⟨x :: L, by simp only [Frontend.denoteNList, hx, hL]⟩

/-- con-leche: none — **a denoting name handle reads back**, the store kept. -/
theorem readNameM_ok {s : AState} {h : NIdx} {nm : ConLeche.Name}
    (hd : denoteN s.store.ns h = some nm) :
    ∃ x s', readNameM h s = .ok (x, s') ∧ s'.store = s.store := by
  cases hc : s.caches.readNC[h]? with
  | some x =>
    refine ⟨x, s, ?_, rfl⟩
    simp only [readNameM, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, Except.bind, Except.pure, hc]
  | none =>
    refine ⟨nm, { s with caches := { s.caches with readNC := s.caches.readNC.insert h nm } }, ?_, rfl⟩
    simp only [readNameM, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, Except.bind, Except.pure, hc, hd, set, StateT.set]

/-! ## The walk's state, at a larger store -/

theorem _root_.ConRon.Bridge.Modular.NSeen.ext {st st' : EStore} {seen : Std.HashMap EIdx Bool} {seenP : Std.HashSet Expr}
    (h : NSeen st seen seenP) (hx : Ext st st') : NSeen st' seen seenP where
  fwd := fun k e he hc => by
    obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp (h.dom k hc)
    rw [denote_ext he0 hx] at he
    obtain rfl := Option.some.inj he
    exact h.fwd k e0 he0 hc
  bwd := fun eP hc => let ⟨k, hk, hd⟩ := h.bwd eP hc; ⟨k, hk, denote_ext hd hx⟩
  dom := fun k hc => by
    obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp (h.dom k hc)
    rw [denote_ext he0 hx]; rfl

theorem _root_.ConRon.Bridge.Modular.XRel.ext {st st' : EStore} {x : Arena.NeedsSt} {xP : ConLeche.Cached.NeedsSt}
    (h : XRel st x xP) (hx : Ext st st') : XRel st' x xP :=
  ⟨h.1.ext hx, denoteNListE_ext hx _ _ h.2⟩

/-! ## What `entryNeeds` lists -/

/-- con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds — the recursors' names, interned:
each new handle denotes. -/
theorem recNames_den {s : AState} (hok : StateOK s) :
    ∀ (ms out : List NIdx) {r : List NIdx} {s' : AState}, AllDen s.store ms →
      Arena.recNames out ms s = .ok (r, s') →
      Frontend.IStepS s s' ∧ ∀ k ∈ r, k ∈ out ∨ ∃ nm, denoteN s'.store.ns k = some nm
  | [], out, r, s', _, hrun => by
    simp only [Arena.recNames] at hrun
    obtain ⟨hr, hs⟩ := AM.pure_ok hrun
    subst hr hs
    exact ⟨Frontend.IStepS.refl hok, fun k hk => .inl hk⟩
  | m :: ms, out, r, s', hms, hrun => by
    obtain ⟨y, hy⟩ := hms m List.mem_cons_self
    simp only [Arena.recNames] at hrun
    obtain ⟨n, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨st1, hn⟩ := Frontend.internNNode_sstep hok
      (by intro c hc
          simp only [NNodeView.children, List.mem_singleton] at hc
          subst hc
          exact nview_isSome_of_denote hy) h1
    have hn' : denoteN s1.store.ns n = some (y.str "rec") := by
      rw [hn, denoteNView, denoteN_ext hy st1.ext, Option.map_some]
    obtain ⟨st2, hr⟩ := recNames_den st1.ok ms (out ++ [n])
      (fun k hk => (hms k (List.mem_cons_of_mem _ hk)).elim fun nm hd => ⟨nm, denoteN_ext hd st1.ext⟩)
      h2
    refine ⟨st1.trans st2, fun k hk => ?_⟩
    rcases hr k hk with hk | hk
    · rcases List.mem_append.mp hk with hk | hk
      · exact .inl hk
      · rw [List.mem_singleton] at hk; subst hk
        exact .inr ⟨_, denoteN_ext hn' st2.ext⟩
    · exact .inr hk

theorem names_den {st : EStore} {x : Arena.NeedsSt} {xP : ConLeche.Cached.NeedsSt}
    (hx : XRel st x xP) {ns : List NIdx} (hns : AllDen st ns) :
    ∃ yP, XRel st (x.names ns) yP := by
  obtain ⟨L, hL⟩ := denoteNList_of_allDen hns
  exact ⟨_, names_exact hx hL⟩

/-- con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds — **every handle `entryNeeds`
lists denotes**. -/
theorem entryNeeds_den {env : Env} {fe : IFEnv} {s s' : AState} {ci : IConstantInfo}
    {c : ConstantInfo} {mates : Std.HashMap NIdx (List NIdx)} {ns : List NIdx}
    (hck : CheckOK false env fe s)
    (hc : Frontend.denoteCI s.store ci = some c) (hm : CvMatesDen s.store mates)
    (hrun : Arena.entryNeeds mates fe ci s = .ok (ns, s')) :
    AllDen s'.store ns := by
  have hok := hck.state
  have hp := hck.pins
  have hr0 := hck.readOK
  simp only [Arena.entryNeeds] at hrun
  obtain ⟨x0, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, o0⟩ := const_exact hok hp (XRel.empty s.store) hc h1
  rw [hs1] at h2
  -- the type former's constructors and recursors; then the mates and the table
  have tail : ∀ {x2 : Arena.NeedsSt} {x2P : ConLeche.Cached.NeedsSt} {s2 : AState},
      RStep s s2 → XRel s2.store x2 x2P →
      (do
        let x3 := match mates[ci.name]? with
          | some ms => x2.names ms
          | none => x2
        match fe.findTable? ci.name with
        | some t => do
          let x4 ← x3.table t
          pure x4.acc
        | none => pure x3.acc : AM (List NIdx)) s2 = .ok (ns, s') →
      AllDen s'.store ns := by
    intro x2 x2P s2 hst hx2 hrun
    have hck2 := hst.checkOK hck
    have last : ∀ {x3 : Arena.NeedsSt} {x3P : ConLeche.Cached.NeedsSt}, XRel s2.store x3 x3P →
        (match fe.findTable? ci.name with
          | some t => do
            let x4 ← x3.table t
            pure x4.acc
          | none => pure x3.acc : AM (List NIdx)) s2 = .ok (ns, s') →
        AllDen s'.store ns := by
      intro x3 x3P hx3 hrun
      cases ht : fe.findTable? ci.name with
      | some t =>
        rw [ht] at hrun
        obtain ⟨x4, s4, h4, h5⟩ := AM.bind_ok hrun
        obtain ⟨-, pt, -, hpt, -, -⟩ := hck2.ienv.tblHit _ t ht
        obtain ⟨rfl, o4⟩ := table_exact hck2.state hck2.pins hx3 hpt h4
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h5
        exact allDen_of_denoteNList o4.2
      | none =>
        rw [ht] at hrun
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
        exact allDen_of_denoteNList hx3.2
    cases hmt : mates[ci.name]? with
    | some ms =>
      simp only [hmt] at hrun
      obtain ⟨x3P, hx3⟩ := names_den hx2 (fun k hk => (hm _ ms hmt k hk).2.elim fun nm hd =>
        ⟨nm, denoteN_ext hd hst.ext⟩)
      exact last hx3 hrun
    | none =>
      simp only [hmt] at hrun
      exact last hx2 hrun
  cases ci
  case indInfo v cap =>
    obtain ⟨cv, d, rfl, -, hd⟩ := denoteCI_ind_inv hc
    simp only [Frontend.denoteCaps] at hd
    split at hd
    · next all ctors hall hctors =>
      obtain ⟨rn, s2, h3, h4⟩ := AM.bind_ok h2
      obtain ⟨x1P, o1⟩ := names_den o0 (allDen_of_denoteNList hctors)
      obtain ⟨st2, hrn⟩ := recNames_den hok cap.all [] (allDen_of_denoteNList hall) h3
      obtain ⟨y, s3, h5, h6⟩ := AM.bind_ok h4
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h5
      obtain ⟨x2P, o2⟩ := names_den (o1.ext st2.ext) (fun k hk => (hrn k hk).elim
        (fun h => nomatch h) id)
      exact tail (RStep.of_istep st2 hr0) o2 h6
    · exact absurd hd (by simp)
  all_goals
    obtain ⟨y, s3, h5, h6⟩ := AM.bind_ok h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h5
    exact tail (RStep.refl hok hr0) o0 h6

/-! ## The cone walk's culprit -/

/-- con-leche: ConLeche/Cached/Justify.lean:163-183 coneGo — **one name of the cone, compared**:
a renaming step, and an accepted name's reads denote. -/
theorem coneEntry_den {env envS : Env} {fe : IFEnv} {J : ISolution}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)} {n : NIdx}
    {o : Option (List NIdx)} {s s' : AState} (hck : CheckOK false env fe s)
    (hsol : IFEnvOK envS (SolView J) s) (hm : MatesDen s.store J.mates matesU)
    (hcm : CvMatesDen s.store J.mates)
    (hrun : coneEntry J fe n s = .ok (o, s')) :
    RStep s s' ∧ ∀ ns, o = some ns → AllDen s'.store ns := by
  have hok := hck.state
  have hr := hck.readOK
  cases o with
  | some ns =>
    obtain ⟨hst, -⟩ := coneEntry_run hck hsol hm hrun
    refine ⟨hst, fun ns' e => ?_⟩
    obtain rfl := Option.some.inj e
    simp only [coneEntry] at hrun
    cases hf : fe.find? n with
    | none => rw [hf] at hrun; exact nomatch (AM.pure_ok hrun).1
    | some ci =>
    rw [hf] at hrun
    obtain ⟨nm, c, -, hc, -⟩ := hck.ienv.hit n ci hf
    rw [ISolution.find?_view] at hrun
    cases hf' : (SolView J).find? n with
    | none => rw [hf'] at hrun; exact nomatch (AM.pure_ok hrun).1
    | some ci' =>
    rw [hf'] at hrun
    simp only at hrun
    obtain ⟨nm', c', -, hc', -⟩ := hsol.hit n ci' hf'
    obtain ⟨b, s₁, h1, k1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, -⟩ := refinesB_run hok hr hck.pins hc hc' h1
    rcases AM.ite_ok k1 with ⟨-, k⟩ | ⟨-, k⟩
    · rcases AM.ite_ok k with ⟨-, k⟩ | ⟨-, k⟩
      · obtain ⟨ns', s₂, h2, k2⟩ := AM.bind_ok k
        obtain ⟨hns, rfl⟩ := AM.pure_ok k2
        obtain rfl := Option.some.inj hns
        exact entryNeeds_den (hs1.checkOK hck) (denoteCI_ext hc hs1.ext) (hcm.ext hs1.ext) h2
      · exact nomatch (AM.pure_ok k).1
    · exact nomatch (AM.pure_ok k).1
  | none =>
    refine ⟨?_, fun _ e => nomatch e⟩
    simp only [coneEntry] at hrun
    cases hf : fe.find? n with
    | none =>
      rw [hf] at hrun
      obtain ⟨-, rfl⟩ := AM.pure_ok hrun
      exact RStep.refl hok hr
    | some ci =>
    rw [hf] at hrun
    obtain ⟨nm, c, -, hc, -⟩ := hck.ienv.hit n ci hf
    rw [ISolution.find?_view] at hrun
    cases hf' : (SolView J).find? n with
    | none =>
      rw [hf'] at hrun
      obtain ⟨-, rfl⟩ := AM.pure_ok hrun
      exact RStep.refl hok hr
    | some ci' =>
    rw [hf'] at hrun
    simp only at hrun
    obtain ⟨nm', c', -, hc', -⟩ := hsol.hit n ci' hf'
    obtain ⟨b, s₁, h1, k1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, -⟩ := refinesB_run hok hr hck.pins hc hc' h1
    rcases AM.ite_ok k1 with ⟨-, k⟩ | ⟨-, k⟩
    · rcases AM.ite_ok k with ⟨-, k⟩ | ⟨-, k⟩
      · obtain ⟨ns', s₂, h2, k2⟩ := AM.bind_ok k
        exact nomatch (AM.pure_ok k2).1
      · obtain ⟨-, rfl⟩ := AM.pure_ok k; exact hs1
    · obtain ⟨-, rfl⟩ := AM.pure_ok k; exact hs1

/-- con-leche: ConLeche/Cached/Justify.lean:163-183 coneGo — **the walk's culprit denotes**: from
a work list of denoting handles, the walk is a renaming step and the name it stops at denotes. -/
theorem coneGo_den {env envS : Env} {fe : IFEnv} {J : ISolution}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)} :
    ∀ (fuel : Nat) (seen : Std.HashMap NIdx Bool) (work : List NIdx) (s s' : AState)
      (r : Option NIdx × Nat × Std.HashMap NIdx Bool),
      CheckOK false env fe s → IFEnvOK envS (SolView J) s → MatesDen s.store J.mates matesU →
      CvMatesDen s.store J.mates → AllDen s.store work →
      coneGo J fe fuel seen work s = .ok (r, s') →
      RStep s s' ∧ ∀ k, r.1 = some k → ∃ nm, denoteN s'.store.ns k = some nm := by
  intro fuel
  induction fuel with
  | zero =>
    intro seen work
    induction work generalizing seen with
    | nil =>
      intro s s' r hck _ _ _ _ h
      simp only [coneGo] at h
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h
      exact ⟨RStep.refl hck.state hck.readOK, fun _ e => nomatch e⟩
    | cons n work ihw =>
      intro s s' r hck hsol hm hcm hw h
      simp only [coneGo] at h
      rcases AM.ite_ok h with ⟨-, k⟩ | ⟨-, k⟩
      · exact ihw seen s s' r hck hsol hm hcm (fun x hx => hw x (List.mem_cons_of_mem _ hx)) k
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
        refine ⟨RStep.refl hck.state hck.readOK, fun x e => ?_⟩
        obtain rfl := Option.some.inj e
        exact hw _ List.mem_cons_self
  | succ d ihd =>
    intro seen work
    induction work generalizing seen with
    | nil =>
      intro s s' r hck _ _ _ _ h
      simp only [coneGo] at h
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h
      exact ⟨RStep.refl hck.state hck.readOK, fun _ e => nomatch e⟩
    | cons n work ihw =>
      intro s s' r hck hsol hm hcm hw h
      simp only [coneGo] at h
      rcases AM.ite_ok h with ⟨-, k⟩ | ⟨-, k⟩
      · exact ihw seen s s' r hck hsol hm hcm (fun x hx => hw x (List.mem_cons_of_mem _ hx)) k
      obtain ⟨o, s₁, h1, k1⟩ := AM.bind_ok k
      obtain ⟨hs1, hns⟩ := coneEntry_den hck hsol hm hcm h1
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
        refine ⟨hs1, fun x e => ?_⟩
        obtain rfl := Option.some.inj e
        obtain ⟨nm, hd⟩ := hw _ List.mem_cons_self
        exact ⟨nm, denoteN_ext hd hs1.ext⟩
      | some ns =>
        simp only at k1
        obtain ⟨hs2, hk⟩ := ihd (seen.insert n true) (ns ++ work) s₁ s' r (hs1.checkOK hck)
          (hsol.mono hs1.ext) (hm.mono hs1.ok.wf hs1.ext) (hcm.ext hs1.ext)
          (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact hns ns rfl x hx
            · obtain ⟨nm, hd⟩ := hw x (List.mem_cons_of_mem _ hx)
              exact ⟨nm, denoteN_ext hd hs1.ext⟩) k1
        exact ⟨hs1.trans hs2, hk⟩

end ConRon.Bridge.CmpV
