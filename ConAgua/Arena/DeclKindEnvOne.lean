module

public import ConAgua.Arena.DeclKindEnv
import ConRon.Bridge.Checker.Basis
public import ConRon.Bridge.Checker.DeclVal
import ConRon.Bridge.Checker.Hyp

@[expose] public section

/-!
# What a one-constant declaration's own checks add to the environment

`checkDeclKind` on a one-constant declaration returns `fe` (at most with temporary pushes taken
back: the gates' `popTemp`, `IFEnv.SameView`), with the record's own constant pushed (or, for a
quotient record and `Quot.sound`, its slot's pin at the record's names; nothing for `sorryAx`).
Every pushed constant's level parameters read back (`oneKind_envGrowDen`), so the environment
grows by `EnvGrowDen`.
-/

namespace L.Arena

open ConRon.Arena ConRon.Bridge

theorem denoteNList_mapM' {st : NStore} :
    ∀ {l : List NIdx} {xs : List ConLeche.Name}, Frontend.denoteNList st l = some xs →
      l.mapM (denoteN st) = some xs
  | [], xs, h => by simp [Frontend.denoteNList] at h; subst h; rfl
  | c :: cs, xs, h => by
    simp only [Frontend.denoteNList] at h
    cases h1 : denoteN st c with
    | none => rw [h1] at h; simp at h
    | some x =>
      cases h2 : Frontend.denoteNList st cs with
      | none => rw [h1, h2] at h; simp at h
      | some ys =>
        rw [h1, h2] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [List.mapM_cons, h1, denoteNList_mapM' h2]

/-! ## Growth by a push -/

theorem EnvGrowDen.of_sameView {st : EStore} {fe y : IFEnv} (h : ConRon.Bridge.IFEnv.SameView y fe) :
    EnvGrowDen st fe y where
  find c ci hc := .inl (by rw [← h.find]; exact hc)
  tbl c t ht := .inl (by
    simp only [IFEnv.findTable?, IFEnv.rawTable?] at ht ⊢
    rw [h.find, h.tbls, h.base] at ht; exact ht)

/-- A constant whose own level parameters read back and which is not a recursor. -/
theorem ciLvlDen_of {st : EStore} {ci : IConstantInfo} {ks : List ConLeche.Name}
    (hl : Frontend.denoteNList st.ns ci.toConstantVal.levelParams = some ks)
    (hnr : ∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) : CiLvlDen st ci :=
  ⟨⟨ks, denoteNList_mapM' hl⟩, fun cv mI rP isK rules e => absurd e (hnr cv mI rP isK rules)⟩

theorem EnvGrowDen.push {st : EStore} {fe y : IFEnv} {ci : IConstantInfo}
    (h : ConRon.Bridge.IFEnv.SameView y fe) (hg : TblGate fe) (hci : CiLvlDen st ci) :
    EnvGrowDen st fe (y.push ci) where
  find c ci' hc := by
    rw [ConRon.Bridge.IFEnv.find?_push] at hc
    split at hc
    · obtain rfl := Option.some.inj hc; exact .inr hci
    · exact .inl (by rw [← h.find]; exact hc)
  tbl c t ht := by
    left
    have hraw : (y.push ci).rawTable? c = fe.rawTable? c := by
      simp only [IFEnv.rawTable?, IFEnv.push, h.tbls, h.base]
    simp only [IFEnv.findTable?] at ht ⊢
    split at ht
    · rw [hraw] at ht
      rw [ite_eq_left (hg c t ht)]; exact ht
    · cases ht

/-! ## The gates give their environment back -/

theorem checkStructuralNatPin_env {mode : ConLeche.CheckMode} {fe y : IFEnv} {ci : IConstantInfo}
    {n : NIdx} {s s' : AState} (h : checkStructuralNatPin mode fe ci n s = .ok (y, s')) :
    y = (fe.push ci).popTemp n fe.idx[n]? := by
  unfold checkStructuralNatPin at h
  obtain ⟨_, _, -, h⟩ := AM.bind_ok h
  obtain ⟨_, _, -, h⟩ := AM.bind_ok h
  obtain ⟨_, _, -, h⟩ := AM.bind_ok h
  obtain ⟨_, _, -, h⟩ := AM.bind_ok h
  rcases AM.ite_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · exact (AM.pure_ok h).1
  · obtain ⟨_, _, h1, -⟩ := AM.bind_ok h
    exact (AM.fail_ok h1).elim

theorem checkDivModPin_env {mode : ConLeche.CheckMode} {pins : List INatOpPinSet} {fe y : IFEnv}
    {ci : IConstantInfo} {n : NIdx} {s s' : AState}
    (h : checkDivModPin mode pins fe ci n s = .ok (y, s')) :
    y = (fe.push ci).popTemp n fe.idx[n]? := by
  unfold checkDivModPin at h
  obtain ⟨_, _, -, h⟩ := AM.bind_ok h
  obtain ⟨_, _, -, h⟩ := AM.bind_ok h
  exact (AM.pure_ok h).1

theorem checkReducePin_env {mode : ConLeche.CheckMode} {fe y : IFEnv} {ci : IConstantInfo}
    {n : NIdx} {v : EIdx} {s s' : AState} (h : checkReducePin mode fe ci n v s = .ok (y, s')) :
    y = (fe.push ci).popTemp n fe.idx[n]? := by
  unfold checkReducePin at h
  obtain ⟨_, _, -, h⟩ := AM.bind_ok h
  rcases AM.ite_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, _, -, h⟩ := AM.bind_ok h
    exact (AM.pure_ok h).1
  · exact (AM.fail_ok h).elim

theorem sameView_gate {fe : IFEnv} {ci : IConstantInfo} :
    ConRon.Bridge.IFEnv.SameView ((fe.push ci).popTemp ci.name fe.idx[ci.name]?) fe :=
  ConRon.Bridge.IFEnv.sameView_popTemp fe ci

theorem sameView_trans {a b c : IFEnv} (h1 : ConRon.Bridge.IFEnv.SameView a b)
    (h2 : ConRon.Bridge.IFEnv.SameView b c) : ConRon.Bridge.IFEnv.SameView a c :=
  ⟨fun n => (h1.idx n).trans (h2.idx n), fun n => (h1.find n).trans (h2.find n),
    h1.tbls.trans h2.tbls, h1.base.trans h2.base, h1.env.trans h2.env⟩

theorem sameView_refl (a : IFEnv) : ConRon.Bridge.IFEnv.SameView a a :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl⟩

/-- `SameView` is a congruence for `push`/`popTemp` of the same constant. -/
theorem sameView_gate_of {fe fe₁ : IFEnv} {ci : IConstantInfo} (h : ConRon.Bridge.IFEnv.SameView fe₁ fe) :
    ConRon.Bridge.IFEnv.SameView ((fe₁.push ci).popTemp ci.name fe₁.idx[ci.name]?) fe :=
  sameView_trans (ConRon.Bridge.IFEnv.sameView_popTemp fe₁ ci) h

/-! ## The value checks return the record's constant -/

theorem checkDefnVal_ret {mode : ConLeche.CheckMode} {fe : IFEnv} {cv : IConstantVal} {v : EIdx}
    {h : ConLeche.ReducibilityHint} {ci : IConstantInfo} {s s' : AState}
    (hr : checkDefnVal mode fe cv v h s = .ok (ci, s')) : ci = .defnInfo cv v h := by
  unfold checkDefnVal at hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  rcases AM.ite_ok hr with ⟨-, hr⟩ | ⟨-, hr⟩
  · exact (AM.pure_ok hr).1
  · obtain ⟨_, _, h1, -⟩ := AM.bind_ok hr; exact (AM.fail_ok h1).elim

theorem checkThmVal_ret {mode : ConLeche.CheckMode} {fe : IFEnv} {cv : IConstantVal} {v : EIdx}
    {ci : IConstantInfo} {s s' : AState}
    (hr : checkThmVal mode fe cv v s = .ok (ci, s')) : ci = .thmInfo cv := by
  unfold checkThmVal at hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  rcases AM.ite_ok hr with ⟨-, hr⟩ | ⟨-, hr⟩
  rotate_left
  · obtain ⟨_, _, h1, -⟩ := AM.bind_ok hr; exact (AM.fail_ok h1).elim
  dsimp only at hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  rcases AM.ite_ok hr with ⟨-, hr⟩ | ⟨-, hr⟩
  · exact (AM.pure_ok hr).1
  · obtain ⟨_, _, h1, -⟩ := AM.bind_ok hr; exact (AM.fail_ok h1).elim

theorem checkOpaqueVal_ret {mode : ConLeche.CheckMode} {fe : IFEnv} {cv : IConstantVal} {v : EIdx}
    {ci : IConstantInfo} {s s' : AState}
    (hr : checkOpaqueVal mode fe cv v s = .ok (ci, s')) : ci = .axiomInfo cv := by
  unfold checkOpaqueVal at hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  obtain ⟨_, _, -, hr⟩ := AM.bind_ok hr
  rcases AM.ite_ok hr with ⟨-, hr⟩ | ⟨-, hr⟩
  · exact (AM.pure_ok hr).1
  · obtain ⟨_, _, h1, -⟩ := AM.bind_ok hr; exact (AM.fail_ok h1).elim

/-! ## The quotient records -/

theorem denoteLList_mem {st : LStore} :
    ∀ {us : List LIdx} {ls : List ConLeche.Level}, denoteLList st us = some ls →
      ∀ u ∈ us, ∃ L, denoteL st u = some L
  | [], _, _, u, hu => absurd hu (List.not_mem_nil)
  | v :: vs, ls, h, u, hu => by
    simp only [denoteLList] at h
    cases h1 : denoteL st v with
    | none => rw [h1] at h; simp [opt2] at h
    | some x =>
      cases h2 : denoteLList st vs with
      | none => rw [h1, h2] at h; simp [opt2] at h
      | some xs =>
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨x, h1⟩
        · exact denoteLList_mem h2 u hu

theorem denoteRules_mem {st : EStore} :
    ∀ {rs : List IRecRule} {xs : List ConLeche.RecRule}, Frontend.denoteRules st rs = some xs →
      ∀ r ∈ rs, ∃ f, Frontend.denoteFire st r.fire = some f
  | [], _, _, r, hr => absurd hr (List.not_mem_nil)
  | q :: qs, xs, h, r, hr => by
    simp only [Frontend.denoteRules] at h
    cases h1 : Frontend.denoteRule st q with
    | none => rw [h1] at h; simp at h
    | some x =>
      cases h2 : Frontend.denoteRules st qs with
      | none => rw [h1, h2] at h; simp at h
      | some ys =>
        rcases List.mem_cons.1 hr with rfl | hr
        · simp only [Frontend.denoteRule] at h1
          split at h1
          · rename_i c f e hc hf he; exact ⟨f, hf⟩
          · cases h1
        · exact denoteRules_mem h2 r hr

/-- **A constant that denotes has `CiLvlDen`**: its level parameters, and a recursor's rules'
fired levels (`denoteFire` reads them back). -/
theorem ciLvlDen_of_denote {st : EStore} {ci : IConstantInfo} {x : ConLeche.ConstantInfo}
    (h : Frontend.denoteCI st ci = some x) : CiLvlDen st ci := by
  refine ⟨⟨_, denoteNList_mapM' (denoteCV_inv (denoteCI_toConstantVal h)).2.1⟩, ?_⟩
  intro cv mI rP isK rules e r hr
  subst e
  simp only [Frontend.denoteCI] at h
  split at h
  · rename_i c rs hc hrs
    obtain ⟨f, hf⟩ := denoteRules_mem hrs r hr
    refine ⟨fun lvls pins e u hu => ?_, fun lvls e u hu => ?_⟩
    · rw [e] at hf; simp only [Frontend.denoteFire] at hf
      split at hf
      · rename_i ls ps hls hps; exact denoteLList_mem hls u hu
      · cases hf
    · rw [e] at hf; simp only [Frontend.denoteFire, Option.map_eq_some_iff] at hf
      obtain ⟨ls, hls, -⟩ := hf; exact denoteLList_mem hls u hu
  · cases h

theorem checkQuotRecord_env {env : ConLeche.Env} {fe fe' : IFEnv} {k : ConLeche.QuotKind}
    {cv : IConstantVal} {c : ConLeche.ConstantVal} {s s' : AState}
    (hok : CheckOK false env fe s) (hg : TblGate fe) (hcv : Frontend.denoteCV s.store cv = some c)
    (h : checkQuotRecord fe k cv s = .ok (fe', s')) : EnvGrowDen s'.store fe fe' := by
  unfold checkQuotRecord at h
  obtain ⟨b1, s1, h1, k1⟩ := AM.bind_ok h
  obtain ⟨hr1, -⟩ := quotPinHit_run hok.state hok.readOK hcv h1
  try dsimp only at k1
  rcases AM.ite_ok k1 with ⟨-, k2⟩ | ⟨-, k2⟩
  rotate_left
  · obtain ⟨_, _, h0, -⟩ := AM.bind_ok k2; exact (AM.fail_ok h0).elim
  try dsimp only at k2
  obtain ⟨b2, s2, h2, k3⟩ := AM.bind_ok k2
  have hok1 : CheckOK false env fe s1 := hr1.checkOK hok
  obtain ⟨e2, -⟩ := quotPredsOk_run hok1.state hok1.pins hok1.ienv h2
  subst e2
  try dsimp only at k3
  rcases AM.ite_ok k3 with ⟨-, k4⟩ | ⟨-, k4⟩
  rotate_left
  · obtain ⟨_, _, h0, -⟩ := AM.bind_ok k4; exact (AM.fail_ok h0).elim
  try dsimp only at k4
  obtain ⟨ci, s3, h3, k5⟩ := AM.bind_ok k4
  obtain ⟨hr3, hd3⟩ := quotAt_run hok1.state hok1.readOK (denoteCV_ext hcv hr1.ext) h3
  unfold installBasisDecl at k5
  rcases AM.ite_ok k5 with ⟨-, k6⟩ | ⟨-, k6⟩
  rotate_left
  · obtain ⟨_, _, h0, -⟩ := AM.bind_ok k6; exact (AM.fail_ok h0).elim
  try dsimp only at k6
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k6
  exact EnvGrowDen.push (sameView_refl fe) hg (ciLvlDen_of_denote hd3)

/-! ## The one-constant arms -/

section arms
variable {env : ConLeche.Env} {mode : ConLeche.CheckMode} {pins : List INatOpPinSet}
  {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {c : ConLeche.ConstantVal}

/-- The record's own constant, at its constant value `cv` (not a recursor). -/
theorem ciLvlDen_cv {st : EStore} {ci : IConstantInfo} (hci : ci.toConstantVal = cv)
    (hnr : ∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules)
    (hcv : Frontend.denoteCV st cv = some c) : CiLvlDen st ci :=
  ciLvlDen_of (by rw [hci]; exact (denoteCV_inv hcv).2.1) hnr

theorem defnKind_env {v : EIdx} {h : ConLeche.ReducibilityHint}
    (hok : FoldOK env fe s) (hcv : Frontend.denoteCV s'.store cv = some c)
    (hrun : checkDeclKind mode pins fe (.defnDecl cv v h) s = .ok (fe', s')) :
    EnvGrowDen s'.store fe fe' := by
  unfold checkDeclKind at hrun
  dsimp only at hrun
  obtain ⟨_, s1, -, k1⟩ := AM.bind_ok hrun
  obtain ⟨ci, s2, h2, k2⟩ := AM.bind_ok k1
  obtain rfl := checkDefnVal_ret h2
  obtain ⟨_, s3, -, k3⟩ := AM.bind_ok k2
  try dsimp only at k3
  rcases AM.ite_ok k3 with ⟨-, k3⟩ | ⟨-, k3⟩ <;> obtain ⟨fe1, s4, h4, k4⟩ := AM.bind_ok k3
  all_goals have hsv1 : ConRon.Bridge.IFEnv.SameView fe1 fe := by first | (rw [checkStructuralNatPin_env h4]; exact sameView_gate (ci := .defnInfo cv v h)) | (rw [(AM.pure_ok h4).1]; exact sameView_refl fe)
  all_goals
    clear h4
    try dsimp only at k4
    obtain ⟨_, s5, -, k5⟩ := AM.bind_ok k4
    try dsimp only at k5
    rcases AM.ite_ok k5 with ⟨-, k5⟩ | ⟨-, k5⟩ <;> obtain ⟨fe2, s6, h6, k6⟩ := AM.bind_ok k5
    all_goals have hsv2 : ConRon.Bridge.IFEnv.SameView fe2 fe := by first | (rw [checkDivModPin_env h6]; exact sameView_gate_of (ci := .defnInfo cv v h) hsv1) | (rw [(AM.pure_ok h6).1]; exact hsv1)
    all_goals
      try dsimp only at k6
      obtain ⟨rfl, -⟩ := AM.pure_ok k6
      exact EnvGrowDen.push hsv2 hok.gate (ciLvlDen_cv rfl (by intros; simp) hcv)

theorem thmKind_env {v : EIdx}
    (hok : FoldOK env fe s) (hcv : Frontend.denoteCV s'.store cv = some c)
    (hrun : checkDeclKind mode pins fe (.thmDecl cv v) s = .ok (fe', s')) :
    EnvGrowDen s'.store fe fe' := by
  unfold checkDeclKind at hrun
  dsimp only at hrun
  obtain ⟨_, s1, -, k1⟩ := AM.bind_ok hrun
  obtain ⟨ci, s2, h2, k2⟩ := AM.bind_ok k1
  obtain rfl := checkThmVal_ret h2
  obtain ⟨rfl, -⟩ := AM.pure_ok k2
  exact EnvGrowDen.push (sameView_refl fe) hok.gate (ciLvlDen_cv rfl (by intros; simp) hcv)

theorem opaqueKind_env {v : EIdx}
    (hok : FoldOK env fe s) (hcv : Frontend.denoteCV s'.store cv = some c)
    (hrun : checkDeclKind mode pins fe (.opaqueDecl cv v) s = .ok (fe', s')) :
    EnvGrowDen s'.store fe fe' := by
  unfold checkDeclKind at hrun
  dsimp only at hrun
  obtain ⟨_, s1, -, k1⟩ := AM.bind_ok hrun
  obtain ⟨ci, s2, h2, k2⟩ := AM.bind_ok k1
  obtain rfl := checkOpaqueVal_ret h2
  obtain ⟨_, s3, -, k3⟩ := AM.bind_ok k2
  try dsimp only at k3
  rcases AM.ite_ok k3 with ⟨-, k3⟩ | ⟨-, k3⟩ <;> obtain ⟨fe1, s4, h4, k4⟩ := AM.bind_ok k3
  all_goals have hsv1 : ConRon.Bridge.IFEnv.SameView fe1 fe := by first | (rw [checkReducePin_env h4]; exact sameView_gate (ci := .axiomInfo cv)) | (rw [(AM.pure_ok h4).1]; exact sameView_refl fe)
  all_goals
    try dsimp only at k4
    obtain ⟨rfl, -⟩ := AM.pure_ok k4
    exact EnvGrowDen.push hsv1 hok.gate (ciLvlDen_cv rfl (by intros; simp) hcv)

theorem quotKind_env {k : ConLeche.QuotKind}
    (hok : FoldOK env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : checkDeclKind mode pins fe (.quotDecl k cv) s = .ok (fe', s')) :
    EnvGrowDen s'.store fe fe' := by
  unfold checkDeclKind at hrun
  dsimp only at hrun
  exact checkQuotRecord_env hok.check hok.gate hcv hrun

theorem pinAt_state {i : Nat} {n : NIdx} {s s' : AState} (h : pinAt i s = .ok (n, s')) : s' = s := by
  unfold pinAt at h
  obtain ⟨t, s1, h1, k1⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  split at k1
  · exact (AM.pure_ok k1).2
  · exact (AM.fail_ok k1).elim

theorem axiomKind_env
    (hok : FoldOK env fe s) (hcv0 : Frontend.denoteCV s.store cv = some c)
    (hcv : Frontend.denoteCV s'.store cv = some c)
    (hrun : checkDeclKind mode pins fe (.axiomDecl cv) s = .ok (fe', s')) :
    EnvGrowDen s'.store fe fe' := by
  have hpush : ∀ {s₁ : AState}, (pure (fe.push (.axiomInfo cv)) : AM IFEnv) s₁ = .ok (fe', s') →
      EnvGrowDen s'.store fe fe' := fun k => by
    obtain ⟨rfl, -⟩ := AM.pure_ok k
    exact EnvGrowDen.push (sameView_refl fe) hok.gate (ciLvlDen_cv rfl (by intros; simp) hcv)
  unfold checkDeclKind at hrun
  dsimp only at hrun
  obtain ⟨qs, s1, h1, k1⟩ := AM.bind_ok hrun
  obtain rfl := pinAt_state h1
  rcases AM.ite_ok k1 with ⟨-, k2⟩ | ⟨-, k2⟩
  · exact checkQuotRecord_env hok.check hok.gate hcv0 k2
  obtain ⟨_, _, -, k3⟩ := AM.bind_ok k2
  obtain ⟨b1, _, -, k4⟩ := AM.bind_ok k3
  rcases AM.ite_ok k4 with ⟨-, k5⟩ | ⟨-, k5⟩
  · exact hpush k5
  obtain ⟨_, _, -, k6⟩ := AM.bind_ok k5
  rcases AM.ite_ok k6 with ⟨-, k7⟩ | ⟨-, k7⟩
  · obtain ⟨_, _, -, k8⟩ := AM.bind_ok k7
    rcases AM.ite_ok k8 with ⟨-, k9⟩ | ⟨-, k9⟩
    · exact hpush k9
    · exact (AM.fail_ok k9).elim
  obtain ⟨_, _, -, k8⟩ := AM.bind_ok k7
  obtain ⟨_, _, -, k9⟩ := AM.bind_ok k8
  rcases AM.ite_ok k9 with ⟨-, k10⟩ | ⟨-, k10⟩
  · obtain ⟨_, _, -, k11⟩ := AM.bind_ok k10
    rcases AM.ite_ok k11 with ⟨-, k12⟩ | ⟨-, k12⟩
    · exact hpush k12
    · exact (AM.fail_ok k12).elim
  obtain ⟨_, _, -, k11⟩ := AM.bind_ok k10
  obtain ⟨_, _, -, k12⟩ := AM.bind_ok k11
  rcases AM.ite_ok k12 with ⟨-, k13⟩ | ⟨-, k13⟩
  · exact (AM.fail_ok k13).elim
  obtain ⟨_, _, -, k14⟩ := AM.bind_ok k13
  rcases AM.ite_ok k14 with ⟨-, k15⟩ | ⟨-, k15⟩
  · obtain ⟨rfl, -⟩ := AM.pure_ok k15; exact EnvGrowDen.of_sameView (sameView_refl _)
  · obtain ⟨_, _, -, k16⟩ := AM.bind_ok k15; exact (AM.fail_ok k16).elim

/-- **A one-constant declaration's own checks grow the environment by `EnvGrowDen`**: the
record's constant value `cv` denotes at the start and (by the store's extension) at the end. -/
theorem oneKind_envGrowDen {d : IDeclaration} (hok : FoldOK env fe s)
    (hcv0 : Frontend.denoteCV s.store cv = some c) (hx : Ext s.store s'.store)
    (hd : d = .axiomDecl cv ∨ (∃ v h, d = .defnDecl cv v h) ∨ (∃ v, d = .thmDecl cv v) ∨
      (∃ v, d = .opaqueDecl cv v) ∨ ∃ k, d = .quotDecl k cv)
    (hrun : checkDeclKind mode pins fe d s = .ok (fe', s')) : EnvGrowDen s'.store fe fe' := by
  have hcv := denoteCV_ext hcv0 hx
  rcases hd with rfl | ⟨v, h, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨k, rfl⟩
  · exact axiomKind_env hok hcv0 hcv hrun
  · exact defnKind_env hok hcv hrun
  · exact thmKind_env hok hcv hrun
  · exact opaqueKind_env hok hcv hrun
  · exact quotKind_env hok hcv0 hrun

end arms

end L.Arena
