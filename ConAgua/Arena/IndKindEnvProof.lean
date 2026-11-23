module

public import ConAgua.Arena.DeclKindEnv
import ConAgua.Arena.DeclKindEnvOne
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Inductives.BlockTail
public import ConRon.Bridge.Inductives.GenRec
import ConRon.Bridge.Inductives.BlockInstall
import ConRon.Bridge.Inductives.RecCheck
import ConRon.Bridge.Inductives.StreamRecs
import ConRon.Bridge.Inductives.Install
import ConRon.Bridge.Inductives.IotaRead
import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Denote.IndFrame
import ConRon.Bridge.Inductives.ClassRead
import ConRon.Bridge.Inductives.BlockShape
import ConRon.Bridge.Inductives.Positivity
import ConRon.Bridge.Inductives.PosWalks
import ConRon.Bridge.Inductives.StructInstall
import ConRon.Bridge.Inductives.StructParts
import ConLeche.Verify.Cached.GenRecC
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Core.Walks.Guards
import ConRon.Bridge.EnvDenote
import ConRon.Bridge.Inductives.Rel
import ConLeche.Verify.Inductives.BlockShapeInv

@[expose] public section

/-!
# `IndKindEnv`: what an inductive block's check adds to the environment

`checkDeclKind`'s `.indDecl` arm (`readBlock`, then `checkBlock`) returns the environment
`fe` with the block's formers (`consBlockInds`), its constructors (`consBlockCtors`), its
recursor records and its projection tables (`pushDelta`) pushed; the generated recursors'
temporary pushes are popped (`classFeR_pop`, `consBlockRecsTemp_pop`). Every pushed constant's
level lists and every table's level parameters read back in the final store: the shape the
reader returns denotes (`readBlock_spec`), and the recursors and tables denote by their
runs (`blockRecs_run`, `blockTables_run`). The run facts come from con-ron's own walk
(`checkBlock_bridge`'s steps, repeated here with the environment kept).
-/

namespace L.Arena

open ConRon.Arena ConRon.Bridge ConRon.Bridge.Inductives

/-! ## Growth: the algebra -/

theorem EnvGrowDen.refl' (st : EStore) (fe : IFEnv) : EnvGrowDen st fe fe :=
  ⟨fun _ _ h => .inl h, fun _ _ h => .inl h⟩

theorem EnvGrowDen.trans {st : EStore} {a b c : IFEnv} (h1 : EnvGrowDen st a b)
    (h2 : EnvGrowDen st b c) : EnvGrowDen st a c :=
  ⟨fun n ci h => (h2.find n ci h).elim (fun h => h1.find n ci h) .inr,
   fun n t h => (h2.tbl n t h).elim (fun h => h1.tbl n t h) .inr⟩

/-- The ι reading rule's driver gives back an index that answers as its input (the pushes
undone, the flags set back). -/
theorem blockReadsAt_feq {fe : IFEnv} {p : ConRon.Arena.BlockShape} {s s' : AState} {r : Bool × IFEnv}
    (h : ConRon.Arena.blockReadsAt fe p s = .ok (r, s')) : GR.FEq r.2 fe := by
  simp only [ConRon.Arena.blockReadsAt] at h
  obtain ⟨cs, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨recs, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨ok, s₃, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
  obtain ⟨news, hn, hpop⟩ := BT.consBlockRecsTemp_pop cs fe []
  rw [List.nil_append] at hn
  simp only [hn]
  exact hpop

/-- `EnvGrowDen` from an index that answers as another. -/
theorem EnvGrowDen.ofFEqL {st : EStore} {fe' a b : IFEnv} (he : GR.FEq b a)
    (h : EnvGrowDen st b fe') : EnvGrowDen st a fe' :=
  ⟨fun n ci hc => (h.find n ci hc).imp_left (fun h' => by rw [← he.find? n]; exact h'),
   fun n t ht => (h.tbl n t ht).imp_left (fun h' => by
     simp only [IFEnv.findTable?] at h' ⊢
     rw [← he.find? n, ← he.rawTable? n]; exact h')⟩

theorem EnvGrowDen.ofFEq {st : EStore} {fe a b : IFEnv} (he : GR.FEq a b)
    (h : EnvGrowDen st fe b) : EnvGrowDen st fe a :=
  ⟨fun n ci hc => h.find n ci (by rw [← he.find? n]; exact hc),
   fun n t ht => h.tbl n t (by
     simp only [IFEnv.findTable?] at ht ⊢
     rw [← he.find? n, ← he.rawTable? n]; exact ht)⟩

theorem EnvGrowDen.push' {st : EStore} {fe0 fe : IFEnv} {ci : IConstantInfo}
    (h : EnvGrowDen st fe0 fe) (hg : TblGate fe) (hci : CiLvlDen st ci) :
    EnvGrowDen st fe0 (fe.push ci) :=
  h.trans (EnvGrowDen.push (sameView_refl fe) hg hci)

theorem IFEnv.find?_pushTable' (fe : IFEnv) (t : IProjTable) (n : NIdx) :
    (fe.pushTable t).find? n = fe.find? n := rfl

theorem EnvGrowDen.pushTable {st : EStore} {fe0 fe : IFEnv} {t : IProjTable}
    (h : EnvGrowDen st fe0 fe) (ht : ∃ ks, t.levelParams.mapM (denoteN st.ns) = some ks) :
    EnvGrowDen st fe0 (fe.pushTable t) := by
  refine h.trans ⟨fun n ci hc => .inl (by rw [IFEnv.find?_pushTable'] at hc; exact hc),
    fun n t' hc => ?_⟩
  have hc' : (if (fe.find? n).isSome = true then (fe.pushTable t).rawTable? n else none) = some t' :=
    hc
  clear hc
  show (if (fe.find? n).isSome = true then fe.rawTable? n else none) = some t' ∨ _
  by_cases hf : (fe.find? n).isSome = true
  · rw [ite_eq_left hf] at hc' ⊢
    have hc := hc'
    simp only [IFEnv.rawTable?, IFEnv.pushTable, Std.HashMap.getElem?_insert] at hc
    by_cases hn : (t.structName == n) = true
    · rw [ite_eq_left hn] at hc; obtain rfl := Option.some.inj hc; exact .inr ht
    · rw [ite_eq_right hn] at hc; left; simp only [IFEnv.rawTable?]; exact hc
  · rw [ite_eq_right hf] at hc'; cases hc'

/-- The formers, consed (the capability records' never-zero reads change no environment). -/
theorem EnvGrowDen.consBlockInds {st : EStore} {p₁ : BlockShape} {isRec : Bool} :
    ∀ (cvs : List IConstantVal) (i : Nat) {fe0 fe fe' : IFEnv} {s s' : AState},
      consBlockInds p₁ isRec cvs i fe s = .ok (fe', s') → EnvGrowDen st fe0 fe → TblGate fe →
      (∀ cv ∈ cvs, ∃ ks, Frontend.denoteNList st.ns cv.levelParams = some ks) →
      EnvGrowDen st fe0 fe' ∧ TblGate fe'
  | [], _, _, fe, fe', s, s', hr, h, hg, _ => by
    unfold ConRon.Arena.consBlockInds at hr
    obtain ⟨rfl, -⟩ := AM.pure_ok hr; exact ⟨h, hg⟩
  | cv :: cvs, i, _, fe, fe', s, s', hr, h, hg, hd => by
    unfold ConRon.Arena.consBlockInds at hr
    obtain ⟨caps, s1, -, hr⟩ := AM.bind_ok hr
    obtain ⟨ks, hks⟩ := hd cv (by simp)
    exact EnvGrowDen.consBlockInds cvs (i + 1) hr
      (h.push' hg (ciLvlDen_of (ci := .indInfo cv caps) hks
        (fun _ _ _ _ _ e => nomatch e)))
      (hg.push _) (fun cv' h' => hd cv' (by simp [h']))

/-- One member's constructors, consed. -/
theorem EnvGrowDen.consSumCtors {st : EStore} {nP : Nat} {T : NIdx} :
    ∀ (cs : List (IConstantVal × Nat)) {fe0 fe : IFEnv}, EnvGrowDen st fe0 fe → TblGate fe →
      (∀ c ∈ cs, ∃ ks, Frontend.denoteNList st.ns c.1.levelParams = some ks) →
      EnvGrowDen st fe0 (consSumCtors nP T cs fe) ∧ TblGate (consSumCtors nP T cs fe)
  | [], _, _, h, hg, _ => ⟨h, hg⟩
  | c :: cs, _, fe, h, hg, hd => by
    obtain ⟨ks, hks⟩ := hd c (by simp)
    exact EnvGrowDen.consSumCtors cs
      (h.push' hg (ciLvlDen_of (ci := .ctorInfo c.1 nP c.2 T) hks (fun _ _ _ _ _ e => nomatch e)))
      (hg.push _) (fun c' h' => hd c' (by simp [h']))

/-- Every member's constructors, consed. -/
theorem EnvGrowDen.consBlockCtors {st : EStore} {nP : Nat} :
    ∀ (css : List (NIdx × List (IConstantVal × Nat))) {fe0 fe : IFEnv}, EnvGrowDen st fe0 fe →
      TblGate fe →
      (∀ g ∈ css, ∀ c ∈ g.2, ∃ ks, Frontend.denoteNList st.ns c.1.levelParams = some ks) →
      EnvGrowDen st fe0 (consBlockCtors nP css fe) ∧ TblGate (consBlockCtors nP css fe)
  | [], _, _, h, hg, _ => ⟨h, hg⟩
  | (T, cs) :: css, _, fe, h, hg, hd => by
    obtain ⟨h1, g1⟩ := EnvGrowDen.consSumCtors (nP := nP) (T := T) cs h hg (hd (T, cs) (by simp))
    exact EnvGrowDen.consBlockCtors css h1 g1 (fun g' h' => hd g' (by simp [h']))

theorem EnvGrowDen.pushAll {st : EStore} :
    ∀ (L : List IConstantInfo) {fe0 fe : IFEnv}, EnvGrowDen st fe0 fe → TblGate fe →
      (∀ ci ∈ L, CiLvlDen st ci) →
      EnvGrowDen st fe0 (IFEnv.pushAll L fe) ∧ TblGate (IFEnv.pushAll L fe)
  | [], _, _, h, hg, _ => ⟨h, hg⟩
  | ci :: L, _, fe, h, hg, hd =>
    EnvGrowDen.pushAll L (h.push' hg (hd ci (by simp))) (hg.push _)
      (fun c' h' => hd c' (by simp [h']))

theorem EnvGrowDen.pushTables {st : EStore} :
    ∀ (Q : List IProjTable) {fe0 fe : IFEnv}, EnvGrowDen st fe0 fe →
      (∀ t ∈ Q, ∃ ks, t.levelParams.mapM (denoteN st.ns) = some ks) →
      EnvGrowDen st fe0 (IFEnv.pushTables Q fe)
  | [], _, _, h, _ => h
  | t :: Q, _, fe, h, hd =>
    EnvGrowDen.pushTables Q (h.pushTable (hd t (by simp))) (fun t' h' => hd t' (by simp [h']))

/-! ## The environments the stages return -/

section envs
variable {mode : ConLeche.CheckMode}

theorem withSort_members {p p₁ : BlockShape} {x : LIdx} {s s' : AState}
    (h : p.withSort x s = .ok (p₁, s')) : p₁.members = p.members := by
  simp only [BlockShape.withSort] at h
  repeat (first
    | (obtain ⟨_, _, _, h⟩ := AM.bind_ok h)
    | (split at h))
  all_goals (obtain ⟨rfl, rfl⟩ := AM.pure_ok h; rfl)

theorem checkBlockInds_env {fe fe₁ : IFEnv} {p p₁ : BlockShape} {isRec : Bool} {s s' : AState}
    (h : checkBlockInds mode fe p isRec s = .ok ((fe₁, p₁), s')) :
    (∃ sa sb, consBlockInds p₁ isRec (p.members.map (·.declared)) 0 fe sa = .ok (fe₁, sb)) ∧
      p₁.members = p.members := by
  unfold checkBlockInds at h
  cases hm : p.members with
  | nil => rw [hm] at h; exact absurd h (fun h' => AM.fail_ok h')
  | cons ms₀ rest =>
  rw [hm] at h
  obtain ⟨_, _, _, h⟩ := AM.bind_ok h
  obtain ⟨_, _, _, h⟩ := AM.bind_ok h
  obtain ⟨_, _, _, h⟩ := AM.bind_ok h
  obtain ⟨p₂, _, hw, h⟩ := AM.bind_ok h
  obtain ⟨fe₂, _, hc, h⟩ := AM.bind_ok h
  obtain ⟨he, -⟩ := AM.pure_ok h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨⟨_, _, by first | exact hc | simpa [hm] using hc⟩, (withSort_members hw).trans hm⟩

theorem checkBlockPass_env {fe : IFEnv} {p : BlockShape} {isRec : Bool} {q : BlockPass} {s s' : AState}
    (h : checkBlockPass mode fe p isRec s = .ok (q, s')) :
    (∃ sa sb, consBlockInds q.p isRec (p.members.map (·.declared)) 0 fe sa = .ok (q.env1, sb)) ∧
      q.p.members = p.members := by
  unfold checkBlockPass at h
  obtain ⟨⟨fe₁, p₁⟩, _, h1, h⟩ := AM.bind_ok h
  have e := checkBlockInds_env h1
  repeat (obtain ⟨_, _, _, h⟩ := AM.bind_ok h)
  obtain ⟨rfl, -⟩ := AM.pure_ok h
  exact e

theorem genRecCheck_env {fe : IFEnv} {p : BlockShape} {nb : Bool}
    {params : List EIdx} {tbl : List NestCtorNf} {rd : ClassRead} {ms : List TargetMajor}
    {block : List IConstantInfo} {s s' : AState} {r : IFEnv × List (IConstantVal × TargetMajor × List EIdx)}
    (h : genRecCheck mode fe p nb params tbl rd ms block s = .ok (r, s')) : GR.FEq r.1 fe := by
  simp only [genRecCheck] at h
  iterate 40 (all_goals (try (first
    | (exact absurd h (fun h' => AM.fail_ok h'))
    | (obtain ⟨_, _, _, h⟩ := AM.bind_ok h)
    | (split at h))))
  all_goals (obtain ⟨rfl, -⟩ := AM.pure_ok h; exact GR.classFeR_pop _ _ _ fe)

theorem checkBlockTail_env {block : List IConstantInfo} {q : BlockPass} {Q : List IProjTable}
    {fe₃ : IFEnv} {s s' : AState}
    (h : checkBlockTail mode block q Q s = .ok (fe₃, s')) :
    GR.FEq fe₃ (consBlockCtors q.p.nP q.p.ctorGroups q.env1) := by
  unfold checkBlockTail at h
  obtain ⟨_, _, _, h⟩ := AM.bind_ok h
  obtain ⟨_, _, _, h⟩ := AM.bind_ok h
  obtain ⟨⟨fe₂b, out⟩, _, hr, h⟩ := AM.bind_ok h
  have e1 : GR.FEq fe₂b (consBlockCtors q.p.nP q.p.ctorGroups q.env1) :=
    genRecCheck_env (r := (fe₂b, out)) hr
  iterate 8 (try (obtain ⟨_, _, _, h⟩ := AM.bind_ok h))
  obtain ⟨rfl, -⟩ := AM.pure_ok h
  obtain ⟨news, hn, hf⟩ := BT.consBlockRecsTemp_pop _ fe₂b []
  simp only [List.nil_append] at hn
  rw [hn]
  exact hf.trans e1

end envs

/-! ## The members, the records and the tables read back -/

theorem reduceMember_keeps {mode : ConLeche.CheckMode} {fe : IFEnv} {ms ms' : MemberShape} {nP : Nat}
    {s s' : AState} (h : reduceMember mode fe ms nP s = .ok (ms', s')) :
    ms'.declared = ms.declared ∧ ms'.ctors = ms.ctors := by
  unfold reduceMember at h
  iterate 12 (all_goals (try (first
    | (exact absurd h (fun h' => AM.fail_ok h'))
    | (obtain ⟨_, _, _, h⟩ := AM.bind_ok h)
    | (split at h))))
  all_goals (obtain ⟨rfl, -⟩ := AM.pure_ok h; exact ⟨rfl, rfl⟩)

theorem reduceMembers_keeps {mode : ConLeche.CheckMode} {fe : IFEnv} {nP : Nat} :
    ∀ (ms : List MemberShape) {ms' : List MemberShape} {s s' : AState},
      reduceMembers mode fe nP ms s = .ok (ms', s') →
      ms'.map (·.declared) = ms.map (·.declared) ∧ ms'.map (·.ctors) = ms.map (·.ctors)
  | [], ms', s, s', h => by
    simp only [reduceMembers] at h
    obtain ⟨rfl, -⟩ := AM.pure_ok h; exact ⟨rfl, rfl⟩
  | m :: ms, ms', s, s', h => by
    simp only [reduceMembers] at h
    obtain ⟨_, _, _, h⟩ := AM.bind_ok h
    obtain ⟨m', _, h1, h⟩ := AM.bind_ok h
    obtain ⟨rest', _, h2, h⟩ := AM.bind_ok h
    obtain ⟨rfl, -⟩ := AM.pure_ok h
    obtain ⟨e1, e2⟩ := reduceMember_keeps h1
    obtain ⟨e3, e4⟩ := reduceMembers_keeps ms h2
    simp [e1, e2, e3, e4]

theorem denoteCIList_mem {st : EStore} :
    ∀ {L : List IConstantInfo} {xs : List ConLeche.ConstantInfo}, Frontend.denoteCIList st L = some xs →
      ∀ ci ∈ L, ∃ x, Frontend.denoteCI st ci = some x
  | [], _, _, ci, h => nomatch h
  | c :: cs, xs, h, ci, hm => by
    simp only [Frontend.denoteCIList] at h
    split at h
    · rename_i x xs' hx hxs
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨x, hx⟩
      · exact denoteCIList_mem hxs ci hm
    · cases h

theorem denoteProjTableList_mem {st : EStore} :
    ∀ {Q : List IProjTable} {xs : List ConLeche.ProjTable}, Frontend.denoteProjTableList st Q = some xs →
      ∀ t ∈ Q, ∃ ks, t.levelParams.mapM (denoteN st.ns) = some ks
  | [], _, _, t, h => nomatch h
  | c :: cs, xs, h, t, hm => by
    simp only [Frontend.denoteProjTableList] at h
    split at h
    · rename_i x xs' hx hxs
      rcases List.mem_cons.mp hm with rfl | hm
      · simp only [Frontend.denoteProjTable] at hx
        split at hx
        · rename_i sn lps c' _ hl _
          exact ⟨lps, denoteNList_mapM' hl⟩
        · cases hx
      · exact denoteProjTableList_mem hxs t hm
    · cases h

theorem mapM_option_mem' {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys → ∀ {x}, x ∈ l → ∃ y, f x = some y
  | [], _, _, _, hx => nomatch hx
  | a :: l, ys, h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, -⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, hy⟩
    · exact mapM_option_mem' hys hx

/-- The members of a denoting shape: their declared constant values and their constructors
read back. -/
theorem dShape_members_den {st : EStore} {p : BlockShape} {pP : ConLeche.BlockShape}
    (hp : dShape st p = some pP) :
    (∀ cv ∈ p.members.map (·.declared), ∃ ks, Frontend.denoteNList st.ns cv.levelParams = some ks) ∧
    (∀ cs ∈ p.members.map (·.ctors), ∀ c ∈ cs, ∃ ks, Frontend.denoteNList st.ns c.1.levelParams = some ks) := by
  obtain ⟨hms, -⟩ := dShape_inv hp
  have hm : ∀ m ∈ p.members, ∃ mP, dMember st m = some mP := fun m h => mapM_option_mem' hms h
  refine ⟨fun cv hcv => ?_, fun cs hcs c hc => ?_⟩
  · obtain ⟨m, hmem, rfl⟩ := List.mem_map.mp hcv
    obtain ⟨mP, hmP⟩ := hm m hmem
    simp only [dMember, Option.bind_eq_bind, Option.bind_eq_some_iff] at hmP
    obtain ⟨_, _, d, hd, -⟩ := hmP
    exact ⟨_, (denoteCV_inv hd).2.1⟩
  · obtain ⟨m, hmem, rfl⟩ := List.mem_map.mp hcs
    obtain ⟨mP, hmP⟩ := hm m hmem
    simp only [dMember, Option.bind_eq_bind, Option.bind_eq_some_iff] at hmP
    obtain ⟨_, _, _, _, cs', hcs', -⟩ := hmP
    obtain ⟨cP, hcP⟩ := mapM_option_mem' hcs' hc
    simp only [dCtor, Option.map_eq_some_iff] at hcP
    obtain ⟨cv, hcv, -⟩ := hcP
    exact ⟨_, (denoteCV_inv hcv).2.1⟩

end L.Arena

namespace ConRon.Bridge.Inductives

open ConLeche ConRon.Arena ConRon.Bridge BT L.Arena

/-! ## The block's check -/

/-- **`checkBlock` grows the environment by `EnvGrowDen`**: con-ron's `checkBlock_bridge`, step
by step, with the environments the stages return. -/
theorem checkBlock_grow (hk : CoreSpec Arena.checkFuel)
    {env : Env} {fe fe' : IFEnv} {s s' : AState} {block : List IConstantInfo}
    {b : List ConstantInfo} {p₀ : Arena.BlockShape} {p₀P : ConLeche.BlockShape}
    (hok : CheckOK false env fe s) (henv : EnvWF env) (hrel : EnvRel env fe s.store)
    (hgate : TblGate fe)
    (hb : Frontend.denoteCIList s.store block = some b) (hp : dShape s.store p₀ = some p₀P)
    (hd : ∀ ms ∈ p₀P.members, ms.declared = ms.cvT)
    (hrun : Arena.checkBlock .verified fe block p₀ s = .ok (fe', s')) :
    EnvGrowDen s'.store fe fe' := by
  simp only [Arena.checkBlock] at hrun
  -- the distinct names
  have hnC := nameNodup_spec hok.state.wf _ _ (dCtors_names (BlockShape.allCtors_spec hp))
  have hnM := nameNodup_spec hok.state.wf _ _ (BlockShape.memberNames_spec hp)
  by_cases hc : (!nameNodup (p₀.allCtors.map (·.1.name)) ||
      !nameNodup p₀.memberNames) = true
  · rw [ite_eq_left hc] at hrun; exact absurd hrun (fun h => AM.fail_ok h)
  rw [ite_eq_right hc] at hrun
  have hnd : (p₀P.allCtors.map (·.1.name)).Nodup ∧ p₀P.memberNames.Nodup := by
    rw [hnC, hnM] at hc
    refine ⟨(name_nodup_iff _).1 ?_, (name_nodup_iff _).1 ?_⟩ <;> revert hc <;>
      cases ConLeche.Name.nodup (p₀P.allCtors.map (·.1.name)) <;>
      cases ConLeche.Name.nodup p₀P.memberNames <;> simp
  -- the `Bool` constructors' names
  obtain ⟨bt, s₀₁, kb1, zb1⟩ := AM.bind_ok hrun
  obtain ⟨hs01, hbt⟩ := pinAt_run hok.pins (by rfl) kb1
  subst s₀₁
  obtain ⟨bf, s₀₂, kb2, zb2⟩ := AM.bind_ok zb1
  obtain ⟨hs02, hbf⟩ := pinAt_run hok.pins (by rfl) kb2
  subst s₀₂
  have hct := contains_handle_eq hok.state.wf hbt (BlockShape.memberNames_spec hp)
  have hcf := contains_handle_eq hok.state.wf hbf (BlockShape.memberNames_spec hp)
  by_cases hbc : (p₀.memberNames.contains bt || p₀.memberNames.contains bf) = true
  · rw [ite_eq_left hbc] at zb2; exact absurd zb2 (fun h => AM.fail_ok h)
  rw [ite_eq_right hbc] at zb2
  have hbool : ConLeche.boolTrueName ∉ p₀P.memberNames ∧
      ConLeche.boolFalseName ∉ p₀P.memberNames := by
    rw [hct, hcf] at hbc
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hbc
    simp only [ConLeche.boolTrueName, ConLeche.boolFalseName, ConLeche.boolName]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hm := List.contains_iff_mem.mpr h
      rw [hbc.1] at hm; exact nomatch hm
    · have hm := List.contains_iff_mem.mpr h
      rw [hbc.2] at hm; exact nomatch hm
  -- the members at their telescopes
  obtain ⟨hms₀, -⟩ := dShape_inv hp
  obtain ⟨ms, s₁, h1, h2⟩ := AM.bind_ok zb2
  obtain ⟨c1, msP, hms, hF1⟩ := reduceMembers_spec fe hk henv p₀.nP p₀.members p₀P.members
    s s₁ ms hok hms₀ h1
  have hnP₀ := (dShape_inv hp).2.2.1
  rw [hnP₀] at hF1
  obtain ⟨F1, hF1'⟩ := id hF1
  rw [reduceMembers_datF] at hF1'
  obtain ⟨hAt, -⟩ := ConLeche.reduceMembers_inv hd hF1'
  -- the flush
  obtain ⟨u, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨c2, i2, hs2⟩ := ReadOK.flush c1.ok.toR h3
  have x12 : Ext s.store s₂.store := by rw [hs2]; exact c1.ext
  -- official's `is_rec`
  obtain ⟨isRec, s₃, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨p3, hisRec⟩ := blockIsRec_spec p₀ p₀P s₂ s₃ isRec c2.state (dShape_ext x12 _ _ hp) h5
  simp only [RV] at hisRec
  subst hisRec
  have c3 := p3.toCore c2
  have x13 := x12.trans p3.ext
  -- the pass
  obtain ⟨q, s₄, h7, h8⟩ := AM.bind_ok h6
  obtain ⟨env₁, qP, i4, c4, hrel4, henv₁, hq, hT, henv₂, hMs, hpl, hFP⟩ :=
    checkBlockPass_of (p₀P := { p₀P with members := msP }) hk henv c3.ok
      (hrel.mono x13) (dShape_members (dShape_ext x13 _ _ hp)
        (dMember_ext.list (show Ext s₁.store s₃.store by rw [← hs2]; exact p3.ext) _ _ hms))
      (fun m hm => (hAt m hm).declaredWF) h7
  have x4 := i4.ext
  -- the projection tables, read off the block once
  obtain ⟨oQ, s₄₁, h81, h82⟩ := AM.bind_ok h8
  obtain ⟨p41, -, hQ⟩ := blockTables_run p₀.members p₀P.members i4.state
    (dShape_ext (x13.trans x4) _ _ hp) (dMember_ext.list (x13.trans x4) _ _ hms₀) h81
  obtain ⟨Q, s₄₂, h83, h84⟩ := AM.bind_ok h82
  obtain ⟨rfl, rfl⟩ := unwrapOr_ok h83
  obtain ⟨QP, hQP, hQd, -⟩ := hQ
  have c41 := p41.toCore c4
  have x41 := x4.trans p41.ext
  -- the checks after it
  obtain ⟨fe₂, s₅, h9, h10⟩ := AM.bind_ok h84
  obtain ⟨i5, hFT⟩ := checkBlockTail_of hk henv₁ c41.ok (hrel4.mono p41.ext)
    (dPass_ext p41.ext hq) (denoteCIList_mono (x13.trans x41) _ _ hb) hT henv₂ hMs hpl hQd h9
  have x5 := i5.ext
  -- the block's install, read off the block
  have x05 : Ext s.store s₅.store := (x13.trans x41).trans x5
  have hpins5 : s₅.pins = s.pins := by
    rw [i5.pins, p41.pins, i4.pins, p3.pins, i2.pins, c1.pins]
  obtain ⟨recs, s₆, h11, h12⟩ := AM.bind_ok h10
  obtain ⟨p6, -, hL6⟩ := blockRecs_run p₀.recs p₀P.recs i5.state
    (hok.pins.mono x05 hpins5) (dShape_ext x05 _ _ hp)
    (dRec_ext.list x05 _ _ (dShape_inv hp).2.1) h11
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h12
  -- the environment
  have x06 : Ext s.store s'.store := x05.trans p6.ext
  have hp6 := dShape_ext x06 _ _ hp
  obtain ⟨hdecl, hctors⟩ := dShape_members_den hp6
  obtain ⟨hkd, hkc⟩ := reduceMembers_keeps _ h1
  obtain ⟨he1, hqm⟩ := checkBlockPass_env h7
  have hfe₂ := checkBlockTail_env h9
  have g1 : EnvGrowDen s'.store fe q.env1 ∧ TblGate q.env1 := by
    obtain ⟨sa, sb, hc1⟩ := he1
    exact EnvGrowDen.consBlockInds _ 0 hc1 (EnvGrowDen.refl' _ fe) hgate (by simpa [hkd] using hdecl)
  have g2 := EnvGrowDen.consBlockCtors (st := s'.store) (nP := q.p.nP) q.p.ctorGroups g1.1 g1.2
    (by
      intro g hg c hc
      rw [Arena.BlockShape.ctorGroups, hqm] at hg
      obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hg
      have hcs' : ms.ctors ∈ p₀.members.map (·.ctors) := by
        rw [← hkc]; exact List.mem_map.mpr ⟨ms, hms, rfl⟩
      exact hctors _ hcs' c hc)
  have g3 := g2.1.ofFEq hfe₂
  have gg3 : TblGate fe₂ := GR.FEq.gate hfe₂ g2.2
  have g4 := EnvGrowDen.pushAll recs g3 gg3 (fun ci hci => by
    obtain ⟨x, hx⟩ := denoteCIList_mem hL6 ci hci
    exact ciLvlDen_of_denote hx)
  have hQ6 : Frontend.denoteProjTableList s'.store Q = some QP :=
    denoteProjTableList_ext (i5.ext.trans p6.ext) hQd
  exact EnvGrowDen.pushTables Q g4.1 (denoteProjTableList_mem hQ6)

end ConRon.Bridge.Inductives

namespace L.Arena

open ConLeche ConRon.Arena ConRon.Bridge ConRon.Bridge.Inductives

/-- **`IndKindEnv`**: the inductive arm's environment grows by `EnvGrowDen` (con-ron's
`checkIndRoute_bridge`'s steps up to `checkBlock`, then `checkBlock_grow`). -/
theorem indKindEnv : IndKindEnv := by
  intro env pins fe fe' block nP s s' b hok hb hrun
  unfold ConRon.Arena.checkDeclKind at hrun
  obtain ⟨okb, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, hr1⟩ := indParamsOk_spec nP block b s s₁ okb hok.check.state hb h1
  subst hr1
  cases hparams : ConLeche.indParamsOk nP b with
  | false => rw [hparams] at h2; exact absurd h2 (fun h => AM.fail_ok h)
  | true =>
  rw [hparams] at h2
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h2
  obtain ⟨o, s₂, h3, h4⟩ := AM.bind_ok h2
  have c1 := hstep1.toCore hok.check
  have hb₁ : Frontend.denoteCIList s₁.store block = some b :=
    denoteCIList_mono hstep1.ext _ _ hb
  obtain ⟨c2, hr2⟩ := readBlock_spec fe nP block b s₁ s₂ o c1.ok hb₁ h3
  have hext12 : Ext s.store s₂.store := hstep1.ext.trans c2.ext
  cases o with
  | error e => exact absurd h4 (fun h => AM.fail_ok h)
  | ok p =>
  simp only [ROp] at hr2
  obtain ⟨q, hq, hrel⟩ := hr2
  have hq' := toOption_eq_some hq
  -- the ι reading rule, at the input index with the block pushed; the pops give it back
  obtain ⟨⟨reads, fe₀⟩, s₃, h5, h6⟩ := AM.bind_ok h4
  have hfeq := blockReadsAt_feq h5
  obtain ⟨c3, hrel3, x3, -, -⟩ := blockReadsAt_bridge c2.ok
    (EnvRel.ofCheck hok.check hok.gate hok.envWF |>.mono hext12) hrel h5
  obtain ⟨fe'', s₄, h7, h8⟩ := AM.bind_ok h6
  cases reads with
  | false => exact absurd h8 (fun h => AM.fail_ok h)
  | true =>
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h8
  exact EnvGrowDen.ofFEqL hfeq (checkBlock_grow CoreSpec.of_core c3 hok.envWF hrel3
    (GR.FEq.gate hfeq hok.gate) (denoteCIList_mono (c2.ext.trans x3) _ _ hb₁) (dShape_ext x3 _ _ hrel)
    (ConLeche.readBlock_declared hq') h7)

end L.Arena
