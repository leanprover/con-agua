module

public import ConAgua.Arena.DeclKindEnv
import ConAgua.Arena.DeclKindEnvOne
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Inductives.BlockTail
public import ConRon.Bridge.Inductives.GenRec

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

/-- The formers, consed. -/
theorem EnvGrowDen.consBlockInds {st : EStore} {p₁ : BlockShape} {isRec : Bool} :
    ∀ (cvs : List IConstantVal) (i : Nat) {fe0 fe : IFEnv}, EnvGrowDen st fe0 fe → TblGate fe →
      (∀ cv ∈ cvs, ∃ ks, Frontend.denoteNList st.ns cv.levelParams = some ks) →
      EnvGrowDen st fe0 (consBlockInds p₁ isRec cvs i fe) ∧ TblGate (consBlockInds p₁ isRec cvs i fe)
  | [], _, _, _, h, hg, _ => ⟨h, hg⟩
  | cv :: cvs, i, _, fe, h, hg, hd => by
    obtain ⟨ks, hks⟩ := hd cv (by simp)
    exact EnvGrowDen.consBlockInds cvs (i + 1)
      (h.push' hg (ciLvlDen_of (ci := .indInfo cv (blockCapsAt p₁ i isRec)) hks
        (fun _ _ _ _ _ e => nomatch e)))
      (hg.push _) (fun cv' h' => hd cv' (by simp [h']))

/-- One member's constructors, consed. -/
theorem EnvGrowDen.consSumCtors {st : EStore} {nP : Nat} :
    ∀ (cs : List (IConstantVal × Nat)) {fe0 fe : IFEnv}, EnvGrowDen st fe0 fe → TblGate fe →
      (∀ c ∈ cs, ∃ ks, Frontend.denoteNList st.ns c.1.levelParams = some ks) →
      EnvGrowDen st fe0 (consSumCtors nP cs fe) ∧ TblGate (consSumCtors nP cs fe)
  | [], _, _, h, hg, _ => ⟨h, hg⟩
  | c :: cs, _, fe, h, hg, hd => by
    obtain ⟨ks, hks⟩ := hd c (by simp)
    exact EnvGrowDen.consSumCtors cs
      (h.push' hg (ciLvlDen_of (ci := .ctorInfo c.1 nP c.2) hks (fun _ _ _ _ _ e => nomatch e)))
      (hg.push _) (fun c' h' => hd c' (by simp [h']))

/-- Every member's constructors, consed. -/
theorem EnvGrowDen.consBlockCtors {st : EStore} {nP : Nat} :
    ∀ (css : List (List (IConstantVal × Nat))) {fe0 fe : IFEnv}, EnvGrowDen st fe0 fe → TblGate fe →
      (∀ cs ∈ css, ∀ c ∈ cs, ∃ ks, Frontend.denoteNList st.ns c.1.levelParams = some ks) →
      EnvGrowDen st fe0 (consBlockCtors nP css fe) ∧ TblGate (consBlockCtors nP css fe)
  | [], _, _, h, hg, _ => ⟨h, hg⟩
  | cs :: css, _, fe, h, hg, hd => by
    obtain ⟨h1, g1⟩ := EnvGrowDen.consSumCtors (nP := nP) cs h hg (hd cs (by simp))
    exact EnvGrowDen.consBlockCtors css h1 g1 (fun cs' h' => hd cs' (by simp [h']))

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
    fe₁ = consBlockInds p₁ isRec (p.members.map (·.declared)) 0 fe ∧ p₁.members = p.members := by
  unfold checkBlockInds at h
  cases hm : p.members with
  | nil => rw [hm] at h; exact absurd h (fun h' => AM.fail_ok h')
  | cons ms₀ rest =>
  rw [hm] at h
  obtain ⟨_, _, _, h⟩ := AM.bind_ok h
  obtain ⟨_, _, _, h⟩ := AM.bind_ok h
  obtain ⟨_, _, _, h⟩ := AM.bind_ok h
  obtain ⟨p₂, _, hw, h⟩ := AM.bind_ok h
  obtain ⟨he, -⟩ := AM.pure_ok h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨rfl, (withSort_members hw).trans hm⟩

theorem checkBlockPass_env {fe : IFEnv} {p : BlockShape} {isRec : Bool} {q : BlockPass} {s s' : AState}
    (h : checkBlockPass mode fe p isRec s = .ok (q, s')) :
    q.env1 = consBlockInds q.p isRec (p.members.map (·.declared)) 0 fe ∧ q.p.members = p.members := by
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
    GR.FEq fe₃ (consBlockCtors q.p.nP q.p.memberCtors q.env1) := by
  unfold checkBlockTail at h
  obtain ⟨_, _, _, h⟩ := AM.bind_ok h
  obtain ⟨_, _, _, h⟩ := AM.bind_ok h
  obtain ⟨⟨fe₂b, out⟩, _, hr, h⟩ := AM.bind_ok h
  have e1 : GR.FEq fe₂b (consBlockCtors q.p.nP q.p.memberCtors q.env1) :=
    genRecCheck_env (r := (fe₂b, out)) hr
  iterate 8 (try (obtain ⟨_, _, _, h⟩ := AM.bind_ok h))
  obtain ⟨rfl, -⟩ := AM.pure_ok h
  obtain ⟨news, hn, hf⟩ := BT.consBlockRecsTemp_pop _ fe₂b []
  simp only [List.nil_append] at hn
  rw [hn]
  exact hf.trans e1

end envs

end L.Arena
