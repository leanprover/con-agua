import ConAgua.Arena.IndT.RecGen28
import ConAgua.Arena.IndInstallSpec.GpbWSimF
import ConRon.Bridge.Inductives.GenRec

/-!
# `genRecCheck` under `StageC`, part 1 (lane `indstaget`, helper `grc`)

What the refinements of `gen_rec_check_prep` and `gen_rec_check` (`GenRec2`, `GenRec3`) read:
`StageC.of_checkE` (`StageC` at another view and environment, from con-ron's `CheckOK` there) and
`cnfs_ref` (`classes_nfs` for both outcomes, under `StageC`, with the classes' constructors'
level-parameter slices as a conditional field, `classesNfs_refinesLp`'s); its ok half
`classesNfs_refinesC`.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtorNf dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`StageC` at another view and environment**: the stage relation there, `CheckOK` there, the
memory's half from `AbsOK` and the store's extension. -/
theorem StageC.of_checkE {dn : NIdx → Option ConLeche.Name} {vis vis' : Word} {fe fe' : IFEnv}
    {env env' : ConLeche.Env} {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR dn vis' fe' m' a') (hA : AbsOK m') (hck : ConRon.Bridge.CheckOK V env' fe' a')
    (hx : ConRon.Arena.Ext a.store a'.store) : StageC dn vis' fe' env' m' a' :=
  ⟨hS, hck,
    ⟨hA.wk.2.1, hA.wk.2.2.1, hA.wk.2.2.2.1, ⟨hA.il, hA.ab, hA.wk.1⟩,
      fun k x e => hx.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    hA.wk.2.2.2.2⟩

/-- What `classes_nfs` gives besides the twin's classes `ys` (from `m`, the classes' slice `(mo, ml)`):
the result slice, the stage, the growth, the memos, `AbsOK`; and, when the classes' constructor
records' level-parameter slices are given (`ClassesLp`) and the arrays kept their sizes, those of the
result's records. -/
structure CnfsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (mo ml : Word) (r : List Word) (m' : Mem) (ys : List TargetMajor) (a' : AState) : Prop where
  slice : PSlR decTM ys (r.headD 0) (r.tail.headD 0) m'
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  rc : RcMR m'
  abs : AbsOK m'
  lp : ClassesLp m mo ml → KeepW m m' → ClassesLp m' (r.headD 0) (r.tail.headD 0)

/-- **`classes_nfs` refines `classesNfs`, both outcomes** (under `StageC`, the inputs' denotations and
scoping as con-ron's `classesNfs_spec` asks): `iw_alloc` (class `0` on failure), then the loop
(`cns_ref`). -/
theorem cnfs_ref {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (P : CnsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis q fto ftl tblo tbll mo ml : Word}
    {bs : BlockShape} {formerTys : List EIdx} {tbl : List NestCtorNf} {ms : List TargetMajor}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hbs : BSOK m q.toNat bs)
    (hft : decHL m fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tblo tbll m) (hms : PSlR decTM ms mo ml m) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {MsP : List ConLeche.TargetMajor} (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (htblP : tbl.mapM (dCtorNf a.store) = some tblP) (hmsP : ms.mapM (dMajor a.store) = some MsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    RefE (VerdictCtx p) (cnfsE p n m vis q fto ftl tblo tbll mo ml)
      (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a
      (fun v ys a' => CnfsPost dn vis fe env m mo ml v.1 v.2 ys a') := by
  rcases n with _ | n
  · rw [cnfsE_zero]; exact RefE.of_cls0 (by simp)
  rw [cnfsE_succ]
  cases c0 : callW p n "iw_alloc" [ml] m with
  | none => rw [cnfsEK1_none]; exact RefE.of_cls0 (by simp)
  | some q0 =>
  obtain ⟨r0, m0⟩ := q0
  rw [cnfsEK1_some]
  obtain ⟨s0, rfl, -, hw0⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (iwAlloc_specW p P.ha n _ ml) c0
  obtain ⟨hS0, hg0, hq0, ht0⟩ := allocW_stage hw0 hC.stage
  have hA0 := allocW_afr hw0 hA
  have hL := cns_ref hkp henv P dn fe vis q fto ftl tblo tbll mo ml (r0.headD 0) bs formerTys tbl ms m hq0
    hms htbl hbs hft hftb hformer (n + 1) (by omega) s0.mem a 0 [] [] MsP
    (hC.of_pstep hS0 hA0 (PStep.refl hC.check.state)) hA0 hg0 (by omega) (hP.fr (allocW_mfr hw0))
    UInt64.zero_le (by simp [decNL]) FA2.nil hsh hftP htblP (by simpa using hmsP) hMs
  simp only [UInt64.toNat_zero, List.drop_zero] at hL
  refine RefE.tailMap_eq (fun _ => rfl) (fun _ => rfl) id rfl (fun mF rest a' hR => ?_) hL
  obtain ⟨hSF, hgF, htF, hPF, hAF, ws', hws', hacc'⟩ := hR
  simp only [List.nil_append] at hacc'
  refine ⟨⟨?_, by simpa using htF⟩, hSF, hgF, hPF, hAF, fun hlp hk => ?_⟩
  · show decPL (truncM mF) (decTM (truncM mF)) _ _ = some rest
    simp only [List.headD_cons, List.tail_cons]
    rw [decPL_eq_bind, show decNL (truncM mF) (r0.headD 0).toNat ml.toNat = some ws' from decNL_decB hws' htF]
    exact cnsRec_mapM hgF hacc'
  · simp only [List.headD_cons, List.tail_cons]
    exact classesLp_of_cnsRec hlp hgF hk hC.stage.2.2.2.1 hws' hacc'

/-- **`classes_nfs` refines `classesNfs`** under `StageC` (`cnfs_ref`'s ok half). -/
@[refines ConRon.Arena.classesNfs]
theorem classesNfs_refinesC {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (P : CnsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl tblo tbll mo ml : Word)
    (bs : BlockShape) (formerTys : List EIdx) (tbl : List NestCtorNf) (ms : List TargetMajor)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (htbl : PSlR decNCN tbl tblo tbll s₀.mem) (hms : PSlR decTM ms mo ml s₀.mem) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {MsP : List ConLeche.TargetMajor} (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (htblP : tbl.mapM (dCtorNf a₀.store) = some tblP) (hmsP : ms.mapM (dMajor a₀.store) = some MsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "classes_nfs" [vis, q, fto, ftl, tblo, tbll, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀ ∧
      PSlR decTM (AM.res (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀) (r.headD 0) (r.tail.headD 0) s'.mem ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (cnfsE_spec p P.cns n s₀ vis q fto ftl tblo tbll mo ml)
    (cnfs_ref hkp henv P n hn hC hA hbs hft hftb htbl hms hP hsh hftP htblP hmsP hformer hMs)) ?_
  rintro r s' ⟨hl, ys, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hres]; exact hR.slice, by rw [hst]; exact hR.stage, hR.grow, hR.rc, hR.abs⟩


end L.Ind
