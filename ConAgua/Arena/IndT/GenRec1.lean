import ConAgua.Arena.IndT.RecGen28
import ConAgua.Arena.IndInstallSpec.GpbWSimF
import ConRon.Bridge.Inductives.GenRec

/-!
# `genRecCheck` under `StageC`, part 1 (lane `indstaget`, helper `grc`)

What the refinements of `gen_rec_check_prep` and `gen_rec_check` (`GenRec2`, `GenRec3`) read:
`StageC.of_checkE` (`StageC` at another view and environment, from con-ron's `CheckOK` there) and
`classesNfs_refinesLpC` (`classes_nfs` under `StageC` with the classes' constructors'
level-parameter slices, `classesNfs_refinesLp`'s).
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
    ⟨hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.1, ⟨hA.2.2.2.1, hA.1, hA.2.2.2.2.1⟩,
      fun k x e => hx.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    hA.2.2.2.2.2.2.2.2⟩

/-- **`classes_nfs` refines `classesNfs` under `StageC`**, with the classes' constructor records'
level-parameter slices (`ClassesLp`) carried to the result (`classesNfs_refinesLp`'s). -/
theorem classesNfs_refinesLpC {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (P : CnsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl tblo tbll mo ml : Word)
    (bs : BlockShape) (formerTys : List EIdx) (tbl : List NestCtorNf) (ms : List TargetMajor)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (htbl : PSlR decNCN tbl tblo tbll s₀.mem) (hms : PSlR decTM ms mo ml s₀.mem) (hP : RcMR s₀.mem)
    (hlp : ClassesLp s₀.mem mo ml)
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
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem ∧
      (KeepW s₀.mem s'.mem → ClassesLp s'.mem (r.headD 0) (r.tail.headD 0)); ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (cnfs_spec p P.cns n s₀ vis q fto ftl tblo tbll mo ml) ?_
  rintro r s' ⟨hl, hm⟩
  rw [cnfsW_eq] at hm
  obtain ⟨⟨r0, m0⟩, c0, hm⟩ := of_K hm rfl
  rw [cnfsK1_some] at hm
  obtain ⟨mF, c1, hm⟩ := of_K hm rfl
  rw [cnfsK2_some] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm; obtain ⟨rfl, hmF⟩ := hm
  obtain ⟨s0, rfl, -, hw0⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩) (iwAlloc_specW p P.ha n _ ml) c0
  obtain ⟨hS0, hg0, hq0, ht0⟩ := allocW_stage hw0 hC.stage
  have hA0 := allocW_afr hw0 hA
  obtain ⟨rest, a', run, hSF, hgF, htF, hPF, hAF, ws', hws', hacc'⟩ := cnsW_okC hkp henv P dn fe vis q fto ftl
    tblo tbll mo ml (r0.headD 0) bs formerTys tbl ms s₀.mem hq0 hms htbl hbs hft hftb hformer (n + 1)
    (by omega) s0.mem mF a₀ 0 [] [] MsP c1 (hC.of_pstep hS0 hA0 (PStep.refl hC.check.state)) hA0 hg0
    (by omega) (hP.fr (allocW_mfr hw0)) UInt64.zero_le (by simp [decNL]) FA2.nil hsh hftP htblP
    (by simpa using hmsP) hMs
  simp only [UInt64.toNat_zero, List.drop_zero, List.nil_append] at run hacc'
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  rw [← hmF]
  refine ⟨hl, hok, ?_, by rw [hst]; exact hSF, hgF, hPF, hAF, fun hk => ?_⟩
  · rw [hres]
    refine ⟨?_, by simpa using htF⟩
    show decPL (truncM mF) (decTM (truncM mF)) _ _ = some rest
    simp only [List.headD_cons, List.tail_cons]
    rw [decPL_eq_bind, show decNL (truncM mF) (r0.headD 0).toNat ml.toNat = some ws' from decNL_decB hws' htF]
    exact cnsRec_mapM hgF hacc'
  · simp only [List.headD_cons, List.tail_cons]
    exact classesLp_of_cnsRec hlp hgF hk hC.stage.2.2.2.1 hws' hacc'


end L.Ind
