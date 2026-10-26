import ConAgua.L.ModelGen
import ConAgua.Arena.Verdict
import ConAgua.Arena.IndT.CheckIndDecl
import ConAgua.Checker.NoVerdictClosed

/-!
# `check_ind_decl`'s error refinement (lane `verdicts-b`, helper `ia`)

The verdict claim of the inductive arm of `checkDecl`: a failing run of class `1`/`2` claims the
twin's `checkDecl V pins fe (.indDecl block w)` fails with that class. Its callees outside the
verdict closure (`basis_pin_hit`, `ind_params_ok`, `block_parts`) claim nothing; the claims of
`check_basis_decl`, `check_block` and `check_shapeless` are hypotheses in the shape of their ok
refinements (`CheckBasisDeclE`, `CheckBlockE`, `CheckShapelessE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model cidE_spec (p : Prog) (hf : p.lookup "check_ind_decl" = some checkIndDecl)
  fns [hf ↦ cidE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

/-- **`check_basis_decl`'s error claim**, in the shape of `checkBasisDecl_refines`. -/
def CheckBasisDeclE (p : Prog) : Prop :=
  ∀ (_ : BasisProg p) (_ : CanonProg p) (_ : L.Rom.RomRefs p)
    (_ : p.lookup "pin_at" = some pinAtL)
    (_ : p.lookup "check_basis_decl" = some checkBasisDeclL) (n : Nat) (m : Mem) (a : AState)
    (dn : NIdx → Option ConLeche.Name) (_ : DnInj dn) (fe : IFEnv) (vis k : Word),
    k.toNat < 5 → StageR dn vis fe m a →
    (k = 4 → ConRon.Bridge.StateOK a ∧ L.Rom.NamesDn dn a L.Rom.quotNames) →
    ∀ e, callE p n "check_basis_decl" [vis, k] m = .error e →
      ErrClaim (checkBasisDecl fe (basisOfW k.toNat)) a e

/-- **`check_block`'s error claim**, in the shape of `checkBlock_refinesC` (any fuel `n ≤ 2 ^ 62`:
a class-`1`/`2` error at a fuel is the twin's). -/
def CheckBlockE (p : Prog) : Prop :=
  ∀ {env : ConLeche.Env} (_ : KnotStageProg p) (_ : ConLeche.EnvWF env) (_ : ValProg p)
    (_ : OpfF p) (_ : LvlCacheProg p) (_ : p.lookup "lv_leq_top" = some lvLeqTop)
    (_ : ApdF p) (_ : CrKeep p) (_ : IlpfF p) (_ : LzcF p)
    (_ : CbProg p) {fs fs2 : List FnName}
    (_ : closedA p posFreeA posFreeC fs = true) (_ : ∀ f ∈ passCallees, f ∈ fs)
    (_ : "block_raw_rec" ∈ fs) (_ : closedA p hbFreeA hbFreeC fs2 = true)
    (_ : ∀ f ∈ tailCallees, f ∈ fs2) {fsR fsT : List FnName} (_ : closedA p rcFreeA rcFreeC fsR = true)
    (_ : ∀ f ∈ tailRcCallees, f ∈ fsR) (_ : closedA p taFreeA taFreeC fsT = true)
    (_ : ∀ f ∈ blockTaCallees, f ∈ fsT) (n : Nat) (_ : n ≤ 2 ^ 62)
    (m : Mem) (a : AState) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {bO bL p0 : Word} {bs : BlockShape} {block : List IConstantInfo}
    (_ : StageC dn vis fe env m a) (_ : DecB (fun m => decBS m p0.toNat) m bs)
    (_ : ShapeSrc m p0) (_ : ShapeCV m p0)
    (_ : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block)
    (_ : PosMR m) (_ : ∃ mp, maMR m mp) (_ : AbsOK m)
    (_ : ∀ f ∈ passKeepCalleesC, AbsKeep p f) (_ : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (_ : AbsKeep p "block_raw_rec") (_ : ∃ mp, taMR m mp)
    (_ : RecsB m p0)
    (_ : ConRon.Bridge.IFEnvCoh fe) (_ : ConRon.Bridge.denoteFEnv a.store fe = some env)
    {shP : ConLeche.BlockShape} (_ : ConRon.Bridge.Inductives.dShape a.store bs = some shP)
    {blockP : List ConLeche.ConstantInfo} (_ : Frontend.denoteCIList a.store block = some blockP)
    {fsH fsM : List FnName} (_ : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR)
    (_ : closedA p rcHbFreeA rcHbFreeC fsH = true) (_ : "check_block_tables" ∈ fsH)
    (_ : closedA p maFreeA maFreeC fsM = true)
    (_ : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ fsM)
    (_ : ∀ ms ∈ bs.members, ∀ k ∈ ms.cvT.levelParams, (dn k).isSome),
    ∀ e, callE p n "check_block" [vis, bO, bL, p0] m = .error e →
      ErrClaim (ConRon.Arena.checkBlock V fe block ⟨bs⟩) a e

/-- **`check_shapeless`'s error claim**: the block's formers are checked as constants, then the
twin declines (`IndA5.lean` proves it from the claim of `check_constant_val`). -/
def CheckShapelessE (p : Prog) : Prop :=
  ∀ (_ : KnotStageProg p) (_ : ValProg p) (_ : ApdF p) (_ : CrKeep p)
    (_ : p.lookup "check_shapeless_formers" = some checkShapelessFormers)
    (_ : p.lookup "check_shapeless" = some checkShapeless) (n : Nat), n ≤ 2 ^ 62 →
    ∀ (m : Mem) (a : AState) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {o l : Word} {block : List IConstantInfo},
    StageT dn vis fe m a → DecB (fun m => decEBlk dn m o.toNat l.toNat) m block →
    L.Stubs.CrOK m → BlockLpsDn dn block → o.toNat + l.toNat ≤ erTop m →
    ∀ e, callE p n "check_shapeless" [vis, o, l] m = .error e →
      ErrClaim (ConRon.Arena.checkShapeless V fe block) a e

section sims
variable {p : Prog} (hkp : KnotStageProg p) (hV : ValProg p)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p) (hLz : LzcF p)

include hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz in
/-- **`check_ind_decl`'s error refinement**: the hypotheses of `cidW_okC`, the model `cidE`'s error
instead of `cidW`'s result, and the claims of `check_basis_decl`, `check_block`, `check_shapeless`. -/
theorem cidE_claim (P : CidProg p) {fs fs2 fsR fsT fsC : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC)
    (hkP : ∀ f ∈ passKeepCalleesC, AbsKeep p f) (hkt : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hkr : AbsKeep p "block_raw_rec")
    (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hCBD : CheckBasisDeclE p) (hCB : CheckBlockE p) (hCS : CheckShapelessE p)
    {n : Nat} (hn : n ≤ 2 ^ 62)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} {o l w : Word} {block : List IConstantInfo}
    {pins : List INatOpPinSet}
    {env : ConLeche.Env} {e : Err}
    (he : cidE p n m vis o l w = .error e) (hT : StageT dn vis fe m a)
    (hfold : ConRon.Bridge.FoldOK V env fe a)
    (hblk : DecB (fun m => decEBlk dn m o.toNat l.toNat) m block) (hb : o.toNat + l.toNat ≤ erTop m)
    (hden : ∃ x, Frontend.denoteDecl a.store (.indDecl block w.toNat) = some x) (hM : IndMemos m)
    (hfB : "check_basis_decl" ∈ fsC) (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR)
    {fsH fsM fsMc : List FnName} (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true)
    (hfH : "check_block_tables" ∈ fsH) (hclM : closedA p maFreeA maFreeC fsM = true)
    (hfM : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ fsM)
    (hlpd : BlockLpsDn dn block) :
    ErrClaim (checkDecl V pins fe (.indDecl block w.toNat)) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hT.stage
  have hIM := hM
  have hCM : CoreMemos m := hT.twin.memos
  replace hM : CidMemos m := ⟨hIM.stage.pos, hIM.stage.ma,
    hT.absOK hIM.i1 (L.Stubs.CrOK.crMemo hIM.cr), hIM.stage.ta⟩
  have hok : ConRon.Bridge.StateOK a := hfold.check.state
  obtain ⟨blockP, hbP⟩ : ∃ blockP, Frontend.denoteCIList a.store block = some blockP := by
    obtain ⟨x, hx⟩ := hden
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
    obtain ⟨b, hb, -⟩ := hx
    exact ⟨b, hb⟩
  have dnE : ∀ {st : ConRon.Arena.EStore}, ConRon.Arena.Ext a.store st →
      ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → denoteN st.ns k = some x :=
    fun hx k x e => hx.lss.ls.ns k x (hT.twin.mem.dnN k x e)
  cases n with
  | zero => rw [cidE.eq_1] at he; cases he; exact absurd Err.cls_outOfFuel hk0
  | succ n =>
  rw [cidE.arm1] at he
  unfold checkDecl
  dsimp only
  cases c1 : callE p n "basis_pin_hit" [o, l] m with
  | error e1 =>
    rw [c1, cidE.k_basis_pin_hit.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1] at he
  obtain ⟨x, a1, hrun1, hS1, hg1, hx⟩ := basisPinHit_ok P.bph n dn vis fe m m1 a o l block r1 hS hok hblk
    (callW_of_callE c1)
  refine ErrClaim.bind_right hrun1 ?_
  have hM1 := hM.call hclC (hfC _ (by simp [cidFrameCallees])) (callW_of_callE c1)
  obtain ⟨hIM1, hCM1⟩ := armMemos_call hclC (hfC _ (by simp [cidFrameCallees])) (callW_of_callE c1) hIM hCM
  obtain ⟨ok1, x1, hc1, hp1, -⟩ := ConRon.Bridge.basisPinHit_run hok hbP hrun1
  have k1 := (ConRon.Bridge.Inductives.PStep.of_caches ok1 x1 hc1 hp1).toCore hfold.check
  have hblk1 := hblk.grow (decEBlk_mono _ _ _) hg1
  cases x with
  | some kind =>
    obtain ⟨hz, hk4, hkind⟩ := hx
    rw [cidE.k_basis_pin_hit.eq_2, if_pos hz] at he
    cases c2 : callE p n "check_basis_decl" [vis, r1.tail.headD 0] m1 with
    | error e2 =>
      rw [c2, cidE.k_check_basis_decl.none] at he
      cases he
      show ErrClaim (checkBasisDecl fe kind) a1 _
      rw [← hkind]
      exact hCBD P.basis P.canon P.rom P.pa P.cbd n m1 a1 dn hdn fe vis (r1.tail.headD 0) (by omega) hS1
        (fun e => absurd hk4 (by rw [e]; decide)) _ c2
    | ok q2 =>
      rw [c2] at he
      cases he
  | none =>
  replace hx : r1.headD 0 = 0 := hx
  rw [cidE.k_basis_pin_hit.eq_2, if_neg (fun h => h hx)] at he
  have hbE : o.toNat + l.toNat < 2 ^ 64 := by
    have := hS.2.2.1; have := hS.2.2.2.2.1; omega
  cases c3 : callE p n "ind_params_ok" [w, o, l] m1 with
  | error e3 =>
    rw [c3, cidE.k_ind_params_ok.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3] at he
  obtain ⟨s3, hs3, -, hm3, hok3, hst3, hres3, -⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (indParamsOk_refines p P.ps P.ev P.ipo n ⟨m1, Locals.init []⟩ a1 dn vis fe w o l block hS1 hblk1 hbE)
    (callW_mono (callW_of_callE c3) (Nat.le_succ n))
  simp only at hm3
  rw [hm3] at hs3
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hst3] at hrun3
  refine ErrClaim.bind_right hrun3 ?_
  by_cases z3 : r3.headD 0 = 0
  · rw [cidE.k_ind_params_ok.abort1 p n vis o l w r3 _ z3] at he
    cases he
    have hpo3 : AM.res (indParamsOk w.toNat block) a1 = false := by
      rw [← hres3, z3]; rfl
    rw [hpo3]
    exact ErrClaim.fail _ _ (by decide)
  rw [cidE.k_ind_params_ok.arm1 p n vis o l w r3 _ z3] at he
  have hpo3 : AM.res (indParamsOk w.toNat block) a1 = true := by
    rw [← hres3]; simpa using z3
  rw [hpo3]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  -- `block_parts`
  cases c4 : callE p n "block_parts" [w, o, l] m1 with
  | error e4 =>
    rw [c4, cidE.k_block_parts.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [c4] at he
  obtain ⟨s4, hs4, -, hok4, hR4, hS4, hg4⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (blockParts_refinesC p hkp.closed hLC P.parts n ⟨m1, Locals.init []⟩ a1 w o l block
      (StageC.of_parts hS1 k1.ok hM1.2.2.1 (dnE k1.ext)) hM1.2.2.1
      (ConRon.Bridge.denoteCIList_mono k1.ext _ _ hbP) hblk1)
    (callW_mono (callW_of_callE c4) (by omega))
  subst hs4
  have hrun4 := AM.run_of_ok _ _ hok4
  refine ErrClaim.bind_right hrun4 ?_
  have hM4 := hM1.call hclC (hfC _ (by simp [cidFrameCallees])) (callW_of_callE c4)
  obtain ⟨hIM4, -⟩ := armMemos_call hclC (hfC _ (by simp [cidFrameCallees])) (callW_of_callE c4) hIM1 hCM1
  generalize AM.res (blockParts? w.toNat block) a1 = bp at hrun4 hR4 ⊢
  generalize AM.st (blockParts? w.toNat block) a1 = a4 at hrun4 hS4 ⊢
  have x01 := k1.ext
  obtain ⟨k4, hr4⟩ := ConRon.Bridge.Inductives.blockParts?_spec fe w.toNat block blockP a1 a4 bp k1.ok
    (ConRon.Bridge.denoteCIList_mono x01 _ _ hbP) hrun4
  have hC4 := StageC.of_parts hS4 k4.ok hM4.2.2.1 (dnE (x01.trans k4.ext))
  cases bp with
  | none =>
    have z4 : r4.headD 0 = 0 := hR4
    rw [cidE.k_block_parts.arm2 p n vis o l r4 _ z4] at he
    cases c5 : callE p n "check_shapeless" [vis, o, l] s4.mem with
    | error e5 =>
      rw [c5, cidE.k_check_shapeless.none] at he
      cases he
      exact hCS hkp hV hApd hCrk P.csf P.csl n (by omega) s4.mem a4 hC4.stageT
        (hblk1.grow (decEBlk_mono _ _ _) hg4) hIM4.cr hlpd (Nat.le_trans hb (hg1.trans hg4).2.1) _ c5
    | ok q5 =>
      rw [c5] at he
      cases he
  | some bp =>
  obtain ⟨hr41, hd4, hsl4⟩ := hR4
  obtain ⟨bs⟩ := bp
  have hq4 : DecB (fun m => decBS m (r4.tail.headD 0).toNat) s4.mem bs := by
    have hd : decBP (truncM s4.mem) (r4.tail.headD 0).toNat = some ⟨bs⟩ := hd4
    simp only [decBP, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hd
    obtain ⟨bs', hbs', e⟩ := hd
    cases e
    exact hbs'
  obtain ⟨hP4, hma4, hA4, hta4⟩ := hM4
  simp only [ConRon.Bridge.Inductives.ROp] at hr4
  obtain ⟨bpP, -, hpP4⟩ := hr4
  obtain ⟨shP, hshP, -⟩ : ∃ shP, ConRon.Bridge.Inductives.dShape a4.store bs = some shP ∧ bpP = ⟨shP⟩ := by
    simp only [ConRon.Bridge.Inductives.dParts, Option.map_eq_some_iff] at hpP4
    obtain ⟨shP, h1, h2⟩ := hpP4
    exact ⟨shP, h1, h2.symm⟩
  have z4 : r4.headD 0 ≠ 0 := by rw [hr41]; decide
  rw [cidE.k_block_parts.arm1 p n vis o l r4 _ z4] at he
  cases c5 : callE p n "check_block" [vis, o, l, r4.tail.headD 0] s4.mem with
  | error e5 =>
    rw [c5, cidE.k_check_basis_decl.none] at he
    cases he
    exact hCB hkp hfold.envWF hV hOpf hLC hLT hApd hCrk hIlpf hLz P.cb hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT
      n (by omega) s4.mem a4 hC4 hq4 hsl4.1 (shapeCV_of_decB hq4)
      (hblk1.grow (decEBlk_mono _ _ _) hg4) hP4 hma4 hA4 hkP hkt hkr hta4 hsl4.2 hfold.coh
      (ConRon.Bridge.denoteFEnv_mono (x01.trans k4.ext) hfold.denote) hshP
      (ConRon.Bridge.denoteCIList_mono (x01.trans k4.ext) _ _ hbP) hfRc hclH hfH hclM hfM (hlpd.members hrun4) _ c5
  | ok q5 =>
    rw [c5] at he
    cases he

end sims

end L.Ind
