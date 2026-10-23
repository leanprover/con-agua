import ConAgua.Arena.IndInstallSpec42
import ConAgua.Arena.IndT.Block
import ConAgua.Arena.IndT.ArmMemos
import ConAgua.Arena.IndRealAbsT
import ConAgua.Arena.IndRealMemoCrT

/-!
# `check_ind_decl` under `StageC` (lane `indstaget`)

`cidW_ok`'s proof from `StageT` and the twin's fold invariant (`FoldOK`: `CheckOK`, the
environment's coherence and denotation): `basis_pin_hit` (con-ron's `basisPinHit_run`: a `PStep`),
`ind_params_ok` and `block_parts` (con-ron's `indParamsOk_spec`, `blockParts?_spec`: `CheckOK` at
`block_parts`' state, the shape's denotation), then `checkBlock_refinesC` at the call's own fuel
(lifted to `5` only when below it). Lane `indproofs4` composes it into `IndArmSpec`.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hkp : KnotStageProg p) (hV : ValProg p) (hkc : AbsKeep p "check_constant_val")
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p)

include hkp hV hkc hOpf hLC hLT hApd hCrk hIlpf in
/-- **`check_ind_decl`'s model refines the `.indDecl` arm of `checkDecl`** under `StageT` and the
twin's fold invariant (`cidW_ok`'s, the inner stages under `StageC`): the post is `cidW_ok`'s. -/
@[refines_part ConRon.Arena.checkDecl "the inductive arm (check_ind_decl), under StageC"]
theorem cidW_okC (P : CidProg p) {fs fs2 fsR fsT fsC : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC)
    (hkP : ∀ f ∈ passKeepCalleesC, AbsKeep p f) (hkt : ∀ f ∈ tailKeepCallees, AbsKeep p f)
    (hkr : AbsKeep p "block_raw_rec")
    {n : Nat} (hn : n ≤ 2 ^ 62)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {o l w : Word} {r : List Word} {block : List IConstantInfo}
    {pins : List INatOpPinSet}
    {env : ConLeche.Env}
    (h : cidW p n m vis o l w = some (r, m')) (hT : StageT dn vis fe m a)
    (hfold : ConRon.Bridge.FoldOK V env fe a)
    (hblk : DecB (fun m => decEBlk dn m o.toNat l.toNat) m block) (hb : o.toNat + l.toNat ≤ erTop m)
    (hden : ∃ x, Frontend.denoteDecl a.store (.indDecl block w.toNat) = some x) (hM : IndMemos m)
    (hfB : "check_basis_decl" ∈ fsC) (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR)
    {fsH fsM fsMc : List FnName} (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true)
    (hfH : "check_block_tables" ∈ fsH) (hclM : closedA p maFreeA maFreeC fsM = true)
    (hfM : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ fsM)
    (hclMc : closedA p mcFreeA mcFreeC fsMc = true) (hfMc : "check_block" ∈ fsMc) :
    ∃ fe' a', (checkDecl V pins fe (.indDecl block w.toNat)).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m' ∧ IndMemos m' := by
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
  | zero => simp [cidW] at h
  | succ n =>
  rw [cidW_step] at h
  -- `basis_pin_hit`
  cases c1 : callW p n "basis_pin_hit" [o, l] m with
  | none => rw [c1] at h; cases h
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1, cidK1_some] at h
  obtain ⟨x, a1, hrun1, hS1, hg1, hx⟩ := basisPinHit_ok P.bph n dn vis fe m m1 a o l block r1 hS hok hblk c1
  have hM1 := hM.call hclC (hfC _ (by simp [cidFrameCallees])) c1
  obtain ⟨hIM1, hCM1⟩ := armMemos_call hclC (hfC _ (by simp [cidFrameCallees])) c1 hIM hCM
  obtain ⟨ok1, x1, hc1, hp1, -⟩ := ConRon.Bridge.basisPinHit_run hok hbP hrun1
  have k1 := (ConRon.Bridge.Inductives.PStep.of_caches ok1 x1 hc1 hp1).toCore hfold.check
  have hblk1 := hblk.grow (decEBlk_mono _ _ _) hg1
  cases x with
  | some kind =>
    obtain ⟨hz, hk4, hkind⟩ := hx
    rw [if_neg hz] at h
    cases c2 : callW p n "check_basis_decl" [vis, r1.tail.headD 0] m1 with
    | none => rw [c2] at h; cases h
    | some q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [c2, cidK2_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨s2, hs2, -, hok2, hS2, hg2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (checkBasisDecl_refines p P.basis P.canon P.rom P.pa P.cbd n ⟨m1, Locals.init []⟩ a1 dn hdn fe
        vis (r1.tail.headD 0) (by omega) hS1
        (fun e => absurd hk4 (by rw [e]; decide))) c2
    subst hs2
    have hrun2 := AM.run_of_ok _ _ hok2
    rw [hkind] at hrun2 hS2
    obtain ⟨hIM2, hCM2⟩ := armMemos_call hclC hfB c2 hIM1 hCM1
    refine ⟨_, _, ?_, by simpa using hS2, hCM2, hg1.trans hg2, hIM2⟩
    simp only [checkDecl, StateT.run_bind, hrun1, exc_ok_bind']
    exact hrun2
  | none =>
  rw [if_pos hx] at h
  -- `ind_params_ok`
  have hbE : o.toNat + l.toNat < 2 ^ 64 := by
    have := hS.2.2.1; have := hS.2.2.2.2.1; omega
  cases c3 : callW p n "ind_params_ok" [w, o, l] m1 with
  | none => rw [c3] at h; cases h
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3, cidK3_some] at h
  obtain ⟨s3, hs3, -, hm3, hok3, hst3, hres3, -⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (indParamsOk_refines p P.ps P.ev P.ipo n ⟨m1, Locals.init []⟩ a1 dn vis fe w o l block hS1 hblk1 hbE)
    (callW_mono c3 (Nat.le_succ n))
  simp only at hm3
  rw [hm3] at hs3
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hst3] at hrun3
  by_cases z3 : r3.headD 0 = 0
  · rw [if_pos z3] at h; cases h
  rw [if_neg z3] at h
  have hpo3 : AM.res (indParamsOk w.toNat block) a1 = true := by
    rw [← hres3]; simpa using z3
  rw [hpo3] at hrun3
  obtain ⟨st3, -⟩ := ConRon.Bridge.Inductives.indParamsOk_spec w.toNat block blockP a1 a1 _ k1.ok.state
    (ConRon.Bridge.denoteCIList_mono k1.ext _ _ hbP) hrun3
  -- `block_parts`
  cases c4 : callW p n "block_parts" [w, o, l] m1 with
  | none => rw [c4] at h; cases h
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [c4, cidK4_some] at h
  obtain ⟨s4, hs4, -, hok4, hR4, hS4, hg4⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (blockParts_refines p P.parts n ⟨m1, Locals.init []⟩ a1 dn vis fe w o l block hS1 hblk1)
    (callW_mono c4 (by omega))
  subst hs4
  have hrun4 := AM.run_of_ok _ _ hok4
  have hM4 := hM1.call hclC (hfC _ (by simp [cidFrameCallees])) c4
  obtain ⟨hIM4, -⟩ := armMemos_call hclC (hfC _ (by simp [cidFrameCallees])) c4 hIM1 hCM1
  by_cases z4 : r4.headD 0 = 0
  · rw [if_pos z4] at h; cases h
  rw [if_neg z4] at h
  generalize AM.res (blockParts? w.toNat block) a1 = bp at hrun4 hR4
  generalize AM.st (blockParts? w.toNat block) a1 = a4 at hrun4 hS4
  have x01 := k1.ext
  obtain ⟨k4, hr4⟩ := ConRon.Bridge.Inductives.blockParts?_spec fe w.toNat block blockP a1 a4 bp k1.ok
    (ConRon.Bridge.denoteCIList_mono x01 _ _ hbP) hrun4
  cases bp with
  | none => exact absurd hR4 z4
  | some bp =>
  obtain ⟨-, hd4, hsl4⟩ := hR4
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
  have x04 := x01.trans k4.ext
  have hC4 := StageC.of_parts hS4 k4.ok hA4 (dnE x04)
  -- `check_block`
  cases c5 : callW p n "check_block" [vis, o, l, r4.tail.headD 0] s4.mem with
  | none => rw [c5] at h; cases h
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [c5, cidK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨j, hj, c5b⟩ : ∃ j, j + 4 ≤ 2 ^ 62 ∧
      callW p (j + 5) "check_block" [vis, o, l, r4.tail.headD 0] s4.mem = some (r5, m5) := by
    by_cases h5 : 5 ≤ n
    · exact ⟨n - 5, by omega, by rw [show n - 5 + 5 = n by omega]; exact c5⟩
    · exact ⟨0, by omega, callW_mono c5 (by omega)⟩
  have hmc5 := mcMR.ofClosed hclMc hfMc c5b hIM4.stage.mc
  obtain ⟨s5, hs5, -, hok5, hS5, hg5, -, hA5, hR5, hma5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (checkBlock_refinesC hkp hfold.envWF hV hkc hOpf hLC hLT hApd hCrk hIlpf P.cb hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT j hj
      ⟨s4.mem, Locals.init []⟩ a4 hC4 hq4 hsl4.1 (shapeCV_of_decB hq4)
      (hblk1.grow (decEBlk_mono _ _ _) hg4) hP4 hma4 hA4 hkP hkt hkr hta4 hsl4.2 hfold.coh
      (ConRon.Bridge.denoteFEnv_mono x04 hfold.denote) hshP
      (ConRon.Bridge.denoteCIList_mono x04 _ _ hbP) hfRc hclH hfH hclM hfM) c5b
  subst hs5
  have hrun5 := AM.run_of_ok _ _ hok5
  have hCM5 : CoreMemos s5.mem := ⟨hA5.2.2.2.1, hA5.1, hA5.2.2.2.2.1⟩
  refine ⟨_, _, ?_, by simpa using hS5, hCM5, hg1.trans (hg4.trans hg5),
    ⟨⟨hR5.pos, hma5, hmc5, hR5.ta⟩, hA5.2.1, hA5.2.2.1.crOK⟩⟩
  simp only [checkDecl, StateT.run_bind, hrun1, exc_ok_bind', hrun3, Bool.not_true, Bool.false_eq_true, ite_false, hrun4]
  exact hrun5

end sims

end L.Ind
