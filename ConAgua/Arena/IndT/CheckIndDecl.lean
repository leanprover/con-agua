module

public import ConAgua.Arena.IndRealPartsC2
public import ConAgua.Arena.IndT.Block
public import ConAgua.Arena.IndArmLps
public import ConAgua.Arena.IndRealIpo
public import ConAgua.Arena.IndInstallSpec.ShapeCVOfDecB
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.L.ModelGen
import ConAgua.Arena.IndPartsSpec.BlockSplitRecs
import ConAgua.Arena.IndRealAbsT
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndT.Tail
import ConAgua.Arena.StageC
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Inductives.Install
import ConLeche.Verify.Inductives.BlockShapeInv
import all ConAgua.Arena.IndParts
import all Init.Data.List.Control
import ConAgua.Arena.IndT.ArmMemos
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.ExceptOpt

@[expose] public section

/-!
# `check_ind_decl` under `StageC` (lane `indstaget`)

`check_ind_decl`'s unified model `cidE` and its refinement `cid_ref` (both outcomes) from `StageT`
and the twin's fold invariant (`FoldOK`: `CheckOK`, the environment's coherence and denotation);
`checkIndDecl_refinesC` is its ok half (`IndArm.lean` composes it into `IndArmSpec`), the error
half the inductive arm's claim (`indArmSpecE_of`, `Verdict/IndArmTopE.lean`). Its `G` is `CtsG`.
-/


noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

open ConRon.Bridge (AM.bind_ok AM.pure_ok)

set_option experimental.vcgen true in
/-- **`check_ind_decl`'s unified model**: the parameters' check and the reader (outside the
verdict closure) lifted; `check_block` through its run. -/
l_model cidE_spec (p : Prog) (P : CidProg p)
  fns [P.cid ↦ cidE]
  specs [callW_spec p n "ind_params_ok", callW_spec p n "read_block",
    callW_spec p n "block_reads_at"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-- A former of `blockSplit`'s split is an `indInfo` of the block. -/
theorem blockSplit_formers_mem : ∀ (block : List IConstantInfo) {cvTs cs rs} (cv : IConstantVal),
    ConRon.Arena.blockSplit block = some (cvTs, cs, rs) → cv ∈ cvTs → ∃ caps, IConstantInfo.indInfo cv caps ∈ block
  | [], cvTs, cs, rs, cv, h, hm => by
    simp only [ConRon.Arena.blockSplit] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp at hm
    · cases h
  | ci :: rest, cvTs, cs, rs, cv, h, hm => by
    cases ci with
    | indInfo cvT caps =>
      simp only [ConRon.Arena.blockSplit] at h
      split at h
      · rename_i q hq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rcases List.mem_cons.1 hm with rfl | hm
        · exact ⟨caps, List.mem_cons_self ..⟩
        · obtain ⟨caps', h'⟩ := blockSplit_formers_mem rest cv (show ConRon.Arena.blockSplit rest = some (q.1, q.2.1, q.2.2) from hq) hm
          exact ⟨caps', List.mem_cons_of_mem _ h'⟩
      · cases h
    | _ =>
      simp only [ConRon.Arena.blockSplit] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp at hm
      · cases h

local syntax "chase2 " ident ident : tactic
macro_rules
  | `(tactic| chase2 $y $k) => `(tactic| first
      | (obtain ⟨e, -⟩ := AM.pure_ok $y; cases e; exact $k _)
      | (obtain ⟨_, t, -, y'⟩ := AM.bind_ok $y; chase2 y' $k)
      | (split at $y:ident <;> chase2 $y $k))

theorem piBinders_len : ∀ (fuel : Nat) {h : EIdx} {s s' : AState} {r : List EIdx × EIdx},
    ConRon.Arena.piBinders fuel h s = .ok (r, s') → r.1.length ≤ fuel
  | 0, h, s, s', r, hr => by
    simp only [ConRon.Arena.piBinders] at hr; exact absurd hr (fun hc => ConRon.Bridge.AM.fail_ok hc)
  | fuel + 1, h, s, s', r, hr => by
    simp only [ConRon.Arena.piBinders] at hr
    split at hr
    · obtain ⟨v, s1, -, hr⟩ := AM.bind_ok hr
      split at hr
      · exact absurd hr (fun hc => ConRon.Bridge.AM.fail_ok hc)
      · obtain ⟨⟨bs, e⟩, s2, h2, hr⟩ := AM.bind_ok hr
        obtain ⟨rfl, -⟩ := AM.pure_ok hr
        have := piBinders_len fuel h2
        simp only [List.length_cons] at this ⊢; omega
    · obtain ⟨rfl, -⟩ := AM.pure_ok hr; simp

theorem blockCounts_nP {nPd k nC nR : Nat} {cvT : IConstantVal} {r : Option (Nat × Nat)}
    {s s' : AState} {c : Nat × Nat} (hk : 0 < k)
    (h : ConRon.Arena.blockCounts nPd k nC nR cvT r s = .ok (.ok c, s')) :
    nPd ≤ coreWalkFuel ∨ ∃ mI rP, r = some (mI, rP) ∧ nPd < rP := by
  unfold ConRon.Arena.blockCounts at h
  obtain ⟨⟨bs, res⟩, s1, h1, h⟩ := AM.bind_ok h
  have hl := piBinders_len _ h1
  obtain ⟨v, s2, -, h⟩ := AM.bind_ok h
  dsimp only at h hl
  split at h
  · split at h
    · left; omega
    · cases (AM.pure_ok h).1
  · rcases r with _ | ⟨mI, rP⟩
    · cases (AM.pure_ok h).1
    · right; refine ⟨mI, rP, rfl, ?_⟩
      dsimp only at h
      split at h
      · cases (AM.pure_ok h).1
      · rename_i h1; simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h1
        split at h
        · rename_i h2; simp only [beq_iff_eq] at h2; omega
        · split at h
          · rename_i h3; simp only [Bool.and_eq_true, decide_eq_true_eq] at h3; omega
          · cases (AM.pure_ok h).1

theorem findM?_mem {α : Type} {f : α → AM Bool} : ∀ {l : List α} {s s' : AState} {q : α},
    List.findM? f l s = .ok (some q, s') → q ∈ l
  | [], s, s', q, h => by simp only [List.findM?] at h; cases (AM.pure_ok h).1
  | x :: xs, s, s', q, h => by
    simp only [List.findM?] at h
    obtain ⟨b, s1, -, h⟩ := AM.bind_ok h
    cases b
    · exact List.mem_cons_of_mem _ (findM?_mem h)
    · obtain ⟨e, -⟩ := AM.pure_ok h; cases e; exact List.mem_cons_self ..

theorem blockMemberCounts_nP {nPd k nC : Nat} {names : List NIdx}
    {rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)} {m : Nat} {cvT : IConstantVal}
    {ts : List IConstantVal} {s s' : AState} {ns : List Nat} (hk : 0 < k)
    (h : ConRon.Arena.blockMemberCounts nPd k nC names rs m (cvT :: ts) s = .ok (.ok ns, s')) :
    nPd ≤ coreWalkFuel ∨ ∃ q ∈ rs, nPd < q.2.2.1 := by
  simp only [ConRon.Arena.blockMemberCounts] at h
  obtain ⟨q, s1, h1, h⟩ := AM.bind_ok h
  obtain ⟨c, s2, h2, h⟩ := AM.bind_ok h
  rcases c with _ | c
  · cases (AM.pure_ok h).1
  rcases blockCounts_nP hk h2 with h3 | ⟨mI, rP, hr, hlt⟩
  · exact .inl h3
  · right
    rcases q with _ | q
    · cases hr
    · simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      exact ⟨q, findM?_mem h1, hlt⟩

theorem blockSplitRecs_mem : ∀ (block : List IConstantInfo) {rs}, ConRon.Arena.blockSplitRecs block = some rs →
    ∀ q ∈ rs, IConstantInfo.recInfo q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ∈ block
  | [], rs, h => by simp only [ConRon.Arena.blockSplitRecs, Option.some.injEq] at h; subst h; simp
  | ci :: rest, rs, h => by
    cases ci with
    | recInfo cv mI rP isK rules =>
      simp only [ConRon.Arena.blockSplitRecs] at h
      split at h
      · rename_i rs' hrs
        simp only [Option.some.injEq] at h; subst h
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (blockSplitRecs_mem rest hrs q hq)
      · cases h
    | _ => simp only [ConRon.Arena.blockSplitRecs] at h; cases h

theorem blockSplitCtors_mem : ∀ (block : List IConstantInfo) {cs rs},
    ConRon.Arena.blockSplitCtors block = some (cs, rs) →
    ∀ q ∈ rs, IConstantInfo.recInfo q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ∈ block
  | [], cs, rs, h => by
    simp only [ConRon.Arena.blockSplitCtors, ConRon.Arena.blockSplitRecs, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; simp
  | ci :: rest, cs, rs, h => by
    cases ci with
    | ctorInfo cv a b _ =>
      simp only [ConRon.Arena.blockSplitCtors] at h
      split at h
      · rename_i q hq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact fun x hx => List.mem_cons_of_mem _ (blockSplitCtors_mem rest (cs := q.1) (by rw [hq]) x hx)
      · cases h
    | _ =>
      simp only [ConRon.Arena.blockSplitCtors] at h
      split at h
      · rename_i rs' hrs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact blockSplitRecs_mem _ hrs
      · cases h

theorem blockSplit_recs_mem : ∀ (block : List IConstantInfo) {cvTs cs rs},
    ConRon.Arena.blockSplit block = some (cvTs, cs, rs) →
    ∀ q ∈ rs, IConstantInfo.recInfo q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ∈ block
  | [], cvTs, cs, rs, h => by
    simp only [ConRon.Arena.blockSplit] at h
    split at h
    · rename_i q hq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      exact blockSplitCtors_mem [] (cs := q.1) (by rw [hq])
    · cases h
  | ci :: rest, cvTs, cs, rs, h => by
    cases ci with
    | indInfo cvT caps =>
      simp only [ConRon.Arena.blockSplit] at h
      split at h
      · rename_i q hq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, h2⟩ := h
        exact fun x hx => List.mem_cons_of_mem _
          (blockSplit_recs_mem rest (cvTs := q.1) (cs := cs) (by rw [hq, ← h2]) x hx)
      · cases h
    | _ =>
      simp only [ConRon.Arena.blockSplit] at h
      split at h
      · rename_i q hq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        exact blockSplitCtors_mem _ (cs := q.1) (by rw [hq])
      · cases h

/-- `chase2` with the key at `rfl`. -/
local syntax "chase3 " ident ident : tactic
macro_rules
  | `(tactic| chase3 $y $k) => `(tactic| first
      | (obtain ⟨e, -⟩ := AM.pure_ok $y; cases e; exact $k _ rfl)
      | (obtain ⟨e, -⟩ := AM.pure_ok $y; cases e; done)
      | (obtain ⟨_, t, -, y'⟩ := AM.bind_ok $y; chase3 y' $k)
      | (split at $y:ident <;> chase3 $y $k))

/-- **The reader's parameter count is below `2^64 - 1`** (`block_tables`' `struct_proj_bodies`
computes `o + nP - 1 - k` in words): `blockCounts`' first arm bounds it by the fuel of
`piBinders`, its other two by a recursor's `rP`, which `hrp` bounds (a decoded word: `decCIsR_rP`). -/
theorem readBlock_nP_lt {nPd : Nat} {block : List IConstantInfo} {s s' : AState} {bs : BlockShape}
    (hrp : ∀ cv mI rP isK rules, IConstantInfo.recInfo cv mI rP isK rules ∈ block → rP < 2 ^ 64)
    (h : (ConRon.Arena.readBlock nPd block).run s = .ok (.ok bs, s')) : bs.nP + 1 < 2 ^ 64 := by
  unfold ConRon.Arena.readBlock at h
  cases hsp : ConRon.Arena.blockSplit block with
  | none => rw [hsp] at h; cases (AM.pure_ok h).1
  | some q =>
  obtain ⟨cvTs, cs, rs⟩ := q
  rw [hsp] at h
  rcases cvTs with _ | ⟨cvT0, cvTs'⟩
  · cases (AM.pure_ok h).1
  rcases rs with _ | ⟨⟨cvR0, x1, x2, x3, x4⟩, rs'⟩
  · cases (AM.pure_ok h).1
  dsimp only at h
  obtain ⟨cnt, s1, h1, z1⟩ := AM.bind_ok h
  cases cnt with
  | error e => cases (AM.pure_ok z1).1
  | ok nIdxs =>
  have hb : nPd + 1 < 2 ^ 64 := by
    rcases blockMemberCounts_nP (by simp) h1 with h2 | ⟨q, hq, hlt⟩
    · have : coreWalkFuel = 4000000000 := rfl; omega
    · have := hrp _ _ _ _ _ (blockSplit_recs_mem block hsp q hq); omega
  dsimp only at z1
  have key : ∀ x : BlockShape, x.nP = nPd → x.nP + 1 < 2 ^ 64 := fun x hx => hx ▸ hb
  chase3 z1 key

theorem decCI_recInfo_rP {a : Nat → Option Word} {p : Nat} {cv : IConstantVal} {mI rP : Nat} {isK : Bool}
    {rules : List IRecRule} (h : L.Arena.decCI a p = some (.recInfo cv mI rP isK rules)) : rP < 2 ^ 64 := by
  unfold L.Arena.decCI at h
  cases hp : L.Arena.nat? a p with
  | none => simp [hp] at h
  | some t =>
  simp only [hp, Option.bind_eq_bind, Option.bind_some] at h
  split at h <;> simp only [Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq, reduceCtorEq, exists_false, and_false] at h
  obtain ⟨_, _, _, _, y, hy, _, _, _, _, _, _, _, _, -, h⟩ := h
  simp only [L.Arena.nat?, Option.map_eq_some_iff] at hy
  obtain ⟨w, -, rfl⟩ := hy
  exact w.toNat_lt

theorem mem_mapM_option {α β : Type} {f : α → Option β} : ∀ {l : List α} {l' : List β},
    l.mapM f = some l' → ∀ y ∈ l', ∃ x ∈ l, f x = some y
  | [], l', h, y, hy => by simp at h; subst h; simp at hy
  | x :: xs, l', h, y, hy => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨x, List.mem_cons_self .., hb⟩
    · obtain ⟨z, hz, hz'⟩ := mem_mapM_option hbs y hy
      exact ⟨z, List.mem_cons_of_mem _ hz, hz'⟩

theorem decCIsR_rP {a : Nat → Option Word} {o l : Nat} {block : List IConstantInfo}
    (h : L.Front.decCIsR a o l = some block) :
    ∀ cv mI rP isK rules, IConstantInfo.recInfo cv mI rP isK rules ∈ block → rP < 2 ^ 64 := by
  intro cv mI rP isK rules hm
  unfold L.Front.decCIsR at h
  obtain ⟨j, -, hj⟩ := mem_mapM_option h _ hm
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hj
  obtain ⟨q, -, hq⟩ := hj
  exact decCI_recInfo_rP hq

/-- The program facts `cid_ref` takes beyond `CidProg`: the core's write set and the level cache
(`read_block`'s refinement). -/
structure CidProg2 (p : Prog) : Prop extends CidProg p where
  hcl : CoreStageClosed p
  hL : LvlCacheProg p

section sims
variable {p : Prog}

/-- **`check_ind_decl` refines the `.indDecl` arm of `checkDeclKind`, both outcomes** under
`StageT` and the twin's fold invariant: `ind_params_ok` (con-ron's `indParamsOk_spec`: the state
kept), `read_block` (`readBlock_refinesC` under `StageC`; con-ron's `readBlock_installS`: a
`PStep`), then `check_block` (its contract `BlockRefS`) or the reader's reason (an invalid input:
`RbR`). The memos across `read_block` by its write set (`armMemos_call`). -/
theorem cid_ref (P : CidProg2 p) {G : Prop} {dn : NIdx → Option ConLeche.Name}
    (hbr : BlockRefS G p dn) {fsC : List FnName} (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC)
    {N : Nat} (hN : N ≤ 2 ^ 62 + 1) {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} {o l w : Word} {block : List IConstantInfo} {pins : List INatOpPinSet}
    {env : ConLeche.Env} (hT : StageT dn vis fe m a) (hfold : ConRon.Bridge.FoldOK env fe a)
    (hdec : L.Front.decCIsR (erecP m) o.toNat l.toNat = some block) (hb : o.toNat + l.toNat < 2 ^ 64)
    (hden : ∃ x, Frontend.denoteDecl a.store (.indDecl block w.toNat) = some x) (hM : IndMemos m)
    (hlpd : BlockLpsDn dn block) :
    RefE G (cidE p N m vis o l w) (checkDeclKind V pins fe (.indDecl block w.toNat)) a
      (fun v x a' => CidPost dn m v.1 x v.2 a') := by
  have hS := hT.stage
  have hCM : CoreMemos m := hT.twin.memos
  have hblk : DecB (fun m => decEBlk dn m o.toNat l.toNat) m block := decB_decEBlk_of_decCIs hdec
  obtain ⟨blockP, hbP⟩ : ∃ blockP, Frontend.denoteCIList a.store block = some blockP := by
    obtain ⟨x, hx⟩ := hden
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
    obtain ⟨b, hb, -⟩ := hx
    exact ⟨b, hb⟩
  rcases N with _ | n
  · rw [cidE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [cidE.arm1]
  unfold checkDeclKind
  dsimp only
  -- `ind_params_ok`
  refine RefE.bindLift (fun _ => cidE.k_ind_params_ok.none ..) fun r3 m3 c3 => ?_
  obtain ⟨s3, hs3, -, hm3, hok3, hst3, hres3, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (indParamsOk_refines p P.ps P.ev P.ipo n ⟨m, Locals.init []⟩ a dn vis fe w o l block hS hblk hb)
    (callW_mono c3 (Nat.le_succ n))
  simp only at hm3
  rw [hm3] at hs3
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hst3] at hrun3
  refine ⟨_, _, hrun3, ?_⟩
  refine RefE.ofArms (fun h => cidE.k_ind_params_ok.abort1 (hc1 := h) ..) (fun h => cidE.k_ind_params_ok.arm1 (hc1 := h) ..)
    (RefE.guardThen (by decide) (fun h => by rw [← hres3, h]; rfl) (fun h => by rw [← hres3] at h; simpa using h)
      fun _ _ => ?_)
  -- `read_block`
  have hA : AbsOK m := hT.absOK hM.i1 (L.Stubs.CrOK.crMemo hM.cr)
  have hC : StageC dn vis fe env m a := StageC.of_T hT hfold.check
  refine RefE.bindLift (fun _ => cidE.k_read_block.none ..) fun r4 m4 c4 => ?_
  obtain ⟨s4, hs4, -, hok4, hR4, hS4, hg4⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (readBlock_refinesC p P.hcl P.hL P.parts n ⟨m, Locals.init []⟩ a w o l block hC hA hbP hblk)
    (callW_mono c4 (by omega))
  subst hs4
  have hrun4 := AM.run_of_ok _ _ hok4
  refine ⟨_, _, hrun4, ?_⟩
  generalize AM.res (ConRon.Arena.readBlock w.toNat block) a = x4 at hrun4 hR4 ⊢
  generalize AM.st (ConRon.Arena.readBlock w.toNat block) a = a4 at hrun4 hS4 ⊢
  obtain ⟨hps4, -, hq4⟩ := ConRon.Bridge.Inductives.readBlock_installS hfold.check hbP hrun4
  have hchk4 : ConRon.Bridge.CheckOK false env fe a4 :=
    ⟨hps4.ok, hfold.check.caches.monoF hps4.ext hps4.cframe, hfold.check.pins.mono hps4.ext hps4.pins,
      hfold.check.ienv.mono hps4.ext⟩
  have hf4 := hfC "read_block" (by simp [cidFrameCallees])
  obtain ⟨hIM4, -⟩ := armMemos_call hclC hf4 c4 hM hCM
  have hA4 : AbsOK s4.mem :=
    (CidMemos.call hclC hf4 c4 ⟨hM.stage.pos, hM.stage.ma, hA, hM.stage.ta⟩).2.2.1
  have hC4 : StageC dn vis fe env s4.mem a4 := StageC.of_check hC hS4 hA4 hchk4 hps4.ext
  have hbP4 := ConRon.Bridge.denoteCIList_mono hps4.ext _ _ hbP
  have hblk4 := hblk.grow (decEBlk_mono _ _ _) hg4
  cases x4 with
  | error ce =>
    obtain ⟨hc4, s, rfl⟩ := hR4
    -- the reader's reason: one abort per code, each of class `1`
    by_cases e1 : r4.headD 0 = R_INDUCTIVE_TYPE_DECLARES
    · rw [cidE.k_read_block.abort1 _ _ _ _ _ _ _ hc4.1 e1]
      exact fun _ => ErrClaim.fail_abort _ _ (by rw [twinCls_invalid]; decide)
    by_cases e2 : r4.headD 0 = R_NO_RECURSOR_OF
    · rw [cidE.k_read_block.abort2 _ _ _ _ _ _ _ hc4.1 e1 e2]
      exact fun _ => ErrClaim.fail_abort _ _ (by rw [twinCls_invalid]; decide)
    by_cases e3 : r4.headD 0 = R_THE_ARGUMENT_COUNTS
    · rw [cidE.k_read_block.abort3 _ _ _ _ _ _ _ hc4.1 e1 e2 e3]
      exact fun _ => ErrClaim.fail_abort _ _ (by rw [twinCls_invalid]; decide)
    by_cases e4 : r4.headD 0 = R_INDUCTIVE_TYPE_DECLARES_OTHER
    · rw [cidE.k_read_block.abort4 _ _ _ _ _ _ _ hc4.1 e1 e2 e3 e4]
      exact fun _ => ErrClaim.fail_abort _ _ (by rw [twinCls_invalid]; decide)
    by_cases e5 : r4.headD 0 = R_CONSTRUCTOR_DECLARES_ANOTHER
    · rw [cidE.k_read_block.abort5 _ _ _ _ _ _ _ hc4.1 e1 e2 e3 e4 e5]
      exact fun _ => ErrClaim.fail_abort _ _ (by rw [twinCls_invalid]; decide)
    by_cases e6 : r4.headD 0 = R_CONSTRUCTOR_DECLARES_OTHER
    · rw [cidE.k_read_block.abort6 _ _ _ _ _ _ _ hc4.1 e1 e2 e3 e4 e5 e6]
      exact fun _ => ErrClaim.fail_abort _ _ (by rw [twinCls_invalid]; decide)
    by_cases e7 : r4.headD 0 = R_CONSTRUCTOR_DECLARES_OTHER_UNIVERSE
    · rw [cidE.k_read_block.abort7 _ _ _ _ _ _ _ hc4.1 e1 e2 e3 e4 e5 e6 e7]
      exact fun _ => ErrClaim.fail_abort _ _ (by rw [twinCls_invalid]; decide)
    by_cases e8 : r4.headD 0 = R_INDUCTIVE_BLOCK_ITS
    · rw [cidE.k_read_block.abort8 _ _ _ _ _ _ _ hc4.1 e1 e2 e3 e4 e5 e6 e7 e8]
      exact fun _ => ErrClaim.fail_abort _ _ (by rw [twinCls_invalid]; decide)
    by_cases e9 : r4.headD 0 = R_INDUCTIVE_BLOCK_DECLARES
    · rw [cidE.k_read_block.abort9 _ _ _ _ _ _ _ hc4.1 e1 e2 e3 e4 e5 e6 e7 e8 e9]
      exact fun _ => ErrClaim.fail_abort _ _ (by rw [twinCls_invalid]; decide)
    by_cases e10 : r4.headD 0 = R_INDUCTIVE_BLOCK_CARRIES
    · rw [cidE.k_read_block.abort10 _ _ _ _ _ _ _ hc4.1 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10]
      exact fun _ => ErrClaim.fail_abort _ _ (by rw [twinCls_invalid]; decide)
    rw [cidE.k_read_block.abort11 _ _ _ _ _ _ _ hc4.1 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10]
    exact fun _ => ErrClaim.of_cls0 (by decide)
  | ok bs =>
  obtain ⟨hr41, hq4', hsl4⟩ := hR4
  simp only [ConRon.Bridge.Inductives.ROp] at hq4
  obtain ⟨bsP, hpP, hdP⟩ := hq4
  rw [cidE.k_read_block.arm1 _ _ _ _ _ _ _ hr41]
  dsimp only
  -- TODO(ronsync8-iota): `block_reads_at` (`blockReadsAt_refinesC`), then `check_block` at the
  -- view it gives back, then the verdict
  sorry

/-- **`check_ind_decl` refines the `.indDecl` arm of `checkDeclKind`** under `StageT` and the
twin's fold invariant: the ok half of `cid_ref`, from the call's run. -/
@[refines_part ConRon.Arena.checkDeclKind "the inductive arm (check_ind_decl), under StageT"]
theorem checkIndDecl_refinesC (P : CidProg2 p) {G : Prop} {dn : NIdx → Option ConLeche.Name}
    (hbr : BlockRefS G p dn) {fsC : List FnName} (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC)
    {n : Nat} (hn : n ≤ 2 ^ 62) {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {o l w : Word} {r : List Word} {block : List IConstantInfo}
    {pins : List INatOpPinSet} {env : ConLeche.Env}
    (h : callW p n "check_ind_decl" [vis, o, l, w] m = some (r, m')) (hT : StageT dn vis fe m a)
    (hfold : ConRon.Bridge.FoldOK env fe a)
    (hdec : L.Front.decCIsR (erecP m) o.toNat l.toNat = some block) (hb : o.toNat + l.toNat < 2 ^ 64)
    (hden : ∃ x, Frontend.denoteDecl a.store (.indDecl block w.toNat) = some x) (hM : IndMemos m)
    (hlpd : BlockLpsDn dn block) :
    ∃ fe' a', (checkDeclKind V pins fe (.indDecl block w.toNat)).run a = .ok (fe', a') ∧
      StageR (r.headD 0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m' ∧ IndMemos m' := by
  obtain ⟨s', rfl, -, x, a', hrun, hR⟩ := RefE.run_okW (s₀ := ⟨m, Locals.init []⟩)
    (cidE_spec p P.toCidProg n _ vis o l w)
    (cid_ref P hbr hclC hfC (N := n) (by omega) hT hfold hdec hb hden hM hlpd) h
  exact ⟨x, a', hrun, hR.stage, hR.core, hR.grow, hR.ind⟩

end sims

end L.Ind

end
