module

public import ConAgua.Arena.JustifyRef6
public import ConAgua.Arena.DeclCheckT
public import ConRon.Bridge.Compare.Cone
public import ConAgua.Arena.JustifySideRefSide
public import ConAgua.Arena.JustifySide
public import ConAgua.Arena.RefWalk
import ConAgua.Arena.StubNamesRefine
import ConAgua.Arena.DeclStepSpec
public import ConAgua.Arena.IndT.Lift
import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Checker.Base
import all ConAgua.Arena.Justify

@[expose] public section

/-!
# The check of one record with a solution (lane compare, helper compare-cone)

`justifiable(i)` refines `justifiable` (`justifiable_ok`); `check_justified(i, vis)` the twin's
`checkJustified` (`cjs_ref`: the axiom arm's ordinary path, `cda_ref`, with the justification
`justify_why` in front); `check_record_sol(i, vis)` the twin's `checkRecord` with a solution
(`crs_ref`, in `cd_ref`'s shape).

**The rejection by the justification**: L rejects a statement the solution does not justify with
`R_NOT_JUSTIFIED_BY`; the twin rejects it with a message that reads names back (the statement's,
the culprit of the cone, `readNameM`), which would fail `.internal` on a name that does not
denote. Every one of them denotes (`justifyWhy_ok`'s run, from the solution's mates denoting,
`CvMatesDen`), so the twin's justification and label run (`JwGuard`) and the rejection is the
twin's.

**The memory the route keeps** (`CrsKeep`): the frames of the route's callees on the step's write
set (`stepA`, `stepC`), the inductive stage's memos and the walks' memory (`WalkMem`) across
them, program facts decided on the concrete program.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)

local notation "V" => ConLeche.CheckMode.verified

/-! ## The program, the guard, the kept memory -/

/-- `check_justified`'s callees through their runs. -/
def crsCalls : List FnName :=
  ["erec_ci", "justify_why", "check_constant_val", "basis_names_ok", "env_push"]

/-- **What the route keeps** (program facts, decided on the concrete program from the write
sets; `Checker/CrsKeepPB.lean`): each callee of `check_justified` is a frame of a step's write
set and keeps the inductive stage's memos; all but the walk (`justify_why`, which re-relates them)
keep the walks' memory, and so does `check_decl`. The models call `check_constant_val` and
`check_decl` through their runs (`callE`): an ok model result is not one of the call (a class-`0`
error leaves a unified model free). -/
structure CrsKeep (p : Prog) : Prop where
  calls : ∀ f ∈ crsCalls, ∀ (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
    callW p n f vs m = some (r, m') →
    MemFrame stepA stepC m m' ∧ (IndMemos m → IndMemos m') ∧ (f ≠ "justify_why" → WalkMem m → WalkMem m')
  cd : ∀ (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
    callW p n "check_decl" vs m = some (r, m') → WalkMem m → WalkMem m'

/-- **What the refinements of this file need of a program.** -/
structure CrsProg (p : Prog) : Prop where
  cone : ConeProg p
  cj : p.lookup "check_justified" = some checkJustifiedL
  crs : p.lookup "check_record_sol" = some checkRecordSolL
  jf : p.lookup "justifiable" = some justifiableL
  ban : p.lookup "builtin_axiom_name" = some builtinAxiomNameL
  ax : AxArmProg p
  bno : L.Ind.BnoProg p
  leaf : LeafClosed p
  keep : CrsKeep p

/-- **The rejection by the justification runs in the twin**: the twin's justification of `cv`
runs from `a`, and so does the record's label after it (the twin's message reads names back). -/
def JwGuard (J : ISolution) (fe : IFEnv) (pd : IDeclaration) (cv : IConstantVal) (a : AState) :
    Prop :=
  ∃ y a₁ l a₂, (justifyWhy J fe cv).run a = .ok (y, a₁) ∧ (declLabel pd).run a₁ = .ok (l, a₂)

/-- **What the route's errors assume of the program**, beside the job's: the constant check's
context, the no-verdict closure of the justification's functions. -/
structure CrsG (p : Prog) : Prop where
  vctx : VerdictCtxU p
  nv : closedNV p jfNvFns = true

theorem solCtl_not' : ∀ x ∈ ([129, 130] : List Word), x ∉ solCtl := by
  intro x hx hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [solCtl, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hx with rfl | rfl <;> rcases hm with h | h | h <;> exact absurd h (by decide)

/-! ## `justifiable` -/

section jf
variable {p : Prog} (P : CrsProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
include P

/-- **`justifiable(i)` refines `justifiable`** of record `i`: the memory and the twin's state kept,
`0` exactly for the twin's `none`, a `some` only at an axiom. -/
@[refines ConRon.Arena.justifiable]
theorem justifiable_ok {n : Nat} {m m' : Mem} {a : AState} {i : Word} {r : List Word}
    {ds : Array IDeclaration} (h : callW p n "justifiable" [i] m = some (r, m'))
    (hT : StageT dn vis fe m a) (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds)
    (hi : i.toNat < ds.size) :
    m' = m ∧ ∃ y, (justifiable ds[i.toNat]).run a = .ok (y, a) ∧ (r.headD 0 = 0 ↔ y = none) ∧
      ∀ cv, y = some cv → ds[i.toNat] = .axiomDecl cv := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (justifiable_specW p P.jf n _ i) h
  have hdecl := hD.recs i.toNat hi
  have h1 := hD.room
  have h2 := hD.dsize
  have hw0 : rdW (m.arr64 DECL) (1 + 8 * i) = L.Front.dw (m.arr64 DECL) i.toNat 0 :=
    rdW_dw _ (by omega) (by decide) (by decide)
  have hw1 : rdW (m.arr64 DECL) (2 + 8 * i) = L.Front.dw (m.arr64 DECL) i.toNat 1 :=
    rdW_dw _ (by omega) (by decide) (by decide)
  rcases n with _ | n
  · rw [justifiableW.eq_1] at hW; cases hW
  by_cases hk : rdW (m.arr64 DECL) (1 + 8 * i) = 1
  · rw [justifiableW.arm2 _ _ _ _ hk] at hW
    rw [hw0] at hk
    generalize hdi : ds[i.toNat] = d at hdecl ⊢
    obtain ⟨cv, rfl⟩ : ∃ cv, d = .axiomDecl cv := by
      cases d <;> simp only [L.Front.DeclAtF, L.Front.DeclAt, L.Front.IndDeclAt] at hdecl <;>
        first | exact ⟨_, rfl⟩ | (exfalso; rw [hdecl.1] at hk; revert hk; decide) |
          (exfalso; exact hdecl)
    obtain ⟨-, hcv⟩ := hdecl
    generalize hnw : rdW (m.arr64 DECL) (2 + 8 * i) &&& 4294967295 = nw at hW
    have hnwl : nw.toNat < 2 ^ 32 := by
      rw [← hnw, UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have hname : decI nw = cv.name := by rw [← hnw, decI_mask, hw1]; exact hcv.1
    -- `builtin_axiom_name`
    cases c1 : callW p n "builtin_axiom_name" [nw] m with
    | none => rw [c1, justifiableW.k_builtin_axiom_name.none] at hW; cases hW
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [c1] at hW
    obtain ⟨s1, rfl, hm1, -, hb1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (builtinAxiomName_refines p P.ban n _ a hT.stage.check.pins nw hnwl) c1
    simp only at hm1 hb1
    subst hm1
    have hj : (justifiable (.axiomDecl cv)).run a =
        (do
          if ← builtinAxiomName cv.name then pure none
          else if ← natOpName cv.name then pure none
          else if (← reduceOpNames).contains cv.name then pure none
          else pure (some cv) : AM (Option IConstantVal)).run a := rfl
    rw [hj, ← hname, StateT.run_bind, hb1, except_ok_bind]
    by_cases e1 : r1.headD 0 ≠ 0
    · rw [justifiableW.k_builtin_axiom_name.arm1 _ _ _ _ _ e1] at hW
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨by rw [← (Prod.mk.inj (Option.some.inj hW)).2], none, ?_, by simp, fun _ h => nomatch h⟩
      simp only [show (r1.headD 0 != 0) = true by simpa using e1, ↓reduceIte]; rfl
    rw [justifiableW.k_builtin_axiom_name.arm2 _ _ _ _ _ (Classical.not_not.mp e1)] at hW
    have e1' : (r1.headD 0 != 0) = false := by simpa using Classical.not_not.mp e1
    rw [e1']
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- `nat_op_name`
    cases c2 : callW p n "nat_op_name" [nw] s1.mem with
    | none => rw [c2, justifiableW.k_nat_op_name.none] at hW; cases hW
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    rw [c2] at hW
    obtain ⟨b2, a2, hrun2, hm2, ha2, hb2⟩ := L.Stubs.natOpName_sim P.cone.nd.nat_op_name
      P.cone.nd.pin_range_has P.cone.nd.pin_at n hT.stage hnwl r2 m2 c2
    subst hm2
    rw [ha2] at hrun2
    rw [StateT.run_bind, hrun2, except_ok_bind]
    by_cases e2 : r2.headD 0 ≠ 0
    · rw [justifiableW.k_nat_op_name.arm1 _ _ _ _ _ e2] at hW
      obtain ⟨rfl, e⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨e.symm, none, ?_, by simp, fun _ h => nomatch h⟩
      rw [hb2.mp e2]; rfl
    rw [justifiableW.k_nat_op_name.arm2 _ _ _ _ _ (Classical.not_not.mp e2)] at hW
    have hb2' : b2 = false := by
      cases hq : b2
      · rfl
      · exact absurd (hb2.mpr hq) e2
    rw [hb2']
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- `pin_at(43)`, `pin_at(44)`
    have hF1 : PinsFull s1.mem a.pins := hT.stage.check.pins.full hT.flag
    cases c3 : callW p n "pin_at" [43] s1.mem with
    | none => rw [c3, justifiableW.k_pin_at.none] at hW; cases hW
    | some x3 =>
    obtain ⟨r3, m3⟩ := x3
    rw [c3, justifiableW.k_pin_at.arm1] at hW
    obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
      (pinAt_specW p P.cone.nd.pin_at n _ 43) c3
    obtain ⟨hm3, hr3, -, -⟩ := pinAtW_ok hW3 hT.stage.check.pins
    have hm3' : m3 = s1.mem := hs3 ▸ hm3
    subst hm3'
    cases c4 : callW p n "pin_at" [44] s1.mem with
    | none => rw [c4, justifiableW.k_pin_at_2.none] at hW; cases hW
    | some x4 =>
    obtain ⟨r4, m4⟩ := x4
    rw [c4] at hW
    obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
      (pinAt_specW p P.cone.nd.pin_at n _ 44) c4
    obtain ⟨hm4, hr4, -, -⟩ := pinAtW_ok hW4 hT.stage.check.pins
    have hm4' : m4 = s1.mem := hs4 ▸ hm4
    subst hm4'
    rw [hr3, hr4] at hW
    simp only [List.headD_cons] at hW
    simp only [StateT.run_bind, reduceOpNames_run hF1, except_ok_bind]
    have hp44 : (pinW s1.mem 44).toNat < 2 ^ 32 := hF1.names_lt 43 (by decide)
    have hp45 : (pinW s1.mem 45).toNat < 2 ^ 32 := hF1.names_lt 44 (by decide)
    have e43 : pinW s1.mem (1 + (43 : Word).toNat) = pinW s1.mem 44 := rfl
    have e44 : pinW s1.mem (1 + (44 : Word).toNat) = pinW s1.mem 45 := rfl
    rw [e43, e44] at hW
    have hcond : (nw = pinW s1.mem 44 ∨ nw = pinW s1.mem 45) ↔
        ((List.range' 44 2).map (fun j => (decI (pinW s1.mem j) : NIdx))).contains (decI nw) = true := by
      simp only [List.range', List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
        Bool.or_false, Bool.or_eq_true, beq_iff_eq, decI_inj_iff hnwl hp44, decI_inj_iff hnwl hp45]
    by_cases e5 : nw = pinW s1.mem 44 ∨ nw = pinW s1.mem 45
    · rw [justifiableW.k_pin_at_2.arm1 _ _ _ _ _ e5] at hW
      obtain ⟨rfl, e⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨e.symm, none, ?_, by simp, fun _ h => nomatch h⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true (hcond.mp e5))]; rfl
    rw [justifiableW.k_pin_at_2.arm2 _ _ _ _ _ e5] at hW
    obtain ⟨rfl, e⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨e.symm, some cv, ?_, by simp, fun _ h => by cases h; rfl⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false (mt hcond.mpr e5))]; rfl
  · rw [justifiableW.arm1 _ _ _ _ hk] at hW
    obtain ⟨rfl, e⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨e.symm, none, ?_, by simp, fun _ h => nomatch h⟩
    rw [hw0] at hk
    generalize hdi : ds[i.toNat] = d at hdecl ⊢
    cases d <;> simp only [justifiable] <;> try rfl
    exact absurd hdecl.1 hk

end jf

/-! ## `check_justified` -/

section cj
variable {pins : List INatOpPinSet} {ds : Array IDeclaration} {p : Prog} (P : CrsProg p)
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
include P

/-- **`check_justified(i, vis)` refines `checkJustified`, both outcomes**, under `StageT`: the
axiom record's constant into `EREC` (`erec_ci(i, 0)`), the justification (`justifyWhy_ok`; its
rejection claimed under `JwGuard`), the constant check (`ccv_ref`, nothing allowed), the reserved
names' check (`bno_sim`, `bne_sim`), the axiom pushed (`push_call`); the job relation, the memos
and the walks' memory after it. -/
@[refines ConRon.Arena.checkJustified]
theorem cjs_ref (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p)
    (hC : CcvSims p dn) {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {i : Word}
    {cv : IConstantVal} {J : ISolution} {envS : ConLeche.Env}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
    (hS : StageT dn vis fe m a) (hR : LoopR pins m a vis fe ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .axiomDecl cv) {c : ConLeche.ConstantVal}
    (hcvd : Frontend.denoteCV a.store cv = some c) (hF : ∃ env, ConRon.Bridge.FoldOK env fe a)
    (hIM : IndMemos m) (hJ : SolR m J)
    (hsol : ConRon.Bridge.IFEnvOK envS (ConRon.Bridge.SolView J) a)
    (hm : ConRon.Bridge.MatesDen a.store J.mates matesU)
    (hcm : ConRon.Bridge.CvMatesDen a.store J.mates) (hWM : WalkMem m)
    (hnx : J.idx.next + 1 < 2 ^ 64) :
    RefE (CrsG p) (checkJustifiedE p n m i vis)
      (checkJustified V J fe (.axiomDecl cv) cv) a
      (fun v x a' => CdPost pins ds m v.1 x v.2 a' ∧ WalkMem v.2) := by
  have hdecl := hR.decls.recs i.toNat hi
  rw [hd] at hdecl
  obtain ⟨-, hcvAt⟩ := hdecl
  obtain ⟨env, hFo⟩ := hF
  have hsden : FindDen a.store J.find? := fun k ci e => by
    rw [ConRon.Bridge.ISolution.find?_view] at e
    obtain ⟨-, c', -, hc', -⟩ := hsol.hit k ci e; exact ⟨c', hc'⟩
  cases n with
  | zero => rw [checkJustifiedE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkJustifiedE.arm1]
  -- `erec_ci(i, 0)`
  refine RefE.onlySim (fun _ => checkJustifiedE.k_erec_ci.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
  rw [checkJustifiedE.k_erec_ci.arm1]
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erecCi_specW p P.ax.rcp n _ i 0) h1
  simp only at hW1
  rw [hs1] at hW1
  obtain ⟨hf1, hI1, hK1⟩ := P.keep.calls "erec_ci" (by decide) n _ m r1 m1 h1
  have hfe1 := erecCiW_frame hW1
  obtain ⟨hT1, hg1, hci1, hcv1⟩ := erecCiW_okAT hW1 hS hR.decls hi hcvAt
  generalize hq0 : r1.headD 0 = q at hci1 hcv1 ⊢
  have hJ1 : SolR m1 J := hJ.growF hfe1 (by decide) solCtl_not' hg1.erecGrow
  have hC1 : ConeT dn vis fe J m1 a := ConeT.of_twin hT1 hFo hsden hJ1
  have hWM1 : WalkMem m1 := hK1 (by decide) hWM
  have hIM1 : IndMemos m1 := hI1 hIM
  have hden1 : ∃ C, Frontend.denoteCI a.store (.axiomInfo cv) = some C :=
    ⟨.axiomInfo c, by simp only [Frontend.denoteCI, hcvd, Option.map_some]⟩
  -- `justify_why(vis, q + CI.cv)`
  rcases c2 : callE p n "justify_why" [vis, q + CI.cv] m1 with e2 | ⟨r2, m2⟩
  · rw [checkJustifiedE.k_justify_why.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (jfNv_mem (by decide)) c2
  have d2 := callW_of_callE c2
  obtain ⟨a2, hC2, hg2, hWM2, h0, hne, hjr⟩ := justifyWhy_ok P.cone d2 hC1 hci1 hden1 hWM1 hnx
  obtain ⟨hf2, hI2, -⟩ := P.keep.calls "justify_why" (by decide) n _ m1 r2 m2 d2
  have hIM2 : IndMemos m2 := hI2 hIM1
  by_cases e2 : r2.headD 0 ≠ 0
  · rw [checkJustifiedE.k_justify_why.abort1 _ _ _ _ _ _ e2]
    intro hG
    obtain ⟨y, a₁, l, a₂, hjw, hdl⟩ : JwGuard J fe (.axiomDecl cv) cv a := by
      obtain ⟨y, a₁, hjw, hx1⟩ := hjr e2 hFo.check hsol hm hcm
      obtain ⟨l, a₂, hdl, -⟩ := msg_ok (g := fun s => s!"axiom {s}") hx1
        (ConRon.Bridge.denoteN_ext (ConRon.Bridge.denoteCV_inv hcvd).1 hx1)
      exact ⟨y, a₁, l, a₂, hjw, by simpa only [declLabel] using hdl⟩
    obtain ⟨why, rfl⟩ := Option.isSome_iff_exists.mp (hne e2 y a₁ hjw)
    refine ErrClaim.bind_right hjw ?_
    refine ErrClaim.bind_right hdl ?_
    exact ErrClaim.fail_abort _ _ (by simp only [twinCls]; decide)
  have e2' : r2.headD 0 = 0 := Classical.not_not.mp e2
  rw [checkJustifiedE.k_justify_why.arm1 _ _ _ _ _ _ e2']
  have hrun2 := h0 e2'
  obtain ⟨hst2, -⟩ := ConRon.Bridge.justifyWhy_run hFo.check hsol hm hcvd hrun2
  refine RefE.bind_right hrun2 ?_
  simp only
  have hFo2 : ConRon.Bridge.FoldOK env fe a2 := hFo.step (hst2.checkOK hFo.check) hst2.pins
  have hcvd2 : Frontend.denoteCV a2.store cv = some c := ConRon.Bridge.denoteCV_ext hcvd hst2.ext
  -- the constant check
  have hcv2 : decCV (erecP m2) (q + CI.cv).toNat = some cv := by
    obtain ⟨w, hw, -⟩ := decCV_name hcv1
    rw [off_add_toNat rfl (by have := erecP_lt64 hw; omega)]
    exact ArrExt.decCV hg2.ext hcv1
  have hcc := ccv_ref P.ax.ccv hq hap hkp hcrf hC hn' hC2.T hcv2 hcvd2 hIM2.cr (allow := 0)
    (allowRd := 0) (allowSorry := 0)
  rw [show ((0 : Word) != 0) = false from rfl] at hcc
  refine RefE.bindRun (s₀ := ⟨m2, Locals.init []⟩)
    (fun _ => checkJustifiedE.k_check_constant_val.none ..)
    (checkConstantVal_specE p P.ax.ccv n _ vis (q + CI.cv) 0 0 0) (fun hG => hG.vctx.nv)
    (fun hG => hG.vctx) hcc fun r3 s3 u3 a3 h3 _ hrun3 hP3 => ?_
  rw [checkJustifiedE.k_check_constant_val.arm1]
  dsimp only at hP3
  generalize s3.mem = m3 at h3 hP3 ⊢
  obtain ⟨hf3, hI3, hK3⟩ :=
    P.keep.calls "check_constant_val" (by decide) n _ m2 r3 m3 (callW_of_callE h3)
  obtain ⟨hstep3, -⟩ := ConRon.Bridge.checkConstantVal_bridge_of_fold
    ConRon.Bridge.CoreSpec.of_core hFo2 hcvd2 hrun3
  have hFo3 := hFo2.ofCore hstep3
  have hT3 := hP3.stage
  have hg3 := hP3.grow
  -- `basis_names_ok(1, name, 0, 0)`
  have hcv3 : decCV (erecP m3) (q + CI.cv).toNat = some cv := ArrExt.decCV hg3.ext hcv2
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCV_name hcv3
  have ex : rdW (m3.arr64 (L.tierA EREC ((q + (CI.cv + CV.name)) >>> 40)))
      (q + (CI.cv + CV.name) &&& 1099511627775) = wn := by
    have := (erRdOK m3).at (q := q + CI.cv) _ (show (CV.name : Word).toNat = 0 from rfl)
      (by simpa using hwn)
    rw [UInt64.add_assoc] at this; exact this
  rw [ex]
  have hA3 : L.Ind.BnoArgs (.axiomDecl cv) 1 wn 0 0 m3 := ⟨rfl, hwnl, hname0.symm⟩
  have hden3 : ∃ x, Frontend.denoteDecl a3.store (.axiomDecl cv) = some x :=
    ⟨_, by simp only [Frontend.denoteDecl, ConRon.Bridge.denoteCV_ext hcvd2 hstep3.ext, Option.map_some]; rfl⟩
  refine RefE.bindSim (fun _ => checkJustifiedE.k_basis_names_ok.none ..)
    (L.Ind.bno_sim P.bno hT3 hFo3.check.state hFo3.check.readOK hFo3.check.pins hA3 hden3)
    fun r4 b4 m4 a4 c4 hrun4 ⟨hT4, hg4, hR4, hb4⟩ => ?_
  obtain ⟨hf4, hI4, hK4⟩ := P.keep.calls "basis_names_ok" (by decide) n _ m3 r4 m4 c4
  by_cases h40 : r4.headD 0 = 0
  · -- the reserved names' failure
    rw [checkJustifiedE.k_basis_names_ok.arm1 _ _ _ _ _ _ h40]
    have hb : b4 = false := by
      cases hq4 : b4
      · rfl
      · exact absurd (hb4.mpr hq4) (by simpa using h40)
    subst hb
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r5 m5 c5 => ?_
    obtain ⟨ce, a5, hrun5, -, -, hcls⟩ := L.Ind.bne_sim P.bno hT4 hR4.ok hR4.read
      (d := .axiomDecl cv) (k := 1) (nw := wn) (bo := 0) (bl := 0) ⟨rfl, hwnl, hname0.symm⟩
      ⟨_, by simp only [Frontend.denoteDecl, ConRon.Bridge.denoteCV_ext hcvd2 (hstep3.ext.trans hR4.ext),
        Option.map_some]; rfl⟩ r5 m5 c5
    refine RefE.bind_right hrun5 ?_
    simp only [checkJustifiedE.k_basis_names_error.eq_2]
    by_cases e1 : r5.headD 0 = R_RESERVED_BASIS_NAME_THE
    · rw [ite_eq_left e1]; exact fun _ => ErrClaim.fail_abort a5 ce (by rw [hcls]; decide)
    rw [ite_eq_right e1]
    by_cases e3 : r5.headD 0 = R_RESERVED_BASIS_NAME_IN
    · rw [ite_eq_left e3]; exact fun _ => ErrClaim.fail_abort a5 ce (by rw [hcls]; decide)
    rw [ite_eq_right e3]; exact fun _ => ErrClaim.fail_abort a5 ce (by rw [hcls]; decide)
  -- passed: the push
  rw [checkJustifiedE.k_basis_names_ok.arm2 _ _ _ _ _ _ h40]
  have hb : b4 = true := hb4.mp h40
  subst hb
  simp only [↓reduceIte]
  refine RefE.onlySim (fun _ => checkJustifiedE.k_env_push.none ..) (fun _ _ h => h) fun r5 m5 c5 => ?_
  rw [checkJustifiedE.k_env_push.arm1]
  obtain ⟨hf5, hI5, hK5⟩ := P.keep.calls "env_push" (by decide) n _ m4 r5 m5 c5
  have hci4 : decCI (erecP m4) q.toNat = some (.axiomInfo cv) :=
    ArrExt.decCI (hg2.trans (hg3.trans hg4)).ext hci1
  obtain ⟨hS5, hg5⟩ := push_call P.ax.rcp c5 hT4.stage hci4
  have hgrow : IWGrow m m5 := hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5)))
  have hfr : MemFrame stepA stepC m m5 := hf1.trans (hf2.trans (hf3.trans (hf4.trans hf5)))
  refine RefE.ret rfl ⟨⟨hR.of_step hS5 hfr hgrow.ext,
    leaf_memos P.leaf (leaf_mem _ rfl) c5 hT4.twin.memos, hI5 (hI4 (hI3 hIM2)), hgrow⟩,
    hK5 (by decide) (hK4 (by decide) (hK3 (by decide) hWM2))⟩

end cj

/-! ## `check_record_sol` -/

section crs
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
  {p : Prog} (P : CrsProg p)
include P

/-- **`check_record_sol(i, vis)` refines `checkRecord` with a solution, both outcomes**, under
`StageT`, in `cd_ref`'s shape: `justifiable` (`justifiable_ok`), then the record's own check
(`cd_ref`) or the justification route (`cjs_ref`); the walks' memory kept. -/
@[refines ConRon.Arena.checkRecord]
theorem crs_ref (hP : CdProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
    (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p)
    (hC : CcvSims p dn)
    {N : Nat} (hN : N ≤ 2 ^ 62 + 1) {m : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {i : Word} (hi : i.toNat < ds.size) (hok : ConRon.Bridge.StateOK a)
    (hR : LoopR pins m a vis fe ds) (hS : StageT dn vis fe m a)
    (hF : ∃ env, ConRon.Bridge.FoldOK env fe a)
    (hden : ∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x)
    (hPD : ∃ pinsP, ConRon.Bridge.PinsDenote a.store pins pinsP) (hIM : IndMemos m)
    {J : ISolution} {envS : ConLeche.Env} {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
    (hJ : SolR m J) (hsol : ConRon.Bridge.IFEnvOK envS (ConRon.Bridge.SolView J) a)
    (hm : ConRon.Bridge.MatesDen a.store J.mates matesU)
    (hcm : ConRon.Bridge.CvMatesDen a.store J.mates) (hWM : WalkMem m)
    (hnx : J.idx.next + 1 < 2 ^ 64) :
    RefE (CdG pins dn ds p ∧ CrsG p) (checkRecordSolE p N m i vis)
      (checkRecord V pins (some J) fe (dsAt ds i)) a
      (fun v x a' => CdPost pins ds m v.1 x v.2 a' ∧ WalkMem v.2) := by
  have hds : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  rcases N with _ | n
  · rw [checkRecordSolE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [checkRecordSolE.arm1]
  have hrec : checkRecord V pins (some J) fe (dsAt ds i) =
      (do
        match ← justifiable (dsAt ds i) with
        | none => checkDecl V pins fe (dsAt ds i)
        | some cv => checkJustified V J fe (dsAt ds i) cv : AM IFEnv) := rfl
  rw [hrec]
  rcases c1 : callE p n "justifiable" [i] m with e1 | ⟨r1, m1⟩
  · rw [checkRecordSolE.k_justifiable.none]
    exact fun hG => ErrClaim.of_callE_nv hG.2.nv (jfNv_mem (by decide)) c1
  obtain ⟨rfl, y, hy, hr, hax⟩ := justifiable_ok P (callW_of_callE c1) hS hR.decls hi
  rw [← hds] at hy hax
  refine RefE.bind_right hy ?_
  by_cases e1 : r1.headD 0 = 0
  · rw [checkRecordSolE.k_justifiable.arm1 _ _ _ _ _ _ e1, hr.mp e1]
    have hcd := cd_ref hP hFD hLD (N := n) (by omega) hi hok hR hS hF hden hPD hIM
    have hs := checkDecl_specE p hP.cd.cd hP.cd.ckd n ⟨m1, Locals.init []⟩ i vis
    rcases c : callE p n "check_decl" [i, vis] m1 with e | ⟨r, m'⟩
    · rw [checkRecordSolE.k_check_decl.none]
      exact fun hG => RefE.run_err hs hG.2.vctx.nv hG.1 hcd c
    rw [checkRecordSolE.k_check_decl.arm1]
    obtain ⟨s', rfl, -, y', a', hrun, hpost⟩ := RefE.run_ok hs hcd c
    exact ⟨y', a', hrun, hpost, P.keep.cd n _ m1 r s'.mem (callW_of_callE c) hWM⟩
  rw [checkRecordSolE.k_justifiable.arm2 _ _ _ _ _ _ e1]
  obtain ⟨cv, rfl⟩ := Option.ne_none_iff_exists'.mp (fun h => e1 (hr.mpr h))
  have hd := hax cv rfl
  have hd' : ds[i.toNat] = .axiomDecl cv := by rw [← hds]; exact hd
  obtain ⟨x, hx⟩ := hden
  rw [hd] at hx
  simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
  obtain ⟨c, hc, -⟩ := hx
  rw [hd]
  exact RefE.weakenG (fun hG => hG.2)
    (cjs_ref P hq hap hkp hcrf hC (by omega) hS hR hi hd' hc hF hIM hJ hsol hm hcm hWM hnx)

end crs

end L.Arena
