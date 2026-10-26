import ConAgua.Arena.RecCheckSpec11
import ConAgua.Arena.IndT.Lift
import ConRon.Bridge.Inductives.RecCheck
import ConAgua.Census.Attr

/-!
# `targetParamsDefEq` under `StageC` (lane `indstaget`, helper `pds`)

`target_params_def_eq`'s model at `realCall p`, from `StageC` and the inputs' denotations con-ron's
`targetParamsDefEq_spec` asks, its twin side transcribed from that spec's proof: the closedness
reads (`RC.closed4_bind_run`), the canon forms (`targetCanonParams_spec`, a `PSpecP`), the member
abstraction (`targetAbs_spec`, a `PSpec`), then the knot (`inferC_rsim`, `isDefEqC_rsim`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Frames -/

/-- Across a core call: the stage memos stand (`coreStageA_stage`). -/
theorem MFr.ofCore {p : Prog} (hcl : CoreStageClosed p) {f : FnName} (hf : f ∈ stageCoreFns)
    {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word} (h : callW p n f vs m = some (r, m')) :
    MFr [] [] m m' :=
  MFr.of_frame (run_memFrame hcl hf (run_of_callW h)).1 coreStageA_stage coreStageC_stage

theorem tcpF_afr {n : Nat} {m m' : Mem} {pfo pfl e : Word} {r : List Word}
    (h : tcpF n m pfo pfl e = some (r, m')) : AFr m m' := by
  obtain _ | n := n
  · simp [tcpF] at h
  simp only [tcpF, tcpW, tcpK1.eq_def, eftK2.eq_def] at h
  afr_auto h [recW_afr, rxW_afr]

theorem taGoW_afr (n : Nat) :
    (∀ (m m' : Mem) (no nl lvls ho hl f h r : Word), taGoW n m no nl lvls ho hl f h = some (r, m') →
      AFr m m') ∧
    (∀ (m m' : Mem) (no nl lvls ho hl f1 g x y z r : Word),
      taNodeW n m no nl lvls ho hl f1 g x y z = some (r, m') → AFr m m') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ _ h => by simp [taGoW] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [taNodeW] at h⟩
  | succ j =>
  have ihG : ∀ (m m' : Mem) (no nl lvls ho hl f h r : Word), taGoW j m no nl lvls ho hl f h = some (r, m') →
      AFr m m' := (ih j (by omega)).1
  refine ⟨?_, ?_⟩
  · intro m m' no nl lvls ho hl f h r hg
    by_cases hf : f = 0
    · rw [taGoW_abort (hf := hf)] at hg; simp at hg
    rw [taGoW_view (hf := hf)] at hg
    unfold taG1 at hg
    split at hg; · simp at hg
    split at hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact AFr.refl _
    split at hg
    · rw [taCW_same hg]; exact AFr.refl _
    unfold taG3 at hg
    split at hg; · simp at hg
    split at hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact AFr.refl _
    cases hn : taNodeW j m no nl lvls ho hl (f - 1) _ _ _ _ with
    | none => rw [hn] at hg; simp [taG4] at hg
    | some pr =>
      obtain ⟨rn, m1⟩ := pr
      rw [hn, taG4_some] at hg
      rcases hs : msetG taSch m1 h 0 rn with _ | m2 <;> simp only [hs, taG5, reduceCtorEq] at hg
      simp only [Option.some.injEq, Prod.mk.injEq] at hg
      rw [← hg.2]
      cases j with
      | zero => simp [taNodeW] at hn
      | succ i =>
        exact ((ih (i + 1) (by omega)).2 _ _ _ _ _ _ _ _ _ _ _ _ _ hn).trans
          (AFr.of_frame (msetG_frame taSch taSch_wf m1 m2 h 0 rn hs))
  · intro m m' no nl lvls ho hl f1 g x y z r hn
    unfold taNodeW at hn
    split at hn
    · rcases h1 : taGoW j m no nl lvls ho hl f1 x with _ | ⟨a2, m1⟩ <;> simp only [h1, taB1, reduceCtorEq] at hn
      rcases h2 : taGoW j m1 no nl lvls ho hl f1 y with _ | ⟨x2, m2⟩ <;> simp only [h2, taB2, reduceCtorEq] at hn
      exact ((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans (rpMkW_afr hn)
    split at hn
    · rcases h1 : taGoW j m no nl lvls ho hl f1 x with _ | ⟨a2, m1⟩ <;> simp only [h1, taL1, reduceCtorEq] at hn
      rcases h2 : taGoW j m1 no nl lvls ho hl f1 y with _ | ⟨x2, m2⟩ <;> simp only [h2, taL2, reduceCtorEq] at hn
      rcases h3 : taGoW j m2 no nl lvls ho hl f1 z with _ | ⟨c2, m3⟩ <;> simp only [h3, taL3, reduceCtorEq] at hn
      exact (((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans
        (ihG _ _ _ _ _ _ _ _ _ _ h3)).trans (rpMkW_afr hn)
    · rcases h1 : taGoW j m no nl lvls ho hl f1 z with _ | ⟨a2, m1⟩ <;> simp only [h1, taP1, reduceCtorEq] at hn
      exact (ihG _ _ _ _ _ _ _ _ _ _ h1).trans (rpMkW_afr hn)

theorem taF_afr {n : Nat} {m m' : Mem} {no nl lvls ho hl e r : Word}
    (h : taF n m no nl lvls ho hl e = some (r, m')) : AFr m m' := by
  obtain _ | n := n
  · simp [taF] at h
  simp only [taF] at h
  by_cases h0 : rdW (m.arr64 CTL) taSch.cs + 2 = 0
  · simp [taAW, h0] at h
  rw [taAW_eq n m no nl lvls ho hl e h0] at h
  exact (AFr.of_frame (mclearG_frame taSch m)).trans ((taGoW_afr n).1 _ _ _ _ _ _ _ _ _ _ h)

/-! ## The closedness reads -/

/-- con-ron's `RC.closed4_bind_run` at `tpClosed`. -/
theorem tpClosed_pstep {pfvs : List EIdx} {a b : EIdx} {aP bP : ConLeche.Expr} {s₀ s' : AState}
    {c : Bool} (hok : ConRon.Bridge.StateOK s₀) (ha : denoteE s₀.store a = some aP)
    (hb : denoteE s₀.store b = some bP)
    (hrun : (tpClosed pfvs a b).run s₀ = .ok (c, s')) :
    PStep s₀ s' ∧ c = (aP.bvarB == 0 && bP.bvarB == 0 && decide (aP.fvarB ≤ pfvs.length) &&
      decide (bP.fvarB ≤ pfvs.length)) := by
  have hrun' : (tpClosed pfvs a b) s₀ = .ok (c, s') := hrun
  obtain ⟨s1, p1, z1⟩ := ConRon.Bridge.Inductives.RC.closed4_bind_run (k := pure) (n := pfvs.length)
    hok ha hb (by simpa only [tpClosed, pure_bind, bind_pure] using hrun')
  obtain ⟨rfl, rfl⟩ := ConRon.Bridge.AM.pure_ok z1
  exact ⟨p1, rfl⟩

/-! ## The rest of the head step under `StageC` -/

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`tpRest` under `StageC`** (twin side: con-ron's `targetParamsDefEq_spec`, the `cons` arm
after the closedness test). -/
theorem pdsR_okC (n : Nat) (hn : n ≤ 2 ^ 62) {m m' : Mem} {a : AState}
    {d no nl lvls ho hl pfo pfl x y : Word} {r : List Word} {names : List NIdx}
    {holes pfvs : List EIdx}
    (h : pdsK5 (realCall p) n vis d no nl lvls ho hl pfo pfl y (tcpF n m pfo pfl x) = some (r, m'))
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hx : H x) (hy : H y) (hlv : H lvls)
    (hno : decHL m no.toNat nl.toNat = some names) (hnob : no.toNat + nl.toNat ≤ iwTop m)
    (hho : decHL m ho.toNat hl.toNat = some holes) (hhob : ho.toNat + hl.toNat ≤ iwTop m)
    (hpf : HSl0 m pfo pfl pfvs) (hP : RcMR m)
    {namesP : List ConLeche.Name} {lvlsP : List ConLeche.Level} {holesP pfvsP : List ConLeche.Expr}
    {xP yP : ConLeche.Expr}
    (hTA : TAArgs names (decI lvls) holes namesP lvlsP holesP a.store)
    (hpfP : Frontend.denoteEList a.store pfvs = some pfvsP)
    (hxP : denoteE a.store (decE x) = some xP) (hyP : denoteE a.store (decE y) = some yP)
    (habs : ∀ e, ConLeche.Expr.WScoped d.toNat e →
      ConLeche.Expr.WScoped d.toNat (ConLeche.targetAbs namesP lvlsP holesP e))
    (hpw : ∀ z ∈ pfvsP, ConLeche.Expr.WScoped d.toNat z)
    (hfx : xP.fvarB ≤ pfvsP.length) (hfy : yP.fvarB ≤ pfvsP.length) :
    ∃ c a', (tpRest fe d.toNat names (decI lvls) holes pfvs (decE x) (decE y)).run a = .ok (c, a') ∧
      (r.headD 0 != 0) = c ∧ StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ RcMR m' ∧ AbsOK m' ∧
      CoreStep V env fe a a' := by
  have hwx : ConLeche.Expr.WScoped d.toNat (ConLeche.targetAbs namesP lvlsP holesP
      (ConLeche.targetCanonParams pfvsP xP)) :=
    habs _ (ConLeche.targetCanonParams_WScoped hpw xP
      (ConLeche.Expr.fvarsBelow_iff.mpr (ConLeche.Expr.fvarB_eq xP ▸ hfx)))
  have hwy : ConLeche.Expr.WScoped d.toNat (ConLeche.targetAbs namesP lvlsP holesP
      (ConLeche.targetCanonParams pfvsP yP)) :=
    habs _ (ConLeche.targetCanonParams_WScoped hpw yP
      (ConLeche.Expr.fvarsBelow_iff.mpr (ConLeche.Expr.fvarB_eq yP ▸ hfy)))
  -- the canon form of `x`
  rcases h5 : tcpF n m pfo pfl x with _ | ⟨r5, m5⟩ <;> simp only [h5, pdsK5, reduceCtorEq] at h
  obtain ⟨a5, run5, hH5, hS5, hg5, hP5⟩ := tcpF_ok dn fe vis n h5 hC.stage hpf hx hP
  have hA5 := tcpF_afr h5 hA
  obtain ⟨q5, hR5⟩ := ConRon.Bridge.Inductives.targetCanonParams_spec pfvs pfvsP (decE x) xP a a5 _
    hC.check.state hC.check.pins ⟨hpfP, hxP⟩ run5
  have hC5 := hC.of_pstep hS5 hA5 q5
  -- its abstraction
  rcases h6 : taF n m5 no nl lvls ho hl (r5.headD 0) with _ | ⟨av, m6⟩ <;> rw [h6] at h
  · cases h
  obtain ⟨a6, run6, hS6, hg6, hP6⟩ := taF_ok dn fe vis n h6 hS5 hH5 hlv
    (by rw [decHL_grow hg5 hnob]; exact hno) (by have := hg5.1; omega)
    (by rw [decHL_grow hg5 hhob]; exact hho) (by have := hg5.1; omega) hP5
  have hA6 := taF_afr h6 hA5
  obtain ⟨q6, hR6⟩ := ConRon.Bridge.Inductives.targetAbs_spec names (decI lvls) holes namesP lvlsP
    holesP (decE (r5.headD 0)) _ a5 a6 _ hC5.check.state ⟨hTA.ext q5.ext, hR5⟩ run6
  have hC6 := hC5.of_pstep hS6 hA6 q6
  by_cases hb6 : 4294967296 ≤ av
  · rw [pdsK6_big (h := hb6)] at h; cases h
  rw [pdsK6_ok (h := hb6)] at h
  have hav : H av := by simp only [H]; rw [UInt64.le_iff_toNat_le] at hb6; simp at hb6; omega
  have hg56 := hg5.trans hg6
  have q56 := q5.trans q6
  -- the canon form of `y`
  rcases h7 : tcpF n m6 pfo pfl y with _ | ⟨r7, m7⟩ <;> simp only [h7, pdsK7, reduceCtorEq] at h
  obtain ⟨a7, run7, hH7, hS7, hg7, hP7⟩ := tcpF_ok dn fe vis n h7 hS6 (hpf.grow hg56) hy hP6
  have hA7 := tcpF_afr h7 hA6
  obtain ⟨q7, hR7⟩ := ConRon.Bridge.Inductives.targetCanonParams_spec pfvs pfvsP (decE y) yP a6 a7 _
    hC6.check.state hC6.check.pins ⟨denoteEList_ext q56.ext _ _ hpfP, denote_ext hyP q56.ext⟩ run7
  have hC7 := hC6.of_pstep hS7 hA7 q7
  have hg57 := hg56.trans hg7
  -- its abstraction
  rcases h8 : taF n m7 no nl lvls ho hl (r7.headD 0) with _ | ⟨bv, m8⟩ <;> rw [h8] at h
  · cases h
  obtain ⟨a8, run8, hS8, hg8, hP8⟩ := taF_ok dn fe vis n h8 hS7 hH7 hlv
    (by rw [decHL_grow hg57 hnob]; exact hno) (by have := hg57.1; omega)
    (by rw [decHL_grow hg57 hhob]; exact hho) (by have := hg57.1; omega) hP7
  have hA8 := taF_afr h8 hA7
  obtain ⟨q8, hR8⟩ := ConRon.Bridge.Inductives.targetAbs_spec names (decI lvls) holes namesP lvlsP
    holesP (decE (r7.headD 0)) _ a7 a8 _ hC7.check.state ⟨hTA.ext (q56.trans q7).ext, hR7⟩ run8
  have hC8 := hC7.of_pstep hS8 hA8 q8
  have q58 := (q56.trans q7).trans q8
  have hg58 := hg57.trans hg8
  have hR6' := denote_ext hR6 (q7.trans q8).ext
  by_cases hb8 : 4294967296 ≤ bv
  · rw [pdsK8_big (h := hb8)] at h; cases h
  have hbv : H bv := by simp only [H]; rw [UInt64.le_iff_toNat_le] at hb8; simp at hb8; omega
  by_cases he : av = bv
  · rw [pdsK8_eq (h := hb8) (he := he)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨true, a8, ?_, rfl, hC8, hg58, hP8, hA8, q58.toCore hC.check⟩
    subst he
    simp only [tpRest, StateT.run_bind, run5, except_ok_bind, run6, run7, run8, beq_self_eq_true,
      if_true]
    rfl
  rw [pdsK8_ne (h := hb8) (he := he)] at h
  have hne : (decE av == decE bv) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => he (decE_inj av bv hav hbv e)
  -- the knot
  rcases h9 : realCall p n "infer_type_core" [vis, d, av] m8 with _ | ⟨r9, m9⟩ <;> simp only [h9, pdsK9, reduceCtorEq] at h
  obtain ⟨t9, a9, run9, hC9, hg9, -, hA9, c9, -⟩ :=
    inferC_rsim hq henv n hn hC8 hA8 d av hav hR6' hwx _ h9
  rcases h10 : realCall p n "infer_type_core" [vis, d, bv] m9 with _ | ⟨r10, m10⟩ <;> simp only [h10, pdsK10, reduceCtorEq] at h
  obtain ⟨t10, a10, run10, hC10, hg10, -, hA10, c10, -⟩ :=
    inferC_rsim hq henv n hn hC9 hA9 d bv hbv (denote_ext hR8 c9.ext) hwy _ h10
  rcases h11 : realCall p n "is_def_eq_core" [vis, d, av, bv] m10 with _ | ⟨r11, m11⟩ <;> simp only [h11, pdsK11, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨c, a11, run11, hC11, hg11, hd11, hA11, c11⟩ :=
    isDefEqC_rsim hq henv n hn hC10 hA10 d av bv hav hbv (denote_ext hR6' (c9.trans c10).ext)
      (denote_ext hR8 (c9.trans c10).ext) hwx hwy _ h11
  refine ⟨c, a11, ?_, by simpa [decBool] using hd11, hC11, ((hg58.trans hg9).trans hg10).trans hg11,
    ((hP8.fr (MFr.ofCore hq.closed (by decide) h9)).fr (MFr.ofCore hq.closed (by decide) h10)).fr
      (MFr.ofCore hq.closed (by decide) h11), hA11,
    (((q58.toCore hC.check).trans c9).trans c10).trans c11⟩
  simp only [← decE_eq] at run9 run10 run11
  simp only [tpRest, StateT.run_bind, run5, except_ok_bind, run6, run7, run8, hne, Bool.false_eq_true,
    if_false, run9, run10, run11]

include hq henv in
/-- **The head step under `StageC`**: the closedness reads (`tpClosed_pstep`), then `pdsR_okC`. -/
theorem pdsW_okC (n : Nat) (hn : n ≤ 2 ^ 62) {m m' : Mem} {a : AState}
    {d no nl lvls ho hl pfo pfl x y : Word} {r : List Word} {names : List NIdx}
    {holes pfvs : List EIdx}
    (h : pdsW (realCall p) n m vis d no nl lvls ho hl pfo pfl x y = some (r, m'))
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hx : H x) (hy : H y) (hlv : H lvls)
    (hno : decHL m no.toNat nl.toNat = some names) (hnob : no.toNat + nl.toNat ≤ iwTop m)
    (hho : decHL m ho.toNat hl.toNat = some holes) (hhob : ho.toNat + hl.toNat ≤ iwTop m)
    (hpf : HSl0 m pfo pfl pfvs) (hP : RcMR m)
    {namesP : List ConLeche.Name} {lvlsP : List ConLeche.Level} {holesP pfvsP : List ConLeche.Expr}
    {xP yP : ConLeche.Expr}
    (hTA : TAArgs names (decI lvls) holes namesP lvlsP holesP a.store)
    (hpfP : Frontend.denoteEList a.store pfvs = some pfvsP)
    (hxP : denoteE a.store (decE x) = some xP) (hyP : denoteE a.store (decE y) = some yP)
    (habs : ∀ e, ConLeche.Expr.WScoped d.toNat e →
      ConLeche.Expr.WScoped d.toNat (ConLeche.targetAbs namesP lvlsP holesP e))
    (hpw : ∀ z ∈ pfvsP, ConLeche.Expr.WScoped d.toNat z) :
    ∃ c a', (tpStep fe d.toNat names (decI lvls) holes pfvs (decE x) (decE y)).run a = .ok (c, a') ∧
      (r.headD 0 != 0) = c ∧ StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ RcMR m' ∧ AbsOK m' ∧
      CoreStep V env fe a a' := by
  have hlen := ConRon.Bridge.Inductives.denoteEList_length hpfP
  rcases pdsC_ok dn fe vis n h hC.stage hx hy hpf.len hP with
    ⟨a', run, rfl, hS', hg, hP', hF⟩ | ⟨m4, a4, run, h4, hS4, hg4, hP4, hF4⟩
  · obtain ⟨q, -⟩ := tpClosed_pstep hC.check.state hxP hyP run
    refine ⟨false, a', ?_, rfl, hC.of_pstep hS' (hF hA) q, hg, hP', hF hA, q.toCore hC.check⟩
    simp only [tpStep, StateT.run_bind, run, except_ok_bind, Bool.not_false, if_true]; rfl
  · obtain ⟨q, hc⟩ := tpClosed_pstep hC.check.state hxP hyP run
    have hc' := hc.symm
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc'
    obtain ⟨⟨⟨-, -⟩, hfx⟩, hfy⟩ := hc'
    rw [hlen] at hfx hfy
    have hC4 := hC.of_pstep hS4 (hF4 hA) q
    obtain ⟨c, a', run', hc, hC', hg, hP', hA', cs⟩ := pdsR_okC hq henv n hn h4 hC4 (hF4 hA) hx hy hlv
      (by rw [decHL_grow hg4 hnob]; exact hno) (by have := hg4.1; omega)
      (by rw [decHL_grow hg4 hhob]; exact hho) (by have := hg4.1; omega)
      (hpf.grow hg4) hP4 (hTA.ext q.ext) (denoteEList_ext q.ext _ _ hpfP) (denote_ext hxP q.ext)
      (denote_ext hyP q.ext) habs hpw hfx hfy
    refine ⟨c, a', ?_, hc, hC', hg4.trans hg, hP', hA', (q.toCore hC.check).trans cs⟩
    simp only [tpStep, StateT.run_bind, run, except_ok_bind, Bool.not_true, Bool.false_eq_true, if_false]
    exact run'

include hq henv in
/-- **`target_params_def_eq` under `StageC`** (twin side: con-ron's `targetParamsDefEq_spec`'s list
induction). -/
theorem pdeW_okC (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ {m m' : Mem} {a : AState} {d no nl lvls ho hl pfo pfl ao al bo bl : Word}
    {r : List Word} {names : List NIdx} {holes pfvs as bs : List EIdx}
    {namesP : List ConLeche.Name} {lvlsP : List ConLeche.Level}
    {holesP pfvsP asP bsP : List ConLeche.Expr},
    pdeW (realCall p) n m vis d no nl lvls ho hl pfo pfl ao al bo bl = some (r, m') →
    StageC dn vis fe env m a → AbsOK m → H lvls →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat ≤ iwTop m →
    decHL m ho.toNat hl.toNat = some holes → ho.toNat + hl.toNat ≤ iwTop m →
    HSl0 m pfo pfl pfvs → HSl0 m ao al as → HSl0 m bo bl bs → RcMR m →
    TAArgs names (decI lvls) holes namesP lvlsP holesP a.store →
    Frontend.denoteEList a.store pfvs = some pfvsP →
    Frontend.denoteEList a.store as = some asP → Frontend.denoteEList a.store bs = some bsP →
    (∀ e, ConLeche.Expr.WScoped d.toNat e →
      ConLeche.Expr.WScoped d.toNat (ConLeche.targetAbs namesP lvlsP holesP e)) →
    (∀ z ∈ pfvsP, ConLeche.Expr.WScoped d.toNat z) →
    ∃ c a', (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs).run a =
      .ok (c, a') ∧ (r.headD 0 != 0) = c ∧ StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ RcMR m' ∧
      AbsOK m' := by
  induction n with
  | zero =>
    intro m m' a d no nl lvls ho hl pfo pfl ao al bo bl r names holes pfvs as bs namesP lvlsP
      holesP pfvsP asP bsP h
    simp [pdeW] at h
  | succ n ih =>
  intro m m' a d no nl lvls ho hl pfo pfl ao al bo bl r names holes pfvs as bs namesP lvlsP holesP
    pfvsP asP bsP h hC hA hlv hno hnob hho hhob hpf has hbs hP hTA hpfP hasP hbsP habs hpw
  have hS := hC.stage
  have hlt : ∀ {x : Nat}, x ≤ iwTop m → x < 2 ^ 64 := fun h => hS.lt64 h
  by_cases hal : al = 0
  · rw [pdeW_nil (h := hal)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hal
    have : as = [] := by have := has.len; simpa using this
    subst this
    refine ⟨bs.isEmpty, a, by rw [tpd_nil]; rfl, ?_, hC, IWGrow.refl _, hP, hA⟩
    have hbl : bs.length = bl.toNat := hbs.len
    by_cases hb0 : bl = 0
    · subst hb0; have : bs = [] := by simpa using hbl
      subst this; simp
    · have : bs ≠ [] := fun e => hb0 (UInt64.toNat_inj.mp (by rw [← hbl, e]; rfl))
      simp [hb0, this]
  by_cases hbl : bl = 0
  · rw [pdeW_nilr (h := hal) (hb := hbl)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hbl
    have : bs = [] := by have := hbs.len; simpa using this
    subst this
    have hasb : ao.toNat + al.toNat ≤ iwTop m := has.2.resolve_left hal
    obtain ⟨w, as', rfl, -, -, -⟩ := decHL_cons has.1 hal (hlt hasb)
    exact ⟨false, a, by rw [tpd_nilr]; rfl, rfl, hC, IWGrow.refl _, hP, hA⟩
  rw [pdeW_cons (h := hal) (hb := hbl)] at h
  have hasb : ao.toNat + al.toNat ≤ iwTop m := has.2.resolve_left hal
  have hbsb : bo.toNat + bl.toNat ≤ iwTop m := hbs.2.resolve_left hbl
  obtain ⟨x, as', rfl, ex, hx, has'⟩ := decHL_cons has.1 hal (hlt hasb)
  obtain ⟨y, bs', rfl, ey, hy, hbs'⟩ := decHL_cons hbs.1 hbl (hlt hbsb)
  obtain ⟨xP, asP', hxP, hasP', rfl⟩ := ConRon.Bridge.denoteEList_cons_inv hasP
  obtain ⟨yP, bsP', hyP, hbsP', rfl⟩ := ConRon.Bridge.denoteEList_cons_inv hbsP
  rw [ex, ey] at h
  obtain ⟨ea1, el1, hal0⟩ := slice_step hal (hlt hasb)
  obtain ⟨eb1, ebl1, hbl0⟩ := slice_step hbl (hlt hbsb)
  cases n with
  | zero => simp [pdsF, pdeK1] at h
  | succ k =>
  cases h1 : pdsW (realCall p) k m vis d no nl lvls ho hl pfo pfl x y with
  | none => simp only [pdsF] at h; rw [h1] at h; simp [pdeK1] at h
  | some p1 =>
  obtain ⟨r1, m1⟩ := p1
  simp only [pdsF] at h; rw [h1] at h
  obtain ⟨c, a1, run1, hc, hC1, hg1, hP1, hA1, cs1⟩ :=
    pdsW_okC hq henv k (by omega) h1 hC hA hx hy hlv hno hnob hho hhob hpf hP hTA hpfP hxP hyP habs hpw
  by_cases hr1 : r1.headD 0 = 0
  · rw [pdeK1_stop (h := hr1)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have : c = false := by rw [← hc, hr1]; rfl
    subst this
    refine ⟨false, a1, ?_, rfl, hC1, hg1, hP1, hA1⟩
    rw [tpd_cons]; simp only [StateT.run_bind, ← decE_eq, run1, except_ok_bind, Bool.false_eq_true, if_false]; rfl
  rw [pdeK1_go (h := hr1)] at h
  have : c = true := by rw [← hc]; simpa using hr1
  subst this
  rcases h2 : pdeW (realCall p) (k + 1) m1 vis d no nl lvls ho hl pfo pfl (ao + 1) (al - 1) (bo + 1) (bl - 1) with _ | ⟨r2, m2⟩ <;> simp only [h2, pdsK11, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hgo := hg1.1
  obtain ⟨c2, a2, run2, hc2, hC2, hg2, hP2, hA2⟩ := ih (by omega) h2 hC1 hA1 hlv
    (by rw [decHL_grow hg1 hnob]; exact hno) (by omega)
    (by rw [decHL_grow hg1 hhob]; exact hho) (by omega)
    (hpf.grow hg1)
    (HSl0.of (by rw [decHL_grow hg1 (by rw [ea1, el1]; omega)]; exact has') (by rw [ea1, el1]; omega))
    (HSl0.of (by rw [decHL_grow hg1 (by rw [eb1, ebl1]; omega)]; exact hbs') (by rw [eb1, ebl1]; omega)) hP1
    (hTA.ext cs1.ext) (denoteEList_ext cs1.ext _ _ hpfP) (denoteEList_ext cs1.ext _ _ hasP')
    (denoteEList_ext cs1.ext _ _ hbsP') habs hpw
  refine ⟨c2, a2, ?_, by simpa using hc2, hC2, hg1.trans hg2, hP2, hA2⟩
  rw [tpd_cons]; simp only [StateT.run_bind, ← decE_eq, run1, except_ok_bind, if_true]; exact run2

include hq henv in
/-- **`target_params_def_eq` refines `targetParamsDefEq`** under `StageC` (the knot's core calls;
the inputs' denotations and scoping as con-ron's `targetParamsDefEq_spec` asks). -/
@[refines ConRon.Arena.targetParamsDefEq]
theorem targetParamsDefEq_refinesC (L : TpLook p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (d no nl lvls ho hl pfo pfl ao al bo bl : Word)
    (names : List NIdx) (holes pfvs as bs : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem) (hlv : H lvls)
    (hno : decHL s₀.mem no.toNat nl.toNat = some names) (hnob : no.toNat + nl.toNat ≤ iwTop s₀.mem)
    (hho : decHL s₀.mem ho.toNat hl.toNat = some holes) (hhob : ho.toNat + hl.toNat ≤ iwTop s₀.mem)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (has : HSl0 s₀.mem ao al as) (hbs : HSl0 s₀.mem bo bl bs)
    (hP : RcMR s₀.mem)
    {namesP : List ConLeche.Name} {lvlsP : List ConLeche.Level}
    {holesP pfvsP asP bsP : List ConLeche.Expr}
    (hTA : TAArgs names (decI lvls) holes namesP lvlsP holesP a₀.store)
    (hpfP : Frontend.denoteEList a₀.store pfvs = some pfvsP)
    (hasP : Frontend.denoteEList a₀.store as = some asP)
    (hbsP : Frontend.denoteEList a₀.store bs = some bsP)
    (habs : ∀ e, ConLeche.Expr.WScoped d.toNat e →
      ConLeche.Expr.WScoped d.toNat (ConLeche.targetAbs namesP lvlsP holesP e))
    (hpw : ∀ z ∈ pfvsP, ConLeche.Expr.WScoped d.toNat z) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_params_def_eq"
      [vis, d, no, nl, lvls, ho, hl, pfo, pfl, ao, al, bo, bl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs) a₀ ∧
      (r.headD 0 != 0) =
        AM.res (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (tpd_spec p L (realCall p) (realCall_spec p) n s₀ vis d no nl lvls ho hl pfo pfl
    ao al bo bl) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨c, a', run, hc, hC', hg, hP', hA'⟩ := pdeW_okC hq henv n hn hm hC hA hlv hno hnob hho hhob
    hpf has hbs hP hTA hpfP hasP hbsP habs hpw
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres]; exact hc, by rw [hst]; exact hC', hg, hP', hA'⟩

end sims

end L.Ind
