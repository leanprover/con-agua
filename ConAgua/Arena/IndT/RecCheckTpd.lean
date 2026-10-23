import ConAgua.Arena.RecCheckSpec11
import ConAgua.Arena.IndT.Lift
import ConRon.Bridge.Inductives.RecCheck

/-!
# `targetParamsDefEq` under `StageC` (lane `indstaget`, helper `pds`)

`target_params_def_eq`'s model at `realCall p`, from `StageC` and the inputs' denotations con-ron's
`targetParamsDefEq_spec` asks, its twin side transcribed from that spec's proof: the closedness
reads (`RC.closed4_bind_run`), the canon forms (`targetCanonParams_spec`, a `PSpecP`), the member
abstraction (`targetAbs_spec`, a `PSpec`), then the knot (`inferC_rsim`, `isDefEqC_rsim`).
-/

set_option linter.deprecated false

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
  cases n with
  | zero => simp [tcpF] at h
  | succ n =>
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
      cases hs : msetG taSch m1 h 0 rn with
      | none => rw [hs] at hg; simp [taG5] at hg
      | some m2 =>
        rw [hs, taG5_some] at hg
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
    · cases h1 : taGoW j m no nl lvls ho hl f1 x with
      | none => rw [h1] at hn; simp [taB1] at hn
      | some p1 =>
        obtain ⟨a2, m1⟩ := p1
        rw [h1, taB1_some] at hn
        cases h2 : taGoW j m1 no nl lvls ho hl f1 y with
        | none => rw [h2] at hn; simp [taB2] at hn
        | some p2 =>
          obtain ⟨x2, m2⟩ := p2
          rw [h2, taB2_some] at hn
          exact ((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans (rpMkW_afr hn)
    split at hn
    · cases h1 : taGoW j m no nl lvls ho hl f1 x with
      | none => rw [h1] at hn; simp [taL1] at hn
      | some p1 =>
        obtain ⟨a2, m1⟩ := p1
        rw [h1, taL1_some] at hn
        cases h2 : taGoW j m1 no nl lvls ho hl f1 y with
        | none => rw [h2] at hn; simp [taL2] at hn
        | some p2 =>
          obtain ⟨x2, m2⟩ := p2
          rw [h2, taL2_some] at hn
          cases h3 : taGoW j m2 no nl lvls ho hl f1 z with
          | none => rw [h3] at hn; simp [taL3] at hn
          | some p3 =>
            obtain ⟨c2, m3⟩ := p3
            rw [h3, taL3_some] at hn
            exact (((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans
              (ihG _ _ _ _ _ _ _ _ _ _ h3)).trans (rpMkW_afr hn)
    · cases h1 : taGoW j m no nl lvls ho hl f1 z with
      | none => rw [h1] at hn; simp [taP1] at hn
      | some p1 =>
        obtain ⟨a2, m1⟩ := p1
        rw [h1, taP1_some] at hn
        exact (ihG _ _ _ _ _ _ _ _ _ _ h1).trans (rpMkW_afr hn)

theorem taF_afr {n : Nat} {m m' : Mem} {no nl lvls ho hl e r : Word}
    (h : taF n m no nl lvls ho hl e = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [taF] at h
  | succ n =>
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
  cases h5 : tcpF n m pfo pfl x with
  | none => rw [h5] at h; cases h
  | some p5 =>
  obtain ⟨r5, m5⟩ := p5
  rw [h5, pdsK5_some] at h
  obtain ⟨a5, run5, hH5, hS5, hg5, hP5⟩ := tcpF_ok dn fe vis n h5 hC.stage hpf hx hP
  have hA5 := tcpF_afr h5 hA
  obtain ⟨q5, hR5⟩ := ConRon.Bridge.Inductives.targetCanonParams_spec pfvs pfvsP (decE x) xP a a5 _
    hC.check.state hC.check.pins ⟨hpfP, hxP⟩ run5
  have hC5 := hC.of_pstep hS5 hA5 q5
  -- its abstraction
  cases h6 : taF n m5 no nl lvls ho hl (r5.headD 0) with
  | none => rw [h6] at h; cases h
  | some p6 =>
  obtain ⟨av, m6⟩ := p6
  rw [h6] at h
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
  cases h7 : tcpF n m6 pfo pfl y with
  | none => rw [h7] at h; cases h
  | some p7 =>
  obtain ⟨r7, m7⟩ := p7
  rw [h7, pdsK7_some] at h
  obtain ⟨a7, run7, hH7, hS7, hg7, hP7⟩ := tcpF_ok dn fe vis n h7 hS6 (hpf.grow hg56) hy hP6
  have hA7 := tcpF_afr h7 hA6
  obtain ⟨q7, hR7⟩ := ConRon.Bridge.Inductives.targetCanonParams_spec pfvs pfvsP (decE y) yP a6 a7 _
    hC6.check.state hC6.check.pins ⟨denoteEList_ext q56.ext _ _ hpfP, denote_ext hyP q56.ext⟩ run7
  have hC7 := hC6.of_pstep hS7 hA7 q7
  have hg57 := hg56.trans hg7
  -- its abstraction
  cases h8 : taF n m7 no nl lvls ho hl (r7.headD 0) with
  | none => rw [h8] at h; cases h
  | some p8 =>
  obtain ⟨bv, m8⟩ := p8
  rw [h8] at h
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
  cases h9 : realCall p n "infer_type_core" [vis, d, av] m8 with
  | none => rw [h9] at h; cases h
  | some p9 =>
  obtain ⟨r9, m9⟩ := p9
  rw [h9, pdsK9_some] at h
  obtain ⟨t9, a9, run9, hC9, hg9, -, hA9, c9, -⟩ :=
    inferC_rsim hq henv n hn hC8 hA8 d av hav hR6' hwx _ h9
  cases h10 : realCall p n "infer_type_core" [vis, d, bv] m9 with
  | none => rw [h10] at h; cases h
  | some p10 =>
  obtain ⟨r10, m10⟩ := p10
  rw [h10, pdsK10_some] at h
  obtain ⟨t10, a10, run10, hC10, hg10, -, hA10, c10, -⟩ :=
    inferC_rsim hq henv n hn hC9 hA9 d bv hbv (denote_ext hR8 c9.ext) hwy _ h10
  cases h11 : realCall p n "is_def_eq_core" [vis, d, av, bv] m10 with
  | none => rw [h11] at h; cases h
  | some p11 =>
  obtain ⟨r11, m11⟩ := p11
  rw [h11, pdsK11_some] at h
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

end sims

end L.Ind
