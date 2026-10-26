import ConAgua.Arena.IndT.PosWalk
import ConAgua.Arena.IlpRdReal

/-!
# `nest_ctors_crest` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`p2ctW_ok`'s proof (`IndPos2SpecM`) at `realCall p`, its twin side transcribed from con-ron's
`nestCtors_spec` (the cons case's head): the level instantiation (`instLPFast_cstep`), the crest
(`nestCrest_spec`, well scoped by `WScoped_nestCrest`), its type (`inferC_rsim`) and that type's
sort (`ensureSortC_rsim`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A core entry point keeps the stage's memos (`coreStageA`/`coreStageC` miss 201‥208). -/
theorem coreF_mfr {p : Prog} (hq : KnotStageProg p) {f : FnName} (hf : f ∈ stageCoreFns) {n : Nat}
    {args r : List Word} {m m' : Mem} (h : realCall p n f args m = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (run_memFrame hq.closed hf (run_of_callW h)).1 coreStageA_stage coreStageC_stage

section crest
variable {p : Prog} (hq : KnotStageProg p) (hIlpf : IlpfF p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
  (fe : IFEnv) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq hIlpf henv in
/-- **`nest_ctors_crest` under `StageC`**: `p2ctW_ok` with `StageC`, con-ron's preconditions of the
constructor's head (`nestCtors_spec`'s), and after: `StageC`, the `CoreStep`, the crest denoting a
term well scoped at the frame's depth. -/
theorem p2ctW_okC {k : Nat} (hn : k ≤ 2 ^ 62) {m m' : Mem} {a : AState}
    {no nl us dO dL hO hL cv hi : Word} {names : List NIdx}
    {ds holes : List EIdx} {cvv : IConstantVal} {r : List Word}
    (h : p2ctW (realCall p) k m vis no nl us dO dL hO hL cv hi = some (r, m')) (hC : StageC dn vis fe env m a)
    (hus : H us) (hdec : decHL m no.toNat nl.toNat = some names) (hit : no.toNat + nl.toNat ≤ iwTop m)
    (hnn : dL.toNat + names.length < 2 ^ 64)
    (hds : decHL m dO.toNat dL.toNat = some ds) (hdsb : dO.toNat + dL.toNat ≤ iwTop m)
    (hho : decHL m hO.toNat hL.toNat = some holes) (hhob : hO.toNat + hL.toNat ≤ iwTop m)
    (hcv : decCVp m cv.toNat = some cvv) (hcv3 : cv.toNat + 3 < 2 ^ 64) (hP : PosMR m) (hA : AbsOK m)
    {usP : List ConLeche.Level} {dsP : List ConLeche.Expr} {namesP : List ConLeche.Name}
    {holesP : List ConLeche.Expr} {cvP : ConLeche.ConstantVal}
    (hpre : CtorsPre a.store (decI us) ds names holes hi.toNat usP dsP namesP holesP)
    (hcvP : Frontend.denoteCV a.store cvv = some cvP) (hcl : cvP.type.hasFvar = false) :
    ∃ cty a1 crest a2 ty a3 so a4, nameNodup cvv.levelParams = true ∧
      (instLPFast coreWalkFuel cvv.levelParams (decI us) cvv.type).run a = .ok (cty, a1) ∧
      (ConRon.Arena.nestCrest names (decI us) ds holes cty).run a1 = .ok (some crest, a2) ∧
      (inferTypeCore .verified fe checkFuel hi.toNat crest).run a2 = .ok (ty, a3) ∧
      (ensureSortCore .verified fe checkFuel hi.toNat ty).run a3 = .ok (so, a4) ∧
      StageC dn vis fe env m' a4 ∧ IWGrow m m' ∧ H (r.headD 0) ∧ decI (r.headD 0) = crest ∧ PosMR m' ∧
      AbsOK m' ∧ ConRon.Bridge.CoreStep V env fe a a4 ∧
      ∃ crestP, denoteE a4.store crest = some crestP ∧ ConLeche.Expr.WScoped hi.toNat crestP := by
  have hS := hC.stage
  cases k with
  | zero => simp [p2ctW] at h
  | succ k =>
  simp only [p2ctW] at h
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hcvn, hcvl, hcvt⟩ := ConRon.Bridge.Core.denoteCV_inv hcvP
  -- the level parameters
  rcases hlp : cvLpsW k m cv with _ | ⟨r1, m1⟩ <;> rw [hlp] at h; · simp [p2ctK1] at h
  rw [p2ctK1_eq] at h
  obtain ⟨hS1, hg1, hE1, hdec1, ht1⟩ := pos2_cvLpsW_stage hlp hS hcv hcv3
  have hA1 : AbsOK m1 := erToIwW_afr (show erToIwW _ m _ _ = some (r1, m1) from hlp) hA
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨ws, hws, hwsd, hwH⟩ := slR_of_decHL m1 _ _ _ hdec1 (by omega)
  simp only [UInt64.ofNat_toNat] at hws
  rcases hnd : nodupW k m1 (r1.headD 0) (r1.tail.headD 0) with _ | b <;> rw [hnd] at h; · cases h
  simp only at h
  by_cases hb0 : b = 0
  · rw [if_pos hb0] at h; cases h
  rw [if_neg hb0] at h
  have hnod : nameNodup cvv.levelParams = true := by
    have := nodupW_ok k m1 _ _ b ws hws hnd
    rw [hwsd, nameNodup_map ws hwH]
    by_cases hn : ws.Nodup
    · simp [hn]
    · rw [if_neg hn] at this; exact absurd this hb0
  -- the instantiated type
  obtain ⟨-, -, hty⟩ := decCV_some hcv
  obtain ⟨wt, hwt, hwtH, hwtd⟩ := hd?_some hty
  have e3 : (cv + 3).toNat = cv.toNat + 3 := word_add_toNat (by simp; omega)
  have hrdt : rdW (m1.arr64 EREC) (cv + 3) = wt := by
    rw [hE1]; simp only [erA] at hwt; simp [rdW, e3, hwt]
  rw [hrdt] at h
  rcases hil : realCall p k "inst_lp_fast" [CWF, r1.headD 0, r1.tail.headD 0, us, wt] m1 with _ | ⟨r2, m2⟩ <;> rw [hil] at h; · simp [p2ctK2] at h
  rw [p2ctK2_some] at h
  obtain ⟨cty, a1, hrun1, ⟨hS2, hg2, hcH, hcd⟩, ⟨A2, C2, hA2s, hC2s, hfr2⟩, hAF2⟩ :=
    IlpRd.realC hIlpf hC k CWF _ _ _ _ cvv.levelParams m1 m2 a r2 hus hwtH ⟨rfl, erToIwW_iwFr hlp⟩ hS1 hdec1 hil
  rw [CWF_eq, ← hwtd] at hrun1
  have hA2 : AbsOK m2 := hAF2 hA1
  obtain ⟨c1, hctyP⟩ := ConRon.Bridge.Inductives.instLPFast_cstep hC.check hcvl hpre.hus hcvt hrun1
  have hC2 : StageC dn vis fe env m2 a1 := hC.of_cstep hS2 hA2 c1
  -- the crest
  have hg12 := hg1.trans hg2
  cases k with
  | zero => simp [pcrWf, p2ctK3] at h
  | succ k =>
  cases k with
  | zero => simp [pcrWf, p2ctK3] at h
  | succ k =>
  cases k with
  | zero => simp [pcrWf, p2ctK3] at h
  | succ k =>
  simp only [pcrWf] at h
  rcases hpc : pcrW k m2 no nl us dO dL hO hL (r2.headD 0) with _ | ⟨r3, m3⟩ <;> rw [hpc] at h; · simp [p2ctK3] at h
  rw [p2ctK3_eq] at h
  have hP2 : PosMR m2 := (hP.fr (posmemo_cvLpsW_mfr hlp)).fr (MFr.of_frame hfr2 hA2s hC2s)
  obtain ⟨M, G, g, hR⟩ := hP2.rf
  obtain ⟨mp2, hM2⟩ := hP2.rp
  obtain ⟨x, a2, hrun2, hx, ⟨M', G', hS3, hg3, hR3, -⟩, hM3⟩ := pcrW_ok dn fe vis k m2 m3 a1 no nl us dO dL hO hL
    (r2.headD 0) r3 names ds holes M G g hpc hS2 hcH hus
    (by rw [decHL_agree (RdS.of_grow hg12) (fun j hj => by omega)]; exact hdec) (by omega)
    (by have := hg12.1; omega) hnn mp2 hM2
    (by rw [decHL_agree (RdS.of_grow hg12) (fun j hj => by omega)]; exact hds) (by have := hg12.1; omega)
    (by rw [decHL_agree (RdS.of_grow hg12) (fun j hj => by omega)]; exact hho) (by have := hg12.1; omega) hR
  rw [hcd] at hrun2
  have hA3 : AbsOK m3 := pcrW_afr hpc hA2
  obtain ⟨p2, ho⟩ := ConRon.Bridge.Inductives.nestCrest_spec names namesP (decI us) usP ds dsP holes holesP cty _
    a1 a2 x hC2.check.state hC2.check.pins
    ⟨ConRon.Bridge.denoteNListE_ext c1.ext _ _ hpre.hnames, ConRon.Bridge.denoteLs_ext hpre.hus c1.ext,
      ConRon.Bridge.denoteEList_ext c1.ext _ _ hpre.hds, ConRon.Bridge.denoteEList_ext c1.ext _ _ hpre.hholes,
      hctyP⟩ hrun2
  cases x with
  | none => simp only [decOE] at hx; rw [if_pos hx] at h; cases h
  | some crest =>
  obtain ⟨hx1, hxH, hxd⟩ := hx
  rw [if_neg (by rw [hx1]; decide)] at h
  obtain ⟨crestP, hcrestP, hcrest⟩ := ho
  have hwc : ConLeche.Expr.WScoped hi.toNat crestP :=
    ConLeche.WScoped_nestCrest (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hcl) hpre.hlen
      (fun y hy => (List.mem_append.mp hy).elim (hpre.wds y) (hpre.wholes y)) hcrestP
  have hP3 : PosMR m3 := hP2.setCr (pcrW_mfr hpc) hM3 ⟨M', G', g, hR3⟩
  have hC3 : StageC dn vis fe env m3 a2 := hC2.of_pstep hS3 hA3 p2
  have hxH' : H (r3.tail.headD 0) := by simpa using hxH
  have hxd' : decI (r3.tail.headD 0) = crest := by simpa [decE_eq] using hxd
  -- its type
  rcases hit2 : realCall p (k + 1 + 1 + 1) "infer_type_core" [vis, hi, r3.tail.headD 0] m3 with _ | ⟨r4, m4⟩ <;> rw [hit2] at h; · simp [p2ctK4] at h
  rw [p2ctK4_eq] at h
  obtain ⟨ty, a3, hrun3, hC4, hg4, hdec4, hA4, c4, tyP, htyP, hwty⟩ :=
    inferC_rsim hq henv (k + 1 + 1 + 1) (by omega) hC3 hA3 hi (r3.tail.headD 0) hxH'
      (by rw [hxd']; exact hcrest) hwc _ hit2
  obtain ⟨htyH, htyd⟩ := hdec4
  rw [hxd'] at hrun3
  have hP4 : PosMR m4 := hP3.fr (coreF_mfr hq (by decide) hit2)
  -- its sort
  rcases hes : realCall p (k + 1 + 1 + 1) "ensure_sort_core" [vis, hi, r4.headD 0] m4 with _ | ⟨r5, m5⟩ <;> rw [hes] at h; · cases h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨so, a4, hrun4, hC5, hg5, -, hA5, c5, -⟩ :=
    ensureSortC_rsim hq henv (k + 1 + 1 + 1) (by omega) hC4 hA4 hi (r4.headD 0) htyH
      (by rw [htyd]; exact htyP) hwty _ hes
  rw [htyd] at hrun4
  exact ⟨cty, a1, crest, a2, ty, a3, so, a4, hnod, hrun1, hrun2, hrun3, hrun4, hC5,
    ((hg12.trans hg3).trans hg4).trans hg5, by simpa using hxH', by simpa using hxd',
    hP4.fr (coreF_mfr hq (by decide) hes), hA5,
    ((c1.trans (p2.toCore hC2.check)).trans c4).trans c5,
    crestP, ConRon.Bridge.denote_ext hcrest (c4.ext.trans c5.ext), hwc⟩

end crest

end L.Ind
