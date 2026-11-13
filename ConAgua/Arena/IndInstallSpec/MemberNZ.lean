module

public import ConAgua.Arena.FormerNZRef
public import ConAgua.Arena.IndInstallSpec.CapsProg
public import ConAgua.Arena.IndDecStab
import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.RecClassSpec.CloseLams
import ConAgua.Arena.IndSumSpec.ConsSumCtors
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.WhnfIota
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndRealFvt
import ConAgua.Arena.LdRd

@[expose] public section

/-!
# `member_never_zero` refines `memberNeverZero` (the constructor's family and the caps'
`neverZero`, con-ron's #573)

`member_never_zero(p, mi)` reads member `mi`'s declared former's type through `former_z` (the
heap datum, `FormerNZRef.frzW`) and puts the heap top back. The twin's `formerZ` reads the result
sort back (`readLevelM`), so the refinement runs under `StageR`, the readback cache holding
readbacks (`ReadLCOK`) and the store's sorts read back (`SortsDen`), as `IndRealBle`'s
`blockLargeElimAllowed` does: none of these mentions the environment, so the install's stages carry
them across their pushes.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The store's sorts read back** (`StoreDen.sort`'s half that needs no environment). -/
def SortsDen (a : AState) : Prop :=
  ∀ (h : EIdx) (u : LIdx), a.store.view h = some (.sort u) → ∃ l, denoteL a.store.ls u = some l

/-- The stage relation with the level readback cache replaced (`IndRealBle`'s
`StageR.withReadLC`, which sits above the core's readers). -/
theorem stageR_readLC {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} (hS : StageR vis fe m a)
    (X : Std.HashMap LIdx ConLeche.Level) :
    StageR vis fe m { a with caches := { a.caches with readLC := X } } :=
  ⟨⟨hS.check.arena.caches_irrel _, let ⟨M, hM⟩ := hS.check.core; ⟨M, hM.readLC X⟩, hS.check.pins, hS.check.env,
    hS.check.mode⟩, hS.iw⟩

/-- **`member_never_zero`'s model** (generated): `former_z` lifted. -/
l_model mnzW_spec (p : Prog) (hp : p.lookup "member_never_zero" = some memberNeverZero)
  fns [hp ↦ mnzW list]
  specs [callW_spec p n "former_z"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, ld64_rd_spec]

/-- **`former_z` refines `formerZ` under `StageR`** (`FormerNZRef.frz_ok`'s twin, at the
environment-free invariants): the datum's first word is `0` exactly at `never`; the heap the only
writes; the twin's store kept, its readback cache holding readbacks. -/
theorem frzR_ok {p : Prog} (hpr : p.lookup "pi_result" = some piResultL)
    (hfr : p.lookup "former_res_sort" = some formerResSortL) (hpn : p.lookup "lv_node" = some lvNode)
    (hpp : p.lookup "lh_push" = some lhPush) (hpz : p.lookup "lv_zero" = some lvZero)
    {n : Nat} {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} (hS : StageR vis fe m a)
    (hrl : ReadLCOK a) (hsd : SortsDen a) {ty : Word} (hty : HW ty)
    {cv : IConstantVal} (hcv : cv.type = decE ty) {r : List Word} (h : frzW p n m ty = some (r, m')) :
    ∃ pw a', (ConRon.Arena.formerZ cv).run a = .ok (pw, a') ∧ a'.store = a.store ∧ ReadLCOK a' ∧
      StageR vis fe m' a' ∧ MemFrame [LH] [192] m m' ∧ (r.headD 0 = 0 ↔ pw.isNever = true) := by
  rcases n with _ | n
  · simp [frzW] at h
  rw [frzW.arm1] at h
  rcases hc : callW p n "former_res_sort" [ty] m with _ | ⟨r1, m1⟩
  · rw [hc, frzW.k_former_res_sort.none] at h; cases h
  rw [hc] at h
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (frsV_spec p hfr n ⟨m, Locals.init []⟩ ty) hc
  rw [hs1] at hW1
  obtain ⟨rfl, hrun1, hok1, hv1⟩ := frsV_ok hpr hS.check.arena.base hty hW1
  by_cases h0 : r1.headD 0 = 0
  · rw [frzW.k_former_res_sort.arm1 _ _ _ _ _ h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨.ifAllZero [], a, by
      simp only [ConRon.Arena.formerZ, hcv, StateT.run_bind, hrun1, except_ok_bind, decOS, h0, ↓reduceIte]; rfl,
      rfl, hrl, hS, MemFrame.refl _ _ _, by simp [PropWhen.isNever]⟩
  rw [frzW.k_former_res_sort.arm2 _ _ _ _ _ h0] at h
  obtain ⟨hh, hview⟩ := hv1 h0
  obtain ⟨l, hl⟩ := hsd _ _ hview
  have hu : HW (r1.tail.headD 0) := hok1 h0
  have hlv : LvR (nameN a.store.lss.ls.ns) m1 (r1.tail.headD 0) l := by
    have := denoteL_lvR hS.check.arena.base (decI (r1.tail.headD 0)) l hl
    rwa [decI_word_self _ hu] at this
  rcases hc2 : callW p n "lv_zero" [r1.tail.headD 0] m1 with _ | ⟨r2, m2⟩
  · rw [hc2, frzW.k_lv_zero.none] at h; cases h
  rw [hc2] at h
  obtain ⟨s2, hs2, -, hz2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (lvZero_spec p hpn hpp hpz n ⟨m1, Locals.init []⟩ _) hc2
  rw [hs2] at hz2
  obtain ⟨he, hZ⟩ := zeroW_ok n _ _ _ _ _ hlv hz2
  obtain ⟨X, hX, hXok⟩ := readLevelM_run' a _ l hl hrl
  have hrun : (ConRon.Arena.formerZ cv).run a =
      .ok (Level.zeronessOf l, { a with caches := { a.caches with readLC := X } }) := by
    simp only [ConRon.Arena.formerZ, hcv, StateT.run_bind, hrun1, except_ok_bind, decOS, ite_eq_right h0]
    rw [hX]; rfl
  obtain ⟨hS₂, -⟩ := StageR.frame_hi (stageR_readLC hS X) he.memFrame
    (fun b hb => by simp only [List.mem_singleton] at hb; subst hb; decide)
    (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; decide) (by decide) (by decide)
  rcases hZ with ⟨hx, hpw⟩ | ⟨hx, ps, hpw, -⟩
  · rw [frzW.k_lv_zero.arm1 _ _ _ _ (by rw [hx]; decide)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, hrun, rfl, hXok, hS₂, he.memFrame, by simp [hpw, PropWhen.isNever]⟩
  · rw [frzW.k_lv_zero.arm2 _ _ _ _ hx] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, hrun, rfl, hXok, hS₂, he.memFrame, by simp [hpw, PropWhen.isNever]⟩

/-- A type word of a constant value decoded in the record pool. -/
theorem decCV_typeW {m : Mem} {d : Nat} {cv : IConstantVal} (h : decCV (erecP m) d = some cv) :
    HW (erRd m (UInt64.ofNat d + 3)) ∧ cv.type = decE (erRd m (UInt64.ofNat d + 3)) := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, -, _, -, ty, hty, rfl⟩ := h
  obtain ⟨w, hw, hwl, rfl⟩ := hd?_some hty
  have hl := erecP_lt64 hw
  have e : (UInt64.ofNat d + 3 : Word).toNat = d + 3 := by
    rw [UInt64.toNat_add]; simp; omega
  have := (erRd_of_erecP (a := UInt64.ofNat d + 3) (by rw [e]; exact hw)).1
  rw [this]; exact ⟨hwl, rfl⟩

/-- **`member_never_zero`'s model refines `memberNeverZero`** under `StageR`, `ReadLCOK` and
`SortsDen`: the fact as a word, the heap the only writes (its top put back), the twin's store
kept. -/
theorem mnzW_ok {p : Prog} (P : MnzProg p) {n : Nat} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {pp mi : Word} {r : List Word} {bs : BlockShape}
    (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hS : StageR vis fe m a) (hrl : ReadLCOK a) (hsd : SortsDen a)
    (h : mnzW p n m pp mi = some (r, m')) :
    ∃ a', (ConRon.Arena.memberNeverZero bs mi.toNat).run a = .ok (r.headD 0 != 0, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ a'.store = a.store ∧ ReadLCOK a' := by
  rcases n with _ | n
  · simp [mnzW] at h
  obtain ⟨hq', hq9, -⟩ := partsShapeFacts hq hsrc
  have hkw := partsShapeK hq' hq9
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdm, -⟩ := partsAt decMS_mono hmem
  have hdm' : decPL (truncM m) (decMS (truncM m)) o.toNat l.toNat = some bs.members := hdm
  have hlk : bs.k = l.toNat := decPL_length _ hdm'
  have hkb : bs.k < 2 ^ 64 := by rw [hlk]; exact l.toNat_lt
  obtain ⟨hw0, -, -⟩ := partsIwRd ho (w := pp) rfl
  rw [UInt64.ofNat_toNat] at hw0
  unfold ConRon.Arena.memberNeverZero
  by_cases hmi : bs.k ≤ mi.toNat
  · have hnone : bs.members[mi.toNat]? = none :=
      List.getElem?_eq_none (by unfold BlockShape.k at hmi; omega)
    rw [mnzW.arm1 _ _ _ _ _ (by rw [hkw, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hkb]; exact hmi)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp only [hnone]
    exact ⟨a, rfl, hS, IWGrow.refl _, rfl, hrl⟩
  have hmi' : mi.toNat < bs.k := by omega
  rw [mnzW.arm2 _ _ _ _ _ (by rw [hkw, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hkb]; omega)] at h
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨v, hv, hmsd⟩ := decPL_getH (truncM m) hdm' mi.toNat (by omega)
  generalize hmsh : bs.members[mi.toNat]'(by rw [decPL_length _ hdm']; omega) = msh at hmsd
  have hsome : bs.members[mi.toNat]? = some msh := by rw [← hmsh]; exact List.getElem?_eq_getElem _
  simp only [hsome]
  have hom : (o + mi).toNat = o.toNat + mi.toNat := by
    have := partsIwLt hv; rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hwv, hvb, -⟩ := partsIwRd hv (w := o + mi) hom
  have hv' : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hvb
  obtain ⟨-, ⟨d, hd4, hdecl⟩, -, -⟩ := decMS_some hmsd
  have hv4 : (UInt64.ofNat v + 4 : Word).toNat = v + 4 := by
    have := partsIwLt hd4; rw [UInt64.toNat_add, hv']; simp; omega
  obtain ⟨hwd, -, -⟩ := partsIwRd hd4 (w := UInt64.ofNat v + 4) hv4
  rw [hw0, hwv, hwd] at h
  obtain ⟨hty, hcv⟩ := decCV_typeW (decCVp_truncM hdecl)
  rcases c1 : callW p n "former_z" [erRd m (UInt64.ofNat d + 3)] m with _ | ⟨r1, m1⟩
  · simp only [erRd] at c1; rw [c1, mnzW.k_former_z.none] at h; cases h
  have c1' := c1
  simp only [erRd] at c1'
  rw [c1', mnzW.k_former_z.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (frzW_spec p P.fz n ⟨m, Locals.init []⟩ _) c1
  rw [hs1] at hW1
  obtain ⟨pw, a', hrun, hst, hrl', hS1, hfr, hiff⟩ :=
    frzR_ok P.pr P.fr P.node P.push P.zero hS hrl hsd hty hcv hW1
  obtain ⟨hS2, hg2⟩ := StageR.frame_hi hS1 (MemFrame.setCtl m1 192 (rdW (m.arr64 CTL) 192))
    (fun b hb => by simp at hb) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; decide)
    (by decide) (by decide)
  have hg1 : IWGrow m m1 := IWGrow.of_keep hfr (by decide) (by decide)
  refine ⟨a', ?_, hS2, hg1.trans hg2, hst, hrl'⟩
  simp only [StateT.run_bind, hrun, except_ok_bind, List.headD_cons]
  by_cases h0 : r1.headD 0 = 0
  · rw [ite_eq_left h0]; rw [hiff.mp h0]; rfl
  · rw [ite_eq_right h0]
    have : pw.isNever = false := by
      cases e : pw.isNever
      · rfl
      · exact absurd (hiff.mpr e) h0
    rw [this]; rfl

end L.Ind
