import ConAgua.Arena.RecGenSpec19
import ConAgua.Arena.IndT.RecCheckPins
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.RecClassSpecI
import ConAgua.Arena.IndSumSpec4
import ConAgua.Arena.IndInstallSpec23
import ConRon.Bridge.Inductives.GenRec

/-!
# `classMajors` under `StageC` (lane `indstaget`, helper `indstaget-tpt`)

`class_majors`' model at `realCall p` (its `target_major_pins` through `tmpW_okC`), from `StageC`,
`AbsOK` and the inputs' denotations con-ron's `classMajors_spec` asks, the twin side transcribed
from that spec's proof: the key's intern (`internConstE_run`), `mkAppN` (`mkAppN_run`),
`targetMajorOf` (`targetMajorOf_spec`, a `CoreStep`), `targetMajorPins` (`targetMajorPins_spec`).

`AbsOK` across `target_major_of` (`tmfW_afr`): the walk memos' frames of its model's callees
(`inst_lp_fast`, which writes the `instLP` memos 52‥54, through its stub's `stub_afr`).
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `AbsOK` across `target_major_of` -/

theorem nameCopyW_afr : ∀ (n : Nat) (m m' : Mem) (d s l : Word), nameCopyW n m d s l = some m' →
    AFr m m'
  | 0, _, _, _, _, _, h => by simp [nameCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [nameCopyW_nil n m d s l hl] at h; cases h; exact AFr.refl _
    · rw [nameCopyW_step n m d s l hl] at h
      exact (set64IW_afr _ _ _).trans (nameCopyW_afr n _ _ _ _ _ h)

theorem memberNamesW_afr {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : memberNamesW n m p = some (r, m')) : AFr m m' := by
  unfold memberNamesW at h
  split at h; · cases h
  rename_i q m1 hal
  split at h; · cases h
  rename_i m2 hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (allocW_afr hal).trans (nameCopyW_afr _ _ _ _ _ _ hc)

theorem ckc2W_afr : ∀ (n : Nat) (m m' : Mem) (nP o l : Word) (r : List Word),
    ckc2W n m nP o l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [ckc2W] at h
  | n + 1, m, m', nP, o, l, r, h => by
    by_cases hl : l = 0
    · rw [ckc2W_nil n m nP o l hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ckc2W_cons n m nP o l hl] at h
    cases h1 : bvbW n m (rdW (m.arr64 IW) o) CWF with
    | none => rw [h1] at h; simp [ckc2K1] at h
    | some p1 =>
    obtain ⟨rb, m1⟩ := p1
    rw [h1] at h
    refine (bvbW_afr h1).trans ?_
    by_cases hb : rb ≠ 0
    · rw [ckc2K1_open (h := hb)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ckc2K1_closed (h := hb)] at h
    cases h2 : fvbF m1 [CWF, rdW (m.arr64 IW) o] with
    | none => rw [h2] at h; simp [ckc2K2] at h
    | some p2 =>
    obtain ⟨rf, m2⟩ := p2
    rw [h2] at h
    refine (fvbF_afr h2).trans ?_
    by_cases hf : nP < rf.headD 0
    · rw [ckc2K2_open (h := hf)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ckc2K2_closed (h := hf)] at h
    cases h3 : ckc2W n m2 nP (o + 1) (l - 1) with
    | none => rw [h3] at h; simp [ckcK3] at h
    | some p3 =>
    obtain ⟨r3, m3⟩ := p3
    rw [h3, ckcK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact ckc2W_afr n _ _ _ _ _ _ h3

theorem toiW_afr {N : Nat} {m m' : Mem} {vis I us dso dsl : Word} {r : List Word}
    (h : toiW N m vis I us dso dsl = some (r, m')) : AFr m m' := by
  cases N with
  | zero => simp [toiW] at h
  | succ N =>
  rw [toiW_eq] at h
  unfold toiK1 toiK2 toiK3 toiK4 toiK5 at h
  afr_auto h [envFindW_afr, erToIwW_afr, stub_afr, instW_afr _ _ _ _ _ _ _, piBW_afr _ _ _ _ _ _]

section calls
variable {p : Prog} {n : Nat} {m m' : Mem} {r : List Word}

theorem gaaC_afr (hP : AdF p) {args : List Word}
    (h : callW p n "get_app_args_f" args m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (gaaF_spec p hP n _ args) h
  exact gaaF_afr hW

theorem gafC_afr (hP : AdF p) {args : List Word}
    (h : callW p n "get_app_fn_f" args m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (gafF_spec p hP n _ args) h
  exact gafF_afr hW

theorem evC_afr (hP : p.lookup "e_view" = some eView) {w : Word}
    (h : callW p n "e_view" [w] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, he, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (eView_spec p hP n _ w) h
  rw [he]; exact AFr.refl _

theorem bsmnC_afr (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hp : p.lookup "block_shape_member_names" = some blockShapeMemberNames) {q : Word}
    (h : callW p n "block_shape_member_names" [q] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_spec p ha hc hp n _ q) h
  exact memberNamesW_afr hW

theorem findC_afr (hp : p.lookup "sl_find" = some slFind) {o l x : Word}
    (h : callW p n "sl_find" [o, l, x] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hm, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (slFind_spec p hp n _ o l x) h
  rw [hm]; exact AFr.refl _

theorem tmmC_afr (hP : TmmProg p) {pp cao cal pfo pfl fvo fvl ao al I us t : Word}
    (h : callW p n "target_major_of_member" [pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, I, us, t] m =
      some (r, m')) : AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (tmm_spec p hP.mem k _ pp cao cal pfo pfl fvo fvl ao al I us t) h
  unfold tmmW at hW
  split at hW; · cases hW
  split at hW; · cases hW
  unfold tmmK1 tmmK2 tmmK3 tmmK4 at hW
  split at hW; · cases hW
  rename_i r1 m1 h1
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeLps_spec p hP.alloc hP.erCopy hP.erToIw hP.lps k _ pp) h1
  refine (lpsW_afr hW1).trans ?_
  split at hW; · cases hW
  rename_i r2 m2 h2
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (plW_spec p hP.alloc hP.copy hP.cons hP.get hP.pfind hP.ppush hP.iparam hP.plgo hP.pl hP.il k _ _ _) h2
  refine (plW_afr hW2).trans ?_
  split at hW; · cases hW
  rename_i r3 m3 h3
  obtain ⟨s3, rfl, -, hm3, -⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (slEq_spec p hP.eq k _ ao _ fvo _) h3
  simp only at hm3
  rw [← hm3]
  split at hW; · cases hW
  split at hW; · cases hW
  split at hW; · cases hW
  rename_i r4 m4 h4
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  rw [← hW.2]
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (mkTargetMajor_spec p hP.alloc hP.mkTm k _ _ _ _ _ _ _ _ _ _ _ _ _ _) h4
  exact mkTMW_afr hW4

theorem pinC_afr (hp : p.lookup "pin_at" = some pinAtL) {i : Word}
    (h : callW p n "pin_at" [i] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Arena.pinAt_specW p hp n _ i) h
  unfold L.Arena.pinAtW at hW
  split at hW; · cases hW
  split at hW; · cases hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  rw [← hW.2]; exact AFr.refl _

theorem tcoC_afr (hl : NtLook p) (hp : p.lookup "target_ctors_of" = some targetCtorsOf) {vis I : Word}
    (h : callW p n "target_ctors_of" [vis, I] m = some (r, m')) : AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (tco_spec p hl hp k _ vis I) h
  unfold tcoPK at hW
  split at hW; · cases hW
  rename_i r1 m1 h1
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  rw [← hW.2]; exact ntWf_afr h1

theorem tmocC_afr (hb : BvbProg p) (hf : HfF p)
    (hp : p.lookup "target_major_of_outside_closed" = some targetMajorOfOutsideClosed) {o l nP : Word}
    (h : callW p n "target_major_of_outside_closed" [o, l, nP] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (tmoc_spec p hb hf hp n _ o l nP) h
  exact ckc2W_afr _ _ _ _ _ _ _ hW

theorem noC_afr (hN : NoProg p) {no nl lo hi e : Word}
    (h : callW p n "nest_occ" [no, nl, lo, hi, e] m = some (r, m')) : AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (nestOcc_spec p hN.hv hN.hc hN.hf hN.hput hN.hgo hN.hnode hN.hcl hN.hp k _ no nl lo hi e) h
  exact noConstWf_afr (n := k + 1) hW

theorem ocW_afr (hN : NoProg p) : ∀ (n : Nat) (m m' : Mem) (no nl o l : Word) (r : List Word),
    ocW p n m no nl o l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, h => by simp [ocW] at h
  | n + 1, m, m', no, nl, o, l, r, h => by
    by_cases hl : l = 0
    · rw [ocW_nil p n m no nl o l hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ocW_cons p n m no nl o l hl] at h
    cases h1 : callW p n "nest_occ" [no, nl, 0, 0, rdW (m.arr64 IW) o] m with
    | none => rw [h1] at h; simp [ocK1] at h
    | some x =>
    obtain ⟨r1, m1⟩ := x
    rw [h1] at h
    refine (noC_afr hN h1).trans ?_
    by_cases hb : r1.headD 0 ≠ 0
    · rw [ocK1_hit p n m1 no nl o l r1 hb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ocK1_miss p n m1 no nl o l r1 hb] at h
    cases h2 : ocW p n m1 no nl (o + 1) (l - 1) with
    | none => rw [h2] at h; simp [ocK2] at h
    | some y =>
    obtain ⟨r2, m2⟩ := y
    rw [h2, ocK2_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact ocW_afr hN n _ _ _ _ _ _ _ h2

theorem occC_afr (hN : NoProg p)
    (hp : p.lookup "target_major_of_outside_occ" = some targetMajorOfOutsideOcc) {no nl o l : Word}
    (h : callW p n "target_major_of_outside_occ" [no, nl, o, l] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (oc_spec p hp n _ no nl o l) h
  exact ocW_afr hN _ _ _ _ _ _ _ _ hW

theorem toiC_afr (hP : ToiProg p) {vis I us dso dsl : Word}
    (h : callW p n "target_outside_inst" [vis, I, us, dso, dsl] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetOutsideInst_spec p hP n _ vis I us dso dsl) h
  exact toiW_afr hW

theorem stubC_afr {f : FnName} {args : List Word} (h : callW p n f args m = some (r, m'))
    (hf : f ∈ stubNames := by decide) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (stubM_spec p f n _ args) h
  exact stub_afr hW hf

theorem lvlEqC_afr {args : List Word} (h : callW p n "lvl_eq_c" args m = some (r, m')) : AFr m m' :=
  stubC_afr h

theorem mkTmC_afr (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "mk_target_major" = some mkTargetMajor)
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word}
    (h : callW p n "mk_target_major" [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12] m =
      some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (mkTargetMajor_spec p ha hp n _ _ _ _ _ _ _ _ _ _ _ _ _ _) h
  exact mkTMW_afr hW

theorem tmtC_afr (hP : TmtProg p) {vis pp pfo pfl I us dso dsl cso csl : Word}
    (h : callW p n "target_major_of_outside_tail" [vis, pp, pfo, pfl, I, us, dso, dsl, cso, csl] m =
      some (r, m')) : AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (tmt_spec p hP.tail k _ vis pp pfo pfl I us dso dsl cso csl) h
  unfold tmtW tmtK1 tmtK2 tmtK3 at hW
  afr_auto hW [toiC_afr hP.toi, lvlEqC_afr, mkTmC_afr hP.toi.alloc hP.mkTm]

theorem tmoC_afr (hP : TmoOProg p) {vis pp pfo pfl I us ao al mno mnl : Word}
    (h : callW p n "target_major_of_outside" [vis, pp, pfo, pfl, I, us, ao, al, mno, mnl] m =
      some (r, m')) : AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (tmo_spec p hP.out k _ vis pp pfo pfl I us ao al mno mnl) h
  unfold tmoW tmoK1 tmoK2 tmoK2b tmoK3 tmoK4 at hW
  afr_auto hW [pinC_afr hP.pin, tcoC_afr hP.nt hP.tco, tmocC_afr hP.bvb hP.hf hP.tmoc,
    occC_afr hP.no hP.occ, tmtC_afr hP.tmt]

theorem tmcC_afr (hP : TmfProg p) {vis pp cao cal pfo pfl fvo fvl ao al x y : Word}
    (h : callW p n "target_major_of_const" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, x, y] m =
      some (r, m')) : AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (tmc_spec p hP.tmc k _ vis pp cao cal pfo pfl fvo fvl ao al x y) h
  unfold tmcW tmcK1 tmcK2 tmfK6 at hW
  afr_auto hW [bsmnC_afr hP.tmm.alloc hP.mnc hP.bsmn, findC_afr hP.find, tmmC_afr hP.tmm,
    tmoC_afr hP.tmo]

/-- **`AbsOK` across `target_major_of`.** -/
theorem tmfC_afr (hP : TmfProg p) {vis pp cao cal pfo pfl fvo fvl mty : Word}
    (h : callW p n "target_major_of" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, mty] m = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (tmf_spec p hP.tmf k _ vis pp cao cal pfo pfl fvo fvl mty) h
  unfold tmfW tmfK1 tmfK2 tmfK3 tmfK6 at hW
  afr_auto hW [gaaC_afr hP.ad, gafC_afr hP.ad, evC_afr hP.ev, tmcC_afr hP]

end calls

end L.Ind
