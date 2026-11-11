module

public import ConAgua.Arena.RecGenSpec.IwNLtSize
public import ConAgua.Arena.RecGenSpec.PdWMfr
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.RecCheckSpec.EraseFVarTys
import ConAgua.Arena.WhnfCoreProj
public import ConAgua.Arena.RecCheckSpec.TargetMajorAt2
public import ConAgua.Arena.RecGenSpec.ClassMinorSlotHit
import ConAgua.Arena.RecClassSpec.CloseLams

@[expose] public section

/-!
# CfaFv

What `class_fields_agree`'s refinement reads: the datum variable (`cfaFv_in`/`cfaFv_out`), the callees' write sets, the fields' records, `CfaProg`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The datum variable -/

section dv
variable (p : Prog) (k : Nat) (m : Mem) (fvo fvl i : Word)
theorem cfaFv_in (h : i < fvl) : cfaFv p k m fvo fvl i = some ([rdW (m.arr64 IW) (fvo + i)], m) := by
  simp only [cfaFv]; rw [ite_eq_left h]
theorem cfaFv_out (h : ¬ i < fvl) : cfaFv p k m fvo fvl i = callW p k "intern_bvar" [0] m := by
  simp only [cfaFv]; rw [ite_eq_right h]
end dv

/-! ## Write sets -/

theorem tmdW_mfr {m m' : Mem} {r : List Word} (h : tmdW m = some (r, m')) : MFr [] [] m m' := by
  rw [tmdW.arm1] at h
  obtain ⟨⟨ra, m1⟩, h1, h⟩ := of_K h rfl
  rw [tmdW.k_intern_nanon.arm1] at h
  refine (MFr.of_frame (naF_frame h1) (by simp [tier1, NAREC, NASLOT]) (by simp)).trans ?_
  obtain ⟨ls, hp, h⟩ := of_K h rfl
  rw [tmdW.k_pin_word.arm1] at h
  obtain ⟨⟨r3, m2⟩, hmk, h⟩ := of_K h rfl
  rw [tmdW.k_mk_target_major.arm1] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  simp only [mkTMW] at hmk
  rcases hal : allocW m1 13 with _ | qm
  · rw [hal] at hmk; simp at hmk
  obtain ⟨q, m1a⟩ := qm
  rw [hal] at hmk
  simp only [Option.some.injEq, Prod.mk.injEq] at hmk
  rw [← hmk.2]
  refine (allocW_mfr hal).trans ?_
  have e : tmWr m1a q (ra.headD 0) ls 0 0 0 0 0 0 0 0 0 0 0 =
      wrIW m1a q [ra.headD 0, ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    simp [tmWr, wrIW, UInt64.add_assoc]
  rw [e]; exact MFr.of_iw (wrIW_frame _ _ _)

theorem tmaW_mfr {n : Nat} {m m' : Mem} {mo ml c : Word} {r : List Word} (h : tmaW n m mo ml c = some (r, m')) :
    MFr [] [] m m' := by
  rcases n with _ | n
  · simp [tmaW] at h
  by_cases hc : c < ml
  · rw [tmaW_hit n m mo ml c hc] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
  rw [tmaW_miss n m mo ml c hc] at h
  obtain ⟨⟨r0, m0⟩, ho, h⟩ := of_K h rfl
  rw [tmaK_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
  cases n with
  | zero => cases ho
  | succ n => simp only [fuelW_succ] at ho; exact tmdW_mfr ho

theorem leafAtW_mfr {m m' : Mem} {mm leaf : Word} {r : List Word} (h : leafAtW m mm leaf = some (r, m')) :
    MFr [] [] m m' := by
  simp only [leafAtW] at h
  rcases h1 : gafF m [CWF, leaf] with _ | x
  · rw [h1] at h; cases h
  obtain ⟨r1, m1⟩ := x
  simp only [h1] at h
  refine (MFr.ofGafF h1).trans ?_
  have hm : m' = m1 := by
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
    · split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  rw [hm]; exact MFr.refl _ _ _

theorem decCF_words {m : Mem} {q : Nat} {cf : ClassField} (h : decCF m q = some cf)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (cf = .ordinary ∧ rdW (m.arr64 IW) (UInt64.ofNat q) = 0) ∨
    (∃ t tl, cf = .recursive t tl ∧ rdW (m.arr64 IW) (UInt64.ofNat q) = 1 ∧
      rdW (m.arr64 IW) (UInt64.ofNat q + 1) = UInt64.ofNat t ∧ t < 2 ^ 64 ∧
      rdW (m.arr64 IW) (UInt64.ofNat q + 2) = UInt64.ofNat tl ∧ tl < 2 ^ 64) := by
  simp only [decCF, bind, Option.bind_eq_some_iff] at h
  obtain ⟨tg, htg, hcf⟩ := h
  have hq0 := L.Ind.iwN_lt htg
  have h0 := iwN_rdW htg (by omega)
  rcases tg with _ | _ | tg
  · left; simp only [pure, Option.some.injEq] at hcf; exact ⟨hcf.symm, by rw [h0.1]; rfl⟩
  · right
    simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at hcf
    obtain ⟨t, ht, tl, htl, rfl⟩ := hcf
    have hq2 := L.Ind.iwN_lt htl
    have e1 : UInt64.ofNat q + 1 = UInt64.ofNat (q + 1) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
    have e2 : UInt64.ofNat q + 2 = UInt64.ofNat (q + 2) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
    have h1 := iwN_rdW ht (by omega)
    have h2 := iwN_rdW htl (by omega)
    exact ⟨t, tl, rfl, by rw [h0.1]; rfl, by rw [e1, h1.1], h1.2, by rw [e2, h2.1], h2.2⟩
  · simp at hcf

/-- A class decoded below the tops lies below the top. -/
theorem decTM_lt_top {m : Mem} {q : Nat} {x : TargetMajor} (h : DecB (fun m => decTM m q) m x) :
    q < iwTop m := by
  have h' : decTM (truncM m) q = some x := h
  simp only [decTM, bind, Option.bind_eq_some_iff] at h'
  obtain ⟨i, hi, -⟩ := h'
  simp only [iwH, hd?, bind, Option.bind_eq_some_iff] at hi
  obtain ⟨w, hw, -⟩ := hi
  exact (truncM_iw_get hw).1

/-! ## The relational side -/

/-- The lookups of `class_fields_agree`. -/
structure CfaProg (p : Prog) : Prop extends CnaProg p where
  strip : StripProg p
  pw : p.lookup "pin_word" = some pinWordL
  mtm : p.lookup "mk_target_major" = some mkTargetMajor
  tmd : p.lookup "target_major_default" = some targetMajorDefault
  tma : p.lookup "target_major_at" = some targetMajorAt
  cla : p.lookup "class_leaf_at" = some classLeafAtL
  bf : p.lookup "bvar_find" = some bvarFind
  bp : p.lookup "bvar_push" = some bvarPush
  ib : p.lookup "intern_bvar" = some internBVar
  cfa : p.lookup "class_fields_agree" = some classFieldsAgreeL
  na : NaF p
  ad : AdF p

section rel
variable {p : Prog} (P : CfaProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (vis q fto ftl mo ml fvo fvl eo el ko kl : Word) (bs : BlockShape) (formerTys : List EIdx)
  (ms : List TargetMajor) (fvs : List EIdx) (es : List NestCtorNf) (ks : List ClassField)
include P

/-- The datum variable `i`: `exprGetD`. -/
theorem cfaFv_ok {k : Nat} {m m0 : Mem} {a : AState} {i : Word} {r0 : List Word}
    (h : cfaFv p k m fvo fvl i = some (r0, m0)) (hS : StageR vis fe m a)
    (hfv : decHL m fvo.toNat fvl.toNat = some fvs) (hfvb : fvo.toNat + fvl.toNat < 2 ^ 64) (hP : RcMR m) :
    ∃ a0, (ConRon.Arena.exprGetD fvs i.toNat).run a = .ok (decI (r0.headD 0), a0) ∧ H (r0.headD 0) ∧
      StageR vis fe m0 a0 ∧ IWGrow m m0 ∧ RcMR m0 := by
  by_cases hi : i < fvl
  · rw [cfaFv_in (h := hi)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hit : i.toNat < fvl.toNat := UInt64.lt_iff_toNat_lt.mp hi
    obtain ⟨w, hw1, hw2, hw3⟩ := decHL_get' hfv i.toNat hit hfvb
    have hoi : fvo + i = UInt64.ofNat (fvo.toNat + i.toNat) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
    simp only [List.headD_cons]; rw [hoi, hw1]
    refine ⟨a, ?_, hw2, hS, IWGrow.refl m, hP⟩
    rw [← hw3]
    simp [ConRon.Arena.exprGetD, hit, decHL_length m hfv]; rfl
  · rw [cfaFv_out (h := hi)] at h
    obtain ⟨s0, rfl, -, hb⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (internBVar_spec p P.bf P.bp P.ib k _ 0) h
    obtain ⟨a', hrun, hS', hg⟩ := internBVar_stage hS 0 hb
    have hH := binternW_hw _ a hS.check.arena.base.bvar _ _ _ hb
    refine ⟨a', ?_, hH, hS', hg, hP.fr (MFr.of_frame (binternW_frame _ _ _ _ hb) (by simp [tier1, BREC, BSLOT]) (by simp))⟩
    have hge : fvl.toNat ≤ i.toNat := by
      have : ¬ i.toNat < fvl.toNat := fun h => hi (UInt64.lt_iff_toNat_lt.mpr h)
      omega
    have hn : fvs[i.toNat]? = none := by
      rw [List.getElem?_eq_none_iff, decHL_length m hfv]; exact hge
    simp only [ConRon.Arena.exprGetD, hn]
    exact hrun

end rel

end L.Ind

end
