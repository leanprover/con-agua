module

public import ConAgua.Arena.StrLitChar
public import ConAgua.Arena.StrLitList
import ConAgua.Arena.DefEqMid
public import ConAgua.Arena.IndTwin
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.StrLit

@[expose] public section

/-!
# `lit_shape_ok` refines `litShapeOk` (under `CoreS`)

`lit_shape_ok(p)` reads the name word of the record at `p`, then compares it with the ten pinned
literal names in the twin's order (`pin_at`); at a match it hands the record to that name's shape
gate (`nat_ind_ok(1, p)`, …, `char_of_nat_ty_ok(1, p)`), else answers `1`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

/-! ## `lit_shape_ok`'s write set -/

/-- The call closure of `lit_shape_ok` in the checker's program. -/
def litShapeFns : List FnName :=
  ["app_find", "app_push", "nat_ind_at_cv", "nat_zero_at_cv", "nat_succ_at_cv", "bvar_find", "bvar_push", "char_of_nat_ty_ok", "char_ty_ok", "const_e",
  "const_find", "const_push", "der_b", "e_view", "intern_app", "intern_bvar", "intern_const",
  "intern_ls", "intern_param", "intern_sort", "intern_succ", "limbs_eq", "list_cons_ty_ok",
  "list_nil_ty_ok", "list_ty_ok", "lit_hash", "lit_shape_ok", "ls_find", "ls_match", "ls_push",
  "mk_app", "nat_ind_ok", "nat_succ_ok", "nat_zero_ok", "param_find", "param_push", "pin_at",
  "pin_word", "sort_find", "sort_push", "str_cv", "str_ls1", "str_param_sort",
  "string_of_list_ty_ok", "string_ty_ok", "succ_find", "succ_push"]

/-- `lit_shape_ok`'s closure writes only what a core function may (`coreStageA`, `coreStageC`):
neither pool, nor the pins, nor the stage memos. -/
def LitShapeClosed (p : Prog) : Prop := closedA p coreStageA coreStageC litShapeFns = true

theorem callW_litShapeFrame {p : Prog} (hcl : LitShapeClosed p) {f : FnName} (hf : f ∈ litShapeFns) {n : Nat}
    {args : List Word} {m m' : Mem} {r : List Word} (h : callW p n f args m = some (r, m')) :
    MemFrame coreStageA coreStageC m m' :=
  (run_memFrame hcl hf (run_of_callW h)).1

/-- The model of `lit_shape_ok`. -/
l_model litShapeOk_spec (p : Prog) (hp : StrLitProg p)
  fns [hp.litShapeOk ↦ litShapeOkW]
  specs [callW_spec p n "pin_at", callW_spec p n "nat_ind_at_cv", callW_spec p n "nat_zero_at_cv",
    callW_spec p n "nat_succ_at_cv", callW_spec p n "string_ty_ok", callW_spec p n "string_of_list_ty_ok",
    callW_spec p n "list_ty_ok", callW_spec p n "list_nil_ty_ok", callW_spec p n "list_cons_ty_ok",
    callW_spec p n "char_ty_ok", callW_spec p n "char_of_nat_ty_ok"]
  grind [arena_grind]
  gen 30

/-! ## `litShapeOk`'s three `Nat` arms at the kinds their guards ask for -/

/-- The model of `nat_ind_at_cv`. -/
l_model natIndAtCv_spec (p : Prog) (hp : StrLitProg p)
  fns [hp.natIndAtCv ↦ natIndAtCvW]
  specs [callW_spec p n "pin_word"]
  grind [arena_grind]
  gen 30

/-- The model of `nat_zero_at_cv`. -/
l_model natZeroAtCv_spec (p : Prog) (hp : StrLitProg p)
  fns [hp.natZeroAtCv ↦ natZeroAtCvW]
  specs [callW_spec p n "pin_at", callW_spec p n "const_e"]
  grind [arena_grind]
  gen 30

/-- The model of `nat_succ_at_cv`. -/
l_model natSuccAtCv_spec (p : Prog) (hp : StrLitProg p)
  fns [hp.natSuccAtCv ↦ natSuccAtCvW]
  specs [callW_spec p n "pin_at", callW_spec p n "const_e"]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] gen 30

section natcv
variable (p : Prog) (hp : StrLitProg p)
include hp

/-- **`nat_ind_at_cv(q)` refines `natIndOk (some (.indInfo cv {}))`** at the constant value `q`. -/
@[refines ConRon.Arena.natIndOk]
theorem callW_natIndAtCv (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb q : Word) (hC : CoreS dn s₀.mem a₀ vis fe MM eb)
    {cv : IConstantVal} (hcv : decCV (erecP s₀.mem) q.toNat = some cv)
    (r : List Word) (m' : Mem) (h : callW p n "nat_ind_at_cv" [q] s₀.mem = some (r, m')) :
    CRef (natIndOk (some (.indInfo cv {}))) a₀ decBool dn s₀.mem vis fe MM eb r m' ResH := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (natIndAtCv_spec p hp (n + 1) s₀ q) h
  obtain ⟨-, hlen⟩ := decCV_rdq (erRdOK s₀.mem) hcv
  obtain ⟨-, -, ⟨w3, hw3, hl3, hty⟩⟩ := decCV_words hcv
  have hq3 : erRd s₀.mem (q + 3) = w3 := (erRdOK s₀.mem).off hw3 (by simp)
  rw [natIndAtCvW.eq_2] at hW
  by_cases hk2 : erRd s₀.mem (q + 2) ≠ 0
  · erw [ite_eq_left hk2] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    refine CRef.pure hC false ?_ ?_ ?_
    · rw [natIndOk_run_ind hC.pins]
      have : cv.levelParams.isEmpty = false := by
        rcases hl : cv.levelParams with _ | ⟨x, xs⟩
        · exfalso; rw [hl] at hlen; exact hk2 (UInt64.toNat_inj.mp (by simpa using hlen.symm))
        · rfl
      rw [this]; rfl
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  erw [ite_eq_right hk2] at hW
  have hk2' : erRd s₀.mem (q + 2) = 0 := by simpa using hk2
  rcases h1 : callW p n "pin_word" [54] s₀.mem with _ | ⟨r₁, m₁⟩
    <;> simp only [h1, natIndAtCvW.k_pin_word, reduceCtorEq] at hW
  obtain ⟨rfl, -, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 54 r₁ m₁ h1
  simp only [show (54 : Word).toNat = 54 from rfl] at hr₁
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [← hm]
  have hb : (cv.levelParams.isEmpty && cv.type == decI (pinW s₀.mem 54)) =
      decide (erRd s₀.mem (q + 3) = r₁.headD 0) := by
    have hl0 : cv.levelParams.isEmpty = true := by
      simp only [List.isEmpty_iff, ← List.length_eq_zero_iff]; rw [hlen, hk2']; rfl
    rw [hl0, hty, hq3, hr₁, decI_beq _ _ hl3 hC.pins.lv_lt.2.2]
    simp
  refine CRef.pure hC _ (by rw [natIndOk_run_ind hC.pins]) ?_ ?_
  · show decBool [r.headD 0] = _
    rw [← hr, hb]; exact L.Arena.decBool_ite _
  · show ResH [r.headD 0]
    rw [← hr]; exact L.Arena.resH_ite _

/-- **`nat_zero_at_cv(q)` refines `natZeroOk (some (.ctorInfo cv 0 0 fam))`** at the constant value
`q`. -/
@[refines ConRon.Arena.natZeroOk]
theorem callW_natZeroAtCv (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb q : Word) (hC : CoreS dn s₀.mem a₀ vis fe MM eb)
    {cv : IConstantVal} (hcv : decCV (erecP s₀.mem) q.toNat = some cv) (np nf : Nat) (fam : NIdx)
    (r : List Word) (m' : Mem) (h : callW p n "nat_zero_at_cv" [q] s₀.mem = some (r, m')) :
    CRef (natZeroOk (some (.ctorInfo cv np nf fam))) a₀ decBool dn s₀.mem vis fe MM eb r m' ResH := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (natZeroAtCv_spec p hp (n + 1) s₀ q) h
  obtain ⟨-, hlen⟩ := decCV_rdq (erRdOK s₀.mem) hcv
  obtain ⟨-, -, ⟨w3, hw3, hl3, hty⟩⟩ := decCV_words hcv
  have hq3 : erRd s₀.mem (q + 3) = w3 := (erRdOK s₀.mem).off hw3 (by simp)
  rw [natZeroAtCvW.eq_2] at hW
  cases h1 : callW p n "pin_at" [1] s₀.mem with
  | none => rw [h1, natZeroAtCvW.k_pin_at.none] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1, natZeroAtCvW.k_pin_at.eq_2] at hW
  obtain ⟨rfl, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n s₀.mem 1 r₁ m₁ h1
  simp only [show (1 : Word).toNat = 1 from rfl] at hr₁
  have hnt : HW (r₁.headD 0) := by
    rw [hr₁]; exact hC.pins.names_lt 1 (by decide)
  cases h2 : callW p n "const_e" [r₁.headD 0] s₀.mem with
  | none => rw [h2, natZeroAtCvW.k_const_e.none] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2, natZeroAtCvW.k_const_e.eq_2] at hW
  obtain ⟨hok, hS, hres, hfr, hhw⟩ := callW_constE p hp.toWhnfDeltaProg' n s₀ a₀ dn vis fe MM eb _ hC hnt r₂ m₂ h2
  have hr₁' : r₁.headD 0 = pinW s₀.mem 2 := hr₁
  rw [hr₁'] at hok hS hres
  have hE : ∀ x : Word, rdW (m₂.arr64 (tierA EREC (x >>> 40))) (x &&& 0xFFFFFFFFFF) = erRd s₀.mem x := by
    have h0 := hfr.arr EREC (by simp [tier1, CREC, CSLOT, CLP, EREC]) (by decide)
    have h1 := hfr.arr (tier1 EREC) (by simp [tier1, CREC, CSLOT, CLP, EREC]) (by decide)
    exact erRd_congr h0 h1
  simp only [hE] at hW
  have hrun := AM.run_of_ok _ _ hok
  have hrun' : (constE (decI (pinW s₀.mem 2))).run a₀ =
      .ok (decE (r₂.headD 0), AM.st (constE (decI (pinW s₀.mem 2))) a₀) := by
    rw [hrun, hres]; rfl
  have hz := natZeroOk_run_ctor hC.pins cv np nf fam _ hrun'
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  by_cases hk2 : erRd s₀.mem (q + 2) ≠ 0
  · rw [ite_eq_left hk2] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    refine ⟨hok', by rw [hst']; exact hS, ?_, hfr, ?_⟩
    · rw [hres']
      have : cv.levelParams.isEmpty = false := by
        rcases hl : cv.levelParams with _ | ⟨x, xs⟩
        · exfalso; rw [hl] at hlen; exact hk2 (UInt64.toNat_inj.mp (by simpa using hlen.symm))
        · rfl
      rw [this]; simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [ite_eq_right hk2] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [← hm]
  have hk2' : erRd s₀.mem (q + 2) = 0 := by simpa using hk2
  refine ⟨hok', by rw [hst']; exact hS, ?_, hfr, ?_⟩
  · rw [hres']
    have hl0 : cv.levelParams.isEmpty = true := by
      simp only [List.isEmpty_iff, ← List.length_eq_zero_iff]; rw [hlen, hk2']; rfl
    rw [hl0, hty, ← hq3]
    show _ = decBool [r.headD 0]
    rw [← hr]
    show (true && (decI (erRd s₀.mem (q + 3)) == decI (r₂.headD 0))) = _
    rw [decI_beq _ _ (by rw [hq3]; exact hl3) hhw]
    simp [L.Arena.decBool_ite]
  · show ResH [r.headD 0]
    rw [← hr]; exact L.Arena.resH_ite _

/-- **`nat_succ_at_cv(q)` refines `natSuccOk (some (.ctorInfo cv 0 1 fam))`** at the constant value
`q`. -/
@[refines ConRon.Arena.natSuccOk]
theorem callW_natSuccAtCv (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb q : Word) (hC : CoreS dn s₀.mem a₀ vis fe MM eb)
    {cv : IConstantVal} (hcv : decCV (erecP s₀.mem) q.toNat = some cv) (np nf : Nat) (fam : NIdx)
    (r : List Word) (m' : Mem) (h : callW p n "nat_succ_at_cv" [q] s₀.mem = some (r, m')) :
    CRef (natSuccOk (some (.ctorInfo cv np nf fam))) a₀ decBool dn s₀.mem vis fe MM eb r m' ResH := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (natSuccAtCv_spec p hp (n + 1) s₀ q) h
  obtain ⟨-, hlen⟩ := decCV_rdq (erRdOK s₀.mem) hcv
  obtain ⟨-, -, ⟨w3, hw3, htyl, hty⟩⟩ := decCV_words hcv
  have hq3 : erRd s₀.mem (q + 3) = w3 := (erRdOK s₀.mem).off hw3 (by simp)
  rw [← hq3] at htyl hty
  rw [natSuccAtCvW.eq_2] at hW
  by_cases hk2 : erRd s₀.mem (q + 2) ≠ 0
  · erw [ite_eq_left hk2] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    refine CRef.pure hC false ?_ ?_ ?_
    · apply natSuccOk_run_lps
      rcases hl : cv.levelParams with _ | ⟨x, xs⟩
      · exfalso; rw [hl] at hlen; exact hk2 (UInt64.toNat_inj.mp (by simpa using hlen.symm))
      · rfl
    · simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  erw [ite_eq_right hk2] at hW
  have hk2' : erRd s₀.mem (q + 2) = 0 := by simpa using hk2
  have hl0 : cv.levelParams.isEmpty = true := by
    simp only [List.isEmpty_iff, ← List.length_eq_zero_iff]; rw [hlen, hk2']; rfl
  cases h1 : callW p n "pin_at" [1] s₀.mem with
  | none => rw [h1, natSuccAtCvW.k_pin_at.none] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1, natSuccAtCvW.k_pin_at.eq_2] at hW
  obtain ⟨rfl, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n s₀.mem 1 r₁ m₁ h1
  simp only [show (1 : Word).toNat = 1 from rfl] at hr₁
  have hnt : HW (r₁.headD 0) := by
    rw [hr₁]; exact hC.pins.names_lt 1 (by decide)
  cases h2 : callW p n "const_e" [r₁.headD 0] s₀.mem with
  | none => rw [h2, natSuccAtCvW.k_const_e.none] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2, natSuccAtCvW.k_const_e.eq_2] at hW
  obtain ⟨hok, hS, hres, hfr, hhw⟩ := callW_constE p hp.toWhnfDeltaProg' n s₀ a₀ dn vis fe MM eb _ hC hnt r₂ m₂ h2
  have hr₁' : r₁.headD 0 = pinW s₀.mem 2 := hr₁
  rw [hr₁'] at hok hS hres
  have hE : ∀ x : Word, rdW (m₂.arr64 (tierA EREC (x >>> 40))) (x &&& 0xFFFFFFFFFF) = erRd s₀.mem x := by
    have h0 := hfr.arr EREC (by simp [tier1, CREC, CSLOT, CLP, EREC]) (by decide)
    have h1 := hfr.arr (tier1 EREC) (by simp [tier1, CREC, CSLOT, CLP, EREC]) (by decide)
    exact erRd_congr h0 h1
  have hrun := AM.run_of_ok _ _ hok
  have hrun' : (constE (decI (pinW s₀.mem 2))).run a₀ =
      .ok (decE (r₂.headD 0), AM.st (constE (decI (pinW s₀.mem 2))) a₀) := by
    rw [hrun, hres]; rfl
  simp only [hE] at hW
  by_cases hg : tagW (erRd s₀.mem (q + 3)) ≠ 6
  · rw [ite_eq_left hg] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    have hz := natSuccOk_run_nonforall hC.pins cv np nf fam _ hl0 hrun' (by
      rw [hty]
      cases hb : ((decI (erRd s₀.mem (q + 3)) : EIdx).tag == ETag.forallE)
      · rfl
      · exfalso; exact hg ((decE_tag_forallE _ htyl).mp (beq_iff_eq.mp hb)))
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', by rw [hst']; exact hS, ?_, hfr, ?_⟩
    · rw [hres']; simp only [decBool, ← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [ite_eq_right hg] at hW
  have hg' : tagW (erRd s₀.mem (q + 3)) = 6 := by simpa using hg
  by_cases hsc : tierW (erRd s₀.mem (q + 3)) ≠ 0 ∧ rdW (m₂.arr64 CTL) 1 = 0
  · rw [ite_eq_left hsc] at hW; cases hW
  rw [ite_eq_right hsc] at hW
  by_cases hbd : tcnt m₂ FORALL (tierW (erRd s₀.mem (q + 3))) ≤
      idxW (erRd s₀.mem (q + 3))
  · rw [ite_eq_left hbd] at hW; cases hW
  rw [ite_eq_right hbd] at hW
  rw [ite_some_pair] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [← hm]
  have hvOK : viewOK m₂ (erRd s₀.mem (q + 3)) FORALL := ⟨hsc, by simpa using hbd⟩
  obtain ⟨hview, hd, hb⟩ := view_forall m₂ _ hS.arena.base _ htyl hvOK hg'
  have hz := natSuccOk_run_forall hC.pins cv np nf fam _ _ _ hl0 hrun' (by
      rw [hty]; exact beq_iff_eq.mpr ((decE_tag_forallE _ htyl).mpr hg')) (by rw [hty]; exact hview)
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', by rw [hst']; exact hS, ?_, hfr, ?_⟩
  · rw [hres']
    show _ = decBool [r.headD 0]
    rw [← hr]
    simp only [decE_eq]
    rw [decI_beq _ _ hd hhw, decI_beq _ _ hb hhw]
    rw [L.Arena.decBool_ite, Bool.decide_and]
  · show ResH [r.headD 0]
    rw [← hr]; exact L.Arena.resH_ite _

end natcv

theorem ciName_cv (ci : IConstantInfo) : ci.name = ci.toConstantVal.name := by
  cases ci <;> rfl

section calls
variable (p : Prog) (hp : StrLitProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
  {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
include hp

/-- **One arm of the name chain**: the pin read, the name compared, `T` at a match, else `E`. -/
theorem lsoArm {T E : NIdx → AM Bool} (hS : CoreS dn m a vis fe M eb) {ci : IConstantInfo}
    {nw : Word} (hnw : HW nw) (hname : ci.name = decI nw) {i : Word} {rp : List Word} {mp : Mem}
    (hc : callW p n "pin_at" [i] m = some (rp, mp)) (k : Nat) (hk : i.toNat = k) (hi51 : i ≠ 51)
    (hT : mp = m → nw = rp.headD 0 → CoreRef (T (decI (rp.headD 0))) a decBool dn m vis fe M eb r m')
    (hE : mp = m → nw ≠ rp.headD 0 → CoreRef (E (decI (rp.headD 0))) a decBool dn m vis fe M eb r m') :
    CoreRef (pinAt k >>= fun x => if (ci.name == x) = true then T x else E x) a decBool dn m vis fe M eb
      r m' := by
  obtain ⟨hm, -, hi, hr⟩ := callW_pinAt p hp.pinAt n m i rp mp hc hi51
  subst hk
  refine pin_step p hp hS hc ?_ hi51
  have hpw : HW (rp.headD 0) := by rw [hr]; exact hS.pins.names_lt _ hi
  rw [hname, decI_beq _ _ hnw hpw]
  by_cases he : nw = rp.headD 0
  · rw [ite_eq_left (by simpa using he)]; exact hT hm he
  · rw [ite_eq_right (by simpa using he)]; exact hE hm he

omit hp in
/-- **A gate as the chain's tail call**: its refinement on the call's result. -/
theorem lsoGate {T : AM Bool} {f : FnName} {args : List Word}
    (hW : litShapeOkW.k_nat_ind_at_cv p (callW p n f args m) = some (r.headD 0, m'))
    (hG : ∀ r₂ m₂, callW p n f args m = some (r₂, m₂) →
      CoreRef T a decBool dn m vis fe M eb r₂ m₂) :
    CoreRef T a decBool dn m vis fe M eb r m' := by
  rcases h2 : callW p n f args m with _ | ⟨r₂, m₂⟩
  · rw [h2, litShapeOkW.k_nat_ind_at_cv.none] at hW; cases hW
  rw [h2, litShapeOkW.k_nat_ind_at_cv.eq_2] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, rfl⟩ := hW
  obtain ⟨h1, h2', h3, h4⟩ := hG r₂ _ h2
  exact ⟨h1, h2', by rw [h3]; unfold decBool; rw [hr], by unfold ResH; rw [← hr]; exact h4⟩

/-- **`lit_shape_ok` refines `litShapeOk`** at a decoded record whose level parameters' names
denote (the list gates' one-parameter test). -/
@[refines ConRon.Arena.litShapeOk]
theorem litShapeOk_call (hS : CoreS dn m a vis fe M eb) {c : Word} {ci : IConstantInfo}
    (hci : decCI (erecP m) c.toNat = some ci)
    (hlps : ∃ ks, ci.toConstantVal.levelParams.mapM (denoteN a.store.ns) = some ks)
    (h : callW p n "lit_shape_ok" [c] m = some (r, m')) :
    CoreRef (litShapeOk ci) a decBool dn m vis fe M eb r m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (litShapeOk_spec p hp (n + 1) _ c) h
  change litShapeOkW p (n + 1) m c = some (r.headD 0, s'.mem) at hW
  generalize s'.mem = m' at hW ⊢
  rw [litShapeOkW.eq_2, erRd_congr rfl rfl] at hW
  have hcv := decCI_cvA hci
  obtain ⟨nw, hnw, hnwl, hnm⟩ := decCV_name hcv
  have hc1 : (c + 1).toNat = c.toNat + 1 := by
    have := erecP_lt64 hnw; rw [UInt64.toNat_add]; simp; omega
  have hrd : erRd m (c + 1) = nw := erRd_of _ _ (by rw [hc1]; exact hnw)
  rw [hrd] at hW
  have hname : ci.name = decI nw := by rw [ciName_cv, hnm]
  have hdec : (1 : Word) ≠ 0 → ∃ ci', decCI (erecP m) c.toNat = some ci' := fun _ => ⟨ci, hci⟩
  have hfd : envFound m 1 c = some ci := by simp [envFound, hci]
  have hl : ∀ ci', envFound m 1 c = some ci' →
      ∃ ks, ci'.toConstantVal.levelParams.mapM (denoteN a.store.ns) = some ks := by
    intro ci' h'; rw [hfd] at h'; cases h'; exact hlps
  unfold litShapeOk pinNat pinNatZero pinNatSucc pinString pinStringOfList pinList pinListNil
    pinListCons pinChar pinCharOfNat
  -- `Nat`
  rcases h1 : callW p n "pin_at" [1] m with _ | ⟨r1, m1⟩
  · rw [h1, litShapeOkW.k_pin_at.none] at hW; cases hW
  rw [h1, litShapeOkW.k_pin_at.eq_2] at hW
  refine lsoArm p hp hS hnwl hname h1 _ rfl (by decide) (fun hm he => ?_) (fun hm he => ?_)
  · subst m1; rw [ite_eq_left he] at hW
    refine lsoGate p hW fun r₂ m₂ h₂ => ?_
    exact (callW_natIndAtCv p hp n ⟨m, Locals.init []⟩ a dn vis fe M eb (c + 1) hS
      (by rw [hc1]; exact hcv) r₂ m₂ h₂).core
  subst m1; rw [ite_eq_right he] at hW
  -- `Nat.zero`
  rcases h1 : callW p n "pin_at" [2] m with _ | ⟨r1, m1⟩
  · rw [h1, litShapeOkW.k_pin_at_2.none] at hW; cases hW
  rw [h1, litShapeOkW.k_pin_at_2.eq_2] at hW
  refine lsoArm p hp hS hnwl hname h1 _ rfl (by decide) (fun hm he => ?_) (fun hm he => ?_)
  · subst m1; rw [ite_eq_left he] at hW
    refine lsoGate p hW fun r₂ m₂ h₂ => ?_
    exact (callW_natZeroAtCv p hp n ⟨m, Locals.init []⟩ a dn vis fe M eb (c + 1) hS
      (by rw [hc1]; exact hcv) 0 0 _ r₂ m₂ h₂).core
  subst m1; rw [ite_eq_right he] at hW
  -- `Nat.succ`
  rcases h1 : callW p n "pin_at" [3] m with _ | ⟨r1, m1⟩
  · rw [h1, litShapeOkW.k_pin_at_3.none] at hW; cases hW
  rw [h1, litShapeOkW.k_pin_at_3.eq_2] at hW
  refine lsoArm p hp hS hnwl hname h1 _ rfl (by decide) (fun hm he => ?_) (fun hm he => ?_)
  · subst m1; rw [ite_eq_left he] at hW
    refine lsoGate p hW fun r₂ m₂ h₂ => ?_
    exact (callW_natSuccAtCv p hp n ⟨m, Locals.init []⟩ a dn vis fe M eb (c + 1) hS
      (by rw [hc1]; exact hcv) 0 1 _ r₂ m₂ h₂).core
  subst m1; rw [ite_eq_right he] at hW
  -- `String`
  rcases h1 : callW p n "pin_at" [5] m with _ | ⟨r1, m1⟩
  · rw [h1, litShapeOkW.k_pin_at_4.none] at hW; cases hW
  rw [h1, litShapeOkW.k_pin_at_4.eq_2] at hW
  refine lsoArm p hp hS hnwl hname h1 _ rfl (by decide) (fun hm he => ?_) (fun hm he => ?_)
  · subst m1; rw [ite_eq_left he] at hW
    refine lsoGate p hW fun r₂ m₂ h₂ => ?_
    rw [← hfd]; exact stringTyOk_call p hp hS hdec h₂
  subst m1; rw [ite_eq_right he] at hW
  -- `String.ofList`
  rcases h1 : callW p n "pin_at" [6] m with _ | ⟨r1, m1⟩
  · rw [h1, litShapeOkW.k_pin_at_5.none] at hW; cases hW
  rw [h1, litShapeOkW.k_pin_at_5.eq_2] at hW
  refine lsoArm p hp hS hnwl hname h1 _ rfl (by decide) (fun hm he => ?_) (fun hm he => ?_)
  · subst m1; rw [ite_eq_left he] at hW
    refine lsoGate p hW fun r₂ m₂ h₂ => ?_
    rw [← hfd]; exact stringOfListTyOk_call p hp hS hdec h₂
  subst m1; rw [ite_eq_right he] at hW
  -- `List`
  rcases h1 : callW p n "pin_at" [7] m with _ | ⟨r1, m1⟩
  · rw [h1, litShapeOkW.k_pin_at_6.none] at hW; cases hW
  rw [h1, litShapeOkW.k_pin_at_6.eq_2] at hW
  refine lsoArm p hp hS hnwl hname h1 _ rfl (by decide) (fun hm he => ?_) (fun hm he => ?_)
  · subst m1; rw [ite_eq_left he] at hW
    refine lsoGate p hW fun r₂ m₂ h₂ => ?_
    rw [← hfd]; exact listTyOk_call p hp hS hdec hl h₂
  subst m1; rw [ite_eq_right he] at hW
  -- `List.nil`
  rcases h1 : callW p n "pin_at" [8] m with _ | ⟨r1, m1⟩
  · rw [h1, litShapeOkW.k_pin_at_7.none] at hW; cases hW
  rw [h1, litShapeOkW.k_pin_at_7.eq_2] at hW
  refine lsoArm p hp hS hnwl hname h1 _ rfl (by decide) (fun hm he => ?_) (fun hm he => ?_)
  · subst m1; rw [ite_eq_left he] at hW
    refine lsoGate p hW fun r₂ m₂ h₂ => ?_
    rw [← hfd]; exact listNilTyOk_call p hp hS hdec hl h₂
  subst m1; rw [ite_eq_right he] at hW
  -- `List.cons`
  rcases h1 : callW p n "pin_at" [9] m with _ | ⟨r1, m1⟩
  · rw [h1, litShapeOkW.k_pin_at_8.none] at hW; cases hW
  rw [h1, litShapeOkW.k_pin_at_8.eq_2] at hW
  refine lsoArm p hp hS hnwl hname h1 _ rfl (by decide) (fun hm he => ?_) (fun hm he => ?_)
  · subst m1; rw [ite_eq_left he] at hW
    refine lsoGate p hW fun r₂ m₂ h₂ => ?_
    rw [← hfd]; exact listConsTyOk_call p hp hS hdec hl h₂
  subst m1; rw [ite_eq_right he] at hW
  -- `Char`
  rcases h1 : callW p n "pin_at" [10] m with _ | ⟨r1, m1⟩
  · rw [h1, litShapeOkW.k_pin_at_9.none] at hW; cases hW
  rw [h1, litShapeOkW.k_pin_at_9.eq_2] at hW
  refine lsoArm p hp hS hnwl hname h1 _ rfl (by decide) (fun hm he => ?_) (fun hm he => ?_)
  · subst m1; rw [ite_eq_left he] at hW
    refine lsoGate p hW fun r₂ m₂ h₂ => ?_
    rw [← hfd]; exact charTyOk_call p hp hS hdec h₂
  subst m1; rw [ite_eq_right he] at hW
  -- `Char.ofNat`
  rcases h1 : callW p n "pin_at" [12] m with _ | ⟨r1, m1⟩
  · rw [h1, litShapeOkW.k_pin_at_10.none] at hW; cases hW
  rw [h1, litShapeOkW.k_pin_at_10.eq_2] at hW
  refine lsoArm p hp hS hnwl hname h1 _ rfl (by decide) (fun hm he => ?_) (fun hm he => ?_)
  · subst m1; rw [ite_eq_left he] at hW
    refine lsoGate p hW fun r₂ m₂ h₂ => ?_
    rw [← hfd]; exact charOfNatTyOk_call p hp hS hdec h₂
  subst m1; rw [ite_eq_right he] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, rfl⟩ := hW
  exact coreRef_ret hS (by rw [decBool, ← hr]; rfl) (by unfold ResH HW; rw [← hr]; decide)

end calls

end L.Arena
