module

public import ConAgua.Arena.StrLitTy
public import ConAgua.Arena.StrLitChar
public import ConAgua.Arena.StrLitList
public import ConAgua.Arena.StrLitExt
public import ConAgua.Arena.WhnfDeltaRefine
import ConAgua.Arena.InferLeaves
import ConAgua.Arena.DefEqMid
public import ConAgua.Arena.IndTwin
import ConAgua.Arena.StageC
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
  ["app_find", "app_push", "bvar_find", "bvar_push", "char_of_nat_ty_ok", "char_ty_ok", "const_e",
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
  specs [callW_spec p n "pin_at", callW_spec p n "nat_ind_ok", callW_spec p n "nat_zero_ok",
    callW_spec p n "nat_succ_ok", callW_spec p n "string_ty_ok", callW_spec p n "string_of_list_ty_ok",
    callW_spec p n "list_ty_ok", callW_spec p n "list_nil_ty_ok", callW_spec p n "list_cons_ty_ok",
    callW_spec p n "char_ty_ok", callW_spec p n "char_of_nat_ty_ok"]
  grind [arena_grind]
  gen 30

theorem ciName_cv (ci : IConstantInfo) : ci.name = ci.toConstantVal.name := by
  cases ci <;> rfl

section calls
variable (p : Prog) (hp : StrLitProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
  {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
include hp

/-- **One arm of the name chain**: the pin read, the name compared, `T` at a match, else `E`. -/
theorem lsoArm {T E : AM Bool} (hS : CoreS dn m a vis fe M eb) {ci : IConstantInfo} {nw : Word}
    (hnw : HW nw) (hname : ci.name = decI nw) {i : Word} {rp : List Word} {mp : Mem}
    (hc : callW p n "pin_at" [i] m = some (rp, mp)) (k : Nat) (hk : i.toNat = k) (hi51 : i ≠ 51)
    (hT : mp = m → nw = rp.headD 0 → CoreRef T a decBool dn m vis fe M eb r m')
    (hE : mp = m → nw ≠ rp.headD 0 → CoreRef E a decBool dn m vis fe M eb r m') :
    CoreRef (pinAt k >>= fun x => if (ci.name == x) = true then T else E) a decBool dn m vis fe M eb
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
theorem lsoGate {T : AM Bool} {f : FnName} {c : Word}
    (hW : litShapeOkW.k_nat_ind_ok p (callW p n f [1, c] m) = some (r.headD 0, m'))
    (hG : ∀ r₂ m₂, callW p n f [1, c] m = some (r₂, m₂) →
      CoreRef T a decBool dn m vis fe M eb r₂ m₂) :
    CoreRef T a decBool dn m vis fe M eb r m' := by
  rcases h2 : callW p n f [1, c] m with _ | ⟨r₂, m₂⟩
  · rw [h2, litShapeOkW.k_nat_ind_ok.none] at hW; cases hW
  rw [h2, litShapeOkW.k_nat_ind_ok.eq_2] at hW
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
  rw [litShapeOkW.eq_2, erRdT_congr rfl rfl] at hW
  have hcv := decCI_cvA hci
  obtain ⟨nw, hnw, hnwl, hnm⟩ := decCV_name hcv
  have hc1 : (c + 1).toNat = c.toNat + 1 := by
    have := erecP_lt64 hnw; rw [UInt64.toNat_add]; simp; omega
  have hrd : erRdT m (c + 1) = nw := erRdT_of _ _ (by rw [hc1]; exact hnw)
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
    rw [← hfd]; exact (callW_natIndOk p hp.toWhnfDeltaProg n ⟨m, Locals.init []⟩ a dn vis fe M eb
      1 c hS hdec r₂ m₂ h₂).core
  subst m1; rw [ite_eq_right he] at hW
  -- `Nat.zero`
  rcases h1 : callW p n "pin_at" [2] m with _ | ⟨r1, m1⟩
  · rw [h1, litShapeOkW.k_pin_at_2.none] at hW; cases hW
  rw [h1, litShapeOkW.k_pin_at_2.eq_2] at hW
  refine lsoArm p hp hS hnwl hname h1 _ rfl (by decide) (fun hm he => ?_) (fun hm he => ?_)
  · subst m1; rw [ite_eq_left he] at hW
    refine lsoGate p hW fun r₂ m₂ h₂ => ?_
    rw [← hfd]; exact (callW_natZeroOk p hp.toWhnfDeltaProg' n ⟨m, Locals.init []⟩ a dn vis fe M eb
      1 c hS hdec r₂ m₂ h₂).core
  subst m1; rw [ite_eq_right he] at hW
  -- `Nat.succ`
  rcases h1 : callW p n "pin_at" [3] m with _ | ⟨r1, m1⟩
  · rw [h1, litShapeOkW.k_pin_at_3.none] at hW; cases hW
  rw [h1, litShapeOkW.k_pin_at_3.eq_2] at hW
  refine lsoArm p hp hS hnwl hname h1 _ rfl (by decide) (fun hm he => ?_) (fun hm he => ?_)
  · subst m1; rw [ite_eq_left he] at hW
    refine lsoGate p hW fun r₂ m₂ h₂ => ?_
    rw [← hfd]; exact (callW_natSuccOk p hp.toWhnfDeltaProg' n ⟨m, Locals.init []⟩ a dn vis fe M eb
      1 c hS hdec r₂ m₂ h₂).core
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
