import ConAgua.Arena.CallF
import ConAgua.Arena.StripTeleSpec
import ConAgua.Arena.PromoteNRef
import ConAgua.Arena.StageInst1
import ConAgua.Arena.IndStubs

/-!
# `is_proj_fn_shape` discharged (lane `indproofs4`, helper `indproofs4-names`)

The recipe of `IndReal.lean` for a read of the name store: the model `ipfF := callF ipfProg
"is_proj_fn_shape"`, its word body `ipfW` (`isProjFnShape_specW`), and `ipfW_run`: on the store
`ArenaR` relates, the body is the twin's `NIdx.isProjFnShape` (the `num`/`str` views,
`viewN_num`/`viewN_str`, and the bytes of the string against `"proj"`/`"projTable"`). Kept apart
from `IndRealNames.lean` so the declaration texts (`DeclHeader.lean`) can import it without the
inductive stage's names.
-/

set_option linter.deprecated false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem ipf_rd64 (m : Mem) (a : ArrId) (i : Word) : L.rd64 m a i = rdW (m.arr64 a) i := by
  simp [L.rd64, rdW, Array.getD_eq_getD_getElem?]

theorem ipf_getElem (a : Array Word) (x : Word) (h : x.toNat < a.size) : a[x.toNat] = rdW a x := by
  simp [rdW, h]

/-! ## `is_proj_fn_shape(n)` (a read of the name store) -/

/-- `is_proj_fn_shape` (calls nothing). -/
def ipfProg : Prog := [("is_proj_fn_shape", L.Checker.isProjFnShapeL)]

def ipfFns : List FnName := ipfProg.map (·.1)

/-- `is_proj_fn_shape` writes nothing. -/
theorem ipfProg_closed : closedA ipfProg [] [] ipfFns = true := by decide +kernel

abbrev IpfF (p : Prog) : Prop := ProgHas p ipfProg

/-- **The model of `is_proj_fn_shape`.** -/
noncomputable def ipfF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF ipfProg "is_proj_fn_shape" m args

theorem ipfF_spec (p : Prog) (hp : IpfF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "is_proj_fn_shape" args
    ⦃fun r s' => LocEq s' s₀ ∧ ipfF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec ipfProg_closed (hp.agree ipfFns) (by decide) n s₀ args

theorem ipfF_frame {m m' : Mem} {args r : List Word} (h : ipfF m args = some (r, m')) :
    MemFrame [] [] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame ipfProg_closed (by decide) (run_of_callW hc)).1

/-- The string test on the slice `(o, l)`. -/
def ipfStrW (m : Mem) (o l : Word) : Word :=
  if l ≠ 4 ∧ l ≠ 9 then 0
  else if rdW (m.arr64 POOL) o ≠ 112 ∨ rdW (m.arr64 POOL) (o + 1) ≠ 114 ∨
      rdW (m.arr64 POOL) (o + 2) ≠ 111 ∨ rdW (m.arr64 POOL) (o + 3) ≠ 106 then 0
  else if l = 4 then 1
  else if rdW (m.arr64 POOL) (o + 4) ≠ 84 ∨ rdW (m.arr64 POOL) (o + 5) ≠ 97 ∨
      rdW (m.arr64 POOL) (o + 6) ≠ 98 ∨ rdW (m.arr64 POOL) (o + 7) ≠ 108 ∨
      rdW (m.arr64 POOL) (o + 8) ≠ 101 then 0
  else 1

/-- The `str` prefix `p`. -/
def ipfS (m : Mem) (p : Word) : Option Word :=
  if 4294967295 < p then none
  else if p >>> 28 ≠ 1 then some 0
  else if tierW p ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (36 + tierW p) ≤ idxW p then none
  else some (ipfStrW m (nsO m (tierW p) (idxW p)) (nsL m (tierW p) (idxW p)))

/-- `is_proj_fn_shape`'s body. -/
def ipfW (m : Mem) (n : Word) : Option Word :=
  if 4294967295 < n then none
  else if n >>> 28 ≠ 2 then some 0
  else if tierW n ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (38 + tierW n) ≤ idxW n then none
  else ipfS m (nnQ m (tierW n) (idxW n))

set_option maxHeartbeats 3200000 in
theorem isProjFnShape_specW (p : Prog) (hp : p.lookup "is_proj_fn_shape" = some L.Checker.isProjFnShapeL)
    (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "is_proj_fn_shape" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ ipfW s₀.mem x = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, L.Checker.isProjFnShapeL]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64]
  all_goals (try simp only [Cond.pval, Expr.pval, Cmp.eval, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, ipf_rd64, ipf_getElem] at *)
  all_goals grind (gen := 20) (instances := 10000) [lang_grind, arena_grind, ipfW, ipfS, ipfStrW, tierW, idxW]


theorem str_beq (s t : String) : (s == t) = decide (strWords s = strWords t) := by
  by_cases h : s = t
  · subst h; simp
  · have : strWords s ≠ strWords t := fun e => h (strWords_inj _ _ e)
    simp [h, this]

theorem strWords_projTableI : strWords "projTable" = [112, 114, 111, 106, 84, 97, 98, 108, 101] := by
  decide

theorem strWords_proj : strWords "proj" = [112, 114, 111, 106] := by decide

theorem ipfStrW_ok (m : Mem) (o l : Word) (s : String) (hsz : (m.arr64 POOL).size < 2 ^ 63)
    (hb : o.toNat + l.toNat ≤ (m.arr64 POOL).size)
    (hk : sliceL (m.arr64 POOL) o.toNat l.toNat = strWords s) :
    (ipfStrW m o l != 0) = (s == "proj" || s == "projTable") ∧ (ipfStrW m o l).toNat ≤ 1 := by
  have hlen : (strWords s).length = l.toNat := by rw [← hk, sliceL_length]
  rw [str_beq, str_beq, strWords_proj, strWords_projTableI, ← hk]
  have ho : o.toNat < 2 ^ 63 := by omega
  have e1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (o + 2).toNat = o.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (o + 3).toNat = o.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have e4 : (o + 4).toNat = o.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have e5 : (o + 5).toNat = o.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
  have e6 : (o + 6).toNat = o.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  have e7 : (o + 7).toNat = o.toNat + 7 := by rw [UInt64.toNat_add]; simp; omega
  have e8 : (o + 8).toNat = o.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  by_cases h4 : l = 4
  · subst h4
    simp only [ipfStrW, rdW, sliceL, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
      e1, e2, e3]
    by_cases b0 : (m.arr64 POOL)[o.toNat]?.getD 0 = 112 <;>
    by_cases b1 : (m.arr64 POOL)[o.toNat + 1]?.getD 0 = 114 <;>
    by_cases b2 : (m.arr64 POOL)[o.toNat + 2]?.getD 0 = 111 <;>
    by_cases b3 : (m.arr64 POOL)[o.toNat + 3]?.getD 0 = 106 <;> simp [b0, b1, b2, b3]
  by_cases h9 : l = 9
  · subst h9
    simp only [ipfStrW, rdW, sliceL, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
      e1, e2, e3, e4, e5, e6, e7, e8]
    by_cases b0 : (m.arr64 POOL)[o.toNat]?.getD 0 = 112 <;>
    by_cases b1 : (m.arr64 POOL)[o.toNat + 1]?.getD 0 = 114 <;>
    by_cases b2 : (m.arr64 POOL)[o.toNat + 2]?.getD 0 = 111 <;>
    by_cases b3 : (m.arr64 POOL)[o.toNat + 3]?.getD 0 = 106 <;>
    simp [b0, b1, b2, b3] <;>
    by_cases b4 : (m.arr64 POOL)[o.toNat + 4]?.getD 0 = 84 <;>
    by_cases b5 : (m.arr64 POOL)[o.toNat + 5]?.getD 0 = 97 <;>
    by_cases b6 : (m.arr64 POOL)[o.toNat + 6]?.getD 0 = 98 <;>
    by_cases b7 : (m.arr64 POOL)[o.toNat + 7]?.getD 0 = 108 <;>
    by_cases b8 : (m.arr64 POOL)[o.toNat + 8]?.getD 0 = 101 <;> simp [b4, b5, b6, b7, b8]
  · have hl4 : l.toNat ≠ 4 := fun e => h4 (UInt64.toNat_inj.mp (by simpa using e))
    have hl9 : l.toNat ≠ 9 := fun e => h9 (UInt64.toNat_inj.mp (by simpa using e))
    have d1 : decide (sliceL (m.arr64 POOL) o.toNat l.toNat = [112, 114, 111, 106]) = false := by
      simp only [decide_eq_false_iff_not]; intro e
      have := congrArg List.length e; rw [sliceL_length] at this; simp at this; omega
    have d2 : decide (sliceL (m.arr64 POOL) o.toNat l.toNat = [112, 114, 111, 106, 84, 97, 98, 108, 101])
        = false := by
      simp only [decide_eq_false_iff_not]; intro e
      have := congrArg List.length e; rw [sliceL_length] at this; simp at this; omega
    rw [d1, d2]
    simp [ipfStrW, h4, h9]


theorem lt32_of_not {w : Word} (h : ¬ 4294967295 < w) : w.toNat < 2 ^ 32 := by
  have := mt UInt64.lt_iff_toNat_lt.mpr h
  have e : (4294967295 : Word).toNat = 4294967295 := rfl
  rw [e] at this; omega

/-- **`is_proj_fn_shape`'s body is the twin's `isProjFnShape`** on the store `ArenaR` relates. -/
theorem ipfW_run {m : Mem} {a : AState} (hR : ArenaR m a) {n w : Word} (h : ipfW m n = some w) :
    (NIdx.isProjFnShape (decI n)).run a = .ok (w != 0, a) ∧ w.toNat ≤ 1 := by
  unfold ipfW at h
  by_cases c1 : 4294967295 < n
  · rw [if_pos c1] at h; cases h
  rw [if_neg c1] at h
  have hn := lt32_of_not c1
  have htag : ((decI n : NIdx).tag == NTag.num) = decide (n >>> 28 = 2) := by
    have := decI_tag_eq (k := .name) n hn 2 (by decide)
    by_cases e : n >>> 28 = 2
    · simp [e, NTag.num] at this ⊢; exact this
    · simp [e, NTag.num] at this ⊢; exact this
  by_cases c2 : n >>> 28 ≠ 2
  · rw [if_pos c2] at h; cases h
    refine ⟨?_, by decide⟩
    simp only [NIdx.isProjFnShape, htag, decide_eq_false c2, Bool.false_eq_true, if_false]
    rfl
  rw [if_neg c2] at h
  have c2' : n >>> 28 = 2 := Decidable.of_not_not c2
  by_cases c3 : tierW n ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [if_pos c3] at h; cases h
  rw [if_neg c3] at h
  by_cases c4 : rdW (m.arr64 CTL) (38 + tierW n) ≤ idxW n
  · rw [if_pos c4] at h; cases h
  rw [if_neg c4] at h
  obtain ⟨hv1, hq⟩ := viewN_num hR hn c3 c2' c4
  generalize nnQ m (tierW n) (idxW n) = q at h hv1 hq
  unfold ipfS at h
  by_cases d1 : 4294967295 < q
  · rw [if_pos d1] at h; cases h
  rw [if_neg d1] at h
  have hqt : ((decI q : NIdx).tag == NTag.str) = decide (q >>> 28 = 1) := by
    have := decI_tag_eq (k := .name) q hq 1 (by decide)
    by_cases e : q >>> 28 = 1
    · simp [e, NTag.str] at this ⊢; exact this
    · simp [e, NTag.str] at this ⊢; exact this
  by_cases d2 : q >>> 28 ≠ 1
  · rw [if_pos d2] at h; cases h
    refine ⟨?_, by decide⟩
    simp only [NIdx.isProjFnShape, htag, decide_eq_true c2', if_true, StateT.run_bind, hv1]
    simp only [bind, Except.bind, hqt, decide_eq_false d2, Bool.false_eq_true, if_false]
    rfl
  rw [if_neg d2] at h
  have d2' : q >>> 28 = 1 := Decidable.of_not_not d2
  by_cases d3 : tierW q ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [if_pos d3] at h; cases h
  rw [if_neg d3] at h
  by_cases d4 : rdW (m.arr64 CTL) (36 + tierW q) ≤ idxW q
  · rw [if_pos d4] at h; cases h
  rw [if_neg d4] at h
  cases h
  obtain ⟨s, hv2, hsl, hk, -⟩ := viewN_str hR hq d3 d2' d4
  have hpool := hR.lit.1
  obtain ⟨hb, hle⟩ := ipfStrW_ok m _ _ s hpool.2.2.1 (by have := hpool.2.2.2; simp only [SliceOK] at hsl; omega) hk
  refine ⟨?_, hle⟩
  simp only [NIdx.isProjFnShape, htag, decide_eq_true c2', if_true, StateT.run_bind, hv1]
  simp only [bind, Except.bind, hqt, decide_eq_true d2', if_true]
  rw [hb]
  simp only [StateT.run, StateT.bind] at hv2 ⊢
  rw [hv2]; rfl


/-- **`is_proj_fn_shape`'s model refines `NIdx.isProjFnShape`** (replaces
`IndStubs.isProjFnShape_spec`): a read, the memory and the twin state unchanged. -/
theorem ipfF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (x : Word) (_hx : H x) :
    RelW ipfF [x] (StageR dn vis fe) (NIdx.isProjFnShape (decI x)) (KeepPost dn vis fe decW0B) := by
  intro m m' a r hc hS
  obtain ⟨n', hc'⟩ := callF_run hc
  cases n' with
  | zero => rw [callW_zero] at hc'; cases hc'
  | succ n =>
  obtain ⟨s', hs', -, hm, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (isProjFnShape_specW ipfProg rfl n _ x) hc'
  simp only at hm hW
  obtain ⟨hrun, hle⟩ := ipfW_run hS.1.arena.1 hW
  subst hs'
  rw [hm]
  exact ⟨_, a, hrun, hS, IWGrow.refl _, rfl, hle⟩

end L.Ind
