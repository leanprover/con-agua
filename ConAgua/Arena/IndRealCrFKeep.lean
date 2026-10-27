import ConAgua.Arena.IndRealMemoCr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# `consts_resolve_ffast` keeps its memo well formed, from any memory (lane `indproofs4`, helper `kc`)

`crfF_keepsCrOK`: a returning run of the model `crfF` (`IndRealCrF.lean`), at any arguments, from a
memory whose walk memo `CRM` is related to some memo (`CrOK`), ends with one related to some memo.
No stage relation: the memo's own writes keep it well formed whatever the expression is, because
the walk records only at a handle `e_view` accepted (below `2^32`: a valid `bmKey` key) and only a
`0`/`1` word (a leaf's answer, a hit's stored word, or the conjunction of its children's); every
other callee only reads (`crfRO_closed`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena L.Stubs

/-- The callees of `crf_go` that only read. -/
theorem crfRO_closed : closedA crfP [] []
    ["cr_leaf", "is_str_lit", "cr_lit_pins", "pin_found", "env_find", "env_row_get", "env_ix",
      "pin_at"] = true := by decide +kernel

/-- What a returning call says: the walk memo related after, a `0`/`1` answer. -/
def CG (o : Option (List Word × Mem)) : Prop :=
  ∀ r m', o = some (r, m') → CrOK m' ∧ (r.headD 0 = 0 ∨ r.headD 0 = 1)

theorem ite01 (c : Prop) [Decidable c] : (if c then (1 : Word) else 0) = 0 ∨
    (if c then (1 : Word) else 0) = 1 := by
  split <;> simp

/-- A read-only callee with a `0`/`1` answer. -/
theorem cg_ro {n : Nat} {f : FnName} {vs : List Word} {m : Mem}
    (hf : f ∈ ["cr_leaf", "is_str_lit", "cr_lit_pins", "pin_found", "env_find", "env_row_get",
      "env_ix", "pin_at"])
    (h01 : ∀ r m', callW crfP n f vs m = some (r, m') → r.headD 0 = 0 ∨ r.headD 0 = 1)
    (hc : CrOK m) : CG (callW crfP n f vs m) := fun r m' h =>
  have hfr := (run_memFrame crfRO_closed hf (run_of_callW h)).1
  let ⟨mp, hm⟩ := hc
  ⟨⟨mp, memoRV_frame (S := crSch) (hS := crSch_wf) (K := bmKey) (VR := CrV) [] [] (by simp)
    (by simp) m m' hfr (fun _ _ h => h) mp hm⟩, h01 r m' h⟩

theorem envFind_01 {n : Nat} {m m' : Mem} {w vis : Word} {r : List Word}
    (h : callW crfP n "env_find" [w, vis] m = some (r, m')) : r.headD 0 = 0 ∨ r.headD 0 = 1 := by
  obtain ⟨s', -, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_specW crfP crfP_prog.eix crfP_prog.erg crfP_prog.ef n _ w vis) h
  exact envFindW_01 hW

theorem clpL_01 {k : Nat} {vis : Word} (ks : List Word) :
    ∀ (z : Bool) (o : Option (List Word × Mem)) (r : List Word) (m' : Mem),
    clpL crfP k vis z ks o = some (r, m') → r.headD 0 = 0 ∨ r.headD 0 = 1 := by
  induction ks with
  | nil =>
    intro z o r m' h
    rcases o with _ | ⟨r₀, m₀⟩
    · cases h
    simp only [clpL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [List.headD_cons]; split <;> simp
  | cons k' ks ih =>
    intro z o r m' h
    rcases o with _ | ⟨r₀, m₀⟩
    · cases h
    exact ih _ _ r m' h

theorem leaf_01 {n : Nat} {m m' : Mem} {vis g x h : Word} {r : List Word}
    (hc : callW crfP n "cr_leaf" [vis, g, x, h] m = some (r, m')) :
    r.headD 0 = 0 ∨ r.headD 0 = 1 := by
  rcases n with _ | k
  · rw [callW_zero] at hc; cases hc
  have hW := callW_model (M := fun mm => clW crfP k mm vis g x h) (cl_spec crfP crfP_prog k · vis g x h) hc
  simp only [clW] at hW
  split at hW
  · cases hi : callW crfP k "is_str_lit" [h] m with
    | none => rw [hi] at hW; cases hW
    | some q =>
    rw [hi] at hW
    cases hl : callW crfP k "cr_lit_pins" [vis, q.1.headD 0] q.2 with
    | none => simp only [ntBW, hl] at hW; cases hW
    | some q' =>
    simp only [ntBW, hl, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, -⟩ := hW
    simp only [List.headD_cons]
    rcases k with _ | k
    · rw [callW_zero] at hl; cases hl
    have hP := callW_model (M := fun mm => clpW crfP k mm vis (q.1.headD 0))
      (clp_spec crfP crfP_prog k · vis _) hl
    simp only [clpW] at hP
    split at hP <;> exact clpL_01 _ _ _ _ _ hP
  split at hW
  · cases he : callW crfP k "env_find" [x, vis] m with
    | none => rw [he] at hW; cases hW
    | some q =>
    obtain ⟨re, me⟩ := q
    simp only [ntBW, he, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, -⟩ := hW
    simpa using envFind_01 he
  · simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, -⟩ := hW
    simp

/-- The tail records a `0`/`1` word at an accepted handle. -/
theorem crfT_ok {k : Nat} {m m' : Mem} {h w : Word} {r : List Word} (hM : CrOK m)
    (hh : h.toNat < 2 ^ 32) (hw : w = 0 ∨ w = 1) (hc : crfT crfP k m h w = some (r, m')) :
    CrOK m' ∧ (r.headD 0 = 0 ∨ r.headD 0 = 1) := by
  obtain ⟨memo, hM⟩ := hM
  rcases hw with rfl | rfl
  · obtain ⟨rfl, hM', -⟩ := crfT_callW crfP_prog (b := false) hM hh rfl hc
    exact ⟨⟨_, hM'⟩, by simp⟩
  · obtain ⟨rfl, hM', -⟩ := crfT_callW crfP_prog (b := true) hM hh rfl hc
    exact ⟨⟨_, hM'⟩, by simp⟩

section arms
variable {k : Nat} {vis f h : Word}

theorem cg_fv {o : Option (List Word × Mem)} (ho : CG o) (hh : h.toNat < 2 ^ 32) :
    CG (crfFv crfP k h o) := by
  intro r m' hc
  rcases o with _ | ⟨ra, ma⟩
  · cases hc
  obtain ⟨hM, h01⟩ := ho _ _ rfl
  exact crfT_ok hM hh h01 hc

theorem cg_b2 {a : Word} {o : Option (List Word × Mem)} (ho : CG o) (hh : h.toNat < 2 ^ 32) :
    CG (crfB2 crfP k h a o) := by
  intro r m' hc
  rcases o with _ | ⟨rb, mb⟩
  · cases hc
  exact crfT_ok (ho _ _ rfl).1 hh (ite01 _) hc

theorem cg_l3 {a b : Word} {o : Option (List Word × Mem)} (ho : CG o) (hh : h.toNat < 2 ^ 32) :
    CG (crfL3 crfP k h a b o) := by
  intro r m' hc
  rcases o with _ | ⟨rc, mc⟩
  · cases hc
  exact crfT_ok (ho _ _ rfl).1 hh (ite01 _) hc

theorem cg_p2 {x : Word} {o : Option (List Word × Mem)} (ho : CG o) (hh : h.toNat < 2 ^ 32) :
    CG (crfP2 crfP k h x o) := by
  intro r m' hc
  rcases o with _ | ⟨re, me⟩
  · cases hc
  exact crfT_ok (ho _ _ rfl).1 hh (ite01 _) hc

theorem cg_p1 {x : Word} {o : Option (List Word × Mem)} (ho : CG o) (hh : h.toNat < 2 ^ 32) :
    CG (crfP1 crfP k vis h x o) := by
  intro r m' hc
  rcases o with _ | ⟨rr, mr⟩
  · cases hc
  exact cg_p2 (cg_ro (by simp) (fun _ _ he => envFind_01 he) (ho _ _ rfl).1) hh r m' hc

variable (ih : ∀ m vis f h, CrOK m → CG (callW crfP k "crf_go" [vis, f, h] m))
include ih

theorem cg_b1 {y : Word} {o : Option (List Word × Mem)} (ho : CG o) (hh : h.toNat < 2 ^ 32) :
    CG (crfB1 crfP k vis f h y o) := by
  intro r m' hc
  rcases o with _ | ⟨ra, ma⟩
  · cases hc
  exact cg_b2 (ih _ _ _ _ (ho _ _ rfl).1) hh r m' hc

theorem cg_l2 {w a : Word} {o : Option (List Word × Mem)} (ho : CG o) (hh : h.toNat < 2 ^ 32) :
    CG (crfL2 crfP k vis f h w a o) := by
  intro r m' hc
  rcases o with _ | ⟨rb, mb⟩
  · cases hc
  exact cg_l3 (ih _ _ _ _ (ho _ _ rfl).1) hh r m' hc

theorem cg_l1 {y w : Word} {o : Option (List Word × Mem)} (ho : CG o) (hh : h.toNat < 2 ^ 32) :
    CG (crfL1 crfP k vis f h y w o) := by
  intro r m' hc
  rcases o with _ | ⟨ra, ma⟩
  · cases hc
  exact cg_l2 ih (ih _ _ _ _ (ho _ _ rfl).1) hh r m' hc

theorem cg_n {m : Mem} {rv : List Word} (hM : CrOK m) (hh : h.toNat < 2 ^ 32) :
    CG (crfN crfP k m vis f h rv) := by
  unfold crfN
  split
  · exact cg_fv (ih _ _ _ _ hM) hh
  split
  · exact cg_b1 ih (ih _ _ _ _ hM) hh
  split
  · exact cg_l1 ih (ih _ _ _ _ hM) hh
  · exact cg_p1 (ih _ _ _ _ hM) hh

end arms

/-- **`crf_go` keeps the walk memo related, from any memory**, and answers `0`/`1`. -/
theorem crfGo_keep : ∀ n m vis f h, CrOK m → CG (callW crfP n "crf_go" [vis, f, h] m) := by
  intro n
  induction n with
  | zero => intro m vis f h _ r m' hc; rw [callW_zero] at hc; cases hc
  | succ k ih =>
  intro m vis f h hM r m' hc
  have hW := callW_model (M := fun mm => crfW crfP k mm vis f h) (crf_spec crfP crfP_prog k · vis f h) hc
  simp only [crfW] at hW
  split at hW
  · cases hW
  obtain ⟨⟨rv, mv⟩, hv, hW⟩ := of_K hW rfl
  obtain ⟨s', hmv, hs', hne, hrv⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (eView_spec crfP crfP_prog.view k _ h) hv
  subst hs'
  simp only at hmv hrv
  subst hmv hrv
  have hh : h.toNat < 2 ^ 32 := by
    refine Classical.byContradiction fun hc' => hne ?_
    rw [eViewW, ite_eq_left (UInt64.lt_iff_toNat_lt.mpr (by simp; omega))]
  simp only [crfV] at hW
  split at hW
  · exact cg_ro (by simp) (fun _ _ hl => leaf_01 hl) hM |> fun hg => by
      rcases hl : callW crfP k "cr_leaf" _ m with _ | ⟨rl, ml⟩
      · rw [hl] at hW; cases hW
      rw [hl] at hW
      simp only [crfLf, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl⟩ := hW
      exact ⟨(hg _ _ hl).1, by simpa using (hg _ _ hl).2⟩
  obtain ⟨⟨rf, mf⟩, hfd, hW⟩ := of_K hW rfl
  obtain ⟨s', hmf, hs', hne', hrf⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (memoFindG_spec crSch crfP "crm_find" crfP_prog.find k _ h 0) hfd
  subst hs'
  simp only at hmf hrf
  subst hmf hrf
  simp only [crfM] at hW
  split at hW
  · rename_i hhit
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨memo, hR⟩ := hM
    obtain ⟨bv, -, hw⟩ := memoRV_hit crSch bmKey CrV m memo hR h 0 hne' hhit ⟨hh, rfl⟩
    refine ⟨⟨memo, hR⟩, ?_⟩
    simp only [List.headD_cons]
    change mvG crSch m _ = 0 ∨ mvG crSch m _ = 1
    rw [hw]; exact ite01 _
  · exact cg_n (fun m vis f h hM => ih m vis f h hM) hM hh r m' hW

/-- `consts_resolve_ffast` at any arguments (the missing ones read `0`). -/
theorem crff_specA (p : Prog) (hp : CrfProg p) (k : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "consts_resolve_ffast" args
    ⦃fun r s' => LocEq s' s₀ ∧
      crffW p k s₀.mem (args.getD 0 0) (args.getD 1 0) = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.entry]
  simp only [callFn, constsResolveFFastL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p k "crm_clear",
      callW_spec p k "crf_go"] <;>
    finish (gen := 20) [crffW, ntBW, Locals.init]

/-- **`consts_resolve_ffast` keeps its memo well formed** from any memory (its model `crfF`). -/
theorem crfF_keepsCrOK {m m' : Mem} {args r : List Word} (h : crfF m args = some (r, m'))
    (hc : CrOK m) : CrOK m' := by
  obtain ⟨n, hn⟩ := callF_run h
  rcases n with _ | k
  · rw [callW_zero] at hn; cases hn
  have hW := callW_model (M := fun mm => crffW crfP k mm (args.getD 0 0) (args.getD 1 0))
    (crff_specA crfP crfP_prog k · args) hn
  simp only [crffW] at hW
  rcases h1 : callW crfP k "crm_clear" [] m with _ | ⟨rc, mc⟩
  · rw [h1] at hW; cases hW
  rw [h1] at hW
  obtain ⟨s', hmc, -, hw, hclr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (memoClearG_spec crSch crfP "crm_clear" crfP_prog.clear k _) h1
  simp only at hw hclr
  subst hmc
  obtain ⟨memo, hM⟩ := hc
  have hMc : CrOK s'.mem := ⟨∅, hclr ▸ memoRV_clear crSch crSch_wf bmKey CrV m memo hM hw⟩
  cases h2 : callW crfP k "crf_go" [args.getD 0 0, 4000000000, args.getD 1 0] s'.mem with
  | none => simp only [ntBW, h2] at hW; cases hW
  | some q =>
  simp only [ntBW, h2, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨-, rfl⟩ := hW
  exact (crfGo_keep _ _ _ _ _ hMc _ _ h2).1

end L.Ind
