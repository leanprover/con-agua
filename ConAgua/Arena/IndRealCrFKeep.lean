module

import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.StageInst1
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.ConstsResolveFRefine2
public import ConAgua.Arena.IndRealCrF
import all ConAgua.Arena.ConstsResolveF
import all ConAgua.Arena.Env
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.Pins
import all ConAgua.Arena.WhnfIota
import ConAgua.Arena.IndRealMemoCr

@[expose] public section

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
    ["cr_leaf", "is_str_lit", "cr_lit_pins", "pin_found", "env_find", "env_row_get", "base_row_get",
      "pin_at"] = true := by decide +kernel

theorem crfP_brg : crfP.lookup "base_row_get" = some baseRowGetL := (ProgHas.refl crfP).get _

/-- What a returning call says: the walk memo related after, a `0`/`1` answer. -/
def CG (o : Option (List Word × Mem)) : Prop :=
  ∀ r m', o = some (r, m') → CrOK m' ∧ (r.headD 0 = 0 ∨ r.headD 0 = 1)

theorem ite01 (c : Prop) [Decidable c] : (if c then (1 : Word) else 0) = 0 ∨
    (if c then (1 : Word) else 0) = 1 := by
  split <;> simp

/-- A read-only callee with a `0`/`1` answer. -/
theorem cg_ro {n : Nat} {f : FnName} {vs : List Word} {m : Mem}
    (hf : f ∈ ["cr_leaf", "is_str_lit", "cr_lit_pins", "pin_found", "env_find", "env_row_get",
      "base_row_get", "pin_at"])
    (h01 : ∀ r m', callW crfP n f vs m = some (r, m') → r.headD 0 = 0 ∨ r.headD 0 = 1)
    (hc : CrOK m) : CG (callW crfP n f vs m) := fun r m' h =>
  have hfr := (run_memFrame crfRO_closed hf (run_of_callW h)).1
  let ⟨mp, hm⟩ := hc
  ⟨⟨mp, memoRV_frame (S := crSch) (hS := crSch_wf) (K := bmKey) (VR := CrV) [] [] (by simp)
    (by simp) m m' hfr (fun _ _ h => h) mp hm⟩, h01 r m' h⟩

theorem envFind_01 {n : Nat} {m m' : Mem} {w vis : Word} {r : List Word}
    (h : callW crfP n "env_find" [w, vis] m = some (r, m')) : r.headD 0 = 0 ∨ r.headD 0 = 1 := by
  obtain ⟨s', -, -, -, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_spec crfP L.Ind.crfP_prog.erg crfP_brg L.Ind.crfP_prog.ef n _ vis w) h
  subst hr
  unfold findRes; split <;> (try split) <;> simp

theorem clpW_01 {k : Nat} {m m' : Mem} {vis s : Word} {r : List Word}
    (h : clpW crfP k m vis s = some (r, m')) : r.headD 0 = 0 ∨ r.headD 0 = 1 := by
  have bind {o : Option (List Word × Mem)} {K : List Word → Mem → Option (List Word × Mem)}
      (h : ntBW o K = some (r, m')) : ∃ r₀ m₀, K r₀ m₀ = some (r, m') := by
    rcases o with _ | ⟨r₀, m₀⟩
    · cases h
    exact ⟨r₀, m₀, h⟩
  unfold clpW at h
  iterate 3 obtain ⟨_, _, h⟩ := bind h
  split at h
  · rw [ite_some01] at h; obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h); exact ite01 _
  iterate 7 obtain ⟨_, _, h⟩ := bind h
  rw [ite_some01] at h; obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h); exact ite01 _

theorem leaf_01 {n : Nat} {m m' : Mem} {vis g x h : Word} {r : List Word}
    (hc : callW crfP n "cr_leaf" [vis, g, x, h] m = some (r, m')) :
    r.headD 0 = 0 ∨ r.headD 0 = 1 := by
  rcases n with _ | k
  · rw [callW_zero] at hc; cases hc
  have hW := callW_model (M := fun mm => clW crfP k mm vis g x h) (cl_spec crfP L.Ind.crfP_prog k · vis g x h) hc
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
    exact clpW_01 (callW_model (M := fun mm => clpW crfP k mm vis (q.1.headD 0))
      (clp_spec crfP L.Ind.crfP_prog k · vis _) hl)
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
    (hh : h.toNat < 2 ^ 32) (hw : w = 0 ∨ w = 1) (hc : crfW.j1 crfP k h w m = some (r, m')) :
    CrOK m' ∧ (r.headD 0 = 0 ∨ r.headD 0 = 1) := by
  obtain ⟨memo, hM⟩ := hM
  rcases hw with rfl | rfl
  · obtain ⟨rfl, hM', -⟩ := crfT_callW L.Ind.crfP_prog (b := false) hM hh rfl hc
    exact ⟨⟨_, hM'⟩, by simp⟩
  · obtain ⟨rfl, hM', -⟩ := crfT_callW L.Ind.crfP_prog (b := true) hM hh rfl hc
    exact ⟨⟨_, hM'⟩, by simp⟩

theorem cg_bind {o : Option (List Word × Mem)} {K : List Word → Mem → Option (List Word × Mem)}
    (ho : CG o) (hK : ∀ r m, CrOK m → (r.headD 0 = 0 ∨ r.headD 0 = 1) → CG (K r m)) :
    CG (ntBW o K) := by
  intro r m' hc
  rcases o with _ | ⟨r₀, m₀⟩
  · cases hc
  obtain ⟨hM, h01⟩ := ho _ _ rfl
  exact hK r₀ m₀ hM h01 r m' hc

theorem cg_j1 {k : Nat} {m : Mem} {h w : Word} (hM : CrOK m) (hh : h.toNat < 2 ^ 32)
    (hw : w = 0 ∨ w = 1) : CG (crfW.j1 crfP k h w m) :=
  fun _ _ hc => crfT_ok hM hh hw hc

/-- **`crf_go` keeps the walk memo related, from any memory**, and answers `0`/`1`. -/
theorem crfGo_keep : ∀ n m vis f h, CrOK m → CG (callW crfP n "crf_go" [vis, f, h] m) := by
  intro n
  induction n with
  | zero => intro m vis f h _ r m' hc; rw [callW_zero] at hc; cases hc
  | succ k ih =>
  intro m vis f h hM r m' hc
  have hW := callW_model (M := fun mm => crfW crfP k mm vis f h) (crf_spec crfP L.Ind.crfP_prog k · vis f h) hc
  simp only [crfW] at hW
  split at hW
  · cases hW
  rcases hv : callW crfP k "e_view" [h] m with _ | ⟨rv, mv⟩
  · rw [hv] at hW; cases hW
  rw [hv, bW_some] at hW
  obtain ⟨s', hmv, hs', hne, hrv⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (eView_spec crfP L.Ind.crfP_prog.view k _ h) hv
  subst hs'
  simp only at hmv hrv
  subst hmv hrv
  have hh : h.toNat < 2 ^ 32 := by
    refine Classical.byContradiction fun hc' => hne ?_
    rw [eViewW, ite_eq_left (UInt64.lt_iff_toNat_lt.mpr (by simp; omega))]
  split at hW
  · exact cg_ro (by simp) (fun _ _ hl => leaf_01 hl) hM |> fun hg => by
      rcases hl : callW crfP k "cr_leaf" _ m with _ | ⟨rl, ml⟩
      · rw [hl] at hW; cases hW
      rw [hl, bW_some, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl⟩ := hW
      exact ⟨(hg _ _ hl).1, by simpa using (hg _ _ hl).2⟩
  rcases hfd : callW crfP k "crm_find" [h, 0] m with _ | ⟨rf, mf⟩
  · rw [hfd] at hW; cases hW
  rw [hfd, bW_some] at hW
  obtain ⟨hmf, hne', rfl⟩ := callW_memoFind L.Ind.crfP_prog.find hfd; subst mf
  split at hW
  · rename_i hhit
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨memo, hR⟩ := hM
    obtain ⟨bv, -, hw⟩ := memoRV_hit crSch bmKey CrV m memo hR h 0 hne' hhit ⟨hh, rfl⟩
    refine ⟨⟨memo, hR⟩, ?_⟩
    simp only [List.headD_cons]
    change mvG crSch m _ = 0 ∨ mvG crSch m _ = 1
    rw [hw]; exact ite01 _
  refine (?_ : CG _) r m' hW
  have ef := fun m (hM : CrOK m) x => cg_ro (n := k) (f := "env_find") (vs := [x, vis]) (by simp)
    (fun _ _ he => envFind_01 he) hM
  split
  · exact cg_bind (ih _ _ _ _ hM) fun _ _ hM1 h1 => cg_j1 hM1 hh h1
  split
  · exact cg_bind (ih _ _ _ _ hM) fun _ _ hM1 _ => cg_bind (ih _ _ _ _ hM1) fun _ _ hM2 _ => by
      split <;> exact cg_j1 hM2 hh (by simp)
  split
  · exact cg_bind (ih _ _ _ _ hM) fun _ _ hM1 _ => cg_bind (ih _ _ _ _ hM1) fun _ _ hM2 _ =>
      cg_bind (ih _ _ _ _ hM2) fun _ _ hM3 _ => by split <;> exact cg_j1 hM3 hh (by simp)
  · exact cg_bind (ih _ _ _ _ hM) fun _ _ hM1 _ => cg_bind (ef _ hM1 _) fun _ _ hM2 _ => by
      split <;> exact cg_j1 hM2 hh (by simp)

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
    (crff_specA crfP L.Ind.crfP_prog k · args) hn
  simp only [crffW] at hW
  rcases h1 : callW crfP k "crm_clear" [] m with _ | ⟨rc, mc⟩
  · rw [h1] at hW; cases hW
  rw [h1] at hW
  obtain ⟨s', hmc, -, hw, hclr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (memoClearG_spec crSch crfP "crm_clear" L.Ind.crfP_prog.clear k _) h1
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
