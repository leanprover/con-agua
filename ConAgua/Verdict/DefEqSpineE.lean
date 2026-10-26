import ConAgua.Verdict.DefEqLoopsE
import ConAgua.Verdict.DefEqLazyE

/-!
# `defeq_spine`'s error claim (lane `verdicts-b`, helper `k3`)

The error halves of `DefEqMidSpine.lean`: `spine_cmp` (a failure is `defeq_list_rev`'s, after the
level comparison ran ok), `defeq_spine2` (`spine_cmp`'s, after the two argument slices),
`defeq_spine` (`defeq_spine2`'s, after the two heads). `spine_head`, `get_app_args`, `lvls_eq_c`
are outside the verdict closure.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false

namespace L.Arena

/-! ## `spine_cmp` -/

l_model spineCmp_specE (p : Prog) (hf : p.lookup "spine_cmp" = some spineCmpL)
  fns [hf ↦ spineCmpE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`spine_cmp`'s error claim** (the error half of `spineCmp_refines`). -/
theorem spineCmp_refinesE (p : Prog) (hp : SpineDProg p) (hnv : closedNV p L.Checker.nvFns = true)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d nm us nm₂ us₂ ao an bo bn : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hnm : HW nm) (hnm₂ : HW nm₂) (hus : HW us)
    (hus₂ : HW us₂) (xs ys : List EIdx)
    (hx : SpineR s₀.mem ao an xs.toArray) (hy : SpineR s₀.mem bo bn ys.toArray)
    (hxt : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat)
    (hyt : bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpecE p (n + 1) "spine_cmp" [mode, vis, d, nm, us, nm₂, us₂, ao, an, bo, bn]
      (spineCmpT (coreKnot (decMode mode) fe id F) fe d.toNat (decI nm) (decI us) (decI nm₂) (decI us₂)
        xs ys) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (spineCmp_specE p hp.cmp (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d nm us nm₂ us₂ ao an bo bn) hc0 (Err.code_ne_of_cls hkc)
  have hS := hs.rel
  have hxl := slice_len hx
  have hyl := slice_len hy
  have hcond : (decI nm = (decI nm₂ : NIdx) ∧ xs.reverse.length = ys.reverse.length) ↔
      (nm = nm₂ ∧ an = bn) := by
    rw [List.length_reverse, List.length_reverse, hxl, hyl]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by have := decI_beq (k := .name) nm nm₂ hnm hnm₂; rw [h1, beq_self_eq_true] at this
                simpa using this, UInt64.toNat_inj.mp h2⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  unfold spineCmpT
  by_cases hc : nm = nm₂ ∧ an = bn
  · rw [spineCmpE.arm1 (hc1 := hc)] at hW
    have hc' : decI nm = (decI nm₂ : NIdx) ∧ xs.length = ys.length := by
      have := hcond.mpr hc; simpa using this
    rw [if_pos hc']
    cases hc2 : callE p n "lvls_eq_c" [us, us₂] s₀.mem with
    | error e =>
      rw [hc2, spineCmpE.k_lvls_eq_c.none] at hW; cases hW
      exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc2
    | ok q =>
    obtain ⟨rz, m₁⟩ := q
    rw [hc2] at hW
    obtain ⟨n₁, rfl⟩ := callE_succ hc2
    cases n₁ with
    | zero => exact absurd (callW_of_callE hc2) (lvlsEqC_one p hp.quick.lv _ _ _ _ _)
    | succ n₂ =>
    have e₁ := CoreSpec.of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (lvlsEqC_refines p hp.quick.lv n₂ ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb hS us us₂ hus
        hus₂) (callW_of_callE hc2)
    refine ErrClaim.bind_coreS e₁ (fun M₁ hS₁ hst₁ => ?_)
    by_cases h2 : 2 ≤ rz.headD 0
    · rw [spineCmpE.k_lvls_eq_c.arm1 (hc1 := h2)] at hW
      rw [decO_two h2]
      have h3 := tailE (spineCmpE.k_defeq_list_rev.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
      exact CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
        (defeqListRev_refinesE p hp.rev (n₂ + 1) (hk.mono (by omega)) (hkE.mono (by omega)) F
          (by omega) (by omega) _ _ dn vis fe M₁ eb mode d ao an bo bn ⟨hS₁, hs.mode4, hs.eb_mode⟩
          xs ys (hx.keep hst₁.size hst₁.below hxt hS.spn) (hy.keep hst₁.size hst₁.below hyt hS.spn)
          (hst₁.1 ▸ hxt) (hst₁.1 ▸ hyt)) h3
    · rw [spineCmpE.k_lvls_eq_c.arm2 (hc1 := h2), spineCmpE.j1.arm1] at hW; cases hW
  · rw [spineCmpE.arm2 (hc1 := hc), spineCmpE.j1.arm1] at hW; cases hW

/-! ## `defeq_spine2` -/

l_model defeqSpine2_specE (p : Prog) (hf : p.lookup "defeq_spine2" = some defeqSpine2L)
  fns [hf ↦ defeqSpine2E] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`defeq_spine2`'s error claim** (the error half of `defeqSpine2_refines`). -/
theorem defeqSpine2_refinesE (p : Prog) (hp : SpineDProg p) (hnv : closedNV p L.Checker.nvFns = true)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b nm us nm₂ us₂ : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hnm : HW nm) (hnm₂ : HW nm₂)
    (hus : HW us) (hus₂ : HW us₂) :
    CoreSpecE p (n + 1) "defeq_spine2" [mode, vis, d, a, b, nm, us, nm₂, us₂]
      (spine2T (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (decI nm) (decI us)
        (decI nm₂) (decI us₂)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (defeqSpine2_specE p hp.sp2 (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b nm us nm₂ us₂) hc0 (Err.code_ne_of_cls hkc)
  rw [defeqSpine2E.arm1] at hW
  have hS := hs.rel
  cases hc1 : callE p n "get_app_args" [a] s₀.mem with
  | error e =>
    rw [hc1, defeqSpine2E.k_get_app_args.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1, defeqSpine2E.k_get_app_args.arm1] at hW
  obtain ⟨t₁, ht₁, -, hfr₁, hg₁, ho₁, htop₁, xs, hxs, hx₁⟩ := triple_of_callE
    (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (getAppArgs_refines p hp.spine n ⟨s₀.mem, Locals.init []⟩ a₀ hS.arena.1 a ha hS.spn) hc1
  rw [ht₁] at hfr₁ hg₁ htop₁ hx₁
  have hS₁ := hS.frame_stk hfr₁ (by simp) (by simp)
  cases hc2 : callE p n "get_app_args" [b] m₁ with
  | error e =>
    rw [hc2, defeqSpine2E.k_get_app_args_2.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2, defeqSpine2E.k_get_app_args_2.arm1] at hW
  obtain ⟨t₂, ht₂, -, hfr₂, hg₂, ho₂, htop₂, ys, hys, hy₂⟩ := triple_of_callE
    (s₀ := ⟨m₁, Locals.init []⟩)
    (getAppArgs_refines p hp.spine n ⟨m₁, Locals.init []⟩ a₀ hS₁.arena.1 b hb hS₁.spn) hc2
  rw [ht₂] at hfr₂ hg₂ htop₂ hy₂
  have hS₂ := hS₁.frame_stk hfr₂ (by simp) (by simp)
  have hb₁ := hx₁.bound
  have hb₂ := hy₂.bound
  have hsp₁ := hS₁.spn
  have htop₁' : (spTop m₁).toNat = (r₁.headD 0).toNat + (r₁.tail.headD 0).toNat := by
    rw [htop₁, UInt64.toNat_add, ← ho₁]; omega
  have htop₂' : (spTop m₂).toNat = (r₂.headD 0).toNat + (r₂.tail.headD 0).toNat := by
    have hsz₂ : (m₂.arr64 SPN).size = (m₁.arr64 SPN).size := hg₂.size
    rw [htop₂, UInt64.toNat_add, ← ho₂]; omega
  have hle : (spTop m₁).toNat ≤ (spTop m₂).toNat := UInt64.le_iff_toNat_le.mp hg₂.1
  have hx₂ := hx₁.keep hg₂.size hg₂.below (by omega) hsp₁
  have h3 := tailE (defeqSpine2E.k_spine_cmp.none p _) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  have hT : (spine2T (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (decI nm)
      (decI us) (decI nm₂) (decI us₂)).run a₀ = (spineCmpT (coreKnot (decMode mode) fe id F) fe
        d.toNat (decI nm) (decI us) (decI nm₂) (decI us₂) xs ys).run a₀ := by
    simp only [spine2T, StateT.run_bind, hxs, hys, except_ok_bind]
  refine ErrClaim.congr_run hT (ErrClaim.of_callE_succ h3 fun n' hn' h' => ?_)
  subst hn'
  exact CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
    (spineCmp_refinesE p hp hnv n' (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega)
      ⟨m₂, Locals.init []⟩ a₀ dn vis fe M eb mode d nm us nm₂ us₂ _ _ _ _ ⟨hS₂, hs.mode4, hs.eb_mode⟩
      hnm hnm₂ hus hus₂ xs ys hx₂ hy₂ (by show _ ≤ (spTop m₂).toNat; omega)
      (by show _ ≤ (spTop m₂).toNat; omega)) h'

/-! ## `defeq_spine` -/

l_model defeqSpine_specE (p : Prog) (hf : p.lookup "defeq_spine" = some defeqSpineL)
  fns [hf ↦ defeqSpineE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`defeq_spine`'s error claim** (`DefeqSpineE`). -/
theorem defeqSpine_refinesE (p : Prog) (hp : SpineDProg p) (hnv : closedNV p L.Checker.nvFns = true) :
    DefeqSpineE p := by
  intro n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (defeqSpine_specE p hp.sp (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  rw [defeqSpineE.arm1] at hW
  have hS := hs.rel
  rw [defeqSpine_eq]
  cases hc1 : callE p n "spine_head" [a] s₀.mem with
  | error e =>
    rw [hc1, defeqSpineE.k_spine_head.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc1
  | ok q =>
  obtain ⟨ra, m₁⟩ := q
  rw [hc1] at hW
  obtain ⟨k, rfl⟩ := callE_succ hc1
  obtain ⟨hm₁, hra, ⟨hra0, hra1, hra2⟩, hva⟩ := spineHead_run hp hS.arena.1 ha (callW_of_callE hc1)
  rw [hm₁] at hW
  simp only [defeqSpineE.k_spine_head] at hW
  by_cases h0 : ra.headD 0 = 0
  · rw [if_pos h0] at hW; cases hW
  rw [if_neg h0] at hW
  cases hc2 : callE p (k + 1) "spine_head" [b] s₀.mem with
  | error e =>
    rw [hc2, defeqSpineE.k_spine_head_2.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc2
  | ok q =>
  obtain ⟨rb, m₂⟩ := q
  rw [hc2] at hW
  obtain ⟨hm₂, hrb, ⟨hrb0, hrb1, hrb2⟩, hvb⟩ := spineHead_run hp hS.arena.1 hb (callW_of_callE hc2)
  rw [hm₂] at hW
  simp only [defeqSpineE.k_spine_head_2] at hW
  have hT₁ : ((spineHeadT (decE a) >>= fun o => match o with
      | none => pure false
      | some (n, us) => spineHeadT (decE b) >>= fun o' => match o' with
        | none => pure false
        | some (n', us') => spine2T (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)
            n us n' us') : AM Bool).run a₀ =
      ((match decSH rb with
        | none => pure false
        | some (n', us') => spine2T (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)
            (decI (ra.tail.headD 0)) (decI (ra.tail.tail.headD 0)) n' us') : AM Bool).run a₀ := by
    rw [StateT.run_bind, hra, except_ok_bind, decSH_some h0]
    simp only [StateT.run_bind, hrb, except_ok_bind]
  refine ErrClaim.congr_run hT₁ ?_
  by_cases h0' : rb.headD 0 = 0
  · rw [if_pos h0'] at hW; cases hW
  rw [if_neg h0'] at hW
  rw [decSH_some h0']
  have h3 := tailE (defeqSpineE.k_defeq_spine2.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  exact CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (defeqSpine2_refinesE p hp hnv k (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega)
      (by omega) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb mode d a b _ _ _ _
      ⟨hS, hs.mode4, hs.eb_mode⟩ ha hb hra1 hrb1 hra2 hrb2) h3

end L.Arena
