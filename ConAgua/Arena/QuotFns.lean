module

public import ConAgua.Arena.IndMaster
public import ConAgua.Arena.Frame
public import ConAgua.Arena.CoreErec
import ConAgua.Arena.DerRel

@[expose] public section

/-!
# The quotient pins' functions leave the environment alone (lane `ronsync2`, stage 3)

`quot_pin_hit` and `quot_at` allocate a record and fill it across calls (`cv_at_lps` writes into
the record its caller allocated, `ci_at_lps` writes the kind word, then the cv, then the rest). A
write below the current top keeps the stage relation only if no relation reads the written words:
`EnvR` is the one that reads records, and it reads the environment's. The program hypothesis
`QuotClosed p` (the call closure `quotFns` of `quot_pin_hit`, `quot_at` writes no array `EnvR` reads but
the record pool's tiers, no control word `EnvR` reads but the pool's tops; decided for the
checker's program in `ConAgua/Checker/QuotFns.lean`) gives every call's frame, and
`StageR.putFresh`: a write into the region allocated above a base state's tops keeps `StageR`,
`EnvR` taken from the base.
-/

namespace L.Ind

open ConRon.Arena
open L.Arena

/-- The call closure of `quot_pin_hit` and `quot_at` in `checkerProg`, a literal list (115
functions; `_tmp/p3r/qfns.lean` prints it). -/
def quotFns : List FnName := [
  "app_find", "app_push", "ci_at_lps", "const_find", "const_push", "cv_at_lps", "cv_eq", "cv_lps",
  "der_b", "ek_copy", "er_copy", "er_copy_er", "er_sl_eq", "er_to_iw", "erec_alloc", "erec_put",
  "fire_levels_at", "forall_find", "forall_push", "fvar_find", "fvar_push", "ilp_clear",
  "ilp_find", "ilp_put", "ilpl_clear", "ilpl_find", "ilpl_put", "ilpls_clear", "ilpls_find",
  "ilpls_put", "imax_find", "imax_push", "inst_lp", "inst_lp_core", "intern_app", "intern_const",
  "intern_forall", "intern_fvar", "intern_imax", "intern_lam", "intern_letE", "intern_ls",
  "intern_ls_iw", "intern_max", "intern_param", "intern_proj", "intern_sort", "intern_succ",
  "intern_zero", "iw_alloc", "iw_copy", "iw_pool", "keys_ok", "keys_push", "lam_find", "lam_push",
  "letE_find", "letE_push", "lh_mk", "limbs_eq", "lit_hash", "lp_app", "lp_forall", "lp_fvar",
  "lp_go", "lp_lam", "lp_let", "lp_let_tail", "lp_lookup", "lp_proj", "lp_rb_let", "lp_substl",
  "ls_find", "ls_match", "ls_node", "ls_push", "lv_intern", "lv_node", "lv_sub_int", "max_find",
  "max_push", "mk_app", "mk_forall", "mk_lam", "mk_let", "mk_proj", "param_find", "param_levels",
  "param_levels_go", "param_push", "pool_room", "proj_find", "proj_push", "quot_at", "quot_pin",
  "quot_pin_hit", "rom_basis_decls", "rules_at_lps_go", "sl_cons", "sl_contains", "sl_get",
  "sl_memo", "sl_nodup", "sle_go", "sls_go", "sls_memo", "sort_find", "sort_push", "spn_ls",
  "spn_pool", "spn_to_er", "succ_find", "succ_push", "zero_find", "zero_push"
]

/-- The arrays `quotFns` may write: the record pool's tiers and every array `EnvR` does not read. -/
def quotA : List TieredArray := checkerWordArrays.filter fun b => b.arr = 136 ∨ b ∉ envArrs

/-- The `CTL` words `quotFns` may write: the record pool's tops and every word `EnvR` does not
read. -/
def quotC : List Word :=
  ((List.range 256).filter fun i => i = 129 ∨ i = 130 ∨ i.toUInt64 ∉ envCtl).map Nat.toUInt64

/-- **The program hypothesis**: `quotFns` writes inside `quotA`, `quotC`. -/
def QuotClosed (p : Prog) : Prop := closedA p quotA quotC quotFns = true

theorem quotA_env : ∀ b ∈ quotA, b.arr = 136 ∨ b ∉ envArrs := by
  intro b hb; simp only [quotA, List.mem_filter, decide_eq_true_eq] at hb; exact hb.2

theorem quotC_env : ∀ x ∈ quotC, x = 129 ∨ x = 130 ∨ x ∉ envCtl := by
  intro x hx
  simp only [quotC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
  obtain ⟨i, ⟨hi, h⟩, rfl⟩ := hx
  rcases h with rfl | rfl | h
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr h)

theorem erec_quotA : (EREC : TieredArray) ∈ quotA ∧ tier1 EREC ∈ quotA := by
  simp only [quotA, List.mem_filter, decide_eq_true_eq]; decide

theorem ctl_quotC : (129 : Word) ∈ quotC ∧ (130 : Word) ∈ quotC := by decide

/-- A call of `quotFns`'s frame. -/
theorem callW_quotFrame {p : Prog} (hcl : QuotClosed p) {f : FnName} (hf : f ∈ quotFns) {n : Nat}
    {vs : List Word} {m : Mem} {r : List Word} {m' : Mem} (h : callW p n f vs m = some (r, m')) :
    MemFrame quotA quotC m m' :=
  (run_memFrame hcl hf (run_of_callW h)).1

/-- An `erec_put`'s frame inside `quotA`, `quotC`. -/
theorem erecPutMem_quotFrame (m : Mem) (a v : Word) : MemFrame quotA quotC m (erecPutMem m a v) :=
  (erecPutMem_frame m a v).mono (by simpa using erec_quotA) (by simp)

/-- `CheckR` across a writer of the record pool, `EnvR` given after it. -/
theorem _root_.L.Arena.CheckR.erEnv {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} (h : CheckR m a vis fe)
    (hf : MemFrame [EREC, tier1 EREC] [129, 130] m m') (he : EnvR m' vis fe) : CheckR m' a vis fe := by
  have hA : ∀ b ∈ [(EREC : TieredArray), tier1 EREC], 136 ≤ b.arr ∧ b.arr < 137 := by
    simp [EREC, tier1]
  have hC : ∀ x ∈ ([129, 130] : List Word), 129 ≤ x.toNat ∧ x.toNat < 131 := by simp
  have hlow : ∀ y ∈ arenaArrs, y.arr < 64 := by decide
  refine ⟨⟨?_, ?_⟩, h.core.frame (fun b hb => .inr (by have := hA b hb; omega)) (fun x hx => .inr (by have := hC x hx; omega)) hf,
    h.pins.frame (fun b hb => .inr (by have := hA b hb; omega)) hf, he,
    h.mode.frame hf (by decide) (by decide)⟩
  · exact ArenaR.frame (fun b hb hm => by have := hlow b hm; have := hA b hb; omega) (fun x hx => not_mem_arenaCtl x (by have := hC x hx; omega)) hf h.arena.base
  · exact DerR.frameM _ _ m m' hf (fun b hb => by have := hA b hb; omega) a h.arena.der

/-- **A write at or above a base state's top of its tier keeps the growth from the base.** -/
theorem IWGrow.put {m₀ m : Mem} {a v : Word} (hg : IWGrow m₀ m) (h : erTopOf m₀ a ≤ erOff a) :
    IWGrow m₀ (erecPutMem m a v) := by
  have hc := erecPutMem_ctl m a v
  have hI : (erecPutMem m a v).arr64 IW = m.arr64 IW := by
    rw [erecPutMem_arr, ite_eq_right_iff.mpr (fun e => absurd e ?_)]; unfold erTier; split <;> decide
  simp only [erTopOf, erOff] at h
  refine ⟨?_, ?_, fun i hi => by rw [hI]; exact hg.iwGet i hi, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · simp only [iwTop, hc]; exact hg.iw
  · simp only [erTop, hc]; exact hg.er
  · rw [erecPutMem_arr]; unfold erTier; split
    · rename_i e; simp only [e, ite_true] at h
      have : ¬ (a.toNat % 2 ^ 40 = i) := by have := hg.er; simp only [erTop, erecTop] at *; omega
      simp [Array.getElem?_setIfInBounds, erOff, this, hg.erGet i hi]
    · simp [hg.erGet i hi]
  · simp only [erecTop1, hc]; exact hg.er1
  · rw [erecPutMem_arr]; unfold erTier; split
    · simp [hg.er1Get i hi]
    · rename_i e; simp only [e, ite_false] at h
      have : ¬ (a.toNat % 2 ^ 40 = i) := by omega
      simp [Array.getElem?_setIfInBounds, erOff, this, hg.er1Get i hi]

/-- **A write into the region allocated above a base state's top keeps the stage relation**: the
base's `EnvR` (`EnvR.growF` over the frame from the base), the rest from the state before the
write; the growth and the frame from the base kept. -/
theorem StageR.putFresh {vis : Word} {fe : IFEnv} {m₀ m : Mem} {a₀ a : AState} {d v : Word}
    (h₀ : StageR vis fe m₀ a₀) (hS : StageR vis fe m a) (hf : MemFrame quotA quotC m₀ m)
    (hg : IWGrow m₀ m) (hd : erTopOf m₀ d ≤ erOff d) :
    StageR vis fe (erecPutMem m d v) a ∧ IWGrow m₀ (erecPutMem m d v) ∧
      MemFrame quotA quotC m₀ (erecPutMem m d v) := by
  have hg' := hg.put (v := v) hd
  have hf' := hf.trans (erecPutMem_quotFrame m d v)
  have he : EnvR (erecPutMem m d v) vis fe := h₀.check.env.growF hf' quotA_env quotC_env hg'.erecGrow
  have hfe : MemFrame [EREC, tier1 EREC] [129, 130] m (erecPutMem m d v) :=
    (erecPutMem_frame m d v).mono (fun _ h => h) (by simp)
  exact ⟨⟨hS.check.erEnv hfe he, IWOK.of_er (erecPutMem_frame m d v) hS.iw⟩, hg', hf'⟩

end L.Ind
