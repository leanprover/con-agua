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

/-- The top of a tier is inside its array. -/
theorem IWOK.topOf {m : Mem} (h : IWOK m) (a : Word) : erTopOf m a ≤ (m.arr64 (erTier a)).size ∧
    (m.arr64 (erTier a)).size < 2 ^ 40 := by
  unfold erTopOf erTier; split
  · exact ⟨h.er, h.erCap⟩
  · exact ⟨h.er1, h.er1Cap⟩

/-- **Words written into the region allocated above a base state's top** (`wrER`, the record's
`erec_put`s in order): `StageR` kept (`StageR.putFresh` at each), the growth and the frame from the
base kept, the words read back, every other address as before. -/
theorem wrER_fresh {vis : Word} {fe : IFEnv} {m₀ : Mem} {a₀ : AState} (h₀ : StageR vis fe m₀ a₀) :
    ∀ (ws : List Word) (m : Mem) (a : AState) (d : Word), StageR vis fe m a →
    MemFrame quotA quotC m₀ m → IWGrow m₀ m → erTopOf m₀ d ≤ erOff d →
    erOff d + ws.length ≤ erTopOf m d → d.toNat < 2 ^ 41 →
    StageR vis fe (wrER m d ws) a ∧ IWGrow m₀ (wrER m d ws) ∧ MemFrame quotA quotC m₀ (wrER m d ws) ∧
      (∀ j < ws.length, erecP (wrER m d ws) (d.toNat + j) = ws[j]?) ∧
      (∀ i, (∀ j < ws.length, i % 2 ^ 41 ≠ (d.toNat + j) % 2 ^ 41) →
        erecP (wrER m d ws) i = erecP m i)
  | [], m, a, d, hS, hf, hg, _, _, _ => ⟨hS, hg, hf, fun j hj => by simp at hj, fun i _ => rfl⟩
  | x :: ws, m, a, d, hS, hf, hg, hd0, hdt, hd41 => by
    simp only [List.length_cons] at hdt
    obtain ⟨hS1, hg1, hf1⟩ := StageR.putFresh h₀ hS hf hg hd0 (v := x)
    have ⟨htop, hcap⟩ := hS.iw.topOf d
    have hself : erecP (erecPutMem m d x) d.toNat = some x :=
      erecP_putMem_self (by omega) (by omega)
    have hc1 := erecPutMem_ctl m d x
    cases ws with
    | nil =>
      refine ⟨hS1, hg1, hf1, fun j hj => ?_, fun i hi => ?_⟩
      · obtain rfl : j = 0 := by simp at hj; omega
        simpa [wrER] using hself
      · exact erecP_putMem_other (by have := hi 0 (by simp); simpa using this)
    | cons y ws =>
    simp only [List.length_cons] at hdt
    have hoff : erOff d + 1 < 2 ^ 40 := by omega
    have h64 : d.toNat + 1 < 2 ^ 64 := by unfold erOff at hoff; omega
    obtain ⟨ho, ht⟩ := erOff_succ hoff h64
    have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hbit : (d + 1).toNat / 2 ^ 40 % 2 = d.toNat / 2 ^ 40 % 2 := by
      rw [hd1]; unfold erOff at hoff; omega
    have hT : ∀ m' : Mem, erTopOf m' (d + 1) = erTopOf m' d := fun m' => by
      simp only [erTopOf, hbit]
    have hT1 : erTopOf (erecPutMem m d x) d = erTopOf m d := by
      simp only [erTopOf, erecTop, erecTop1, hc1]
    obtain ⟨hS2, hg2, hf2, hrd, hout⟩ := wrER_fresh h₀ (y :: ws) _ a (d + 1) hS1 hf1 hg1
      (by rw [hT, ho]; omega) (by rw [hT, hT1, ho]; simp only [List.length_cons]; omega)
      (by rw [hd1]; unfold erOff at hoff; omega)
    have hU : wrER m d (x :: y :: ws) = wrER (erecPutMem m d x) (d + 1) (y :: ws) := rfl
    have hlt : ∀ j ≤ ws.length + 1, d.toNat + j < 2 ^ 41 := fun j hj => by
      unfold erOff at hdt; omega
    refine ⟨hS2, hg2, hf2, fun j hj => ?_, fun i hi => ?_⟩
    · rw [hU]
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem?_cons_zero]
        rw [hout _ (fun j hj => by
          rw [hd1]; simp only [List.length_cons] at hj
          have h1 := hlt (j + 1) (by omega)
          have h2 : d.toNat < 2 ^ 41 := hd41
          rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (by omega)]; omega)]
        exact hself
      | succ j =>
        simp only [List.getElem?_cons_succ]
        have := hrd j (by simp only [List.length_cons] at hj ⊢; omega)
        rw [hd1, show d.toNat + 1 + j = d.toNat + (j + 1) by omega] at this
        exact this
    · rw [hU, hout i (fun j hj => by
        rw [hd1]; have := hi (j + 1) (by simp only [List.length_cons] at hj ⊢; omega)
        rwa [show d.toNat + (j + 1) = d.toNat + 1 + j by omega] at this)]
      exact erecP_putMem_other (by have := hi 0 (by simp); simpa using this)

/-! ## The level-parameter functions leave the records and the core memos alone -/

/-- The call closure of `param_levels` and `er_to_iw` in `checkerProg` (`_tmp/p3r/plfns.lean`). -/
def plFns : List FnName := [
  "er_copy", "er_to_iw", "intern_ls", "intern_ls_iw", "intern_param", "iw_alloc", "iw_copy",
  "iw_pool", "limbs_eq", "lit_hash", "ls_find", "ls_match", "ls_push", "param_find", "param_levels",
  "param_levels_go", "param_push", "pool_room", "sl_cons", "sl_get"]

/-- The arrays `plFns` never writes: the record pool's tiers, the core memos `TwinOK` reads, the ROM
cache, the pins. -/
def plBad : List TieredArray :=
  [EREC, tier1 EREC, ILMEMO, ABMEMO, WSM, FLM, LSM, LPMEMO, LPLMEMO, LPLSMEMO, L.Rom.ROMC, PINS]

/-- The `CTL` words `plFns` never writes: the pool's tops, the core memos' control words. -/
def plBadC : List Word := [129, 130, 48, 50, 54, 56, 58, 152, 154, 156]

def plA : List TieredArray := checkerWordArrays.filter fun b => b ∉ plBad
def plC : List Word := ((List.range 256).map Nat.toUInt64).filter fun x => x ∉ plBadC

/-- **The program hypothesis** for `param_levels`, `er_to_iw`. -/
def PlClosed (p : Prog) : Prop := closedA p plA plC plFns = true

theorem plA_not {b : TieredArray} (h : b ∈ plBad) : b ∉ plA := by
  simp only [plA, List.mem_filter, decide_eq_true_eq, not_and]; exact fun _ h2 => h2 h

theorem plC_not {x : Word} (h : x ∈ plBadC) : x ∉ plC := by
  simp only [plC, List.mem_filter, decide_eq_true_eq, not_and]; exact fun _ h2 => h2 h

/-- A call of `plFns`: its frame, the records unchanged. -/
theorem callW_plFrame {p : Prog} (hcl : PlClosed p) {f : FnName} (hf : f ∈ plFns) {n : Nat}
    {vs : List Word} {m : Mem} {r : List Word} {m' : Mem} (h : callW p n f vs m = some (r, m')) :
    MemFrame plA plC m m' ∧ erecP m' = erecP m := by
  have hF := (run_memFrame hcl hf (run_of_callW h)).1
  exact ⟨hF, erecP_frame hF (plA_not (by simp [plBad])) (plA_not (by simp [plBad]))
    (plC_not (by simp [plBadC])) (plC_not (by simp [plBadC]))⟩

end L.Ind
