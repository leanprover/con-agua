module

public import ConAgua.Arena.GrindAttr
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.DeclStep
public import ConAgua.Checker.NoVerdictFns
public import ConAgua.Arena.Verdict
public import ConAgua.Arena.DeclHeader

@[expose] public section
/-!
# The declaration family's callees outside the verdict closure

`declNvList` (`declNv_mem`: in `nvFns`, so their failures claim nothing: `nvl`), and the reads of
the reserved-name table (`resFromW_hit`, `resContW_hit`) the value checks' refinements use.
(`install_header` is gone with the old twin's fold.)
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- The callees of the declaration family outside the verdict closure. -/
def declNvList : List FnName :=
  ["cv_lps", "loose_bvars_bounded_fast", "has_fvar_fast", "all_level_params_defined",
   "consts_resolve_ffast", "sl_nodup", "reserved_contains", "env_find", "env_push", "erec_ci",
   "reduce_stored_ok", "reduce_elem_ok", "reduce_pin_guard", "reduce_decl_pin", "reduce_cert_var",
   "mk_app", "pin_at", "flush_caches", "scratch_enter",
   "scratch_drop", "and_pin_ok", "rom_ci", "rom_basis_decls",
   "ci_to_cv", "ci_canon_eq", "cv_canon_eq", "std_axiom_ok", "trust_compiler_ok",
   "of_reduce_ax_ok", "sl_contains", "nat_op_names", "nat_op_guard", "nat_op_deps",
   "nat_div_mod_names", "rom_pin_sets", "ind_block_to_erec",
   "quot_pin_hit", "pin_word", "iw_reset"]

theorem declNv_mem : ∀ f ∈ declNvList, f ∈ L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

/-- A failing callee of the list claims nothing. -/
theorem nvl {p : Prog} (hnv : closedNV p L.Checker.nvFns = true) {α : Type} {T : AM α} {a : AState}
    {f : FnName} (hf : f ∈ declNvList) {n : Nat} {vs : List Word} {m : Mem} {e : Err}
    (h : callE p n f vs m = .error e) : ErrClaim T a e :=
  ErrClaim.of_callE_nv hnv (declNv_mem f hf) h

/-- A hit of `reserved_from`: one of the reserved words is `x`. -/
theorem resFromW_hit (n : Nat) : ∀ (m : Mem) (x j c : Word), j.toNat ≤ 16 → c ≠ 0 →
    resFromW n m x j = some c → ∃ i, i < 16 ∧ pinW m (55 + i) = x := by
  induction n with
  | zero => intro m x j c _ _ h; simp [resFromW] at h
  | succ n ih =>
    intro m x j c hj hc h
    rw [resFromW_step] at h
    have hn16 : ¬ 16 ≤ j := by
      by_cases h16 : 16 ≤ j
      · rw [ite_eq_left h16] at h; simp at h; exact absurd h.symm hc
      · exact h16
    rw [ite_eq_right hn16] at h
    have hj16 : j.toNat < 16 := by
      refine Classical.byContradiction fun hh => hn16 ?_
      rw [UInt64.le_iff_toNat_le]; simp; omega
    by_cases he : rdW (m.arr64 PINS) (55 + j) = x
    · refine ⟨j.toNat, hj16, ?_⟩
      have : (55 + j).toNat = 55 + j.toNat := by rw [UInt64.toNat_add]; simp; omega
      simpa [rdW, pinW, this] using he
    rw [ite_eq_right he] at h
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    exact ih m x (j + 1) c (by omega) hc h

/-- **A hit of `reserved_contains` is a hit of `reservedBasisNames`.** -/
theorem resContW_hit {m : Mem} {a : AState} {n : Nat} {x : Word}
    {c : Word} (hc : c ≠ 0) (h : resContW n m x = some c) (hP : PinsR m a.pins) :
    ∃ l, reservedBasisNames.run a = .ok (l, a) ∧ l.contains (decI x) = true := by
  cases n with
  | zero => simp [resContW] at h
  | succ n =>
  rw [resContW_step] at h
  by_cases h0 : pinW m 0 = 0
  · rw [ite_eq_left h0] at h; simp at h
  rw [ite_eq_right h0] at h
  have hF := hP.full h0
  refine ⟨_, pinReserved_run hF, ?_⟩
  obtain ⟨i, hi, e⟩ := resFromW_hit n m x 0 c (by simp) hc h
  simp only [List.contains_iff_mem, List.mem_map, List.mem_range]
  exact ⟨i, hi, by rw [e]⟩

end L.Arena
