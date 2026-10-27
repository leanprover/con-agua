import ConAgua.Checker.Prog
import ConAgua.Arena.DeclStepGo

/-!
# The declaration texts' agreement halves for the checker's program (lane `loopt2`)

`checkerProg` agrees with the texts (`cvgProg`, `ivProg`, `armText`) on their functions but
`openFns`: one lookup each, by `rfl`, in chunks of twelve (split from `LoopDecl.lean` to keep each
module's elaboration small). With `LoopDecl.lean`'s write sets: `CvgProg checkerProg`,
`IvProg checkerProg`, `ArmProg checkerProg`.
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-! ## The texts' agreement halves

`checkerProg` agrees with the texts on their functions but `openFns`: one lookup each, by `rfl`
(the elaborator and the kernel compare the names along `checkerProg`'s list), in chunks. -/

/-- `cvgFns` but `openFns`, part 0. -/
def cvgOwn0 : List FnName :=
  ["check_value_group", "iw_reset", "pin_word", "lvl_eq_c", "lq_find", "lvl_eq_rec", "lvl_eq",
   "lv_equiv", "lv_eq", "lv_node", "lv_simp", "lh_mk"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_cvgOwn0 : ∀ f ∈ cvgOwn0, checkerProg.lookup f = cvgProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `cvgFns` but `openFns`, part 1. -/
def cvgOwn1 : List FnName :=
  ["lv_comb", "lv_leq", "lv_rest", "lv_imax", "lv_cases", "lv_cases_at", "lv_subsimp", "lv_subst",
   "lv_imax_l", "lv_dist1", "lv_dist2", "lv_imax_r"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_cvgOwn1 : ∀ f ∈ cvgOwn1, checkerProg.lookup f = cvgProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `cvgFns` but `openFns`, part 2. -/
def cvgOwn2 : List FnName :=
  ["lq_put", "install_value_guards", "cv_lps", "er_to_iw", "iw_alloc", "er_copy"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_cvgOwn2 : ∀ f ∈ cvgOwn2, checkerProg.lookup f = cvgProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 100000 in
theorem cvgOwn_of : ∀ f ∈ cvgFns, f ∉ openFns →
    f ∈ cvgOwn0 ++ (cvgOwn1 ++ cvgOwn2) := by
  decide +kernel

theorem checkerProg_cvgAgree : ∀ f ∈ cvgFns, f ∉ openFns → checkerProg.lookup f = cvgProg.lookup f :=
  fun f hf ho => (List.mem_append.1 (cvgOwn_of f hf ho)).elim (checkerProg_cvgOwn0 f) fun h =>
    (List.mem_append.1 h).elim (checkerProg_cvgOwn1 f) (checkerProg_cvgOwn2 f)

/-- `ivFns` but `openFns`, part 0. -/
def ivOwn0 : List FnName :=
  ["install_value", "erec_ci", "erec_alloc", "dlp_copy", "install_header", "env_find",
   "env_row_get", "env_ix", "reserved_contains", "reserved_from", "cv_lps", "er_to_iw"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_ivOwn0 : ∀ f ∈ ivOwn0, checkerProg.lookup f = ivProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `ivFns` but `openFns`, part 1. -/
def ivOwn1 : List FnName :=
  ["iw_alloc", "er_copy", "sl_nodup", "sl_contains", "install_value_guards", "env_push",
   "env_row_set", "erec_vg"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_ivOwn1 : ∀ f ∈ ivOwn1, checkerProg.lookup f = ivProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 100000 in
theorem ivOwn_of : ∀ f ∈ ivFns, f ∉ openFns →
    f ∈ ivOwn0 ++ ivOwn1 := by
  decide +kernel

theorem checkerProg_ivAgree : ∀ f ∈ ivFns, f ∉ openFns → checkerProg.lookup f = ivProg.lookup f :=
  fun f hf ho => (List.mem_append.1 (ivOwn_of f hf ho)).elim (checkerProg_ivOwn0 f) (checkerProg_ivOwn1 f)

end L.Checker
