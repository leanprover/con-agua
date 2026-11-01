module

public import ConAgua.Arena.DeclArmQuot
public import ConAgua.Arena.DeclAxiomSpec
public import ConAgua.Arena.DeclAxiomSpec2
public import ConAgua.Arena.DeclAxiomSpec4
public import ConAgua.Arena.DeclValSpec
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclValRef

@[expose] public section

/-!
# The axiom arm `check_decl_axiom(i, vis)`: its lookups and leaves (lane `decls3`)

`checkDecl`'s `.axiomDecl` arm: `Quot.sound` against the pinned quotient block (installing
nothing; `ci_canon_eq`, helper `decls3-canon`'s `ciCanonEq_refines`, literals by handle: `LitInj`
from the twin state's `StateOK`, lane `decls4`), else the constant check and the five recognised
axioms (`std_axiom_ok`, `Lean.trustCompiler`, the `ofReduce*` pair), `propext`/`choice` of another
shape and every other axiom declining, `sorryAx` skipped. Here: the push at the stage relation,
the arm's lookups and its leaf calls; the unified model and refinement `cda_ref` are in
`DeclAxQuotT.lean`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)

local notation "V" => ConLeche.CheckMode.verified

/-- An `env_push` call of a decoded record, at the stage relation. -/
theorem push_call {p : Prog} (hRp : RecProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    {ci : IConstantInfo} (hc : callW p n "env_push" [vis, c] m = some (r, m'))
    (hS : StageR dn vis fe m a) (hci : decCI (erecP m) dn c.toNat = some ci) :
    StageR dn (r.headD 0) (fe.push ci) m' a ∧ IWGrow m m' := by
  obtain ⟨w, hw1, hwl, -⟩ := decCI_name hci
  have hcb : c.toNat + 1 < 2 ^ 64 := erecP_bound hw1 hS.iw
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 hcb
  have hw : (rdW (m.arr64 EREC) (c + 1)).toNat < 2 ^ 32 := by
    rw [rdW_of_get? hc1.symm (erecP_get hw1)]; exact hwl
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envPush_specW p hRp n ⟨m, Locals.init []⟩ vis c hw) hc
  rw [hs'] at hW
  exact envPushW_ok hW hS hci

/-- The lookups of the axiom arm. -/
structure AxProg (p : Prog) : Prop where
  quot : QuotProg p
  val : ValProg p
  std : StdProg2 p
  tco : TcoProg p
  ora : OraProg p
  cda : p.lookup "check_decl_axiom" = some checkDeclAxiom

/-- The calls of the axiom arm other than `erec_ci` and `check_constant_val` (all leaves of the
declaration loop: `cda_ref` carries the core's memos across them by their frame). -/
def cdaLeaves : List FnName :=
  ["rom_basis_decls", "ci_canon_eq", "std_axiom_ok", "env_push", "trust_compiler_ok",
    "of_reduce_ax_ok"]

end L.Arena
