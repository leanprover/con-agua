import ConAgua.Arena.DeclArmQuot

/-!
# The axiom arm `check_decl_axiom(i, vis)` (lane `decls3`)

`checkDecl`'s `.axiomDecl` arm: `Quot.sound` against the pinned quotient block (installing
nothing; `ci_canon_eq`, taken as the hypothesis `CiCanonSpec` until helper `decls3-canon` lands
it), else the constant check and the five recognised axioms (`std_axiom_ok`, `Lean.trustCompiler`,
the `ofReduce*` pair), `propext`/`choice` of another shape and every other axiom declining,
`sorryAx` skipped. Through the ROM stubs and the core's.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsR DeclAt CVAt dw)

/-- What `ci_canon_eq` must refine (helper `decls3-canon`'s statement shape). -/
def CiCanonSpec (p : Prog) : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (x y : Word)
    (c c' : IConstantInfo),
    RefAM p "ci_canon_eq" [x, y]
      (fun m a => StageR dn vis fe m a ∧ decCI (erA m) dn x.toNat = some c ∧
        decCI (erA m) dn y.toNat = some c')
      (c.canonEq c') (KeepPost dn vis fe decW0B)

section model
variable (p : Prog) (n : Nat) (vis : Word)

/-- After a push: its view. -/
def cdaRet : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- A recognised axiom: abort unless its test passed, then the push. -/
def cdaT (c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else cdaRet (callW p n "env_push" [vis, c] m)

/-- After the `sorryAx` pin. -/
def cdaK10 (nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if nm = r.headD 0 then some ([vis], m) else none

/-- After the `choice` pin: `propext`/`choice` of another shape decline. -/
def cdaK9 (nm a : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if nm = a ∨ nm = r.headD 0 then none else cdaK10 vis nm (pinAtW m 13)

/-- After the `propext` pin. -/
def cdaK8 (nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cdaK9 vis nm (r.headD 0) (pinAtW m 33)

/-- After the `ofReduceBool` pin. -/
def cdaK7 (c nm a : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if nm = a ∨ nm = r.headD 0 then cdaT p n vis c (callW p n "of_reduce_ax_ok" [vis, c + 1] m)
    else cdaK8 vis nm (pinAtW m 32)

/-- After the `ofReduceNat` pin. -/
def cdaK6 (c nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cdaK7 p n vis c nm (r.headD 0) (pinAtW m 46)

/-- After the `trustCompiler` pin. -/
def cdaK5 (c nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if nm = r.headD 0 then cdaT p n vis c (callW p n "trust_compiler_ok" [vis, c + 1] m)
    else cdaK6 p n vis c nm (pinAtW m 45)

/-- After `std_axiom_ok`. -/
def cdaK4 (c nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then cdaRet (callW p n "env_push" [vis, c] m)
    else cdaK5 p n vis c nm (pinAtW m 42)

/-- After `check_constant_val`. -/
def cdaK3 (c nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => cdaK4 p n vis c nm (callW p n "std_axiom_ok" [vis, c + 1] m)

/-- `Quot.sound`: after `ci_canon_eq`. -/
def cdaQ2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else some ([vis], m)

/-- `Quot.sound`: after the block's read. -/
def cdaQ1 (c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.tail.headD 0 ≤ 4 then none
    else cdaQ2 vis (callW p n "ci_canon_eq" [c, rdW (m.arr64 IW) (r.headD 0 + 4)] m)

/-- After the `Quot.sound` pin. -/
def cdaK2 (c nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if nm = r.headD 0 then cdaQ1 p n vis c (stubM "rom_basis_decls" m [4])
    else cdaK3 p n vis c nm (callW p n "check_constant_val" [vis, c + 1] m)

/-- After `erec_ci`. -/
def cdaK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    cdaK2 p n vis (r.headD 0) (rdW (m.arr64 EREC) (r.headD 0 + 1)) (pinAtW m 4)

end model

/-- **The model of `check_decl_axiom(i, vis)`.** -/
def cdaW (p : Prog) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, i, vis => cdaK1 p n vis (erecCiW n m i 0)

section arms
variable (p : Prog) (n : Nat) (vis i c nm a : Word) (r : List Word) (m : Mem)
theorem cdaW_step : cdaW p (n + 1) m i vis = cdaK1 p n vis (erecCiW n m i 0) := rfl
theorem cdaK1_some : cdaK1 p n vis (some (r, m)) =
    cdaK2 p n vis (r.headD 0) (rdW (m.arr64 EREC) (r.headD 0 + 1)) (pinAtW m 4) := rfl
theorem cdaK2_some : cdaK2 p n vis c nm (some (r, m)) =
    if nm = r.headD 0 then cdaQ1 p n vis c (stubM "rom_basis_decls" m [4])
    else cdaK3 p n vis c nm (callW p n "check_constant_val" [vis, c + 1] m) := rfl
theorem cdaQ1_some : cdaQ1 p n vis c (some (r, m)) =
    if r.tail.headD 0 ≤ 4 then none
    else cdaQ2 vis (callW p n "ci_canon_eq" [c, rdW (m.arr64 IW) (r.headD 0 + 4)] m) := rfl
theorem cdaQ2_some : cdaQ2 vis (some (r, m)) = if r.headD 0 = 0 then none else some ([vis], m) :=
  rfl
theorem cdaK3_some : cdaK3 p n vis c nm (some (r, m)) =
    cdaK4 p n vis c nm (callW p n "std_axiom_ok" [vis, c + 1] m) := rfl
theorem cdaK4_some : cdaK4 p n vis c nm (some (r, m)) =
    if r.headD 0 ≠ 0 then cdaRet (callW p n "env_push" [vis, c] m)
    else cdaK5 p n vis c nm (pinAtW m 42) := rfl
theorem cdaK5_some : cdaK5 p n vis c nm (some (r, m)) =
    if nm = r.headD 0 then cdaT p n vis c (callW p n "trust_compiler_ok" [vis, c + 1] m)
    else cdaK6 p n vis c nm (pinAtW m 45) := rfl
theorem cdaK6_some : cdaK6 p n vis c nm (some (r, m)) =
    cdaK7 p n vis c nm (r.headD 0) (pinAtW m 46) := rfl
theorem cdaK7_some : cdaK7 p n vis c nm a (some (r, m)) =
    if nm = a ∨ nm = r.headD 0 then cdaT p n vis c (callW p n "of_reduce_ax_ok" [vis, c + 1] m)
    else cdaK8 vis nm (pinAtW m 32) := rfl
theorem cdaK8_some : cdaK8 vis nm (some (r, m)) = cdaK9 vis nm (r.headD 0) (pinAtW m 33) := rfl
theorem cdaK9_some : cdaK9 vis nm a (some (r, m)) =
    if nm = a ∨ nm = r.headD 0 then none else cdaK10 vis nm (pinAtW m 13) := rfl
theorem cdaK10_some : cdaK10 vis nm (some (r, m)) = if nm = r.headD 0 then some ([vis], m) else none :=
  rfl
theorem cdaT_some : cdaT p n vis c (some (r, m)) =
    if r.headD 0 = 0 then none else cdaRet (callW p n "env_push" [vis, c] m) := rfl
theorem cdaRet_some : cdaRet (some (r, m)) = some ([r.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] cdaW_step => cdaW p (n + 1) m i vis
grind_pattern [ind_grind] cdaK1_some => cdaK1 p n vis (some (r, m))
grind_pattern [ind_grind] cdaK2_some => cdaK2 p n vis c nm (some (r, m))
grind_pattern [ind_grind] cdaQ1_some => cdaQ1 p n vis c (some (r, m))
grind_pattern [ind_grind] cdaQ2_some => cdaQ2 vis (some (r, m))
grind_pattern [ind_grind] cdaK3_some => cdaK3 p n vis c nm (some (r, m))
grind_pattern [ind_grind] cdaK4_some => cdaK4 p n vis c nm (some (r, m))
grind_pattern [ind_grind] cdaK5_some => cdaK5 p n vis c nm (some (r, m))
grind_pattern [ind_grind] cdaK6_some => cdaK6 p n vis c nm (some (r, m))
grind_pattern [ind_grind] cdaK7_some => cdaK7 p n vis c nm a (some (r, m))
grind_pattern [ind_grind] cdaK8_some => cdaK8 vis nm (some (r, m))
grind_pattern [ind_grind] cdaK9_some => cdaK9 vis nm a (some (r, m))
grind_pattern [ind_grind] cdaK10_some => cdaK10 vis nm (some (r, m))
grind_pattern [ind_grind] cdaT_some => cdaT p n vis c (some (r, m))
grind_pattern [ind_grind] cdaRet_some => cdaRet (some (r, m))

set_option maxHeartbeats 3200000 in
theorem cda_specW (p : Prog) (hp : p.lookup "check_decl_axiom" = some checkDeclAxiom)
    (hR : RecProg p) (hpa : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (i vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl_axiom" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ cdaW p n s₀.mem i vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDeclAxiom]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erecCi_specW p hR n,
        pinAt_specW p hpa n, stubM_spec p "rom_basis_decls" n, callW_spec p n "ci_canon_eq",
        callW_spec p n "check_constant_val", callW_spec p n "std_axiom_ok",
        callW_spec p n "env_push", callW_spec p n "trust_compiler_ok",
        callW_spec p n "of_reduce_ax_ok"] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, pinAtW]

end L.Arena
