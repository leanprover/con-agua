import ConAgua.Arena.StubInd
import ConAgua.Arena.DeclNatLit
import ConAgua.Arena.IndRealFvt

/-!
# `open_pis_at_fvars_f`'s model (lane `indproofs4`, helper `opf`)

The program- and fuel-free model `opfF := callF opfP "open_pis_at_fvars_f"` (the recipe of
`IndReal.lean`) over the call-closed program `opfP`: the entry, the one-pass walk `opf_go`, the
fallback `opa_go`, the stack push, the pool copy, `e_view`, `intern_fvar`, and the two walks
`inst_list` (`instListProg`) and `inst_entry` (`instProg`). Each L function's body is a word model
over its callees' runs (`callW`, the recipe of `IndRealFvt.lean`'s `gaaAdW`): `opfGoK`, `opaGoK`,
`opfTopK`, proved by `vcgen`. The refinement `opfF_ok` is in `IndRealOpf2.lean`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The program and the model -/

/-- `open_pis_at_fvars_f`'s functions and the walks it calls. -/
def opfP : Prog :=
  [("open_pis_at_fvars_f", L.Stubs.openPisAtFvarsFL), ("opf_go", L.Stubs.opfGo),
    ("opa_go", L.Stubs.opaGo), ("spn_push", L.Stubs.spnPush), ("iw_alloc", iwAlloc),
    ("spn_to_iw", spnToIwL), ("e_view", eView)] ++ fvarProg ++ instListProg ++ instProg

/-- The functions `open_pis_at_fvars_f` reaches. -/
def opfPFns : List FnName :=
  ["open_pis_at_fvars_f", "opf_go", "opa_go", "spn_push", "iw_alloc", "spn_to_iw", "e_view",
    "fvar_find", "fvar_push", "intern_fvar"] ++ instListFns ++ instFns

/-- What it writes: the stack, the pool, the `fvar` store, both walks' memos and stores. -/
def opfA : List ArrId := [SPN, IW, FVREC, FVSLOT, FVLP, FVREC + 256, FVSLOT + 256, FVLP + 256] ++ instListA ++ instA
/-- The stack's and the pool's tops, the `fvar` counts, both walks' words. -/
def opfC : List Word := [136, 200, 26, 27] ++ instListC ++ instC

theorem opfP_closed : closedA opfP opfA opfC opfPFns = true := by decide +kernel

/-- The program bundle. -/
abbrev OpfF (p : Prog) : Prop := ProgHas p opfP

/-- **The model of `open_pis_at_fvars_f`** (program- and fuel-free). -/
noncomputable def opfF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF opfP "open_pis_at_fvars_f" m args

theorem opfF_spec (p : Prog) (hp : OpfF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "open_pis_at_fvars_f" args
    ⦃fun r s' => LocEq s' s₀ ∧ opfF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec opfP_closed (hp.agree opfPFns) (by decide) n s₀ args

/-- `open_pis_at_fvars_f` writes only `opfA`, `opfC`. -/
theorem opfF_frame {m m' : Mem} {args r : List Word} (h : opfF m args = some (r, m')) :
    MemFrame opfA opfC m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame opfP_closed (by decide) (run_of_callW hc)).1

/-! ## The bodies over their callees' runs -/

/-- `spn_push(x)`'s model. -/
def spnPushW (m : Mem) (x : Word) : Option (List Word × Mem) :=
  if m.len64 SPN ≤ rdW (m.arr64 CTL) 136 then none
  else some ([0], (m.set64 SPN (rdW (m.arr64 CTL) 136) x).set64 CTL 136 (rdW (m.arr64 CTL) 136 + 1))

theorem spnPush_spec (p : Prog) (hp : p.lookup "spn_push" = some L.Stubs.spnPush) (n : Nat)
    (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "spn_push" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ spnPushW s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, L.Stubs.spnPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [spnPushW]

/-- `opf_go(n, e, i, co, cn)`'s body over its callees' runs. -/
def opfGoK (p : Prog) (k : Nat) (m : Mem) (n e i co cn : Word) : Option (List Word × Mem) :=
  if n = 0 then ntBW (callW p k "inst_list" [e, co, cn, 0] m) fun r m1 => some ([1, r.headD 0], m1)
  else if e >>> 28 ≠ 6 then some ([0, 0], m)
  else ntBW (callW p k "e_view" [e] m) fun rv m1 =>
    ntBW (callW p k "inst_list" [rv.tail.headD 0, co, cn, 0] m1) fun rd m2 =>
    ntBW (callW p k "intern_fvar" [i, rd.headD 0] m2) fun rf m3 =>
    ntBW (callW p k "spn_push" [rf.headD 0] m3) fun _ m4 =>
    ntBW (callW p k "opf_go" [n - 1, rv.tail.tail.headD 0, i + 1, co, cn + 1] m4) fun rb m5 =>
    some ([rb.headD 0, rb.tail.headD 0], m5)

theorem opfGoK_spec (p : Prog) (hp : p.lookup "opf_go" = some L.Stubs.opfGo) (k : Nat) (s₀ : St)
    (n e i co cn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "opf_go" [n, e, i, co, cn]
    ⦃fun r s' => LocEq s' s₀ ∧ opfGoK p k s₀.mem n e i co cn = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, L.Stubs.opfGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p k] <;>
    finish (gen := 20) [opfGoK, ntBW]

/-- `opa_go(n, e, i)`'s body over its callees' runs. -/
def opaGoK (p : Prog) (k : Nat) (m : Mem) (n e i : Word) : Option (List Word × Mem) :=
  if n = 0 then some ([1, e], m)
  else if e >>> 28 ≠ 6 then some ([0, 0], m)
  else ntBW (callW p k "e_view" [e] m) fun rv m1 =>
    ntBW (callW p k "intern_fvar" [i, rv.tail.headD 0] m1) fun rf m2 =>
    ntBW (callW p k "inst_entry" [rv.tail.tail.headD 0, rf.headD 0, 0] m2) fun rb m3 =>
    ntBW (callW p k "spn_push" [rf.headD 0] m3) fun _ m4 =>
    ntBW (callW p k "opa_go" [n - 1, rb.headD 0, i + 1] m4) fun ro m5 =>
    some ([ro.headD 0, ro.tail.headD 0], m5)

theorem opaGoK_spec (p : Prog) (hp : p.lookup "opa_go" = some L.Stubs.opaGo) (k : Nat) (s₀ : St)
    (n e i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "opa_go" [n, e, i]
    ⦃fun r s' => LocEq s' s₀ ∧ opaGoK p k s₀.mem n e i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, L.Stubs.opaGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p k] <;>
    finish (gen := 20) [opaGoK, ntBW]

/-- The common tail: the fresh pool slice, the copy of the stack slice, the stack top put back. -/
def opfTail (k : Nat) (n co b : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m2) => ntBW (s2iW k m2 q co n) fun _ m3 => some ([1, q, n, b], m3.set64 CTL 136 co)

theorem opfTail_some (k : Nat) (n co b q : Word) (m2 : Mem) :
    opfTail k n co b (some (q, m2)) =
      ntBW (s2iW k m2 q co n) fun _ m3 => some ([1, q, n, b], m3.set64 CTL 136 co) := rfl

/-- After `opa_go`. -/
def opfK3 (k : Nat) (n co : Word) (r2 : List Word) (m2 : Mem) : Option (List Word × Mem) :=
  if r2.headD 0 = 0 then some ([0, 0, 0, 0], m2.set64 CTL 136 co)
  else opfTail k n co (r2.tail.headD 0) (allocW m2 n)

/-- After `opf_go`. -/
def opfK2 (p : Prog) (k : Nat) (n e i co : Word) (r1 : List Word) (m1 : Mem) :
    Option (List Word × Mem) :=
  if r1.headD 0 = 0 then ntBW (callW p k "opa_go" [n, e, i] (m1.set64 CTL 136 co)) (opfK3 k n co)
  else opfTail k n co (r1.tail.headD 0) (allocW m1 n)

/-- `open_pis_at_fvars_f(n, e, i)`'s body over its callees' runs. -/
def opfTopK (p : Prog) (k : Nat) (m : Mem) (n e i : Word) : Option (List Word × Mem) :=
  if i >>> 63 ≠ 0 then none else
  if m.len64 SPN < rdW (m.arr64 CTL) 136 then none else
  ntBW (callW p k "opf_go" [n, e, i, rdW (m.arr64 CTL) 136, 0] m)
    (opfK2 p k n e i (rdW (m.arr64 CTL) 136))

theorem opfTopK_spec (p : Prog) (hp : p.lookup "open_pis_at_fvars_f" = some L.Stubs.openPisAtFvarsFL)
    (ha : p.lookup "iw_alloc" = some iwAlloc) (hs : p.lookup "spn_to_iw" = some spnToIwL)
    (k : Nat) (s₀ : St) (n e i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "open_pis_at_fvars_f" [n, e, i]
    ⦃fun r s' => LocEq s' s₀ ∧ opfTopK p k s₀.mem n e i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, L.Stubs.openPisAtFvarsFL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, callW_spec p k "opf_go",
      callW_spec p k "opa_go",
      iwAlloc_specW p ha k, s2i_spec p hs k] <;>
    finish (gen := 20) [opfTopK, opfK2, opfK3, opfTail_some, ntBW]

end L.Ind
