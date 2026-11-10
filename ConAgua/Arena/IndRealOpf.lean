module

public import ConAgua.Arena.StubInd
public import ConAgua.Arena.IndRealFvt
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.StageInst1
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.StubInd
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.FVarStore
import all ConAgua.Arena.ForallStore
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.Inst1
import all ConAgua.Arena.Inst1Spec
import all ConAgua.Arena.InstList
import all ConAgua.Arena.InstListSpec
import all ConAgua.Arena.LamStore
import all ConAgua.Arena.LetStore
import all ConAgua.Arena.LiftL
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.WhnfEntry

@[expose] public section

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
def opfA : List TieredArray := [(SPN : TieredArray), (IW : TieredArray), (FVREC : TieredArray), (FVSLOT : TieredArray),
  (FVLP : TieredArray), tier1 FVREC, tier1 FVSLOT, tier1 FVLP] ++ instListA ++ instA
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

l_model spnPush_spec (p : Prog) (hp : p.lookup "spn_push" = some L.Stubs.spnPush)
  fns [hp ↦ spnPushW list]
  grind [arena_grind]

l_model opfGoK_spec (p : Prog) (hp : p.lookup "opf_go" = some L.Stubs.opfGo)
  fns [hp ↦ opfGoK list]
  specs [callW_spec p n "inst_list", callW_spec p n "e_view", callW_spec p n "intern_fvar",
    callW_spec p n "spn_push", callW_spec p n "opf_go"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model opaGoK_spec (p : Prog) (hp : p.lookup "opa_go" = some L.Stubs.opaGo)
  fns [hp ↦ opaGoK list]
  specs [callW_spec p n "e_view", callW_spec p n "intern_fvar", callW_spec p n "inst_entry",
    callW_spec p n "spn_push", callW_spec p n "opa_go"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

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
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, callW_spec p k "opf_go",
      callW_spec p k "opa_go",
      iwAlloc_specW p ha k, s2i_spec p hs k] <;>
    finish (gen := 20) [opfTopK, opfK2, opfK3, opfTail_some, ntBW]

end L.Ind
