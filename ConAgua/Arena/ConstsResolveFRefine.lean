import ConAgua.Arena.ConstsResolveF
import ConAgua.Arena.DeclNatSpec
import ConAgua.Arena.WhnfIotaRefine
import ConAgua.Arena.RecClassSpecE
import ConAgua.Census.Attr

/-!
# `consts_resolve_ffast` refines `constsResolveFFast` (lane `tails`)

`ConstsResolveF.lean`'s L code (lane `stubs`) under the inductive stage's relation `StageR`, in the
`RefAM` shape of `IndStubs.lean`'s contract `constsResolveFFast_spec`.

* **Models from the calls.** Every function's word model is written over `callW` of its callees
  (`DeclNatBase.lean`'s style), so each `vcgen` spec only matches the text; the callees' meaning
  enters in the relational lemmas (`pin_at`: `pinAt_model`; `env_find`: `envFindW_found`; `e_view`:
  `eViewW_ok`; `is_str_lit`: `islW`, `viewLit_ok`).
* **The memo.** The twin threads its memo (`Std.HashMap EIdx Bool`) through the walk; the L table
  `CRM` (`crSch`) is related to it by the memo library's `MemoRV` at key `(h, 0)` (`bmKey`) and the
  value relation `CrV` (the word is `0` or `1`, and decodes to the Bool). The twin's walk changes
  no state; the L walk writes only `CRM` and `CTL[158‥159]`, which `StageR` does not read
  (`StageR.frame_hi`).
* **Fuel.** The counter word `f` is the twin's fuel (`4000000000` = `coreWalkFuel` at the entry);
  the induction is on L's fuel.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Stubs

open L.Arena L.Ind

/-- What the specs need of the program. -/
structure CrfProg (p : Prog) : Prop where
  entry : p.lookup "consts_resolve_ffast" = some constsResolveFFastL
  go : p.lookup "crf_go" = some crfGo
  leaf : p.lookup "cr_leaf" = some crLeaf
  lit : p.lookup "cr_lit_pins" = some crLitPins
  pf : p.lookup "pin_found" = some pinFound
  find : p.lookup "crm_find" = some (memoFindG crSch)
  put : p.lookup "crm_put" = some (memoPutG crSch)
  clear : p.lookup "crm_clear" = some (memoClearG crSch)
  view : p.lookup "e_view" = some eView
  isl : p.lookup "is_str_lit" = some isStrLitL
  ef : p.lookup "env_find" = some envFindL
  erg : p.lookup "env_row_get" = some envRowGetL
  eix : p.lookup "env_ix" = some envIxL
  pin : p.lookup "pin_at" = some pinAtL

/-! ## The models over the calls, and their specs -/

/-- `1` if no word of the list is `0`, else `0`: an `&&` chain of `≠ 0` tests, as nested
tests (the short-circuit paths of the L condition). -/
def allNZ : List Word → Word
  | [] => 1
  | w :: ws => if w = 0 then 0 else allNZ ws

@[lang_grind =] theorem allNZ_nil : allNZ [] = 1 := rfl
@[lang_grind =] theorem allNZ_cons (w : Word) (ws : List Word) :
    allNZ (w :: ws) = if w = 0 then 0 else allNZ ws := rfl

section models
variable (p : Prog) (k : Nat)

/-- `pin_found(vis, i)`. -/
def pfW (m : Mem) (vis i : Word) : Option (List Word × Mem) :=
  ntBW (callW p k "pin_at" [i] m) fun r1 m1 =>
  ntBW (callW p k "env_find" [r1.headD 0, vis] m1) fun r2 m2 => some ([r2.headD 0], m2)

/-- `cr_lit_pins`' chain of `pin_found` calls: the answers so far `acc`, the pins still to ask
`ks`, the last call's result. -/
def clpL (vis : Word) : Bool → List Word → Option (List Word × Mem) → Option (List Word × Mem)
  | _, _, none => none
  | z, [], some (r, m) => some ([if z || r.headD 0 == 0 then 0 else 1], m)
  | z, k' :: ks, some (r, m) => clpL vis (z || r.headD 0 == 0) ks (callW p k "pin_found" [vis, k'] m)

/-- `cr_lit_pins(vis, s)`: three pins for a `Nat` literal (`s = 0`), ten for a `String` one. -/
def clpW (m : Mem) (vis s : Word) : Option (List Word × Mem) :=
  if s = 0 then clpL p k vis false [2, 3] (callW p k "pin_found" [vis, 1] m)
  else clpL p k vis false [2, 3, 5, 6, 7, 8, 9, 10, 12] (callW p k "pin_found" [vis, 1] m)

/-- `cr_leaf(vis, g, x, h)`. -/
def clW (m : Mem) (vis g x h : Word) : Option (List Word × Mem) :=
  if g = 8 then
    ntBW (callW p k "is_str_lit" [h] m) fun rs ms =>
    ntBW (callW p k "cr_lit_pins" [vis, rs.headD 0] ms) fun r mr => some ([r.headD 0], mr)
  else if g = 3 then
    ntBW (callW p k "env_find" [x, vis] m) fun r mr => some ([r.headD 0], mr)
  else some ([1], m)

end models

theorem clpL_none (p : Prog) (k : Nat) (vis : Word) (z : Bool) (ks : List Word) :
    clpL p k vis z ks none = none := by cases ks <;> rfl
theorem clpL_nil (p : Prog) (k : Nat) (vis : Word) (z : Bool) (r : List Word) (m : Mem) :
    clpL p k vis z [] (some (r, m)) = some ([if z || r.headD 0 == 0 then 0 else 1], m) := rfl
theorem clpL_cons (p : Prog) (k : Nat) (vis k' : Word) (z : Bool) (ks r : List Word) (m : Mem) :
    clpL p k vis z (k' :: ks) (some (r, m)) =
      clpL p k vis (z || r.headD 0 == 0) ks (callW p k "pin_found" [vis, k'] m) := rfl


theorem pf_spec (p : Prog) (hp : CrfProg p) (k : Nat) (s₀ : St) (vis i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "pin_found" [vis, i]
    ⦃fun r s' => LocEq s' s₀ ∧ pfW p k s₀.mem vis i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.pf]
  simp only [callFn, pinFound]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p k "pin_at", callW_spec p k "env_find"] <;>
    finish (gen := 20) [pfW, ntBW]

set_option maxHeartbeats 6400000 in
theorem clp_spec (p : Prog) (hp : CrfProg p) (k : Nat) (s₀ : St) (vis s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "cr_lit_pins" [vis, s]
    ⦃fun r s' => LocEq s' s₀ ∧ clpW p k s₀.mem vis s = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.lit]
  simp only [callFn, crLitPins]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, callW_spec p k "pin_found"]
  all_goals (try simp only [Cond.pval, Expr.pval, Cmp.eval, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, beq_iff_eq] at *)
  all_goals grind (gen := 20) (instances := 10000) [lang_grind, arena_grind, clpW, clpL_none,
    clpL_nil, clpL_cons, allNZ_cons, allNZ_nil]

theorem cl_spec (p : Prog) (hp : CrfProg p) (k : Nat) (s₀ : St) (vis g x h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "cr_leaf" [vis, g, x, h]
    ⦃fun r s' => LocEq s' s₀ ∧ clW p k s₀.mem vis g x h = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.leaf]
  simp only [callFn, crLeaf]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p k "is_str_lit",
      callW_spec p k "cr_lit_pins", callW_spec p k "env_find"] <;>
    finish (gen := 20) [clW, ntBW]

end L.Stubs
