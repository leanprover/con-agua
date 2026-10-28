import ConAgua.Arena.IndInstallSpec.CbProg
import ConAgua.Arena.IndInstallSpec.Frame
import ConAgua.Arena.IndPartsSpec.IndPartsProg5
import ConAgua.Arena.IndRealBph2
import ConAgua.Arena.RecGenSpec.Classes
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# ShapeCVOfDecB

`checkShapeless_never`, `cidFrameCallees`, `shapeCV_of_decB` and `CidProg`: what `check_ind_decl`'s
refinement (`IndT/CheckIndDecl`) reads.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_shapeless` -/

/-- **`check_shapeless` never returns**: it calls `check_shapeless_formers` (whatever that
does) and then aborts. Unlike `checkShapeless_refines` this needs no contract of the callee. -/
theorem checkShapeless_never (p : Prog)
    (hp : p.lookup "check_shapeless" = some checkShapeless) (n : Nat) (s₀ : St)
    (vis off cnt : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_shapeless" [vis, off, cnt]
    ⦃fun _ _ => False; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkShapeless]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        callW_spec p n "check_shapeless_formers"] <;>
      finish

/-- The callees of `check_ind_decl` that cross the walk memos by their write set. -/
def cidFrameCallees : List FnName := ["basis_pin_hit", "block_parts"]

theorem CidMemos.call {p : Prog} {fs : List FnName} (hcl : closedA p cidFreeA cidFreeC fs = true)
    {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word} {m' : Mem}
    (h : callW p n f vs m = some (r, m')) (hM : CidMemos m) : CidMemos m' :=
  hM.frame (run_memFrame hcl hf (run_of_callW h)).1

/-! ## `ShapeCV` from the record's decoding -/

/-- A `BlockShape` record decoded below the tops has its members' constant records in `EREC`. -/
theorem shapeCV_of_decB {m : Mem} {q : Word} {bs : BlockShape}
    (h : DecB (fun m => decBS m q.toNat) m bs) : ShapeCV m q := by
  intro o l ho hl j hj c hc d hd
  obtain ⟨hmem, -⟩ := decBS_some (show decBS (truncM m) q.toNat = some bs from h)
  obtain ⟨o', l', ho', hl', hd'⟩ := decAt_some hmem
  rw [(rec2IwN_trunc ho').2] at ho
  rw [(rec2IwN_trunc hl').2] at hl
  obtain rfl := Option.some.inj ho
  obtain rfl := Option.some.inj hl
  obtain ⟨v, ms, hv, hms, -⟩ := decPL_get _ _ _ hd' j hj
  rw [(rec2IwN_trunc hv).2] at hc
  obtain rfl := Option.some.inj hc
  simp only [decMS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hms
  obtain ⟨d', hd'', cv, hcv, -⟩ := hms
  rw [(rec2IwN_trunc hd'').2] at hd
  obtain rfl := Option.some.inj hd
  exact (rec3CVExt_of_trunc hcv).1

/-! ## The arm -/

/-- The lookups of the inductive arm. -/
structure CidProg (p : Prog) : Prop where
  cid : p.lookup "check_ind_decl" = some checkIndDecl
  csf : p.lookup "check_shapeless_formers" = some checkShapelessFormers
  csl : p.lookup "check_shapeless" = some checkShapeless
  basis : BasisProg p
  canon : CanonProg p
  rom : L.Rom.RomRefs p
  pa : p.lookup "pin_at" = some pinAtL
  cbd : p.lookup "check_basis_decl" = some checkBasisDeclL
  ps : p.lookup "pi_sort_tele_len" = some L.Front.Ind.piSortTeleLen
  ev : p.lookup "e_view" = some eView
  ipo : p.lookup "ind_params_ok" = some L.Checker.indParamsOkL
  parts : IndPartsProg5 p
  cb : CbProg p
  bph : BphProg p

end L.Ind
