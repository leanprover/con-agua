import ConAgua.Arena.IndPartsSpec5
import ConAgua.Arena.IndSumSpec.ColW
import ConAgua.Arena.IndSumSpec.StructProjArgP
import ConAgua.Arena.IndSumSpec.SumProg

/-!
# CtlK1

`ctlK7`, `ctlK6`, `ctlK5`, `ctlK4`, `ctlK3`, `ctlK2` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- After `field_doms_resolve`: the index arguments. -/
def ctlK7 (cR : CallM) (n : Nat) (vis0 vis isP lg rs nP nF xo xl ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else ctlK8 cR n vis isP lg rs nP nF xo xl ao al (iarW (n + 1) m vis0 (ao + nP) (al - nP))
/-- After `sl_eq` (or its skip): the residual's shape. -/
def ctlK6 (cR : CallM) (n : Nat) (vis0 vis nP nIdx rs isP lg nF xo xl hd xfn ao al : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some e => if xfn ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0 then none
    else ctlK7 cR n vis0 vis isP lg rs nP nF xo xl ao al (fdrW (n + 1) m vis0 xo xl)
/-- After `get_app_args_f`: the parameter prefix. -/
def ctlK5 (cR : CallM) (n : Nat) (vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd xfn : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m) => ctlK6 cR n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn (ra.headD 0) (ra.tail.headD 0) m
      (if nP ≤ ra.tail.headD 0 then eqW (n + 1) m (ra.headD 0) nP cqO cqL else some 0)
/-- After `get_app_fn_f`. -/
def ctlK4 (cR : CallM) (n : Nat) (vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m) => ctlK5 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd (rf.headD 0)
      (gaaF m [CWF, xb])
/-- After `intern_const`: the guard, `get_app_fn_f`. -/
def ctlK3 (cR : CallM) (n : Nat) (vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hd, m) => if 4294967296 ≤ hd then none
    else ctlK4 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd (gafF m [CWF, xb])
/-- After `param_levels`: the family's head. -/
def ctlK2 (cR : CallM) (n : Nat) (vis0 vis T nP nIdx rs isP lg nF cqO cqL xo xl xb : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ru, m) => ctlK3 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (ceinternW m T (ru.headD 0))
/-- After `open_pis_at_fvars_f`. -/
def ctlK1 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rx, m) => if rx.headD 0 = 0 then none
    else ctlK2 cR n vis0 vis T nP nIdx rs isP lg nF cqO cqL (rx.tail.headD 0) (rx.tail.tail.headD 0)
      (rx.tail.tail.tail.headD 0) (plW (n + 1) m lo ll)

/-- **The model of `check_sum_ctor_tail(vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, nF, cqO, cqL,
cqB)`** (its callees at exec fuel `n + 1`). -/
def ctlW (cR : CallM) (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB : Word) :
    Option (List Word × Mem) :=
  ctlK1 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL (cR (n + 1) "open_pis_at_fvars_f" [nF, cqB, nP] m)

/-- After `check_struct_doms_at`: the tail. -/
def ctorK8 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => ctorK9 cvC (ctlW cR n m vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB)
/-- After `fvar_type_ds`: the binder domains. -/
def ctorK7 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rt, m) => ctorK8 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB
      (sdomsW cR (n + 2) m vis 0 cqO cqL (rt.headD 0) (rt.tail.headD 0) nP)
end L.Ind

end
