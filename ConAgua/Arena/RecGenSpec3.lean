import ConAgua.Arena.RecClassSpecH
import ConAgua.Arena.IndRealWalk
import ConAgua.Arena.DeclHeader

/-!
# `RecGen`: `classConstOk` (lane `indproofs2`, helper `rec`)

`class_const_ok` calls `install_header` (lane `decls2`'s `installHeader`, the same guards in the
same order) and then infers the type. `ccoGuards` is `ihW_ok` (`DeclHeader.lean`) with the
conclusion stated for `classConstOk`'s guards (they differ from `installHeader`'s in the error
messages only).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `class_const_ok` -/

def ccoK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m3) => some ([0], m3)

def ccoK2 (cR : CallM) (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => ccoK3 (cR n "ensure_sort_core" [vis, 0, r2.headD 0] m2)

def ccoK1 (cR : CallM) (n : Nat) (vis q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => ccoK2 cR n vis (cR n "infer_type_core" [vis, 0, rdW (m1.arr64 EREC) (q + 3)] m1)

/-- **The model of `class_const_ok`**: `install_header`, then the inference (the core's calls
read through `c`: `IndCallM.lean`). -/
def ccoW (cR : CallM) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, q => ccoK1 cR n vis q (L.Arena.ihW cR n m vis q)

section arms
variable (cR : CallM) (n : Nat) (m m1 m2 m3 : Mem) (vis q : Word) (r1 r2 r3 : List Word)
theorem ccoW_eq : ccoW cR (n + 1) m vis q = ccoK1 cR n vis q (L.Arena.ihW cR n m vis q) := rfl
theorem ccoK1_some : ccoK1 cR n vis q (some (r1, m1)) =
    ccoK2 cR n vis (cR n "infer_type_core" [vis, 0, rdW (m1.arr64 EREC) (q + 3)] m1) := rfl
theorem ccoK2_some : ccoK2 cR n vis (some (r2, m2)) =
    ccoK3 (cR n "ensure_sort_core" [vis, 0, r2.headD 0] m2) := rfl
theorem ccoK3_some : ccoK3 (some (r3, m3)) = some ([0], m3) := rfl
end arms

grind_pattern [ind_grind] ccoW_eq => ccoW cR (n + 1) m vis q
grind_pattern [ind_grind] ccoK1_some => ccoK1 cR n vis q (some (r1, m1))
grind_pattern [ind_grind] ccoK2_some => ccoK2 cR n vis (some (r2, m2))
grind_pattern [ind_grind] ccoK3_some => ccoK3 (some (r3, m3))

/-- `class_const_ok_header`'s spec: `install_header`'s (`ih_specW`), the same body. -/
theorem classConstOkHeader_spec (p : Prog) (h : IhProg p)
    (hh : p.lookup "class_const_ok_header" = some classConstOkHeader) (cR : CallM) (hcR : CallSpec p cR)
    (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_const_ok_header" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ L.Arena.ihW cR n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hh]
  simp only [callFn, classConstOkHeader]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      envFind_specW p h.ix h.rowGet h.find n, resCont_spec p h.resF h.resC n,
      L.Arena.cvLps_specW p h.alloc h.copy h.eti h.lps n, slNodup_spec p h.cont h.nodup n,
      lbbF_spec p h.bvb n, hffF_spec p h.hf n,
      hcR n "all_level_params_defined", hcR n "consts_resolve_ffast",
      hcR n "unresolved_consts_error"] <;>
    finish (gen := 20)

theorem classConstOk_spec (p : Prog) (h : IhProg p)
    (hh : p.lookup "class_const_ok_header" = some classConstOkHeader)
    (hc : p.lookup "class_const_ok" = some classConstOkL) (cR : CallM) (hcR : CallSpec p cR)
    (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_const_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ ccoW cR n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hc]
  simp only [callFn, classConstOkL]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      classConstOkHeader_spec p h hh cR hcR n,
      hcR n "infer_type_core", hcR n "ensure_sort_core"] <;>
    finish (gen := 20) [rdW_eq]

end L.Ind
