import ConAgua.Arena.IndInstallSpec16
import ConAgua.Arena.IndSumSpec13

/-!
# Refinements of `IndInstall`, part 17 (lane `indproofs2`, helper `install`): `checkBlockIdxSorts`

Per member: the former's telescope opened (`open_pis_at_fvars_f`'s stub), the index binders'
universes (`check_struct_field_sorts_i`, `IndSumSpec11`'s refinement, `installSimFsorts`), recursion as the twin's with the pointers consed (D18).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_struct_field_sorts_i` as a callee (lane `indproofs2`'s `IndSumSpec11`) -/

/-! ## `check_block_idx_sorts_one` -/

/-- The index binders' slice: the telescope's tail past `nP`, `(0, 0)` when empty. -/
def idxTail (nP o l : Word) : Word × Word := if nP < l then (o + nP, l - nP) else (0, 0)

def iisK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
def iisK2 (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => iisK3 (callW p n "rec2" [r.headD 0, r.tail.headD 0] m)
def iisK1 (p : Prog) (n : Nat) (vis nP ni srt : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else iisK2 p n (callW p n "check_struct_field_sorts_i" [vis, 1, 0, srt, nP,
      (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).1,
      (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).2, 0, 0, ni] m)

/-- **The model of `check_block_idx_sorts_one(vis, p, ms, cvTa)`** (body fuel `n`). -/
def iisW (p : Prog) (n : Nat) (m : Mem) (vis pp ms cv : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (ms + 1) < rdW (m.arr64 IW) (pp + 4) then none
  else iisK1 p n vis (rdW (m.arr64 IW) (pp + 4)) (rdW (m.arr64 IW) (ms + 1)) (rdW (m.arr64 IW) (pp + 6))
    (callW p n "open_pis_at_fvars_f" [rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (ms + 1),
      rdW (m.arr64 EREC) (cv + 3), 0] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis nP ni srt : Word) (r : List Word)
theorem iisK3_some : iisK3 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem iisK2_some : iisK2 p n (some (r, m)) = iisK3 (callW p n "rec2" [r.headD 0, r.tail.headD 0] m) := rfl
theorem iisK1_none (h : r.headD 0 = 0) : iisK1 p n vis nP ni srt (some (r, m)) = none := by
  simp only [iisK1, h, ↓reduceIte]
theorem iisK1_some (h : ¬ r.headD 0 = 0) : iisK1 p n vis nP ni srt (some (r, m)) =
    iisK2 p n (callW p n "check_struct_field_sorts_i" [vis, 1, 0, srt, nP,
      (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).1,
      (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).2, 0, 0, ni] m) := by
  simp only [iisK1, h, ↓reduceIte, ite_false]
end arms
attribute [ind_grind] iisK3_some iisK2_some iisK1_none iisK1_some

set_option maxHeartbeats 1600000 in
theorem iis_spec (p : Prog) (hp : p.lookup "check_block_idx_sorts_one" = some checkBlockIdxSortsOne)
    (n : Nat) (s₀ : St) (vis pp ms cv : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_idx_sorts_one" [vis, pp, ms, cv]
    ⦃fun r s' => LocEq s' s₀ ∧ iisW p n s₀.mem vis pp ms cv = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockIdxSortsOne]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "open_pis_at_fvars_f", callW_spec p n "check_struct_field_sorts_i",
    callW_spec p n "rec2"]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval, BinOp.eval,
    Nat.reduceEqDiff, reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, iisW, idxTail, rdW_eq]

/-! ## `check_block_idx_sorts` -/

/-- **`check_block_idx_sorts` is its model `iisrW`** (generated). -/
l_model iisr_spec (p : Prog) (hp : p.lookup "check_block_idx_sorts" = some checkBlockIdxSorts)
  fns [hp ↦ iisrW]
  specs [callW_spec p n "check_block_idx_sorts_one", callW_spec p n "sl_cons"]
  grind [ind_grind] finish [rdW_eq] gen 20

end L.Ind
