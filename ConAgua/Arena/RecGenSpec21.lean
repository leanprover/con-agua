import ConAgua.Arena.RecGenSpec20
import ConAgua.Arena.RecGenSpec11
import ConAgua.Arena.IndInstallSpec30

/-!
# `checkBlockClasses` (lane `indproofs4`)

`check_block_classes(vis, p, params.off, params.len, ctorsAs.off, ctorsAs.len)`: `class_read`
(`classRead_refines`, `RecClassSpecH`), its slots' classes (`classReadClasses_refines`,
`RecClassSpec`), the canonical keys (`ckkW_sim`, `RecGenSpec14`), the majors (`clmW_sim`,
`RecGenSpec19`), one class per member (`opmW_ok`).

* **Glue.** `class_read`'s slots are decoded stably (`SPL`); `slots_ok` turns that into the
  decoding and `SlotsExt` that `class_read_classes` takes (`stab_decCS_ext`, `RecGenSpec20`).
  `class_read_classes`' keys (`CcRes`) are decoded below the tops (`ccRes_pslR`: `decCK` reads
  the same in the cut pools for a key whose extent is below the top, `decCK_truncM`).
* **The positivity memos across `class_read` and `class_read_classes`**: neither has a memo
  lemma, so the walk memos (`PosMR`) come from a write-set fact (`hcl`: their closures write no
  stage memo, arrays 201‥208 and `CTL` 202‥219; decided for the checker's program), as the tail's
  `HbMemo.ofClosed`.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Glue -/

/-- **`class_read`'s stable slots** are decoded with their extents below the top. -/
theorem slots_ok {m : Mem} {so sl : Nat} {slots : List ClassSlot} (h : SPL decCS m so sl slots)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    decPL m (decCS m) so sl = some slots ∧ SlotsExt m so sl := by
  refine ⟨h.decPL, h.1, fun j hj sp hsp => ?_⟩
  obtain ⟨hb, ps, hps, hfa⟩ := h
  have hlen := decNL_length m hps
  have hat := decNL_at hps j hj
  rw [hsp] at hat
  cases hat
  have hl2 := FA2.length_eq hfa
  exact stab_decCS_ext (FA2.get hfa j (by omega) (by omega)) hsz

theorem decCK_truncM {m : Mem} {k : Nat} (hk : CKExt m k) : decCK (truncM m) k = decCK m k := by
  obtain ⟨h1, h2⟩ := hk
  simp only [decCK]
  rw [iwH_truncM (by omega), iwH_truncM (by omega)]
  have hat : decAt (truncM m) (decHL (k := IdxKind.expr) (truncM m)) (k + 2) =
      decAt m (decHL (k := IdxKind.expr) m) (k + 2) := by
    simp only [decAt]
    rw [iwN_truncM (by omega), iwN_truncM (by omega)]
    cases ho : iwN m (k + 2) with
    | none => simp
    | some o =>
      cases hl : iwN m (k + 2 + 1) with
      | none => simp
      | some l =>
        show decHL (truncM m) o l = decHL m o l
        rcases h2 o l ho (by simpa using hl) with hb | rfl
        · exact decHL_truncM hb
        · simp [decHL, hslice?]
  rw [hat]

/-- **`class_read_classes`' keys are decoded below the tops.** -/
theorem ccRes_pslR {m : Mem} {r : List Word} {keys : List ClassKey} (h : CcRes m r keys) :
    PSlR decCK keys (r.headD 0) (r.tail.headD 0) m := by
  obtain ⟨ptrs, hps, hdk, hext, hb⟩ := h
  refine ⟨?_, hb⟩
  show decPL (truncM m) (decCK (truncM m)) _ _ = some keys
  rw [← hdk]
  unfold decPL
  refine mapM_congr_range _ fun j hj => ?_
  have hj' : j < (r.tail.headD 0).toNat := List.mem_range.mp hj
  rw [iwN_truncM (by omega)]
  have hat := decNL_at hps j hj'
  rw [hat]
  simp only [Option.bind_eq_bind, Option.bind_some]
  exact decCK_truncM (hext _ (List.getElem_mem _))

/-! ## The model -/

section model
variable (p : Prog) (n : Nat)

/-- After `check_block_classes_one_per_member`: the result. -/
def cbcK5 (rd : Word) (rm : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (g, m) => if g.headD 0 = 0 then none else some ([rd, rm.headD 0, rm.tail.headD 0], m)

/-- After `class_majors`: one class per member. -/
def cbcK4 (pp rd : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cbcK5 rd r (callW p n "check_block_classes_one_per_member"
      [0, rdW (m.arr64 IW) (pp + 1), r.headD 0, r.tail.headD 0] m)

/-- After the keys: the majors. -/
def cbcK3 (vis pp po pl co cl rd : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cbcK4 p n pp rd (callW p n "class_majors"
      [vis, pp, co, cl, po, pl, r.headD 0, r.tail.headD 0] m)

/-- After the classes: the keys. -/
def cbcK2 (vis pp po pl co cl rd : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cbcK3 p n vis pp po pl co cl rd (callW p n "check_block_classes_keys"
      [rdW (m.arr64 IW) (pp + 4), po, pl, r.headD 0, r.tail.headD 0] m)

/-- After `class_read`: the classes of its slots. -/
def cbcK1 (vis pp po pl co cl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else
      cbcK2 p n vis pp po pl co cl (r.tail.headD 0) (callW p n "class_read_classes"
        [rdW (m.arr64 IW) (r.tail.headD 0), rdW (m.arr64 IW) (r.tail.headD 0 + 1)] m)

/-- **The model of `check_block_classes(vis, p, params.off, params.len, ctorsAs.off,
ctorsAs.len)`** (callees at fuel `n`). -/
def cbcW (m : Mem) (vis pp po pl co cl : Word) : Option (List Word × Mem) :=
  cbcK1 p n vis pp po pl co cl (callW p n "class_read"
    [pp, vis, rdW (m.arr64 IW) (pp + 4), rdW (m.arr64 IW) (pp + 2), rdW (m.arr64 IW) (pp + 3)] m)

section arms
variable (vis pp po pl co cl rd : Word) (r rm : List Word) (m : Mem)
theorem cbcK5_some_bad (h : r.headD 0 = 0) : cbcK5 rd rm (some (r, m)) = none := by
  simp only [cbcK5]; rw [if_pos h]
theorem cbcK5_some_ok (h : ¬ r.headD 0 = 0) :
    cbcK5 rd rm (some (r, m)) = some ([rd, rm.headD 0, rm.tail.headD 0], m) := by
  simp only [cbcK5]; rw [if_neg h]
theorem cbcK4_some : cbcK4 p n pp rd (some (r, m)) = cbcK5 rd r (callW p n
    "check_block_classes_one_per_member" [0, rdW (m.arr64 IW) (pp + 1), r.headD 0, r.tail.headD 0] m) := rfl
theorem cbcK3_some : cbcK3 p n vis pp po pl co cl rd (some (r, m)) = cbcK4 p n pp rd (callW p n
    "class_majors" [vis, pp, co, cl, po, pl, r.headD 0, r.tail.headD 0] m) := rfl
theorem cbcK2_some : cbcK2 p n vis pp po pl co cl rd (some (r, m)) = cbcK3 p n vis pp po pl co cl rd
    (callW p n "check_block_classes_keys" [rdW (m.arr64 IW) (pp + 4), po, pl, r.headD 0, r.tail.headD 0] m) :=
  rfl
theorem cbcK1_some_bad (h : r.headD 0 = 0) : cbcK1 p n vis pp po pl co cl (some (r, m)) = none := by
  simp only [cbcK1]; rw [if_pos h]
theorem cbcK1_some_ok (h : ¬ r.headD 0 = 0) : cbcK1 p n vis pp po pl co cl (some (r, m)) =
    cbcK2 p n vis pp po pl co cl (r.tail.headD 0) (callW p n "class_read_classes"
      [rdW (m.arr64 IW) (r.tail.headD 0), rdW (m.arr64 IW) (r.tail.headD 0 + 1)] m) := by
  simp only [cbcK1]; rw [if_neg h]
end arms

end model

attribute [ind_grind] cbcK5_some_bad cbcK5_some_ok cbcK4_some cbcK3_some cbcK2_some cbcK1_some_bad
  cbcK1_some_ok

set_option maxHeartbeats 1600000 in
theorem cbc_spec (p : Prog) (hp : p.lookup "check_block_classes" = some checkBlockClassesL) (n : Nat)
    (s₀ : St) (vis pp po pl co cl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_classes" [vis, pp, po, pl, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ cbcW p n s₀.mem vis pp po pl co cl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockClassesL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "class_read", callW_spec p n "class_read_classes",
      callW_spec p n "check_block_classes_keys", callW_spec p n "class_majors",
      callW_spec p n "check_block_classes_one_per_member"] <;>
    finish (gen := 40) (instances := 20000) [cbcW, rdW_eq]

end L.Ind
