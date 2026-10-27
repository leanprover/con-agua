import ConAgua.Arena.RecGenSpec22
import ConAgua.Arena.RecClassSpecH
import ConAgua.Arena.RecGenSpec19

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

set_option maxHeartbeats 1600000 in
l_model cbc_spec (p : Prog) (hp : p.lookup "check_block_classes" = some checkBlockClassesL)
  fns [hp ↦ cbcW]
  specs [callW_spec p n "class_read", callW_spec p n "class_read_classes",
    callW_spec p n "check_block_classes_keys", callW_spec p n "class_majors",
    callW_spec p n "check_block_classes_one_per_member"]
  grind [arena_grind] finish [rdW_eq] gen 40 instances 20000

/-! ## The relation -/

/-- The lookups of `check_block_classes`. -/
structure CbcProg (p : Prog) : Prop where
  read : ReadProg p
  clm : ClmProg p
  ha : p.lookup "iw_alloc" = some iwAlloc
  crc : p.lookup "class_read_classes" = some classReadClasses
  cnt : p.lookup "check_block_classes_count" = some checkBlockClassesCount
  opm : p.lookup "check_block_classes_one_per_member" = some checkBlockClassesOnePerMember
  cbc : p.lookup "check_block_classes" = some checkBlockClassesL

end L.Ind
