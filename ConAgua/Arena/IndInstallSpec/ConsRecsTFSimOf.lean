module
public import ConAgua.Arena.SimLib
import ConLeche.Kernel.Env


@[expose] public section

/-!
# ConsRecsTFSimOf

`ConsRecsTFSim`, `_root_.L.Arena.Sim.of_model`, `tailRcCallees`, `tailCallees`, `tailToNat`, `consRecsTFSim_of`.
-/

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified


/-- Replace the model by one that returns whatever it returns. -/
theorem _root_.L.Arena.Sim.of_model {β α : Type} {mo mo' : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (h : ∀ r m', mo = some (r, m') → mo' = some (r, m'))
    (hs : Sim mo' op a Q) : Sim mo op a Q := fun r m' e => hs r m' (h r m' e)

/-- The callees whose program text keeps the recursor check's walk memos: the tail's before
`check_block_rec`, and `gen_rec_check`'s. -/
def tailRcCallees : List FnName :=
  ["check_block_idx_sorts", "cons_block_ctors", "flush_caches", "block_nested_bit", "target_rec_pins",
    "class_stream_recs"]

/-- The tail's callees with no memo lemma. -/
def tailCallees : List FnName :=
  ["check_block_idx_sorts", "cons_block_ctors", "block_nested_bit", "check_block_rec"]

end L.Ind

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified


end L.Ind

end
