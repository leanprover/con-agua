module

public import ConAgua.Arena.IndInstallSpec.HbFreeMfr
public import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
public import ConAgua.Arena.RecGenSpec.Rec3TmdWDecB

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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **What the tail needs of `cons_block_recs_tf(vis2, p, 0, out.off, out.len, vis)`**: from the
stage relation at `vis` of `fe`, the shape and the recursor stage's output decoded below the tops,
and the `hb` memo, a returning run is `consBlockRecsTF` at the view `vis2`. (To be discharged by
helper `indproofs3-rec`'s refinement.) -/
def ConsRecsTFSim (p : Prog) : Prop :=
  ∀ (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis vis2 pp : Word) (fe : IFEnv) (m : Mem) (a : AState)
    (bs : BlockShape) (rr : List Word) (outs : List (IConstantVal × TargetMajor × List EIdx)),
    StageR vis fe m a → DecB (fun m => decBS m pp.toNat) m bs → decRRS m rr outs → HbMemo m → AbsOK m →
    Sim (callW p n "cons_block_recs_tf" [vis2, pp, 0, rr.headD 0, rr.tail.headD 0, vis] m)
      (ConRon.Arena.consBlockRecsTF vis2.toNat bs 0 outs fe) a
      (fun r x m' a' => StageR (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m' ∧ AbsOK m')
-/

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
  ["check_block_idx_sorts", "cons_block_ctors", "block_nested_bit", "check_block_rec", "cons_block_recs_tf"]

theorem tailToNat {q : Word} {k : Nat} (h : q.toNat + k < 2 ^ 64) :
    (q + UInt64.ofNat k).toNat = q.toNat + k := by
  have hs : UInt64.size = 2 ^ 64 := rfl
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega)]; exact Nat.mod_eq_of_lt h

end L.Ind

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`cons_block_recs_tf` as the tail needs it**, from its refinement. -/
theorem consRecsTFSim_of {p : Prog} (L : CbrLook p) {fs : List FnName}
    (hcl : closedA p hbFreeA hbFreeC fs = true) (hf : "cons_block_recs_tf" ∈ fs) :
    ConsRecsTFSim p := by
  sorry
-/

end L.Ind

end
