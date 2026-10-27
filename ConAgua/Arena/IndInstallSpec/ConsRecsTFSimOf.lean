import ConAgua.Arena.IndInstallSpec.HbFreeMfr
import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.RecGenSpec.Rec3TmdWDecB

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

/-- **What the tail needs of `cons_block_recs_tf(vis2, p, 0, out.off, out.len, vis)`**: from the
stage relation at `vis` of `fe`, the shape and the recursor stage's output decoded below the tops,
and the `hb` memo, a returning run is `consBlockRecsTF` at the view `vis2`. (To be discharged by
helper `indproofs3-rec`'s refinement.) -/
def ConsRecsTFSim (p : Prog) : Prop :=
  ∀ (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis vis2 pp : Word) (fe : IFEnv) (m : Mem) (a : AState)
    (bs : BlockShape) (rr : List Word) (outs : List (IConstantVal × TargetMajor × List EIdx)),
    StageR dn vis fe m a → DecB (fun m => decBS m pp.toNat) m bs → decRRS m rr outs → HbMemo m → AbsOK m →
    Sim (callW p n "cons_block_recs_tf" [vis2, pp, 0, rr.headD 0, rr.tail.headD 0, vis] m)
      (ConRon.Arena.consBlockRecsTF vis2.toNat bs 0 outs fe) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m' ∧ AbsOK m')

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

/-- **`cons_block_recs_tf` as the tail needs it**, from its refinement. -/
theorem consRecsTFSim_of {p : Prog} (L : CbrLook p) {fs : List FnName}
    (hcl : closedA p hbFreeA hbFreeC fs = true) (hf : "cons_block_recs_tf" ∈ fs) :
    ConsRecsTFSim p := by
  intro n dn vis vis2 pp fe m a bs rr outs hS hbs hrr hM hA r m' hc
  obtain ⟨s', hs', -, hok, hS', hg, hA'⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (consBlockRecsTF_refines p L n _ a dn fe vis2 pp 0 (rr.headD 0) (rr.tail.headD 0) vis bs outs
      hS hbs hrr (by simpa using (rr.tail.headD 0).toNat_lt) hA) hc
  subst hs'
  have hrun := AM.run_of_ok _ a hok
  simp only [UInt64.toNat_zero] at hrun hS'
  exact ⟨_, _, hrun, hS', hg, HbMemo.ofClosed hcl hf hc hM, hA'⟩

end L.Ind

end
