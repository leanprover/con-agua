import ConAgua.Arena.IndParts
import ConAgua.Arena.IndLibSpec

/-!
# Refinements of `IndParts` (lane `induct`): the record projections

A pure twin function of a decoded record is refined by an L function that reads the record:
the post says the memory is unchanged and the result word is the twin's value. The decoders are
`IndIface.lean`'s; `decAt_some`, `iwN_rdW` read a decoded field.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A decoded shape's fields. -/
theorem decBS_some {m : Mem} {p : Nat} {bs : BlockShape} (h : decBS m p = some bs) :
    decAt m (decPL m (decMS m)) p = some bs.members ∧ decAt m (decPL m (decRS m)) (p + 2) = some bs.recs ∧
    iwN m (p + 4) = some bs.nP ∧ iwH m (p + 5) = some bs.elim ∧ iwH m (p + 6) = some bs.resSort ∧
    iwB m (p + 7) = some bs.large ∧ iwB m (p + 8) = some bs.isProp := by
  rw [decBS] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, f, hf, g, hg, rfl⟩ := h
  exact ⟨ha, hb, hc, hd, he, hf, hg⟩

/-- The members' count of a decoded shape is word `p + 1`. -/
theorem decBS_k {m : Mem} {p : Nat} {bs : BlockShape} (h : decBS m p = some bs)
    (hp : p + 1 < 2 ^ 64) :
    rdW (m.arr64 IW) (UInt64.ofNat (p + 1)) = UInt64.ofNat bs.k := by
  obtain ⟨o, l, -, hl, hg⟩ := decAt_some (decBS_some h).1
  rw [(iwN_rdW hl hp).1, BlockShape.k, decPL_length m hg]


/-- **`block_shape_k` is `BlockShape.k`.** -/
@[refines ConRon.Arena.BlockShape.k]
theorem blockShapeK_refines (p : Prog) (hp : p.lookup "block_shape_k" = some blockShapeK)
    (n : Nat) (s₀ : St) (q : Word) (bs : BlockShape) (hq : decBS s₀.mem q.toNat = some bs)
    (hq1 : q.toNat + 1 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_k" [q]
    ⦃fun r s' => s' = s₀ ∧ r.headD 0 = UInt64.ofNat bs.k; ⊤⦄ := by
  have key := decBS_k hq hq1
  have e : UInt64.ofNat (q.toNat + 1) = q + 1 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  rw [e] at key
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeK]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish

end L.Ind
