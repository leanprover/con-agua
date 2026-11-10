module

import ConAgua.Arena.IWFrame
import ConAgua.Arena.IndPosSpec.NkcW
import ConAgua.Arena.StripTeleSpec
import ConAgua.Arena.WhnfSpineRefine
public import ConAgua.Arena.IndStubs
public import ConAgua.Arena.IndView
import ConAgua.L.WordOff

@[expose] public section

/-!
# Pos2DecHLSplit

`pos2_forall_view`, `pos2_ns_rd`, `pos2_decHL_split` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A `Π` handle's view: its domain and body, decoded. -/
theorem pos2_forall_view {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    {w : Word} (hS : StageR vis fe m a) (hw : H w) (h6 : tagW w = 6) (hne : eViewW m w ≠ []) :
    ∃ d b, eViewW m w = [6, d, b, 0] ∧ H d ∧ H b ∧
      (viewBind (decI w)).run a = .ok (some (decI d, decI b), a) ∧ (decI w : EIdx).tag = ETag.forallE := by
  obtain ⟨hvok, hew⟩ := eViewW_forall m w h6 hne
  obtain ⟨-, hty, hb⟩ := view_forall m a hS.check.arena.base w hw hvok h6
  have hvb := viewBind_forall m a hS.check.arena.base w hw hvok h6
  exact ⟨_, _, hew, hty, hb, by rw [viewBind_run']; simp only [← decE_eq]; rw [hvb],
    (decE_tag_forallE w hw).mpr h6⟩

/-- The words of a `NestState` record, read after the pool grew. -/
theorem pos2_ns_rd {m m' : Mem} (hg : IWGrow m m') {p : Word} (hp : p.toNat + 6 ≤ iwTop m)
    (htop : iwTop m < 2 ^ 64) (i : Word) (hi : i.toNat < 6) : rdW (m'.arr64 IW) (p + i) = rdW (m.arr64 IW) (p + i) :=
  rdW_iw_grow hg (by rw [L.toNat_add_of_lt _ _ (by omega)]; omega)

/-- A handle slice split at `k`. -/
theorem pos2_decHL_split {k : IdxKind} {m : Mem} {o l n : Nat} {xs : List (Idx k)} (h : decHL m o l = some xs)
    (hn : n ≤ l) : decHL m o n = some (xs.take n) ∧ decHL m (o + n) (l - n) = some (xs.drop n) := by
  obtain ⟨hl, hg⟩ := pos2_hslice_get h
  have get : ∀ j (hj : j < xs.length), iwH m (o + j) = some xs[j] := fun j hj => by
    have := mapM_opt_get (fun j => (hd? (iwA m) (o + j) : Option (Idx k))) (List.range l) xs h j
      (by simp; omega)
    simpa [iwH] using this
  constructor
  · have := decHL_of_get m (xs.take n) o (fun j hj => by
      simp only [List.length_take] at hj; rw [List.getElem_take]; exact get j (by omega))
    simpa [List.length_take, hl, Nat.min_eq_left hn] using this
  · have := decHL_of_get m (xs.drop n) (o + n) (fun j hj => by
      simp only [List.length_drop] at hj; rw [List.getElem_drop, show o + n + j = o + (n + j) by omega]
      exact get (n + j) (by omega))
    simpa [List.length_drop, hl] using this

/-- `aL == nPc + nI` on words is the twin's comparison, `nPc ≤ aL`. -/
theorem pos2_len_eq {aL nPc nI : Word} (h : nPc.toNat ≤ aL.toNat) :
    (aL = nPc + nI) ↔ aL.toNat = nPc.toNat + nI.toNat := by
  constructor
  · intro e
    rcases Nat.lt_or_ge (nPc.toNat + nI.toNat) (2 ^ 64) with hl | hl
    · rw [e, L.toNat_add_of_lt _ _ hl]
    · exfalso
      have := congrArg UInt64.toNat e; rw [UInt64.toNat_add] at this
      have := nI.toNat_lt; have := nPc.toNat_lt
      omega
  · intro e
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, ← e]; exact (Nat.mod_eq_of_lt aL.toNat_lt).symm

end L.Ind

end
