import ConAgua.Arena.IndInstallSpec17
import ConAgua.Arena.IndInstallSpec8
import ConAgua.Arena.IndSumSpec12

/-!
# Refinements of `IndInstall`, part 18 (lane `indproofs2`, helper `install`): `checkBlockIdxSorts`,
the relation
-/

noncomputable section


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A pointer to `[off, len]` of level handles. -/
def decIS (m : Mem) (rp : Nat) : Option (List LIdx) := decAt m (decHL m) rp

theorem decIS_mono (q : Nat) : OMono (fun m => decIS m q) :=
  OMono.decAt (fun o l => OMono.decHL o l) q

/-- **A model-only tail** after the twin's last step. -/
theorem _root_.L.Arena.Sim.tail {β γ α : Type} {K : Option (β × Mem) → Option (γ × Mem)} {body : β → Mem → Option (γ × Mem)}
    {mo : Option (β × Mem)} {op : AM α} {a : AState} {Q : β → α → Mem → AState → Prop}
    {R : γ → α → Mem → AState → Prop}
    (hn : K Option.none = Option.none) (hs : ∀ r m₁, K (some (r, m₁)) = body r m₁)
    (h : Sim mo op a Q) (h2 : ∀ r x m₁ a₁, Q r x m₁ a₁ → ∀ r' m', body r m₁ = some (r', m') → R r' x m' a₁) :
    Sim (K mo) op a R := by
  intro r' m' e
  cases hmo : mo with
  | none => rw [hmo, hn] at e; cases e
  | some x =>
    obtain ⟨r, m₁⟩ := x
    rw [hmo, hs] at e
    obtain ⟨y, a₁, h1, hq⟩ := h r m₁ hmo
    exact ⟨y, a₁, h1, h2 r y m₁ a₁ hq r' m' e⟩

/-- One member's index sorts, as the twin computes them. -/
def idxOneAM (fe : IFEnv) (bs : BlockShape) (ms : MemberShape) (cvTa : IConstantVal) : AM (List LIdx) := do
  let tq ← unwrapOr (← openPisAtFvarsF (bs.nP + ms.nIdx) cvTa.type 0)
    (.internal "direct rec: type former telescope")
  checkStructFieldSortsI V fe true false bs.resSort bs.nP (tq.1.drop bs.nP) [] ms.nIdx

theorem installIdx_cons (fe : IFEnv) (bs : BlockShape) (ms : MemberShape) (rest : List MemberShape)
    (cvTa : IConstantVal) (cvTas : List IConstantVal) :
    ConRon.Arena.checkBlockIdxSorts V fe bs (ms :: rest) (cvTa :: cvTas) =
      (idxOneAM fe bs ms cvTa >>= fun is =>
        ConRon.Arena.checkBlockIdxSorts V fe bs rest cvTas >>= fun rs => pure (is :: rs)) := by
  simp only [ConRon.Arena.checkBlockIdxSorts, idxOneAM, bind_assoc]

/-- A handle slice whose tail past `k` is taken: `idxTail`'s slice. -/
theorem installIdxTail {m : Mem} {o l : Word} {xs : List EIdx} {k : Word}
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    decHL m (idxTail k o l).1.toNat (idxTail k o l).2.toNat = some (xs.drop k.toNat) ∧
      (idxTail k o l).1.toNat + (idxTail k o l).2.toNat ≤ iwTop m := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hlen := decHL_length m hd
  unfold idxTail
  split
  · rename_i hk
    have hk' : k.toNat < l.toNat := hk
    have e1 : (o + k).toNat = o.toNat + k.toNat := by rw [UInt64.toNat_add]; omega
    have e2 : (l - k).toNat = l.toNat - k.toNat := UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]; omega)
    rw [e1, e2]
    exact ⟨decHL_drop k.toNat hd (by omega), by omega⟩
  · rename_i hk
    have hk' : ¬ k.toNat < l.toNat := hk
    have : xs.drop k.toNat = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]
    exact ⟨by simp [decHL, hslice?], by simp⟩

/-- The lookups of `check_block_idx_sorts`. -/
structure IdxProg (p : Prog) : Prop extends CstProg p where
  rec2 : p.lookup "rec2" = some rec2
  one : p.lookup "check_block_idx_sorts_one" = some checkBlockIdxSortsOne
  idx : p.lookup "check_block_idx_sorts" = some checkBlockIdxSorts
  sum : SumProg p

end L.Ind
