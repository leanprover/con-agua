import ConAgua.Arena.IndCopy2
import ConAgua.Arena.IndParts
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# RulePrefixAt: `ConRon.Arena.BlockShape.k`, `ConRon.Arena.BlockShape.majorIdxAt`, `ConRon.Arena.BlockShape.nIdxs`, `ConRon.Arena.BlockShape.numCtors`, `ConRon.Arena.BlockShape.rulePrefixAt`, `ConRon.Arena.numCtorsOf`

The refinement theorems `blockShapeK_refines`, `blockShapeRulePrefixAt_refines`, `blockShapeMajorIdxAt_refines`, `numCtorsOf_refines`, `blockShapeNumCtors_refines`, `blockShapeNIdxs_refines` and the lemmas only they use.
-/

noncomputable section

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

/-- **A continuation `K` (`K none = none`) that returned: its argument did** (the model's callee
split in one line: `obtain ⟨r, m₁, hc, h⟩ := ipK_inv h (by simp [K])`). -/
theorem ipK_inv {β γ : Type} {K : Option (β × Mem) → Option γ} {o : Option (β × Mem)} {y : γ}
    (h : K o = some y) (hn : K none = none) : ∃ r m, o = some (r, m) ∧ K (some (r, m)) = some y := by
  rcases o with _ | ⟨r, m⟩
  · rw [hn] at h; cases h
  · exact ⟨r, m, rfl, h⟩

/-- `ipK_inv` for a callee with one result. -/
theorem ipK_inv1 {β γ : Type} {K : Option β → Option γ} {o : Option β} {y : γ} (h : K o = some y)
    (hn : K none = none) : ∃ r, o = some r ∧ K (some r) = some y := by
  rcases o with _ | r
  · rw [hn] at h; cases h
  · exact ⟨r, rfl, h⟩

/-! ## Small Word arithmetic helpers, reused throughout this file -/

/-- `UInt64.ofNat` is additive (both sides are mod `2 ^ 64`, so no overflow side condition). -/
theorem ofNat_add_word (a b : Nat) : UInt64.ofNat (a + b) = UInt64.ofNat a + UInt64.ofNat b := by
  apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp

/-- `UInt64.ofNat` roundtrips a word. -/
theorem ofNat_toNat_word (w : Word) : UInt64.ofNat w.toNat = w := by
  apply UInt64.toNat_inj.mp; simp

/-! ## From `decPL`'s `mapM` to a head/tail unfolding (as `hslice?_succ` does for `decHL`) -/

theorem mapM_shift_succ {α : Type} (g : Nat → Option α) (off n : Nat) :
    (List.range (n + 1)).mapM (fun j => g (off + j)) = (do
      let x ← g off
      let xs ← (List.range n).mapM (fun j => g (off + 1 + j))
      pure (x :: xs)) := by
  simp only [List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range n))
  funext j; simp only [Function.comp]; congr 1; omega

/-- **`decPL` unfolds head first**, as `hslice?_succ` does for `decHL`. -/
theorem decPL_succ {m : Mem} {α : Type} (f : Nat → Option α) (off n : Nat) :
    decPL m f off (n + 1) = (do
      let v ← iwN m off
      let x ← f v
      let xs ← decPL m f (off + 1) n
      pure (x :: xs)) := by
  have e1 : decPL m f off (n + 1) = (List.range (n + 1)).mapM (fun j => (iwN m (off + j)).bind f) :=
    rfl
  have e2 : decPL m f (off + 1) n = (List.range n).mapM (fun j => (iwN m (off + 1 + j)).bind f) :=
    rfl
  rw [e1, e2, mapM_shift_succ (fun i => (iwN m i).bind f) off n]
  cases iwN m off <;> rfl

/-- **Indexing a `decPL` result**: element `j` decodes the pointer word at `o + j`, to some value
`y` at that index of the decoded list (`xs[j]?`). -/
theorem decPL_get {m : Mem} {α : Type} {f : Nat → Option α} :
    ∀ (l o : Nat) (xs : List α), decPL m f o l = some xs → ∀ (j : Nat), j < l →
    ∃ v y, iwN m (o + j) = some v ∧ f v = some y ∧ xs[j]? = some y
  | 0, _, _, _, _, hj => absurd hj (by omega)
  | k + 1, o, xs, h, j, hj => by
    rw [decPL_succ] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨v0, hv0, x0, hx0, xs', hxs', rfl⟩ := h
    cases j with
    | zero => exact ⟨v0, x0, by simpa using hv0, hx0, by simp⟩
    | succ j' =>
      obtain ⟨v, y, hv, hf, hget⟩ := decPL_get k (o + 1) xs' hxs' j' (by omega)
      refine ⟨v, y, ?_, hf, ?_⟩
      · have e : o + (j' + 1) = o + 1 + j' := by omega
        rw [e]; exact hv
      · simpa using hget

/-- `RecShape`'s fields: `cvR` is read through an indirection (`decRS` first reads the pointer
word at `p`, then decodes the constant there). -/
theorem decRS_some {m : Mem} {p : Nat} {rs : RecShape} (h : decRS m p = some rs) :
    (∃ a, iwN m p = some a ∧ decCVp m a = some rs.cvR) ∧ iwN m (p + 1) = some rs.rP ∧
    iwN m (p + 2) = some rs.mI ∧ iwN m (p + 3) = some rs.tgt ∧
    decAt m (decHL m) (p + 4) = some rs.rhss := by
  rw [decRS] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, f, hf, rfl⟩ := h
  exact ⟨⟨a, ha, hb⟩, hc, hd, he, hf⟩

/-- `MemberShape`'s fields: `cvT` is read through the same indirection. -/
theorem decMS_some {m : Mem} {p : Nat} {ms : MemberShape} (h : decMS m p = some ms) :
    (∃ a, iwN m p = some a ∧ decCVp m a = some ms.cvT) ∧ iwN m (p + 1) = some ms.nIdx ∧
    decAt m (decPL m (decCN m)) (p + 2) = some ms.ctors := by
  rw [decMS] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
  exact ⟨⟨a, ha, hb⟩, hc, hd⟩

/-! ## `BlockShape.rulePrefixAt`, `BlockShape.majorIdxAt` -/

/-- **`block_shape_rule_prefix_at` is `BlockShape.rulePrefixAt`.** -/
@[refines ConRon.Arena.BlockShape.rulePrefixAt]
theorem blockShapeRulePrefixAt_refines (p : Prog)
    (hp : p.lookup "block_shape_rule_prefix_at" = some blockShapeRulePrefixAt) (n : Nat) (s₀ : St)
    (q r : Word) (bs : BlockShape) (hq : decBS s₀.mem q.toNat = some bs)
    (hb : q.toNat + 9 < 2 ^ 64) (_hrw : r.toNat < 2 ^ 64)
    (hol : ∀ o l, iwN s₀.mem (q.toNat + 2) = some o → iwN s₀.mem (q.toNat + 3) = some l →
      o + l < 2 ^ 64)
    (hov : ∀ o l v, iwN s₀.mem (q.toNat + 2) = some o → iwN s₀.mem (q.toNat + 3) = some l →
      iwN s₀.mem (o + r.toNat) = some v → v + 1 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_rule_prefix_at" [q, r]
    ⦃fun res s' => s' = s₀ ∧ res.headD 0 = UInt64.ofNat (bs.rulePrefixAt r.toNat); ⊤⦄ := by
  obtain ⟨o, l, ho, hl, hg⟩ := decAt_some (decBS_some hq).2.1
  have holl := hol o l ho hl
  obtain ⟨ho', -⟩ := iwN_rdW ho (by omega)
  obtain ⟨hl', hlb⟩ := iwN_rdW hl (by omega)
  have e2 : UInt64.ofNat (q.toNat + 2) = q + 2 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  have e3 : UInt64.ofNat (q.toNat + 3) = q + 3 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  rw [e2] at ho'; rw [e3] at hl'
  have hlo : (UInt64.ofNat l).toNat = l := by simp [hlb]
  rw [BlockShape.rulePrefixAt]
  by_cases hlen : l < r.toNat + 1
  have hNone : bs.recs[r.toNat]? = none := by
    rw [List.getElem?_eq_none_iff, decPL_length s₀.mem hg]; omega
  rw [hNone]
  have hc : UInt64.ofNat l ≤ r := by
    apply UInt64.le_iff_toNat_le.mpr; rw [hlo]; omega
  rotate_left
  obtain ⟨v, y, hv, hf, hget⟩ := decPL_get l o bs.recs hg r.toNat (by omega)
  obtain ⟨-, hrP, -, -, -⟩ := decRS_some hf
  rw [hget]
  have hovv := hov o l v ho hl hv
  obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
  have ev : UInt64.ofNat (o + r.toNat) = UInt64.ofNat o + r := by
    rw [ofNat_add_word, ofNat_toNat_word]
  rw [ev] at hv'
  obtain ⟨hw1, -⟩ := iwN_rdW hrP (by omega)
  have ew : UInt64.ofNat (v + 1) = UInt64.ofNat v + 1 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  rw [ew] at hw1
  have hc : ¬ UInt64.ofNat l ≤ r := by
    intro hcontra
    have := UInt64.le_iff_toNat_le.mp hcontra
    rw [hlo] at this; omega
  all_goals
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapeRulePrefixAt]
    cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      sym only [lang_grind, arena_grind] =>
        vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
        finish

/-- **`block_shape_major_idx_at` is `BlockShape.majorIdxAt`.** -/
@[refines ConRon.Arena.BlockShape.majorIdxAt]
theorem blockShapeMajorIdxAt_refines (p : Prog)
    (hp : p.lookup "block_shape_major_idx_at" = some blockShapeMajorIdxAt) (n : Nat) (s₀ : St)
    (q r : Word) (bs : BlockShape) (hq : decBS s₀.mem q.toNat = some bs)
    (hb : q.toNat + 9 < 2 ^ 64) (_hrw : r.toNat < 2 ^ 64)
    (hol : ∀ o l, iwN s₀.mem (q.toNat + 2) = some o → iwN s₀.mem (q.toNat + 3) = some l →
      o + l < 2 ^ 64)
    (hov : ∀ o l v, iwN s₀.mem (q.toNat + 2) = some o → iwN s₀.mem (q.toNat + 3) = some l →
      iwN s₀.mem (o + r.toNat) = some v → v + 2 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_major_idx_at" [q, r]
    ⦃fun res s' => s' = s₀ ∧ res.headD 0 = UInt64.ofNat (bs.majorIdxAt r.toNat); ⊤⦄ := by
  obtain ⟨o, l, ho, hl, hg⟩ := decAt_some (decBS_some hq).2.1
  have holl := hol o l ho hl
  obtain ⟨ho', -⟩ := iwN_rdW ho (by omega)
  obtain ⟨hl', hlb⟩ := iwN_rdW hl (by omega)
  have e2 : UInt64.ofNat (q.toNat + 2) = q + 2 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  have e3 : UInt64.ofNat (q.toNat + 3) = q + 3 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  rw [e2] at ho'; rw [e3] at hl'
  have hlo : (UInt64.ofNat l).toNat = l := by simp [hlb]
  rw [BlockShape.majorIdxAt]
  by_cases hlen : l < r.toNat + 1
  have hNone : bs.recs[r.toNat]? = none := by
    rw [List.getElem?_eq_none_iff, decPL_length s₀.mem hg]; omega
  rw [hNone]
  have hc : UInt64.ofNat l ≤ r := by
    apply UInt64.le_iff_toNat_le.mpr; rw [hlo]; omega
  rotate_left
  obtain ⟨v, y, hv, hf, hget⟩ := decPL_get l o bs.recs hg r.toNat (by omega)
  obtain ⟨-, -, hmI, -, -⟩ := decRS_some hf
  rw [hget]
  have hovv := hov o l v ho hl hv
  obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
  have ev : UInt64.ofNat (o + r.toNat) = UInt64.ofNat o + r := by
    rw [ofNat_add_word, ofNat_toNat_word]
  rw [ev] at hv'
  obtain ⟨hw1, -⟩ := iwN_rdW hmI (by omega)
  have ew : UInt64.ofNat (v + 2) = UInt64.ofNat v + 2 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  rw [ew] at hw1
  have hc : ¬ UInt64.ofNat l ≤ r := by
    intro hcontra
    have := UInt64.le_iff_toNat_le.mp hcontra
    rw [hlo] at this; omega
  all_goals
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapeMajorIdxAt]
    cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      sym only [lang_grind, arena_grind] =>
        vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
        finish

/-! ## `numCtorsOf`, `BlockShape.numCtors` -/

/-- The model of `num_ctors_of`. -/
def numCtorsOfW : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, off, l =>
    if l = 0 then some 0
    else numCtorsOfW.cons m off (numCtorsOfW n m (off + 1) (l - 1))
where
  /-- After the recursive call: add this member's own `ctors.len` (`none` when the sum wraps). -/
  cons (m : Mem) (off : Word) : Option Word → Option Word
    | none => none
    | some r => if rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) + r < r then none
      else some (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) + r)

section arms
variable (n : Nat) (m : Mem) (off l r : Word)
theorem numCtorsOfW_nil (hl : l = 0) : numCtorsOfW (n + 1) m off l = some 0 := by
  simp [numCtorsOfW, hl]
theorem numCtorsOfW_cons (hl : l ≠ 0) :
    numCtorsOfW (n + 1) m off l = numCtorsOfW.cons m off (numCtorsOfW n m (off + 1) (l - 1)) := by
  simp [numCtorsOfW, hl]
theorem numCtorsOfW_cons_some (h : ¬ rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) + r < r) :
    numCtorsOfW.cons m off (some r) =
      some (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) + r) := by simp [numCtorsOfW.cons, h]
theorem numCtorsOfW_cons_wrap (h : rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) + r < r) :
    numCtorsOfW.cons m off (some r) = none := by simp [numCtorsOfW.cons, h]
end arms

grind_pattern [ind_grind] numCtorsOfW_nil => numCtorsOfW (n + 1) m off l
grind_pattern [ind_grind] numCtorsOfW_cons => numCtorsOfW (n + 1) m off l
grind_pattern [ind_grind] numCtorsOfW_cons_some => numCtorsOfW.cons m off (some r)
grind_pattern [ind_grind] numCtorsOfW_cons_wrap => numCtorsOfW.cons m off (some r)

section specs
variable (p : Prog)

theorem numCtorsOf_spec (hp : p.lookup "num_ctors_of" = some numCtorsOf) (n : Nat) :
    ∀ (s₀ : St) (off l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "num_ctors_of" [off, l]
    ⦃fun r s' => s' = s₀ ∧ numCtorsOfW n s₀.mem off l = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ off l; rw [invoke_eq _ hp]; simp only [callFn, numCtorsOf]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ off l
    rw [invoke_eq _ hp]
    simp only [callFn, numCtorsOf]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)

end specs

/-- A sum of words that does not wrap (`¬ a + b < b`) is the sum of the naturals. -/
theorem nctAddNowrap {a b : Word} (h : ¬ a + b < b) : a.toNat + b.toNat < 2 ^ 64 := by
  have h1 := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h)
  rw [UInt64.toNat_add] at h1
  have ha := a.toNat_lt; have hb := b.toNat_lt
  omega

theorem numCtorsOfW_ok (n : Nat) : ∀ (m : Mem) (off l r : Word) (ms : List MemberShape),
    (m.arr64 IW).size < 2 ^ 64 →
    off.toNat + l.toNat < 2 ^ 64 → decPL m (decMS m) off.toNat l.toNat = some ms →
    numCtorsOfW n m off l = some r →
    r = UInt64.ofNat (ConRon.Arena.numCtorsOf ms) ∧ ConRon.Arena.numCtorsOf ms < 2 ^ 64 := by
  induction n with
  | zero => intro m off l r ms _ _ _ h; simp [numCtorsOfW] at h
  | succ n ih =>
    intro m off l r ms hsmall hbnd hd h
    by_cases hl : l = 0
    · rw [numCtorsOfW_nil n m off l hl] at h
      have hl0 : l.toNat = 0 := by
        have := congrArg UInt64.toNat hl; simpa using this
      rw [hl0] at hd
      simp only [decPL, List.range_zero, List.mapM_nil, pure, Option.some.injEq] at hd
      simp only [Option.some.injEq] at h
      simp [← hd, ConRon.Arena.numCtorsOf, ← h]
    · obtain ⟨k, hk⟩ : ∃ k, l.toNat = k + 1 := by
        have : l.toNat ≠ 0 := fun h0 => hl (by
          apply UInt64.toNat_inj.mp; simpa using h0)
        exact ⟨l.toNat - 1, by omega⟩
      rw [hk] at hd
      rw [decPL_succ] at hd
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hd
      obtain ⟨v, hv, ms0, hms0, mrest, hmrest, rfl⟩ := hd
      have hoff1 : (off + 1).toNat = off.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      have hl1 : (l - 1).toNat = k := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp [hk]
      have hd1 : decPL m (decMS m) (off + 1).toNat (l - 1).toNat = some mrest := by
        rw [hoff1, hl1]; exact hmrest
      have hbnd1 : (off + 1).toNat + (l - 1).toNat < 2 ^ 64 := by rw [hoff1, hl1]; omega
      cases hcons : numCtorsOfW n m (off + 1) (l - 1) with
      | none =>
        exfalso
        have hcontra : numCtorsOfW (n + 1) m off l = none := by
          simp [numCtorsOfW, numCtorsOfW.cons, hl, hcons]
        rw [hcontra] at h; simp at h
      | some r' =>
        rw [numCtorsOfW_cons n m off l hl, hcons] at h
        obtain ⟨hr', hlt'⟩ := ih m (off + 1) (l - 1) r' mrest hsmall hbnd1 hd1 hcons
        have hv3 : v + 3 < 2 ^ 64 := by
          obtain ⟨_, _, _, hl3, _⟩ := decAt_some (decMS_some hms0).2.2
          have : v + 2 + 1 < (m.arr64 IW).size := by
            simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at hl3
            obtain ⟨w, hw, -⟩ := hl3
            exact (Array.getElem?_eq_some_iff.mp hw).1
          omega
        have hv' := (iwN_rdW hv (by omega)).1
        rw [ofNat_toNat_word] at hv'
        have hdm := decMS_some hms0
        obtain ⟨o2, l2, ho2, hl2, hg2⟩ := decAt_some hdm.2.2
        have heq1 : v + 2 + 1 = v + 3 := by omega
        rw [heq1] at hl2
        have hl2rd := (iwN_rdW hl2 (by omega)).1
        have e3 : UInt64.ofNat (v + 3) = UInt64.ofNat v + 3 := by
          apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
        rw [e3, ← hv'] at hl2rd
        by_cases hw : rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) + r' < r'
        · rw [numCtorsOfW_cons_wrap _ _ _ hw] at h; cases h
        rw [numCtorsOfW_cons_some _ _ _ hw] at h
        have hnw := nctAddNowrap hw
        simp only [Option.some.injEq] at h
        rw [hl2rd, hr'] at h hnw
        have hl2b : l2 < 2 ^ 64 := by
          simp only [iwN, nat?, Option.map_eq_some_iff] at hl2
          obtain ⟨w, -, rfl⟩ := hl2; exact w.toNat_lt
        rw [UInt64.toNat_ofNat_of_lt' (show l2 < UInt64.size from hl2b),
          UInt64.toNat_ofNat_of_lt' (show _ < UInt64.size from hlt')] at hnw
        rw [← ofNat_add_word] at h
        rw [← decPL_length m hg2] at h hnw
        simp only [ConRon.Arena.numCtorsOf]
        exact ⟨h.symm, hnw⟩

/-- **`num_ctors_of` is `numCtorsOf`.** -/
@[refines ConRon.Arena.numCtorsOf]
theorem numCtorsOf_refines (p : Prog) (hp : p.lookup "num_ctors_of" = some numCtorsOf) (n : Nat)
    (s₀ : St) (off l : Word) (ms : List MemberShape)
    (hsmall : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hd : decPL s₀.mem (decMS s₀.mem) off.toNat l.toNat = some ms)
    (hbnd : off.toNat + l.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "num_ctors_of" [off, l]
    ⦃fun r s' => s' = s₀ ∧ r.headD 0 = UInt64.ofNat (ConRon.Arena.numCtorsOf ms) ∧
      ConRon.Arena.numCtorsOf ms < 2 ^ 64; ⊤⦄ := by
  have h := numCtorsOf_spec p hp n s₀ off l
  refine triple_post h ?_
  intro r s' ⟨h1, h2⟩
  exact ⟨h1, (numCtorsOfW_ok n s₀.mem off l (r.headD 0) ms hsmall hbnd hd h2)⟩

/-! ## `BlockShape.numCtors`: the word-model idiom for a caller

`vcgen`'s callee-spec search wants a callee spec with no decoder hypotheses (PLAN.md's
"precondition-only arguments stay metavariables"): give it `numCtorsOf_spec` (the word-model
spec), prove `block_shape_num_ctors`'s own word-model spec by `vcgen`, and only then, outside
`vcgen`, compose with `numCtorsOfW_ok` and `decBS_some` to reach the twin value. -/

theorem blockShapeNumCtorsW_spec (p : Prog) (hc : p.lookup "num_ctors_of" = some numCtorsOf)
    (hp : p.lookup "block_shape_num_ctors" = some blockShapeNumCtors) (n : Nat) (s₀ : St)
    (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_shape_num_ctors" [q]
    ⦃fun r s' => s' = s₀ ∧
      numCtorsOfW n s₀.mem (rdW (s₀.mem.arr64 IW) q) (rdW (s₀.mem.arr64 IW) (q + 1)) =
        some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeNumCtors]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, numCtorsOf_spec p hc n] <;>
    finish [rdW_eq]

/-- The model, decoded: `BlockShape.numCtors` at a `BlockShape` pointer `q`. -/
theorem blockShapeNumCtorsW_ok (n : Nat) (m : Mem) (q r : Word) (bs : BlockShape)
    (hq : decBS m q.toNat = some bs) (hb : q.toNat + 9 < 2 ^ 64)
    (hol : ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l < 2 ^ 64)
    (hsmall : (m.arr64 IW).size < 2 ^ 64)
    (h : numCtorsOfW n m (rdW (m.arr64 IW) q) (rdW (m.arr64 IW) (q + 1)) = some r) :
    r = UInt64.ofNat bs.numCtors := by
  obtain ⟨o, l, ho, hl, hg⟩ := decAt_some (decBS_some hq).1
  obtain ⟨ho', hob⟩ := iwN_rdW ho (by omega)
  obtain ⟨hl', hlb⟩ := iwN_rdW hl (by omega)
  have e1 : UInt64.ofNat (q.toNat + 1) = q + 1 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  rw [ofNat_toNat_word] at ho'
  rw [e1] at hl'
  have hoo : (UInt64.ofNat o).toNat = o := by simp [hob]
  have hll : (UInt64.ofNat l).toNat = l := by simp [hlb]
  have hd2 : decPL m (decMS m) (UInt64.ofNat o).toNat (UInt64.ofNat l).toNat =
      some bs.members := by rw [hoo, hll]; exact hg
  have hbnd2 : (UInt64.ofNat o).toNat + (UInt64.ofNat l).toNat < 2 ^ 64 := by
    rw [hoo, hll]; exact hol o l ho hl
  rw [ho', hl'] at h
  rw [BlockShape.numCtors]
  exact (numCtorsOfW_ok n m (UInt64.ofNat o) (UInt64.ofNat l) r bs.members hsmall hbnd2 hd2 h).1

/-- **`block_shape_num_ctors` is `BlockShape.numCtors`.** -/
@[refines ConRon.Arena.BlockShape.numCtors]
theorem blockShapeNumCtors_refines (p : Prog) (hc : p.lookup "num_ctors_of" = some numCtorsOf)
    (hp : p.lookup "block_shape_num_ctors" = some blockShapeNumCtors) (n : Nat) (s₀ : St)
    (q : Word) (bs : BlockShape) (hq : decBS s₀.mem q.toNat = some bs)
    (hb : q.toNat + 9 < 2 ^ 64)
    (hol : ∀ o l, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l →
      o + l < 2 ^ 64)
    (hsmall : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_num_ctors" [q]
    ⦃fun r s' => s' = s₀ ∧ r.headD 0 = UInt64.ofNat bs.numCtors; ⊤⦄ := by
  cases n with
  | zero =>
    rw [invoke_eq _ hp]; simp only [callFn, blockShapeNumCtors]; vcgen [exec] <;> grind
  | succ n =>
    have h := blockShapeNumCtorsW_spec p hc hp n s₀ q
    refine triple_post h ?_
    intro r s' ⟨h1, h2⟩
    exact ⟨h1, blockShapeNumCtorsW_ok n s₀.mem q (r.headD 0) bs hq hb hol hsmall h2⟩

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `BlockShape.nIdxs`: a copy with one extra indirection per element

`n_idxs_copy` is `iw_copy`-shaped (`IndCopy.lean`'s `copyW`/`copyW_get`) but each written word is
the member pointer's OWN `nIdx` field, not the pointer itself: one more indirection, both reads
(the pointer, then its field) off the source side, which stays frozen throughout (the destination
is the fresh top, disjoint from both the source slice and the member records it points into). -/

/-- `UInt64.size` is `2 ^ 64`. -/
theorem UInt64_size_eq : UInt64.size = 2 ^ 64 := rfl

/-- The model of `n_idxs_copy`. -/
def nIdxsCopyW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, d, s, l =>
    if l = 0 then some m
    else nIdxsCopyW n (m.set64 IW d (rdW (m.arr64 IW) (rdW (m.arr64 IW) s + 1))) (d + 1) (s + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (d s l : Word)
theorem nIdxsCopyW_nil (hl : l = 0) : nIdxsCopyW (n + 1) m d s l = some m := by
  simp [nIdxsCopyW, hl]
theorem nIdxsCopyW_step (hl : l ≠ 0) :
    nIdxsCopyW (n + 1) m d s l =
      nIdxsCopyW n (m.set64 IW d (rdW (m.arr64 IW) (rdW (m.arr64 IW) s + 1))) (d + 1) (s + 1) (l - 1) := by
  simp [nIdxsCopyW, hl]
end arms

grind_pattern [ind_grind] nIdxsCopyW_nil => nIdxsCopyW (n + 1) m d s l
grind_pattern [ind_grind] nIdxsCopyW_step => nIdxsCopyW (n + 1) m d s l

theorem nIdxsCopy_spec (p : Prog) (hp : p.lookup "n_idxs_copy" = some nIdxsCopy) (n : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "n_idxs_copy" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ nIdxsCopyW n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ d s l; rw [invoke_eq _ hp]; simp only [callFn, nIdxsCopy]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ d s l
    rw [invoke_eq _ hp]
    simp only [callFn, nIdxsCopy]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20)

/-- A write at a position other than `d` does not change the read at another position. -/
theorem rdW_set64_IW_ne (m : Mem) (d v x : Word) (h : x.toNat ≠ d.toNat) :
    rdW ((m.set64 IW d v).arr64 IW) x = rdW (m.arr64 IW) x := by
  simp only [rdW]
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [Ne.symm h]

/-- **What a copy loop leaves** (`n_idxs_copy`, `member_names_copy`): the model `W` writes
`g m (rdW IW s)` to `IW[d]`, `l` times, where the read `g` at a pointer `x` with `P x d` sees no
`IW` cell at or above `d`; the destination slice then holds the reads off the ORIGINAL memory. -/
theorem ipCopyW_get (W : Nat → Mem → Word → Word → Word → Option Mem) (g : Mem → Word → Word)
    (P : Word → Nat → Prop) (h0 : ∀ m d s l, W 0 m d s l = none)
    (hnil : ∀ n m d s l, l = 0 → W (n + 1) m d s l = some m)
    (hstep : ∀ n m d s l, l ≠ 0 → W (n + 1) m d s l =
      W n (m.set64 IW d (g m (rdW (m.arr64 IW) s))) (d + 1) (s + 1) (l - 1))
    (hg : ∀ m d v x, P x d.toNat → g (m.set64 IW d v) x = g m x)
    (hP : ∀ x d, P x d → P x (d + 1)) (n : Nat) :
    ∀ (m m' : Mem) (d s l : Word), W n m d s l = some m' →
    s.toNat + l.toNat ≤ d.toNat → d.toNat + l.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 →
    (∀ j < l.toNat, P (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + j))) d.toNat) →
    (∀ b, b ≠ IW → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 IW).size = (m.arr64 IW).size ∧
    m'.words.size = m.words.size ∧
    ∀ i, (m'.arr64 IW)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat
      then some (g m (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (i - d.toNat)))))
      else (m.arr64 IW)[i]? := by
  induction n with
  | zero => intro m m' d s l h; simp [h0] at h
  | succ n ih =>
    intro m m' d s l h hsd hd hsz hptr
    by_cases hl : l = 0
    · rw [hnil n m d s l hl] at h
      cases h
      subst hl
      refine ⟨fun _ _ => rfl, rfl, rfl, fun i => ?_⟩
      have : ¬ (d.toNat ≤ i ∧ i < d.toNat + (0 : Word).toNat) := by
        simp only [UInt64.toNat_zero]; omega
      simp only [this, ite_false]
    rw [hstep n m d s l hl] at h
    have hl0 : 0 < l.toNat := by
      have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
      omega
    have hl1 : (l - 1).toNat = l.toNat - 1 := by rw [UInt64.toNat_sub]; simp; omega
    have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hs1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hdlt : d.toNat < (m.arr64 IW).size := by omega
    obtain ⟨v, hv⟩ : ∃ v : Word, v = g m (rdW (m.arr64 IW) s) := ⟨_, rfl⟩
    rw [← hv] at h
    obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.set64 IW d v := ⟨_, rfl⟩
    rw [← hm1] at h
    have hsz1 : (m1.arr64 IW).size = (m.arr64 IW).size := by
      rw [hm1, Mem.arr64_set64_same]; simp
    have hm1get : ∀ i, (m1.arr64 IW)[i]? = if i = d.toNat then some v else (m.arr64 IW)[i]? := by
      intro i
      rw [hm1, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases hi : d.toNat = i
      · subst hi; simp only [hdlt, ite_true]
      · simp [hi, Ne.symm hi]
    have hrd : ∀ x : Word, x.toNat ≠ d.toNat → rdW (m1.arr64 IW) x = rdW (m.arr64 IW) x := by
      intro x hx; rw [hm1]; exact rdW_set64_IW_ne m d v x hx
    have hsrc : ∀ j < l.toNat, rdW (m1.arr64 IW) (UInt64.ofNat (s.toNat + j)) =
        rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + j)) := fun j hj =>
      hrd _ (by rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; omega)
    have hptr1 : ∀ j < (l - 1).toNat,
        P (rdW (m1.arr64 IW) (UInt64.ofNat ((s + 1).toNat + j))) (d + 1).toNat := by
      intro j hj
      rw [hl1] at hj
      rw [hs1, show s.toNat + 1 + j = s.toNat + (j + 1) by omega, hsrc _ (by omega), hd1]
      exact hP _ _ (hptr (j + 1) (by omega))
    obtain ⟨hA, hS, hW, hG⟩ := ih m1 m' (d + 1) (s + 1) (l - 1) h
      (by rw [hs1, hd1, hl1]; omega) (by rw [hd1, hl1, hsz1]; omega) (by rw [hsz1]; exact hsz)
      hptr1
    refine ⟨fun b hb => (hA b hb).trans ?_, hS.trans hsz1, hW.trans ?_, fun i => ?_⟩
    · rw [hm1, Mem.arr64_set64_ne _ _ _ _ _ hb]
    · rw [hm1]; exact Mem.words_size_set64 _ _ _ _
    rw [hG i, hd1, hl1, hs1]
    by_cases hi : d.toNat ≤ i ∧ i < d.toNat + l.toNat
    · rw [ite_eq_left hi]
      by_cases hid : i = d.toNat
      · subst hid
        rw [ite_eq_right (by omega), show s.toNat + (d.toNat - d.toNat) = s.toNat by omega,
                ofNat_toNat_word, hm1get, ite_eq_left rfl, hv]
      · rw [ite_eq_left (by omega), show s.toNat + 1 + (i - (d.toNat + 1)) = s.toNat + (i - d.toNat) by omega,
               hsrc _ (by omega), hm1, hg _ _ _ _ (hptr _ (by omega))]
    · rw [ite_eq_right hi, ite_eq_right (by omega), hm1get, ite_eq_right (by omega)]

/-- **What `n_idxs_copy` leaves**, as `copyW_get` does for `iw_copy`: the destination slice holds
each source pointer's `nIdx` field, read off the ORIGINAL memory throughout (both the pointer
read at `s + j` and the field read at `p + 1`, `p` that pointer, lie below the fresh destination
`d`, so neither is ever disturbed by this function's own writes). -/
theorem nIdxsCopyW_get (n : Nat) : ∀ (m m' : Mem) (d s l : Word), nIdxsCopyW n m d s l = some m' →
    s.toNat + l.toNat ≤ d.toNat → d.toNat + l.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 →
    (∀ j < l.toNat, (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + j)) + 1).toNat < d.toNat) →
    (∀ b, b ≠ IW → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 IW).size = (m.arr64 IW).size ∧
    m'.words.size = m.words.size ∧
    ∀ i, (m'.arr64 IW)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat
      then some (rdW (m.arr64 IW) (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (i - d.toNat))) + 1))
      else (m.arr64 IW)[i]? :=
  ipCopyW_get nIdxsCopyW (fun m x => rdW (m.arr64 IW) (x + 1)) (fun x d => (x + 1).toNat < d)
    (fun _ _ _ _ => by simp [nIdxsCopyW]) (nIdxsCopyW_nil · · · · ·) (nIdxsCopyW_step · · · · ·)
    (fun m d v x hx => rdW_set64_IW_ne m d v _ (by omega)) (fun _ _ h => by omega) n

/-! ## `BlockShape.nIdxs`: the block-level function -/

/-- The model of `block_shape_n_idxs`. -/
def nIdxsW (n : Nat) (m : Mem) (p : Word) : Option (List Word × Mem) :=
  match allocW m (rdW (m.arr64 IW) (p + 1)) with
  | none => none
  | some (q, m1) =>
    match nIdxsCopyW (n - 1) m1 q (rdW (m.arr64 IW) p) (rdW (m.arr64 IW) (p + 1)) with
    | none => none
    | some m2 => some ([q, rdW (m.arr64 IW) (p + 1)], m2)

theorem blockShapeNIdxs_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "n_idxs_copy" = some nIdxsCopy)
    (hp : p.lookup "block_shape_n_idxs" = some blockShapeNIdxs) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_shape_n_idxs" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ nIdxsW n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeNIdxs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hmod : ∀ a m1 m2, allocW s₀.mem (rdW (s₀.mem.arr64 IW) (q + 1)) = some (a, m1) →
        nIdxsCopyW n m1 a (rdW (s₀.mem.arr64 IW) q) (rdW (s₀.mem.arr64 IW) (q + 1)) = some m2 →
        nIdxsW (n + 1) s₀.mem q = some ([a, rdW (s₀.mem.arr64 IW) (q + 1)], m2) := by
      intro a m1 m2 h1 h2
      simp [nIdxsW, h1, h2]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n, nIdxsCopy_spec p hc n] <;>
      finish (gen := 20)

theorem decNL_of_get (m : Mem) : ∀ (xs : List Nat) (o : Nat),
    (∀ j (hj : j < xs.length), iwN m (o + j) = some xs[j]) → decNL m o xs.length = some xs
  | [], o, _ => by simp [decNL]
  | x :: xs, o, h => by
    have h0 : iwN m o = some x := h 0 (by simp)
    have ih := decNL_of_get m xs (o + 1) (fun j hj => by
      have := h (j + 1) (by simpa using hj)
      have e : o + (j + 1) = o + 1 + j := by omega
      simpa [e] using this)
    show (List.range (xs.length + 1)).mapM (fun j => iwN m (o + j)) = _
    rw [mapM_shift_succ (fun i => iwN m i) o xs.length]
    have ih' : (List.range xs.length).mapM (fun j => iwN m (o + 1 + j)) = some xs := ih
    simp [h0, ih']

theorem nIdxsW_dec {n : Nat} {m m' : Mem} {p : Word} {r : List Word} {bs : BlockShape}
    (h : nIdxsW n m p = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hq : decBS m p.toNat = some bs)
    (hb : p.toNat + 9 < 2 ^ 64)
    (hsrc : ∀ o l, iwN m p.toNat = some o → iwN m (p.toNat + 1) = some l → o + l ≤ iwTop m)
    (hptr : ∀ o l j v, iwN m p.toNat = some o → iwN m (p.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v + 1 < iwTop m) :
    r = [rdW (m.arr64 CTL) 200, UInt64.ofNat bs.k] ∧
    decNL m' (rdW (m.arr64 CTL) 200).toNat bs.k = some bs.nIdxs ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
    (rdW (m.arr64 CTL) 200).toNat + bs.k = iwTop m' := by
  obtain ⟨o, l, ho, hl, hg⟩ := decAt_some (decBS_some hq).1
  have hlen := decPL_length m hg
  have hk : bs.k = l := by rw [BlockShape.k, hlen]
  obtain ⟨ho', hob⟩ := iwN_rdW ho (by omega)
  obtain ⟨hl', hlb⟩ := iwN_rdW hl (by omega)
  have e1 : UInt64.ofNat (p.toNat + 1) = p + 1 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  rw [ofNat_toNat_word] at ho'
  rw [e1] at hl'
  have hoo : (UInt64.ofNat o).toNat = o := by simp [hob]
  have hll : (UInt64.ofNat l).toNat = l := by simp [hlb]
  have hsrc' := hsrc o l ho hl
  simp only [nIdxsW, ho', hl'] at h
  rcases hal : allocW m (UInt64.ofNat l) with _ | ⟨q, m1⟩
  · simp [hal] at h
  obtain ⟨hq', hm1, hroom⟩ := allocW_facts hal hsz
  rw [hll] at hroom
  simp only [hal] at h
  rcases hcp : nIdxsCopyW (n - 1) m1 q (UInt64.ofNat o) (UInt64.ofNat l) with _ | m2
  · simp [hcp] at h
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq' hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hIW := allocMem_IW m (UInt64.ofNat l)
  have htop0 : iwTop m = q.toNat := by simp only [iwTop, hqq]
  have hptr' : ∀ j < (UInt64.ofNat l).toNat,
      (rdW ((allocMem m (UInt64.ofNat l)).arr64 IW) (UInt64.ofNat ((UInt64.ofNat o).toNat + j)) + 1).toNat < q.toNat := by
    intro j hj
    rw [hll] at hj
    obtain ⟨v, y, hv, -, -⟩ := decPL_get l o bs.members hg j hj
    have hvb := hptr o l j v ho hl hj hv
    obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
    rw [hIW, hoo]
    have e : UInt64.ofNat (o + j) = UInt64.ofNat o + UInt64.ofNat j := ofNat_add_word _ _
    rw [hv']
    have : (UInt64.ofNat v + 1).toNat = v + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    rw [this]; omega
  obtain ⟨hA, hS, hW, hG⟩ := nIdxsCopyW_get (n - 1) _ _ _ _ _ hcp
    (by rw [hoo, hll]; simp only [iwTop, hqq] at hsrc'; omega)
    (by rw [hIW, hll]; exact hroom) (by rw [hIW]; exact hsz) hptr'
  rw [hIW] at hS hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m _).trans (copy_frame hA (by rw [hS, hIW]) hW)
  have htop : rdW (m2.arr64 CTL) 200 = q + UInt64.ofNat l := by
    rw [hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + UInt64.ofNat l).toNat = q.toNat + l := by
    rw [UInt64.toNat_add]; simp [hll]; omega
  refine ⟨by rw [hk], ?_, ?_, hfr, ?_⟩
  · rw [hk]
    have hxs : bs.nIdxs.length = l := by simp [BlockShape.nIdxs, hlen]
    have := decNL_of_get m2 bs.nIdxs q.toNat (fun j hj => by
      have hj' : j < l := by omega
      obtain ⟨v, y, hv, hy, hget⟩ := decPL_get l o bs.members hg j hj'
      obtain ⟨-, hnI, -⟩ := decMS_some hy
      have hGj := hG (q.toNat + j)
      rw [ite_eq_left (by rw [hll]; omega)] at hGj
      have e2 : q.toNat + j - q.toNat = j := by omega
      rw [e2, hoo] at hGj
      obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
      have hvb := hptr o l j v ho hl hj' hv
      rw [hv'] at hGj
      obtain ⟨hn', hnb⟩ := iwN_rdW hnI (by omega)
      have e4 : UInt64.ofNat v + 1 = UInt64.ofNat (v + 1) := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
      rw [e4, hn'] at hGj
      simp only [iwN, nat?, iwA]
      rw [hGj]
      have hy' : bs.members[j]'(by omega) = y := by
        simpa [List.getElem?_eq_getElem (show j < bs.members.length by omega)] using hget
      simp [BlockShape.nIdxs, List.getElem_map, hy', Nat.mod_eq_of_lt hnb])
    rw [hxs] at this
    exact this
  · refine iwGrow_of_frame hfr (N := UInt64.ofNat l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq, hll]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, ite_eq_right (by omega)]
  · simp only [iwTop, htop, hsum, hk]

/-- **`block_shape_n_idxs` is `BlockShape.nIdxs`**: the new `IW` slice holds the members' index counts. -/
@[refines ConRon.Arena.BlockShape.nIdxs]
theorem blockShapeNIdxs_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "n_idxs_copy" = some nIdxsCopy)
    (hp : p.lookup "block_shape_n_idxs" = some blockShapeNIdxs) (n : Nat) (s₀ : St) (q : Word)
    (bs : BlockShape) (hq : decBS s₀.mem q.toNat = some bs) (hb : q.toNat + 9 < 2 ^ 64)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hcl : 200 < (s₀.mem.arr64 CTL).size)
    (hsrc : ∀ o l, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l →
      o + l ≤ iwTop s₀.mem)
    (hptr : ∀ o l j v, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l → j < l →
      iwN s₀.mem (o + j) = some v → v + 1 < iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_n_idxs" [q]
    ⦃fun r s' => r = [rdW (s₀.mem.arr64 CTL) 200, UInt64.ofNat bs.k] ∧
      decNL s'.mem (rdW (s₀.mem.arr64 CTL) 200).toNat bs.k = some bs.nIdxs ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem ∧
      (rdW (s₀.mem.arr64 CTL) 200).toNat + bs.k = iwTop s'.mem; ⊤⦄ := by
  refine triple_post (blockShapeNIdxs_spec p ha hc hp n s₀ q) ?_
  intro r s' ⟨_, h⟩
  exact nIdxsW_dec h hsz hcl hq hb hsrc hptr

end L.Ind

end
