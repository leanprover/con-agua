module

public import ConLeche.Model.Inductives.FixKit
public import ConLeche.Semantics.Tower.BlockTower
public section

/-!
# The block leaf's P currency

A member's former leaf (`blockTyG`: the block operator's tower, the
index-set tuple and the carrier tuple under the parameter frame) is
closed (`blockTyAV_below`) and graded at the hereditary premise.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## Closedness -/

section Below

omit [SetTheory V] in
/-- The non-dependent tower is closed at its components' bound plus
its own depth. -/
theorem ndTowerAV_below {r b : Nat} {G : Nat → Term} :
    ∀ (n s d : Nat), (∀ i, i < s + n → Term.bvarsBelow b (G i)) →
      Term.bvarsBelow (b + d) (ndTowerAV r G s d n)
  | 0, _, _, _ => by simp [ndTowerAV, Term.bvarsBelow]
  | n + 1, s, d, hG => by
    show Term.bvarsBelow (b + d) ((.app (.app (.const .psigma [r, r]) ((G s).liftN d 0))
        (.lam ((G s).liftN d 0) (ndTowerAV r G (s + 1) (d + 1) n))))
    have hC : Term.bvarsBelow (b + d) ((G s).liftN d 0) := by
      exact VExprAux.bvarsBelow_liftN d (G s) b 0 (hG s (by omega))
    have htail : Term.bvarsBelow (b + d + 1) (ndTowerAV r G (s + 1) (d + 1) n) := by
      have := ndTowerAV_below (r := r) (G := G) (b := b) n (s + 1) (d + 1)
        (fun i hi => hG i (by omega))
      rwa [show b + (d + 1) = b + d + 1 from by omega] at this
    simp only [Term.bvarsBelow]
    exact ⟨⟨trivial, hC⟩, hC, htail⟩

omit [SetTheory V] in
/-- The non-dependent tuple VALUE is closed at its components' bound. -/
theorem ndMkTowerAV_below {r b : Nat} {Gty G : Nat → Term} :
    ∀ (n s : Nat), (∀ i, i < s + n → Term.bvarsBelow b (Gty i)) →
      (∀ i, i < s + n → Term.bvarsBelow b (G i)) →
      Term.bvarsBelow b (ndMkTowerAV r Gty G s n)
  | 0, _, _, _ => by simp [ndMkTowerAV, Term.bvarsBelow]
  | n + 1, s, hGty, hG => by
    show Term.bvarsBelow b ((Term.mkAppN (.const .psigmaMk [r, r])
      [Gty s, .lam (Gty s) (ndTowerAV r Gty (s + 1) 1 n),
       G s, ndMkTowerAV r Gty G (s + 1) n]))
    refine VExprAux.bvarsBelow_mkAppN (by simp [Term.bvarsBelow]) ?_
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | rfl | rfl | rfl | h
    · exact hGty s (by omega)
    · simp only [Term.bvarsBelow]
      refine ⟨hGty s (by omega), ?_⟩
      have := ndTowerAV_below (r := r) (G := Gty) (b := b) n (s + 1) 1
        (fun i hi => hGty i (by omega))
      rwa [show b + 1 = b + 1 from rfl] at this
    · exact hG s (by omega)
    · exact ndMkTowerAV_below (r := r) (Gty := Gty) (G := G) n (s + 1)
        (fun i hi => hGty i (by omega)) (fun i hi => hG i (by omega))
    · exact nomatch h

/-! ### The chains and the leaf -/

/-! ### The operator tower -/

section LeafBelow

variable {k w nP nIdx : Nat} {uf : Nat → Nat} {Idss : Nat → List Term}
  {Chs : Nat → List (List Term)}

omit [SetTheory V] in
theorem famTyAV_below {u w : Nat} {Ids : List Term} (h : DomsBelow nP Ids) :
    Term.bvarsBelow nP (famTyAV u w Ids) := by
  unfold famTyAV
  simp only [Term.bvarsBelow]
  exact ⟨towerBodyAV_below h, trivial⟩

omit [SetTheory V] in
/-- Member `m`'s arm of the operator, below the operator's λ. -/
theorem blockArmAV_below {m : Nat} (hIds : ∀ c, DomsBelow nP (Idss c))
    (hchains : ∀ chain ∈ Chs m, DomsBelow (nP + 2) chain) :
    Term.bvarsBelow (nP + 1)
      (blockArmG w uf Idss Chs m) := by
  unfold blockArmG
  simp only [Term.bvarsBelow]
  refine ⟨?_, ?_⟩
  · exact VExprAux.bvarsBelow_liftN 1 (idxTyAV (uf m) (Idss m)) nP 0
      (towerBodyAV_below (hIds m))
  · exact sumBodyAV_below hchains

omit [SetTheory V] in
/-- The block's operator, below the parameter frame. -/
theorem blockFunAV_below (hIds : ∀ c, DomsBelow nP (Idss c))
    (hchains : ∀ m, m < k → ∀ chain ∈ Chs m, DomsBelow (nP + 2) chain) :
    Term.bvarsBelow nP (blockFunG k w uf Idss Chs) := by
  unfold blockFunG
  simp only [Term.bvarsBelow]
  refine ⟨?_, ?_⟩
  · unfold famsTyBAV
    have := ndTowerAV_below (r := blockR k w uf)
      (G := fun m => famTyAV (uf m) w (Idss m)) (b := nP) k 0 0
      (fun i _ => famTyAV_below (hIds i))
    rwa [Nat.add_zero] at this
  · exact ndMkTowerAV_below (r := blockR k w uf) (b := nP + 1) k 0
      (fun i _ => by
        exact VExprAux.bvarsBelow_liftN 1 (famTyAV (uf i) w (Idss i)) nP 0
          (famTyAV_below (hIds i)))
      (fun i hi => blockArmAV_below hIds (hchains i (by omega)))

omit [SetTheory V] in
/-- The index-set tuple, below the parameter frame. -/
theorem idxTupAV_below (hIds : ∀ c, DomsBelow nP (Idss c)) :
    Term.bvarsBelow nP (idxTupAV k w uf Idss) := by
  unfold idxTupAV
  exact ndMkTowerAV_below (r := blockS k w uf) (b := nP) k 0
    (fun _ _ => by trivial)
    (fun i _ => towerBodyAV_below (hIds i))

omit [SetTheory V] in
/-- The block's carrier tuple, below the parameter frame. -/
theorem blockBodyAV_below (hIds : ∀ c, DomsBelow nP (Idss c))
    (hchains : ∀ m, m < k → ∀ chain ∈ Chs m, DomsBelow (nP + 2) chain) :
    Term.bvarsBelow nP (blockBodyG k w uf Idss Chs) := by
  unfold blockBodyG
  refine VExprAux.bvarsBelow_mkAppN (by simp [Term.bvarsBelow]) ?_
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | h
  · exact idxTupAV_below hIds
  · exact blockFunAV_below hIds hchains
  · exact nomatch h

omit [SetTheory V] in
/-- **A member's former leaf is closed.** -/
theorem blockTyAV_below {m : Nat} {pps : List Term}
    (hp : DomsBelow 0 pps) (hlen : pps.length = nP + nIdx)
    (hIdsLen : (Idss m).length = nIdx)
    (hIds : ∀ c, DomsBelow nP (Idss c))
    (hchains : ∀ m, m < k → ∀ chain ∈ Chs m, DomsBelow (nP + 2) chain) :
    Term.bvarsBelow 0
      (blockTyG k w uf Idss Chs pps m) := by
  refine mkLamsAV_below hp ?_
  rw [hlen, Nat.zero_add, ← hIdsLen]
  simp only [Term.bvarsBelow]
  refine ⟨?_, ?_⟩
  · refine projNV_below ?_
    exact VExprAux.bvarsBelow_liftN (Idss m).length
      (blockBodyG k w uf Idss Chs) nP 0
      (blockBodyAV_below hIds hchains)
  · exact mkTowerGo_below (w := uf m) (hIds m)

end LeafBelow

end Below

/-! ## The leaf's currency -/

section Currency

variable {k w nP : Nat} {uf : Nat → Nat} {Idss : Nat → List Term}
  {Chs : Nat → List (List Term)}

end Currency

end ConLeche.Model
