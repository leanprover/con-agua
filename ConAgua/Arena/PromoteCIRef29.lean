import ConAgua.Arena.PromoteCIRef28
import ConAgua.Arena.DeclBase
import ConAgua.Arena.DeclStepSpec

/-!
# `promote_new` refines `promoteNew` under the loop's relation: the frame
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

open L.Front (DECL DLP DeclsF)

/-- **The loop's relation across a promotion-like step**: the writes land in the arrays below 50,
`132‥136` and `146‥149`, the table arrays (`129‥131`, `143`, `385‥387`), and in the `CTL` words
below 64, `129`, `133`, `140‥147`; the arena side is given, the environment is given; the rest is a
frame. -/
theorem LoopR.of_frame {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe fe' : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    {A : List ArrId} {C : List Word} {pm' : PMemo}
    (hR : LoopR pins dn m a vis fe pend ds) (hD : ArenaD m' a') (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, ((b < 50 ∨ (54 < b ∧ b < 64)) ∨ ((132 ≤ b ∧ b ≤ 136) ∨ (140 ≤ b ∧ b ≤ 142)) ∨
      (146 ≤ b ∧ b ≤ 149) ∨
      (256 ≤ b ∧ b < 306) ∨ (310 < b ∧ b < 320)) ∨
      ((129 ≤ b ∧ b ≤ 131) ∨ b = 143 ∨ (385 ≤ b ∧ b ≤ 387)))
    (hC : ∀ x ∈ C, (x.toNat < 64 ∨ x.toNat = 129 ∨ (140 ≤ x.toNat ∧ x.toNat ≤ 147)) ∨ x.toNat = 133)
    (hcp : cp a' = cp a) (hg : ErecGrow m m') (hts : erecTop m' ≤ (m'.arr64 EREC).size)
    (hP : PMemoR m' pm') (hE : EnvR dn m' vis fe') (hmode : ModeOK m') :
    LoopR pins dn m' a' vis fe' pend ds := by
  obtain ⟨hiw1, hiw2, hiw3, hiw4, hiw5⟩ := hR.iw
  have hcA : a'.caches = a.caches := congrArg Prod.fst hcp
  have hpA : a'.pins = a.pins := congrArg Prod.snd hcp
  have hIW : m'.arr64 L.Ind.IW = m.arr64 L.Ind.IW :=
    hf.1 _ (fun h => by have := hA _ h; revert this; decide) (by decide)
  refine ⟨⟨hD, ?_, ?_, hE, hmode⟩, ?_, ?_, ?_, ⟨pm', hP⟩, ?_⟩
  · rw [hcA]
    exact hR.check.core.frame (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
      (fun x hx => by have := hC x hx; omega) hf
  · rw [hpA]
    exact hR.check.pins.frame (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega) hf
  · exact hR.pend.ext (hf.1 _ (fun h => by have := hA _ h; revert this; decide) (by decide))
      (hf.2.1 130 (fun h => by have := hC _ h; simp at this)) hg.ext
  · rw [hf.1 DECL (fun h => by have := hA _ h; revert this; decide) (by decide),
      hf.1 DLP (fun h => by have := hA _ h; revert this; decide) (by decide)]
    exact hR.decls
  · refine ⟨?_, hts, ?_, by rw [hf.2.2.1]; exact hiw4, by rw [hf.2.2.1]; exact hiw5⟩
    · simp only [L.Ind.iwTop, hIW]
      rw [hf.2.1 200 (fun h => by have := hC _ h; simp at this)]; exact hiw1
    · rw [hIW]; exact hiw3
  · exact PinSetsR.grow hR.pinsets ⟨hg.1, hg.2.1⟩
      (hf.2.1 150 (fun h => by have := hC _ h; simp at this))
      (hf.2.1 151 (fun h => by have := hC _ h; simp at this))

end L.Arena
