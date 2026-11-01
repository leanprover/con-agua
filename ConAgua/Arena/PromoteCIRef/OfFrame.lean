module

import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.DeclPins
public import ConAgua.Arena.DeclBase

@[expose] public section

/-!
# OfFrame

`LoopR.of_frame`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Front (DECL DLP DeclsF)

/-- **The loop's relation across a promotion-like step**: the writes land in the arrays below 50,
`132‥136` and `146‥149`, the table arrays (`129‥131` in both tiers, `143`), and in the `CTL` words
below 64, `129`, `133`, `140‥147`; the arena side is given, the environment is given; the rest is a
frame. -/
theorem LoopR.of_frame {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe fe' : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    {A : List TieredArray} {C : List Word} {pm' : PMemo}
    (hR : LoopR pins dn m a vis fe pend ds) (hD : ArenaD m' a') (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, ((b.arr < 50 ∨ (54 < b.arr ∧ b.arr < 64)) ∨
      ((132 ≤ b.arr ∧ b.arr ≤ 136) ∨ (140 ≤ b.arr ∧ b.arr ≤ 142)) ∨ (146 ≤ b.arr ∧ b.arr ≤ 149)) ∨
      ((129 ≤ b.arr ∧ b.arr ≤ 131) ∨ b.arr = 143))
    (hC : ∀ x ∈ C, (x.toNat < 64 ∨ x.toNat = 129 ∨ (140 ≤ x.toNat ∧ x.toNat ≤ 147)) ∨ x.toNat = 133)
    (hcp : cp a' = cp a) (hg : ErecGrow m m') (hts : erecTop m' ≤ (m'.arr64 EREC).size)
    (hP : PMemoR m' pm') (hE : EnvR dn m' vis fe') (hmode : ModeOK m') :
    LoopR pins dn m' a' vis fe' pend ds := by
  obtain ⟨hiw1, hiw2, hiw3, hiw4, hiw5⟩ := hR.iw
  have hcA : a'.caches = a.caches := congrArg Prod.fst hcp
  have hpA : a'.pins = a.pins := congrArg Prod.snd hcp
  have hIW : m'.arr64 L.Ind.IW = m.arr64 L.Ind.IW :=
    hf.arr _ (fun h => by have := hA _ h; revert this; decide) (by decide)
  refine ⟨⟨hD, ?_, ?_, hE, hmode⟩, ?_, ?_, ?_, ⟨pm', hP⟩, ?_⟩
  · rw [hcA]
    exact hR.check.core.frame (fun b hb => by have := hA b hb; omega)
      (fun x hx => by have := hC x hx; omega) hf
  · rw [hpA]
    exact hR.check.pins.frame (fun b hb => by have := hA b hb; omega) hf
  · exact hR.pend.ext (hf.arr _ (fun h => by have := hA _ h; revert this; decide) (by decide))
      (hf.ctl 130 (fun h => by have := hC _ h; simp at this)) hg.ext
  · rw [hf.arr DECL (fun h => by have := hA _ h; revert this; decide) (by decide),
      hf.arr DLP (fun h => by have := hA _ h; revert this; decide) (by decide)]
    exact hR.decls
  · refine ⟨?_, hts, ?_, by rw [hf.size]; exact hiw4, by rw [hf.size]; exact hiw5⟩
    · simp only [L.Ind.iwTop, hIW]
      rw [hf.ctl 200 (fun h => by have := hC _ h; simp at this)]; exact hiw1
    · rw [hIW]; exact hiw3
  · exact PinSetsR.grow hR.pinsets ⟨hg.top, hg.get⟩
      (hf.ctl 150 (fun h => by have := hC _ h; simp at this))
      (hf.ctl 151 (fun h => by have := hC _ h; simp at this))

end L.Arena
