module

import ConAgua.Arena.IndPosSpec.GgW
public import ConAgua.Arena.IndPosSpec.GrpAt
public import ConAgua.Arena.IndPosSpec.NkcW
import ConAgua.Arena.Env
import ConAgua.Arena.IndPosSpec.RootHoles

@[expose] public section

/-!
# NestAcceptGroup: `ConRon.Arena.nestAcceptGroup`

The refinement theorems `nestAcceptGroup_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem KsB.nil (m : Mem) (o : Nat) : KsB m o 0 [] := by simp [KsB, DecB, decPL]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Pointer slices decoded below the tops, element by element -/

section pslice
variable {α : Type} {f : Mem → Nat → Option α}

/-- **Two pointer slices concatenated** (`sl_append`). -/
theorem pos2_decB_append (hf : ∀ q, OMono (fun m => f m q)) {m m' : Mem} {o1 l1 o2 l2 q : Nat}
    {xs ys : List α} (h1 : DecB (fun m => decPL m (f m) o1 l1) m xs)
    (h2 : DecB (fun m => decPL m (f m) o2 l2) m ys) (hg : IWGrow m m') (hq : q + l1 + l2 ≤ iwTop m')
    (hw1 : ∀ i < l1, (m'.arr64 IW)[q + i]? = (m.arr64 IW)[o1 + i]?)
    (hw2 : ∀ i < l2, (m'.arr64 IW)[q + l1 + i]? = (m.arr64 IW)[o2 + i]?) :
    DecB (fun m => decPL m (f m) q (l1 + l2)) m' (xs ++ ys) := by
  sorry

end pslice

end L.Ind

namespace L.Ind

open L.Arena

/-- **`nest_accept_group` is `nestAcceptGroup`** over the decoded group and key slice. -/
theorem nagW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (us dO dL : Word) (ds : List EIdx)
    (hus : H us) : ∀ (n : Nat) (m m' : Mem) (a : AState) (gO gL kO kL : Word) (grp : List (NIdx × EIdx))
    (keys : Array NestKey) (r : List Word),
    nagW n m us dO dL gO gL kO kL = some (r, m') → StageR vis fe m a →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp →
    KsB m kO.toNat kL.toNat keys.toList → kO.toNat + kL.toNat ≤ iwTop m →
    StageR vis fe m' a ∧ IWGrow m m' ∧
      KsB m' (r.headD 0).toNat (r.tail.headD 0).toNat (nestAcceptGroup (decI us) ds grp keys).toList ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  sorry

end L.Ind

namespace L.Ind

open L.Arena

/-- **`nest_accept_group` refines `nestAcceptGroup`** (a pure twin: the key slice it returns
decodes as the accepted keys). -/
@[refines ConRon.Arena.nestAcceptGroup]
theorem nestAcceptGroup_refines (p : Prog) (L : NagLook p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (us dO dL gO gL kO kL : Word)
    (ds : List EIdx) (grp : List (NIdx × EIdx)) (keys : Array NestKey) (hS : StageR vis fe s₀.mem a₀)
    (hus : H us) (hds : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) s₀.mem ds)
    (hgl : gL.toNat = grp.length) (hgb : gO.toNat + grp.length ≤ iwTop s₀.mem)
    (hgrp : GrpAt s₀.mem gO.toNat grp) (hks : KsB s₀.mem kO.toNat kL.toNat keys.toList)
    (hkb : kO.toNat + kL.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_accept_group" [us, dO, dL, gO, gL, kO, kL]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      KsB s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat (nestAcceptGroup (decI us) ds grp keys).toList ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  refine triple_post (nestAcceptGroup_spec p L n s₀ us dO dL gO gL kO kL) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨h1, h2, h3, h4⟩ := nagW_ok dn vis fe us dO dL ds hus n _ _ a₀ gO gL kO kL grp keys _ hm hS hds hgl hgb
    hgrp hks hkb
  exact ⟨hlc, h1, h2, by simpa using h3, by simpa using h4⟩

end L.Ind

end
