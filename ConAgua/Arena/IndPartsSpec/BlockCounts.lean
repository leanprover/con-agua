module

public import ConAgua.Arena.IndPartsSpec.RecTW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndParts

@[expose] public section

/-!
# BlockCounts: `ConRon.Arena.blockCounts`, `ConRon.Arena.piBinders`, `ConRon.Arena.recTargetOf`

The refinement theorems `piBinders_refines`, `recTargetOf_refines`, `blockCounts_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`pi_binders` is `piBinders`**: under `ArenaR`, a returning run is a successful twin run
(no state change) whose binders are the new `IW` slice and whose body is the third result. -/
@[refines ConRon.Arena.piBinders]
theorem piBinders_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hv : p.lookup "e_view" = some eView)
    (hs : p.lookup "sl_cons" = some slCons) (hp : p.lookup "pi_binders" = some piBinders)
    (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (fuel h : Word)
    (hh : h.toNat < 2 ^ 32) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hcl : 200 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_binders" [fuel, h]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [r.headD 0, r.getD 1 0, r.getD 2 0] ∧
      (∃ bs e, (ConRon.Arena.piBinders fuel.toNat (decE h)).run a₀ = .ok ((bs, e), a₀) ∧
        decHL s'.mem (r.headD 0).toNat (r.getD 1 0).toNat = some bs ∧
        (r.getD 2 0).toNat < 2 ^ 32 ∧ decE (r.getD 2 0) = e) ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem ∧
      (r.headD 0).toNat + (r.getD 1 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  refine triple_post (piBinders_spec p ha hc hv hs hp n s₀ fuel h) ?_
  intro r s' ⟨hl, hm, _⟩
  obtain ⟨bs, e, hrun, hsh, hdec, hb1, hb2, hg, hf, hle⟩ :=
    piBW_ok n s₀.mem s'.mem a₀ fuel h r hR hm hh hsz hcl
  exact ⟨hl, hsh, ⟨bs, e, hrun, hdec, hb1, hb2⟩, hg, hf, hle⟩

/-- **`rec_target_of` refines `recTargetOf`** (through the stub `get_app_fn`). -/
@[refines ConRon.Arena.recTargetOf]
theorem recTargetOf_refines (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hp : p.lookup "rec_target_of" = some recTargetOf)
    (hst : StripProg p) (had : AdF p) (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis no nl mI ty : Word) (names : List NIdx) (hS : StageR vis fe s₀.mem a₀)
    (hty : ty.toNat < 2 ^ 32) (hnames : decHL s₀.mem no.toNat nl.toNat = some names)
    (hb : no.toNat + nl.toNat < 2 ^ 64) (hbt : no.toNat + nl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec_target_of" [no, nl, mI, ty]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.recTargetOf names mI.toNat (decI ty)) a₀ ∧
      r = [UInt64.ofNat (AM.res (ConRon.Arena.recTargetOf names mI.toNat (decI ty)) a₀)] ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.recTargetOf names mI.toNat (decI ty)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (recTargetOf_spec p hv hf hp hst had n s₀ no nl mI ty) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨t, a', hrun, hr, hS', hg⟩ := recTW_ok n dn fe vis s₀.mem s'.mem a₀ no nl mI ty r names hm
    hS hty hnames hb hbt
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hr, by rw [hst]; exact hS', hg⟩

/-- **`block_counts` refines `blockCounts?`** (the recursor datum `r` as `(rOk, rMI, rRP)`). -/
@[refines ConRon.Arena.blockCounts?]
theorem blockCounts_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hv : p.lookup "e_view" = some eView)
    (hs : p.lookup "sl_cons" = some slCons) (hpb : p.lookup "pi_binders" = some piBinders)
    (hh : p.lookup "block_counts_head" = some blockCountsHead)
    (hpp : p.lookup "block_counts_pure" = some blockCountsPure)
    (hp : p.lookup "block_counts" = some blockCounts) (n : Nat) (s₀ : St) (a₀ : AState)
    (nPd k nC nR cvT rOk rMI rRP : Word) (cv : IConstantVal) (rr : Option (Nat × Nat))
    (hR : ArenaR s₀.mem a₀) (hcv : decCVp s₀.mem cvT.toNat = some cv) (hb : cvT.toNat + 3 < 2 ^ 64)
    (hrr : rr = if rOk = 0 then none else some (rMI.toNat, rRP.toNat))
    (h1 : nPd.toNat < 2 ^ 32) (h2 : k.toNat < 2 ^ 32) (h3 : nC.toNat < 2 ^ 32)
    (h4 : nR.toNat < 2 ^ 32) (h5 : rMI.toNat < 2 ^ 32) (h6 : rRP.toNat < 2 ^ 32)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hcl : 200 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_counts" [nPd, k, nC, nR, cvT, rOk, rMI, rRP]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.blockCounts? nPd.toNat k.toNat nC.toNat nR.toNat cv rr) a₀ ∧
      AM.st (ConRon.Arena.blockCounts? nPd.toNat k.toNat nC.toNat nR.toNat cv rr) a₀ = a₀ ∧
      r = encONN (AM.res (ConRon.Arena.blockCounts? nPd.toNat k.toNat nC.toNat nR.toNat cv rr) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (blockCounts_spec p ha hc hv hs hpb hh hpp hp n s₀ nPd k nC nR cvT rOk rMI rRP) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, hrun, hr, -, hg, hf⟩ := bcW_ok n s₀.mem s'.mem a₀ nPd k nC nR cvT rOk rMI rRP r cv rr
    hR hm hcv hb hrr h1 h2 h3 h4 h5 h6 hsz hcl
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hst, by rw [hres]; exact hr, hg, hf⟩

end L.Ind

end
