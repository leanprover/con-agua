module

public import ConAgua.Arena.RecGenSpec.KcW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all Init.Data.List.Control
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndSumSpec.StructProjArgP
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

/-!
# ClassKeyCanon: `ConRon.Arena.classKeyCanon`, `ConRon.Arena.targetCanonParams`

The refinement theorems `targetCanonParams_refinesP`, `classKeyCanon_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The relational side -/

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem ckc2W_mfr : ∀ (n : Nat) (m m' : Mem) (nP o l : Word) (r : List Word),
    ckc2W n m nP o l = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [ckc2W] at h
  | n + 1, m, m', nP, o, l, r, h => by
    by_cases hl : l = 0
    · rw [ckc2W_nil n m nP o l hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [ckc2W_cons n m nP o l hl] at h
    obtain ⟨⟨rb, m1⟩, h1, h⟩ := of_K h (by simp only [ckc2K1])
    refine (bvbW_mfr h1).trans ?_
    by_cases hb : rb ≠ 0
    · rw [ckc2K1_open (h := hb)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [ckc2K1_closed (h := hb)] at h
    obtain ⟨⟨rf, m2⟩, h2, h⟩ := of_K h (by simp only [ckc2K2])
    refine (MFr.ofFvbF h2).trans ?_
    by_cases hf : nP < rf.headD 0
    · rw [ckc2K2_open (h := hf)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [ckc2K2_closed (h := hf)] at h
    obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl
    rw [ckcK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact ckc2W_mfr n _ _ _ _ _ _ h3

theorem ckc2W_ok (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (nP o l : Word) (xs : List EIdx) (r : List Word),
    ckc2W n m nP o l = some (r, m') → StageR vis fe m a → decHL m o.toNat l.toNat = some xs →
    o.toNat + l.toNat < 2 ^ 64 → o.toNat + l.toNat ≤ iwTop m →
    ∃ b a', (xs.allM (keyClosedTest nP.toNat)).run a = .ok (b, a') ∧
      KeepPost vis fe decW0B m m' a' r b := by
  sorry

end rel

/-! ## Census -/

section census
variable {p : Prog} (L : KofProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
include L

/-- **`target_canon_params` refines `targetCanonParams`** (`replace_fvars` through its `mk_app_n`
stub): the parameters a slice below the top, the walk memos well formed before and after. -/
@[refines ConRon.Arena.targetCanonParams]
theorem targetCanonParams_refinesP (k : Nat) (s₀ : St) (a₀ : AState) (pfo pfl e : Word) (pfvs : List EIdx)
    (hS : StageR vis fe s₀.mem a₀) (hpf : decHL s₀.mem pfo.toNat pfl.toNat = some pfvs)
    (hpb : pfo.toNat + pfl.toNat ≤ iwTop s₀.mem) (he : H e) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "target_canon_params" [pfo, pfl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀ ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀ ∧ H (r.headD 0) ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ PosMR s'.mem; ⊤⦄ := by
  sorry

/-- **`class_key_canon` refines `classKeyCanon`** (through `replace_fvars`' stub): the key decoded
below the tops, the canonical parameters a slice below the top; the canonical key a fresh record
decoded below the tops, its parameter slice below the top. -/
@[refines ConRon.Arena.classKeyCanon]
theorem classKeyCanon_refines (k : Nat) (s₀ : St) (a₀ : AState) (po pl key : Word) (pfvs : List EIdx)
    (ck : ClassKey) (hS : StageR vis fe s₀.mem a₀) (hpf : decHL s₀.mem po.toNat pl.toNat = some pfvs)
    (hpb : po.toNat + pl.toNat ≤ iwTop s₀.mem) (hk : DecB (fun m => decCK m key.toNat) s₀.mem ck)
    (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "class_key_canon" [po, pl, key]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classKeyCanon pfvs ck) a₀ ∧
      DecB (fun m => decCK m (r.headD 0).toNat) s'.mem (AM.res (ConRon.Arena.classKeyCanon pfvs ck) a₀) ∧
      (r.headD 0).toNat + 4 ≤ iwTop s'.mem ∧
      (rdW (s'.mem.arr64 IW) (r.headD 0 + 2)).toNat + (rdW (s'.mem.arr64 IW) (r.headD 0 + 3)).toNat ≤
        iwTop s'.mem ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.classKeyCanon pfvs ck) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ PosMR s'.mem; ⊤⦄ := by
  sorry

end census

end L.Ind

end
