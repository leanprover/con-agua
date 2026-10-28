import ConAgua.Arena.IndPos2
import ConAgua.Arena.IndPosSpec.GgW2
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.Verdict
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Error models of `nest_pos`, `nest_pos_bind`, `nest_pos_app`, `nest_cont`, their leaves
(lane `verdicts-b`, helper `ia2`, fork `kn1`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model npE_spec (p : Prog) (hf : p.lookup "nest_pos" = some nestPosL)
  fns [hf ↦ npE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model npbE_spec (p : Prog) (hf : p.lookup "nest_pos_bind" = some nestPosBindL)
  fns [hf ↦ npbE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model npaE_spec (p : Prog) (hf : p.lookup "nest_pos_app" = some nestPosAppL)
  fns [hf ↦ npaE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model ncE_spec (p : Prog) (hf : p.lookup "nest_cont" = some nestContL)
  fns [hf ↦ ncE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

/-- `nest_occ_any`'s model with its one result as a word (the generator reads `some (r, m)`). -/
def noaW1 (k : Nat) (m : Mem) (no nl lo hi off ln : Word) : Option (Word × Mem) :=
  (noaW k m no nl lo hi off ln).map fun x => (x.1.headD 0, x.2)

theorem noaW1_some {k : Nat} {m m' : Mem} {no nl lo hi off ln b : Word}
    (h : noaW1 k m no nl lo hi off ln = some (b, m')) :
    ∃ r, noaW k m no nl lo hi off ln = some (r, m') ∧ r.headD 0 = b := by
  simp only [noaW1, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨r, m₁⟩, h, rfl, rfl⟩ := h
  exact ⟨r, h, rfl⟩

theorem nestOccAny_spec1 (p : Prog) (hl : NoLook p) (hp : p.lookup "nest_occ_any" = some nestOccAnyL)
    (k : Nat) (s₀ : St) (no nl lo hi off ln : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_occ_any" [no, nl, lo, hi, off, ln]
    ⦃fun r s' => LocEq s' s₀ ∧ noaW1 k s₀.mem no nl lo hi off ln = some (r.headD 0, s'.mem); ⊤⦄ :=
  triple_post (nestOccAny_spec p hl hp k s₀ no nl lo hi off ln) fun r s' ⟨hl', h⟩ =>
    ⟨hl', by simp [noaW1, h]⟩

l_model pfvE_spec (p : Prog) (hL : PfLook p)
  fns [hL.hp ↦ pfvE]
  specs [nestHoleAt_spec' p hL n, nestOccAny_spec1 p hL.no hL.hoa n, nestArity_spec' p hL.na n,
    nestPosHoleKind_spec p hL.hh hL.hk n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model nccE_spec (p : Prog) (hf : p.lookup "nest_cont_checks" = some nestContChecksL)
  fns [hf ↦ nccE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model nitE_spec (p : Prog) (hf : p.lookup "nest_inst_type" = some nestInstTypeL)
  fns [hf ↦ nitE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model ntyE_spec (p : Prog) (hf : p.lookup "nest_inst_type_ty" = some nestInstTypeTyL)
  fns [hf ↦ ntyE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

end L.Ind
