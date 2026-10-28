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

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model npE_spec (p : Prog) (hf : p.lookup "nest_pos" = some nestPosL)
  fns [hf ↦ npE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified

l_model npbE_spec (p : Prog) (hf : p.lookup "nest_pos_bind" = some nestPosBindL)
  fns [hf ↦ npbE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified

l_model npaE_spec (p : Prog) (hf : p.lookup "nest_pos_app" = some nestPosAppL)
  fns [hf ↦ npaE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified

l_model ncE_spec (p : Prog) (hf : p.lookup "nest_cont" = some nestContL)
  fns [hf ↦ ncE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified

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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `nest_cont_params_closed`'s model with its one result as a word. -/
def cpW1 (k : Nat) (m : Mem) (hpw dO dL : Word) : Option (Word × Mem) :=
  (cpW k m hpw dO dL).map fun x => (x.1.headD 0, x.2)

theorem cpW1_some {k : Nat} {m m' : Mem} {hpw dO dL b : Word} (h : cpW1 k m hpw dO dL = some (b, m')) :
    ∃ r, cpW k m hpw dO dL = some (r, m') ∧ r.headD 0 = b := by
  simp only [cpW1, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨r, m₁⟩, h, rfl, rfl⟩ := h
  exact ⟨r, h, rfl⟩

theorem nestContParamsClosed_spec1 (p : Prog) (hb : BvbProg p) (hf : HfF p)
    (hp : p.lookup "nest_cont_params_closed" = some nestContParamsClosedL) (n : Nat) (s₀ : St)
    (hpw dO dL : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_params_closed" [hpw, dO, dL]
    ⦃fun r s' => LocEq s' s₀ ∧ cpW1 n s₀.mem hpw dO dL = some (r.headD 0, s'.mem); ⊤⦄ :=
  triple_post (nestContParamsClosed_spec p hb hf hp n s₀ hpw dO dL) fun r s' ⟨hl', h⟩ =>
    ⟨hl', by simp [cpW1, h]⟩

l_model nccE_spec (p : Prog) (hL : NbLook p)
  fns [hL.hcc ↦ nccE]
  specs [nestOccAny_spec1 p hL.nit.no hL.nit.hoa n, pos2Pin_spec p hL.hpa n,
    nestContParamsClosed_spec1 p hL.usl.hbp hL.dc.hf hL.hpc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model nitE_spec (p : Prog) (hf : p.lookup "nest_inst_type" = some nestInstTypeL)
  fns [hf ↦ nitE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

noncomputable section

l_model ntyE_spec (p : Prog) (hL : NtyLook p)
  fns [hL.hp ↦ ntyE]
  specs [envFind_specW p hL.hx hL.hg hL.hf n, callW_spec p n "view_ls_len", stripPis_specF p hL.hst n,
    cvLps_spec p hL.ha hL.hc hL.he hL.hcv n, callW_spec p n "inst_lp_fast",
    instPisWith_spec p hL.hv hL.hip hL.hi1 n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end

end L.Ind

end
