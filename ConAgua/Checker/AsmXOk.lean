module

public import ConAgua.Checker.AsmX
public import ConAgua.Checker.ProgI
import ConAgua.Checker.ProgIRef
import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.LoopProgTac
import ConAgua.Compiler.InlineCorrect
import all ConAgua.Arena.NatMul
import all ConAgua.Arena.NatDivSubmul
import all ConAgua.Arena.NatLeaf
import all ConAgua.Front.NatDec
import ConAgua.AsmEsc.ChainL

@[expose] public section

/-!
# The checker's hand-written bodies meet the compiler's contract

`checkerX_ok : AsmOkT checkerProgI checkerTab checkerX`: in every layout of `checkerTab`, each body
of `checkerX` starts with its function's label and meets `FnSimAt` (`mulRowAsm_sim`,
`subRowAsm_sim`, `divSubmulAsm_sim`, `natMadAsm_sim`, and `chain2Asm_sim`/`chain1Asm_sim` with the leaves' L sides
`addN_spec`, `subN_spec`, `add1_spec`, `sub1_spec`), at the function as `checkerProgI` declares it
(`checkerProgI_mulRow` …: the inliner leaves these functions, which call nothing, as they are).
-/

namespace L.Checker

open L L.Compiler L.Compiler.Inl L.AsmEsc L.Arena

theorem checkerTab_pool : checkerTab.dom64 (tier1 0) = true := by decide +kernel
theorem checkerTab_poolL : SmallOff (checkerTab.len64 (0 : ArrId)) := by decide +kernel
theorem checkerTab_poolB : SmallOff (checkerTab.base64 (0 : ArrId)) := by decide +kernel

theorem nameCode_mul_row : nameCode "mul_row" = mulRowCode := by decide

theorem nameCode_sub_row : nameCode "sub_row" = subRowCode := by decide

theorem checkerProgI_subRow : checkerProgI.lookup "sub_row" = some subRow := by
  rw [← checkerProgI_inline, inlineProg, inlineProg, lookup_inlRound,
    show checkerProg.lookup "sub_row" = some subRow by chk_lk]
  rfl

theorem nameCode_div_submul : nameCode "div_submul" = divSubmulCode := by decide

theorem checkerProgI_divSubmul : checkerProgI.lookup "div_submul" = some divSubmul := by
  rw [← checkerProgI_inline, inlineProg, inlineProg, lookup_inlRound,
    show checkerProg.lookup "div_submul" = some divSubmul by chk_lk]
  rfl

theorem checkerProgI_mulRow : checkerProgI.lookup "mul_row" = some mulRow := by
  rw [← checkerProgI_inline, inlineProg, inlineProg, lookup_inlRound,
    show checkerProg.lookup "mul_row" = some mulRow by chk_lk]
  rfl

theorem nameCode_add_n : nameCode "add_n" = addNCode := by decide

theorem checkerProgI_addN : checkerProgI.lookup "add_n" = some addN := by
  rw [← checkerProgI_inline, inlineProg, inlineProg, lookup_inlRound,
    show checkerProg.lookup "add_n" = some addN by chk_lk]
  rfl

theorem nameCode_add_1 : nameCode "add_1" = add1Code := by decide

theorem checkerProgI_add1 : checkerProgI.lookup "add_1" = some add1 := by
  rw [← checkerProgI_inline, inlineProg, inlineProg, lookup_inlRound,
    show checkerProg.lookup "add_1" = some add1 by chk_lk]
  rfl

theorem nameCode_sub_n : nameCode "sub_n" = subNCode := by decide

theorem checkerProgI_subN : checkerProgI.lookup "sub_n" = some subN := by
  rw [← checkerProgI_inline, inlineProg, inlineProg, lookup_inlRound,
    show checkerProg.lookup "sub_n" = some subN by chk_lk]
  rfl

theorem nameCode_sub_1 : nameCode "sub_1" = sub1Code := by decide

theorem checkerProgI_sub1 : checkerProgI.lookup "sub_1" = some sub1 := by
  rw [← checkerProgI_inline, inlineProg, inlineProg, lookup_inlRound,
    show checkerProg.lookup "sub_1" = some sub1 by chk_lk]
  rfl

theorem nameCode_nat_mad : nameCode "nat_mad" = natMadCode := by decide

theorem checkerProgI_natMad : checkerProgI.lookup "nat_mad" = some L.Front.natMad := by
  rw [← checkerProgI_inline, inlineProg, inlineProg, lookup_inlRound,
    show checkerProg.lookup "nat_mad" = some L.Front.natMad by chk_lk]
  rfl

theorem checkerX_ok : AsmOkT checkerProgI checkerTab checkerX := by
  intro _ G hG hT f c hl
  simp only [checkerX, List.lookup] at hl
  split at hl
  · rename_i hk
    cases hl
    have hf : f = "mul_row" := nameCode_inj ((beq_iff_eq.mp hk).trans nameCode_mul_row.symm)
    subst hf
    refine ⟨rfl, fun sk n fd kf hlk hcode => ?_⟩
    rw [checkerProgI_mulRow] at hlk
    cases hlk
    rw [← hT] at hcode
    exact mulRowAsm_sim checkerProgI G hG checkerProgI_mulRow (by rw [hT]; exact checkerTab_pool)
      (by rw [hT]; exact checkerTab_poolL) (by rw [hT]; exact checkerTab_poolB) kf hcode sk n
  split at hl
  · rename_i hk
    cases hl
    have hf : f = "sub_row" := nameCode_inj ((beq_iff_eq.mp hk).trans nameCode_sub_row.symm)
    subst hf
    refine ⟨rfl, fun sk n fd kf hlk hcode => ?_⟩
    rw [checkerProgI_subRow] at hlk
    cases hlk
    rw [← hT] at hcode
    exact subRowAsm_sim checkerProgI G hG checkerProgI_subRow (by rw [hT]; exact checkerTab_pool)
      (by rw [hT]; exact checkerTab_poolL) (by rw [hT]; exact checkerTab_poolB) kf hcode sk n
  split at hl
  · rename_i hk
    cases hl
    have hf : f = "div_submul" := nameCode_inj ((beq_iff_eq.mp hk).trans nameCode_div_submul.symm)
    subst hf
    refine ⟨rfl, fun sk n fd kf hlk hcode => ?_⟩
    rw [checkerProgI_divSubmul] at hlk
    cases hlk
    rw [← hT] at hcode
    exact divSubmulAsm_sim checkerProgI G hG checkerProgI_divSubmul (by rw [hT]; exact checkerTab_pool)
      (by rw [hT]; exact checkerTab_poolL) (by rw [hT]; exact checkerTab_poolB) kf hcode sk n
  split at hl
  · rename_i hk
    cases hl
    have hf : f = "add_n" := nameCode_inj ((beq_iff_eq.mp hk).trans nameCode_add_n.symm)
    subst hf
    refine ⟨rfl, fun sk n fd kf hlk hcode => ?_⟩
    rw [checkerProgI_addN] at hlk
    cases hlk
    rw [← hT] at hcode
    exact chain2Asm_sim checkerProgI G hG _ _ _ (addN_spec _ checkerProgI_addN) rfl rfl
      (by rw [hT]; exact checkerTab_pool) (by rw [hT]; exact checkerTab_poolL) (by rw [hT]; exact checkerTab_poolB)
      kf hcode sk n
  split at hl
  · rename_i hk
    cases hl
    have hf : f = "add_1" := nameCode_inj ((beq_iff_eq.mp hk).trans nameCode_add_1.symm)
    subst hf
    refine ⟨rfl, fun sk n fd kf hlk hcode => ?_⟩
    rw [checkerProgI_add1] at hlk
    cases hlk
    rw [← hT] at hcode
    exact chain1Asm_sim checkerProgI G hG _ _ _ (add1_spec _ checkerProgI_add1) rfl rfl
      (by rw [hT]; exact checkerTab_pool) (by rw [hT]; exact checkerTab_poolL) (by rw [hT]; exact checkerTab_poolB)
      kf hcode sk n
  split at hl
  · rename_i hk
    cases hl
    have hf : f = "sub_n" := nameCode_inj ((beq_iff_eq.mp hk).trans nameCode_sub_n.symm)
    subst hf
    refine ⟨rfl, fun sk n fd kf hlk hcode => ?_⟩
    rw [checkerProgI_subN] at hlk
    cases hlk
    rw [← hT] at hcode
    exact chain2Asm_sim checkerProgI G hG _ _ _ (subN_spec _ checkerProgI_subN) rfl rfl
      (by rw [hT]; exact checkerTab_pool) (by rw [hT]; exact checkerTab_poolL) (by rw [hT]; exact checkerTab_poolB)
      kf hcode sk n
  split at hl
  · rename_i hk
    cases hl
    have hf : f = "sub_1" := nameCode_inj ((beq_iff_eq.mp hk).trans nameCode_sub_1.symm)
    subst hf
    refine ⟨rfl, fun sk n fd kf hlk hcode => ?_⟩
    rw [checkerProgI_sub1] at hlk
    cases hlk
    rw [← hT] at hcode
    exact chain1Asm_sim checkerProgI G hG _ _ _ (sub1_spec _ checkerProgI_sub1) rfl rfl
      (by rw [hT]; exact checkerTab_pool) (by rw [hT]; exact checkerTab_poolL) (by rw [hT]; exact checkerTab_poolB)
      kf hcode sk n
  split at hl
  · rename_i hk
    cases hl
    have hf : f = "nat_mad" := nameCode_inj ((beq_iff_eq.mp hk).trans nameCode_nat_mad.symm)
    subst hf
    refine ⟨rfl, fun sk n fd kf hlk hcode => ?_⟩
    rw [checkerProgI_natMad] at hlk
    cases hlk
    rw [← hT] at hcode
    exact natMadAsm_sim checkerProgI G hG checkerProgI_natMad (by rw [hT]; exact checkerTab_pool)
      (by rw [hT]; exact checkerTab_poolL) (by rw [hT]; exact checkerTab_poolB) kf hcode sk n
  · cases hl

end L.Checker
