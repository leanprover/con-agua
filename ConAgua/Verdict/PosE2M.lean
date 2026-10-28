import ConAgua.Verdict.PosE3Fm
import ConAgua.Arena.IndPosSpec.NestGroupCtors
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.Verdict
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Error models of `nest_cont_new`, `nest_frame`, `nest_grow_group`, `nest_group_ctors` (lane
`verdicts-b`, helper `ia2`, fork `kn2a`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model nggE_spec (p : Prog) (hf : p.lookup "nest_grow_group" = some nestGrowGroupL)
  fns [hf ↦ nggE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

noncomputable section

l_model ngcE_spec (p : Prog) (hl : NtLook p) (hc : p.lookup "iw_copy" = some iwCopy)
    (hap : p.lookup "sl_append" = some slAppend) (hp : p.lookup "nest_group_ctors" = some nestGroupCtorsL)
  fns [hp ↦ ngcE list]
  specs [nt_spec' p hl n, slAppend_specW p hl.ha hc hap n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end

l_model nnewE_specC (p : Prog) (hf : p.lookup "nest_cont_new" = some nestContNewL)
  fns [hf ↦ nnewE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

/-- `nest_cont_new`'s unified spec (the error post over the class; the generated `unified` steps fail). -/
theorem nnewE_spec (p : Prog) (hf : p.lookup "nest_cont_new" = some nestContNewL) (n : Nat) (s₀ : St)
    (vis ctx fuel progOff progLen kb n' us dsOff dsLen nPc cty ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_new"
      [vis, ctx, fuel, progOff, progLen, kb, n', us, dsOff, dsLen, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      nnewE p n s₀.mem vis ctx fuel progOff progLen kb n' us dsOff dsLen nPc cty ns = .ok (r, s'.mem);
     fun ε => True → ε.cls ≠ 0 →
      nnewE p n s₀.mem vis ctx fuel progOff progLen kb n' us dsOff dsLen nPc cty ns = .error ε⦄ :=
  triple_uni_of_code (nnewE_specC p hf n s₀ _ _ _ _ _ _ _ _ _ _ _ _ _)

l_model nfrE_specC (p : Prog) (hf : p.lookup "nest_frame" = some nestFrameL)
  fns [hf ↦ nfrE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

/-- `nest_frame`'s unified spec (the error post over the class), from the `errors` spec. -/
theorem nfrE_spec (p : Prog) (hf : p.lookup "nest_frame" = some nestFrameL) (n : Nat) (s₀ : St)
    (vis ctx fuel progOff progLen hi us dsOff dsLen nPc grpOff grpLen ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame" [vis, ctx, fuel, progOff, progLen, hi, us, dsOff, dsLen, nPc, grpOff, grpLen, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nfrE p n s₀.mem vis ctx fuel progOff progLen hi us dsOff dsLen nPc grpOff grpLen ns = .ok (r, s'.mem);
     fun ε => True → ε.cls ≠ 0 → nfrE p n s₀.mem vis ctx fuel progOff progLen hi us dsOff dsLen nPc grpOff grpLen ns = .error ε⦄ :=
  triple_uni_of_code (nfrE_specC p hf n s₀ _ _ _ _ _ _ _ _ _ _ _ _ _)

end L.Ind
