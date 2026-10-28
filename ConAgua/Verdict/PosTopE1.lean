import ConAgua.Arena.Verdict
import ConAgua.Arena.IndPosSpec.NuW
import ConAgua.Checker.NoVerdictTree
import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPosSpec.RsLook

/-!
# The positivity pass's entry points: error models (lane `verdicts-b`, helper `ia2`, fork `top`)

The `errors` models of `check_abs_ctor_sorts_one`, `check_abs_ctor_sorts`,
`check_abs_ctor_sorts_all`, `nest_uniform`, `nest_root`, `nest_seeds`, `check_block_positivity`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

noncomputable section

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model iaoE_spec (p : Prog) (hf : p.lookup "check_abs_ctor_sorts_one" = some checkAbsCtorSortsOne)
  fns [hf ↦ iaoE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model iacE_spec (p : Prog) (hf : p.lookup "check_abs_ctor_sorts" = some checkAbsCtorSorts)
  fns [hf ↦ iacE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model iaaE_spec (p : Prog) (hf : p.lookup "check_abs_ctor_sorts_all" = some checkAbsCtorSortsAll)
  fns [hf ↦ iaaE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

/-- `nest_uniform_cs`' model with its one result as a word (the generator reads `some (r, m)`). -/
def ucW1 (cR : CallM) (k : Nat) (m : Mem) (ctx o l : Word) : Option (Word × Mem) :=
  (ucW cR k m ctx o l).map fun x => (x.1.headD 0, x.2)

theorem ucW1_some {cR : CallM} {k : Nat} {m m' : Mem} {ctx o l b : Word}
    (h : ucW1 cR k m ctx o l = some (b, m')) : ∃ r, ucW cR k m ctx o l = some (r, m') ∧ r.headD 0 = b := by
  simp only [ucW1, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨r, m₁⟩, h, rfl, rfl⟩ := h
  exact ⟨r, h, rfl⟩

theorem nestUniformCs_spec1 (p : Prog) (hl : NuLook p) (hp : p.lookup "nest_uniform_cs" = some nestUniformCsL)
    (k : Nat) (s₀ : St) (ctx o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_uniform_cs" [ctx, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ucW1 (realCall p) k s₀.mem ctx o l = some (r.headD 0, s'.mem); ⊤⦄ :=
  triple_post (nestUniformCs_spec p hl hp (realCall p) (realCall_spec p) k s₀ ctx o l) fun r s' ⟨hl', h⟩ =>
    ⟨hl', by simp [ucW1, h]⟩

l_model nuE_spec (p : Prog) (hL : NuLook p) (hc : p.lookup "nest_uniform_cs" = some nestUniformCsL)
  (hf : p.lookup "nest_uniform" = some nestUniformL)
  fns [hf ↦ nuE list] specs [nestUniformCs_spec1 p hL hc n] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `nest_ctx_hi_at`'s model as an `Option` (the generator lifts those, not pure models). -/
def nhiO (m : Mem) (ctx nf : Word) : Option (Word × Mem) := some (nhiW m ctx nf, m)

theorem nestCtxHiAt_specO (p : Prog) (hp : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt) (n : Nat)
    (s₀ : St) (ctx nf : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctx_hi_at" [ctx, nf]
    ⦃fun r s' => LocEq s' s₀ ∧ nhiO s₀.mem ctx nf = some (r.headD 0, s'.mem); ⊤⦄ :=
  triple_post (nestCtxHiAt_specE p hp n s₀ ctx nf) fun _ _ ⟨hl, hm, hr⟩ => ⟨hl, by rw [nhiO, hm, hr]⟩

l_model nrtE_spec (p : Prog) (hL : RsLook p)
  fns [hL.proot ↦ nrtE list]
  specs [nestCtxHiAt_specO p hL.nb.ct.cr.rx.hi n, posRec2_specW p hL.nb.ct.cr.rx.ha hL.nb.ct.cr.rx.h2 n,
    slSnoc_specW p hL.nb.ct.cr.rx.ha hL.nb.nit.hc2 hL.nb.nag.hsn n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model nsdE_spec (p : Prog) (hf : p.lookup "nest_seeds" = some nestSeedsL)
  fns [hf ↦ nsdE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model cbpE_spec (p : Prog) (hf : p.lookup "check_block_positivity" = some checkBlockPositivity)
  fns [hf ↦ cbpE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

end L.Ind

end
