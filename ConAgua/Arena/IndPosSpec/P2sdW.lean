import ConAgua.Arena.IndPosSpec.GgW2
import ConAgua.Arena.IndPosSpec.P2rtW

/-!
# P2sdW

`p2sdW`, `p2sdK1`, `p2sdK2`, `p2sdK3`, `nestSeeds_spec` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

mutual
/-- `nest_seeds`. -/
def p2sdW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, vis, ctx, sO, sL, ns =>
    if sL = 0 then some ([ns], m)
    else p2sdK1 cR n vis ctx sO sL (nhiW m ctx 0) (rdW (m.arr64 IW) (rdW (m.arr64 IW) sO))
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) sO + 1)) ns
      (p2sfW n m (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) sO) + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) sO) + 3)) 0 SLACK)
def p2sdK1 (cR : CallM) (n : Nat) (vis ctx sO sL hi key nPc ns : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => p2sdK2 cR n vis ctx sO sL key nPc ns (r.headD 0) (nitWf cR n m1 vis ctx hi key)
def p2sdK2 (cR : CallM) (n : Nat) (vis ctx sO sL key nPc ns f : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => p2sdK3 cR n vis ctx sO sL
      (nbKeyW cR n m2 vis ctx f 0 0 0 (rdW (m2.arr64 IW) key) (rdW (m2.arr64 IW) (key + 1))
        (rdW (m2.arr64 IW) (key + 2)) (rdW (m2.arr64 IW) (key + 3)) nPc (r.tail.headD 0) ns)
def p2sdK3 (cR : CallM) (n : Nat) (vis ctx sO sL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => p2sdW cR n m3 vis ctx (sO + 1) (sL - 1) (r.tail.headD 0)
end

section arms
variable (cR : CallM) (n : Nat) (m m1 : Mem) (vis ctx ns f sO sL hi key nPc : Word)
  (r : List Word)
theorem p2sdW_succ : p2sdW cR (n + 1) m vis ctx sO sL ns =
    if sL = 0 then some ([ns], m)
    else p2sdK1 cR n vis ctx sO sL (nhiW m ctx 0) (rdW (m.arr64 IW) (rdW (m.arr64 IW) sO))
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) sO + 1)) ns
      (p2sfW n m (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) sO) + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) sO) + 3)) 0 SLACK) := by
  rw [p2sdW]
theorem p2sdK1_some : p2sdK1 cR n vis ctx sO sL hi key nPc ns (some (r, m1)) =
    p2sdK2 cR n vis ctx sO sL key nPc ns (r.headD 0) (nitWf cR n m1 vis ctx hi key) := by rw [p2sdK1]
theorem p2sdK2_some : p2sdK2 cR n vis ctx sO sL key nPc ns f (some (r, m1)) =
    p2sdK3 cR n vis ctx sO sL
      (nbKeyW cR n m1 vis ctx f 0 0 0 (rdW (m1.arr64 IW) key) (rdW (m1.arr64 IW) (key + 1))
        (rdW (m1.arr64 IW) (key + 2)) (rdW (m1.arr64 IW) (key + 3)) nPc (r.tail.headD 0) ns) := by rw [p2sdK2]
theorem p2sdK3_some : p2sdK3 cR n vis ctx sO sL (some (r, m1)) =
    p2sdW cR n m1 vis ctx (sO + 1) (sL - 1) (r.tail.headD 0) := by rw [p2sdK3]
end arms
section spec
variable {p : Prog} (L : RsLook p)
include L

theorem nestSeeds_spec (cR : CallM) (hcR : CallSpec p cR) (n : Nat) : ∀ (s₀ : St) (vis ctx sO sL ns : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_seeds" [vis, ctx, sO, sL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ p2sdW cR n s₀.mem vis ctx sO sL ns = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis ctx sO sL ns
    exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | succ n ih =>
    intro s₀ vis ctx sO sL ns
    have R := L.nb.ct.cr.rx
    have hKey := (nbSpec_all L.nb cR hcR n).2.2.2.2.1
    simp only [invoke_eq _ L.pseeds, callFn, nestSeedsL]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        nestCtxHiAt_specE p R.hi n, nestSeedsFuel_spec L n, nestInstType_spec' p L.nb.nit cR hcR n, hKey, ih] <;>
      simp_all [p2sdW_succ, p2sdK1_some, p2sdK2_some, p2sdK3_some, SLACK,
        LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
        St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

end spec

end L.Ind

end
