import ConAgua.Arena.IndPos2SpecO

/-! # `IndPos2`, the root frame and the seeds (lane `indproofs2`, helper `pos2`): the word models of
`nest_root`, `nest_seeds_fuel`, `nest_seeds`, and L ⊑ the models at every exec fuel. -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Models -/

mutual
/-- `nest_root`. -/
def p2rtW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, ctx, hO, hL, cO, cL, ns, oO, oL =>
    if cL = 0 then some ([oO, oL, ns], m)
    else p2rtK1 cR n vis ctx hO hL cO cL oO oL
      (nbCtorsW cR n m vis ctx 1 0 0 0 (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 10)) (rdW (m.arr64 IW) (ctx + 7))
        (rdW (m.arr64 IW) (ctx + 8)) (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) hO hL
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO)) (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1)) ns 0 0)
def p2rtK1 (cR : CallM) (n : Nat) (vis ctx hO hL cO cL oO oL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => p2rtK2 cR n vis ctx hO hL cO cL oO oL (r.tail.tail.headD 0) (posRecW m1 [r.headD 0, r.tail.headD 0])
def p2rtK2 (cR : CallM) (n : Nat) (vis ctx hO hL cO cL oO oL ns2 : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m2) => p2rtK3 cR n vis ctx hO hL cO cL ns2 (snocW n m2 oO oL q)
def p2rtK3 (cR : CallM) (n : Nat) (vis ctx hO hL cO cL ns2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => p2rtW cR n m3 vis ctx hO hL (cO + 1) (cL - 1) ns2 (r.headD 0) (r.tail.headD 0)
end

mutual
/-- `nest_seeds_fuel`. -/
def p2sfW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, dO, dL, k, f =>
    if dL ≤ k then some ([f], m)
    else p2sfK n dO dL k f (wfWf n m (rdW (m.arr64 IW) (dO + k)))
def p2sfK (n : Nat) (dO dL k f : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => p2sfW n m1 dO dL (k + 1) (if f < r.headD 0 then r.headD 0 else f)
end

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
variable (cR : CallM) (n : Nat) (m m1 : Mem) (vis ctx hO hL cO cL ns oO oL ns2 q dO dL k f sO sL hi key nPc : Word)
  (r : List Word)
theorem p2rtW_succ : p2rtW cR (n + 1) m vis ctx hO hL cO cL ns oO oL =
    if cL = 0 then some ([oO, oL, ns], m)
    else p2rtK1 cR n vis ctx hO hL cO cL oO oL
      (nbCtorsW cR n m vis ctx 1 0 0 0 (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 10)) (rdW (m.arr64 IW) (ctx + 7))
        (rdW (m.arr64 IW) (ctx + 8)) (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) hO hL
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO)) (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1)) ns 0 0) := by
  rw [p2rtW]
theorem p2rtK1_some : p2rtK1 cR n vis ctx hO hL cO cL oO oL (some (r, m1)) =
    p2rtK2 cR n vis ctx hO hL cO cL oO oL (r.tail.tail.headD 0) (posRecW m1 [r.headD 0, r.tail.headD 0]) := by
  rw [p2rtK1]
theorem p2rtK2_some : p2rtK2 cR n vis ctx hO hL cO cL oO oL ns2 (some (q, m1)) =
    p2rtK3 cR n vis ctx hO hL cO cL ns2 (snocW n m1 oO oL q) := by rw [p2rtK2]
theorem p2rtK3_some : p2rtK3 cR n vis ctx hO hL cO cL ns2 (some (r, m1)) =
    p2rtW cR n m1 vis ctx hO hL (cO + 1) (cL - 1) ns2 (r.headD 0) (r.tail.headD 0) := by rw [p2rtK3]
theorem p2sfK_some : p2sfK n dO dL k f (some (r, m1)) =
    p2sfW n m1 dO dL (k + 1) (if f < r.headD 0 then r.headD 0 else f) := by rw [p2sfK]
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
theorem p2sfW_done (h : dL ≤ k) : p2sfW (n + 1) m dO dL k f = some ([f], m) := by simp [p2sfW, h]
theorem p2sfW_step (h : ¬ dL ≤ k) : p2sfW (n + 1) m dO dL k f =
    p2sfK n dO dL k f (wfWf n m (rdW (m.arr64 IW) (dO + k))) := by simp [p2sfW, h]
end arms
attribute [ind_grind] p2sfW_done p2sfW_step p2sfK_some

/-! ## L ⊑ the models -/

/-- The root frame's and the seeds' lookups. -/
structure RsLook (p : Prog) : Prop where
  nb : NbLook p
  proot : p.lookup "nest_root" = some nestRootL
  pfuel : p.lookup "nest_seeds_fuel" = some nestSeedsFuelL
  pseeds : p.lookup "nest_seeds" = some nestSeedsL

section spec
variable {p : Prog} (L : RsLook p)
include L

theorem nestSeedsFuel_spec (n : Nat) : ∀ (s₀ : St) (dO dL k f : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_seeds_fuel" [dO, dL, k, f]
    ⦃fun r s' => LocEq s' s₀ ∧ p2sfW n s₀.mem dO dL k f = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ dO dL k f
    exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | succ n ih =>
    intro s₀ dO dL k f
    simp only [invoke_eq _ L.pfuel, callFn, nestSeedsFuelL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, whnfWalkFuel_spec' p L.nb n, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem nestRoot_spec (cR : CallM) (hcR : CallSpec p cR) (n : Nat) : ∀ (s₀ : St) (vis ctx hO hL cO cL ns oO oL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_root" [vis, ctx, hO, hL, cO, cL, ns, oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧ p2rtW cR n s₀.mem vis ctx hO hL cO cL ns oO oL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis ctx hO hL cO cL ns oO oL
    exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | succ n ih =>
    intro s₀ vis ctx hO hL cO cL ns oO oL
    have R := L.nb.ct.cr.rx
    have hCtors := (nbSpec_all L.nb cR hcR n).2.2.2.2.2.2.2.1
    simp only [invoke_eq _ L.proot, callFn, nestRootL]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        nestCtxHiAt_specE p R.hi n, hCtors, posRec2_specW p R.ha R.h2 n,
        slSnoc_specW p R.ha L.nb.nit.hc2 L.nb.nag.hsn n, ih] <;>
      simp_all [p2rtW_succ, p2rtK1_some, p2rtK2_some, p2rtK3_some,
        LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
        St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

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
