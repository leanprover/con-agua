import ConAgua.Arena.IndInstallSpec6

/-!
# Refinements of `IndInstall`, part 7 (lane `indproofs2`, helper `parts`): `blockNestCtx`

The direct-recursion context: member 0's former telescope opened at the parameters
(`open_pis_at_fvars_f`, a stub), the walk's context (`BlockShape.nestCtx`), its holes
(`nest_holes`, helper `pos`'s). `nP + k` past `2^64` is a capacity abort.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `nest_holes`' model as a `Sim` (helper `pos`'s `nestHoles_refines`, unpacked). -/
theorem nhW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat) {m : Mem}
    {a : AState} {ctx : Word} {c : NestCtx} (hS : StageR dn vis fe m a) (hc : decCtx m ctx.toNat = some c)
    (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat) (hhi : c.hiAt 0 < 2 ^ 64) :
    Sim (nhW k m vis ctx) (ConRon.Arena.nestHoles fe c) a
      (fun r x m' a' => NhOut m' r x ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  intro r m' hm
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hn, hnb, -⟩ := ctx_fields hc hin htop
  have hlen := decHL_length _ hn
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := nhGoW_ok dn fe vis ctx c k _ _ a 0 _ _ 0 0 c.names [] _ hm hS hc hin
    hsl hn hnb (by simp [decHL, hslice?]) (by simp) (by have := hlen; simp [NestCtx.hiAt] at hhi; simp; omega)
  have he : ConRon.Arena.nestHoles fe c = ConRon.Arena.nestHoles.go fe c 0 c.names [] := rfl
  rw [show (0 : Word).toNat = 0 from rfl, ← he] at hrun
  refine ⟨x, a', hrun, ?_, hS', hg⟩
  cases x with
  | none => exact hout
  | some l => obtain ⟨h1, h2, h3⟩ := hout; exact ⟨h1, h2, h3⟩

/-- After `nest_holes`. -/
def bncK3 (ctx : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else some ([ctx, r.tail.headD 0, r.tail.tail.headD 0], m)

/-- After `block_shape_nest_ctx`. -/
def bncK2 (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bncK3 (r.headD 0) (nhW n m vis (r.headD 0))

/-- After `open_pis_at_fvars_f`. -/
def bncK1 (n : Nat) (vis p : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else bncK2 n vis (nckW n m p (r.tail.headD 0) (r.tail.tail.headD 0))

/-- **The model of `block_nest_ctx`** (at exec fuel `n + 2`). -/
def bncW (n : Nat) (m : Mem) (vis p cvO cvL : Word) : Option (List Word × Mem) :=
  if cvL = 0 then none
  else if rdW (m.arr64 IW) (p + 4) + rdW (m.arr64 IW) (p + 1) < rdW (m.arr64 IW) (p + 4) then none
  else bncK1 n vis p (stubM "open_pis_at_fvars_f" m [rdW (m.arr64 IW) (p + 4),
    rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvO + 3), 0])

section arms
variable (n : Nat) (m : Mem) (vis p ctx : Word) (r : List Word)
theorem bncK3_none (h : r.headD 0 = 0) : bncK3 ctx (some (r, m)) = none := by
  simp only [bncK3]; exact if_pos h
theorem bncK3_some (h : ¬ r.headD 0 = 0) : bncK3 ctx (some (r, m)) =
    some ([ctx, r.tail.headD 0, r.tail.tail.headD 0], m) := by simp only [bncK3]; exact if_neg h
theorem bncK2_some : bncK2 n vis (some (r, m)) = bncK3 (r.headD 0) (nhW n m vis (r.headD 0)) := rfl
theorem bncK1_none (h : r.headD 0 = 0) : bncK1 n vis p (some (r, m)) = none := by
  simp only [bncK1]; exact if_pos h
theorem bncK1_some (h : ¬ r.headD 0 = 0) : bncK1 n vis p (some (r, m)) =
    bncK2 n vis (nckW n m p (r.tail.headD 0) (r.tail.tail.headD 0)) := by simp only [bncK1]; exact if_neg h
end arms
attribute [ind_grind] bncK3_none bncK3_some bncK2_some bncK1_none bncK1_some

theorem bnc_spec (p : Prog) (hP : NckProg p) (hl : NhLook p)
    (hp : p.lookup "block_nest_ctx" = some blockNestCtx) (n : Nat) (s₀ : St) (vis q cvO cvL : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 2)) "block_nest_ctx" [vis, q, cvO, cvL]
    ⦃fun r s' => LocEq s' s₀ ∧ bncW n s₀.mem vis q cvO cvL = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockNestCtx]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      stubM_spec p "open_pis_at_fvars_f" (n + 1), nck_spec p hP n, nestHoles_spec p hl n] <;>
    finish (gen := 20) [bncW, rdW_eq]

end L.Ind
