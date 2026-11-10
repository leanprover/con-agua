module

public import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndPosSpec.NestHoles
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.Arena.IndPosSpec.Pos2CvLpsWStage

@[expose] public section

/-!
# NhW

`nhW_sim`, `bncK3`, `bncK2`, `bncK1`, `bncK3_none`, `bncK3_some` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `nest_holes`' model as a `Sim` (helper `pos`'s `nestHoles_refines`, unpacked). -/
theorem nhW_sim {vis : Word} {fe : IFEnv} (k : Nat) {m : Mem}
    {a : AState} {ctx : Word} {c : NestCtx} (hS : StageR vis fe m a) (hc : decCtx m ctx.toNat = some c)
    (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat) (hhi : c.hiAt 0 < 2 ^ 64) :
    Sim (nhW k m ctx) (ConRon.Arena.nestHoles c) a
      (fun r x m' a' => NhOut m' r x ∧ StageR vis fe m' a' ∧ IWGrow m m') := by
  intro r m' hm
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  obtain ⟨hn, hnb, -⟩ := ctx_fields hc hin htop
  have hlen := decHL_length _ hn
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := nhGoW_ok fe vis ctx c k _ _ a 0 _ _ 0 0 c.names [] _ hm hS hc hin
    hsl hn hnb (by simp [decHL, hslice?]) (by simp) (by have := hlen; simp [NestCtx.hiAt] at hhi; simp; omega)
  have he : ConRon.Arena.nestHoles c = ConRon.Arena.nestHoles.go c 0 c.names [] := rfl
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
def bncK2 (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bncK3 (r.headD 0) (nhW n m (r.headD 0))

/-- After `open_pis_at_fvars_f`. -/
def bncK1 (n : Nat) (p : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else if r.tail.tail.headD 0 + rdW (m.arr64 IW) (p + 1) < r.tail.tail.headD 0 then none
    else bncK2 n (nckW n m p (r.tail.headD 0) (r.tail.tail.headD 0))

section arms
variable (n : Nat) (m : Mem) (p ctx : Word) (r : List Word)
theorem bncK3_none (h : r.headD 0 = 0) : bncK3 ctx (some (r, m)) = none := by
  simp only [bncK3]; exact ite_eq_left h
theorem bncK3_some (h : ¬ r.headD 0 = 0) : bncK3 ctx (some (r, m)) =
    some ([ctx, r.tail.headD 0, r.tail.tail.headD 0], m) := by simp only [bncK3]; exact ite_eq_right h
theorem bncK2_some : bncK2 n (some (r, m)) = bncK3 (r.headD 0) (nhW n m (r.headD 0)) := rfl
theorem bncK1_none (h : r.headD 0 = 0) : bncK1 n p (some (r, m)) = none := by
  simp only [bncK1]; exact ite_eq_left h
theorem bncK1_ov (h : ¬ r.headD 0 = 0)
    (ho : r.tail.tail.headD 0 + rdW (m.arr64 IW) (p + 1) < r.tail.tail.headD 0) :
    bncK1 n p (some (r, m)) = none := by simp only [bncK1]; rw [ite_eq_right h, ite_eq_left ho]
theorem bncK1_some (h : ¬ r.headD 0 = 0)
    (ho : ¬ r.tail.tail.headD 0 + rdW (m.arr64 IW) (p + 1) < r.tail.tail.headD 0) : bncK1 n p (some (r, m)) =
    bncK2 n (nckW n m p (r.tail.headD 0) (r.tail.tail.headD 0)) := by
  simp only [bncK1]; rw [ite_eq_right h, ite_eq_right ho]
end arms
attribute [ind_grind] bncK3_none bncK3_some bncK2_some bncK1_none bncK1_ov bncK1_some

end L.Ind

end
