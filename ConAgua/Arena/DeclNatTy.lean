module

public import ConAgua.Arena.DeclNatGuard
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclNatGate
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Triple.SpecLemmas
public import ConRon.Arena.DeclCheck
import all ConAgua.Arena.DeclArmsNat

@[expose] public section

/-!
# The structural-`Nat` gate: the pinned types (lane `decls3`, helper `decls3-nat`)

`nat_op_cod`, `nat_op_ty_pinned`, `nat_op_stored_ok`, `nat_op_stored_ok_all`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

structure NatTyProg (p : Prog) : Prop extends NatGuardProg p where
  lNatOpCod : p.lookup "nat_op_cod" = some natOpCodL
  lNatOpTyPinned : p.lookup "nat_op_ty_pinned" = some natOpTyPinnedL
  lNatOpStoredOk : p.lookup "nat_op_stored_ok" = some natOpStoredOkL
  lNatOpStoredOkAll : p.lookup "nat_op_stored_ok_all" = some natOpStoredOkAllL

theorem rd64_eq_rdW (m : Mem) (a : ArrId) (i : Word) : L.rd64 m a i = rdW (m.arr64 a) i := by
  simp [L.rd64, rdW, Array.getD_eq_getD_getElem?]

section ty
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-! ### `nat_op_cod` -/

/-- **`nat_op_cod` is its model `natOpCodW`** (generated). -/
l_model natOpCod_specW (p : Prog) (hp : p.lookup "nat_op_cod" = some natOpCodL)
  fns [hp ↦ natOpCodW list]
  specs [callW_spec p n "pin_at", callW_spec p n "const_e", callW_spec p n "env_find", callW_spec p n "ci_to_cv", callW_spec p n "pin_word"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW instances 10000

theorem natOpCod_ref (hN : NatTyProg p) (c e : Word) :
    CallRef p "nat_op_cod" [vis, c, e] (fun m a => StageR vis fe m a ∧ H c ∧ H e)
      (natOpCod fe (decI c) (decI e)) (KeepPost vis fe decW0B) := by
  sorry

@[refines ConRon.Arena.natOpCod]
theorem natOpCod_refines (hN : NatTyProg p) (c e : Word) :
    RefAM p "nat_op_cod" [vis, c, e] (fun m a => StageR vis fe m a ∧ H c ∧ H e)
      (natOpCod fe (decI c) (decI e)) (KeepPost vis fe decW0B) :=
  (natOpCod_ref hN c e).refAM

/-! ### `nat_op_ty_pinned` -/

/-- **`nat_op_ty_pinned` is its model `natOpTyPinnedW`** (generated). -/
l_model natOpTyPinned_specW (p : Prog) (hp : p.lookup "nat_op_ty_pinned" = some natOpTyPinnedL)
  fns [hp ↦ natOpTyPinnedW list]
  specs [callW_spec p n "pin_at", callW_spec p n "const_e", callW_spec p n "e_view", callW_spec p n "nat_op_cod"]
  grind [arena_grind] heartbeats 3200000 bind ntBW

theorem getD2 (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  cases r with
  | nil => simp
  | cons a t => cases t with
    | nil => simp
    | cons b u => cases u <;> simp

theorem viewR_forall {rv : List Word} {v : ENodeView} (h : ViewR rv v) :
    (rv.headD 0 = 6 ∧ ∃ dom body, v = .forallE dom body ∧ H (rv.tail.headD 0) ∧
      decE (rv.tail.headD 0) = dom ∧ H (rv.tail.tail.headD 0) ∧ decE (rv.tail.tail.headD 0) = body) ∨
    (rv.headD 0 ≠ 6 ∧ ∀ dom body, v ≠ .forallE dom body) := by
  cases v <;> simp only [ViewR] at h
  all_goals first
    | (left; obtain ⟨h0, h1, h2, h3, h4⟩ := h
       refine ⟨h0, _, _, rfl, ?_, ?_, ?_, ?_⟩ <;> simp_all [H])
    | (right; refine ⟨?_, fun _ _ => by simp⟩; simp_all)

theorem natOpTyPinned_ref (hN : NatTyProg p) (c ty : Word) :
    CallRef p "nat_op_ty_pinned" [vis, c, ty] (fun m a => StageR vis fe m a ∧ H c ∧ H ty)
      (natOpTyPinned fe (decI c) (decI ty)) (KeepPost vis fe decW0B) := by
  sorry

@[refines ConRon.Arena.natOpTyPinned]
theorem natOpTyPinned_refines (hN : NatTyProg p) (c ty : Word) :
    RefAM p "nat_op_ty_pinned" [vis, c, ty] (fun m a => StageR vis fe m a ∧ H c ∧ H ty)
      (natOpTyPinned fe (decI c) (decI ty)) (KeepPost vis fe decW0B) :=
  (natOpTyPinned_ref hN c ty).refAM

/-! ### `nat_op_stored_ok` -/

/-- **`nat_op_stored_ok` is its model `natOpStoredOkW`** (generated). -/
l_model natOpStoredOk_specW (p : Prog) (hp : p.lookup "nat_op_stored_ok" = some natOpStoredOkL)
  fns [hp ↦ natOpStoredOkW list]
  specs [callW_spec p n "env_find", callW_spec p n "nat_op_ty_pinned"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW instances 10000

theorem natOpStoredOk_ref (hN : NatTyProg p) (w : Word) :
    CallRef p "nat_op_stored_ok" [vis, w] (fun m a => StageR vis fe m a ∧ H w)
      (natOpStoredOk fe (decI w)) (KeepPost vis fe decW0B) := by
  sorry

@[refines ConRon.Arena.natOpStoredOk]
theorem natOpStoredOk_refines (hN : NatTyProg p) (w : Word) :
    RefAM p "nat_op_stored_ok" [vis, w] (fun m a => StageR vis fe m a ∧ H w)
      (natOpStoredOk fe (decI w)) (KeepPost vis fe decW0B) :=
  (natOpStoredOk_ref hN w).refAM

theorem slice_succ {o l : Word} (hl0 : l ≠ 0) (hb : o.toNat + l.toNat < 2 ^ 64) :
    (o + 1).toNat = o.toNat + 1 ∧ (l - 1).toNat + 1 = l.toNat := by
  have hpos : 0 < l.toNat := Nat.pos_of_ne_zero (fun h => hl0 (UInt64.toNat_inj.mp (by simpa using h)))
  refine ⟨by rw [UInt64.toNat_add]; simp; omega, ?_⟩
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
  simp; omega

/-! ### `nat_op_stored_ok_all` -/

/-- **`nat_op_stored_ok_all` is its model `okAllW`** (generated). -/
l_model okAll_specW (p : Prog) (hp : p.lookup "nat_op_stored_ok_all" = some natOpStoredOkAllL)
  fns [hp ↦ okAllW list]
  specs [callW_spec p n "nat_op_stored_ok", callW_spec p n "nat_op_stored_ok_all"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW

theorem okAll_ref (hN : NatTyProg p) (o l : Word) (ns : List NIdx) :
    ∀ (k : Nat) (m : Mem) (a : AState) (r : List Word) (m' : Mem), StageR vis fe m a →
      decHL m o.toNat l.toNat = some ns → o.toNat + l.toNat ≤ iwTop m →
      callW p k "nat_op_stored_ok_all" [vis, o, l] m = some (r, m') →
      ∃ x a', (natOpStoredOkAll fe ns).run a = .ok (x, a') ∧ KeepPost vis fe decW0B m m' a' r x := by
  sorry

@[refines ConRon.Arena.natOpStoredOkAll]
theorem natOpStoredOkAll_refines (hN : NatTyProg p) (o l : Word) (ns : List NIdx) :
    RefAM p "nat_op_stored_ok_all" [vis, o, l]
      (fun m a => StageR vis fe m a ∧ decHL m o.toNat l.toNat = some ns ∧ o.toNat + l.toNat ≤ iwTop m)
      (natOpStoredOkAll fe ns) (KeepPost vis fe decW0B) :=
  CallRef.refAM (fun k m a r m' ⟨hS, hd, hb⟩ hc => okAll_ref hN o l ns k m a r m' hS hd hb hc)

end ty

end L.Ind
