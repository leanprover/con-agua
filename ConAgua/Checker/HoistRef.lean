module

public import ConAgua.Checker.HoistTargetsRef
public import ConAgua.Checker.HoistOrderRef
public import ConAgua.Checker.HoistIndexRef
public import ConAgua.Checker.HoistNatRef
public import ConAgua.Checker.HoistWalkRef

@[expose] public section

/-!
# `hoist_nat_op_ground` refines `hoistNatOpGround` (lane `front4`)

The assembly: the name index (`hoistIndexGo_ok`), two fresh slices (targets, stack), the targets
zeroed, the targets pass (`targets_ok`: the twin's `hoistTargets`), `hoist_any` (`isEmpty`), and
the reorder (`hoistApply_ok`: `applyHoist`'s sorted order). When L returns, the twin returns, in
the same state, the records in the order L's result slice gives (`OrdR`); `movedNames` (the second
component) is not computed (docs/deviations.md D30).
-/

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

theorem getElem?_of_rd2 {m m' : Mem} (hs : (m'.arr64 IW).size = (m.arr64 IW).size) {x : Nat}
    (hx : x < 2 ^ 64) (h : rd m' x = rd m x) : (m'.arr64 IW)[x]? = (m.arr64 IW)[x]? := by
  have e : (UInt64.ofNat x).toNat = x := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hx
  simp only [rd, rdW, e] at h
  by_cases hl : x < (m.arr64 IW).size
  · rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hl] at *
    simp at h; rw [h]
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]

/-- The stream relation needs only the `IW` words below `B`, `DECL` and `DLP`. -/
theorem ordR_low {m m' : Mem} {ord : Word} {ds : Array IDeclaration} (B : Nat) (hO : OrdR m ord ds)
    (hB : ord.toNat + ds.size ≤ B) (hBs : B < 2 ^ 64)
    (hIW : ∀ x : Nat, x < B → (m'.arr64 IW)[x]? = (m.arr64 IW)[x]?)
    (hD : m'.arr64 DECL = m.arr64 DECL) (hP : m'.arr64 DLP = m.arr64 DLP) : OrdR m' ord ds := by
  intro k hk
  have hn : (ord + UInt64.ofNat k).toNat = ord.toNat + k := addW_toNat _ _ (by omega)
  have hr : rdW (m'.arr64 IW) (ord + UInt64.ofNat k) = rdW (m.arr64 IW) (ord + UInt64.ofNat k) := by
    simp only [rdW, hn]; rw [hIW _ (by omega)]
  rw [hr, hD, hP]
  exact hO k hk

/-- An allocation is an `AFr`. -/
theorem allocW_afr {m m₁ : Mem} {k q : Word} (hw : allocW m k = some (q, m₁)) (hI : IWOK m) :
    AFr m m₁ ∧ q.toNat = iwTop m ∧ iwTop m₁ = iwTop m + k.toNat ∧ iwTop m + k.toNat ≤ (m.arr64 IW).size := by
  sorry

/-- **The hoist on the model**: when `hoist_nat_op_ground(ord, c)` returns `r`, the twin's
`hoistNatOpGround ds` succeeds in the same state, and the slice `IW[r ‥ r + c)` is its records'
order (`OrdR`). -/
theorem hNatOpGround_ok (p : Prog) (hx : HoistExt p) (n : Nat) (m m' : Mem) (a : AState)
    (ds : Array IDeclaration) (ord cw r : Word) (hA : ArenaR m a) (hseen : ∃ s, SeenR m s)
    (hnix : ∃ idx, NixR m idx) (hO : OrdR m ord ds) (hc : ds.size = cw.toNat)
    (hc60 : cw.toNat < 2 ^ 60) (hI : IWOK m)
    (hord : ord.toNat + cw.toNat ≤ iwTop m) (hP : PinsR m a.pins)
    (h : hNatOpGroundW p n m ord cw = some (r, m')) :
    ∃ res, (hoistNatOpGround IDeclaration.usedConsts ds).run a = .ok (res, a) ∧ res.1.size = cw.toNat ∧ OrdR m' r res.1 ∧
      ArenaR m' a ∧ IWOK m' ∧ IWGrow m m' ∧ r.toNat + cw.toNat ≤ iwTop m' ∧ PinsR m' a.pins ∧
      MemFrame [IW, HSEEN, HNIX] [73, 74, 75, 76, 200] m m' := by
  sorry

/-- **`hoist_nat_op_ground(ord, c)` refines `hoistNatOpGround`** (its first component; the second,
`movedNames`, is dropped by `preparePrelude` and not computed: docs/deviations.md D30). When L
returns `r`, the twin succeeds in the same state and `IW[r ‥ r + c)` is the order of its records;
the memory still represents the store and the pins, and the pool only grew. -/
@[refines_part ConRon.Arena.Frontend.hoistNatOpGround
  "the reordered records (movedNames, dropped by preparePrelude, is not computed: D30)"]
theorem hoistNatOpGround_refines (p : Prog) (hp : HoistProg p) (hx : HoistExt p) (n : Nat) (s₀ : St)
    (a : AState) (ds : Array IDeclaration) (ord cw : Word) (hA : ArenaR s₀.mem a)
    (hseen : ∃ s, SeenR s₀.mem s) (hnix : ∃ idx, NixR s₀.mem idx) (hO : OrdR s₀.mem ord ds)
    (hc : ds.size = cw.toNat) (hc60 : cw.toNat < 2 ^ 60) (hI : IWOK s₀.mem)
    (hord : ord.toNat + cw.toNat ≤ iwTop s₀.mem) (hP : PinsR s₀.mem a.pins) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "hoist_nat_op_ground" [ord, cw]
    ⦃fun r s' => ∃ res, (hoistNatOpGround IDeclaration.usedConsts ds).run a = .ok (res, a) ∧ res.1.size = cw.toNat ∧
      OrdR s'.mem (r.headD 0) res.1 ∧ ArenaR s'.mem a ∧ IWOK s'.mem ∧ IWGrow s₀.mem s'.mem ∧
      (r.headD 0).toNat + cw.toNat ≤ iwTop s'.mem ∧ PinsR s'.mem a.pins ∧
      MemFrame [IW, HSEEN, HNIX] [73, 74, 75, 76, 200] s₀.mem s'.mem; ⊤⦄ :=
  triple_post (hoistNatOpGround_spec p hp hx n s₀ ord cw) (fun r s' h =>
    hNatOpGround_ok p hx n s₀.mem s'.mem a ds ord cw (r.headD 0) hA hseen hnix hO hc hc60 hI hord hP h.2)

/-! ## The links

The pieces are stated over the generated models (`hWalkW`, …), each of which is its L function by
the generated spec (`hoistWalk_spec`, …, `Hoist.lean`): the chain L = model ⊑ twin. -/

attribute [refines ConRon.Arena.Frontend.usedConstsGo] hoistWalk_ok
attribute [refines ConRon.Arena.Frontend.usedConstsRules] hoistRulesGo_ok
attribute [refines ConRon.Arena.Frontend.usedConstsBlock] hoistBlockGo_ok
attribute [refines ConRon.Arena.Frontend.IDeclaration.usedConsts] hoistDepsOf_ok
attribute [refines ConRon.Arena.Frontend.nameIndex] hoistIndexGo_ok
attribute [refines ConRon.Arena.Frontend.hoistClosure] closure_ok
attribute [refines ConRon.Arena.Frontend.hoistTargetsGo.hoistDeps] deps_ok
attribute [refines ConRon.Arena.Frontend.hoistTargetsGo] targets_ok
attribute [refines ConRon.Arena.Frontend.isNatOpRecord] natOpRec_ok
attribute [refines ConRon.Arena.Frontend.hoistTargets] hNatOpGround_ok
attribute [refines ConRon.Arena.Frontend.reorder ConRon.Arena.Frontend.hoistKey
  ConRon.Arena.Frontend.hoistLt] hoistApply_ok
attribute [refines_part ConRon.Arena.Frontend.applyHoist
  "the sorted records (movedNames, dropped by preparePrelude, is not computed: D30)"] hoistApply_ok

end L.Checker
