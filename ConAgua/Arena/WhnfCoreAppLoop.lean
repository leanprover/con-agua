module

import ConAgua.Arena.WhnfCoreApp
public import ConAgua.Arena.RefECore
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.KnotE
public import ConAgua.Verdict.WhnfModels2E
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.L.WordOff
import ConAgua.Arena.Inst1Refine

@[expose] public section

/-!
# `whnf_app` refines `whnfApp` (split from `WhnfCoreApp.lean`)

One refinement over the loop's unified model (`whnfAppE`, `Verdict/WhnfModels2E.lean`), both
outcomes, by induction on the L fuel (`appLoop_ref`, `app_ref`); its errors are `iota_rec_at`'s
(`AppG`). `WhnfCoreApp.lean` has the helpers and `beta_peel`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- The next spine node of the walk: the saved node (`same`), else `mk_app(v, a)`. -/
def apW (p : Prog) (k : Nat) (m : Mem) (v same a node : Word) : Option (Word × Mem) :=
  if same ≠ 0 then some (node, m)
  else match callW p k "mk_app" [v, a] m with
    | none => none
    | some (r, m₁) => some (r.headD 0, m₁)

/-- The twin's `whnfApp` after the ι step's answer. -/
def appStepT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (hd ap : EIdx)
    (va : Array EIdx) (same2 : Bool) (args nodes : Array EIdx) (i : Nat) (step : Option EIdx) :
    AM WhnfStep :=
  match step with
  | none => whnfApp mode r fe depth ap hd va same2 args nodes (i + 1)
  | some e2 => do
    let e3 ← mkAppNFrom e2 args (i + 1)
    pure (WhnfStep.cont e3)

theorem whnfApp_nolam (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (v hd : EIdx) (vargs : Array EIdx) (same : Bool) (args nodes : Array EIdx) (i : Nat)
    (hi : i < args.size) (hv : (v.tag == ETag.lam) = false) :
    whnfApp mode r fe depth v hd vargs same args nodes i =
      (show AM WhnfStep from do
        let ap ← internAppRebuilt nodes[i]! same v args[i]
        if hd.tag == ETag.const then do
          let step ← iotaRecAt mode r fe depth hd (vargs.push args[i]) (vargs.push args[i]).size
          appStepT mode r fe depth hd ap (vargs.push args[i]) (ap == nodes[i]!) args nodes i step
        else
          appStepT mode r fe depth hd ap (vargs.push args[i]) (ap == nodes[i]!) args nodes i none) := by
  rw [whnfApp]
  simp only [hi, dite_true, hv, Bool.false_eq_true, ite_false]
  rfl

section appRef0
variable (p : Prog) (hp : WhnfCoreProg p)

include hp in
/-- **The next spine node refines `internAppRebuilt`**: the saved node, or `mk_app`'s interning. -/
theorem apW_ref (k : Nat) (m : Mem) (a : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb : Word) (hS : CoreS dn m a vis fe MM eb)
    (v same aW nW : Word) (_hv : HW v) (_ha : HW aW) (hnW : HW nW) (ap : Word) (m₁ : Mem)
    (h : apW p k m v same aW nW = some (ap, m₁)) :
    ∃ a₁, (internAppRebuilt (decE nW) (same != 0) (decE v) (decE aW)).run a = .ok (decE ap, a₁) ∧
      CoreS dn m₁ a₁ vis fe MM eb ∧ StackKept m m₁ ∧ HW ap := by
  unfold apW at h
  by_cases hs : same ≠ 0
  · simp only [hs, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb : (same != 0) = true := by simpa using hs
    refine ⟨a, ?_, hS, StackKept.refl _, hnW⟩
    simp only [internAppRebuilt, hb, ite_true]; rfl
  · simp only [hs, ↓reduceIte] at h
    have hs' : same = 0 := by simpa using hs
    have hb : (same != 0) = false := by simp [hs']
    cases hc : callW p k "mk_app" [v, aW] m with
    | none => rw [hc] at h; simp at h
    | some q =>
    obtain ⟨r, m'⟩ := q
    rw [hc] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hok, hD, hres, hfr, hhw⟩ := callW_mkApp p hp.spine k ⟨m, Locals.init []⟩ a hS.arena
      v aW r m' hc
    have hrun := AM.run_of_ok _ _ hok
    refine ⟨AM.st (internE (.app (decE v) (decE aW))) a, ?_, ?_, StackKept.of_app_frame hfr, hhw⟩
    · simp only [internAppRebuilt, hb, Bool.false_eq_true, ite_false]
      rw [hrun, hres]
    · exact hS.of_app hD (Keeps.run (keeps_cpl_internApp _ _) hrun) hfr

end appRef0
/-! ## The ι step's claim and what the `app` arm's errors assume -/

/-- `iota_rec_at`'s error claim at fuel `N + 1` (the shape of `IotaRecAtOK`). -/
def IotaRecAtE (p : Prog) : Prop :=
  ∀ N, KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d hd so sn : Word) (xs : Array EIdx), N ≤ F → N ≤ 2 ^ 62 →
    SlotPre s₀ a₀ dn vis fe M eb mode → HW hd → SpineR s₀.mem so sn xs →
    so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpecE p (N + 1) "iota_rec_at" [mode, vis, d, hd, so, sn]
      (iotaRecAt (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE hd) xs xs.size) s₀ a₀

/-- **What the `app` arm's errors assume** at L fuel `n` (`whnf_app`, `whnf_core_app2`,
`whnf_core_app`): the knot's slots' claims and `iota_rec_at`'s. -/
structure AppG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  iota : IotaRecAtE p

theorem AppG.mono {p : Prog} {n m : Nat} (h : AppG p n) (hm : m ≤ n) : AppG p m :=
  ⟨h.knot.mono hm, h.iota⟩

/-- The stack top put back after a run that kept the stack below it (the store's bound not
needed: `StackKept.restoreG'`). -/
theorem StackKept.restoreTop {m₀ m : Mem} (hb : ∀ j : Word, j < spTop m₀ → spW m j = spW m₀ j)
    (hle : spTop m₀ ≤ spTop m) (hsz : (m.arr64 SPN).size = (m₀.arr64 SPN).size) (hbk : BKept m₀ m)
    (hpg : PoolGrew m₀ m) : StackKept m₀ (m.set64 CTL 136 (spTop m₀)) :=
  StackKept.restoreG' ⟨hle, hsz, hb, hbk, hpg⟩

/-! ## `whnf_app` refines `whnfApp`, both outcomes -/

theorem apW_same {p : Prog} {k : Nat} {m : Mem} {v same aW nW : Word} (hs : same ≠ 0) :
    apW p k m v same aW nW = some (nW, m) := by
  simp [apW, hs]

section appRef
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)

include hp hwc hcc in
/-- **The `whnf_app` loop refines `whnfApp`, both outcomes**, by induction on the L fuel: its
errors are `iota_rec_at`'s (`AppG`). -/
theorem appLoop_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (mode vis d hd vo ao an top : Word) (args nodes : Array EIdx)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (eb : Word) (m₀ : Mem)
    (hmode : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hhd : HW hd)
    (har₀ : SpineR m₀ ao an args) (hno₀ : SpineR m₀ (ao + an) an nodes)
    (hlo : ao.toNat + an.toNat + an.toNat ≤ vo.toNat) (hvot : vo.toNat ≤ top.toNat)
    (htop0 : top = spTop m₀) (hspn0 : (m₀.arr64 SPN).size < 2 ^ 63) :
    ∀ (k : Nat), k ≤ n + 1 → ∀ (a : AState) (m : Mem) (v vn same i : Word) (va : Array EIdx)
      (MM : ModeMaps),
      CoreS dn m a vis fe MM eb → HW v → SpineR m vo vn va → spTop m = vo + vn →
      top.toNat ≤ (vo + vn).toNat → (∀ j : Word, j < top → spW m j = spW m₀ j) →
      (m.arr64 SPN).size = (m₀.arr64 SPN).size → BKept m₀ m → PoolGrew m₀ m →
      RefE (AppG p n)
        (whnfAppE.k_loop1 p top (whnfAppE.loop1 p k m mode vis d v hd vo vn same ao an i top))
        (whnfApp (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE v) (decE hd) va
          (same != 0) args nodes i.toNat) a (CorePost decStep dn m₀ vis fe MM eb ResW) := by
  sorry

include hp hwc hcc in
/-- **`whnf_app` refines `whnfApp`, both outcomes**: `vargs` the slice `(vo, vn)` at the top of the
stack, the spine's arguments and nodes the slices `(ao, an)`, `(ao + an, an)` below it. -/
theorem app_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d v hd vo vn same ao an i : Word)
    (vargs args nodes : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hv : HW v)
    (hhd : HW hd) (hva : SpineR s₀.mem vo vn vargs) (htop : spTop s₀.mem = vo + vn)
    (har : SpineR s₀.mem ao an args) (hno : SpineR s₀.mem (ao + an) an nodes)
    (hlo : ao.toNat + an.toNat + an.toNat ≤ vo.toNat) :
    RefE (AppG p n) (whnfAppE p (n + 1) s₀.mem mode vis d v hd vo vn same ao an i)
      (whnfApp (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE v) (decE hd) vargs
        (same != 0) args nodes i.toNat) a₀ (CorePost decStep dn s₀.mem vis fe MM eb ResW) := by
  have hS := hs.rel
  have hvn64 : vo.toNat + vn.toNat < 2 ^ 64 := by have := hva.bound; have := hS.spn; omega
  have hadd : (vo + vn).toNat = vo.toNat + vn.toNat := L.toNat_add_of_lt _ _ hvn64
  exact appLoop_ref p hp hwc hcc n hk F hF hn mode vis d hd vo ao an (spTop s₀.mem) args nodes dn fe
    eb s₀.mem hs.mode4 hs.eb_mode hhd har hno hlo (by rw [htop, hadd]; omega) rfl hS.spn (n + 1)
    (Nat.le_refl _) a₀ s₀.mem v vn same i vargs MM hS hv hva htop (by rw [htop]; exact Nat.le_refl _)
    (fun _ _ => rfl) rfl (BKept.refl _) (PoolGrew.refl _)

include hp hwc hcc in
/-- **`whnf_app` refines `whnfApp`** (`app_ref`'s ok half). -/
theorem whnfApp_refines' (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d v hd vo vn same ao an i : Word)
    (vargs args nodes : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hv : HW v)
    (hhd : HW hd) (hva : SpineR s₀.mem vo vn vargs) (htop : spTop s₀.mem = vo + vn)
    (har : SpineR s₀.mem ao an args) (hno : SpineR s₀.mem (ao + an) an nodes)
    (hlo : ao.toNat + an.toNat + an.toNat ≤ vo.toNat) :
    CoreSpec p (n + 1) "whnf_app" [mode, vis, d, v, hd, vo, vn, same, ao, an, i]
      (whnfApp (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE v) (decE hd) vargs
        (same != 0) args nodes i.toNat) decStep s₀ a₀ dn vis fe MM eb ResW :=
  RefE.coreSpec (whnfAppE_spec p hp.app (n + 1) s₀ mode vis d v hd vo vn same ao an i)
    (app_ref p hp hwc hcc n hk F hF hn s₀ a₀ dn vis fe MM eb mode d v hd vo vn same ao an i vargs args
      nodes hs hv hhd hva htop har hno hlo)

end appRef

end L.Arena
