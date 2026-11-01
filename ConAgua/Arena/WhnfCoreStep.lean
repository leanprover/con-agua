module

public import ConAgua.Arena.WhnfCoreAppLoop
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.WhnfCoreRefine

@[expose] public section

/-!
# `whnf_core_step` and its `app` arm refine `whnfCoreStep`

The step dispatches on the handle's tag after the view's checks; the `app` arm (`whnf_core_app`,
`WhnfCore.lean`) walks the spine (`get_app_spine`), normalises the head (the knot's `whnfCore`
slot), takes the reduct's own spine (`head_and_args`) and runs the batched β/ι walk (`whnf_app`),
then puts the stack top back. Twin: `whnfCoreStep` (`Arena/Core.lean:2351`), its `.app` clause
named `whnfCoreAppT` here. One refinement each over the unified models (`capp2_ref`, `capp_ref`),
both outcomes.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The `app` arm -/

/-- The twin's `.app` clause of `whnfCoreStep`. -/
def whnfCoreAppT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool) (depth : Nat)
    (e : EIdx) : AM WhnfStep := do
  let sp ← getAppSpine coreWalkFuel e
  let v ← r.whnfCore cheap depth sp.1
  let same := v == sp.1
  let hv ← headAndArgs v
  whnfApp mode r fe depth v hv.1 hv.2 same sp.2.1 sp.2.2 0

theorem whnfCoreAppT_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool)
    (depth : Nat) (e : EIdx) :
    whnfCoreAppT mode r fe cheap depth e = (do
      let sp ← getAppSpine coreWalkFuel e
      let v ← r.whnfCore cheap depth sp.1
      whnfCoreApp2T mode r fe depth v sp.1 sp.2.1 sp.2.2) := rfl

section app
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)

include hp hwc hcc in
/-- **`whnf_core_app2` refines the second half of the `.app` clause, both outcomes**, the spine's
arguments and nodes the slices `(so, sn)`, `(so + sn, sn)` below the top: the errors are
`whnf_app`'s. `head_and_args` leaves its slice on the stack; the top is put back without its
bound (`GrowPost.restore`). -/
theorem capp2_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d v h so sn : Word) (args nodes : Array EIdx)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hv : HW v) (hh : HW h)
    (har : SpineR s₀.mem so sn args) (hno : SpineR s₀.mem (so + sn) sn nodes)
    (hlo : so.toNat + sn.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (htop : (spTop s₀.mem).toNat ≤ (s₀.mem.arr64 SPN).size) :
    RefE (AppG p n) (coreApp2E p (n + 2) s₀.mem mode vis d v h so sn)
      (whnfCoreApp2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v) (decE h)
        args nodes) a₀ (CorePost decStep dn s₀.mem vis fe MM eb ResW) := by
  have hS := hs.rel
  simp only [coreApp2E]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₃ m₃ h3 => ?_
  simp only [coreApp2E.k_head_and_args]
  obtain ⟨t₃, ht₃, -, hf₃, hg₃, hhw, ho3, htop3, xs, hha, hxs⟩ := triple_of_callW
    (headAndArgs_refines p hp.spine (n + 1) ⟨s₀.mem, Locals.init []⟩ a₀ hS.arena.base v hv hS.spn htop) h3
  rw [ht₃] at hf₃ hg₃ htop3 hxs
  have hS₃ := hS.frame_stk hf₃ (by simp) (by simp)
  have har₃ := har.keep hg₃.size hg₃.below (by omega) hS.spn
  have hno₃ := hno.keep hg₃.size hg₃.below (by
    have hb := har.bound; have := hS.spn
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega) hS.spn
  have hvo : spTop m₃ = r₃.tail.headD 0 + r₃.tail.tail.headD 0 := by rw [htop3, ho3]
  unfold whnfCoreApp2T
  refine RefE.bind_right hha ?_
  have h4 := app_ref p hp hwc hcc n hk F hF hn ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode d v
    (r₃.headD 0) (r₃.tail.headD 0) (r₃.tail.tail.headD 0) (if v = h then 1 else 0) so sn 0 xs args
    nodes ⟨hS₃, hs.mode4, hs.eb_mode⟩ hv hhw hxs hvo har₃ hno₃ (by rw [ho3]; omega)
  have hsame : ((if v = h then (1 : Word) else 0) != 0) = (decE v == decE h) := by
    rw [← evalW_eq_ne v h hv hh]; simp [Cmp.evalW, Cmp.eval]
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [hsame, h0] at h4
  refine RefE.lastE (K := coreApp2E.k_whnf_app p _) (fun _ => rfl) (fun _ => rfl) id h4
    fun ⟨r₄, m₄⟩ y a' _ hP => ?_
  obtain ⟨M', hS₄, hK₄, hSt₄⟩ := hP.after
  exact (⟨⟨M', hS₄, hK₄, hg₃.trans hSt₄.toGrew⟩, hP.res, hP.valid⟩ :
    GrowPost decStep dn s₀.mem vis fe MM eb ResW (r₄, m₄) y a').restore _ rfl hP.valid

include hp hwc hcc in
/-- **`whnf_core_app2` refines the second half of the `.app` clause** (`capp2_ref`'s ok half). -/
theorem coreApp2_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d v h so sn : Word) (args nodes : Array EIdx)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hv : HW v) (hh : HW h)
    (har : SpineR s₀.mem so sn args) (hno : SpineR s₀.mem (so + sn) sn nodes)
    (hlo : so.toNat + sn.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (htop : (spTop s₀.mem).toNat ≤ (s₀.mem.arr64 SPN).size) :
    CoreSpec p (n + 2) "whnf_core_app2" [mode, vis, d, v, h, so, sn]
      (whnfCoreApp2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v) (decE h)
        args nodes) decStep s₀ a₀ dn vis fe MM eb ResW :=
  RefE.coreSpec (coreApp2E_spec p hp.capp2 hp.app (n + 2) s₀ mode vis d v h so sn)
    (capp2_ref p hp hwc hcc n hk F hF hn s₀ a₀ dn vis fe MM eb mode d v h so sn args nodes hs hv hh har
      hno hlo htop)

include hp hwc hcc in
/-- **`whnf_core_app` refines the `.app` clause of `whnfCoreStep` (`whnfCoreAppT`), both
outcomes**: the errors are the head's `whnf_core` slot's and `whnf_core_app2`'s. -/
theorem capp_ref (N : Nat) (hk : KnotUpTo p N) (F : Nat) (hF : N ≤ F) (hn : N ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode cheap d e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    RefE (AppG p N) (coreAppE p (N + 1) s₀.mem mode cheap vis d e)
      (whnfCoreAppT (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat (decE e))
      a₀ (CorePost decStep dn s₀.mem vis fe MM eb ResW) := by
  have hS := hs.rel
  simp only [coreAppE]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₁ m₁ h1 => ?_
  simp only [coreAppE.k_get_app_spine]
  obtain ⟨t₁, ht₁, -, hf₁, hg₁, hhw, ho1, htop1, xs, ns, hsp, hxs, hns⟩ := triple_of_callW
    (getAppSpine_refines p hp.spine N ⟨s₀.mem, Locals.init []⟩ a₀ hS.arena.base e he hS.spn) h1
  rw [ht₁] at hf₁ hg₁ htop1 hxs hns
  have hS₁ := hS.frame_stk hf₁ (by simp) (by simp)
  rw [whnfCoreAppT_eq]
  refine RefE.bind_right hsp ?_
  refine RefE.bind_callE (s₀ := ⟨m₁, Locals.init []⟩)
    (x := fun c => coreAppE.k_whnf_core p N mode vis d (rdW (s₀.mem.arr64 CTL) 136) (r₁.headD 0)
      (r₁.tail.headD 0) (r₁.tail.tail.headD 0) c) (fun _ => rfl)
    ((hk N (Nat.le_refl _)).whnfCore F _ a₀ dn vis fe MM eb mode cheap d (r₁.headD 0) hF hn
      ⟨hS₁, hs.mode4, hs.eb_mode⟩ hhw)
    (fun hG => (hG.knot N (Nat.le_refl _)).whnfCore F _ a₀ dn vis fe MM eb mode cheap d (r₁.headD 0)
      hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hhw) (fun r₂ m₂ _ h2 => ?_)
  obtain ⟨-, ⟨M', hS₂, hK₂, hSt₂⟩, -, hrw₂⟩ := h2
  simp only [coreAppE.k_whnf_core]
  cases N with
  | zero => rw [callW_zero] at h1; cases h1
  | succ N =>
  cases N with
  | zero =>
    simp only [coreApp2E, callW_zero, liftE_none, coreApp2E.k_head_and_args,
      coreAppE.k_whnf_core_app2]
    exact RefE.of_cls0 (by simp)
  | succ n' =>
  rw [show n' + 1 + 1 = n' + 2 from rfl]
  have hspn₁ : (m₁.arr64 SPN).size < 2 ^ 63 := hS₁.spn
  have hb1 := hxs.bound
  have hb2 := hns.bound
  have e1 : (r₁.tail.headD 0 + r₁.tail.tail.headD 0).toNat =
      (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat := addW _ _ (by omega)
  rw [e1] at hb2
  have htopN : (spTop m₁).toNat = (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat +
      (r₁.tail.tail.headD 0).toNat := by
    rw [htop1, ← ho1, addW _ _ (by rw [e1]; omega), e1]
  have hxs₂ := hxs.keep hSt₂.size hSt₂.below (by omega) hspn₁
  have hns₂ := hns.keep hSt₂.size hSt₂.below (by rw [e1]; omega) hspn₁
  have h4 := capp2_ref p hp hwc hcc n' (hk.mono (by omega)) F (by omega) (by omega)
    ⟨m₂, Locals.init []⟩ _ dn vis fe M' eb mode d (r₂.headD 0) (r₁.headD 0) (r₁.tail.headD 0)
    (r₁.tail.tail.headD 0) xs ns ⟨hS₂, hs.mode4, hs.eb_mode⟩ hrw₂ hhw hxs₂ hns₂
    (by have h22 := hSt₂.1; simp only at h22 ⊢; rw [h22]; omega)
    (by show (spTop m₂).toNat ≤ (m₂.arr64 SPN).size
        have a := hSt₂.1; have b := hSt₂.size; simp only at a b; rw [a, b]; omega)
  refine RefE.lastE (K := coreAppE.k_whnf_core_app2 p _) (fun _ => rfl) (fun _ => rfl)
    (·.mono (by omega)) h4 fun ⟨r₄, m₄⟩ y a' _ hP => ?_
  obtain ⟨M'', hS₄, hK₄, hSt₄⟩ := hP.after
  exact (⟨⟨M'', hS₄, hK₂.trans hK₄, (hg₁.trans hSt₂.toGrew).trans hSt₄.toGrew⟩, hP.res, hP.valid⟩ :
    GrowPost decStep dn s₀.mem vis fe MM eb ResW (r₄, m₄) y a').restore _ rfl hP.valid

include hp hwc hcc in
/-- **`whnf_core_app` refines the `.app` clause of `whnfCoreStep`** (`capp_ref`'s ok half). -/
theorem coreApp_refines (N : Nat) (hk : KnotUpTo p N) (F : Nat) (hF : N ≤ F) (hn : N ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode cheap d e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpec p (N + 1) "whnf_core_app" [mode, cheap, vis, d, e]
      (whnfCoreAppT (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat (decE e))
      decStep s₀ a₀ dn vis fe MM eb ResW :=
  RefE.coreSpec (coreAppE_spec p hp.capp hp.capp2 hp.app (N + 1) s₀ mode cheap vis d e)
    (capp_ref p hp hwc hcc N hk F hF hn s₀ a₀ dn vis fe MM eb mode cheap d e hs he)

end app

end L.Arena
