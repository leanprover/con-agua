import ConAgua.Arena.WhnfCoreAppLoop
import ConAgua.L.ModelGen

/-!
# `whnf_core_step` and its `app` arm refine `whnfCoreStep`

The step dispatches on the handle's tag after the view's checks; the `app` arm (`whnf_core_app`,
`WhnfCore.lean`) walks the spine (`get_app_spine`), normalises the head (the knot's `whnfCore`
slot), takes the reduct's own spine (`head_and_args`) and runs the batched β/ι walk (`whnf_app`),
then puts the stack top back. Twin: `whnfCoreStep` (`Arena/Core.lean:2351`), its `.app` clause
named `whnfCoreAppT` here.
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

/-- **`whnf_core_app2` is its model `coreApp2W`** (generated). -/
l_model coreApp2_spec (p : Prog) (hp : p.lookup "whnf_core_app2" = some whnfCoreApp2L)
  fns [hp ↦ coreApp2W tuple]
  specs [callW_spec p n "head_and_args", callW_spec p n "whnf_app"]
  grind [arena_grind] finish [St.setLocs_mem'] gen 20 heartbeats 1000000
  sym "(gen := 80) (instances := 5000)"

/-- **`whnf_core_app` is its model `coreAppW`** (generated). -/
l_model coreApp_spec (p : Prog) (hp : p.lookup "whnf_core_app" = some whnfCoreAppL)
  fns [hp ↦ coreAppW tuple]
  specs [callW_spec p n "get_app_spine", callW_spec p n "whnf_core", callW_spec p n "whnf_core_app2"]
  grind [arena_grind] finish [St.setLocs_mem'] gen 20 heartbeats 1000000
  sym "(gen := 80) (instances := 5000)"

/-- `StackKept.restore` without the bound on `CTL`: out of bounds the store is void and the top
reads `0`, so a top that did not drop is kept. -/
theorem StackKept.restore' {m m₁ : Mem} (hk : ∀ i : Word, i < spTop m → spW m₁ i = spW m i)
    (hsz : (m₁.arr64 SPN).size = (m.arr64 SPN).size) (hb : BKept m m₁) (hp : PoolGrew m m₁)
    (ht : spTop m ≤ spTop m₁) : StackKept m (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) := by
  by_cases h136 : (136 : Word).toNat < (m₁.arr64 CTL).size
  · exact StackKept.restore hk hsz hb hp h136
  have hfs := MemFrame.setCtl m₁ 136 (rdW (m.arr64 CTL) 136)
  have hspn : (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)).arr64 SPN = m₁.arr64 SPN :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨?_, by rw [hspn, hsz], fun i hi => by simp only [spW, hspn]; exact hk i hi,
    hb.trans (BKept.of_frame hfs (by decide) (by decide)),
    hp.trans (PoolGrew.of_frame hfs (by decide) (by decide))⟩
  have h0 : spTop m₁ = 0 := by simp only [spTop, rdW]; rw [Array.getElem?_eq_none (by omega)]; rfl
  have e : spTop (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) = spTop m₁ := by
    simp only [spTop, rdW_set64, h136, and_false, ↓reduceIte]
  rw [e, h0]; rw [h0] at ht
  exact (UInt64.le_antisymm ht UInt64.zero_le).symm

/-! ## `whnf_core_app2` refines the reduct's spine and the β/ι walk -/

section app2
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)

include hp hwc hcc in
/-- **`whnf_core_app2` refines the second half of the `.app` clause**, the spine's arguments and
nodes the slices `(so, sn)`, `(so + sn, sn)` below the top. -/
theorem coreApp2_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d v h so sn : Word) (args nodes : Array EIdx)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hv : HW v) (hh : HW h)
    (har : SpineR s₀.mem so sn args) (hno : SpineR s₀.mem (so + sn) sn nodes)
    (hlo : so.toNat + sn.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (htop : (spTop s₀.mem).toNat ≤ (s₀.mem.arr64 SPN).size) :
    CoreSpec p (n + 2) "whnf_core_app2" [mode, vis, d, v, h, so, sn]
      (whnfCoreApp2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v) (decE h)
        args nodes) decStep s₀ a₀ dn vis fe MM eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (coreApp2_spec p hp.capp2 (n + 2) s₀ mode vis d v h so sn)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  rw [coreApp2W.arm1] at hW
  cases h3 : callW p (n + 1) "head_and_args" [v] s.mem with
  | none => rw [h3, coreApp2W.k_head_and_args.none] at hW; cases hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  simp only [h3, coreApp2W.k_head_and_args] at hW
  rw [show (if v = h then (1 : Word) else 0) = Cmp.evalW .eq v h by simp [Cmp.evalW, Cmp.eval]] at hW
  cases h4 : callW p (n + 1) "whnf_app" [mode, vis, d, v, r₃.headD 0, r₃.tail.headD 0,
      r₃.tail.tail.headD 0, Cmp.evalW .eq v h, so, sn, 0] m₃ with
  | none => rw [h4, coreApp2W.k_whnf_app.none] at hW; cases hW
  | some q =>
  obtain ⟨r₄, m₄⟩ := q
  simp only [h4, coreApp2W.k_whnf_app, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  obtain ⟨t₃, ht₃, -, hf₃, hg₃, hhw, ho3, htop3, xs, hha, hxs⟩ := triple_of_callW
    (headAndArgs_refines p hp.spine (n + 1) s a₀ hS.arena.1 v hv hS.spn htop) h3
  rw [ht₃] at hf₃ hg₃ htop3 hxs
  have hS₃ := hS.frame_stk hf₃ (by simp) (by simp)
  obtain ⟨hgt, hgsz, hgk, hgb, hgp⟩ := hg₃
  have har₃ := har.keep hgsz hgk (by omega) hS.spn
  have hno₃ := hno.keep hgsz hgk (by
    have hb := har.bound; have := hS.spn
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega) hS.spn
  have hvo : spTop m₃ = r₃.tail.headD 0 + r₃.tail.tail.headD 0 := by rw [htop3, ho3]
  have hwapp := whnfApp_refines' p hp hwc hcc n hk F hF hn ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode d v
    (r₃.headD 0) (r₃.tail.headD 0) (r₃.tail.tail.headD 0) (Cmp.evalW .eq v h) so sn 0 xs args nodes
    ⟨hS₃, hs.mode4, hs.eb_mode⟩ hv hhw hxs hvo har₃ hno₃ (by rw [ho3]; omega)
  obtain ⟨hok, ⟨M', hS₄, hK₄, hSt₄⟩, hres, hrw⟩ := CoreSpec.of_callW hwapp h4
  rw [evalW_eq_ne v h hv hh] at hok hres hS₄
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [h0] at hok hres hS₄
  have hrun₁ : (whnfCoreApp2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v)
      (decE h) args nodes).run a₀ = (whnfApp (decMode mode) (coreKnot (decMode mode) fe id F) fe
        d.toNat (decE v) (decE (r₃.headD 0)) xs (decE v == decE h) args nodes 0).run a₀ := by
    simp only [whnfCoreApp2T, StateT.run_bind, hha, except_ok_bind]
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ (by rw [hrun₁]; exact AM.run_of_ok _ _ hok)
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst', ← hm]
    refine ⟨M', hS₄.frame_stk (MemFrame.setCtl m₄ 136 _) (by simp) (by simp), hK₄, ?_⟩
    apply StackKept.restore' _ (by rw [hSt₄.size, hgsz]) (hgb.trans hSt₄.bstk) (hgp.trans hSt₄.pool)
      (by rw [hSt₄.top]; exact hgt)
    intro i hi
    rw [hSt₄.below i (UInt64.lt_of_lt_of_le hi hgt)]; exact hgk i hi
  · rw [hres', hres]; simp only [decStep, hr0, hr1]
  · exact ⟨hr0 ▸ hrw.1, hr1 ▸ hrw.2⟩

end app2

/-! ## `whnf_core_app` refines the `.app` clause -/

theorem whnfCoreAppT_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool)
    (depth : Nat) (e : EIdx) :
    whnfCoreAppT mode r fe cheap depth e = (do
      let sp ← getAppSpine coreWalkFuel e
      let v ← r.whnfCore cheap depth sp.1
      whnfCoreApp2T mode r fe depth v sp.1 sp.2.1 sp.2.2) := rfl

section app
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)

include hp hwc hcc in
/-- **`whnf_core_app` refines the `.app` clause of `whnfCoreStep`** (`whnfCoreAppT`). -/
theorem coreApp_refines (N : Nat) (hk : KnotUpTo p N) (F : Nat) (hF : N ≤ F) (hn : N ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode cheap d e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpec p (N + 1) "whnf_core_app" [mode, cheap, vis, d, e]
      (whnfCoreAppT (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat (decE e))
      decStep s₀ a₀ dn vis fe MM eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (coreApp_spec p hp.capp (N + 1) s₀ mode cheap vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  rw [coreAppW.arm1] at hW
  cases h1 : callW p N "get_app_spine" [e] s.mem with
  | none => rw [h1, coreAppW.k_get_app_spine.none] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  simp only [h1, coreAppW.k_get_app_spine] at hW
  cases h2 : callW p N "whnf_core" [mode, cheap, vis, d, r₁.headD 0] m₁ with
  | none => rw [h2, coreAppW.k_whnf_core.none] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  simp only [h2, coreAppW.k_whnf_core] at hW
  cases h4 : callW p N "whnf_core_app2" [mode, vis, d, r₂.headD 0, r₁.headD 0, r₁.tail.headD 0,
      r₁.tail.tail.headD 0] m₂ with
  | none => rw [h4, coreAppW.k_whnf_core_app2.none] at hW; cases hW
  | some q =>
  obtain ⟨r₄, m₄⟩ := q
  simp only [h4, coreAppW.k_whnf_core_app2, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  -- the spine
  obtain ⟨t₁, ht₁, -, hf₁, hg₁, hhw, ho1, htop1, xs, ns, hsp, hxs, hns⟩ := triple_of_callW
    (getAppSpine_refines p hp.spine N s a₀ hS.arena.1 e he hS.spn) h1
  rw [ht₁] at hf₁ hg₁ htop1 hxs hns
  have hS₁ := hS.frame_stk hf₁ (by simp) (by simp)
  obtain ⟨hgt, hgsz, hgk, hgb, hgp⟩ := hg₁
  -- the head
  have hslot := (hk N (Nat.le_refl _)).whnfCore F ⟨m₁, Locals.init []⟩ a₀ dn vis fe MM eb mode cheap
    d (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hhw
  obtain ⟨hok₂, ⟨M', hS₂, hK₂, hSt₂⟩, hres₂, hrw₂⟩ := CoreSpec.of_callW hslot h2
  -- the second half
  cases N with
  | zero => simp [callW_zero] at h1
  | succ N =>
  cases N with
  | zero =>
    obtain ⟨t, -, -, hz⟩ := triple_of_callW (coreApp2_spec p hp.capp2 1 ⟨m₂, Locals.init []⟩
      mode vis d (r₂.headD 0) (r₁.headD 0) (r₁.tail.headD 0) (r₁.tail.tail.headD 0)) h4
    rw [coreApp2W.arm1, callW_zero, coreApp2W.k_head_and_args.none] at hz; cases hz
  | succ n' =>
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
  have happ := coreApp2_refines p hp hwc hcc n' (hk.mono (by omega)) F (by omega) (by omega)
    ⟨m₂, Locals.init []⟩ _ dn vis fe M' eb mode d (r₂.headD 0) (r₁.headD 0) (r₁.tail.headD 0)
    (r₁.tail.tail.headD 0) xs ns ⟨hS₂, hs.mode4, hs.eb_mode⟩ hrw₂ hhw hxs₂ hns₂
    (by have h22 := hSt₂.1; simp only at h22 ⊢; rw [h22]; omega)
    (by show (spTop m₂).toNat ≤ (m₂.arr64 SPN).size
        have a := hSt₂.1; have b := hSt₂.size; simp only at a b; rw [a, b]; omega)
  obtain ⟨hok₄, ⟨M'', hS₄, hK₄, hSt₄⟩, hres₄, hrw₄⟩ := CoreSpec.of_callW happ h4
  have hrun : (whnfCoreAppT (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
      (decE e)).run a₀ = .ok (AM.res (whnfCoreApp2T (decMode mode)
        (coreKnot (decMode mode) fe id F) fe d.toNat (decE (r₂.headD 0)) (decE (r₁.headD 0)) xs ns)
        (AM.st ((coreKnot (decMode mode) fe id F).whnfCore (cheap != 0) d.toNat (decE (r₁.headD 0)))
          a₀), AM.st (whnfCoreApp2T (decMode mode)
        (coreKnot (decMode mode) fe id F) fe d.toNat (decE (r₂.headD 0)) (decE (r₁.headD 0)) xs ns)
        (AM.st ((coreKnot (decMode mode) fe id F).whnfCore (cheap != 0) d.toNat (decE (r₁.headD 0)))
          a₀)) := by
    rw [whnfCoreAppT_eq]
    simp only [StateT.run_bind, hsp, except_ok_bind, AM.run_of_ok _ _ hok₂]
    rw [hres₂]
    exact AM.run_of_ok _ _ hok₄
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst', ← hm]
    refine ⟨M'', hS₄.frame_stk (MemFrame.setCtl m₄ 136 _) (by simp) (by simp), hK₂.trans hK₄, ?_⟩
    have h22 := hSt₂.1
    simp only at h22
    apply StackKept.restore' _ (by rw [hSt₄.size, hSt₂.size, hgsz]) ((hgb.trans hSt₂.bstk).trans hSt₄.bstk)
      ((hgp.trans hSt₂.pool).trans hSt₄.pool) (by rw [hSt₄.top, h22]; exact hgt)
    intro i hi
    have hi1 : i < spTop m₁ := UInt64.lt_of_lt_of_le hi hgt
    rw [hSt₄.below i (by rw [h22]; exact hi1), hSt₂.below i hi1, hgk i hi]
  · rw [hres', hres₄]; simp only [decStep, hr0, hr1]
  · exact ⟨hr0 ▸ hrw₄.1, hr1 ▸ hrw₄.2⟩

end app

end L.Arena
