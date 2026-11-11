module

public import ConAgua.Arena.RecCheckSpec.PtrNamesWDec
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.RecClassSpec.CloseLams
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.RecSim
import all ConAgua.Arena.RecCheck
import ConAgua.L.ModelGen

@[expose] public section

/-!
# TargetMajorAt2: `ConRon.Arena.targetMajorAt`

The refinement theorems `targetMajorAt_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `target_major_at` -/

/-- **`target_major_at` is its model `tmaW`** (generated): the hit a read, the miss
`target_major_default`. -/
l_model targetMajorAt_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hpw : p.lookup "pin_word" = some pinWordL) (hm : p.lookup "mk_target_major" = some mkTargetMajor)
    (hd : p.lookup "target_major_default" = some targetMajorDefault)
    (hp : p.lookup "target_major_at" = some targetMajorAt) (hna : NaF p)
  fns [hp ↦ tmaW list]
  specs [targetMajorDefault_spec p ha hpw hm hd hna n]
  grind [arena_grind]

/-- The decoded result of `target_major_at`. -/
def decTM0 (m' : Mem) (r : List Word) (x : TargetMajor) : Prop := decTM m' (r.headD 0).toNat = some x

theorem tmaW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem)
    (a : AState) (mo ml c : Word) (ms : List TargetMajor) (hS : StageR vis fe m a)
    (hms : decPL m (decTM m) mo.toNat ml.toNat = some ms) (_hb : mo.toNat + ml.toNat < 2 ^ 64) :
    RSim (tmaW m mo ml c) (ConRon.Arena.targetMajorAt ms c.toNat) a (KP vis fe m decTM0) := by
  by_cases hc : c < ml
  · rw [tmaW.arm1 m mo ml c hc]
    have hc' : c.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hc
    obtain ⟨v, hv, hdec⟩ := decPL_getH m hms c.toNat hc'
    have hlen := decPL_length m hms
    have hrd := iwN_rdW_at (w := mo) (k := c.toNat) hv hS.iw.iwSize
    have hcw : mo + UInt64.ofNat c.toNat = mo + c := by simp
    rw [hcw] at hrd
    have hop : ConRon.Arena.targetMajorAt ms c.toNat = pure (ms[c.toNat]'(by omega)) := by
      simp [ConRon.Arena.targetMajorAt, List.getElem?_eq_getElem (by omega : c.toNat < ms.length)]
    rw [hop]
    refine RSim.pure_some ⟨hS, IWGrow.refl m, ?_⟩
    show decTM m (rdW (m.arr64 IW) (mo + c)).toNat = _
    rw [hrd.1, UInt64.toNat_ofNat_of_lt' hrd.2]; exact hdec
  · rw [tmaW.arm2 m mo ml c hc]
    have hc' : ¬ c.toNat < ml.toNat := fun h => hc (UInt64.lt_iff_toNat_lt.mpr h)
    have hlen := decPL_length m hms
    have hop : ConRon.Arena.targetMajorAt ms c.toNat = ConRon.Arena.targetMajorDefault := by
      simp [ConRon.Arena.targetMajorAt, List.getElem?_eq_none (by omega : ms.length ≤ c.toNat)]
    rw [hop]
    rintro ⟨r, m'⟩ h
    rw [tmaW.k_target_major_default.eq_def] at h
    rcases ho : tmdW m with _ | ⟨r0, m0⟩ <;> rw [ho] at h
    · cases h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨tm, a', hrun, hS', hg, hd⟩ := tmdW_ok dn vis fe m m0 a r0 ho hS
    exact ⟨tm, a', hrun, hS', hg, hd⟩

/-- **`target_major_at` refines `targetMajorAt`** (the hit arm a read, the miss arm
`target_major_default`). -/
@[refines ConRon.Arena.targetMajorAt]
theorem targetMajorAt_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hpw : p.lookup "pin_word" = some pinWordL) (hm : p.lookup "mk_target_major" = some mkTargetMajor)
    (hd : p.lookup "target_major_default" = some targetMajorDefault)
    (hp : p.lookup "target_major_at" = some targetMajorAt) (hna : NaF p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mo ml c : Word)
    (ms : List TargetMajor) (hS : StageR vis fe s₀.mem a₀)
    (hms : decPL s₀.mem (decTM s₀.mem) mo.toNat ml.toNat = some ms) (hb : mo.toNat + ml.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_at" [mo, ml, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetMajorAt ms c.toNat) a₀ ∧
      KP vis fe s₀.mem decTM0 (r, s'.mem) (AM.st (ConRon.Arena.targetMajorAt ms c.toNat) a₀)
        (AM.res (ConRon.Arena.targetMajorAt ms c.toNat) a₀); ⊤⦄ :=
  triple_post (targetMajorAt_spec p ha hpw hm hd hp hna n s₀ mo ml c) fun _ _ ⟨hl, hw⟩ =>
    ⟨hl, (tmaW_sim dn vis fe _ a₀ mo ml c ms hS hms hb).am hw⟩

end L.Ind

end
