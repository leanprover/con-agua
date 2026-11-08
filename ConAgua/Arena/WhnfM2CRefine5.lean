module

import ConAgua.Arena.WhnfM2CRefine4
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.WhnfIotaRefine6
import ConAgua.Arena.WhnfM2CRefine3
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.WhnfM2CRefine2

@[expose] public section

/-!
# `major_to_ctor`: the dispatch (`m2c_arms`), the family (`m2c_ctor`), the header (`m2c_head`)
and `major_to_ctor` itself
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Record words -/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- A rule record's `ctor`, `k` and `eta` words. -/
theorem decRule_words (a : Array Word) (q : Nat) (rl : IRecRule) (h : decRule (aread a) q = some rl) :
    (∃ w, a[q]? = some w ∧ w.toNat < 2 ^ 32 ∧ rl.ctor = decI w) ∧
    (∃ w, a[q + 9]? = some w ∧ rl.k = (w != 0)) ∧ ∃ w, a[q + 10]? = some w ∧ rl.eta = (w != 0) := by
  sorry

-/

/-- A constructor record's kind, level-parameter count, type and parameter count words. -/
theorem decCI_ctor_words (b : Array Word) (dn : NIdx → Option ConLeche.Name) (q : Nat)
    (cv : IConstantVal) (nP nF : Nat) (h : decCI (aread b) q = some (.ctorInfo cv nP nF)) :
    (∃ w, b[q]? = some w ∧ w = 4) ∧ (∃ w, b[q + 3]? = some w ∧ cv.levelParams.length = w.toNat) ∧
    (∃ w, b[q + 4]? = some w ∧ w.toNat < 2 ^ 32 ∧ cv.type = decI w) ∧
    (∃ w, b[q + 5]? = some w ∧ nP = w.toNat) := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  match k, h with
  | 0, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 1, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 2, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 3, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 5, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 6, h => simp_all []
  | (_ + 7), h => simp_all
  | 4, h =>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv', hcv, np', hnp, nf', -, h3⟩ := h
    simp only [IConstantInfo.ctorInfo.injEq] at h3
    obtain ⟨rfl, rfl, rfl⟩ := h3
    obtain ⟨w0, e0, k0⟩ := nat?_some hk
    obtain ⟨w5, e5, rfl⟩ := nat?_some hnp
    simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff] at hcv
    obtain ⟨nm, -, ls, hls, ty, hty, hc⟩ := hcv
    cases hc
    obtain ⟨o, c, -, hc3, hs⟩ := hlist?_slice hls
    obtain ⟨w4, e4, l4, rfl⟩ := hd?_eq hty
    refine ⟨⟨w0, e0, UInt64.toNat_inj.mp (by rw [k0]; rfl)⟩, ⟨c, by simpa [Nat.add_assoc] using hc3,
      hslice?_length hs⟩, ⟨w4, by simpa [Nat.add_assoc] using e4, l4, rfl⟩, ⟨w5, e5, rfl⟩⟩

/-- The kind word of a decoded record says whether it is an inductive or a constructor. -/
theorem decCI_kind34 (b : Array Word) (dn : NIdx → Option ConLeche.Name) (q : Nat)
    (ci : IConstantInfo) (h : decCI (aread b) q = some ci) :
    ∃ w, b[q]? = some w ∧ ((∃ cv caps, ci = .indInfo cv caps) ↔ w = 3) ∧
      ((∃ cv nP nF, ci = .ctorInfo cv nP nF) ↔ w = 4) := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  obtain ⟨w, ew, kw⟩ := nat?_some hk
  have e3 : w = 3 ↔ k = 3 :=
    ⟨fun e => by rw [← kw, e]; rfl, fun e => UInt64.toNat_inj.mp (by rw [kw, e]; rfl)⟩
  have e4 : w = 4 ↔ k = 4 :=
    ⟨fun e => by rw [← kw, e]; rfl, fun e => UInt64.toNat_inj.mp (by rw [kw, e]; rfl)⟩
  refine ⟨w, ew, ?_⟩
  rw [e3, e4]
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  all_goals grind

/-- A word at `q + k` of a record, as `rdW`. -/
theorem rdW_rec {b : Array Word} {q : Word} {k : Nat} {w : Word} (hb : b[q.toNat + k]? = some w)
    (hk : k < 2 ^ 32) (hsz : b.size < 2 ^ 63) : rdW b (q + k.toUInt64) = w :=
  rdW_off' hb (by simp; omega) hsz

section top
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hpi : ProofIrrelOKM p)
  (hE : ErecKeptKnot p) (hcc : ProjCallees p)
include hp hc hpi hE hcc

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`m2c_arms` refines `m2cArmsT`, both outcomes** (the errors are the arm's). -/
theorem m2cArms_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ro cvjP T indP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hT : HW T) (hmaj : HW major) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat)
    (cvT : IConstantVal) (caps : IIndCaps) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hrl : decRule (erecP m) ro.toNat = some rl)
    (hcj : decCI (erecP m) cvjP.toNat = some (.ctorInfo cvj cnP cnF))
    (hci : decCI (erecP m) indP.toNat = some (.indInfo cvT caps))
    (hfe : ∃ c, fe.find? c = some (.indInfo cvT caps)) :
    RefE (M2CCtxE p N) (m2cArmsE p (N + 1) m mode vis d ro cvjP T indP major)
      (m2cArmsT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat rl cvj cnP (decI T)
        cvT caps (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`m2c_ctor` refines `m2cCtorT`, both outcomes** (the errors are `m2c_arms`'). -/
theorem m2cCtor_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ro cvjP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hmaj : HW major) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (hrl : decRule (erecP m) ro.toNat = some rl)
    (hcj : decCI (erecP m) cvjP.toNat = some (.ctorInfo cvj cnP cnF)) :
    RefE (M2CCtxE p N) (m2cCtorE p (N + 1) m mode vis d ro cvjP major)
      (m2cCtorT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat rl cvj cnP
        (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`m2c_head` refines `m2cHeadT`, both outcomes** (the errors are `m2c_ctor`'s). -/
theorem m2cHead_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ro rc major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hmaj : HW major) (rules : List IRecRule) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hr : decRules (erecP m) ro.toNat rc.toNat = some rules) :
    RefE (M2CCtxE p N) (m2cHeadE p (N + 1) m mode vis d ro rc major)
      (m2cHeadT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat rules
        (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`major_to_ctor` refines `majorToCtor`, both outcomes** (the top put back): `m2c_head`'s
(`m2cHead_ref`). -/
theorem mtc_ref (n F : Nat) (hk : KnotUpTo p n) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode d rec ro rc major : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hmaj : HW major) (rules : List IRecRule)
    (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (hr : decRules (erecP m) ro.toNat rc.toNat = some rules) :
    RefE (M2CCtxE p n) (mtcE p (n + 1) m mode vis d rec ro rc major)
      (majorToCtor (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec) rules
        (decE major)) a (CorePost decH dn m vis fe M eb ResH) := by
  sorry

-/

/-- **`major_to_ctor` refines `majorToCtor`** (the callees' specs as hypotheses): `mtc_ref`'s ok
half. -/
theorem majorToCtor_refines' : MajorToCtorOK p := by
  sorry

end top

end L.Arena
