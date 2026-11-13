module

public import ConAgua.Arena.WhnfCoreSlot
public import ConAgua.Arena.RefECore
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.Verdict
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Checker.NoVerdictFns
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
public import ConAgua.Arena.WhnfCore
import all ConAgua.Arena.WhnfCore

@[expose] public section

/-!
# The `whnfCore` memo policy (con-ron's #572): the lookup and the chain's store

`whnf_core_lookup_at` refines `whnfCoreLookupAt`, `whnf_core_store_keys`/`_cheap_keys` refine
`whnfCoreStoreKeys`/`whnfCoreStoreCheapKeys` on a stack slice, `whnf_core_store_chain` refines
`whnfCoreStoreChain` on the loop's pending keys (`pend` a slice, `pendC` its suffix). Each over its
unified model, by the RefE kit.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The models -/

l_model whnfCoreLookupE_spec (p : Prog) (hf : p.lookup "whnf_core_lookup_at" = some whnfCoreLookupL)
  fns [hf ↦ whnfCoreLookupE list]
  specs [callW_spec p n "wk_find", callW_spec p n "wc_find"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model whnfCoreStoreKeysE_spec (p : Prog) (hf : p.lookup "whnf_core_store_keys" = some whnfCoreStoreKeysL)
  fns [hf ↦ whnfCoreStoreKeysE list]
  specs [callW_spec p n "wc_find", callW_spec p n "wc_put"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model whnfCoreStoreCheapKeysE_spec (p : Prog)
    (hf : p.lookup "whnf_core_store_cheap_keys" = some whnfCoreStoreCheapKeysL)
  fns [hf ↦ whnfCoreStoreCheapKeysE list]
  specs [callW_spec p n "wk_find", callW_spec p n "wk_put"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model whnfCoreStoreChainE_spec (p : Prog) (hf : p.lookup "whnf_core_store_chain" = some whnfCoreStoreChainL)
    (hk : p.lookup "whnf_core_store_keys" = some whnfCoreStoreKeysL)
    (hc : p.lookup "whnf_core_store_cheap_keys" = some whnfCoreStoreCheapKeysL)
  fns [hf ↦ whnfCoreStoreChainE list]
  specs [whnfCoreStoreKeysE_spec p hk n, whnfCoreStoreCheapKeysE_spec p hc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## The refinements -/

/-- **`whnf_core_lookup_at` refines `whnfCoreLookupAt`** (both outcomes; it fails nowhere). -/
@[refines ConRon.Arena.whnfCoreLookupAt ConRon.Arena.whnfCoreLookup]
theorem lookup_ref (p : Prog) (hp : WhnfCoreProg p) (G : Prop) (n : Nat) (m : Mem) (a : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb mode key cheap e : Word)
    (hS : CoreS dn m a vis fe MM eb) (heb : eb = (mode >>> 1) &&& 1) (he : HW e) :
    RefE G (whnfCoreLookupE p (n + 1) m mode key cheap e)
      (whnfCoreLookupAt (key != 0) (cheap != 0) (decE e)) a (CorePost decOptR dn m vis fe MM eb ResW) := by
  have hkey : ((mode >>> 1) &&& 1) <<< 32 = genW 0 eb := ebKey_eq mode eb heb
  have heb1 := hS.core.eb1
  by_cases hk : key = 0
  · rw [whnfCoreLookupE.arm1 _ _ _ _ _ _ _ hk]
    have : (key != 0) = false := by simp [hk]
    rw [this]
    exact RefE.ret rfl (CorePost.ret hS rfl ⟨by unfold HW; decide, by unfold HW; decide⟩)
  have hkb : (key != 0) = true := by simpa using hk
  rw [hkb]
  by_cases hc : cheap ≠ 0
  · rw [whnfCoreLookupE.arm2 _ _ _ _ _ _ _ hk hc]
    have hcb : (cheap != 0) = true := by simpa using hc
    rw [hcb]
    refine RefE.onlySim (fun _ => rfl) (fun _ _ h => callW_memoFind hp.wkf h) fun r₁ m₁ ⟨hm, hne, hr⟩ => ?_
    rw [hkey] at hr
    subst m₁ hr
    have hf := hS.core.wk.findE heb1 e he hne
    by_cases h1 : (mfindG wkSch m e (genW 0 eb)).headD 0 = 0
    · rw [whnfCoreLookupE.k_wk_find.arm2 _ _ _ h1]
      exact RefE.ret (by simp [whnfCoreLookupAt, whnfCoreLookup, hf.2 h1]; rfl)
        (CorePost.ret hS rfl ⟨by unfold HW; decide, by unfold HW; decide⟩)
    rw [whnfCoreLookupE.k_wk_find.arm1 _ _ _ h1]
    exact RefE.ret (by simp [whnfCoreLookupAt, whnfCoreLookup, (hf.1 h1).1]; rfl)
      (CorePost.ret hS (by simp [decOptR, decOpt, mvG]) ⟨show HW 1 by unfold HW; decide, (hf.1 h1).2⟩)
  rw [whnfCoreLookupE.arm3 _ _ _ _ _ _ _ hk (by simpa using hc)]
  have hcb : (cheap != 0) = false := by simpa using hc
  rw [hcb]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => callW_memoFind hp.wcf h) fun r₁ m₁ ⟨hm, hne, hr⟩ => ?_
  rw [hkey] at hr
  subst m₁ hr
  have hf := hS.core.wc.findE heb1 e he hne
  by_cases h1 : (mfindG wcSch m e (genW 0 eb)).headD 0 = 0
  · rw [whnfCoreLookupE.k_wc_find.arm2 _ _ _ h1]
    exact RefE.ret (by simp [whnfCoreLookupAt, whnfCoreLookup, hf.2 h1]; rfl)
      (CorePost.ret hS rfl ⟨by unfold HW; decide, by unfold HW; decide⟩)
  rw [whnfCoreLookupE.k_wc_find.arm1 _ _ _ h1]
  exact RefE.ret (by simp [whnfCoreLookupAt, whnfCoreLookup, (hf.1 h1).1]; rfl)
    (CorePost.ret hS (by simp [decOptR, decOpt, mvG]) ⟨show HW 1 by unfold HW; decide, (hf.1 h1).2⟩)

theorem whnfCoreSet_run (e r : EIdx) (a : AState) :
    (whnfCoreSet e r).run a = .ok ((), { a with caches := { a.caches with
      whnfCoreC := a.caches.whnfCoreC.insert e r } }) := by
  simp [whnfCoreSet]; rfl

theorem whnfCoreCheapSet_run (e r : EIdx) (a : AState) :
    (whnfCoreCheapSet e r).run a = .ok ((), { a with caches := { a.caches with
      whnfCoreCheapC := a.caches.whnfCoreCheapC.insert e r } }) := by
  simp [whnfCoreCheapSet]; rfl

/-- **`whnf_core_store_keys` refines `whnfCoreStoreKeys`** on a slice below the top, from any
state the run reached (the loop's induction). -/
@[refines ConRon.Arena.whnfCoreStoreKeys ConRon.Arena.whnfCoreSet]
theorem storeKeys_ref (p : Prog) (hp : WhnfCoreProg p) (G : Prop) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (mode o nn v : Word) (pend : Array EIdx) (m₀ : Mem) (MM₀ : ModeMaps)
    (eb : Word) (heb : eb = (mode >>> 1) &&& 1) (hv : HW v) (hsl : SpineR m₀ o nn pend)
    (hlo : o.toNat + nn.toNat ≤ (spTop m₀).toNat) :
    ∀ (k : Nat) (i : Word) (m : Mem) (a : AState) (MM : ModeMaps), i.toNat ≤ nn.toNat →
      CoreS dn m a vis fe MM eb → KeptAll MM₀ MM eb → StackKept m₀ m →
      RefE G (whnfCoreStoreKeysE.k_loop1 p (whnfCoreStoreKeysE.loop1 p k m mode o nn i v))
        (whnfCoreStoreKeys pend i.toNat (decE v)) a
        (CorePost (fun _ => ()) dn m₀ vis fe MM₀ eb (fun _ => True)) := by
  have hkey : ((mode >>> 1) &&& 1) <<< 32 = genW 0 eb := ebKey_eq mode eb heb
  intro k
  induction k with
  | zero =>
    intro i m a MM _ _ _ _
    simp only [whnfCoreStoreKeysE.loop1]
    exact RefE.of_cls0 rfl
  | succ k ih =>
    intro i m a MM hi hS hK hSt
    simp only [whnfCoreStoreKeysE.loop1]
    by_cases hlt : i < nn
    · rw [ite_eq_left hlt]
      have hlt' : i.toNat < nn.toNat := UInt64.lt_iff_toNat_lt.mp hlt
      have hit : i.toNat.toUInt64 = i := by simp
      have hb0 : (m₀.arr64 SPN).size < 2 ^ 63 := hSt.size ▸ hS.spn
      have hkw : HW (rdW (m.arr64 SPN) (o + i)) := by
        have := hsl.lt i.toNat hlt'; rw [hit] at this
        rw [show rdW (m.arr64 SPN) (o + i) = spW m (o + i) from rfl, hSt.below]
        · exact this
        · rw [UInt64.lt_iff_toNat_lt, L.toNat_add_of_lt _ _ (by have := hsl.bound; have := hb0; omega)]
          omega
      have hpi : pend[i.toNat]'(by rw [hsl.size]; exact hlt') = decE (rdW (m.arr64 SPN) (o + i)) := by
        rw [hsl.get, hit, show rdW (m.arr64 SPN) (o + i) = spW m (o + i) from rfl, hSt.below]
        rw [UInt64.lt_iff_toNat_lt, L.toNat_add_of_lt _ _ (by have := hsl.bound; have := hb0; omega)]
        omega
      refine RefE.onlySim (K := fun c => whnfCoreStoreKeysE.k_loop1 p
        (whnfCoreStoreKeysE.k_wc_find p k mode o nn i v (rdW (m.arr64 SPN) (o + i)) c))
        (fun _ => by rw [whnfCoreStoreKeysE.k_wc_find.none, whnfCoreStoreKeysE.k_loop1.none])
        (fun _ _ h => h) fun r₃ m₃ h3 => ?_
      rw [whnfCoreStoreKeysE.k_wc_find.arm1]
      refine RefE.onlySim (K := fun c => whnfCoreStoreKeysE.k_loop1 p
        (whnfCoreStoreKeysE.k_wc_put p k mode o nn i v c))
        (fun _ => by rw [whnfCoreStoreKeysE.k_wc_put.none, whnfCoreStoreKeysE.k_loop1.none])
        (fun _ _ h => h) fun r₄ m₄ h4 => ?_
      rw [whnfCoreStoreKeysE.k_wc_put.arm1]
      have hset := callW_memoSet hp.wcf hp.wcp h3 h4
      rw [hkey] at hset
      obtain ⟨hS₂, hSt₂⟩ := hS.set_wc _ v hkw hv hset
      have hn : i.toNat < pend.size := by rw [hsl.size]; exact hlt'
      rw [whnfCoreStoreKeys]
      simp only [hn, dite_true]
      rw [hpi]
      refine RefE.bind_right (whnfCoreSet_run _ _ a) ?_
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; have := nn.toNat_lt; omega
      have := ih (i + 1) m₄ _ _ (by omega) hS₂ (hK.wc _ _) (hSt.trans hSt₂)
      rwa [hi1] at this
    · rw [ite_eq_right hlt, whnfCoreStoreKeysE.k_loop1.arm1]
      have hn : ¬ i.toNat < pend.size := by
        rw [hsl.size]; exact fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      exact RefE.ret (by rw [whnfCoreStoreKeys]; simp [hn]; rfl) ⟨⟨MM, hS, hK, hSt⟩, rfl, trivial⟩

/-- **`whnf_core_store_cheap_keys` refines `whnfCoreStoreCheapKeys`** (as `storeKeys_ref`). -/
@[refines ConRon.Arena.whnfCoreStoreCheapKeys ConRon.Arena.whnfCoreCheapSet]
theorem storeCheapKeys_ref (p : Prog) (hp : WhnfCoreProg p) (G : Prop) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (mode o nn v : Word) (pend : Array EIdx) (m₀ : Mem) (MM₀ : ModeMaps)
    (eb : Word) (heb : eb = (mode >>> 1) &&& 1) (hv : HW v) (hsl : SpineR m₀ o nn pend)
    (hlo : o.toNat + nn.toNat ≤ (spTop m₀).toNat) :
    ∀ (k : Nat) (i : Word) (m : Mem) (a : AState) (MM : ModeMaps), i.toNat ≤ nn.toNat →
      CoreS dn m a vis fe MM eb → KeptAll MM₀ MM eb → StackKept m₀ m →
      RefE G (whnfCoreStoreCheapKeysE.k_loop1 p (whnfCoreStoreCheapKeysE.loop1 p k m mode o nn i v))
        (whnfCoreStoreCheapKeys pend i.toNat (decE v)) a
        (CorePost (fun _ => ()) dn m₀ vis fe MM₀ eb (fun _ => True)) := by
  have hkey : ((mode >>> 1) &&& 1) <<< 32 = genW 0 eb := ebKey_eq mode eb heb
  intro k
  induction k with
  | zero =>
    intro i m a MM _ _ _ _
    simp only [whnfCoreStoreCheapKeysE.loop1]
    exact RefE.of_cls0 rfl
  | succ k ih =>
    intro i m a MM hi hS hK hSt
    simp only [whnfCoreStoreCheapKeysE.loop1]
    by_cases hlt : i < nn
    · rw [ite_eq_left hlt]
      have hlt' : i.toNat < nn.toNat := UInt64.lt_iff_toNat_lt.mp hlt
      have hit : i.toNat.toUInt64 = i := by simp
      have hb0 : (m₀.arr64 SPN).size < 2 ^ 63 := hSt.size ▸ hS.spn
      have hkw : HW (rdW (m.arr64 SPN) (o + i)) := by
        have := hsl.lt i.toNat hlt'; rw [hit] at this
        rw [show rdW (m.arr64 SPN) (o + i) = spW m (o + i) from rfl, hSt.below]
        · exact this
        · rw [UInt64.lt_iff_toNat_lt, L.toNat_add_of_lt _ _ (by have := hsl.bound; have := hb0; omega)]
          omega
      have hpi : pend[i.toNat]'(by rw [hsl.size]; exact hlt') = decE (rdW (m.arr64 SPN) (o + i)) := by
        rw [hsl.get, hit, show rdW (m.arr64 SPN) (o + i) = spW m (o + i) from rfl, hSt.below]
        rw [UInt64.lt_iff_toNat_lt, L.toNat_add_of_lt _ _ (by have := hsl.bound; have := hb0; omega)]
        omega
      refine RefE.onlySim (K := fun c => whnfCoreStoreCheapKeysE.k_loop1 p
        (whnfCoreStoreCheapKeysE.k_wk_find p k mode o nn i v (rdW (m.arr64 SPN) (o + i)) c))
        (fun _ => by rw [whnfCoreStoreCheapKeysE.k_wk_find.none, whnfCoreStoreCheapKeysE.k_loop1.none])
        (fun _ _ h => h) fun r₃ m₃ h3 => ?_
      rw [whnfCoreStoreCheapKeysE.k_wk_find.arm1]
      refine RefE.onlySim (K := fun c => whnfCoreStoreCheapKeysE.k_loop1 p
        (whnfCoreStoreCheapKeysE.k_wk_put p k mode o nn i v c))
        (fun _ => by rw [whnfCoreStoreCheapKeysE.k_wk_put.none, whnfCoreStoreCheapKeysE.k_loop1.none])
        (fun _ _ h => h) fun r₄ m₄ h4 => ?_
      rw [whnfCoreStoreCheapKeysE.k_wk_put.arm1]
      have hset := callW_memoSet hp.wkf hp.wkp h3 h4
      rw [hkey] at hset
      obtain ⟨hS₂, hSt₂⟩ := hS.set_wk _ v hkw hv hset
      have hn : i.toNat < pend.size := by rw [hsl.size]; exact hlt'
      rw [whnfCoreStoreCheapKeys]
      simp only [hn, dite_true]
      rw [hpi]
      refine RefE.bind_right (whnfCoreCheapSet_run _ _ a) ?_
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; have := nn.toNat_lt; omega
      have := ih (i + 1) m₄ _ _ (by omega) hS₂ (hK.wk _ _) (hSt.trans hSt₂)
      rwa [hi1] at this
    · rw [ite_eq_right hlt, whnfCoreStoreCheapKeysE.k_loop1.arm1]
      have hn : ¬ i.toNat < pend.size := by
        rw [hsl.size]; exact fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      exact RefE.ret (by rw [whnfCoreStoreCheapKeys]; simp [hn]; rfl) ⟨⟨MM, hS, hK, hSt⟩, rfl, trivial⟩

/-- A trailing part of a stack slice, as `Array.extract` (the cheap keys' suffix). -/
theorem SpineR.suffix {m : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (c : Word) (hc : c.toNat ≤ cnt.toNat) (hspn : (m.arr64 SPN).size < 2 ^ 63) :
    SpineR m (off + c) (cnt - c) (xs.extract c.toNat xs.size) := by
  have hb := h.bound
  have hsz := h.size
  have hoc : (off + c).toNat = off.toNat + c.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hcc : (cnt - c).toNat = cnt.toNat - c.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hc)
  have hw : ∀ i : Nat, i < cnt.toNat - c.toNat →
      off + c + i.toUInt64 = off + (c.toNat + i).toUInt64 := by
    intro i hi
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    have : off.toNat < 2 ^ 64 := off.toNat_lt
    omega
  refine ⟨by simp [hsz, hcc], by rw [hoc, hcc]; omega, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hcc] at hi; rw [hw i hi]; exact h.lt _ (by omega)
  · simp only [Array.size_extract] at hi
    have hi' : c.toNat + i < xs.size := by omega
    rw [hw i (by omega)]
    have := h.get (c.toNat + i) hi'
    simpa [Array.getElem_extract] using this

/-- **`whnf_core_store_chain` refines `whnfCoreStoreChain`**: `pend` the slice `SPN[pb, pb + pn)`
below the top, `pendC` its suffix from `pc`. -/
@[refines ConRon.Arena.whnfCoreStoreChain]
theorem storeChain_ref (p : Prog) (hp : WhnfCoreProg p) (G : Prop) (n : Nat) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (mode cheap pb pn pc v : Word) (pend pendC : Array EIdx) (m : Mem) (a : AState)
    (MM : ModeMaps) (eb : Word) (heb : eb = (mode >>> 1) &&& 1) (hv : HW v) (hS : CoreS dn m a vis fe MM eb)
    (hsl : SpineR m pb pn pend) (hpc : pc.toNat ≤ pn.toNat) (hsuf : pend.extract pc.toNat pend.size = pendC)
    (hlo : pb.toNat + pn.toNat ≤ (spTop m).toNat) :
    RefE G (whnfCoreStoreChainE p (n + 1) m mode cheap pb pn pc v)
      (whnfCoreStoreChain (cheap != 0) pend pendC (decE v)) a
      (CorePost (fun _ => ()) dn m vis fe MM eb (fun _ => True)) := by
  by_cases hc : cheap ≠ 0
  · rw [whnfCoreStoreChainE.arm1 _ _ _ _ _ _ _ _ _ hc]
    have hcb : (cheap != 0) = true := by simpa using hc
    rw [hcb]
    exact RefE.ret rfl (CorePost.ret hS rfl trivial)
  have hc0 : cheap = 0 := by simpa using hc
  have hcb : (cheap != 0) = false := by simp [hc0]
  rw [hcb]
  by_cases hn : pn = 0
  · rw [whnfCoreStoreChainE.arm2 _ _ _ _ _ _ _ _ _ hc0 hn]
    have : pend.size = 0 := by rw [hsl.size, hn]; rfl
    exact RefE.ret (by simp [whnfCoreStoreChain, this]; rfl) (CorePost.ret hS rfl trivial)
  rw [whnfCoreStoreChainE.arm3 _ _ _ _ _ _ _ _ _ hc0 hn]
  have hsz : ¬ pend.size = 0 := by
    rw [hsl.size]; exact fun h => hn (UInt64.toNat_inj.mp (by rw [h]; rfl))
  simp only [whnfCoreStoreChain, hsz, ite_false, Bool.false_eq_true]
  cases n with
  | zero => exact RefE.of_cls0 rfl
  | succ n =>
  rw [whnfCoreStoreKeysE.arm1]
  have h1 := storeKeys_ref p hp G dn vis fe mode pb pn v pend m MM eb heb hv hsl hlo (n + 1) 0 m a MM
    (by simp) hS (KeptAll.refl _ _) (StackKept.refl _)
  refine RefE.bindE (fun _ => rfl) id h1 fun ⟨r₁, m₁⟩ y a₁ _ hP => ?_
  obtain ⟨M₁, hS₁, hK₁, hSt₁⟩ := hP.after
  simp only [whnfCoreStoreChainE.k_whnf_core_store_keys]
  have hspn : (m.arr64 SPN).size < 2 ^ 63 := hS.spn
  have hbd := hsl.bound
  have hd := hsl.suffix pc hpc hspn
  rw [hsuf] at hd
  have hd₁ := hd.keep hSt₁.size hSt₁.below (by
    rw [L.toNat_add_of_lt _ _ (by omega), UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hpc)]; omega) hspn
  rw [whnfCoreStoreCheapKeysE.arm1]
  have h2 := storeCheapKeys_ref p hp G dn vis fe mode (pb + pc) (pn - pc) v pendC m₁ M₁ eb heb hv hd₁ (by
    rw [hSt₁.top, L.toNat_add_of_lt _ _ (by omega),
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hpc)]; omega) (n + 1) 0 m₁ a₁ M₁
    (by simp) hS₁ (KeptAll.refl _ _) (StackKept.refl _)
  refine RefE.lastE (f := fun v => ([0], v.2)) (fun _ => whnfCoreStoreChainE.k_whnf_core_store_cheap_keys.none ..)
    (fun ⟨_, _⟩ => whnfCoreStoreChainE.k_whnf_core_store_cheap_keys.arm1 ..) id h2 fun ⟨r₂, m₂⟩ z a₂ _ hP₂ => ?_
  obtain ⟨M₂, hS₂, hK₂, hSt₂⟩ := hP₂.after
  exact ⟨⟨M₂, hS₂, hK₁.trans hK₂, hSt₁.trans hSt₂⟩, rfl, trivial⟩

end L.Arena
