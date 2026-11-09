module

import ConAgua.Arena.IndRealLvlZT
public import ConAgua.Arena.IndRealLvlZ
import ConAgua.Arena.IndInstallSpec.IcaW
public import ConAgua.Arena.TwinStep
public import ConRon.Bridge.Inductives.Records
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndPosSpec.MatesW
public import ConAgua.Arena.DeclBase
public import ConAgua.Arena.IndInstallSpec.CapsProg
public import ConAgua.Arena.IndPartsSpec.PartsConsPL

@[expose] public section

/-!
# `lv_zero_caps` under the stage relation with the twin's read-back facts (lane `indproofs4`,
helper `lz`)

`lzcF_simT` (`IndRealLvlZT.lean`) needs `StageT` at the CURRENT environment; inside
`cons_block_inds` the environment grows (a former's `.indInfo` record per member), so `StageT`
(`TwinOK`'s `StoreDen` is about the environment) is not at hand there. What the proof of
`lzcF_simT` really reads of the twin is fe-free: the readback cache holds readbacks (`ReadLCOK`)
and the handle reads back. `lzcF_simR` is that proof under `StageR` (at any environment), the
twin's state after it the cache-updated one (its store unchanged, `ReadLCOK` after).

The names of the zero-ness datum decode by the name store; the stage relation's record decoder
`dn` decodes them when the level's `ifAllZero` names all have a `dn` handle (`SortDn`) — the name
store is injective (`denoteN_inj`) and `dn` agrees with it (`TwinMem.dnN`): `decZC_toDn`.

* `lzcSimR_of`: the `lv_zero_caps` call of `block_caps_at` at every state of the invariant
  `LzInv st₀` (store `st₀`, `ReadLCOK`), as `icbiW_simG` (`IndInstallSpec/IcaW.lean`) takes it.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The names of a level's zero-ness datum have handles under `dn`.** -/
def SortDn (dn : NIdx → Option ConLeche.Name) (lv : ConLeche.Level) : Prop :=
  ∀ ps, ConLeche.Level.zeronessOf lv = .ifAllZero ps → ∀ x ∈ ps, ∃ k, dn k = some x

theorem mapM_some_sub {f g : NIdx → Option ConLeche.Name} :
    ∀ (l : List NIdx) (ys : List ConLeche.Name), l.mapM f = some ys →
      (∀ k y, f k = some y → y ∈ ys → g k = some y) → l.mapM g = some ys
  | [], ys, h, _ => h
  | k :: l, ys, h, hg => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys', rfl⟩ := h
    have ih := mapM_some_sub l ys' hys' (fun k' y' h1 h2 => hg k' y' h1 (List.mem_cons_of_mem _ h2))
    simp only [List.mapM_cons, Option.bind_eq_bind, hg k y hy (List.mem_cons_self ..), ih,
      Option.bind_some, Option.pure_def]

/-- **`decZC` by the name store is `decZC` by `dn`** where the datum's names have `dn` handles. -/
theorem decZC_toDn {dn : NIdx → Option ConLeche.Name} {ns : NStore} {m : Mem} {r : List Word}
    {lv : ConLeche.Level} (h : decZC (denoteN ns) m r lv) (hwf : NStoreWF ns)
    (hdnN : ∀ k x, dn k = some x → denoteN ns k = some x) (hz : SortDn dn lv) :
    decZC dn m r lv := by
  intro arr ha
  have h1 := h arr ha
  revert h1
  unfold pwWords
  split
  · exact id
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq]
    rintro ⟨ks, hks, ys, hys, e⟩
    refine ⟨ks, hks, ys, mapM_some_sub ks ys hys (fun k y hk hy => ?_), e⟩
    obtain ⟨k', hk'⟩ := hz ys e.symm y hy
    have := denoteN_inj hwf hk (hdnN _ _ hk')
    subst this; exact hk'
  · exact id

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- The stage relation with the level readback cache replaced. -/
theorem StageR.withReadLC {m : Mem} {a : AState} (hS : StageR vis fe m a)
    (X : Std.HashMap LIdx ConLeche.Level) :
    StageR vis fe m { a with caches := { a.caches with readLC := X } } :=
  ⟨⟨hS.check.arena.caches_irrel _, let ⟨M, hM⟩ := hS.check.core; ⟨M, hM.readLC X⟩, hS.check.pins, hS.check.env,
    hS.check.mode⟩, hS.iw⟩

/-- The stage relation across a level-heap writer. -/
theorem StageR.of_lheap {m m' : Mem} {a : AState} (hS : StageR vis fe m a)
    (hf : MemFrame [LH] [192] m m') : StageR vis fe m' a ∧ IWGrow m m' :=
  hS.frame_hi hf (fun b hb => by simp only [List.mem_singleton] at hb; subst hb; decide)
    (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; decide) (by simp [LH, IW])
    (by simp)

/-- **`lv_zero_caps` under `StageR` and the twin's read-back facts** (`lzcF_simT`'s proof, the
environment free): the twin's `readLevelM l` (the store unchanged, the cache holding readbacks
after), `StageR` after, the pools grown, the zero-ness of `lv` as three words, its names decoded
by the name store. -/
theorem lzcF_simR {m : Mem} {a : AState} (hS : StageR vis fe m a) (hrl : ReadLCOK a) (l : Word)
    (hl : H l) (lv : ConLeche.Level) (hd : denoteL a.store.ls (decI l) = some lv) :
    Sim (lzcF m [l]) (readLevelM (decI l)) a
      (fun r x m' a' => StageR vis fe m' a' ∧ IWGrow m m' ∧
        decZC (denoteN a.store.lss.ls.ns) m' r x ∧ x = lv ∧ a'.store = a.store ∧ ReadLCOK a') := by
  intro r m' h
  obtain ⟨k, hw⟩ := lzcF_lzcW h
  have hlv := denoteL_lvR hS.check.arena.base (decI l) lv hd
  rw [word_decI _ _ hl |>.mpr rfl] at hlv
  obtain ⟨X, hrun, hcX⟩ := readLevelM_run' a (decI l) lv hd hrl
  have hSX := hS.withReadLC X
  refine ⟨lv, _, hrun, ?_⟩
  rcases k with _ | n
  · simp [lzcW] at hw
  simp only [lzcW] at hw
  rcases hz : zeroW n m l with _ | ⟨z, m1⟩
  · rw [hz] at hw; simp [lzcK1] at hw
  rw [hz] at hw
  obtain ⟨he, hZ⟩ := zeroW_ok n m m1 l z lv hlv hz
  have hfH : ∀ v, MemFrame [LH] [192] m (m1.set64 CTL 192 v) := fun v =>
    he.memFrame.trans ((MemFrame.setCtl m1 192 v).mono (by simp) (by simp))
  rcases hZ with ⟨rfl, hpw⟩ | ⟨rfl, ps, hpw, hnm⟩
  · -- `never`: the heap top restored
    simp only [lzcK1, ne_eq, show (1 : Word) ≠ 0 by decide, not_false_eq_true, ↓reduceIte,
      Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨hS', hg⟩ := hSX.of_lheap (hfH _)
    refine ⟨hS', hg, fun arr _ => ?_, rfl, rfl, hcX⟩
    rw [hpw]; rfl
  -- `ifAllZero ps`: the names copied to a fresh record slice
  simp only [lzcK1, ne_eq, not_true_eq_false, ↓reduceIte] at hw
  obtain ⟨hS1, hg1⟩ := hSX.of_lheap he.memFrame
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS1.iw
  generalize hkk : htop m1 - htop m = kk at hw hnm
  have htop1 := he.top
  have hkkN : kk.toNat = (htop m1).toNat - (htop m).toNat := by
    rw [← hkk, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
  rcases ha : erAllocW m1 kk with _ | ⟨q, m2⟩
  · rw [ha] at hw; simp [lzcK2] at hw
  rw [ha] at hw
  simp only [lzcK2] at hw
  cases hcp : lheCopyW n m2 q (htop m) kk with
  | none => rw [hcp] at hw; simp [lzcK3] at hw
  | some m3 =>
  rw [hcp] at hw
  simp only [lzcK3, Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hm3 := lheCopyW_wrER n _ _ _ _ _ hcp
  have hL2 : m2.arr64 LH = m1.arr64 LH := by
    have e : m2 = erAllocMem m1 kk := by unfold erAllocW at ha; split at ha <;> grind
    subst e; unfold erAllocMem; split <;> exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  rw [hL2] at hm3; subst hm3
  -- the record: `erec_alloc` then the `erec_put`s
  obtain ⟨hS3, hg3, -, -, -, -, hW3⟩ :=
    erRec_stage ha hS1 (ieWords (m1.arr64 LH) kk.toNat (htop m)) (ieWords_length _ _ _).symm
  obtain ⟨hS4, hg4⟩ := hS3.of_lheap ((MemFrame.setCtl _ 192 (htop m)).mono (by simp) (by simp))
  refine ⟨hS4, hg1.trans (hg3.trans hg4), fun arr hagr => ?_, rfl, rfl, hcX⟩
  have hb64 : (htop m).toNat + kk.toNat < 2 ^ 64 := by have := (htop m1).toNat_lt; omega
  obtain ⟨lps, hs, hm⟩ := hslice_of_nmsR _ hnm hb64 arr q.toNat
    (fun j hj => by
      have h3 := hW3 j (by rw [ieWords_length]; exact hj)
      rw [ieWords_get _ _ _ _ hj] at h3
      rw [hagr _ _ (hg4.erecGrow.ext _ _ h3)]
      have : (htop m + UInt64.ofNat j).toNat = (htop m).toNat + j := by
        have := hb64; simp [UInt64.toNat_add, UInt64.toNat_ofNat]; omega
      simp only [rdW, this])
  rw [hpw]
  simp only [pwWords, List.headD_cons, List.tail_cons, show (1 : Word).toNat = 1 from rfl, hs,
    Option.bind_eq_bind, Option.bind_some, hm]
  rfl

/-- **`lv_zero_caps` under `StageR` and the read-back facts, as a call** in a program with
`lzcP`. -/
theorem lzc_simR {p : Prog} (hp : LzcF p) (n : Nat) {m : Mem} {a : AState}
    (hS : StageR vis fe m a) (hrl : ReadLCOK a) (l : Word) (hl : H l) (lv : ConLeche.Level)
    (hd : denoteL a.store.ls (decI l) = some lv) :
    Sim (callW p n "lv_zero_caps" [l] m) (readLevelM (decI l)) a
      (fun r x m' a' => StageR vis fe m' a' ∧ IWGrow m m' ∧
        decZC (denoteN a.store.lss.ls.ns) m' r x ∧ x = lv ∧ a'.store = a.store ∧ ReadLCOK a') := by
  intro r m' e
  obtain ⟨s', rfl, -, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (lzcF_spec p hp n _ [l]) e
  exact lzcF_simR hS hrl l hl lv hd r _ hw

end

/-! ## `cons_block_inds` without the stub contract -/

/-- **The loop's invariant on the twin's state**: the store `st₀` (the loop only reads levels
back), the readback cache holding readbacks. -/
def LzInv (st₀ : EStore) (a : AState) : Prop := a.store = st₀ ∧ ReadLCOK a

/-- **The read-back facts `consBlockInds_refinesR` takes**, at the store `st₀`: the name store well
formed, `dn` agreeing with it, the shape's result sort reading back to a level whose zero-ness
names have `dn` handles. -/
structure LzFacts (dn : NIdx → Option ConLeche.Name) (st₀ : EStore) (bs : BlockShape) : Prop where
  nwf : NStoreWF st₀.ns
  dnN : ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → denoteN st₀.ns k = some x
  sort : ∃ lv, denoteL st₀.ls bs.resSort = some lv ∧ SortDn dn lv

/-- `StageC`'s read-back facts (the cache, the name store, `dn`'s agreement). -/
theorem StageC.lzFacts {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {m : Mem} {a : AState} (hC : StageC dn vis fe env m a) :
    ReadLCOK a ∧ NStoreWF a.store.ns ∧
      ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → denoteN a.store.ns k = some x :=
  ⟨hC.stageT.twin.readL, hC.stageT.twin.nwf, hC.mem.dnN⟩

/-- **`LzFacts` from `StageC`**, the shape's denotation and the one fact `StageC` lacks: the
result sort's zero-ness names have `dn` handles. -/
theorem LzFacts.of_stageC {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {m : Mem} {a : AState} {bs : BlockShape} {pP : ConLeche.BlockShape}
    (hC : StageC dn vis fe env m a) (hsh : ConRon.Bridge.Inductives.dShape a.store bs = some pP)
    (hz : SortDn dn pP.resSort) : LzFacts dn a.store bs :=
  have hF := hC.lzFacts
  ⟨hF.2.1, hF.2.2, pP.resSort, (ConRon.Bridge.Inductives.dShape_inv hsh).2.2.2.2.1, hz⟩

/-- **`block_caps_at`'s `lv_zero_caps` call** at every state of `LzInv st₀`, as `icbiW_simG`
takes it. -/
theorem lzcSimR_of {p : Prog} (hp : LzcF p) {dn : NIdx → Option ConLeche.Name} {st₀ : EStore}
    {p1 : Word} {bs : BlockShape} (hF : LzFacts dn st₀ bs) (k : Nat) (m : Mem) (a : AState)
    (vis : Word) (fe : IFEnv) (hS : StageR vis fe m a) (hI : LzInv st₀ a)
    (hq : DecB (fun m => decBS m p1.toNat) m bs) (hsrc : ShapeSrc m p1) :
    Sim (callW p k "lv_zero_caps" [rdW (m.arr64 IW) (p1 + 6)] m) (readLevelM bs.resSort) a
      (fun r x m' a' => (StageR vis fe m' a' ∧ IWGrow m m' ∧ decZC dn m' r x) ∧ LzInv st₀ a') := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨-, -, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  obtain ⟨hst, hrl⟩ := hI
  subst hst
  obtain ⟨lv, hlv, hz⟩ := hF.sort
  rw [← hrse] at hlv ⊢
  refine Sim.mono (lzc_simR hp k hS hrl _ hrs32 lv hlv) ?_
  rintro r x m' a' ⟨hS', hg, hd, rfl, hst, hrl'⟩
  exact ⟨⟨hS', hg, decZC_toDn hd hF.nwf hF.dnN hz⟩, hst.trans rfl, hrl'⟩

end L.Ind
