module

import ConAgua.L.ModelGen
import ConAgua.Arena.IndRealNames
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all Init.Data.Repr
import ConAgua.Arena.DeclMasterStage
import ConAgua.Arena.IndMaster
import ConAgua.Arena.Rom
import ConAgua.Arena.SimLib
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.CallF
public import ConAgua.Arena.StripTeleSpec
public import ConAgua.Arena.StubNames
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.NStrStore
import all ConAgua.Arena.Store
import all ConAgua.Arena.StubNames

@[expose] public section

/-!
# `name_rec_i` discharged (lane `indproofs4`, helper `indproofs4-ilp`)

The recipe of `IndRealNames.lean`'s `name_rec` (`nrF`, `nrF_ok`) for `name_rec_i(n, i)`: the
digit count (`dec_len`), `rec_` and the decimal digits of `i` written at the pool top (most
significant first, the loop running from the end, `x / 10` as `mulhi(x, ⌈2^67/10⌉) >> 3`), then
master's `intern_nstr`. The written words are `strWords s!"rec_{i}"` (`strWords_recI`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Decimal digits -/

/-- `x / 10` the way `dec_len` and `name_rec_i` compute it. -/
def div10W (x : Word) : Word := UInt64.ofNat (x.toNat * 14757395258967641293 / 2 ^ 64) >>> 3

theorem div10W_toNat (x : Word) : (div10W x).toNat = x.toNat / 10 := by
  have hx := x.toNat_lt
  have h1 : x.toNat * 14757395258967641293 / 2 ^ 64 < 2 ^ 64 := by omega
  simp only [div10W, UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h1]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  omega

/-- The number of decimal digits of `n`. -/
def decLenN (n : Nat) : Nat := if n < 10 then 1 else decLenN (n / 10) + 1

theorem decLenN_le (n : Nat) : decLenN n ≤ n / 2 + 1 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold decLenN
    split
    · omega
    · have := ih (n / 10) (by omega); omega

theorem decLenN_pos (n : Nat) : 1 ≤ decLenN n := by
  unfold decLenN; split <;> omega

/-- The last `d` decimal digits of `x` as character words, most significant first. -/
def digsR : Nat → Nat → List Word
  | 0, _ => []
  | d + 1, x => digsR d (x / 10) ++ [(48 + x % 10 : Nat).toUInt64]

theorem strWords_append (s t : String) : strWords (s ++ t) = strWords s ++ strWords t := by
  simp [strWords, String.toByteArray_append]

theorem strWords_digit (d : Nat) (h : d < 10) :
    strWords (String.singleton (Nat.digitChar d)) = [(48 + d : Nat).toUInt64] := by
  have : ∀ e : Fin 10, strWords (String.singleton (Nat.digitChar e)) = [(48 + e : Nat).toUInt64] := by
    decide
  exact this ⟨d, h⟩

theorem strWords_repr (n : Nat) : strWords n.repr = digsR (decLenN n) n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · rw [Nat.repr_of_lt h, strWords_digit n h]
      unfold decLenN; rw [ite_eq_left h]
      simp [digsR, Nat.mod_eq_of_lt h]
    · rw [Nat.repr_of_ge (by omega), strWords_append, ih (n / 10) (by omega),
        strWords_digit _ (Nat.mod_lt _ (by omega))]
      conv => rhs; unfold decLenN
      rw [ite_eq_right h]; rfl

theorem strWords_recI (i : Nat) :
    strWords s!"rec_{i}" = [114, 101, 99, 95] ++ digsR (decLenN i) i := by
  have : s!"rec_{i}" = "rec_" ++ i.repr := by simp; rfl
  rw [this, strWords_append, strWords_repr]
  rfl

/-! ## `dec_len` -/

l_model decLen_specW (p : Prog) (hp : p.lookup "dec_len" = some L.Stubs.decLen)
  fns [hp ↦ decLenW ro]
  grind [arena_grind] finish [div10W]

/-- `dec_len`'s and `name_rec_i`'s `mulhi(x, …) >> 3` is `x / 10`. -/
theorem mulhi10 (x : Word) :
    UInt64.ofNat (x.toNat * (14757395258967641293 : Word).toNat / 2 ^ 64) >>> (3 : Word) = div10W x := rfl

theorem dlW_ok (m : Mem) : ∀ (f : Nat) (x k r : Word), decLenW.loop1 f m x k = some r →
    k.toNat + decLenN x.toNat < 2 ^ 64 → r.toNat = k.toNat + decLenN x.toNat - 1 := by
  intro f
  induction f with
  | zero => intro x k r h; simp [decLenW.loop1] at h
  | succ f ih =>
    intro x k r h hb
    by_cases hx : 9 < x
    · rw [decLenW.loop1.arm1 f m x k hx, mulhi10] at h
      have hx' : 10 ≤ x.toNat := by have := UInt64.lt_iff_toNat_lt.mp hx; simp at this; omega
      have hd : decLenN x.toNat = decLenN (x.toNat / 10) + 1 := by
        conv => lhs; unfold decLenN
        rw [ite_eq_right (by omega)]
      have hk : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have := ih _ _ _ h (by rw [hk, div10W_toNat]; omega)
      rw [hk, div10W_toNat] at this; omega
    · rw [decLenW.loop1.arm2 f m x k hx] at h; cases h
      have hx' : x.toNat < 10 := by
        have := mt UInt64.lt_iff_toNat_lt.mpr hx; simp at this; omega
      unfold decLenN; rw [ite_eq_left hx']; omega

/-! ## `name_rec_i`'s digit loop and body -/

/-- The four bytes `rec_` at `o`. -/
def recIBytes (m : Mem) (o : Word) : Mem :=
  (((m.set64 (tierA POOL (o >>> 40)) (o &&& 1099511627775) 114).set64 (tierA POOL (o >>> 40)) ((o &&& 1099511627775) + 1) 101).set64
    (tierA POOL (o >>> 40)) ((o &&& 1099511627775) + 2) 99).set64 (tierA POOL (o >>> 40)) ((o &&& 1099511627775) + 3) 95

theorem recIBytes_fold (m : Mem) (o : Word) :
    (((m.set64 (tierA POOL (o >>> 40)) (o &&& 1099511627775) 114).set64 (tierA POOL (o >>> 40))
      ((o &&& 1099511627775) + 1) 101).set64 (tierA POOL (o >>> 40)) ((o &&& 1099511627775) + 2) 99).set64
      (tierA POOL (o >>> 40)) ((o &&& 1099511627775) + 3) 95 = recIBytes m o := rfl

l_model nameRecI_specW (p : Prog) (hp : p.lookup "name_rec_i" = some L.Stubs.nameRecIL)
  fns [hp ↦ nriW]
  specs [callW_spec p n "dec_len", callW_spec p n "pool_room", callW_spec p n "intern_nstr"]
  grind [arena_grind] finish [div10W]

/-! ## The program and the model -/

/-- `name_rec_i` and its callees. -/
def nriProg : Prog :=
  [("name_rec_i", L.Stubs.nameRecIL), ("dec_len", L.Stubs.decLen), ("pool_room", L.Stubs.poolRoom),
   ("intern_nstr", internNStr), ("lit_hash", litHash), ("limbs_eq", limbsEq),
   ("nstr_match", nsMatch), ("nstr_find", nsFind), ("nstr_push", nsPush)]

def nriFns : List FnName := nriProg.map (·.1)

/-- `name_rec_i` writes the pool (and its top) and the `str` table. -/
theorem nriProg_closed : closedA nriProg [POOL, POOL1, NSREC, tier1 NSREC, NSSLOT, tier1 NSSLOT] [0, 36, 37] nriFns = true := by
  decide +kernel

abbrev NriF (p : Prog) : Prop := ProgHas p nriProg

/-- **The model of `name_rec_i`.** -/
noncomputable def nriF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF nriProg "name_rec_i" m args

theorem nriF_spec (p : Prog) (hp : NriF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "name_rec_i" args
    ⦃fun r s' => LocEq s' s₀ ∧ nriF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec nriProg_closed (hp.agree nriFns) (by decide) n s₀ args

/-! ## The words written -/

theorem sliceL_snoc (p : Array Word) (o l : Nat) :
    sliceL p o (l + 1) = sliceL p o l ++ [p[o + l]?.getD 0] := by
  simp only [sliceL, List.ofFn_succ_last, Fin.val_last, Fin.val_castSucc]

theorem sliceL_add (p : Array Word) (o a : Nat) : ∀ b, sliceL p o (a + b) = sliceL p o a ++ sliceL p (o + a) b
  | 0 => by simp [sliceL]
  | b + 1 => by
    rw [← Nat.add_assoc, sliceL_snoc, sliceL_add p o a b, sliceL_snoc, List.append_assoc, Nat.add_assoc]

theorem sliceL_congr {p p' : Array Word} {o l : Nat} (h : ∀ t < l, p[o + t]? = p'[o + t]?) :
    sliceL p o l = sliceL p' o l := by
  simp only [sliceL]; congr 1; funext t; rw [h t t.2]

/-- A pool store `POOL⟨t⟩[i] := x` at an address at or above the original top, inside the tier's
array, keeps a growth a growth. -/
theorem grows_pset_ti {m₀ m : Mem} (hg : Grows m₀ m) (hok : PoolOK m₀) {t i x : Word}
    (ht : t.toNat ≤ 1) (hq : m₀.top.toNat ≤ t.toNat * 2 ^ 40 + i.toNat)
    (hi : i.toNat < (m.arr64 (tierA POOL t)).size) :
    Grows m₀ (m.set64 (tierA POOL t) i x) := by
  have hpc : pcap m < 2 ^ 64 := by rw [hg.pcapEq]; have := hok.cap; omega
  have hsz := pcap_tier m t hpc
  have hv := vpool_set64t m t i x ht hi (by omega)
  have hne : tierA POOL t ≠ CTL := Ne.symm (tierA_pool_ne _ _ (by decide) (by decide))
  have htop : (m.set64 (tierA POOL t) i x).top = m.top := L.Rom.top_set64_arr _ _ _ _ hne
  obtain ⟨hf, ha, hle, hcap, hpe, htr, hin⟩ := hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htop]; exact PFrame.set64 _ _ _ hf
  · rw [hv]; exact Agree.set _ _ _ _ _ ha hq
  · rw [htop]; exact hle
  · rw [htop, pcap_set64]; exact hcap
  · rw [pcap_set64]; exact hpe
  · rw [htop]; exact htr
  · rw [htop, L.Mem.size64_set64]; exact hin

/-- **The digit loop**: from the relative index `j` down to `⦃T⦄.idx + 4` in `T`'s tier, the last
digits of `x`; nothing else in the pool changes, the growth from `m₀` is kept. -/
theorem digW_ok (p : Prog) (m₀ : Mem) (hok : PoolOK m₀) (T : Word) (hT : T.toNat < 2 ^ 41)
    (hT0 : m₀.top.toNat ≤ T.toNat) : ∀ (f : Nat) (m m' : Mem) (j x : Word),
    nriW.loop1 p f m j x (T >>> 40) (T &&& 1099511627775) = some m' →
    (T &&& 1099511627775).toNat + 4 ≤ j.toNat → j.toNat ≤ (m.arr64 (tierA POOL (T >>> 40))).size →
    Grows m₀ m →
    Grows m₀ m' ∧ m'.top = m.top ∧ pcap m' = pcap m ∧
      (m'.arr64 (tierA POOL (T >>> 40))).size = (m.arr64 (tierA POOL (T >>> 40))).size ∧
      (∀ t, (t < T.toNat + 4 ∨ T.toNat + (j.toNat - (T &&& 1099511627775).toNat) ≤ t) → (vpool m')[t]? = (vpool m)[t]?) ∧
      sliceL (vpool m') (T.toNat + 4) (j.toNat - ((T &&& 1099511627775).toNat + 4)) =
        digsR (j.toNat - ((T &&& 1099511627775).toNat + 4)) x.toNat := by
  have hsplit := tag_split T
  have htier := tag_tier_le T hT
  have hidx := tag_idx_lt T
  have hne : tierA POOL (T >>> 40) ≠ CTL := Ne.symm (tierA_pool_ne _ _ (by decide) (by decide))
  intro f
  induction f with
  | zero => intro m m' j x h; simp [nriW.loop1] at h
  | succ f ih =>
    intro m m' j x h hj hjs hg
    have hpc : pcap m < 2 ^ 64 := by rw [hg.pcapEq]; have := hok.cap; omega
    have hsz := pcap_tier m (T >>> 40) hpc
    have hp4 : ((T &&& 1099511627775) + 4).toNat = (T &&& 1099511627775).toNat + 4 := by
      have h4 : (4 : Word).toNat = 4 := rfl
      rw [UInt64.toNat_add, h4]; exact Nat.mod_eq_of_lt (by omega)
    by_cases hc : (T &&& 1099511627775) + 4 < j
    · rw [nriW.loop1.arm1 p f m j x _ _ hc, mulhi10] at h
      have hc' : (T &&& 1099511627775).toNat + 4 < j.toNat := by rw [← hp4]; exact UInt64.lt_iff_toNat_lt.mp hc
      have hj1 : (j - 1).toNat = j.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
      have hv := vpool_set64t m (T >>> 40) (j - 1) (48 + (x - div10W x * 10)) htier (by omega) (by omega)
      have hg1 := grows_pset_ti hg hok (t := T >>> 40) (i := j - 1) (x := 48 + (x - div10W x * 10)) htier
        (by omega) (by omega)
      obtain ⟨hg', htop, hpc', hsz', hkeep, hsl⟩ := ih _ m' (j - 1) (div10W x) h (by omega)
        (by rw [L.Mem.size64_set64]; omega) hg1
      have htop1 : (m.set64 (tierA POOL (T >>> 40)) (j - 1) (48 + (x - div10W x * 10))).top = m.top :=
        L.Rom.top_set64_arr _ _ _ _ hne
      have haddr : (T >>> 40).toNat * 2 ^ 40 + (j - 1).toNat = T.toNat + (j.toNat - 1 - (T &&& 1099511627775).toNat) := by
        omega
      refine ⟨hg', by rw [htop, htop1], by rw [hpc', pcap_set64], by rw [hsz', L.Mem.size64_set64], fun t ht' => ?_, ?_⟩
      · rw [hkeep t (by omega), hv, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        have : (T >>> 40).toNat * 2 ^ 40 + (j - 1).toNat ≠ t := by omega
        rw [ite_eq_right this]
      · have hd : j.toNat - ((T &&& 1099511627775).toNat + 4) = (j.toNat - 1 - ((T &&& 1099511627775).toNat + 4)) + 1 := by omega
        rw [hd, sliceL_snoc, digsR, ← hj1, hsl, div10W_toNat]
        congr 2
        have e : T.toNat + 4 + ((j - 1).toNat - ((T &&& 1099511627775).toNat + 4)) =
            (T >>> 40).toNat * 2 ^ 40 + (j - 1).toNat := by omega
        rw [e, hkeep _ (.inr (by omega)), hv, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [vpool_size, show (T >>> 40).toNat * 2 ^ 40 + (j - 1).toNat < 2 ^ 41 by omega,
          ↓reduceIte, Option.getD_some]
        apply UInt64.toNat_inj.mp
        have hx := x.toNat_lt
        have hd10 := div10W_toNat x
        have hm : (div10W x * 10).toNat = x.toNat / 10 * 10 := by
          rw [UInt64.toNat_mul, hd10]; simp; omega
        have hs : (x - div10W x * 10).toNat = x.toNat % 10 := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hm]; omega), hm]; omega
        rw [UInt64.toNat_add, hs]; simp
    · rw [nriW.loop1.arm2 p f m j x _ _ hc] at h; cases h
      have hc' : ¬ (T &&& 1099511627775).toNat + 4 < j.toNat := fun h' => hc (by rw [UInt64.lt_iff_toNat_lt, hp4]; exact h')
      have h0 : j.toNat - ((T &&& 1099511627775).toNat + 4) = 0 := by omega
      exact ⟨hg, rfl, rfl, rfl, fun _ _ => rfl, by rw [h0]; simp [sliceL, digsR]⟩

/-- **The bytes `rec_` after the reserved room** grow the pool. -/
theorem recIBytes_ok (m : Mem) (hpool : PoolOK m) (R : Word) (hR : 4 ≤ R.toNat)
    (hroom : (m.top &&& 1099511627775).toNat + R.toNat ≤ (m.arr64 (tierA POOL (m.top >>> 40))).size) :
    Grows m (recIBytes (m.set64 CTL 0 (m.top + R)) m.top) ∧
      (recIBytes (m.set64 CTL 0 (m.top + R)) m.top).top = m.top + R ∧
      ((recIBytes (m.set64 CTL 0 (m.top + R)) m.top).arr64 (tierA POOL (m.top >>> 40))).size =
        (m.arr64 (tierA POOL (m.top >>> 40))).size ∧
      sliceL (vpool (recIBytes (m.set64 CTL 0 (m.top + R)) m.top)) m.top.toNat 4 = [114, 101, 99, 95] := by
  have hc := hpool.ctl
  have h41 := hpool.top41
  have hsz := hpool.small.tier (m.top >>> 40)
  have hsplit := tag_split m.top
  have htier := tag_tier_le m.top h41
  have hne : tierA POOL (m.top >>> 40) ≠ CTL := Ne.symm (tierA_pool_ne _ _ (by decide) (by decide))
  have hX : (m.set64 CTL 0 (m.top + R)).arr64 (tierA POOL (m.top >>> 40)) = m.arr64 (tierA POOL (m.top >>> 40)) :=
    Mem.arr64_set64_ne _ _ _ _ _ hne
  have e1 : (m.top + 1).toNat = m.top.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (m.top + 2).toNat = m.top.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (m.top + 3).toNat = m.top.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have g0 := grows_raise m R hpool hroom
  have g1 := grows_pset0 g0 hpool (T := m.top) (x := 114) h41 (Nat.le_refl _) (by rw [hX]; omega)
  have g2 := grows_pset_k g1 hpool (T := m.top) (k := 1) (x := 101) h41 (by rw [e1]; omega)
    (by rw [L.Mem.size64_set64, hX]; simp only [UInt64.reduceToNat]; omega)
  have g3 := grows_pset_k g2 hpool (T := m.top) (k := 2) (x := 99) h41 (by rw [e2]; omega)
    (by rw [L.Mem.size64_set64, L.Mem.size64_set64, hX]; simp only [UInt64.reduceToNat]; omega)
  have g4 := grows_pset_k g3 hpool (T := m.top) (k := 3) (x := 95) h41 (by rw [e3]; omega)
    (by rw [L.Mem.size64_set64, L.Mem.size64_set64, L.Mem.size64_set64, hX]; simp only [UInt64.reduceToNat]; omega)
  have htop : (recIBytes (m.set64 CTL 0 (m.top + R)) m.top).top = m.top + R := by
    simp only [recIBytes]
    rw [L.Rom.top_set64_arr _ _ _ _ hne, L.Rom.top_set64_arr _ _ _ _ hne, L.Rom.top_set64_arr _ _ _ _ hne,
      L.Rom.top_set64_arr _ _ _ _ hne]
    exact Mem.top_set64 _ _ hc
  have hsz' : ((recIBytes (m.set64 CTL 0 (m.top + R)) m.top).arr64 (tierA POOL (m.top >>> 40))).size =
      (m.arr64 (tierA POOL (m.top >>> 40))).size := by
    simp only [recIBytes, L.Mem.size64_set64, hX]
  refine ⟨g4, htop, hsz', ?_⟩
  have hv : vpool (recIBytes (m.set64 CTL 0 (m.top + R)) m.top) =
      ((((vpool m).set! m.top.toNat 114).set! (m.top + 1).toNat 101).set! (m.top + 2).toNat 99).set!
        (m.top + 3).toNat 95 := by
    simp only [recIBytes]
    rw [vpool_st_k _ _ _ _ h41 (by simp only [Mem.size_arr64_set64, hX]; omega)
        (by simp only [Mem.size_arr64_set64, hX, UInt64.reduceToNat]; omega),
      vpool_st_k _ _ _ _ h41 (by simp only [Mem.size_arr64_set64, hX]; omega)
        (by simp only [Mem.size_arr64_set64, hX, UInt64.reduceToNat]; omega),
      vpool_st_k _ _ _ _ h41 (by simp only [Mem.size_arr64_set64, hX]; omega)
        (by simp only [Mem.size_arr64_set64, hX, UInt64.reduceToNat]; omega),
      vpool_stidx0 _ _ _ h41 (by simp only [hX]; omega) (by simp only [hX]; omega),
      vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩]
  have b0 : m.top.toNat < 2199023255552 := by omega
  have b1 : m.top.toNat + 1 < 2199023255552 := by omega
  have b2 : m.top.toNat + 2 < 2199023255552 := by omega
  have b3 : m.top.toNat + 3 < 2199023255552 := by omega
  rw [hv]
  simp only [sliceL, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, vpool_size, e1, e2, e3]
  simp (config := { decide := true }) [b0, b1, b2, b3]

theorem callW_dl {n : Nat} {m m' : Mem} {i : Word} {r : List Word}
    (h : callW nriProg n "dec_len" [i] m = some (r, m')) :
    m' = m ∧ (r.headD 0).toNat = decLenN i.toNat := by
  cases n with
  | zero => exact (callW_zero_false h).elim
  | succ n =>
    obtain ⟨s', hs', -, hm, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (decLen_specW nriProg rfl (n + 1) _ i) h
    refine ⟨hs'.symm.trans hm, ?_⟩
    rw [decLenW.arm1] at hW
    rcases hl : decLenW.loop1 (n + 1) m i 1 with _ | k
    · rw [hl, decLenW.k_loop1.none] at hW; cases hW
    rw [hl, decLenW.k_loop1.arm1, Option.some.injEq] at hW
    rw [← hW]
    have := dlW_ok _ _ _ _ _ hl (by have := decLenN_le i.toNat; have := i.toNat_lt; simp; omega)
    rw [show (1 : Word).toNat = 1 from rfl] at this; have := decLenN_pos i.toNat; omega

/-- **`name_rec_i`'s model refines `internNNode (.str n s!"rec_{i}")`** (replaces
`IndStubs.nameRecI_spec`). -/
theorem nriF_ok (_dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (x i : Word) (hx : H x) :
    RelW nriF [x, i] (StageR vis fe) (internNNode (.str (decI x) s!"rec_{i.toNat}"))
      (KeepPost vis fe decW0N) := by
  intro m m' a r hc hS
  obtain ⟨n', hc'⟩ := callF_run hc
  cases n' with
  | zero => exact (callW_zero_false hc').elim
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (nameRecI_specW nriProg rfl (n + 1) _ x i) hc'
  simp only at hs' hW
  rw [hs', nriW.arm1] at hW
  rcases h1 : callW nriProg n "dec_len" [i] m with _ | ⟨r₁, m₁⟩
  · rw [h1, nriW.k_dec_len.none] at hW; cases hW
  rw [h1, nriW.k_dec_len.arm1] at hW
  obtain ⟨rfl, hk⟩ := callW_dl h1
  generalize r₁.headD 0 = k at hW hk
  rcases h2 : callW nriProg n "pool_room" [k + 4] m₁ with _ | ⟨r₂, m₂⟩
  · rw [h2, nriW.k_pool_room.none] at hW; cases hW
  rw [h2, nriW.k_pool_room.arm1, recIBytes_fold] at hW
  have hpool : PoolOK m₁ := hS.check.arena.base.lit.1
  obtain ⟨ho, hm₂, hno, hroom⟩ := prW_some (callW_pr rfl h2) (by have := hpool.cap; omega)
  rw [ho, hm₂] at hW
  have h41 := hpool.top41
  have hsplit := tag_split m₁.top
  have htier := tag_tier_le m₁.top h41
  have hidx := tag_idx_lt m₁.top
  have hk4 : (k + 4).toNat = k.toNat + 4 := by
    have := decLenN_le i.toNat; have := i.toNat_lt; rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hg, htop, hsz, hb⟩ := recIBytes_ok m₁ hpool (k + 4) (by omega) hroom
  generalize hm₃ : recIBytes (m₁.set64 CTL 0 (m₁.top + (k + 4))) m₁.top = m₃ at hW hg htop hsz hb
  have hj : ((m₁.top &&& 1099511627775) + 4 + k).toNat = (m₁.top &&& 1099511627775).toNat + 4 + k.toNat := by
    have h4 : (4 : Word).toNat = 4 := rfl
    have hkb : k.toNat ≤ 2 ^ 63 := by have := decLenN_le i.toNat; have := i.toNat_lt; omega
    have e : ((m₁.top &&& 1099511627775) + 4).toNat = (m₁.top &&& 1099511627775).toNat + 4 := by
      rw [UInt64.toNat_add, h4]; exact Nat.mod_eq_of_lt (by omega)
    rw [UInt64.toNat_add, e]; exact Nat.mod_eq_of_lt (by omega)
  cases h3 : nriW.loop1 nriProg (n + 1) m₃ ((m₁.top &&& 1099511627775) + 4 + k) i (m₁.top >>> 40)
      (m₁.top &&& 1099511627775) with
  | none => rw [h3, nriW.k_loop1.none] at hW; cases hW
  | some m₄ =>
  rw [h3, nriW.k_loop1.arm1] at hW
  obtain ⟨hg4, htop4, hpc4, hsz4, hkeep4, hsl4⟩ := digW_ok nriProg m₁ hpool m₁.top h41 (Nat.le_refl _) (n + 1) m₃ m₄
    ((m₁.top &&& 1099511627775) + 4 + k) i h3 (by rw [hj]; omega) (by rw [hsz, hj]; omega) hg
  rw [hj, show (m₁.top &&& 1099511627775).toNat + 4 + k.toNat - ((m₁.top &&& 1099511627775).toNat + 4) = k.toNat by omega, hk]
    at hsl4
  have hslice : sliceL (vpool m₄) m₁.top.toNat (k + 4).toNat = strWords s!"rec_{i.toNat}" := by
    rw [hk4, Nat.add_comm k.toNat 4, sliceL_add, strWords_recI, hk, hsl4, ← hb]
    congr 1
    exact sliceL_congr fun t ht => hkeep4 _ (.inl (by omega))
  have hsl : SliceOK m₄ m₁.top (k + 4) := SliceOK.fresh hg4 (htop4.trans htop)
  rcases h4 : callW nriProg n "intern_nstr" [x, m₁.top, k + 4] m₄ with _ | ⟨r₄, m₅⟩
  · rw [h4, nriW.k_intern_nstr.none] at hW; cases hW
  by_cases c : 4294967296 ≤ r₄.headD 0
  · rw [h4, nriW.k_intern_nstr.abort1 _ _ _ c] at hW; cases hW
  rw [h4, nriW.k_intern_nstr.arm1 _ _ _ c] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have hR₄ : ArenaR m₄ a := ArenaR.grow m₁ m₄ hg4 a hS.check.arena.base
  have hmo₄ : ModeOK m₄ := hS.check.mode.grows hg4
  have hpc₄ : pcap m₄ < 2 ^ 64 := by rw [hg4.pcapEq]; have := hpool.cap; omega
  have hcap₄ : m₁.top.toNat + (k + 4).toNat ≤ pcap m₄ := by have := hsl.le; have := hg4.cap; omega
  obtain ⟨s₅, hs₅, -, hok, hR₅, hres⟩ := triple_of_callW
    (internNStr_refinesA nriProg rfl rfl rfl rfl rfl rfl a n ⟨m₄, Locals.init []⟩ x m₁.top (k + 4) hR₄
      hx hsl s!"rec_{i.toNat}" hslice (ModeOK.slice0 hmo₄ hsl)) h4
  obtain ⟨s₅', hs₅', -, hI⟩ := triple_of_callW (s₀ := ⟨m₄, Locals.init []⟩)
    (internNStr_spec nriProg rfl rfl rfl rfl rfl rfl n _ x m₁.top (k + 4) hpc₄ hcap₄) h4
  simp only at hs₅ hR₅ hs₅' hI
  rw [hs₅] at hR₅
  rw [hs₅'] at hI
  have hfr : MemFrame [POOL, POOL1, NSREC, tier1 NSREC, NSSLOT, tier1 NSSLOT] [0, 36, 37] m₁ m₅ :=
    ((grows_frame m₁ m₄ hg4).mono (by simp) (by simp)).trans
      ((consInternM_frame nstrCS_wf hI).mono (by simp [ConsSch.wset, nstrCS]) (by simp [nstrCS]))
  obtain ⟨a', hrun, hS', hg', -, -⟩ := stage_of_name hS
    (internNNode_str_run (decI x) s!"rec_{i.toNat}" a) hok hR₅
    hres hfr (by simp [tier1, POOL, POOL1, NSREC, NSSLOT]) (by simp) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
    (hmo₄.frame (consInternM_frame nstrCS_wf hI) (by simp [nstrCS]) (by simp [nstrCS]))
  rw [hr] at hrun c
  refine ⟨decI (r.headD 0), a', hrun, hS', hg', ?_, rfl⟩
  have := mt UInt64.le_iff_toNat_le.mpr c
  have e : (4294967296 : Word).toNat = 4294967296 := rfl
  rw [e] at this; omega

end L.Ind
