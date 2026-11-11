module

import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.Env
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndCopy2
public import ConAgua.Arena.IndParts
import all ConAgua.Arena.IndParts
import ConAgua.L.ModelGen
import ConAgua.Arena.SimLib
import ConAgua.L.WordOff
import ConAgua.Arena.ErecRd

@[expose] public section

/-!
# MemberNames: `ConRon.Arena.BlockParts.complete`, `ConRon.Arena.BlockShape.lps`, `ConRon.Arena.BlockShape.memberNames`

The refinement theorems `blockShapeMemberNames_refines`, `blockPartsComplete_refines`, `blockShapeLps_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A handle slice whose words decode one by one decodes as the list. -/
theorem decHL_of_get {k : IdxKind} (m : Mem) : ∀ (xs : List (Idx k)) (o : Nat),
    (∀ j (hj : j < xs.length), iwH m (o + j) = some xs[j]) → decHL m o xs.length = some xs
  | [], o, _ => by simp [decHL, hslice?]
  | x :: xs, o, h => by
    have h0 : iwH m o = some x := h 0 (by simp)
    have ih := decHL_of_get m xs (o + 1) (fun j hj => by
      have := h (j + 1) (by simpa using hj)
      have e : o + (j + 1) = o + 1 + j := by omega
      simpa [e] using this)
    show hslice? (iwA m) o (xs.length + 1) = _
    rw [hslice?_succ]
    have ih' : hslice? (iwA m) (o + 1) xs.length = some xs := ih
    have h0' : hd? (iwA m) o = some x := h0
    simp [h0', ih']

/-- **`member_names_copy` is its model `nameCopyW`** (generated). -/
l_model memberNamesCopy_spec (p : Prog) (hp : p.lookup "member_names_copy" = some memberNamesCopy)
  fns [hp ↦ nameCopyW void]
  grind [arena_grind]
/-- `nameCopyW`'s step with its continuation applied (the shape `ipCopyW_get` takes). -/
theorem nameCopyW_step (n : Nat) (m : Mem) (d s l : Word) (hl : l ≠ 0) :
    nameCopyW (n + 1) m d s l =
      nameCopyW n (m.set64 IW d (erRd m (rdW (m.arr64 IW) (rdW (m.arr64 IW) s))))
        (d + 1) (s + 1) (l - 1) := by
  rw [nameCopyW.arm2 n m d s l hl, erRd_foldN]
  cases nameCopyW n _ _ _ _ <;> rfl

/-- **What `member_names_copy` leaves.** -/
theorem nameCopyW_get (n : Nat) : ∀ (m m' : Mem) (d s l : Word), nameCopyW n m d s l = some m' →
    s.toNat + l.toNat ≤ d.toNat → d.toNat + l.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 →
    (∀ j < l.toNat, (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + j))).toNat < d.toNat) →
    (∀ b : TieredArray, b ≠ ↑IW → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 IW).size = (m.arr64 IW).size ∧
    ∀ i, (m'.arr64 IW)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat
      then some (erRd m
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (i - d.toNat))))))
      else (m.arr64 IW)[i]? :=
  ipCopyW_get nameCopyW (fun m x => erRd m (rdW (m.arr64 IW) x)) (fun x d => x.toNat < d)
    (fun _ _ _ _ => by simp [nameCopyW]) (nameCopyW.arm1 · · · · ·) (nameCopyW_step · · · · ·)
    (fun m d v x hx => by rw [erRd_set_iw, rdW_set64_IW_ne m d v x (by omega)])
    (fun _ _ h => by omega) n

/-- **`block_shape_member_names(p)`'s model `memberNamesW`** (generated). -/
l_model blockShapeMemberNames_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hp : p.lookup "block_shape_member_names" = some blockShapeMemberNames)
  fns [hp ↦ memberNamesW list]
  specs [iwAlloc_specW p ha n, memberNamesCopy_spec p hc n]
  grind [arena_grind]

/-- A run of `memberNamesW`: the allocation, then the copy into it. -/
theorem memberNamesW_inv {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : memberNamesW n m p = some (r, m')) : ∃ k q m1, n = k + 1 ∧
      allocW m (rdW (m.arr64 IW) (p + 1)) = some (q, m1) ∧
      nameCopyW k m1 q (rdW (m.arr64 IW) p) (rdW (m.arr64 IW) (p + 1)) = some m' ∧
      r = [q, rdW (m.arr64 IW) (p + 1)] := by
  rcases n with _ | k
  · simp [memberNamesW] at h
  rw [memberNamesW.arm1] at h
  obtain ⟨⟨q, m1⟩, hal, h⟩ := of_K h (memberNamesW.k_iw_alloc.none ..)
  rw [memberNamesW.k_iw_alloc.arm1] at h
  obtain ⟨m2, hc, h⟩ := of_K h (memberNamesW.k_member_names_copy.none ..)
  rw [memberNamesW.k_member_names_copy.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨k, q, m1, rfl, hal, hc, rfl⟩

theorem memberNamesW_dec {n : Nat} {m m' : Mem} {p : Word} {r : List Word} {bs : BlockShape}
    (h : memberNamesW n m p = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hq : decBS m p.toNat = some bs)
    (hb : p.toNat + 9 < 2 ^ 64)
    (hsrc : ∀ o l, iwN m p.toNat = some o → iwN m (p.toNat + 1) = some l → o + l ≤ iwTop m)
    (hptr : ∀ o l j v, iwN m p.toNat = some o → iwN m (p.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v < iwTop m) :
    r = [rdW (m.arr64 CTL) 200, UInt64.ofNat bs.k] ∧
    decHL m' (rdW (m.arr64 CTL) 200).toNat bs.k = some bs.memberNames ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
    (rdW (m.arr64 CTL) 200).toNat + bs.k = iwTop m' := by
  obtain ⟨o, l, ho, hl, hg⟩ := decAt_some (decBS_some hq).1
  have hlen := decPL_length m hg
  have hk : bs.k = l := by rw [BlockShape.k, hlen]
  obtain ⟨ho', hob⟩ := iwN_rdW ho (by omega)
  obtain ⟨hl', hlb⟩ := iwN_rdW hl (by omega)
  have e1 : UInt64.ofNat (p.toNat + 1) = p + 1 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  rw [L.ofNat_toNat] at ho'
  rw [e1] at hl'
  have hoo : (UInt64.ofNat o).toNat = o := by simp [hob]
  have hll : (UInt64.ofNat l).toNat = l := by simp [hlb]
  have hsrc' := hsrc o l ho hl
  have htl : iwTop m < 2 ^ 64 := UInt64.toNat_lt _
  obtain ⟨k, q, m1, rfl, hal, hcp, rfl⟩ := memberNamesW_inv h
  simp only [ho', hl'] at hal hcp ⊢
  obtain ⟨hq', hm1, hroom⟩ := allocW_facts hal hsz
  rw [hll] at hroom
  subst hq' hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hIW := allocMem_IW m (UInt64.ofNat l)
  have hRR : ∀ a, erRd (allocMem m (UInt64.ofNat l)) a = erRd m a := fun a => by
    simp only [allocMem, erRd]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by rw [tierA_EREC]; split <;> decide)]
  have hptr' : ∀ j < (UInt64.ofNat l).toNat,
      (rdW ((allocMem m (UInt64.ofNat l)).arr64 IW) (UInt64.ofNat ((UInt64.ofNat o).toNat + j))).toNat
        < q.toNat := by
    intro j hj
    rw [hll] at hj
    obtain ⟨v, y, hv, -, -⟩ := decPL_get l o bs.members hg j hj
    have hvb := hptr o l j v ho hl hj hv
    obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
    rw [hIW, hoo, hv']
    simp only [iwTop, hqq] at hvb
    rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; exact hvb
  obtain ⟨hA, hS, hG⟩ := nameCopyW_get k _ _ _ _ _ hcp
    (by rw [hoo, hll]; simp only [iwTop, hqq] at hsrc'; omega)
    (by rw [hIW, hll]; exact hroom) (by rw [hIW]; exact hsz) hptr'
  rw [hIW] at hS hG
  simp only [hRR] at hG
  have hfr : MemFrame [IW] [200] m m' :=
    (allocMem_frame m _).trans (copy_frame hA (by rw [hS, hIW]))
  have htop : rdW (m'.arr64 CTL) 200 = q + UInt64.ofNat l := by
    rw [hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + UInt64.ofNat l).toNat = q.toNat + l := by
    rw [UInt64.toNat_add]; simp [hll]; omega
  refine ⟨by rw [hk], ?_, ?_, hfr, ?_⟩
  · rw [hk]
    have hxs : bs.memberNames.length = l := by simp [BlockShape.memberNames, hlen]
    have := decHL_of_get m' bs.memberNames q.toNat (fun j hj => by
      have hj' : j < l := by omega
      obtain ⟨v, y, hv, hy, hget⟩ := decPL_get l o bs.members hg j hj'
      obtain ⟨⟨a, hva, hcv⟩, -, -⟩ := decMS_some hy
      have hGj := hG (q.toNat + j)
      rw [ite_eq_left (by rw [hll]; omega)] at hGj
      have e2 : q.toNat + j - q.toNat = j := by omega
      rw [e2, hoo] at hGj
      have hvb := hptr o l j v ho hl hj' hv
      obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
      rw [hv'] at hGj
      obtain ⟨hva', hab⟩ := iwN_rdW hva (by omega)
      rw [hva'] at hGj
      simp only [decCVp, decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcv
      obtain ⟨nm, hnm, lv, -, ce, -, hcvT⟩ := hcv
      have hnmE : nm = y.cvT.name := by rw [← hcvT]
      obtain ⟨w, hw, hwl', hnm'⟩ : ∃ w, erecP m a = some w ∧ w.toNat < 2 ^ 32 ∧ decI w = nm := by
        rcases hw : erecP m a with _ | w
        · simp [hd?, erA, hw] at hnm
        by_cases hwl : w.toNat < 2 ^ 32
        · refine ⟨w, rfl, hwl, ?_⟩
          simp [hd?, erA, hw, hwl] at hnm
          simp [hnm]
        · simp [hd?, erA, hw, hwl] at hnm
      have hrd : erRd m (UInt64.ofNat a) = w := by
        have : (UInt64.ofNat a).toNat = a := by have := erecP_lt64 hw; simp; omega
        exact (erRd_of_erecP (by rw [this]; exact hw)).1
      rw [hrd] at hGj
      have hy' : bs.members[j]'(by omega) = y := by
        simpa [List.getElem?_eq_getElem (show j < bs.members.length by omega)] using hget
      have hnmj : bs.memberNames[j] = nm := by
        simp [BlockShape.memberNames, List.getElem_map, hy', hnmE]
      rw [hnmj]
      simp only [iwH, hd?, iwA, aread_apply, hGj]
      simp [hwl', hnm'])
    rw [hxs] at this
    exact this
  · refine iwGrow_of_frame hfr (N := UInt64.ofNat l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq, hll]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, ite_eq_right (by omega)]
  · simp only [iwTop, htop, hsum, hk]

/-- **`block_shape_member_names` is `BlockShape.memberNames`**: the new `IW` slice holds the
members' names. -/
@[refines ConRon.Arena.BlockShape.memberNames]
theorem blockShapeMemberNames_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hp : p.lookup "block_shape_member_names" = some blockShapeMemberNames) (n : Nat) (s₀ : St)
    (q : Word) (bs : BlockShape) (hq : decBS s₀.mem q.toNat = some bs) (hb : q.toNat + 9 < 2 ^ 64)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hcl : 200 < (s₀.mem.arr64 CTL).size)
    (hsrc : ∀ o l, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l →
      o + l ≤ iwTop s₀.mem)
    (hptr : ∀ o l j v, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l → j < l →
      iwN s₀.mem (o + j) = some v → v < iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_member_names" [q]
    ⦃fun r s' => r = [rdW (s₀.mem.arr64 CTL) 200, UInt64.ofNat bs.k] ∧
      decHL s'.mem (rdW (s₀.mem.arr64 CTL) 200).toNat bs.k = some bs.memberNames ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem ∧
      (rdW (s₀.mem.arr64 CTL) 200).toNat + bs.k = iwTop s'.mem; ⊤⦄ := by
  refine triple_post (blockShapeMemberNames_spec p ha hc hp n s₀ q) ?_
  intro r s' ⟨_, h⟩
  exact memberNamesW_dec h hsz hcl hq hb hsrc hptr

/-! ## `BlockParts.complete` -/

/-! ## `BlockShape.lps` -/

/-- A successful handle slice read is in bounds. -/
theorem hslice?_bound {k : IdxKind} (a : Array Word) : ∀ (c o : Nat) (xs : List (Idx k)),
    hslice? (aread a) o c = some xs → 0 < c → o + c ≤ a.size
  | 0, o, xs, h, hc => absurd hc (by omega)
  | c + 1, o, xs, h, _ => by
    rw [hslice?_succ] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, ys, hys, rfl⟩ := h
    have h2 : o < a.size := by
      cases hw : a[o]? with
      | none => simp [hd?, aread_apply, hw] at hx
      | some w => exact (Array.getElem?_eq_some_iff.mp hw).1
    cases c with
    | zero => omega
    | succ c =>
      have h1 := hslice?_bound a (c + 1) (o + 1) ys hys (by omega)
      omega

/-- Copying zero words reads no source: the source offset is irrelevant. -/
theorem erToIwW_src0 {n : Nat} {m : Mem} {o l : Word} (hl : l = 0) :
    erToIwW n m o l = erToIwW n m 0 l := by
  subst hl
  have : ∀ k m1 q, erCopyW k m1 q o 0 = erCopyW k m1 q 0 0 := by
    intro k m1 q; cases k <;> simp [erCopyW]
  simp only [erToIwW, this]

/-- The pool's top stays within the pool: what a callee that only allocates keeps of `IWOK`. -/
def IWRoom (m m' : Mem) : Prop := iwTop m ≤ (m.arr64 IW).size → iwTop m' ≤ (m'.arr64 IW).size

theorem IWRoom.refl (m : Mem) : IWRoom m m := fun h => h

theorem IWRoom.trans {m₁ m₂ m₃ : Mem} (h₁ : IWRoom m₁ m₂) (h₂ : IWRoom m₂ m₃) : IWRoom m₁ m₃ :=
  fun h => h₂ (h₁ h)

/-- An allocation ending at the new top, within the old pool, the size kept. -/
theorem IWRoom.of_alloc {m m' : Mem} {A : List TieredArray} {C : List Word} (hf : MemFrame A C m m')
    {t : Nat} (ht : t = iwTop m') (hroom : t ≤ (m.arr64 IW).size) : IWRoom m m' :=
  fun _ => by rw [hf.size IW, ← ht]; exact hroom

theorem erToIwW_room {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : erToIwW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (rdW (m.arr64 CTL) 200).toNat + l.toNat ≤ (m.arr64 IW).size := by
  simp only [erToIwW] at h
  rcases hal : allocW m l with _ | ⟨q, m1⟩
  · simp [hal] at h
  obtain ⟨hq, -, hroom⟩ := allocW_facts hal hsz
  rw [← hq]; exact hroom

/-- **`erToIwW_dec` when the slice decodes**: a successful `hslice?` of the source already bounds it
(a nonempty slice lies in `EREC`; an empty one reads nothing). -/
theorem erToIwW_decS {k : IdxKind} {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    {xs : List (Idx k)}
    (h : erToIwW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (_hE : (m.arr64 EREC).size < 2 ^ 64)
    (hsl : hslice? (erA m) o.toNat l.toNat = some xs) :
    r = [rdW (m.arr64 CTL) 200, l] ∧
    (decHL m' (rdW (m.arr64 CTL) 200).toNat l.toNat : Option (List (Idx k))) =
      hslice? (erA m) o.toNat l.toNat ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ m'.arr64 EREC = m.arr64 EREC ∧
    (rdW (m.arr64 CTL) 200).toNat + l.toNat = iwTop m' ∧ IWRoom m m' := by
  have hroom := erToIwW_room h hsz
  have hd : r = [rdW (m.arr64 CTL) 200, l] ∧
      (decHL m' (rdW (m.arr64 CTL) 200).toNat l.toNat : Option (List (Idx k))) =
        hslice? (erA m) o.toNat l.toNat ∧
      IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ m'.arr64 EREC = m.arr64 EREC ∧
      (rdW (m.arr64 CTL) 200).toNat + l.toNat = iwTop m' := by
    rw [hsl]; exact erToIwW_dec (k := k) h hsz hc hsl
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd
  exact ⟨h1, h2, h3, h4, h5, h6, IWRoom.of_alloc h4 h6 hroom⟩

theorem erToIwW_two {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : erToIwW n m o l = some (r, m')) : r = [r.headD 0, r.tail.headD 0] := by
  simp only [erToIwW] at h
  rcases hal : allocW m l with _ | ⟨q, m1⟩
  · simp [hal] at h
  simp only [hal] at h
  rcases hcp : erCopyW (n - 1) m1 q o l with _ | m2
  · simp [hcp] at h
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  rfl

/-- `er_to_iw`'s spec with the result's shape (two words) spelt out. -/
theorem erToIw_specW2 (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (hp : p.lookup "er_to_iw" = some erToIw) (n : Nat)
    (s₀ : St) (o l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "er_to_iw" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ erToIwW n s₀.mem o l = some (r, s'.mem) ∧
      r = [r.headD 0, r.tail.headD 0]; ⊤⦄ :=
  triple_post (erToIw_specW p ha hc hp n s₀ o l) (fun _r _s' ⟨h1, h2⟩ => ⟨h1, h2, erToIwW_two h2⟩)

/-- The model of `block_shape_lps` (its callee runs at `n - 1`). -/
def lpsW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, p =>
    if rdW (m.arr64 IW) (p + 1) = 0 then some ([0, 0], m)
    else erToIwW n m
      (erRd m (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) + 1))
      (erRd m (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) + 2))

section arms
variable (n : Nat) (m : Mem) (p : Word)
theorem lpsW_nil (h : rdW (m.arr64 IW) (p + 1) = 0) : lpsW (n + 1) m p = some ([0, 0], m) := by
  simp [lpsW, h]
theorem lpsW_cons (h : rdW (m.arr64 IW) (p + 1) ≠ 0) : lpsW (n + 1) m p =
    erToIwW n m
      (erRd m (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) + 1))
      (erRd m (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) + 2)) := by
  simp [lpsW, h]
end arms

grind_pattern [ind_grind] lpsW_nil => lpsW (n + 1) m p
grind_pattern [ind_grind] lpsW_cons => lpsW (n + 1) m p

theorem blockShapeLps_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
    (hp : p.lookup "block_shape_lps" = some blockShapeLps) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_shape_lps" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ lpsW n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeLps]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        erToIw_specW2 p ha hc he n] <;>
      finish (gen := 20) [rdW_eq, erRd]

theorem lpsW_dec {n : Nat} {m m' : Mem} {p : Word} {r : List Word} {bs : BlockShape}
    (h : lpsW n m p = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hE : (m.arr64 EREC).size < 2 ^ 64)
    (hq : decBS m p.toNat = some bs) (hb : p.toNat + 9 < 2 ^ 64) :
    r = [r.headD 0, r.tail.headD 0] ∧
    decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some bs.lps ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
    (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ IWRoom m m' := by
  obtain ⟨o, l, ho, hl, hg⟩ := decAt_some (decBS_some hq).1
  have hlen := decPL_length m hg
  obtain ⟨ho', hob⟩ := iwN_rdW ho (by omega)
  obtain ⟨hl', hlb⟩ := iwN_rdW hl (by omega)
  have e1 : UInt64.ofNat (p.toNat + 1) = p + 1 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  rw [L.ofNat_toNat] at ho'
  rw [e1] at hl'
  cases n with
  | zero => simp [lpsW] at h
  | succ n =>
  by_cases hl0 : l = 0
  · have hz : rdW (m.arr64 IW) (p + 1) = 0 := by rw [hl', hl0]; rfl
    rw [lpsW_nil n m p hz] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hms : bs.members = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨rfl, ?_, IWGrow.refl m, MemFrame.refl _ _ m, by simp, IWRoom.refl m⟩
    simp [BlockShape.lps, hms, decHL, hslice?]
  · have hz : rdW (m.arr64 IW) (p + 1) ≠ 0 := by
      rw [hl']; intro h0
      apply hl0
      have := congrArg UInt64.toNat h0
      simp [UInt64.toNat_ofNat_of_lt' (show l < UInt64.size by rw [UInt64_size_eq]; exact hlb)] at this
      exact this
    rw [lpsW_cons n m p hz] at h
    obtain ⟨v, y, hv, hy, hget⟩ := decPL_get l o bs.members hg 0 (by omega)
    obtain ⟨⟨a, hva, hcv⟩, -, -⟩ := decMS_some hy
    have hmem : bs.members = y :: bs.members.tail := by
      cases hm : bs.members with
      | nil => rw [hm] at hlen; simp at hlen; omega
      | cons y0 ys => rw [hm] at hget; simp at hget; rw [hget]; rfl
    have hlps : bs.lps = y.cvT.levelParams := by unfold BlockShape.lps; rw [hmem]
    replace hv : iwN m o = some v := by simpa using hv
    obtain ⟨hv', hvb⟩ := iwN_rdW hv (by omega)
    obtain ⟨hva', hab⟩ := iwN_rdW hva (by omega)
    have hcv' := hcv
    simp only [decCVp, decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcv'
    obtain ⟨nm, -, lv, hlv, ce, -, hcvT⟩ := hcv'
    have hlvE : lv = y.cvT.levelParams := by rw [← hcvT]
    simp only [hlist?, bind, Option.bind_eq_some_iff] at hlv
    obtain ⟨o', ho2, l', hl2, hsl⟩ := hlv
    simp only [nat?, erA, Option.map_eq_some_iff] at ho2 hl2
    obtain ⟨w1, hw1, rfl⟩ := ho2
    obtain ⟨w2, hw2, rfl⟩ := hl2
    have hi1 : a + 1 < 2 ^ 64 := erecP_lt64 hw1
    have hi2 : a + 2 < 2 ^ 64 := erecP_lt64 hw2
    have hrd1 : erRd m (UInt64.ofNat (a + 1)) = w1 := by
      have : (UInt64.ofNat (a + 1)).toNat = a + 1 := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
      exact L.Arena.erRd_of _ _ (by rw [this]; exact hw1)
    have hrd2 : erRd m (UInt64.ofNat (a + 2)) = w2 := by
      have : (UInt64.ofNat (a + 2)).toNat = a + 2 := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
      exact L.Arena.erRd_of _ _ (by rw [this]; exact hw2)
    have e3 : UInt64.ofNat a + 1 = UInt64.ofNat (a + 1) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
    have e4 : UInt64.ofNat a + 2 = UInt64.ofNat (a + 2) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
    have hv'' : rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) = UInt64.ofNat a := by
      rw [ho', hv']; exact hva'
    rw [hv'', e3, e4, hrd1, hrd2] at h
    obtain ⟨hr, hdec, hgrow, hfr, -, htp, hroom⟩ := erToIwW_decS (k := IdxKind.name) h hsz hc hE hsl
    have hh := erToIwW_two h
    refine ⟨hh, ?_, hgrow, hfr, ?_, hroom⟩
    · rw [hr] at hh ⊢
      simp only [List.headD_cons, List.tail_cons]
      rw [hdec, hlps, ← hlvE]
      exact hsl
    · rw [hr]; simp only [List.headD_cons, List.tail_cons]; omega

/-- **`block_shape_lps` is `BlockShape.lps`**: a fresh `IW` copy of member 0's level parameters. -/
@[refines ConRon.Arena.BlockShape.lps]
theorem blockShapeLps_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
    (hp : p.lookup "block_shape_lps" = some blockShapeLps) (n : Nat) (s₀ : St) (q : Word)
    (bs : BlockShape) (hq : decBS s₀.mem q.toNat = some bs) (hb : q.toNat + 9 < 2 ^ 64)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hcl : 200 < (s₀.mem.arr64 CTL).size)
    (hE : (s₀.mem.arr64 EREC).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_lps" [q]
    ⦃fun r s' => r = [r.headD 0, r.tail.headD 0] ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat = some bs.lps ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧ IWRoom s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (blockShapeLps_spec p ha hc he hp n s₀ q) ?_
  intro r s' ⟨_, h⟩
  exact lpsW_dec h hsz hcl hE hq hb

end L.Ind

end
