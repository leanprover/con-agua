import ConAgua.Arena.IndPartsSpec

/-!
# Refinements of `IndParts`, part 2 (lane `indproofs`, helper `parts`)

`BlockShape.memberNames` (a copy with two indirections, the last into `EREC`) and the
functions built on the record projections.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

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

/-- A write at a position other than `d` does not change the read at another position. -/
theorem rdW_set64_IW_ne (m : Mem) (d v x : Word) (h : x.toNat ≠ d.toNat) :
    rdW ((m.set64 IW d v).arr64 IW) x = rdW (m.arr64 IW) x := by
  simp only [rdW]
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [Ne.symm h]

/-- The model of `member_names_copy`. -/
def nameCopyW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, d, s, l =>
    if l = 0 then some m
    else nameCopyW n
      (m.set64 IW d (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) s)))) (d + 1) (s + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (d s l : Word)
theorem nameCopyW_nil (hl : l = 0) : nameCopyW (n + 1) m d s l = some m := by
  simp [nameCopyW, hl]
theorem nameCopyW_step (hl : l ≠ 0) :
    nameCopyW (n + 1) m d s l =
      nameCopyW n (m.set64 IW d (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) s))))
        (d + 1) (s + 1) (l - 1) := by
  simp [nameCopyW, hl]
end arms

grind_pattern [ind_grind] nameCopyW_nil => nameCopyW (n + 1) m d s l
grind_pattern [ind_grind] nameCopyW_step => nameCopyW (n + 1) m d s l

theorem memberNamesCopy_spec (p : Prog) (hp : p.lookup "member_names_copy" = some memberNamesCopy)
    (n : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "member_names_copy" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ nameCopyW n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ d s l; rw [invoke_eq _ hp]; simp only [callFn, memberNamesCopy]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ d s l
    rw [invoke_eq _ hp]
    simp only [callFn, memberNamesCopy]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20)

/-- **What `member_names_copy` leaves.** -/
theorem nameCopyW_get (n : Nat) : ∀ (m m' : Mem) (d s l : Word), nameCopyW n m d s l = some m' →
    s.toNat + l.toNat ≤ d.toNat → d.toNat + l.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 →
    (∀ j < l.toNat, (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + j))).toNat < d.toNat) →
    (∀ b, b ≠ IW → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 IW).size = (m.arr64 IW).size ∧
    m'.words.size = m.words.size ∧
    ∀ i, (m'.arr64 IW)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat
      then some (rdW (m.arr64 EREC)
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (i - d.toNat))))))
      else (m.arr64 IW)[i]? := by
  induction n with
  | zero => intro m m' d s l h; simp [nameCopyW] at h
  | succ n ih =>
    intro m m' d s l h hsd hd hsz hptr
    by_cases hl : l = 0
    · rw [nameCopyW_nil n m d s l hl] at h
      cases h
      subst hl
      refine ⟨fun _ _ => rfl, rfl, rfl, fun i => ?_⟩
      have : ¬ (d.toNat ≤ i ∧ i < d.toNat + (0 : Word).toNat) := by
        simp only [UInt64.toNat_zero]; omega
      simp only [this, if_false]
    · rw [nameCopyW_step n m d s l hl] at h
      have hl0 : 0 < l.toNat := by
        have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      have hl1 : (l - 1).toNat = l.toNat - 1 := by rw [UInt64.toNat_sub]; simp; omega
      have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hs1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hslt : s.toNat < (m.arr64 IW).size := by omega
      have hdlt : d.toNat < (m.arr64 IW).size := by omega
      have hp0 : (rdW (m.arr64 IW) s).toNat < d.toNat := by
        have := hptr 0 hl0; simpa using this
      obtain ⟨v, hv⟩ : ∃ v : Word,
          v = rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) s)) := ⟨_, rfl⟩
      rw [← hv] at h
      obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.set64 IW d v := ⟨_, rfl⟩
      rw [← hm1] at h
      have hsz1 : (m1.arr64 IW).size = (m.arr64 IW).size := by
        rw [hm1, Mem.arr64_set64_same]; simp
      have hE1 : m1.arr64 EREC = m.arr64 EREC := by
        rw [hm1, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
      have hm1get : ∀ i, (m1.arr64 IW)[i]? = if i = d.toNat then some v else (m.arr64 IW)[i]? := by
        intro i
        rw [hm1, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        by_cases hi : d.toNat = i
        · subst hi; simp only [hdlt, true_and, if_true]
        · simp [hi, Ne.symm hi]
      have hrd : ∀ x : Word, x.toNat ≠ d.toNat → rdW (m1.arr64 IW) x = rdW (m.arr64 IW) x := by
        intro x hx; rw [hm1]; exact rdW_set64_IW_ne m d v x hx
      have hptr1 : ∀ j < (l - 1).toNat,
          (rdW (m1.arr64 IW) (UInt64.ofNat ((s + 1).toNat + j))).toNat < (d + 1).toNat := by
        intro j hj
        have hj' : j + 1 < l.toNat := by rw [hl1] at hj; omega
        have hbase := hptr (j + 1) hj'
        have e1 : (s + 1).toNat + j = s.toNat + (j + 1) := by omega
        have hidx : (UInt64.ofNat (s.toNat + (j + 1))).toNat = s.toNat + (j + 1) :=
          UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
        rw [e1, hrd _ (by rw [hidx]; omega), hd1]; omega
      obtain ⟨hA, hS, hW, hG⟩ := ih m1 m' (d + 1) (s + 1) (l - 1) h
        (by rw [hs1, hd1, hl1]; omega) (by rw [hd1, hl1, hsz1]; omega) (by rw [hsz1]; exact hsz)
        hptr1
      refine ⟨fun b hb => (hA b hb).trans ?_, hS.trans hsz1, hW.trans ?_, fun i => ?_⟩
      · rw [hm1, Mem.arr64_set64_ne _ _ _ _ _ hb]
      · rw [hm1]; exact Mem.words_size_set64 _ _ _ _
      · rw [hG i, hd1, hl1, hs1, hE1]
        by_cases hi : d.toNat ≤ i ∧ i < d.toNat + l.toNat
        · rw [if_pos hi]
          by_cases hid : i = d.toNat
          · subst hid
            have hnot : ¬ (d.toNat + 1 ≤ d.toNat ∧ d.toNat < d.toNat + 1 + (l.toNat - 1)) := by omega
            rw [if_neg hnot]
            have e3 : s.toNat + (d.toNat - d.toNat) = s.toNat := by omega
            rw [e3, ofNat_toNat_word, hm1get, if_pos rfl, hv]
          · have h2 : d.toNat + 1 ≤ i ∧ i < d.toNat + 1 + (l.toNat - 1) := by omega
            rw [if_pos h2]
            have e4 : s.toNat + 1 + (i - (d.toNat + 1)) = s.toNat + (i - d.toNat) := by omega
            rw [e4]
            have hidx2 : (UInt64.ofNat (s.toNat + (i - d.toNat))).toNat = s.toNat + (i - d.toNat) :=
              UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
            have hb2 := hptr (i - d.toNat) (by omega)
            have e5 : rdW (m1.arr64 IW) (UInt64.ofNat (s.toNat + (i - d.toNat))) =
                rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (i - d.toNat))) :=
              hrd _ (by rw [hidx2]; omega)
            rw [e5, hrd _ (by omega)]
        · rw [if_neg hi, if_neg (by omega), hm1get, if_neg (by omega)]


/-- The model of `block_shape_member_names`. -/
def memberNamesW (n : Nat) (m : Mem) (p : Word) : Option (List Word × Mem) :=
  match allocW m (rdW (m.arr64 IW) (p + 1)) with
  | none => none
  | some (q, m1) =>
    match nameCopyW (n - 1) m1 q (rdW (m.arr64 IW) p) (rdW (m.arr64 IW) (p + 1)) with
    | none => none
    | some m2 => some ([q, rdW (m.arr64 IW) (p + 1)], m2)

theorem blockShapeMemberNames_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hp : p.lookup "block_shape_member_names" = some blockShapeMemberNames) (n : Nat) (s₀ : St)
    (q : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_shape_member_names" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ memberNamesW n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeMemberNames]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hmod : ∀ a m1 m2, allocW s₀.mem (rdW (s₀.mem.arr64 IW) (q + 1)) = some (a, m1) →
        nameCopyW n m1 a (rdW (s₀.mem.arr64 IW) q) (rdW (s₀.mem.arr64 IW) (q + 1)) = some m2 →
        memberNamesW (n + 1) s₀.mem q = some ([a, rdW (s₀.mem.arr64 IW) (q + 1)], m2) := by
      intro a m1 m2 h1 h2
      simp [memberNamesW, h1, h2]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n, memberNamesCopy_spec p hc n] <;>
      finish (gen := 20)

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
  rw [ofNat_toNat_word] at ho'
  rw [e1] at hl'
  have hoo : (UInt64.ofNat o).toNat = o := by simp [hob]
  have hll : (UInt64.ofNat l).toNat = l := by simp [hlb]
  have hsrc' := hsrc o l ho hl
  have htl : iwTop m < 2 ^ 64 := UInt64.toNat_lt _
  simp only [memberNamesW, ho', hl'] at h
  cases hal : allocW m (UInt64.ofNat l) with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq', hm1, hroom⟩ := allocW_facts hal hsz
  rw [hll] at hroom
  simp only [hal] at h
  cases hcp : nameCopyW (n - 1) m1 q (UInt64.ofNat o) (UInt64.ofNat l) with
  | none => simp [hcp] at h
  | some m2 =>
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq' hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hIW := allocMem_IW m (UInt64.ofNat l)
  have hEE : (allocMem m (UInt64.ofNat l)).arr64 EREC = m.arr64 EREC := by
    simp only [allocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
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
  obtain ⟨hA, hS, hW, hG⟩ := nameCopyW_get (n - 1) _ _ _ _ _ hcp
    (by rw [hoo, hll]; simp only [iwTop, hqq] at hsrc'; omega)
    (by rw [hIW, hll]; exact hroom) (by rw [hIW]; exact hsz) hptr'
  rw [hIW] at hS hG
  rw [hEE] at hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m _).trans (copy_frame hA (by rw [hS, hIW]) hW)
  have htop : rdW (m2.arr64 CTL) 200 = q + UInt64.ofNat l := by
    rw [hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + UInt64.ofNat l).toNat = q.toNat + l := by
    rw [UInt64.toNat_add]; simp [hll]; omega
  refine ⟨by rw [hk], ?_, ?_, hfr, ?_⟩
  · rw [hk]
    have hxs : bs.memberNames.length = l := by simp [BlockShape.memberNames, hlen]
    have := decHL_of_get m2 bs.memberNames q.toNat (fun j hj => by
      have hj' : j < l := by omega
      obtain ⟨v, y, hv, hy, hget⟩ := decPL_get l o bs.members hg j hj'
      obtain ⟨⟨a, hva, hcv⟩, -, -⟩ := decMS_some hy
      have hGj := hG (q.toNat + j)
      rw [if_pos (by rw [hll]; omega)] at hGj
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
      obtain ⟨w, hw, hwl', hnm'⟩ : ∃ w, (m.arr64 EREC)[a]? = some w ∧ w.toNat < 2 ^ 32 ∧ decI w = nm := by
        cases hw : (m.arr64 EREC)[a]? with
        | none => simp [hd?, erA, hw] at hnm
        | some w =>
          by_cases hwl : w.toNat < 2 ^ 32
          · refine ⟨w, rfl, hwl, ?_⟩
            simp [hd?, erA, hw, hwl] at hnm
            simp [hnm]
          · simp [hd?, erA, hw, hwl] at hnm
      have hrd : rdW (m.arr64 EREC) (UInt64.ofNat a) = w := by
        have : (UInt64.ofNat a).toNat = a := by simp; omega
        simp [rdW, this, hw]
      rw [hrd] at hGj
      have hy' : bs.members[j]'(by omega) = y := by
        simpa [List.getElem?_eq_getElem (show j < bs.members.length by omega)] using hget
      have hnmj : bs.memberNames[j] = nm := by
        simp [BlockShape.memberNames, List.getElem_map, hy', hnmE]
      rw [hnmj]
      simp only [iwH, hd?, iwA, hGj, hwl', if_true, Option.bind_some, hnm']
      simp [hwl', hnm'])
    rw [hxs] at this
    exact this
  · refine iwGrow_of_frame hfr (N := UInt64.ofNat l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq, hll]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, if_neg (by omega)]
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

end L.Ind
