import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

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
      else (m.arr64 IW)[i]? :=
  ipCopyW_get nameCopyW (fun m x => rdW (m.arr64 EREC) (rdW (m.arr64 IW) x)) (fun x d => x.toNat < d)
    (fun _ _ _ _ => by simp [nameCopyW]) (nameCopyW_nil · · · · ·) (nameCopyW_step · · · · ·)
    (fun m d v x hx => by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), rdW_set64_IW_ne m d v x (by omega)])
    (fun _ _ h => by omega) n

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
  rcases hal : allocW m (UInt64.ofNat l) with _ | ⟨q, m1⟩
  · simp [hal] at h
  obtain ⟨hq', hm1, hroom⟩ := allocW_facts hal hsz
  rw [hll] at hroom
  simp only [hal] at h
  rcases hcp : nameCopyW (n - 1) m1 q (UInt64.ofNat o) (UInt64.ofNat l) with _ | m2
  · simp [hcp] at h
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
      obtain ⟨w, hw, hwl', hnm'⟩ : ∃ w, (m.arr64 EREC)[a]? = some w ∧ w.toNat < 2 ^ 32 ∧ decI w = nm := by
        rcases hw : (m.arr64 EREC)[a]? with _ | w
        · simp [hd?, erA, hw] at hnm
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
      simp only [iwH, hd?, iwA, hGj]
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

/-- **`block_parts_complete` is `BlockParts.complete`**: the identity on the shape pointer
(`BlockParts` and its shape share one pointer). -/
@[refines ConRon.Arena.BlockParts.complete]
theorem blockPartsComplete_refines (p : Prog)
    (hp : p.lookup "block_parts_complete" = some blockPartsComplete) (n : Nat) (s₀ : St)
    (p0 p1 : Word) (b0 : BlockParts) (bs : BlockShape) (h1 : decBS s₀.mem p1.toNat = some bs) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_parts_complete" [p0, p1]
    ⦃fun r s' => s' = s₀ ∧ r.headD 0 = p1 ∧
      decBP s₀.mem (r.headD 0).toNat = some (BlockParts.complete b0 bs); ⊤⦄ := by
  have hd : decBP s₀.mem p1.toNat = some (BlockParts.complete b0 bs) := by
    simp [decBP, h1, BlockParts.complete]
  rw [invoke_eq _ hp]
  simp only [callFn, blockPartsComplete]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
      finish [Sig.retVal, Locals.init]

/-! ## `BlockShape.lps` -/

/-- A successful handle slice read is in bounds. -/
theorem hslice?_bound {k : IdxKind} (a : Array Word) : ∀ (c o : Nat) (xs : List (Idx k)),
    hslice? a o c = some xs → 0 < c → o + c ≤ a.size
  | 0, o, xs, h, hc => absurd hc (by omega)
  | c + 1, o, xs, h, _ => by
    rw [hslice?_succ] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, ys, hys, rfl⟩ := h
    have h2 : o < a.size := by
      cases hw : a[o]? with
      | none => simp [hd?, hw] at hx
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
theorem IWRoom.of_alloc {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    {t : Nat} (ht : t = iwTop m') (hroom : t ≤ (m.arr64 IW).size) : IWRoom m m' :=
  fun _ => by rw [hf.2.2.1 IW, ← ht]; exact hroom

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
    (hc : 200 < (m.arr64 CTL).size) (hE : (m.arr64 EREC).size < 2 ^ 64)
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
    by_cases hl : l = 0
    · rw [erToIwW_src0 hl] at h
      have := erToIwW_dec (k := k) h hsz hc hE (by subst hl; simp)
      subst hl
      simpa [hslice?] using this
    · have hl0 : 0 < l.toNat := by
        have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      exact erToIwW_dec h hsz hc hE (hslice?_bound _ _ _ _ hsl hl0)
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
      (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) + 1))
      (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) + 2))

section arms
variable (n : Nat) (m : Mem) (p : Word)
theorem lpsW_nil (h : rdW (m.arr64 IW) (p + 1) = 0) : lpsW (n + 1) m p = some ([0, 0], m) := by
  simp [lpsW, h]
theorem lpsW_cons (h : rdW (m.arr64 IW) (p + 1) ≠ 0) : lpsW (n + 1) m p =
    erToIwW n m
      (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) + 1))
      (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) + 2)) := by
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
      finish (gen := 20) [rdW_eq]

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
  rw [ofNat_toNat_word] at ho'
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
    have hi1 := (Array.getElem?_eq_some_iff.mp hw1).1
    have hi2 := (Array.getElem?_eq_some_iff.mp hw2).1
    replace hi1 : a + 1 < (m.arr64 EREC).size := hi1
    replace hi2 : a + 2 < (m.arr64 EREC).size := hi2
    have e2 : ∀ k : Nat, k < 2 ^ 64 → UInt64.ofNat a + UInt64.ofNat k = UInt64.ofNat (a + k) := by
      intro k _; exact (ofNat_add_word a k).symm
    have hrd1 : rdW (m.arr64 EREC) (UInt64.ofNat (a + 1)) = w1 := by
      have : (UInt64.ofNat (a + 1)).toNat = a + 1 :=
        UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
      simp only [rdW, this]; rw [hw1]; rfl
    have hrd2 : rdW (m.arr64 EREC) (UInt64.ofNat (a + 2)) = w2 := by
      have : (UInt64.ofNat (a + 2)).toNat = a + 2 :=
        UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
      simp only [rdW, this]; rw [hw2]; rfl
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
