import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# Copying slices (`iw_copy`) and building lists (`sl_cons`, `sl_snoc`, `sl_append`) (lane `induct`)

`iw_copy(d, s, l)` copies `IW[s ‥ s + l)` to `IW[d ‥ d + l)`, ascending; the word model `copyW`
follows the recursion, and `copyW_get` says what the array holds after it when the source lies
below the destination (every use: the destination is fresh, above the top).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The model of `iw_copy`. -/
def copyW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, d, s, l =>
    if l = 0 then some m
    else copyW n (m.set64 IW d (rdW (m.arr64 IW) s)) (d + 1) (s + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (d s l : Word)
theorem copyW_nil (hl : l = 0) : copyW (n + 1) m d s l = some m := by simp [copyW, hl]
theorem copyW_step (hl : l ≠ 0) :
    copyW (n + 1) m d s l = copyW n (m.set64 IW d (rdW (m.arr64 IW) s)) (d + 1) (s + 1) (l - 1) := by
  simp [copyW, hl]
end arms

grind_pattern [ind_grind] copyW_nil => copyW (n + 1) m d s l
grind_pattern [ind_grind] copyW_step => copyW (n + 1) m d s l

theorem iwCopy_spec (p : Prog) (hp : p.lookup "iw_copy" = some iwCopy) (n : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "iw_copy" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ copyW n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ d s l; rw [invoke_eq _ hp]; simp only [callFn, iwCopy]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ d s l
    rw [invoke_eq _ hp]
    simp only [callFn, iwCopy]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20)

/-- **What a copy leaves**: every other array as it was, `IW` the same size, the destination
holding the source, the rest of `IW` unchanged — when the source ends at or below the destination
and the destination is in bounds (Nat offsets, no wrap). -/
theorem copyW_get (n : Nat) : ∀ (m m' : Mem) (d s l : Word), copyW n m d s l = some m' →
    s.toNat + l.toNat ≤ d.toNat → d.toNat + l.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 →
    (∀ b, b ≠ IW → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 IW).size = (m.arr64 IW).size ∧
    m'.words.size = m.words.size ∧
    ∀ i, (m'.arr64 IW)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat then (m.arr64 IW)[s.toNat + (i - d.toNat)]?
      else (m.arr64 IW)[i]? := by
  induction n with
  | zero => intro m m' d s l h; simp [copyW] at h
  | succ n ih =>
    intro m m' d s l h hsd hd hsz
    by_cases hl : l = 0
    · rw [copyW_nil n m d s l hl] at h
      cases h
      subst hl
      refine ⟨fun _ _ => rfl, rfl, rfl, fun i => ?_⟩
      have : ¬ (d.toNat ≤ i ∧ i < d.toNat + (0 : Word).toNat) := by
        simp only [UInt64.toNat_zero]; omega
      simp only [this, ite_false]
    · rw [copyW_step n m d s l hl] at h
      have hl0 : 0 < l.toNat := by
        have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      have hl1 : (l - 1).toNat = l.toNat - 1 := by
        rw [UInt64.toNat_sub]; simp; omega
      have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hs1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hslt : s.toNat < (m.arr64 IW).size := by omega
      have hdlt : d.toNat < (m.arr64 IW).size := by omega
      obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.set64 IW d (rdW (m.arr64 IW) s) := ⟨_, rfl⟩
      rw [← hm1] at h
      have hsz1 : (m1.arr64 IW).size = (m.arr64 IW).size := by
        rw [hm1, Mem.arr64_set64_same]; simp
      have hget1 : ∀ i, (m1.arr64 IW)[i]? = if i = d.toNat then (m.arr64 IW)[s.toNat]?
          else (m.arr64 IW)[i]? := by
        intro i
        rw [hm1, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        by_cases hi : d.toNat = i
        · subst hi
          simp only [hdlt, ite_true]
          simp [rdW, Array.getElem?_eq_getElem hslt]
        · simp [hi, Ne.symm hi]
      obtain ⟨hA, hS, hW, hG⟩ := ih m1 m' (d + 1) (s + 1) (l - 1) h
        (by rw [hs1, hd1, hl1]; omega) (by rw [hd1, hl1, hsz1]; omega) (by rw [hsz1]; exact hsz)
      refine ⟨fun b hb => (hA b hb).trans ?_, hS.trans hsz1, hW.trans ?_, fun i => ?_⟩
      · rw [hm1, Mem.arr64_set64_ne _ _ _ _ _ hb]
      · rw [hm1]; exact Mem.words_size_set64 _ _ _ _
      · rw [hG i, hd1, hl1, hs1]
        by_cases hi : d.toNat ≤ i ∧ i < d.toNat + l.toNat
        · rw [ite_eq_left hi]
          by_cases hid : i = d.toNat
          · subst hid
            have : ¬ (d.toNat + 1 ≤ d.toNat ∧ d.toNat < d.toNat + 1 + (l.toNat - 1)) := by omega
            rw [ite_eq_right this, hget1, ite_eq_left rfl]; simp
          · have h2 : d.toNat + 1 ≤ i ∧ i < d.toNat + 1 + (l.toNat - 1) := by omega
            rw [ite_eq_left h2, hget1, ite_eq_right (by omega)]
            congr 1; omega
        · rw [ite_eq_right hi, ite_eq_right (by omega), hget1, ite_eq_right (by omega)]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `sl_cons` -/

/-- The memory `sl_cons(x, o, l)` builds before the copy: the allocation and the head word. -/
def consPre (m : Mem) (x l : Word) : Mem :=
  (allocMem m (l + 1)).set64 IW (rdW (m.arr64 CTL) 200) x

end L.Ind

namespace L.Ind

open L.Arena

theorem hslice?_congr {k : IdxKind} (a b : Array Word) (off off' n : Nat)
    (h : ∀ j < n, a[off + j]? = b[off' + j]?) :
    (hslice? a off n : Option (List (Idx k))) = hslice? b off' n := by
  simp only [hslice?]
  apply mapM_congr'
  intro j hj
  simp only [List.mem_range] at hj
  simp only [hd?, h j hj]

theorem consPre_ctl (m : Mem) (x l : Word) (i : Word) (hi : i ≠ 200) :
    rdW ((consPre m x l).arr64 CTL) i = rdW (m.arr64 CTL) i := by
  simp only [consPre, allocMem]
  rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), rdW_set64]
  simp [Ne.symm hi]

/-- **`sl_cons` builds `x :: xs`**, the pool only grown, nothing else written. -/
theorem slCons_dec {k : IdxKind} {m m' : Mem} {x o l : Word} {n : Nat} {xs : List (Idx k)}
    (h : copyW n (consPre m x l) (rdW (m.arr64 CTL) 200 + 1) o l = some m')
    (hne : l + 1 ≠ 0)
    (hroom : (rdW (m.arr64 CTL) 200).toNat + (l + 1).toNat ≤ (m.arr64 IW).size)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hc : 200 < (m.arr64 CTL).size)
    (hsrc : o.toNat + l.toNat ≤ (rdW (m.arr64 CTL) 200).toNat)
    (hx : x.toNat < 2 ^ 32) (hxs : decHL m o.toNat l.toNat = some xs) :
    decHL m' (rdW (m.arr64 CTL) 200).toNat (l + 1).toNat = some (decI x :: xs) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + (l + 1) := by
  generalize hq : rdW (m.arr64 CTL) 200 = q at *
  have hlm : l.toNat ≠ 2 ^ 64 - 1 := fun h0 => hne (by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp [h0])
  have hl1 : (l + 1).toNat = l.toNat + 1 := by
    rw [UInt64.toNat_add]; simp
    have : l.toNat < 2 ^ 64 := l.toNat_lt
    omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [hl1] at hroom
  -- the memory before the copy
  have hm1IW : (consPre m x l).arr64 IW = ((m.arr64 IW).set! q.toNat x) := by
    simp only [consPre, allocMem, hq]
    rw [Mem.arr64_set64_same, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hm1sz : ((consPre m x l).arr64 IW).size = (m.arr64 IW).size := by rw [hm1IW]; simp
  obtain ⟨hA, hS, hW, hG⟩ := copyW_get n _ _ _ _ _ h (by rw [hq1]; omega) (by rw [hq1, hm1sz]; omega)
    (by rw [hm1sz]; exact hsz)
  have hm1get : ∀ i, ((consPre m x l).arr64 IW)[i]? =
      if i = q.toNat then some x else (m.arr64 IW)[i]? := by
    intro i
    rw [hm1IW, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hi : q.toNat = i
    · subst hi; simp [show q.toNat < (m.arr64 IW).size by omega]
    · simp [hi, Ne.symm hi]
  have hget : ∀ i, (m'.arr64 IW)[i]? =
      if i = q.toNat then some x
      else if q.toNat + 1 ≤ i ∧ i < q.toNat + 1 + l.toNat then (m.arr64 IW)[o.toNat + (i - (q.toNat + 1))]?
      else (m.arr64 IW)[i]? := by
    intro i
    rw [hG i, hq1]
    by_cases hi : q.toNat + 1 ≤ i ∧ i < q.toNat + 1 + l.toNat
    · rw [ite_eq_left hi, ite_eq_right (by omega), ite_eq_left hi, hm1get, ite_eq_right (by omega)]
    · rw [ite_eq_right hi, hm1get]
      by_cases hiq : i = q.toNat
      · simp [hiq]
      · rw [ite_eq_right hiq, ite_eq_right hiq, ite_eq_right hi]
  -- the other arrays and CTL
  have hCTL : ∀ i, i ≠ (200 : Word) → rdW (m'.arr64 CTL) i = rdW (m.arr64 CTL) i := by
    intro i hi
    rw [hA CTL (by decide)]; exact consPre_ctl m x l i hi
  have hEREC : m'.arr64 EREC = m.arr64 EREC := by
    rw [hA EREC (by decide)]; simp only [consPre, allocMem]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have htop : rdW (m'.arr64 CTL) 200 = q + (l + 1) := by
    rw [hA CTL (by decide)]; simp only [consPre, allocMem]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), rdW_set64]; simp [hc, hq]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, htop⟩
  · simp only [decHL, hl1, hslice?_succ]
    have h0 : (hd? (iwA m') q.toNat : Option (Idx k)) = some (decI x) := by
      simp [hd?, iwA, hget, hx]
    rw [h0]
    have : (hslice? (iwA m') (q.toNat + 1) l.toNat : Option (List (Idx k))) = some xs := by
      rw [← hxs]; simp only [decHL]
      apply hslice?_congr
      intro j hj
      simp only [iwA, hget]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      congr 1; omega
    simp [this]
  · have : (q + (l + 1)).toNat = q.toNat + (l.toNat + 1) := by
      rw [UInt64.toNat_add, hl1]; simp; omega
    simp only [iwTop, htop, this, hq]; omega
  · simp only [erTop, hCTL 129 (by decide)]; exact Nat.le_refl _
  · intro i hi
    simp only [iwTop, hq] at hi
    rw [hget, ite_eq_right (by omega), ite_eq_right (by omega)]
  · intro i _; rw [hEREC]
  · intro b hb hbc
    rw [hA b (by simpa using hb)]; simp only [consPre, allocMem]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by simpa using hb), Mem.arr64_set64_ne _ _ _ _ _ hbc]
  · intro i hi; exact hCTL i (by simpa using hi)
  · intro b
    by_cases hb : b = IW
    · subst hb; rw [hS, hm1sz]
    · rw [hA b hb]; simp only [consPre, allocMem, size_set64]
  · rw [hW]; simp only [consPre, allocMem, Mem.words_size_set64]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Word models of the allocators, for callers' models -/

/-- The model of `iw_alloc(k)`: the offset and the memory, `none` where it aborts. -/
def allocW (m : Mem) (k : Word) : Option (Word × Mem) :=
  let o := rdW (m.arr64 CTL) 200
  if m.len64 IW < o then none
  else if m.len64 IW - o < k then none
  else some (o, allocMem m k)

theorem iwAlloc_specW (p : Prog) (hp : p.lookup "iw_alloc" = some iwAlloc) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "iw_alloc" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ allocW s₀.mem k = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iwAlloc]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [allocW, allocMem]

/-- The model of `sl_cons(x, o, l)` at the caller's fuel `n` (the copy runs at `n - 1`). -/
def consW (n : Nat) (m : Mem) (x o l : Word) : Option (List Word × Mem) :=
  if l + 1 = 0 then none
  else match allocW m (l + 1) with
    | none => none
    | some (q, m1) =>
      match copyW (n - 1) (m1.set64 IW q x) (q + 1) o l with
      | none => none
      | some m2 => some ([q, l + 1], m2)

theorem slCons_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hp : p.lookup "sl_cons" = some slCons) (n : Nat)
    (s₀ : St) (x o l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "sl_cons" [x, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ consW n s₀.mem x o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, slCons]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hcons : ∀ q m1 m2, l + 1 ≠ 0 → allocW s₀.mem (l + 1) = some (q, m1) →
        copyW n (m1.set64 IW q x) (q + 1) o l = some m2 →
        consW (n + 1) s₀.mem x o l = some ([q, l + 1], m2) := by
      intro q m1 m2 h0 h1 h2
      simp [consW, h0, h1, h2]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n, iwCopy_spec p hc n] <;>
      finish (gen := 20)

/-- `consW` is the memory `slCons_dec` speaks about. -/
theorem consW_dec {k : IdxKind} {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List (Idx k)}
    (h : consW n m x o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hx : x.toNat < 2 ^ 32) (hxs : decHL m o.toNat l.toNat = some xs) :
    r = [rdW (m.arr64 CTL) 200, l + 1] ∧
    decHL m' (rdW (m.arr64 CTL) 200).toNat (l + 1).toNat = some (decI x :: xs) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ (l + 1).toNat = l.toNat + 1 ∧
    (rdW (m.arr64 CTL) 200).toNat + (l + 1).toNat = iwTop m' := by
  simp only [consW] at h
  have h0 : ¬ l + 1 = 0 := fun h0 => by simp [h0] at h
  simp only [h0, ite_false] at h
  simp only [allocW] at h
  have h1 : ¬ m.len64 IW < rdW (m.arr64 CTL) 200 := fun h1 => by simp [h1] at h
  have h2 : ¬ m.len64 IW - rdW (m.arr64 CTL) 200 < l + 1 := fun h2 => by simp [h1, h2] at h
  simp only [h1, h2, ite_false] at h
  cases hcp : copyW (n - 1) ((allocMem m (l + 1)).set64 IW (rdW (m.arr64 CTL) 200) x)
      (rdW (m.arr64 CTL) 200 + 1) o l with
  | none => simp [hcp] at h
  | some m2 =>
    simp [hcp] at h
    obtain ⟨rfl, rfl⟩ := h
    have hlen : (m.len64 IW).toNat = (m.arr64 IW).size := by simp [Mem.len64]; omega
    have hq : (rdW (m.arr64 CTL) 200).toNat ≤ (m.arr64 IW).size := by
      have : ¬ (m.len64 IW).toNat < (rdW (m.arr64 CTL) 200).toNat := h1
      omega
    have hroom : (rdW (m.arr64 CTL) 200).toNat + (l + 1).toNat ≤ (m.arr64 IW).size := by
      have : ¬ (m.len64 IW - rdW (m.arr64 CTL) 200).toNat < (l + 1).toNat := h2
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)] at this
      omega
    have hlm : l.toNat ≠ 2 ^ 64 - 1 := fun e => h0 (by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp [e])
    have hl1 : (l + 1).toNat = l.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; have := l.toNat_lt; omega
    obtain ⟨hd, hg, hf, ht⟩ := slCons_dec (n := n - 1) (xs := xs) hcp h0 hroom hsz hc
      (by simpa [iwTop] using hsrc) hx hxs
    refine ⟨rfl, hd, hg, hf, hl1, ?_⟩
    have e : (rdW (m.arr64 CTL) 200 + (l + 1)).toNat =
        (rdW (m.arr64 CTL) 200).toNat + (l + 1).toNat := by
      rw [UInt64.toNat_add]; omega
    simp only [iwTop, ht, e]

end L.Ind
