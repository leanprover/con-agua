import ConAgua.Arena.IndCopy

/-!
# More slice-library models: `rec3`…`rec6`, `er_to_iw`, `sl_append`, `sl_snoc` (lane `induct`)

Same shape as `IndLibSpec.lean`'s `rec2Mem`/`rec2_spec` (direct memory equations, no fuel: these
never recurse) and `IndCopy.lean`'s `sl_cons` (a fueled word model built from `allocW`/`copyW`, for
`er_to_iw`'s and `sl_append`'s own copies, and a `_get`/`_dec` lemma stating what the call leaves).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Generic facts: writing a list of words into `IW` -/

/-- Write `ws` into `IW` at `q, q + 1, …`. -/
def wrIW (m : Mem) (q : Word) : List Word → Mem
  | [] => m
  | x :: xs => wrIW (m.set64 IW q x) (q + 1) xs

theorem wrIW_frame : ∀ (ws : List Word) (m : Mem) (q : Word), MemFrame [IW] [200] m (wrIW m q ws)
  | [], m, q => MemFrame.refl _ _ _
  | x :: ws, m, q =>
    (MemFrame.mono (MemFrame.set64 m IW (by decide) q x) (by simp) (by simp)).trans
      (wrIW_frame ws _ _)

theorem wrIW_arr_ne : ∀ (ws : List Word) (m : Mem) (q : Word) (b : ArrId), b ≠ IW →
    (wrIW m q ws).arr64 b = m.arr64 b
  | [], m, q, b, hb => rfl
  | x :: ws, m, q, b, hb => by
    simp only [wrIW]; rw [wrIW_arr_ne ws _ _ b hb, Mem.arr64_set64_ne _ _ _ _ _ hb]

theorem wrIW_size : ∀ (ws : List Word) (m : Mem) (q : Word),
    ((wrIW m q ws).arr64 IW).size = (m.arr64 IW).size
  | [], m, q => rfl
  | x :: ws, m, q => by simp only [wrIW]; rw [wrIW_size ws, size_set64]

/-- **What `wrIW` leaves in `IW`**, when the slice is in bounds. -/
theorem wrIW_get : ∀ (ws : List Word) (m : Mem) (q : Word) (i : Nat),
    q.toNat + ws.length ≤ (m.arr64 IW).size → (m.arr64 IW).size < 2 ^ 64 →
    ((wrIW m q ws).arr64 IW)[i]? =
      if q.toNat ≤ i ∧ i < q.toNat + ws.length then ws[i - q.toNat]? else (m.arr64 IW)[i]?
  | [], m, q, i, _, _ => by simp [wrIW]; intro h1 h2; omega
  | x :: ws, m, q, i, h, hsz => by
    simp only [wrIW, List.length_cons] at h ⊢
    have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hqlt : q.toNat < (m.arr64 IW).size := by omega
    have hsz1 : ((m.set64 IW q x).arr64 IW).size = (m.arr64 IW).size := size_set64 _ _ _ _ _
    rw [wrIW_get ws _ _ i (by rw [hq1, hsz1]; omega) (by rw [hsz1]; exact hsz), hq1]
    have hg : (m.set64 IW q x).arr64 IW = (m.arr64 IW).set! q.toNat x := Mem.arr64_set64_same _ _ _ _
    by_cases h1 : q.toNat + 1 ≤ i ∧ i < q.toNat + 1 + ws.length
    · rw [if_pos h1, if_pos (by omega)]
      have : i - q.toNat = (i - (q.toNat + 1)) + 1 := by omega
      rw [this]; simp
    · rw [if_neg h1]
      by_cases hiq : i = q.toNat
      · subst hiq
        rw [if_pos (by omega), hg, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp [hqlt]
      · rw [if_neg (by omega), hg, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp [Ne.symm hiq]

/-- A frame that grew the pool by `N` words from the old top, leaving everything below as it
was, is an `IWGrow`. -/
theorem iwGrow_of_frame {m m' : Mem} {N : Word} (hf : MemFrame [IW] [200] m m')
    (htop : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + N)
    (hroom : iwTop m + N.toNat ≤ (m.arr64 IW).size) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hlow : ∀ i < iwTop m, (m'.arr64 IW)[i]? = (m.arr64 IW)[i]?) : IWGrow m m' := by
  refine ⟨?_, ?_, hlow, ?_⟩
  · simp only [iwTop, htop]; rw [UInt64.toNat_add]; simp only [iwTop] at hroom; omega
  · simp only [erTop]; rw [hf.2.1 129 (by simp)]; exact Nat.le_refl _
  · intro i _; rw [hf.1 EREC (by decide) (by decide)]

/-- A copy that touches only `IW` is a frame. -/
theorem memFrame_of_copy {m m' : Mem} (hA : ∀ b, b ≠ IW → m'.arr64 b = m.arr64 b)
    (hS : (m'.arr64 IW).size = (m.arr64 IW).size) (hW : m'.words.size = m.words.size) :
    MemFrame [IW] [] m m' := by
  refine ⟨fun b hb hc => hA b (by simpa using hb), fun x _ => ?_, fun b => ?_, hW⟩
  · rw [hA CTL (by decide)]
  · by_cases hb : b = IW
    · subst hb; exact hS
    · rw [hA b hb]

/-- **A record writer**: `alloc k` then `ws` written at the old top. The words are readable at
the returned pointer, the pool only grew, nothing else moved, the new top is `q + k`. -/
theorem recMem_post (m : Mem) (ws : List Word) (k : Word) (hk : k.toNat = ws.length)
    (hc : 200 < (m.arr64 CTL).size)
    (hroom : (rdW (m.arr64 CTL) 200).toNat + ws.length ≤ (m.arr64 IW).size)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (∀ j < ws.length,
      ((wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws).arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? =
        ws[j]?) ∧
    IWGrow m (wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws) ∧
    MemFrame [IW] [200] m (wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws) ∧
    rdW ((wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws).arr64 CTL) 200 =
      rdW (m.arr64 CTL) 200 + k := by
  have hIW : (allocMem m k).arr64 IW = m.arr64 IW := by
    simp only [allocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hf : MemFrame [IW] [200] m (wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws) :=
    (allocMem_frame m k).trans (wrIW_frame _ _ _)
  have htop : rdW ((wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws).arr64 CTL) 200 =
      rdW (m.arr64 CTL) 200 + k := by
    rw [wrIW_arr_ne _ _ _ _ (by decide)]
    simp only [allocMem]
    rw [rdW_set64]; simp [hc]
  refine ⟨fun j hj => ?_, ?_, hf, htop⟩
  · rw [wrIW_get ws _ _ _ (by rw [hIW]; exact hroom) (by rw [hIW]; exact hsz), if_pos (by omega)]
    congr 1; omega
  · refine iwGrow_of_frame (N := k) hf htop (by simp only [iwTop]; omega) hsz ?_
    intro i hi
    simp only [iwTop] at hi
    rw [wrIW_get ws _ _ _ (by rw [hIW]; exact hroom) (by rw [hIW]; exact hsz), if_neg (by omega), hIW]

/-! ## Records: `rec3`…`rec6` -/

/-- The memory after `rec3(a, b, c)`. -/
def rec3Mem (m : Mem) (a b c : Word) : Mem :=
  let q := rdW (m.arr64 CTL) 200
  (((allocMem m 3).set64 IW q a).set64 IW (q + 1) b).set64 IW (q + 2) c

theorem rec3_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "rec3" = some rec3) (n : Nat) (s₀ : St) (a b c : Word)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec3" [a, b, c]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = rec3Mem s₀.mem a b c ∧
      r.headD 0 = rdW (s₀.mem.arr64 CTL) 200 ∧
      (rdW (s₀.mem.arr64 CTL) 200).toNat + 3 ≤ (s₀.mem.arr64 IW).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, rec3]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_spec p ha n] <;>
      finish [rec3Mem, allocMem]

/-- The memory after `rec4(a, b, c, d)`. -/
def rec4Mem (m : Mem) (a b c d : Word) : Mem :=
  let q := rdW (m.arr64 CTL) 200
  ((((allocMem m 4).set64 IW q a).set64 IW (q + 1) b).set64 IW (q + 2) c).set64 IW (q + 3) d

theorem rec4_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "rec4" = some rec4) (n : Nat) (s₀ : St) (a b c d : Word)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec4" [a, b, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = rec4Mem s₀.mem a b c d ∧
      r.headD 0 = rdW (s₀.mem.arr64 CTL) 200 ∧
      (rdW (s₀.mem.arr64 CTL) 200).toNat + 4 ≤ (s₀.mem.arr64 IW).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, rec4]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_spec p ha n] <;>
      finish [rec4Mem, allocMem]

/-- The memory after `rec5(a, b, c, d, e)`. -/
def rec5Mem (m : Mem) (a b c d e : Word) : Mem :=
  let q := rdW (m.arr64 CTL) 200
  (((((allocMem m 5).set64 IW q a).set64 IW (q + 1) b).set64 IW (q + 2) c).set64 IW (q + 3) d).set64
    IW (q + 4) e

theorem rec5_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "rec5" = some rec5) (n : Nat) (s₀ : St) (a b c d e : Word)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec5" [a, b, c, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = rec5Mem s₀.mem a b c d e ∧
      r.headD 0 = rdW (s₀.mem.arr64 CTL) 200 ∧
      (rdW (s₀.mem.arr64 CTL) 200).toNat + 5 ≤ (s₀.mem.arr64 IW).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, rec5]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_spec p ha n] <;>
      finish [rec5Mem, allocMem]

/-- The memory after `rec6(a, b, c, d, e, f)`. -/
def rec6Mem (m : Mem) (a b c d e f : Word) : Mem :=
  let q := rdW (m.arr64 CTL) 200
  ((((((allocMem m 6).set64 IW q a).set64 IW (q + 1) b).set64 IW (q + 2) c).set64 IW (q + 3) d).set64
    IW (q + 4) e).set64 IW (q + 5) f

theorem rec6_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "rec6" = some rec6) (n : Nat) (s₀ : St) (a b c d e f : Word)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec6" [a, b, c, d, e, f]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = rec6Mem s₀.mem a b c d e f ∧
      r.headD 0 = rdW (s₀.mem.arr64 CTL) 200 ∧
      (rdW (s₀.mem.arr64 CTL) 200).toNat + 6 ≤ (s₀.mem.arr64 IW).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, rec6]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_spec p ha n] <;>
      finish [rec6Mem, allocMem]

/-! ## The record models as `wrIW`, and what each leaves -/

theorem rec2Mem_eq (m : Mem) (a b : Word) :
    rec2Mem m a b = wrIW (allocMem m 2) (rdW (m.arr64 CTL) 200) [a, b] := by
  simp [rec2Mem, wrIW, UInt64.add_assoc]

/-- **`rec2` leaves**: its 2 words readable at the returned pointer (the old top), the pool only
grown, `IW` and `CTL[200]` the only changes, the new top `q + 2`. -/
theorem rec2Mem_post (m : Mem) (a b : Word) (hc : 200 < (m.arr64 CTL).size)
    (hroom : (rdW (m.arr64 CTL) 200).toNat + 2 ≤ (m.arr64 IW).size)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (∀ j < 2, ((rec2Mem m a b).arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? =
      [a, b][j]?) ∧
    IWGrow m (rec2Mem m a b) ∧ MemFrame [IW] [200] m (rec2Mem m a b) ∧
    rdW ((rec2Mem m a b).arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + 2 := by
  rw [rec2Mem_eq]
  exact recMem_post m [a, b] 2 rfl hc hroom hsz

theorem rec3Mem_eq (m : Mem) (a b c : Word) :
    rec3Mem m a b c = wrIW (allocMem m 3) (rdW (m.arr64 CTL) 200) [a, b, c] := by
  simp [rec3Mem, wrIW, UInt64.add_assoc]

/-- **`rec3` leaves**: its 3 words readable at the returned pointer (the old top), the pool only
grown, `IW` and `CTL[200]` the only changes, the new top `q + 3`. -/
theorem rec3Mem_post (m : Mem) (a b c : Word) (hc : 200 < (m.arr64 CTL).size)
    (hroom : (rdW (m.arr64 CTL) 200).toNat + 3 ≤ (m.arr64 IW).size)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (∀ j < 3, ((rec3Mem m a b c).arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? =
      [a, b, c][j]?) ∧
    IWGrow m (rec3Mem m a b c) ∧ MemFrame [IW] [200] m (rec3Mem m a b c) ∧
    rdW ((rec3Mem m a b c).arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + 3 := by
  rw [rec3Mem_eq]
  exact recMem_post m [a, b, c] 3 rfl hc hroom hsz

theorem rec4Mem_eq (m : Mem) (a b c d : Word) :
    rec4Mem m a b c d = wrIW (allocMem m 4) (rdW (m.arr64 CTL) 200) [a, b, c, d] := by
  simp [rec4Mem, wrIW, UInt64.add_assoc]

/-- **`rec4` leaves**: its 4 words readable at the returned pointer (the old top), the pool only
grown, `IW` and `CTL[200]` the only changes, the new top `q + 4`. -/
theorem rec4Mem_post (m : Mem) (a b c d : Word) (hc : 200 < (m.arr64 CTL).size)
    (hroom : (rdW (m.arr64 CTL) 200).toNat + 4 ≤ (m.arr64 IW).size)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (∀ j < 4, ((rec4Mem m a b c d).arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? =
      [a, b, c, d][j]?) ∧
    IWGrow m (rec4Mem m a b c d) ∧ MemFrame [IW] [200] m (rec4Mem m a b c d) ∧
    rdW ((rec4Mem m a b c d).arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + 4 := by
  rw [rec4Mem_eq]
  exact recMem_post m [a, b, c, d] 4 rfl hc hroom hsz

theorem rec5Mem_eq (m : Mem) (a b c d e : Word) :
    rec5Mem m a b c d e = wrIW (allocMem m 5) (rdW (m.arr64 CTL) 200) [a, b, c, d, e] := by
  simp [rec5Mem, wrIW, UInt64.add_assoc]

/-- **`rec5` leaves**: its 5 words readable at the returned pointer (the old top), the pool only
grown, `IW` and `CTL[200]` the only changes, the new top `q + 5`. -/
theorem rec5Mem_post (m : Mem) (a b c d e : Word) (hc : 200 < (m.arr64 CTL).size)
    (hroom : (rdW (m.arr64 CTL) 200).toNat + 5 ≤ (m.arr64 IW).size)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (∀ j < 5, ((rec5Mem m a b c d e).arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? =
      [a, b, c, d, e][j]?) ∧
    IWGrow m (rec5Mem m a b c d e) ∧ MemFrame [IW] [200] m (rec5Mem m a b c d e) ∧
    rdW ((rec5Mem m a b c d e).arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + 5 := by
  rw [rec5Mem_eq]
  exact recMem_post m [a, b, c, d, e] 5 rfl hc hroom hsz

theorem rec6Mem_eq (m : Mem) (a b c d e f : Word) :
    rec6Mem m a b c d e f = wrIW (allocMem m 6) (rdW (m.arr64 CTL) 200) [a, b, c, d, e, f] := by
  simp [rec6Mem, wrIW, UInt64.add_assoc]

/-- **`rec6` leaves**: its 6 words readable at the returned pointer (the old top), the pool only
grown, `IW` and `CTL[200]` the only changes, the new top `q + 6`. -/
theorem rec6Mem_post (m : Mem) (a b c d e f : Word) (hc : 200 < (m.arr64 CTL).size)
    (hroom : (rdW (m.arr64 CTL) 200).toNat + 6 ≤ (m.arr64 IW).size)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (∀ j < 6, ((rec6Mem m a b c d e f).arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? =
      [a, b, c, d, e, f][j]?) ∧
    IWGrow m (rec6Mem m a b c d e f) ∧ MemFrame [IW] [200] m (rec6Mem m a b c d e f) ∧
    rdW ((rec6Mem m a b c d e f).arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + 6 := by
  rw [rec6Mem_eq]
  exact recMem_post m [a, b, c, d, e, f] 6 rfl hc hroom hsz



/-! ## `sl_snoc` -/

theorem hslice?_add {k : IdxKind} (a : Array Word) : ∀ (n m off : Nat),
    (hslice? a off (n + m) : Option (List (Idx k))) = (do
      let xs ← hslice? a off n
      let ys ← hslice? a (off + n) m
      pure (xs ++ ys))
  | 0, m, off => by simp [hslice?]
  | n + 1, m, off => by
    rw [Nat.add_right_comm, hslice?_succ, hslice?_add a n m (off + 1), hslice?_succ]
    cases hd? a off <;> simp [Nat.add_assoc, Nat.add_comm 1 n] <;>
      cases hslice? a (off + 1) n <;> simp <;>
      cases hslice? a (off + (n + 1)) m <;> simp


theorem set64IW_get (m : Mem) (p x : Word) (i : Nat) :
    ((m.set64 IW p x).arr64 IW)[i]? =
      if i = p.toNat ∧ i < (m.arr64 IW).size then some x else (m.arr64 IW)[i]? := by
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hi : p.toNat = i
  · subst hi; by_cases hl : p.toNat < (m.arr64 IW).size <;> simp [hl]
  · simp [hi, Ne.symm hi]

/-- A copy into `IW` (touching nothing else) is a frame. -/
theorem copy_frame {m m' : Mem} (hA : ∀ b, b ≠ IW → m'.arr64 b = m.arr64 b)
    (hS : (m'.arr64 IW).size = (m.arr64 IW).size) (hW : m'.words.size = m.words.size) :
    MemFrame [IW] [200] m m' :=
  MemFrame.mono (memFrame_of_copy hA hS hW) (by simp) (by simp)

theorem set64IW_frame (m : Mem) (p x : Word) : MemFrame [IW] [200] m (m.set64 IW p x) :=
  MemFrame.mono (MemFrame.set64 m IW (by decide) p x) (by simp) (by simp)

theorem allocMem_IW (m : Mem) (k : Word) : (allocMem m k).arr64 IW = m.arr64 IW := by
  simp only [allocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]

theorem allocMem_top (m : Mem) (k : Word) (hc : 200 < (m.arr64 CTL).size) :
    rdW ((allocMem m k).arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + k := by
  simp only [allocMem]; rw [rdW_set64]; simp [hc]

/-- The model of `sl_snoc(o, l, x)` at the caller's fuel `n` (the copy runs at `n - 1`). -/
def snocW (n : Nat) (m : Mem) (o l x : Word) : Option (List Word × Mem) :=
  if l + 1 = 0 then none
  else match allocW m (l + 1) with
    | none => none
    | some (q, m1) =>
      match copyW (n - 1) m1 q o l with
      | none => none
      | some m2 => some ([q, l + 1], m2.set64 IW (q + l) x)

theorem slSnoc_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hp : p.lookup "sl_snoc" = some slSnoc) (n : Nat)
    (s₀ : St) (o l x : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "sl_snoc" [o, l, x]
    ⦃fun r s' => LocEq s' s₀ ∧ snocW n s₀.mem o l x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, slSnoc]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hsnoc : ∀ q m1 m2, l + 1 ≠ 0 → allocW s₀.mem (l + 1) = some (q, m1) →
        copyW n m1 q o l = some m2 →
        snocW (n + 1) s₀.mem o l x = some ([q, l + 1], m2.set64 IW (q + l) x) := by
      intro q m1 m2 h0 h1 h2
      simp [snocW, h0, h1, h2]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n, iwCopy_spec p hc n] <;>
      finish (gen := 20)


theorem allocW_facts {m m1 : Mem} {k q : Word} (h : allocW m k = some (q, m1))
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    q = rdW (m.arr64 CTL) 200 ∧ m1 = allocMem m k ∧
    q.toNat + k.toNat ≤ (m.arr64 IW).size := by
  simp only [allocW] at h
  by_cases h1 : m.len64 IW < rdW (m.arr64 CTL) 200
  · simp [h1] at h
  by_cases h2 : m.len64 IW - rdW (m.arr64 CTL) 200 < k
  · simp [h1, h2] at h
  simp only [h1, h2, if_false, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, rfl, ?_⟩
  have hlen : (m.len64 IW).toNat = (m.arr64 IW).size := by simp [Mem.len64]; omega
  have hq : (rdW (m.arr64 CTL) 200).toNat ≤ (m.arr64 IW).size := by
    have : ¬ (m.len64 IW).toNat < (rdW (m.arr64 CTL) 200).toNat := h1
    omega
  have : ¬ (m.len64 IW - rdW (m.arr64 CTL) 200).toNat < k.toNat := h2
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)] at this
  omega

theorem snocW_dec {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} {xs : List EIdx}
    (h : snocW n m o l x = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hx : x.toNat < 2 ^ 32) (hxs : decHL m o.toNat l.toNat = some xs) :
    r = [rdW (m.arr64 CTL) 200, l + 1] ∧
    decHL m' (rdW (m.arr64 CTL) 200).toNat (l + 1).toNat = some (xs ++ [decI x]) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ (l + 1).toNat = l.toNat + 1 ∧
    (rdW (m.arr64 CTL) 200).toNat + (l + 1).toNat = iwTop m' := by
  simp only [snocW] at h
  by_cases h0 : l + 1 = 0
  · simp [h0] at h
  simp only [h0, if_false] at h
  cases hal : allocW m (l + 1) with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  cases hcp : copyW (n - 1) m1 q o l with
  | none => simp [hcp] at h
  | some m2 =>
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hlm : l.toNat ≠ 2 ^ 64 - 1 := fun e => h0 (by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp [e])
  have hl1 : (l + 1).toNat = l.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; have := l.toNat_lt; omega
  rw [hl1] at hroom
  have hql : (q + l).toNat = q.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hIW := allocMem_IW m (l + 1)
  obtain ⟨hA, hS, hW, hG⟩ := copyW_get (n - 1) _ _ _ _ _ hcp (by simp only [iwTop, hqq] at hsrc; omega)
    (by rw [hIW]; omega) (by rw [hIW]; exact hsz)
  rw [hIW] at hS hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m (l + 1)).trans (copy_frame hA (by rw [hS, hIW]) (by first | (rw [hW]) | (rw [hW]; simp [allocMem])))
  have hfr' := hfr.trans (set64IW_frame m2 (q + l) x)
  have hget : ∀ i, ((m2.set64 IW (q + l) x).arr64 IW)[i]? =
      if i = q.toNat + l.toNat then some x
      else if q.toNat ≤ i ∧ i < q.toNat + l.toNat then (m.arr64 IW)[o.toNat + (i - q.toNat)]?
      else (m.arr64 IW)[i]? := by
    intro i
    rw [set64IW_get, hql, hS, hG i]
    by_cases h1 : i = q.toNat + l.toNat
    · rw [if_pos ⟨h1, by omega⟩, if_pos h1]
    · rw [if_neg (by omega), if_neg h1]
  have hCTL : (m2.set64 IW (q + l) x).arr64 CTL = (allocMem m (l + 1)).arr64 CTL := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hA CTL (by decide)]
  have htop : rdW ((m2.set64 IW (q + l) x).arr64 CTL) 200 = q + (l + 1) := by
    rw [hCTL, allocMem_top m _ hc, hqq]
  have hq' : q + (l + 1) = q + (l + 1) := rfl
  have hsum : (q + (l + 1)).toNat = q.toNat + (l.toNat + 1) := by
    rw [UInt64.toNat_add, hl1]; simp; omega
  refine ⟨rfl, ?_, ?_, hfr', hl1, ?_⟩
  · simp only [decHL]
    rw [hl1, hslice?_add]
    have h1 : (hslice? (iwA (m2.set64 IW (q + l) x)) q.toNat l.toNat : Option (List EIdx)) =
        some xs := by
      rw [← hxs]; simp only [decHL]
      apply hslice?_congr
      intro j hj
      simp only [iwA, hget]
      rw [if_neg (by omega), if_pos (by omega)]
      congr 1; omega
    have h2 : (hslice? (iwA (m2.set64 IW (q + l) x)) (q.toNat + l.toNat) 1 :
        Option (List EIdx)) = some [decI x] := by
      rw [hslice?_succ]
      have : (hd? (iwA (m2.set64 IW (q + l) x)) (q.toNat + l.toNat) : Option EIdx) =
          some (decI x) := by simp [hd?, iwA, hget, hx]
      rw [this]; simp [hslice?]
    rw [h1, h2]; simp
  · refine iwGrow_of_frame hfr' (N := l + 1) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hget, if_neg (by omega), if_neg (by omega)]
  · simp only [iwTop, htop, hsum]; omega


/-! ## `sl_append` -/

/-- The model of `sl_append(o1, l1, o2, l2)` at the caller's fuel `n` (copies at `n - 1`). -/
def appendW (n : Nat) (m : Mem) (o1 l1 o2 l2 : Word) : Option (List Word × Mem) :=
  if l1 + l2 < l1 then none
  else match allocW m (l1 + l2) with
    | none => none
    | some (q, m1) =>
      match copyW (n - 1) m1 q o1 l1 with
      | none => none
      | some m2 =>
        match copyW (n - 1) m2 (q + l1) o2 l2 with
        | none => none
        | some m3 => some ([q, l1 + l2], m3)

theorem slAppend_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hp : p.lookup "sl_append" = some slAppend) (n : Nat)
    (s₀ : St) (o1 l1 o2 l2 : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "sl_append" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ appendW n s₀.mem o1 l1 o2 l2 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, slAppend]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have happ : ∀ q m1 m2 m3, ¬ (l1 + l2 < l1) → allocW s₀.mem (l1 + l2) = some (q, m1) →
        copyW n m1 q o1 l1 = some m2 → copyW n m2 (q + l1) o2 l2 = some m3 →
        appendW (n + 1) s₀.mem o1 l1 o2 l2 = some ([q, l1 + l2], m3) := by
      intro q m1 m2 m3 h0 h1 h2 h3
      simp [appendW, h0, h1, h2, h3]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n, iwCopy_spec p hc n] <;>
      finish (gen := 20)

theorem appendW_dec {n : Nat} {m m' : Mem} {o1 l1 o2 l2 : Word} {r : List Word}
    {xs ys : List EIdx}
    (h : appendW n m o1 l1 o2 l2 = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc1 : o1.toNat + l1.toNat ≤ iwTop m)
    (hsrc2 : o2.toNat + l2.toNat ≤ iwTop m)
    (hxs : decHL m o1.toNat l1.toNat = some xs) (hys : decHL m o2.toNat l2.toNat = some ys) :
    r = [rdW (m.arr64 CTL) 200, l1 + l2] ∧
    decHL m' (rdW (m.arr64 CTL) 200).toNat (l1 + l2).toNat = some (xs ++ ys) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ (l1 + l2).toNat = l1.toNat + l2.toNat ∧
    (rdW (m.arr64 CTL) 200).toNat + (l1 + l2).toNat = iwTop m' := by
  simp only [appendW] at h
  by_cases h0 : l1 + l2 < l1
  · simp [h0] at h
  simp only [h0, if_false] at h
  cases hal : allocW m (l1 + l2) with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  cases hcp1 : copyW (n - 1) m1 q o1 l1 with
  | none => simp [hcp1] at h
  | some m2 =>
  simp only [hcp1] at h
  cases hcp2 : copyW (n - 1) m2 (q + l1) o2 l2 with
  | none => simp [hcp2] at h
  | some m3 =>
  simp only [hcp2, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hlt : ¬ (l1 + l2).toNat < l1.toNat := by
    intro hh; exact h0 (UInt64.lt_iff_toNat_lt.mpr hh)
  have hs : (l1 + l2).toNat = l1.toNat + l2.toNat := by
    rw [UInt64.toNat_add] at hlt ⊢
    have := l1.toNat_lt; have := l2.toNat_lt
    omega
  rw [hs] at hroom
  have hql : (q + l1).toNat = q.toNat + l1.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hIW := allocMem_IW m (l1 + l2)
  simp only [iwTop, hqq] at hsrc1 hsrc2
  obtain ⟨hA1, hS1, hW1, hG1⟩ := copyW_get (n - 1) _ _ _ _ _ hcp1 (by omega)
    (by rw [hIW]; omega) (by rw [hIW]; exact hsz)
  obtain ⟨hA2, hS2, hW2, hG2⟩ := copyW_get (n - 1) _ _ _ _ _ hcp2 (by rw [hql]; omega)
    (by rw [hql, hS1, hIW]; omega) (by rw [hS1, hIW]; exact hsz)
  rw [hIW] at hS1 hG1
  have hfr : MemFrame [IW] [200] m m3 :=
    (allocMem_frame m (l1 + l2)).trans
      ((copy_frame hA1 (by rw [hS1, hIW]) hW1).trans
       (copy_frame hA2 hS2 hW2))
  have hget : ∀ i, (m3.arr64 IW)[i]? =
      if q.toNat ≤ i ∧ i < q.toNat + l1.toNat then (m.arr64 IW)[o1.toNat + (i - q.toNat)]?
      else if q.toNat + l1.toNat ≤ i ∧ i < q.toNat + l1.toNat + l2.toNat then
        (m.arr64 IW)[o2.toNat + (i - (q.toNat + l1.toNat))]?
      else (m.arr64 IW)[i]? := by
    intro i
    rw [hG2 i, hql]
    by_cases h1 : q.toNat ≤ i ∧ i < q.toNat + l1.toNat
    · rw [if_neg (by omega), hG1, if_pos h1, if_pos h1]
    · by_cases h2 : q.toNat + l1.toNat ≤ i ∧ i < q.toNat + l1.toNat + l2.toNat
      · rw [if_pos h2, hG1, if_neg (by omega), if_neg h1, if_pos h2]
      · rw [if_neg h2, hG1, if_neg h1, if_neg h1, if_neg h2]
  have htop : rdW (m3.arr64 CTL) 200 = q + (l1 + l2) := by
    rw [hA2 CTL (by decide), hA1 CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + (l1 + l2)).toNat = q.toNat + (l1.toNat + l2.toNat) := by
    rw [UInt64.toNat_add, hs]; simp; omega
  refine ⟨rfl, ?_, ?_, hfr, hs, ?_⟩
  · simp only [decHL]
    rw [hs, hslice?_add]
    have h1 : (hslice? (iwA m3) q.toNat l1.toNat : Option (List EIdx)) = some xs := by
      rw [← hxs]; simp only [decHL]
      apply hslice?_congr
      intro j hj
      simp only [iwA, hget]
      rw [if_pos (by omega)]
      congr 1; omega
    have h2 : (hslice? (iwA m3) (q.toNat + l1.toNat) l2.toNat : Option (List EIdx)) =
        some ys := by
      rw [← hys]; simp only [decHL]
      apply hslice?_congr
      intro j hj
      simp only [iwA, hget]
      rw [if_neg (by omega), if_pos (by omega)]
      congr 1; omega
    rw [h1, h2]; simp
  · refine iwGrow_of_frame hfr (N := l1 + l2) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hget, if_neg (by omega), if_neg (by omega)]
  · simp only [iwTop, htop, hsum]; omega

end L.Ind
