import ConAgua.Arena.DeclAndPinIndCopy

/-!
# The `And` pin's inductive arm, part 2c: what the copy's pieces leave

`EW W m m'`: an `EREC` writer (only `EREC` and its top `CTL[129]` change, the top grows within
the array) that changes no word below the old top outside `W`. Allocations, `dind_copy` and the
relocating writes are `EW`s; they compose (`EW.trans`). `dindCopyW_get`: the words a copy leaves.
-/

open ConRon.Arena

namespace L.Arena

open L.Front (DECL DLP trunc)
open L.Ind (erAllocW erAllocMem erTop)

/-! ## `EREC` writers -/

/-- **An `EREC` writer**: only `EREC` and `CTL[129]` change, the top grows within the array, and
below the old top only the words `W` admits change. -/
def EW (W : Nat → Prop) (m m' : Mem) : Prop :=
  MemFrame [EREC] [129] m m' ∧ erTop m ≤ erTop m' ∧ erTop m' ≤ (m'.arr64 EREC).size ∧
  ∀ i, i < erTop m → ¬ W i → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?

theorem EW.refl (W : Nat → Prop) (m : Mem) (h : erTop m ≤ (m.arr64 EREC).size) : EW W m m :=
  ⟨MemFrame.refl _ _ _, Nat.le_refl _, h, fun _ _ _ => rfl⟩

theorem EW.trans {W W' : Nat → Prop} {m₁ m₂ m₃ : Mem} (h₁ : EW W m₁ m₂) (h₂ : EW W' m₂ m₃)
    (hW : ∀ i, i < erTop m₁ → W' i → W i) : EW W m₁ m₃ :=
  ⟨h₁.1.trans h₂.1, Nat.le_trans h₁.2.1 h₂.2.1, h₂.2.2.1, fun i hi hn =>
    (h₂.2.2.2 i (Nat.lt_of_lt_of_le hi h₁.2.1) (fun hw => hn (hW i hi hw))).trans
      (h₁.2.2.2 i hi hn)⟩

theorem EW.mono {W W' : Nat → Prop} {m m' : Mem} (h : EW W m m') (hW : ∀ i, W i → W' i) :
    EW W' m m' :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi hn => h.2.2.2 i hi (fun hw => hn (hW i hw))⟩

theorem EW.dlp {W : Nat → Prop} {m m' : Mem} (h : EW W m m') : m'.arr64 DLP = m.arr64 DLP :=
  h.1.1 DLP (by decide) (by decide)

theorem EW.decl {W : Nat → Prop} {m m' : Mem} (h : EW W m m') : m'.arr64 DECL = m.arr64 DECL :=
  h.1.1 DECL (by decide) (by decide)

theorem EW.esize {W : Nat → Prop} {m m' : Mem} (h : EW W m m') :
    (m'.arr64 EREC).size = (m.arr64 EREC).size := h.1.2.2.1 EREC

theorem EW.csize {W : Nat → Prop} {m m' : Mem} (h : EW W m m') :
    (m'.arr64 CTL).size = (m.arr64 CTL).size := h.1.2.2.1 CTL

/-- **`erec_alloc(k)`**: the pointer is the old top, the top moves by `k` within the array,
nothing else changes. -/
theorem erAllocW_facts {m m1 : Mem} {k o : Word} (h : erAllocW m k = some (o, m1))
    (hc : 129 < (m.arr64 CTL).size) (hE64 : (m.arr64 EREC).size < 2 ^ 64) :
    o.toNat = erTop m ∧ erTop m1 = erTop m + k.toNat ∧ m1.arr64 EREC = m.arr64 EREC ∧
      (∀ W, EW W m m1) := by
  simp only [erAllocW] at h
  by_cases h1 : m.len64 EREC < rdW (m.arr64 CTL) 129
  · simp [h1] at h
  by_cases h2 : m.len64 EREC - rdW (m.arr64 CTL) 129 < k
  · simp [h1, h2] at h
  simp only [h1, h2, if_false, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hlen : (m.len64 EREC).toNat = (m.arr64 EREC).size := by simp [Mem.len64]; omega
  have hq : (rdW (m.arr64 CTL) 129).toNat ≤ (m.arr64 EREC).size := by
    have : ¬ (m.len64 EREC).toNat < (rdW (m.arr64 CTL) 129).toNat := h1
    omega
  have hroom : (rdW (m.arr64 CTL) 129).toNat + k.toNat ≤ (m.arr64 EREC).size := by
    have : ¬ (m.len64 EREC - rdW (m.arr64 CTL) 129).toNat < k.toNat := h2
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)] at this
    omega
  have hE : (erAllocMem m k).arr64 EREC = m.arr64 EREC := by
    simp only [erAllocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hf : MemFrame [EREC] [129] m (erAllocMem m k) :=
    (MemFrame.setCtl m 129 _).mono (by simp) (by simp)
  have h129 : (129 : Word).toNat < (m.arr64 CTL).size := by simp; omega
  have htop : erTop (erAllocMem m k) = erTop m + k.toNat := by
    simp only [erTop, erAllocMem, rdW_set64]
    rw [if_pos ⟨trivial, trivial, h129⟩, UInt64.toNat_add]
    omega
  refine ⟨rfl, htop, hE, fun W => ⟨hf, by omega, ?_, fun i _ _ => by rw [hE]⟩⟩
  rw [htop, hE]; simp only [erTop]; omega

/-- A word written below the top. -/
theorem EW.set {m : Mem} {x v : Word}
    (hr : erTop m ≤ (m.arr64 EREC).size) :
    EW (fun i => i = x.toNat) m (m.set64 EREC x v) := by
  have hf : MemFrame [EREC] [129] m (m.set64 EREC x v) :=
    (MemFrame.set64 m EREC (by decide) x v).mono (by simp) (by simp)
  have ht : erTop (m.set64 EREC x v) = erTop m := by
    simp only [erTop, (MemFrame.set64 m EREC (by decide) x v).2.1 129 (by simp)]
  refine ⟨hf, by omega, by rw [ht, hf.2.2.1 EREC]; exact hr, fun i _ hn => ?_⟩
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [Ne.symm hn]

theorem set64_get_same {m : Mem} {x v : Word} (hx : x.toNat < (m.arr64 EREC).size) :
    ((m.set64 EREC x v).arr64 EREC)[x.toNat]? = some v := by
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [hx]

theorem set64_get_ne {m : Mem} {x v : Word} {i : Nat} (hi : i ≠ x.toNat) :
    ((m.set64 EREC x v).arr64 EREC)[i]? = (m.arr64 EREC)[i]? := by
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [Ne.symm hi]

/-! ## `dind_copy` -/

/-- **What `dind_copy(d, s, l)` leaves**: `EREC[d + j]` the `DLP` word `s + j`, all else as it
was; a non-empty copy has a source other than `0`. -/
theorem dindCopyW_get (n : Nat) : ∀ (m m' : Mem) (d s l : Word), dindCopyW n m d s l = some m' →
    d.toNat + l.toNat ≤ (m.arr64 EREC).size → (m.arr64 EREC).size < 2 ^ 64 →
    MemFrame [EREC] [] m m' ∧ (l ≠ 0 → s ≠ 0) ∧
    ∀ i, (m'.arr64 EREC)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat then
        some (rdW (m.arr64 DLP) (s + UInt64.ofNat (i - d.toNat)))
      else (m.arr64 EREC)[i]? := by
  induction n with
  | zero => intro m m' d s l h; simp [dindCopyW] at h
  | succ n ih =>
    intro m m' d s l h hd hsz
    by_cases hl : l = 0
    · rw [dindCopyW_nil n m d s l hl] at h
      cases h
      subst hl
      refine ⟨MemFrame.refl _ _ _, fun h => absurd rfl h, fun i => ?_⟩
      have : ¬ (d.toNat ≤ i ∧ i < d.toNat + (0 : Word).toNat) := by
        simp only [UInt64.toNat_zero]; omega
      simp only [this, if_false]
    by_cases hs : s = 0
    · rw [dindCopyW_src n m d s l hl hs] at h; cases h
    rw [dindCopyW_step n m d s l hl hs] at h
    have hl0 : 0 < l.toNat := by
      have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
      omega
    have hl1 : (l - 1).toNat = l.toNat - 1 := by
      have := l.toNat_lt
      rw [UInt64.toNat_sub]; simp; omega
    have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hdlt : d.toNat < (m.arr64 EREC).size := by omega
    obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.set64 EREC d (rdW (m.arr64 DLP) s) := ⟨_, rfl⟩
    rw [← hm1] at h
    have hsz1 : (m1.arr64 EREC).size = (m.arr64 EREC).size := by
      rw [hm1, Mem.arr64_set64_same]; simp
    have hP1 : m1.arr64 DLP = m.arr64 DLP := by
      rw [hm1, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    have hf1 : MemFrame [EREC] [] m m1 := by rw [hm1]; exact MemFrame.set64 m EREC (by decide) _ _
    have hget1 : ∀ i, (m1.arr64 EREC)[i]? = if i = d.toNat then some (rdW (m.arr64 DLP) s)
        else (m.arr64 EREC)[i]? := by
      intro i
      rw [hm1, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases hi : d.toNat = i
      · subst hi; simp [hdlt]
      · simp [hi, Ne.symm hi]
    obtain ⟨hF, -, hG⟩ := ih m1 m' (d + 1) (s + 1) (l - 1) h
      (by rw [hd1, hl1, hsz1]; omega) (by rw [hsz1]; exact hsz)
    rw [hP1] at hG
    refine ⟨hf1.trans hF, fun _ => hs, fun i => ?_⟩
    rw [hG i, hd1, hl1]
    by_cases hi : d.toNat ≤ i ∧ i < d.toNat + l.toNat
    · rw [if_pos hi]
      by_cases hid : i = d.toNat
      · subst hid
        have : ¬ (d.toNat + 1 ≤ d.toNat ∧ d.toNat < d.toNat + 1 + (l.toNat - 1)) := by omega
        rw [if_neg this, hget1, if_pos rfl]; simp
      · have h2 : d.toNat + 1 ≤ i ∧ i < d.toNat + 1 + (l.toNat - 1) := by omega
        rw [if_pos h2]
        have e : i - d.toNat = (i - (d.toNat + 1)) + 1 := by omega
        rw [e, UInt64.ofNat_add]
        congr 2
        simp only [UInt64.ofNat_one]
        ac_rfl
    · rw [if_neg hi, if_neg (by omega), hget1, if_neg (by omega)]

/-- `dind_copy` into an allocated region is an `EREC` writer of that region. -/
theorem dindCopyW_EW {n : Nat} {m m' : Mem} {d s l : Word} (h : dindCopyW n m d s l = some m')
    (hd : d.toNat + l.toNat ≤ erTop m) (hr : erTop m ≤ (m.arr64 EREC).size)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) :
    EW (fun i => d.toNat ≤ i ∧ i < d.toNat + l.toNat) m m' := by
  obtain ⟨hF, -, hG⟩ := dindCopyW_get n m m' d s l h (by omega) hsz
  have hf : MemFrame [EREC] [129] m m' := hF.mono (by simp) (by simp)
  have ht : erTop m' = erTop m := by simp only [erTop, hF.2.1 129 (by simp)]
  refine ⟨hf, by omega, by rw [ht, hf.2.2.1 EREC]; exact hr, fun i _ hn => ?_⟩
  rw [hG i, if_neg hn]

/-! ## Reading the front's pool -/

/-- A word the cut pool holds (not its word `0`) is the pool's, read at any word index naming it. -/
theorem rdW_of_trunc {P : Array Word} {t x : Nat} {w v : Word} (h : (trunc P t)[x]? = some v)
    (hx : x ≠ 0) (hw : w.toNat = x) : rdW P w = v := by
  obtain ⟨hP, -⟩ := trunc_get h hx
  simp [rdW, hw, hP]

theorem trunc_lt {P : Array Word} {t x : Nat} {v : Word} (h : (trunc P t)[x]? = some v)
    (hx : x ≠ 0) : x < P.size := (Array.getElem?_eq_some_iff.mp (trunc_get h hx).1).1

theorem toNat_add_ofNat {s : Word} {k : Nat} (h : s.toNat + k < 2 ^ 64) :
    (s + UInt64.ofNat k).toNat = s.toNat + k := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; omega)]
  simp; omega

/-! ## `ind_rec_copy`'s record -/

/-- **The record's copy** (`nn` words from `s`, then word `2` := `q`, and for a recursor word
`7` := `r`), allocated at the top. -/
theorem ircT_ok {n : Nat} {mx m' : Mem} {s q r nn kw p : Word}
    (h : ircT n s q r nn kw (erAllocW mx nn) = some (p, m'))
    (hc : 129 < (mx.arr64 CTL).size) (hE64 : (mx.arr64 EREC).size < 2 ^ 64)
    (hr0 : erTop mx ≤ (mx.arr64 EREC).size) (hnn : 3 ≤ nn.toNat) (h5 : kw = 5 → 8 ≤ nn.toNat) :
    p.toNat = erTop mx ∧ erTop m' = erTop mx + nn.toNat ∧ EW (fun i => erTop mx ≤ i) mx m' ∧
      s ≠ 0 ∧ ∀ k < nn.toNat, (m'.arr64 EREC)[p.toNat + k]? =
        some (if k = 2 then q else if k = 7 ∧ kw = 5 then r
          else rdW (mx.arr64 DLP) (s + UInt64.ofNat k)) := by
  cases ha : erAllocW mx nn with
  | none => rw [ha] at h; cases h
  | some x =>
  obtain ⟨pp, m5⟩ := x
  rw [ha, ircT_some] at h
  obtain ⟨hpp, ht5, hE5, hW5⟩ := erAllocW_facts ha hc hE64
  have hw5 := hW5 (fun _ => False)
  cases hd : dindCopyW n m5 pp s nn with
  | none => rw [hd] at h; cases h
  | some m6 =>
  rw [hd, ircT2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hr5 := hw5.2.2.1
  have hs5 : (m5.arr64 EREC).size = (mx.arr64 EREC).size := by rw [hE5]
  obtain ⟨hF6, hsrc, hG6⟩ := dindCopyW_get n m5 m6 pp s nn hd (by rw [hs5]; omega) (by rw [hs5]; exact hE64)
  have hW6 := dindCopyW_EW hd (by omega) (by rw [hs5]; omega) (by rw [hs5]; exact hE64)
  have hP5 : m5.arr64 DLP = mx.arr64 DLP := hw5.dlp
  have hs6 : (m6.arr64 EREC).size = (mx.arr64 EREC).size := by rw [hW6.esize, hs5]
  have ht6 : erTop m6 = erTop m5 := by simp only [erTop, hF6.2.1 129 (by simp)]
  have hp2 : (pp + 2).toNat = pp.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have hp7 : (pp + 7).toNat = pp.toNat + 7 ∨ kw ≠ 5 := by
    by_cases hk : kw = 5
    · left; have := h5 hk; rw [UInt64.toNat_add]; simp; omega
    · right; exact hk
  have hs0 : s ≠ 0 := hsrc (fun h0 => by subst h0; simp at hnn)
  -- the two relocating writes
  have hWa := EW.set (x := pp + 2) (v := q) (m := m6) (by rw [ht6, hs6]; omega)
  have hta : erTop (m6.set64 EREC (pp + 2) q) = erTop m6 := by
    simp only [erTop, (MemFrame.set64 m6 EREC (by decide) (pp + 2) q).2.1 129 (by simp)]
  have hsa : ((m6.set64 EREC (pp + 2) q).arr64 EREC).size = (mx.arr64 EREC).size := by
    rw [size_set64, hs6]
  have hfin : EW (fun i => erTop mx ≤ i) mx (if kw = 5 then
      ((m6.set64 EREC (pp + 2) q).set64 EREC (pp + 7) r) else m6.set64 EREC (pp + 2) q) := by
    have h1 : EW (fun i => erTop mx ≤ i) mx (m6.set64 EREC (pp + 2) q) :=
      ((hW5 _).trans hW6 (fun i _ hi => by omega)).trans hWa (fun i _ hi => by omega)
    split
    · exact h1.trans (EW.set (by rw [hta, ht6, hsa]; omega)) (fun i _ hi => by
        rcases hp7 with h7 | h7
        · omega
        · contradiction)
    · exact h1
  refine ⟨hpp, ?_, hfin, hs0, fun k hk => ?_⟩
  · have := hfin.2.1
    split
    · simp only [erTop, (MemFrame.set64 _ EREC (by decide) (pp + 7) r).2.1 129 (by simp),
        (MemFrame.set64 m6 EREC (by decide) (pp + 2) q).2.1 129 (by simp)]
      simp only [erTop] at ht6 ht5; omega
    · simp only [erTop, (MemFrame.set64 m6 EREC (by decide) (pp + 2) q).2.1 129 (by simp)]
      simp only [erTop] at ht6 ht5; omega
  have hlt : pp.toNat + k < (m6.arr64 EREC).size := by rw [hs6]; omega
  have hcp : (m6.arr64 EREC)[pp.toNat + k]? = some (rdW (mx.arr64 DLP) (s + UInt64.ofNat k)) := by
    rw [hG6, if_pos (by omega), hP5, Nat.add_sub_cancel_left]
  have e2 : ((m6.set64 EREC (pp + 2) q).arr64 EREC)[pp.toNat + k]? =
      if k = 2 then some q else some (rdW (mx.arr64 DLP) (s + UInt64.ofNat k)) := by
    split
    · rename_i hk2; subst hk2; rw [← hp2]; exact set64_get_same (by rw [hp2]; omega)
    · rw [set64_get_ne (by rw [hp2]; omega), hcp]
  split
  · rename_i hk5
    rcases hp7 with h7 | h7
    · by_cases hk7 : k = 7
      · subst hk7; rw [← h7, set64_get_same (by rw [h7, hsa, ← hs6]; exact hlt)]; simp [hk5]
      · rw [set64_get_ne (by rw [h7]; omega), e2]
        by_cases hk2 : k = 2 <;> simp [hk2, hk7]
    · exact absurd hk5 h7
  · rename_i hk5
    rw [e2]
    by_cases hk2 : k = 2 <;> simp [hk2, hk5]

/-! ## From the copy's words to the relocation's premises -/

theorem shR_of_copy {P B : Array Word} {t : Nat} {sW : Word} {p : Nat} {K : Nat → Prop}
    (hs0 : sW ≠ 0) (hP : P.size < 2 ^ 63)
    (hcopy : ∀ k, K k → B[p + k]? = some (rdW P (sW + UInt64.ofNat k))) :
    ShR (trunc P t) B sW.toNat p K := by
  intro k v hk hv
  have hs : sW.toNat ≠ 0 := fun h0 => hs0 (UInt64.toNat_inj.mp (by simpa using h0))
  have hx : sW.toNat + k ≠ 0 := by omega
  have hlt := trunc_lt hv hx
  rw [hcopy k hk, rdW_of_trunc hv hx (toNat_add_ofNat (by omega))]

/-- A slice of the cut pool whose copy is at `q`. -/
theorem slice_of_copy {P B : Array Word} {t : Nat} {offW cntW : Word} {q : Nat}
    (hP : P.size < 2 ^ 63) (hne : cntW ≠ 0 → offW ≠ 0)
    (hcopy : ∀ j < cntW.toNat, B[q + j]? = some (rdW P (offW + UInt64.ofNat j))) :
    ∀ j v, j < cntW.toNat → (trunc P t)[offW.toNat + j]? = some v → B[q + j]? = some v := by
  intro j v hj hv
  have hc0 : cntW ≠ 0 := fun h0 => by subst h0; simp at hj
  have ho : offW.toNat ≠ 0 := fun h0 => hne hc0 (UInt64.toNat_inj.mp (by simpa using h0))
  have hx : offW.toNat + j ≠ 0 := by omega
  have hlt := trunc_lt hv hx
  rw [hcopy j hj, rdW_of_trunc hv hx (toNat_add_ofNat (by omega))]

/-- A header word the cut pool holds at `s + k` is the pool's word at the word index `s + k`. -/
theorem hdr_of_trunc {P : Array Word} {t : Nat} {sW : Word} {k x : Nat} (hP : P.size < 2 ^ 63)
    (hs0 : sW ≠ 0) (hx : nat? (trunc P t) (sW.toNat + k) = some x) :
    (rdW P (sW + UInt64.ofNat k)).toNat = x := by
  simp only [nat?, Option.map_eq_some_iff] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  have hs : sW.toNat ≠ 0 := fun h0 => hs0 (UInt64.toNat_inj.mp (by simpa using h0))
  have hlt := trunc_lt hw (by omega)
  rw [rdW_of_trunc hw (by omega) (toNat_add_ofNat (by omega))]

/-- **The relocation, from the copy's words.** -/
theorem decCI_of_copy {P B : Array Word} {t : Nat} {dn0 dn : NIdx → Option ConLeche.Name}
    {sW qW rW : Word} {p : Nat} {c : IConstantInfo}
    (hc : decCI (trunc P t) dn0 sW.toNat = some c) (hF : FrontCI c) (hP : P.size < 2 ^ 63)
    (hs0 : sW ≠ 0)
    (hkind : ∀ kk, nat? (trunc P t) sW.toNat = some kk → ∀ k, relocK kk k →
      B[p + k]? = some (rdW P (sW + UInt64.ofNat k)))
    (hq : B[p + 2]? = some qW)
    (hl : ∀ j < (rdW P (sW + 3)).toNat,
      B[qW.toNat + j]? = some (rdW P (rdW P (sW + 2) + UInt64.ofNat j)))
    (hl0 : rdW P (sW + 3) ≠ 0 → rdW P (sW + 2) ≠ 0)
    (hr : nat? (trunc P t) sW.toNat = some 5 → B[p + 7]? = some rW ∧
      (∀ x < 11 * (rdW P (sW + 8)).toNat,
        B[rW.toNat + x]? = some (rdW P (rdW P (sW + 7) + UInt64.ofNat x))) ∧
      (rdW P (sW + 8) ≠ 0 → rdW P (sW + 7) ≠ 0) ∧ (rdW P (sW + 8)).toNat < 2 ^ 60) :
    decCI B dn p = some c := by
  refine decCI_reloc (q := qW.toNat) (r := rW.toNat) hc hF
    (fun kk hkk => shR_of_copy hs0 hP (hkind kk hkk)) (by simp [nat?, hq]) ?_ ?_
  · intro off cnt hoff hcnt
    have e2 := hdr_of_trunc (k := 2) hP hs0 hoff
    have e3 := hdr_of_trunc (k := 3) hP hs0 hcnt
    simp only [show UInt64.ofNat 2 = 2 from rfl, show UInt64.ofNat 3 = 3 from rfl] at e2 e3
    rw [← e2, ← e3]
    exact slice_of_copy hP hl0 hl
  · intro h5
    obtain ⟨h7, hrs, hr0, hb⟩ := hr h5
    refine ⟨by simp [nat?, h7], fun off cnt hoff hcnt => ?_⟩
    have e7 := hdr_of_trunc (k := 7) hP hs0 hoff
    have e8 := hdr_of_trunc (k := 8) hP hs0 hcnt
    simp only [show UInt64.ofNat 7 = 7 from rfl, show UInt64.ofNat 8 = 8 from rfl] at e7 e8
    rw [← e7, ← e8]
    have hcw : (UInt64.ofNat (11 * (rdW P (sW + 8)).toNat)).toNat = 11 * (rdW P (sW + 8)).toNat :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; omega)
    have hcp := slice_of_copy (t := t) (cntW := UInt64.ofNat (11 * (rdW P (sW + 8)).toNat)) hP
      (fun hne => hr0 (fun h0 => hne (by rw [h0]; rfl))) (fun j hj => hrs j (by rw [hcw] at hj; exact hj))
    intro x v hx hv
    exact hcp x v (by rw [hcw]; exact hx) hv

end L.Arena
