import ConAgua.Arena.DeclAndPinIndCopy
import ConAgua.Arena.DeclAndPinInd
import ConAgua.Arena.DeclAndPinIndDec
import ConAgua.Arena.SimLib

/-!
# The `And` pin's inductive arm, part 2c: what the copy's pieces leave

`ErW W m m'`: an `EREC` writer (only `EREC` and its top `CTL[129]` change, the top grows within
the array) that changes no word below the old top outside `W`. Allocations, `dind_copy` and the
relocating writes are `ErW`s; they compose (`ErW.trans`). `dindCopyW_get`: the words a copy leaves.
-/

open ConRon.Arena

namespace L.Arena

open L.Front (DECL DLP trunc decCIs IndDeclAt dw)
open L.Ind (erAllocW erAllocMem erTop erecAlloc)

/-! ## `EREC` writers -/

/-- **An `EREC` writer**: only `EREC` and `CTL[129]` change, the top grows within the array, and
below the old top only the words `W` admits change. -/
def ErW (W : Nat → Prop) (m m' : Mem) : Prop :=
  MemFrame [EREC] [129] m m' ∧ erTop m ≤ erTop m' ∧ erTop m' ≤ (m'.arr64 EREC).size ∧
  ∀ i, i < erTop m → ¬ W i → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?

theorem ErW.refl (W : Nat → Prop) (m : Mem) (h : erTop m ≤ (m.arr64 EREC).size) : ErW W m m :=
  ⟨MemFrame.refl _ _ _, Nat.le_refl _, h, fun _ _ _ => rfl⟩

theorem ErW.trans {W W' : Nat → Prop} {m₁ m₂ m₃ : Mem} (h₁ : ErW W m₁ m₂) (h₂ : ErW W' m₂ m₃)
    (hW : ∀ i, i < erTop m₁ → W' i → W i) : ErW W m₁ m₃ :=
  ⟨h₁.1.trans h₂.1, Nat.le_trans h₁.2.1 h₂.2.1, h₂.2.2.1, fun i hi hn =>
    (h₂.2.2.2 i (Nat.lt_of_lt_of_le hi h₁.2.1) (fun hw => hn (hW i hi hw))).trans
      (h₁.2.2.2 i hi hn)⟩

theorem ErW.mono {W W' : Nat → Prop} {m m' : Mem} (h : ErW W m m') (hW : ∀ i, W i → W' i) :
    ErW W' m m' :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi hn => h.2.2.2 i hi (fun hw => hn (hW i hw))⟩

theorem ErW.dlp {W : Nat → Prop} {m m' : Mem} (h : ErW W m m') : m'.arr64 DLP = m.arr64 DLP :=
  h.1.1 DLP (by decide) (by decide)

theorem ErW.decl {W : Nat → Prop} {m m' : Mem} (h : ErW W m m') : m'.arr64 DECL = m.arr64 DECL :=
  h.1.1 DECL (by decide) (by decide)

theorem ErW.esize {W : Nat → Prop} {m m' : Mem} (h : ErW W m m') :
    (m'.arr64 EREC).size = (m.arr64 EREC).size := h.1.2.2.1 EREC

theorem ErW.csize {W : Nat → Prop} {m m' : Mem} (h : ErW W m m') :
    (m'.arr64 CTL).size = (m.arr64 CTL).size := h.1.2.2.1 CTL

/-- **`erec_alloc(k)`**: the pointer is the old top, the top moves by `k` within the array,
nothing else changes. -/
theorem erAllocW_facts {m m1 : Mem} {k o : Word} (h : erAllocW m k = some (o, m1))
    (hc : 129 < (m.arr64 CTL).size) (hE64 : (m.arr64 EREC).size < 2 ^ 64) :
    o.toNat = erTop m ∧ erTop m1 = erTop m + k.toNat ∧ m1.arr64 EREC = m.arr64 EREC ∧
      (∀ W, ErW W m m1) := by
  simp only [erAllocW] at h
  have h1 : ¬ m.len64 EREC < rdW (m.arr64 CTL) 129 := fun h1 => by simp [h1] at h
  have h2 : ¬ m.len64 EREC - rdW (m.arr64 CTL) 129 < k := fun h2 => by simp [h1, h2] at h
  simp only [h1, h2, ite_false, Option.some.injEq, Prod.mk.injEq] at h
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
    rw [ite_eq_left ⟨trivial, trivial, h129⟩, UInt64.toNat_add]
    omega
  refine ⟨rfl, htop, hE, fun W => ⟨hf, by omega, ?_, fun i _ _ => by rw [hE]⟩⟩
  rw [htop, hE]; simp only [erTop]; omega

/-- A word written below the top. -/
theorem ErW.set {m : Mem} {x v : Word}
    (hr : erTop m ≤ (m.arr64 EREC).size) :
    ErW (fun i => i = x.toNat) m (m.set64 EREC x v) := by
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
      simp only [this, ite_false]
    have hs : ¬ s = 0 := fun hs => by rw [dindCopyW_src n m d s l hl hs] at h; cases h
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
    · rw [ite_eq_left hi]
      by_cases hid : i = d.toNat
      · subst hid
        have : ¬ (d.toNat + 1 ≤ d.toNat ∧ d.toNat < d.toNat + 1 + (l.toNat - 1)) := by omega
        rw [ite_eq_right this, hget1, ite_eq_left rfl]; simp
      · have h2 : d.toNat + 1 ≤ i ∧ i < d.toNat + 1 + (l.toNat - 1) := by omega
        rw [ite_eq_left h2]
        have e : i - d.toNat = (i - (d.toNat + 1)) + 1 := by omega
        rw [e, UInt64.ofNat_add]
        congr 2
        simp only [UInt64.ofNat_one]
        ac_rfl
    · rw [ite_eq_right hi, ite_eq_right (by omega), hget1, ite_eq_right (by omega)]

/-- `dind_copy` into an allocated region is an `EREC` writer of that region. -/
theorem dindCopyW_EW {n : Nat} {m m' : Mem} {d s l : Word} (h : dindCopyW n m d s l = some m')
    (hd : d.toNat + l.toNat ≤ erTop m) (hr : erTop m ≤ (m.arr64 EREC).size)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) :
    ErW (fun i => d.toNat ≤ i ∧ i < d.toNat + l.toNat) m m' := by
  obtain ⟨hF, -, hG⟩ := dindCopyW_get n m m' d s l h (by omega) hsz
  have hf : MemFrame [EREC] [129] m m' := hF.mono (by simp) (by simp)
  have ht : erTop m' = erTop m := by simp only [erTop, hF.2.1 129 (by simp)]
  refine ⟨hf, by omega, by rw [ht, hf.2.2.1 EREC]; exact hr, fun i _ hn => ?_⟩
  rw [hG i, ite_eq_right hn]

/-! ## Reading the front's pool -/

/-- A word the cut pool holds (not its word `0`) is the pool's, read at any word index naming it. -/
theorem rdW_of_trunc {P : Array Word} {t x : Nat} {w v : Word} (h : (trunc P t)[x]? = some v)
    (hx : x ≠ 0) (hw : w.toNat = x) : rdW P w = v := by
  obtain ⟨hP, -⟩ := trunc_getAP h hx
  simp [rdW, hw, hP]

theorem trunc_lt {P : Array Word} {t x : Nat} {v : Word} (h : (trunc P t)[x]? = some v)
    (hx : x ≠ 0) : x < P.size := (Array.getElem?_eq_some_iff.mp (trunc_getAP h hx).1).1

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
    p.toNat = erTop mx ∧ erTop m' = erTop mx + nn.toNat ∧ ErW (fun i => erTop mx ≤ i) mx m' ∧
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
  have hWa := ErW.set (x := pp + 2) (v := q) (m := m6) (by rw [ht6, hs6]; omega)
  have hta : erTop (m6.set64 EREC (pp + 2) q) = erTop m6 := by
    simp only [erTop, (MemFrame.set64 m6 EREC (by decide) (pp + 2) q).2.1 129 (by simp)]
  have hsa : ((m6.set64 EREC (pp + 2) q).arr64 EREC).size = (mx.arr64 EREC).size := by
    rw [size_set64, hs6]
  have hfin : ErW (fun i => erTop mx ≤ i) mx (if kw = 5 then
      ((m6.set64 EREC (pp + 2) q).set64 EREC (pp + 7) r) else m6.set64 EREC (pp + 2) q) := by
    have h1 : ErW (fun i => erTop mx ≤ i) mx (m6.set64 EREC (pp + 2) q) :=
      ((hW5 _).trans hW6 (fun i _ hi => by omega)).trans hWa (fun i _ hi => by omega)
    split
    · exact h1.trans (ErW.set (by rw [hta, ht6, hsa]; omega)) (fun i _ hi => by
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
    rw [hG6, ite_eq_left (by omega), hP5, Nat.add_sub_cancel_left]
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

/-! ## `ind_rec_copy` -/

/-- **A record decoding robustly**: in every array that agrees with `A` on `[lo, hi)`, the
record at `p` decodes to `c`. -/
def RecRob (dn : NIdx → Option ConLeche.Name) (A : Array Word) (lo hi p : Nat)
    (c : IConstantInfo) : Prop :=
  ∀ B : Array Word, (∀ i, lo ≤ i → i < hi → B[i]? = A[i]?) → decCI B dn p = some c

theorem decCI_front_kind {T : Array Word} {dn0 : NIdx → Option ConLeche.Name} {x : Nat}
    {c : IConstantInfo} (hc : decCI T dn0 x = some c) (hF : FrontCI c) :
    ∃ kk, nat? T x = some kk ∧ (kk = 3 ∨ kk = 4 ∨ kk = 5) := by
  unfold decCI at hc
  cases hk : nat? T x with
  | none => simp [hk] at hc
  | some kk =>
  refine ⟨kk, rfl, ?_⟩
  rw [hk] at hc
  simp only [bind, Option.bind_some] at hc
  rcases kk with _ | _ | _ | _ | _ | _ | kk
  · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
    obtain ⟨_, -, rfl⟩ := hc; exact hF.elim
  · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
    obtain ⟨_, -, _, -, _, -, rfl⟩ := hc; exact hF.elim
  · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
    obtain ⟨_, -, rfl⟩ := hc; exact hF.elim
  · simp
  · simp
  · simp
  · simp at hc

/-- The common end of `ind_rec_copy`'s three kinds: the record's copy at the top of `mx`, where
the level parameters (and a recursor's rules) were already copied. -/
theorem irc_fin {n : Nat} {m mx m' : Mem} {t : Nat} {dn0 dn : NIdx → Option ConLeche.Name}
    {s q r nn kw p : Word} {kk : Nat} {c : IConstantInfo}
    (hT : ircT n s q r nn kw (erAllocW mx nn) = some (p, m'))
    (hwx : ErW (fun i => erTop m ≤ i) m mx)
    (hC : 129 < (m.arr64 CTL).size) (hE64 : (m.arr64 EREC).size < 2 ^ 64)
    (hc : decCI (trunc (m.arr64 DLP) t) dn0 s.toNat = some c) (hF : FrontCI c)
    (hP : (m.arr64 DLP).size < 2 ^ 63)
    (hkk : nat? (trunc (m.arr64 DLP) t) s.toNat = some kk) (hkw : kw.toNat = kk)
    (hnn : nn.toNat = if kk = 3 then 20 else if kk = 4 then 7 else 9) (hk345 : kk = 3 ∨ kk = 4 ∨ kk = 5)
    (hql : erTop m ≤ q.toNat) (hlr : q.toNat + (rdW (m.arr64 DLP) (s + 3)).toNat ≤ erTop mx)
    (hl : ∀ j < (rdW (m.arr64 DLP) (s + 3)).toNat, (mx.arr64 EREC)[q.toNat + j]? =
      some (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) (s + 2) + UInt64.ofNat j)))
    (hl0 : rdW (m.arr64 DLP) (s + 3) ≠ 0 → rdW (m.arr64 DLP) (s + 2) ≠ 0)
    (hr : kk = 5 → erTop m ≤ r.toNat ∧ r.toNat + 11 * (rdW (m.arr64 DLP) (s + 8)).toNat ≤ erTop mx ∧
      (∀ x < 11 * (rdW (m.arr64 DLP) (s + 8)).toNat, (mx.arr64 EREC)[r.toNat + x]? =
        some (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) (s + 7) + UInt64.ofNat x))) ∧
      (rdW (m.arr64 DLP) (s + 8) ≠ 0 → rdW (m.arr64 DLP) (s + 7) ≠ 0) ∧
      (rdW (m.arr64 DLP) (s + 8)).toNat < 2 ^ 60) :
    ErW (fun i => erTop m ≤ i) m m' ∧ erTop m ≤ p.toNat ∧
      RecRob dn (m'.arr64 EREC) (erTop m) (erTop m') p.toNat c := by
  have hCx : 129 < (mx.arr64 CTL).size := by rw [hwx.csize]; exact hC
  have hEx : (mx.arr64 EREC).size < 2 ^ 64 := by rw [hwx.esize]; exact hE64
  have hn3 : 3 ≤ nn.toNat := by rw [hnn]; split <;> (try split) <;> omega
  have hn5 : kw = 5 → 8 ≤ nn.toNat := fun h5 => by
    subst h5; rw [hnn]; simp at hkw; subst hkw; decide
  obtain ⟨hp, ht', hW', hs0, hwords⟩ := ircT_ok hT hCx hEx hwx.2.2.1 hn3 hn5
  have hPx : mx.arr64 DLP = m.arr64 DLP := hwx.dlp
  have hmx := hwx.2.1
  have hkw5' : kw = 5 → kk = 5 := fun h => by subst h; simp at hkw; omega
  have hall : ErW (fun i => erTop m ≤ i) m m' := hwx.trans hW' (fun i _ hi => by have := hwx.2.1; omega)
  refine ⟨hall, by have := hwx.2.1; omega, fun B hB => ?_⟩
  -- unchanged words of `mx` below its top
  have hkeep : ∀ i, erTop m ≤ i → i < erTop mx → B[i]? = (mx.arr64 EREC)[i]? := fun i h1 h2 => by
    rw [hB i h1 (by omega)]
    exact hW'.2.2.2 i h2 (by omega)
  refine decCI_of_copy (qW := q) (rW := r) hc hF hP hs0 (fun kk' hkk' k hk => ?_) ?_ (fun j hj => ?_) hl0 (fun h5 => ?_)
  · rw [hkk] at hkk'; cases hkk'
    obtain ⟨hk1, hk2, hk7⟩ := hk
    have hkn : k < nn.toNat := by rw [hnn]; exact hk1
    rw [hB _ (by omega) (by omega), hwords k hkn, hPx]
    rw [ite_eq_right hk2, ite_eq_right (fun ⟨h7, h5⟩ => by subst h5; simp at hkw; exact hk7 hkw.symm h7)]
  · rw [hB _ (by omega) (by omega), hwords 2 (by omega)]; rfl
  · rw [hkeep _ (by omega) (by omega)]; exact hl j hj
  · have h5' : kk = 5 := by rw [hkk] at h5; cases h5; rfl
    obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hr h5'
    refine ⟨?_, fun x hx => ?_, hr4, hr5⟩
    · have hkw5 : kw = 5 := UInt64.toNat_inj.mp (by rw [hkw, h5']; rfl)
      have := hn5 hkw5
      rw [hB _ (by omega) (by omega), hwords 7 (by omega)]
      simp [hkw5]
    · rw [hkeep _ (by omega) (by omega)]; exact hr3 x hx

/-- **`ind_rec_copy(s)` copies a front constant record**: an `EREC` writer above the old top,
the copy at `p` decoding (robustly, `RecRob`) to the record's constant. -/
theorem ircW_ok {n : Nat} {m m' : Mem} {t : Nat} {dn0 dn : NIdx → Option ConLeche.Name}
    {s p : Word} {c : IConstantInfo} (h : ircW n m s = some (p, m'))
    (hc : decCI (trunc (m.arr64 DLP) t) dn0 s.toNat = some c) (hF : FrontCI c)
    (hP : (m.arr64 DLP).size < 2 ^ 63) (hC : 129 < (m.arr64 CTL).size)
    (hE64 : (m.arr64 EREC).size < 2 ^ 64) :
    ErW (fun i => erTop m ≤ i) m m' ∧ erTop m ≤ p.toNat ∧
      RecRob dn (m'.arr64 EREC) (erTop m) (erTop m') p.toNat c := by
  cases n with
  | zero => simp [ircW] at h
  | succ n =>
  rw [ircW_step] at h
  obtain ⟨kk, hkk, hk345⟩ := decCI_front_kind hc hF
  obtain ⟨kw, hTk, rfl⟩ : ∃ kw, (trunc (m.arr64 DLP) t)[s.toNat]? = some kw ∧ kw.toNat = kk := by
    simpa [nat?] using hkk
  have hs0n : s.toNat ≠ 0 := fun h0 => by
    rw [h0] at hTk; have := trunc_get_zero hTk; subst this; simp at hk345
  have hkw : rdW (m.arr64 DLP) s = kw := rdW_of_trunc hTk hs0n rfl
  rw [hkw] at h
  cases ha1 : erAllocW m (rdW (m.arr64 DLP) (s + 3)) with
  | none => rw [ha1] at h; cases h
  | some x =>
  obtain ⟨q, m1⟩ := x
  rw [ha1, ircK1_some] at h
  obtain ⟨hq, ht1, hE1, hW1⟩ := erAllocW_facts ha1 hC hE64
  have hw1 := hW1 (fun i => erTop m ≤ i)
  have hP1 : m1.arr64 DLP = m.arr64 DLP := hw1.dlp
  rw [hP1] at h
  cases hd2 : dindCopyW n m1 q (rdW (m.arr64 DLP) (s + 2)) (rdW (m.arr64 DLP) (s + 3)) with
  | none => rw [hd2] at h; cases h
  | some m2 =>
  rw [hd2, ircK2_some] at h
  have hs1 : (m1.arr64 EREC).size = (m.arr64 EREC).size := by rw [hE1]
  have hr1 := hw1.2.2.1
  obtain ⟨-, hsrc2, hG2⟩ := dindCopyW_get n m1 m2 q _ _ hd2 (by omega) (by rw [hs1]; exact hE64)
  have hW2 := dindCopyW_EW hd2 (by omega) hr1 (by rw [hs1]; exact hE64)
  have hw2 : ErW (fun i => erTop m ≤ i) m m2 := hw1.trans hW2 (fun i _ hi => by omega)
  have hP2 : m2.arr64 DLP = m.arr64 DLP := hw2.dlp
  rw [hP2] at h
  have hl : ∀ j < (rdW (m.arr64 DLP) (s + 3)).toNat, (m2.arr64 EREC)[q.toNat + j]? =
      some (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) (s + 2) + UInt64.ofNat j)) := by
    intro j hj; rw [hG2, ite_eq_left (by omega), Nat.add_sub_cancel_left, hP1]
  have hlr : q.toNat + (rdW (m.arr64 DLP) (s + 3)).toNat ≤ erTop m2 := by have := hW2.2.1; omega
  have hm2 := hw2.2.1
  rcases hk345 with h3 | h4 | h5
  · have e : kw = 3 := UInt64.toNat_inj.mp (by rw [h3]; rfl)
    subst e
    rw [ite_eq_left rfl] at h
    exact irc_fin h hw2 hC hE64 hc hF hP hkk rfl (by rfl) (Or.inl rfl) (by omega) hlr hl hsrc2
      (fun h5 => by simp at h5)
  · have e : kw = 4 := UInt64.toNat_inj.mp (by rw [h4]; rfl)
    subst e
    rw [ite_eq_right (by decide), ite_eq_left rfl] at h
    exact irc_fin h hw2 hC hE64 hc hF hP hkk rfl (by rfl) (Or.inr (Or.inl rfl)) (by omega) hlr hl
      hsrc2 (fun h5 => by simp at h5)
  · have e : kw = 5 := UInt64.toNat_inj.mp (by rw [h5]; rfl)
    subst e
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl] at h
    obtain ⟨hg, h⟩ := of_ite_none h
    have hb : (rdW (m.arr64 DLP) (s + 8)).toNat < 2 ^ 60 := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hg); simpa using this
    have h11 : (11 * rdW (m.arr64 DLP) (s + 8)).toNat = 11 * (rdW (m.arr64 DLP) (s + 8)).toNat := by
      rw [UInt64.toNat_mul]; simp; omega
    have hC2 : 129 < (m2.arr64 CTL).size := by rw [hw2.csize]; exact hC
    have hE2 : (m2.arr64 EREC).size < 2 ^ 64 := by rw [hw2.esize]; exact hE64
    cases ha3 : erAllocW m2 (11 * rdW (m.arr64 DLP) (s + 8)) with
    | none => rw [ha3] at h; cases h
    | some x =>
    obtain ⟨r, m3⟩ := x
    rw [ha3, ircR1_some] at h
    obtain ⟨hr, ht3, hE3, hW3⟩ := erAllocW_facts ha3 hC2 hE2
    have hw3 := hW3 (fun i => erTop m ≤ i)
    have hP3 : m3.arr64 DLP = m.arr64 DLP := by rw [hw3.dlp, hP2]
    rw [hP3] at h
    cases hd4 : dindCopyW n m3 r (rdW (m.arr64 DLP) (s + 7)) (11 * rdW (m.arr64 DLP) (s + 8)) with
    | none => rw [hd4] at h; cases h
    | some m4 =>
    rw [hd4, ircR2_some] at h
    have hs3 : (m3.arr64 EREC).size = (m2.arr64 EREC).size := by rw [hE3]
    have hr3 := hw3.2.2.1
    obtain ⟨-, hsrc4, hG4⟩ := dindCopyW_get n m3 m4 r _ _ hd4 (by omega) (by rw [hs3]; exact hE2)
    have hW4 := dindCopyW_EW hd4 (by omega) hr3 (by rw [hs3]; exact hE2)
    have hw4 : ErW (fun i => erTop m ≤ i) m m4 :=
      (hw2.trans hw3 (fun i _ hi => hi)).trans hW4 (fun i _ hi => by omega)
    have hm4 := hW4.2.1
    refine irc_fin h hw4 hC hE64 hc hF hP hkk rfl (by rfl) (Or.inr (Or.inr rfl)) (by omega)
      (by omega) (fun j hj => ?_) hsrc2 (fun _ => ⟨by omega, by omega, fun x hx => ?_,
        fun h8 => hsrc4 (fun h0 => h8 (by
          apply UInt64.toNat_inj.mp; have := congrArg UInt64.toNat h0; rw [h11] at this; simp at this ⊢; omega)), hb⟩)
    · rw [hW4.2.2.2 _ (by omega) (by omega), hE3]; exact hl j hj
    · rw [hG4, ite_eq_left (by omega), Nat.add_sub_cancel_left, hP3]

/-! ## `ind_copy_go` -/

/-- **`ind_copy_go(o, bo, bl)` copies a front block**: the slots `[o, o + bl)` and fresh records
above the old top written, and in every array agreeing with the result from `o` to the new top
the slots decode (`decCIs`) to the block. -/
theorem icgW_ok {t : Nat} {dn0 dn : NIdx → Option ConLeche.Name} (n : Nat) :
    ∀ (m m' : Mem) (o bo bl : Word) (block : List IConstantInfo), icgW n m o bo bl = some m' →
      decCIs (trunc (m.arr64 DLP) t) dn0 bo.toNat bl.toNat = some block → FrontBlock block →
      (m.arr64 DLP).size < 2 ^ 63 → 129 < (m.arr64 CTL).size →
      (m.arr64 EREC).size < 2 ^ 64 → erTop m ≤ (m.arr64 EREC).size →
      o.toNat + bl.toNat ≤ erTop m →
      ErW (fun i => (o.toNat ≤ i ∧ i < o.toNat + bl.toNat) ∨ erTop m ≤ i) m m' ∧
      ∀ B : Array Word, (∀ i, o.toNat ≤ i → i < erTop m' → B[i]? = (m'.arr64 EREC)[i]?) →
        decCIs B dn o.toNat bl.toNat = some block := by
  induction n with
  | zero => intro m m' o bo bl block h; simp [icgW] at h
  | succ n ih =>
  intro m m' o bo bl block h hdec hFB hP hC hE64 hr0 hob
  by_cases hl : bl = 0
  · rw [icgW_nil n m o bo bl hl] at h
    cases h; subst hl
    simp only [UInt64.toNat_zero, decCIs_zero] at hdec
    cases hdec
    exact ⟨ErW.refl _ _ hr0, fun _ _ => rfl⟩
  rw [icgW_step n m o bo bl hl] at h
  have hl0 : bl.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  have hl1 : (bl - 1).toNat = bl.toNat - 1 := by
    have := bl.toNat_lt; rw [UInt64.toNat_sub]; simp; omega
  obtain ⟨k, hk⟩ : ∃ k, bl.toNat = k + 1 := ⟨bl.toNat - 1, by omega⟩
  rw [hk, decCIs_succ] at hdec
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdec
  obtain ⟨c, ⟨v, hv, hc⟩, cs, hcs, rfl⟩ := hdec
  obtain ⟨w, hw, rfl⟩ : ∃ w, (trunc (m.arr64 DLP) t)[bo.toNat]? = some w ∧ w.toNat = v := by
    simpa [nat?] using hv
  have hFc : FrontCI c := hFB c (by simp)
  have hbo : bo.toNat ≠ 0 := fun h0 => by
    rw [h0] at hw
    have := trunc_get_zero hw; subst this
    obtain ⟨kk, hkk, hk345⟩ := decCI_front_kind hc hFc
    simp only [nat?, Option.map_eq_some_iff, UInt64.toNat_zero] at hkk
    obtain ⟨a, ha, rfl⟩ := hkk
    rw [hw] at ha; cases ha; simp at hk345
  have hrd : rdW (m.arr64 DLP) bo = w := rdW_of_trunc hw hbo rfl
  have hblt := trunc_lt hw hbo
  rw [hrd] at h
  cases hi : ircW n m w with
  | none => rw [hi] at h; cases h
  | some x =>
  obtain ⟨p, m1⟩ := x
  rw [hi, icgK_some] at h
  obtain ⟨hW1, hp1, hR1⟩ := ircW_ok (dn := dn) hi hc hFc hP hC hE64
  have hm1 := hW1.2.1
  have hWs := ErW.set (x := o) (v := p) hW1.2.2.1
  have ho1 : (o + 1).toNat = o.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; have := hW1.2.2.1; omega
  have hbo1 : (bo + 1).toNat = bo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have ht2 : erTop (m1.set64 EREC o p) = erTop m1 := by
    simp only [erTop, (MemFrame.set64 m1 EREC (by decide) o p).2.1 129 (by simp)]
  have hs2 : ((m1.set64 EREC o p).arr64 EREC).size = (m.arr64 EREC).size := by
    rw [size_set64, hW1.esize]
  have hP2 : (m1.set64 EREC o p).arr64 DLP = m.arr64 DLP := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hW1.dlp]
  obtain ⟨hW3, hB3⟩ := ih (m1.set64 EREC o p) m' (o + 1) (bo + 1) (bl - 1) cs h
    (by rw [hP2, hbo1, hl1, hk]; exact hcs) (fun c' hc' => hFB c' (by simp [hc']))
    (by rw [hP2]; exact hP) (by rw [size_set64, hW1.csize]; exact hC) (by rw [hs2]; exact hE64)
    (by rw [ht2, hs2, ← hW1.esize]; exact hW1.2.2.1) (by rw [ho1, hl1, ht2]; omega)
  have ht3 := hW3.2.1
  rw [ht2] at ht3
  refine ⟨((hW1.mono (fun i hi => Or.inr hi)).trans hWs (fun i _ hi => by left; omega)).trans hW3
    (fun i _ hi => by rw [ho1, hl1, ht2] at hi; omega), fun B hB => ?_⟩
  rw [hk, decCIs_succ]
  -- the slot
  have hslot : B[o.toNat]? = some p := by
    rw [hB _ (Nat.le_refl _) (by omega), hW3.2.2.2 _ (by rw [ht2]; omega) (by rw [ho1]; omega)]
    exact set64_get_same (by rw [hW1.esize]; omega)
  have hc' : decCI B dn p.toNat = some c := hR1 B fun i h1 h2 => by
    rw [hB i (by omega) (by omega), hW3.2.2.2 _ (by rw [ht2]; omega) (by rw [ho1, hl1, ht2]; omega),
      set64_get_ne (by omega)]
  have hcs' := hB3 B (fun i h1 h2 => hB i (by rw [ho1] at h1; omega) h2)
  rw [ho1, hl1, hk] at hcs'
  simp only [nat?, hslot, Option.map_some, bind, Option.bind_some, hc', Nat.add_sub_cancel] at hcs' ⊢
  rw [hcs']; rfl

/-! ## `ind_block_to_erec` -/

theorem erecP_get_lt {m : Mem} {j : Nat} (h : j < erTop m) : (erecP m)[j]? = (m.arr64 EREC)[j]? := by
  simp only [erecP, Array.getElem?_extract]
  split
  · simp
  · rename_i h'
    simp only [erTop, erecTop] at h h' ⊢
    rw [Array.getElem?_eq_none (by omega)]

/-- Word `c + 8 i` of `DECL` is word `c - 1` of record `i` (`dw`), for a record that exists. -/
theorem rdW_dwI {D : Array Word} {i c : Word} {k : Nat} (hD : D.size < 2 ^ 63)
    (h0 : dw D i.toNat 0 ≠ 0) (hc : c.toNat = k + 1) (hk : k < 8) :
    rdW D (c + 8 * i) = dw D i.toNat k := by
  have hi : 1 + 8 * i.toNat < D.size := by
    refine Decidable.byContradiction fun hn => h0 ?_
    simp only [dw, Nat.add_zero]
    rw [Array.getElem?_eq_none (by omega)]; rfl
  have e : (c + 8 * i).toNat = 1 + 8 * i.toNat + k := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  simp only [rdW, dw, e]

/-- **`ind_block_to_erec(i)` on the front's inductive record `i`** (model level): the stage
relation kept, the pool grown, and the result an `EREC` slice below the top decoding to the
block. -/
theorem ibeW_ok {n : Nat} {m m' : Mem} {i : Word} {r : List Word} {block : List IConstantInfo}
    {nP : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    (h : ibeW n m i = some (r, m')) (hS : L.Ind.StageR dn vis fe m a)
    (hdecl : IndDeclAt (m.arr64 DECL) (m.arr64 DLP) i.toNat block nP) (hFB : FrontBlock block)
    (hD : (m.arr64 DECL).size < 2 ^ 63) (hP : (m.arr64 DLP).size < 2 ^ 63) :
    L.Ind.StageR dn vis fe m' a ∧ L.Ind.IWGrow m m' ∧ MemFrame [EREC] [129] m m' ∧
      r = [r.headD 0, r.tail.headD 0] ∧ (r.tail.headD 0).toNat = block.length ∧
      decCIs (erecP m') dn (r.headD 0).toNat (r.tail.headD 0).toNat = some block ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ erTop m' := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  obtain ⟨h6, -, t, -, hdec⟩ := hdecl
  have h0 : dw (m.arr64 DECL) i.toNat 0 ≠ 0 := by rw [h6]; decide
  have e3 : rdW (m.arr64 DECL) (3 + 8 * i) = dw (m.arr64 DECL) i.toNat 2 := rdW_dwI hD h0 rfl (by decide)
  have e4 : rdW (m.arr64 DECL) (4 + 8 * i) = dw (m.arr64 DECL) i.toNat 3 := rdW_dwI hD h0 rfl (by decide)
  simp only [ibeW, e3, e4] at h
  cases ha : erAllocW m (dw (m.arr64 DECL) i.toNat 3) with
  | none => rw [ha] at h; cases h
  | some x =>
  obtain ⟨o, m1⟩ := x
  rw [ha] at h
  simp only at h
  rcases hg : icgW n m1 o (dw (m.arr64 DECL) i.toNat 2) (dw (m.arr64 DECL) i.toNat 3) with _ | m2 <;> simp only [hg, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hC : 129 < (m.arr64 CTL).size := by omega
  obtain ⟨ho, ht1, hE1', hW1⟩ := erAllocW_facts ha hC hEs
  have hw1 := hW1 (fun j => erTop m ≤ j)
  obtain ⟨hW2, hB2⟩ := icgW_ok (dn := dn) n m1 m2 o _ _ block hg (by rw [hw1.dlp]; exact hdec) hFB
    (by rw [hw1.dlp]; exact hP) (by rw [hw1.csize]; exact hC) (by rw [hw1.esize]; exact hEs)
    hw1.2.2.1 (by omega)
  have hw : ErW (fun j => erTop m ≤ j) m m2 := hw1.trans hW2 (fun j _ hj => by omega)
  have hlen : block.length = (dw (m.arr64 DECL) i.toNat 3).toNat := by
    have := L.Ind.mapM_opt_length _ _ _ hdec; simpa using this
  obtain ⟨hS', hg'⟩ := L.Ind.StageR.erec hS hw.1 (fun j hj => hw.2.2.2 j hj (by omega)) hw.2.1 hw.2.2.1
  refine ⟨hS', hg', hw.1, rfl, by simp [hlen], ?_, by simp; have := hW2.2.1; omega⟩
  simp only [List.headD_cons, List.tail_cons]
  exact hB2 (erecP m2) (fun j _ hj => erecP_get_lt hj)

/-- `ind_block_to_erec`'s lookups. -/
structure IbeProg (p : Prog) : Prop where
  erec_alloc : p.lookup "erec_alloc" = some erecAlloc
  dind_copy : p.lookup "dind_copy" = some dindCopy
  ind_rec_copy : p.lookup "ind_rec_copy" = some indRecCopy
  ind_copy_go : p.lookup "ind_copy_go" = some indCopyGo
  ind_block_to_erec : p.lookup "ind_block_to_erec" = some indBlockToErec

/-- **`ind_block_to_erec(i)` copies the front's inductive record `i` into `EREC`** (`IndDeclAt`,
a block of the front's shape `FrontBlock`): the stage relation kept at the same twin state, the
pools grown, only `EREC` and its top written, and the result `[o, l]` an `EREC` slice of record
pointers below the top that decodes (`decCIs`, in `erecP`) to the block. -/
theorem indBlockToErec_ok {p : Prog} (hp : IbeProg p) {n : Nat} {m m' : Mem} {i : Word}
    {r : List Word} {block : List IConstantInfo} {nP : Nat} {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {a : AState}
    (hc : callW p n "ind_block_to_erec" [i] m = some (r, m')) (hS : L.Ind.StageR dn vis fe m a)
    (hdecl : IndDeclAt (m.arr64 DECL) (m.arr64 DLP) i.toNat block nP) (hFB : FrontBlock block)
    (hD : (m.arr64 DECL).size < 2 ^ 63) (hP : (m.arr64 DLP).size < 2 ^ 63) :
    L.Ind.StageR dn vis fe m' a ∧ L.Ind.IWGrow m m' ∧ MemFrame [EREC] [129] m m' ∧
      r = [r.headD 0, r.tail.headD 0] ∧ (r.tail.headD 0).toNat = block.length ∧
      decCIs (erecP m') dn (r.headD 0).toNat (r.tail.headD 0).toNat = some block ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ erTop m' := by
  obtain ⟨s', rfl, -, n', hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (indBlockToErec_specW p hp.erec_alloc hp.dind_copy hp.ind_rec_copy hp.ind_copy_go
      hp.ind_block_to_erec n ⟨m, Locals.init []⟩ i) hc
  exact ibeW_ok hW hS hdecl hFB hD hP

end L.Arena
