import ConAgua.Arena.Frame
import ConAgua.Arena.Memo

/-!
# The memo relation: the L memo table represents a `Std.HashMap EIdx Nat`

`MemoR m mp` (the memo of `Memo.lean` against the arena's `bvarBC`): the live slots (stamp `=`
the live stamp) hold distinct keys, each a handle word mapped by `mp` to the slot's value, and
every entry of `mp` sits in a live slot on the run from its key's home slot, after live slots
(linear probing; a stale stamp is free space). The lemmas: a probe hit is `mp`'s entry
(`memoR_hit`), a miss is its absence (`memoR_miss`), `memo_set` is `insert` (`memoR_set`),
`memo_clear` is `∅` (`memoR_clear`), and other writers leave it alone (`memoR_frame`).
-/

open ConRon.Arena

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The stamp, key and value of memo slot `j`. -/
def mstamp (m : Mem) (j : Word) : Word := rdW (m.arr64 BMEMO) (j * 4)
def mkey (m : Mem) (j : Word) : Word := rdW (m.arr64 BMEMO) (j * 4 + 1)
def mval (m : Mem) (j : Word) : Word := rdW (m.arr64 BMEMO) (j * 4 + 2)

/-- Slot `e` of the run from the home slot of key `k`. -/
def mrun (m : Mem) (k : Word) (e : Nat) : Word := walkW (nM m) (homeW k (nM m)) e

/-- **The memo relation.** -/
def MemoR (m : Mem) (mp : Std.HashMap EIdx Nat) : Prop :=
  26 ≤ (m.arr64 CTL).size ∧ epW m ≠ 0 ∧
  (∀ j, j < nM m → (mstamp m j).toNat ≤ (epW m).toNat) ∧
  (∀ j, j < nM m → mstamp m j = epW m →
    (mkey m j).toNat < 2 ^ 32 ∧ mp[decE (mkey m j)]? = some (mval m j).toNat) ∧
  (∀ j j', j < nM m → j' < nM m → mstamp m j = epW m → mstamp m j' = epW m →
    mkey m j = mkey m j' → j = j') ∧
  (∀ (x : EIdx) (v : Nat), mp[x]? = some v → ∃ d : Nat,
    mstamp m (mrun m x.word.toUInt64 d) = epW m ∧ mkey m (mrun m x.word.toUInt64 d) = x.word.toUInt64 ∧
    ∀ e < d, mstamp m (mrun m x.word.toUInt64 e) = epW m)

/-! ## The probe -/

/-- The first `d` slots of the run of `k` are live and hold other keys. -/
def MNoMatch (m : Mem) (k : Word) (d : Nat) : Prop :=
  ∀ e < d, mstamp m (mrun m k e) = epW m ∧ mkey m (mrun m k e) ≠ k

/-- What the probe's result `rs` says: a hit is a live slot `rs[1]` with key `k`; a miss is the
non-live slot `rs[1]`, step `rs[2]` of the run, after live slots with other keys. -/
def MProbeOK (m : Mem) (k : Word) (rs : List Word) : Prop :=
  rs ≠ [] →
    (rs.headD 0 ≠ 0 → mstamp m (rs.tail.headD 0) = epW m ∧ mkey m (rs.tail.headD 0) = k ∧
      rs.tail.headD 0 < nM m) ∧
    (rs.headD 0 = 0 → rs.tail.headD 0 = mrun m k (rs.tail.tail.headD 0).toNat ∧
      rs.tail.headD 0 < nM m ∧ mstamp m (rs.tail.headD 0) ≠ epW m ∧
      MNoMatch m k (rs.tail.tail.headD 0).toNat)

theorem mprobe_ok (m : Mem) (k : Word) (hx : homeW k (nM m) < nM m) :
    ∀ (n : Nat) (d : Word), (nM m).toNat - d.toNat = n → MNoMatch m k d.toNat →
      MProbeOK m k (bmprobeW (m.arr64 BMEMO) k (epW m) (nM m) (mrun m k d.toNat) d) := by
  intro n
  induction n with
  | zero =>
    intro d hk _; rw [bmprobeW]; grind [MProbeOK]
  | succ n ih =>
    intro d hk hnm
    have := ih (d + 1)
    clear ih
    have hd : d < nM m := by grind
    have hd1 : (d + 1).toNat = d.toNat + 1 := by grind
    specialize this (by grind)
    have hlt : mrun m k d.toNat < nM m := walkW_lt _ _ _ hx
    rw [hd1, mrun, walkW_succ, ← mrun] at this
    rw [bmprobeW]
    by_cases h0 : rdW (m.arr64 BMEMO) (mrun m k d.toNat * 4) ≠ epW m
    · simp only [hd, h0, ↓reduceIte, ne_eq, not_false_eq_true]
      grind [MProbeOK, mstamp]
    by_cases hm : rdW (m.arr64 BMEMO) (mrun m k d.toNat * 4 + 1) = k
    · simp only [hd, h0, hm, ↓reduceIte, ne_eq, not_true_eq_false]
      grind [MProbeOK, mstamp, mkey]
    · simp only [hd, h0, hm, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true]
      exact this (by grind [MNoMatch, mstamp, mkey])

/-- The probe `memo_find` makes. -/
theorem mfind_ok (m : Mem) (k : Word) : MProbeOK m k (mfindW m k) := by
  by_cases hn : nM m = 0
  · simp only [mfindW]; rw [bmprobeW]; simp [hn, MProbeOK]
  · have := mprobe_ok m k (homeW_lt _ _ (by grind)) _ 0 rfl (by simp [MNoMatch])
    simpa [mrun, walkW, mfindW] using this

/-- The key word of a handle decoded from a word below `2^32`. -/
theorem word_decE (k : Word) (hk : k.toNat < 2 ^ 32) : (decE k).word.toUInt64 = k := by
  have := word_decI (decE k) k hk
  rw [decE_eq] at this ⊢
  exact this.mpr rfl

section rel
variable (m : Mem) (mp : Std.HashMap EIdx Nat) (hR : MemoR m mp) (k : Word) (hk : k.toNat < 2 ^ 32)

include hR in
/-- **A probe hit is the map's entry.** -/
theorem memoR_hit (hr : mfindW m k ≠ []) (hh : (mfindW m k).headD 0 ≠ 0) :
    mp[decE k]? = some (mval m ((mfindW m k).tail.headD 0)).toNat := by
  obtain ⟨h1, h2, h3⟩ := (mfind_ok m k hr).1 hh
  have := hR.2.2.2.1 _ h3 h1
  rw [h2] at this
  exact this.2

include hR hk in
/-- **A probe miss is the map's absence.** -/
theorem memoR_miss (hr : mfindW m k ≠ []) (hh : (mfindW m k).headD 0 = 0) :
    mp[decE k]? = none := by
  obtain ⟨hj, hlt, hfree, hnm⟩ := (mfind_ok m k hr).2 hh
  cases hc : mp[decE k]? with
  | none => rfl
  | some v =>
    exfalso
    obtain ⟨d, hd1, hd2, hd3⟩ := hR.2.2.2.2.2 _ _ hc
    rw [word_decE k hk] at hd1 hd2 hd3
    clear hR hc
    by_cases hlt' : d < ((mfindW m k).tail.tail.headD 0).toNat
    · exact (hnm d hlt').2 hd2
    · by_cases heq : d = ((mfindW m k).tail.tail.headD 0).toNat
      · subst heq; rw [← hj] at hd1; exact hfree hd1
      · have := hd3 ((mfindW m k).tail.tail.headD 0).toNat (by omega)
        rw [← hj] at this; exact hfree this

end rel

/-! ## `memo_set` and `memo_clear` -/

/-- The memory after `memo_set` when its probe found slot `j` (`fd ≠ 0`) or the free slot `j`. -/
theorem msetMem_arr (m : Mem) (fd j k v : Word) (b : ArrId) (hb : b ≠ BMEMO) (hc : b ≠ CTL) :
    (msetMem m fd j k v).arr64 b = m.arr64 b := by
  unfold msetMem; split <;> simp [Mem.arr64_set64_ne _ _ _ _ _ hb, Mem.arr64_set64_ne _ _ _ _ _ hc]

theorem msetMem_frame (m : Mem) (fd j k v : Word) :
    MemFrame [BMEMO] [25] m (msetMem m fd j k v) := by
  refine ⟨fun b hb hc => msetMem_arr m fd j k v b (by simpa using hb) hc, fun x hx => ?_,
    fun b => ?_, ?_⟩
  · have : x ≠ 25 := by simpa using hx
    unfold msetMem; split <;> simp only [rdW_set64] <;> grind
  · unfold msetMem; split <;> simp only [size_set64]
  · unfold msetMem; split <;> simp only [Mem.words_size_set64]

theorem msetW_frame (m m' : Mem) (k v : Word) (h : msetW m k v = some m') :
    MemFrame [BMEMO] [25] m m' := by
  simp only [msetW] at h
  split at h
  · simp at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h; subst h; exact msetMem_frame _ _ _ _ _

theorem mclearMem_frame (m : Mem) : MemFrame [] [24, 25] m (mclearMem m) := by
  have h1 := MemFrame.setCtl m 24 (rdW (m.arr64 CTL) 24 + 1)
  have h2 := MemFrame.setCtl (m.set64 CTL 24 (rdW (m.arr64 CTL) 24 + 1)) 25 0
  exact (h1.mono (by simp) (by simp)).trans (h2.mono (by simp) (by simp))

theorem nM_toNat (m : Mem) : (nM m).toNat = (m.arr64 BMEMO).size % 2 ^ 64 / 4 := by
  simp only [nM, len64_eq, UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  rfl

theorem nM_mul4 (m : Mem) : (nM m).toNat * 4 ≤ (m.arr64 BMEMO).size := by
  rw [nM_toNat]; have := (m.arr64 BMEMO).size.mod_le (2 ^ 64); omega

theorem nM_lt (m : Mem) : (nM m).toNat < 2 ^ 62 := by
  rw [nM_toNat]; have := Nat.mod_lt (m.arr64 BMEMO).size (show 0 < 2 ^ 64 by decide); omega

/-- Word `f < 4` of slot `x`. -/
theorem ad4 (m : Mem) (x : Word) (hx : x < nM m) (f : Word) (hf : f.toNat < 4) :
    (x * 4 + f).toNat = x.toNat * 4 + f.toNat := by
  have := nM_lt m
  have : x.toNat < (nM m).toNat := hx
  simp only [UInt64.toNat_add, UInt64.toNat_mul]
  rw [show (4 : Word).toNat = 4 from rfl, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem ad4_eq (m : Mem) (x y : Word) (hx : x < nM m) (hy : y < nM m) (f g : Word)
    (hf : f.toNat < 4) (hg : g.toNat < 4) : (x * 4 + f = y * 4 + g) ↔ (x = y ∧ f = g) := by
  constructor
  · intro h
    have h' := congrArg UInt64.toNat h
    rw [ad4 m x hx f hf, ad4 m y hy g hg] at h'
    exact ⟨UInt64.toNat_inj.mp (by omega), UInt64.toNat_inj.mp (by omega)⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem ad4_lt (m : Mem) (x : Word) (hx : x < nM m) (f : Word) (hf : f.toNat < 4) :
    (x * 4 + f).toNat < (m.arr64 BMEMO).size := by
  rw [ad4 m x hx f hf]; have := nM_mul4 m; have : x.toNat < (nM m).toNat := hx; omega

/-- A read of the memo after `memo_set`'s writes at slot `j`. -/
theorem msetMem_rd (m : Mem) (fd j k v : Word) (hj : j < nM m) (x : Word) :
    rdW ((msetMem m fd j k v).arr64 BMEMO) x =
      if x = j * 4 + 2 then v else if fd = 0 ∧ x = j * 4 + 1 then k
      else if fd = 0 ∧ x = j * 4 + 0 then epW m else rdW (m.arr64 BMEMO) x := by
  have l0 := ad4_lt m j hj 0 (by decide)
  have l1 := ad4_lt m j hj 1 (by decide)
  have l2 := ad4_lt m j hj 2 (by decide)
  have n1 : j * 4 + 1 ≠ j * 4 + 2 := fun h => by
    have := (ad4_eq m j j hj hj 1 2 (by decide) (by decide)).mp h; exact absurd this.2 (by decide)
  have n0 : j * 4 + 0 ≠ j * 4 + 2 := fun h => by
    have := (ad4_eq m j j hj hj 0 2 (by decide) (by decide)).mp h; exact absurd this.2 (by decide)
  have n01 : j * 4 + 0 ≠ j * 4 + 1 := fun h => by
    have := (ad4_eq m j j hj hj 0 1 (by decide) (by decide)).mp h; exact absurd this.2 (by decide)
  simp only [UInt64.add_zero] at l0 n0 n01 ⊢
  unfold msetMem
  by_cases hfd : fd = 0
  · simp only [hfd, ↓reduceIte, rdW_set64, size_set64, true_and,
      show (BMEMO : ArrId) ≠ CTL by decide, false_and, l0, l1, l2, and_true]
    by_cases h2 : x = j * 4 + 2
    · subst h2; simp
    by_cases h1 : x = j * 4 + 1
    · subst h1; simp [Ne.symm n1]
    by_cases h0 : x = j * 4
    · subst h0; simp [Ne.symm n0, Ne.symm n01]
    simp [Ne.symm h2, Ne.symm h1, Ne.symm h0, h2, h1, h0]
  · simp only [hfd, ↓reduceIte, rdW_set64, l2, true_and, false_and, and_true]
    by_cases h2 : x = j * 4 + 2
    · subst h2; simp
    · simp [Ne.symm h2, h2]

/-- Reads of the memo after `memo_set`'s writes at slot `j`. -/
theorem msetMem_reads (m : Mem) (fd j k v : Word) (hj : j < nM m) :
    epW (msetMem m fd j k v) = epW m ∧ nM (msetMem m fd j k v) = nM m ∧
    (∀ j', j' < nM m → mstamp (msetMem m fd j k v) j' =
      if j' = j ∧ fd = 0 then epW m else mstamp m j') ∧
    (∀ j', j' < nM m → mkey (msetMem m fd j k v) j' = if j' = j ∧ fd = 0 then k else mkey m j') ∧
    (∀ j', j' < nM m → mval (msetMem m fd j k v) j' = if j' = j then v else mval m j') := by
  have hf := msetMem_frame m fd j k v
  refine ⟨by simp only [epW, hf.2.1 24 (by decide)], by simp only [nM, len64_eq, hf.2.2.1],
    fun j' hj' => ?_, fun j' hj' => ?_, fun j' hj' => ?_⟩
  · have e := fun f g hf hg => ad4_eq m j' j hj' hj f g hf hg
    have e2 := e 0 2 (by decide) (by decide)
    have e1 := e 0 1 (by decide) (by decide)
    have e0 := e 0 0 (by decide) (by decide)
    simp only [UInt64.add_zero] at e2 e1 e0
    simp only [mstamp, msetMem_rd m fd j k v hj, UInt64.add_zero, e2, e1, e0]
    by_cases h : j' = j <;> by_cases hfd : fd = 0 <;> simp [h, hfd]
  · have e := fun f g hf hg => ad4_eq m j' j hj' hj f g hf hg
    have e2 := e 1 2 (by decide) (by decide)
    have e1 := e 1 1 (by decide) (by decide)
    have e0 := e 1 0 (by decide) (by decide)
    simp only [UInt64.add_zero] at e2 e1 e0
    simp only [mkey, msetMem_rd m fd j k v hj, UInt64.add_zero, e2, e1, e0]
    by_cases h : j' = j <;> by_cases hfd : fd = 0 <;> simp [h, hfd]
  · have e := fun f g hf hg => ad4_eq m j' j hj' hj f g hf hg
    have e2 := e 2 2 (by decide) (by decide)
    have e1 := e 2 1 (by decide) (by decide)
    have e0 := e 2 0 (by decide) (by decide)
    simp only [UInt64.add_zero] at e2 e1 e0
    simp only [mval, msetMem_rd m fd j k v hj, UInt64.add_zero, e2, e1, e0]
    by_cases h : j' = j <;> by_cases hfd : fd = 0 <;> simp [h, hfd]

theorem mrun_eq (m m' : Mem) (h : nM m' = nM m) (k : Word) (e : Nat) : mrun m' k e = mrun m k e := by
  simp only [mrun, h]

theorem mrun_lt (m : Mem) (k : Word) (e : Nat) (hn : 0 < nM m) : mrun m k e < nM m :=
  walkW_lt _ _ _ (homeW_lt _ _ hn)

/-- **`memo_set` is `insert`.** -/
theorem memoR_set (m : Mem) (mp : Std.HashMap EIdx Nat) (hR : MemoR m mp) (k v : Word)
    (hk : k.toNat < 2 ^ 32) (m' : Mem) (h : msetW m k v = some m') :
    MemoR m' (mp.insert (decE k) v.toNat) := by
  have hok := mfind_ok m k
  simp only [msetW] at h
  split at h
  · simp at h
  rename_i hne
  split at h
  · simp at h
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨hctl, hep, hst, hlive, huniq, hrun⟩ := hR
  have hmiss := fun hh => memoR_miss m mp ⟨hctl, hep, hst, hlive, huniq, hrun⟩ k hk hne hh
  have hhit := fun hh => memoR_hit m mp ⟨hctl, hep, hst, hlive, huniq, hrun⟩ k hne hh
  have hok' := hok hne
  generalize hrs : mfindW m k = rs at *
  obtain ⟨hhit', hmiss'⟩ := hok'
  have hj : rs.tail.headD 0 < nM m := by
    by_cases hh : rs.headD 0 = 0
    · exact (hmiss' hh).2.1
    · exact (hhit' hh).2.2
  obtain ⟨r1, r2, r3, r4, r5⟩ := msetMem_reads m (rs.headD 0) (rs.tail.headD 0) k v hj
  have hdk : (decE k).word.toUInt64 = k := word_decE k hk
  refine ⟨?_, by rw [r1]; exact hep, ?_, ?_, ?_, ?_⟩
  · have := (msetMem_frame m (rs.headD 0) (rs.tail.headD 0) k v).2.2.1 CTL; omega
  · intro j hj'; rw [r2] at hj'; rw [r3 j hj', r1]; have := hst j hj'; split <;> grind
  · intro j hj' hl
    rw [r2] at hj'
    rw [r3 j hj', r1] at hl
    rw [r4 j hj', r5 j hj']
    by_cases hjj : j = rs.tail.headD 0
    · subst hjj
      by_cases hh : rs.headD 0 = 0
      · simp only [hh, and_self, ↓reduceIte, Std.HashMap.getElem?_insert_self]
        refine ⟨?_, ?_⟩ <;> simp [hk]
      · obtain ⟨h1, h2, -⟩ := hhit' hh
        simp only [hh, and_false, ↓reduceIte, h2, Std.HashMap.getElem?_insert_self]
        refine ⟨?_, ?_⟩ <;> simp [hk]
    · simp only [hjj, false_and, ↓reduceIte] at hl ⊢
      obtain ⟨hk', hm⟩ := hlive j hj' hl
      refine ⟨hk', ?_⟩
      rw [Std.HashMap.getElem?_insert]
      have : ¬ (decE k == decE (mkey m j)) = true := by
        intro he
        have he' : decE k = decE (mkey m j) := beq_iff_eq.mp he
        have : k = mkey m j := by
          rw [← hdk, he', word_decE _ hk']
        by_cases hh : rs.headD 0 = 0
        · have h0 := hmiss hh; rw [this] at h0; rw [h0] at hm
          simp at hm
        · obtain ⟨h1, h2, -⟩ := hhit' hh
          exact hjj (huniq _ _ hj' hj hl h1 (by rw [h2, this]))
      simp only [this, Bool.false_eq_true, ↓reduceIte, hm]
  · intro j j' hj1 hj2 hl1 hl2 hkk
    rw [r2] at hj1 hj2
    rw [r3 j hj1, r1] at hl1
    rw [r3 j' hj2, r1] at hl2
    rw [r4 j hj1, r4 j' hj2] at hkk
    by_cases hh : rs.headD 0 = 0
    · -- the new key is absent from the old live slots
      have habs : ∀ j'', j'' < nM m → mstamp m j'' = epW m → mkey m j'' ≠ k := by
        intro j'' hj'' hl'' hk''
        have := (hlive j'' hj'' hl'').2
        rw [hk'', hmiss hh] at this; simp at this
      by_cases e1 : j = rs.tail.headD 0 <;> by_cases e2 : j' = rs.tail.headD 0
      · rw [e1, e2]
      · simp only [e1, e2, hh, and_self, ↓reduceIte, false_and] at hkk hl2
        exact absurd hkk.symm (habs j' hj2 hl2)
      · simp only [e1, e2, hh, and_self, ↓reduceIte, false_and] at hkk hl1
        exact absurd hkk (habs j hj1 hl1)
      · simp only [e1, e2, false_and, ↓reduceIte] at hkk hl1 hl2
        exact huniq j j' hj1 hj2 hl1 hl2 hkk
    · simp only [hh, and_false, ↓reduceIte] at hkk hl1 hl2
      exact huniq j j' hj1 hj2 hl1 hl2 hkk
  · intro x w hx
    rw [Std.HashMap.getElem?_insert] at hx
    have hn0 : 0 < nM m := by grind
    have hr := fun x e => mrun_eq m (msetMem m (rs.headD 0) (rs.tail.headD 0) k v) r2 x e
    by_cases hxk : (decE k == x) = true
    · have hxe : x = decE k := (beq_iff_eq.mp hxk).symm
      subst hxe
      rw [hdk]
      by_cases hh : rs.headD 0 = 0
      · obtain ⟨hj1, -, -, hnm⟩ := hmiss' hh
        refine ⟨(rs.tail.tail.headD 0).toNat, ?_, ?_, fun e he => ?_⟩
        · rw [hr, ← hj1, r3 _ hj, r1]; simp only [hh, and_self, ↓reduceIte]
        · rw [hr, ← hj1, r4 _ hj]; simp only [hh, and_self, ↓reduceIte]
        · have hlt := mrun_lt m k e hn0
          rw [hr, r3 _ hlt, r1]
          split
          · rfl
          · exact (hnm e he).1
      · have := hhit hh
        obtain ⟨d, hd1, hd2, hd3⟩ := hrun _ _ this
        rw [hdk] at hd1 hd2 hd3
        refine ⟨d, ?_, ?_, fun e he => ?_⟩
        · rw [hr, r3 _ (mrun_lt m k d hn0), r1]; simp only [hh, and_false, ↓reduceIte, hd1]
        · rw [hr, r4 _ (mrun_lt m k d hn0)]; simp only [hh, and_false, ↓reduceIte, hd2]
        · rw [hr, r3 _ (mrun_lt m k e hn0), r1]; simp only [hh, and_false, ↓reduceIte, hd3 e he]
    · simp only [hxk, Bool.false_eq_true, ↓reduceIte] at hx
      obtain ⟨d, hd1, hd2, hd3⟩ := hrun _ _ hx
      have hl : ∀ e, mstamp m (mrun m x.word.toUInt64 e) = epW m →
          mstamp (msetMem m (rs.headD 0) (rs.tail.headD 0) k v)
            (mrun (msetMem m (rs.headD 0) (rs.tail.headD 0) k v) x.word.toUInt64 e) =
            epW (msetMem m (rs.headD 0) (rs.tail.headD 0) k v) := by
        intro e he
        rw [hr, r3 _ (mrun_lt m _ e hn0), r1]
        split
        · rfl
        · exact he
      refine ⟨d, hl d hd1, ?_, fun e he => hl e (hd3 e he)⟩
      rw [hr, r4 _ (mrun_lt m _ d hn0)]
      split
      · -- a new key lands only in a non-live slot, but this slot is live
        rename_i hc
        obtain ⟨hc1, hc2⟩ := hc
        obtain ⟨-, -, hfree, -⟩ := hmiss' hc2
        exact absurd (hc1 ▸ hd1) hfree
      · exact hd2

/-- **`memo_clear` is `∅`.** -/
theorem memoR_clear (m : Mem) (mp : Std.HashMap EIdx Nat) (hR : MemoR m mp)
    (hw : rdW (m.arr64 CTL) 24 + 2 ≠ 0) : MemoR (mclearMem m) ∅ := by
  obtain ⟨hctl, hep, hst, -, -, -⟩ := hR
  have hf := mclearMem_frame m
  have hsz := hf.2.2.1
  have hb : (mclearMem m).arr64 BMEMO = m.arr64 BMEMO := hf.1 BMEMO (by simp) (by decide)
  have hn : nM (mclearMem m) = nM m := by simp only [nM, len64_eq, hb]
  have hs : ∀ j, mstamp (mclearMem m) j = mstamp m j := fun j => by simp only [mstamp, hb]
  have he : epW (mclearMem m) = epW m + 1 := by
    simp only [epW, mclearMem, rdW_set64, size_set64]; grind
  have hlt : ∀ j, j < nM m → (mstamp m j).toNat < (epW m + 1).toNat := by
    intro j hj
    have := hst j hj
    have : (epW m + 1).toNat = (epW m).toNat + 1 := by
      simp only [epW] at *; rw [UInt64.toNat_add]; grind
    omega
  refine ⟨by rw [hsz]; exact hctl, by rw [he]; simp only [epW] at *; grind, ?_, ?_, ?_, ?_⟩
  · intro j hj; rw [hn] at hj; rw [hs, he]; exact Nat.le_of_lt (hlt j hj)
  · intro j hj hl; rw [hn] at hj; rw [hs, he] at hl; have := hlt j hj; rw [hl] at this; omega
  · intro j j' hj _ hl _ _; rw [hn] at hj; rw [hs, he] at hl; have := hlt j hj; rw [hl] at this
    omega
  · intro x v hx; simp at hx

/-- **The memo relation survives a writer of other arrays and of `CTL` words other than the
stamp.** -/
theorem memoR_frame (A : List ArrId) (C : List Word) (hA : BMEMO ∉ A) (hC : (24 : Word) ∉ C)
    (m m' : Mem) (hf : MemFrame A C m m') (mp : Std.HashMap EIdx Nat) (hR : MemoR m mp) :
    MemoR m' mp := by
  have hb : m'.arr64 BMEMO = m.arr64 BMEMO := hf.1 BMEMO hA (by decide)
  have hn : nM m' = nM m := by simp only [nM, len64_eq, hb]
  have he : epW m' = epW m := by simp only [epW, hf.2.1 24 hC]
  have hs : ∀ j, mstamp m' j = mstamp m j := fun j => by simp only [mstamp, hb]
  have hk : ∀ j, mkey m' j = mkey m j := fun j => by simp only [mkey, hb]
  have hv : ∀ j, mval m' j = mval m j := fun j => by simp only [mval, hb]
  have hr : ∀ x e, mrun m' x e = mrun m x e := fun x e => by simp only [mrun, hn]
  obtain ⟨hctl, hep, hst, hlive, huniq, hrun⟩ := hR
  refine ⟨by rw [hf.2.2.1]; exact hctl, by rw [he]; exact hep, ?_, ?_, ?_, ?_⟩
  · intro j hj; rw [hs, he]; exact hst j (hn ▸ hj)
  · intro j hj hl; rw [hs, he] at hl; rw [hk, hv]; exact hlive j (hn ▸ hj) hl
  · intro j j' hj hj' hl hl' hkk; rw [hs, he] at hl hl'; rw [hk, hk] at hkk
    exact huniq j j' (hn ▸ hj) (hn ▸ hj') hl hl' hkk
  · intro x v hx
    obtain ⟨d, h1, h2, h3⟩ := hrun x v hx
    exact ⟨d, by rw [hr, hs, he]; exact h1, by rw [hr, hk]; exact h2,
      fun e hle => by rw [hr, hs, he]; exact h3 e hle⟩

end L.Arena
