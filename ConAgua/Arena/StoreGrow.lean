import ConAgua.Arena.StoreLib

/-!
# The store library: the growth keeps the relation (lane kstp)

`SlotGrowSpec.lean`'s `kgrowM` (the KSTP growth of one tier: the doubled table at the tier's other
offset, zeroed, then every live slot of the old table re-inserted with its key word from the
home of `G` of the key word), read as the table relation: if `G` of every admissible key word is
the node's hash (`hGh`), the relation holds after the growth (`storeR_kgrow`).
-/

open ConRon.Arena

set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## Zeroing -/

theorem rdW_oob (a : Array Word) (x : Word) (h : a.size ≤ x.toNat) : rdW a x = 0 := by
  simp [rdW, h]

theorem rdW_set64_zero (m : Mem) (a b : ArrId) (k x : Word) :
    rdW ((m.set64 a k 0).arr64 b) x = if b = a ∧ k = x then 0 else rdW (m.arr64 b) x := by
  rw [rdW_set64]
  by_cases h : b = a
  · subst h
    by_cases hk : k = x
    · subst hk
      by_cases hs : k.toNat < (m.arr64 b).size
      · simp [hs]
      · simp [hs, rdW_oob (m.arr64 b) k (by omega)]
    · simp [hk]
  · simp [h]

theorem zero8_rd (sa : ArrId) (k : Word) (m : Mem) (x : Word) (hk : k.toNat + 8 < 2 ^ 64) :
    rdW ((zero8 sa k m).arr64 sa) x =
      if k.toNat ≤ x.toNat ∧ x.toNat < k.toNat + 8 then 0 else rdW (m.arr64 sa) x := by
  simp only [zero8, rdW_set64_zero, true_and]
  have e : ∀ i : Nat, i < 8 → (k + UInt64.ofNat i).toNat = k.toNat + i := fun i hi => by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']; omega
  have e1 := e 1 (by omega); have e2 := e 2 (by omega); have e3 := e 3 (by omega)
  have e4 := e 4 (by omega); have e5 := e 5 (by omega); have e6 := e 6 (by omega)
  have e7 := e 7 (by omega)
  simp only [UInt64.ofNat_one] at e1
  simp only [show UInt64.ofNat 2 = 2 from rfl, show UInt64.ofNat 3 = 3 from rfl,
    show UInt64.ofNat 4 = 4 from rfl, show UInt64.ofNat 5 = 5 from rfl,
    show UInt64.ofNat 6 = 6 from rfl, show UInt64.ofNat 7 = 7 from rfl] at *
  have hx : ∀ y : Word, (y = x) = (y.toNat = x.toNat) := fun y => by
    simp [UInt64.toNat_inj]
  simp only [hx, e1, e2, e3, e4, e5, e6, e7]
  grind (splits := 20)

/-- **The zero loop** zeroes the `8 e` words from `x` (no wrap) and changes no other word. -/
theorem kzeroW_rd (sa : ArrId) : ∀ (e : Nat) (x : Word) (m : Mem), x.toNat + 8 * e < 2 ^ 64 →
    ∀ y, rdW ((kzeroW sa x e m).arr64 sa) y =
      if x.toNat ≤ y.toNat ∧ y.toNat < x.toNat + 8 * e then 0 else rdW (m.arr64 sa) y
  | 0, x, m, _, y => by
    simp only [kzeroW, Nat.mul_zero, Nat.add_zero]
    split
    · omega
    · rfl
  | e + 1, x, m, hx, y => by
    have e8 : (x + 8).toNat = x.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
    simp only [kzeroW]
    rw [kzeroW_rd sa e (x + 8) _ (by omega) y, zero8_rd sa x m y (by omega)]
    simp only [e8]
    by_cases hA : x.toNat + 8 ≤ y.toNat ∧ y.toNat < x.toNat + 8 + 8 * e <;>
      by_cases hB : x.toNat ≤ y.toNat ∧ y.toNat < x.toNat + 8 <;>
      by_cases hC : x.toNat ≤ y.toNat ∧ y.toNat < x.toNat + 8 * (e + 1) <;>
      simp only [hA, hB, hC, ↓reduceIte] <;> first | rfl | (exfalso; omega)

/-! ## The walk -/

/-- Value `v` lies on the run from slot `x` of the table at word `r` (`n` slots), after nonzero
value words. -/
def FoundW (sl : Array Word) (n r x v : Word) : Prop :=
  ∃ d : Nat, rdW sl (r + walkW n x d * 2) = v ∧ ∀ e < d, rdW sl (r + walkW n x e * 2) ≠ 0

/-- The growth's probe: its result is the first zero value word on the run. -/
theorem kprobeW_found (sl : Array Word) (r n x : Word) :
    ∀ (f : Nat) (d j : Word), n.toNat - d.toNat ≤ f →
      (∀ e < d.toNat, rdW sl (r + walkW n x e * 2) ≠ 0) →
      kprobeW sl r n (walkW n x d.toNat) d = some j →
      ∃ D : Nat, j = walkW n x D ∧ rdW sl (r + j * 2) = 0 ∧
        ∀ e < D, rdW sl (r + walkW n x e * 2) ≠ 0 := by
  intro f
  induction f with
  | zero =>
    intro d j hf hd h
    rw [kprobeW] at h
    have hnd : n ≤ d := UInt64.le_iff_toNat_le.mpr (by omega)
    by_cases h0 : rdW sl (r + walkW n x d.toNat * 2) = 0
    · simp only [h0, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨d.toNat, rfl, h0, hd⟩
    · simp [h0, hnd] at h
  | succ f ih =>
    intro d j hf hd h
    rw [kprobeW] at h
    by_cases h0 : rdW sl (r + walkW n x d.toNat * 2) = 0
    · simp only [h0, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨d.toNat, rfl, h0, hd⟩
    by_cases hnd : n ≤ d
    · simp [h0, hnd] at h
    simp only [h0, hnd, ↓reduceIte] at h
    have hlt : d.toNat < n.toNat := by
      have := mt UInt64.le_iff_toNat_le.mpr hnd; omega
    have e1 : (d + 1).toNat = d.toNat + 1 := by
      have := n.toNat_lt; rw [UInt64.toNat_add]; simp; omega
    rw [← walkW_succ, ← e1] at h
    refine ih (d + 1) j (by omega) (fun e he => ?_) h
    rw [e1] at he
    by_cases hed : e = d.toNat
    · subst hed; exact h0
    · exact hd e (by omega)

theorem rdW_set64_in (m : Mem) (a : ArrId) (k v x : Word) (hk : k.toNat < (m.arr64 a).size) :
    rdW ((m.set64 a k v).arr64 a) x = if k = x then v else rdW (m.arr64 a) x := by
  rw [rdW_set64]; simp [hk]

/-- A write of a value at a zero value word (and of its key word after it) keeps every nonzero
value found. -/
theorem foundW_keep (sl sl' : Array Word) (n r x v p : Word) (h : FoundW sl n r x v) (hv : v ≠ 0)
    (hp : rdW sl p = 0) (hpar : ∀ e, r + walkW n x e * 2 ≠ p + 1)
    (hsl : ∀ y, y ≠ p → y ≠ p + 1 → rdW sl' y = rdW sl y) : FoundW sl' n r x v := by
  obtain ⟨d, h1, h2⟩ := h
  refine ⟨d, ?_, fun e he => ?_⟩
  · rw [hsl _ (fun hy => by rw [hy, hp] at h1; exact hv h1.symm) (hpar d)]; exact h1
  · have := h2 e he
    rw [hsl _ (fun hy => by rw [hy] at this; exact this hp) (hpar e)]; exact this

section walk
variable (sa : ArrId) (G : Mem → Word → Word) (KPm : Word → Word → Prop) (hsm : Word → Word)
  (N nb bt c ob : Word) (nold : Nat) (m2 : Mem) (sold : Array Word)

/-- The walk's invariant after `k` old slots, from the memory `m2` before it (the zeroed new
table): only the new table's words change; each of its value words is `0` or a live value
(above `bt`, at most `bt + c`) with a key word `KPm` admits for its node; every live old slot
so far is found from the home of its node's hash. -/
def WInv (mi : Mem) (k : Nat) : Prop :=
  (∀ a, a ≠ sa → mi.arr64 a = m2.arr64 a) ∧ (mi.arr64 sa).size = (m2.arr64 sa).size ∧
  (∀ y, (∀ j, j < N → y ≠ nb + j * 2 ∧ y ≠ nb + j * 2 + 1) →
    rdW (mi.arr64 sa) y = rdW (m2.arr64 sa) y) ∧
  (∀ j, j < N → rdW (mi.arr64 sa) (nb + j * 2) = 0 ∨
    (bt < rdW (mi.arr64 sa) (nb + j * 2) ∧
      (rdW (mi.arr64 sa) (nb + j * 2)).toNat ≤ bt.toNat + c.toNat ∧
      KPm (rdW (mi.arr64 sa) (nb + j * 2) - bt - 1) (rdW (mi.arr64 sa) (nb + j * 2 + 1)))) ∧
  (∀ j : Word, j.toNat < k → bt < rdW sold (ob + j * 2) →
    FoundW (mi.arr64 sa) N nb (homeW (hsm (rdW sold (ob + j * 2) - bt - 1)) N)
      (rdW sold (ob + j * 2)))

variable (hN0 : 0 < N)
  (hold : ∀ j : Word, j.toNat < nold → ∀ mi : Mem,
    (∀ y, (∀ j', j' < N → y ≠ nb + j' * 2 ∧ y ≠ nb + j' * 2 + 1) →
      rdW (mi.arr64 sa) y = rdW (m2.arr64 sa) y) →
    rdW (mi.arr64 sa) (ob + j * 2) = rdW sold (ob + j * 2) ∧
      rdW (mi.arr64 sa) (ob + j * 2 + 1) = rdW sold (ob + j * 2 + 1))
  (hpar : ∀ j j', j < N → j' < N → nb + j * 2 + 1 ≠ nb + j' * 2)
  (hinj : ∀ j j', j < N → j' < N → nb + j * 2 = nb + j' * 2 → j = j')
  (hin : ∀ j, j < N → (nb + j * 2 + 1).toNat < (m2.arr64 sa).size ∧
    (nb + j * 2).toNat < (m2.arr64 sa).size)
  (hsold : ∀ j : Word, j.toNat < nold → bt < rdW sold (ob + j * 2) →
    (rdW sold (ob + j * 2)).toNat ≤ bt.toNat + c.toNat ∧
      KPm (rdW sold (ob + j * 2) - bt - 1) (rdW sold (ob + j * 2 + 1)))
  (hGh : ∀ mi : Mem, (∀ a, a ≠ sa → mi.arr64 a = m2.arr64 a) → ∀ i K, KPm i K → G mi K = hsm i)
  (hnold : nold < 2 ^ 63)
include hN0 hold hpar hinj hin hsold hGh hnold

theorem kwalkW_inv : ∀ (e k : Nat) (mi mf : Mem), k + e = nold →
    WInv sa KPm hsm N nb bt c ob m2 sold mi k →
    kwalkW sa G N nb bt e (ob + UInt64.ofNat k * 2) mi = some mf →
    WInv sa KPm hsm N nb bt c ob m2 sold mf nold := by
  intro e
  induction e with
  | zero =>
    intro k mi mf hk hI h
    simp only [kwalkW, Option.some.injEq] at h
    subst h; simpa [← hk] using hI
  | succ e ih =>
    intro k mi mf hk hI h
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    have hkj : (UInt64.ofNat k).toNat = k := by
      rw [UInt64.toNat_ofNat_of_lt']; simp only [UInt64.size]; omega
    obtain ⟨o1, o2⟩ := hold (UInt64.ofNat k) (by omega) mi h3
    have ex2 : ob + UInt64.ofNat k * 2 + 2 = ob + UInt64.ofNat (k + 1) * 2 := by
      rw [UInt64.ofNat_add]; simp only [UInt64.ofNat_one]; grind
    simp only [kwalkW] at h
    split at h
    · -- a live old slot
      rename_i hv
      rw [o1] at hv
      split at h
      · cases h
      rename_i j hj
      simp only [o1, o2] at hj h
      rw [ex2] at h
      obtain ⟨hle, hkp⟩ := hsold (UInt64.ofNat k) (by omega) hv
      rw [hGh mi h1 _ _ hkp] at hj
      have hx : homeW (hsm (rdW sold (ob + UInt64.ofNat k * 2) - bt - 1)) N < N := homeW_lt _ _ hN0
      generalize hX : homeW (hsm (rdW sold (ob + UInt64.ofNat k * 2) - bt - 1)) N = X at hj hx
      obtain ⟨D, hD, hz, hfd⟩ := kprobeW_found (mi.arr64 sa) nb N X _ 0 j (Nat.le_refl _)
        (by simp) hj
      have hjn : j < N := by rw [hD]; exact walkW_lt _ _ _ hx
      obtain ⟨hin1, hin0⟩ := hin j hjn
      refine ih (k + 1) _ mf (by omega) ⟨?_, ?_, ?_, ?_, ?_⟩ h
      · intro a ha; rw [Mem.arr64_set64_ne _ _ _ _ _ ha, Mem.arr64_set64_ne _ _ _ _ _ ha]; exact h1 a ha
      · rw [size_set64, size_set64]; exact h2
      · intro y hy
        rw [rdW_set64_in _ _ _ _ _ (by rw [size_set64, h2]; exact hin1),
          rdW_set64_in _ _ _ _ _ (by rw [h2]; exact hin0)]
        rw [if_neg (fun h' => (hy j hjn).2 h'.symm), if_neg (fun h' => (hy j hjn).1 h'.symm)]
        exact h3 y hy
      · intro j' hj'
        rw [rdW_set64_in _ _ _ _ _ (by rw [size_set64, h2]; exact hin1),
          rdW_set64_in _ _ _ _ _ (by rw [h2]; exact hin0),
          rdW_set64_in _ _ _ _ _ (by rw [size_set64, h2]; exact hin1),
          rdW_set64_in _ _ _ _ _ (by rw [h2]; exact hin0)]
        rw [if_neg (fun h' => hpar j j' hjn hj' h')]
        by_cases hjj : nb + j * 2 = nb + j' * 2
        · have := hinj j j' hjn hj' hjj
          subst this
          simp only [↓reduceIte]
          right
          exact ⟨hv, hle, by simpa using hkp⟩
        · simp only [hjj, ↓reduceIte]
          rw [if_neg (fun h' => hjj (by
            have := congrArg (· - 1) h'; simpa using this)),
            if_neg (fun h' => hpar j' j hj' hjn h'.symm)]
          exact h4 j' hj'
      · intro j' hj' hv'
        by_cases hjk : j'.toNat = k
        · have : j' = UInt64.ofNat k := UInt64.toNat_inj.mp (by rw [hkj]; exact hjk)
          subst this
          rw [hX]
          refine ⟨D, ?_, fun e he => ?_⟩
          · rw [← hD, rdW_set64_in _ _ _ _ _ (by rw [size_set64, h2]; exact hin1),
              rdW_set64_in _ _ _ _ _ (by rw [h2]; exact hin0),
              if_neg (fun h' => hpar j j hjn hjn h'), if_pos rfl]
          · have := hfd e he
            have hwe := walkW_lt N _ e hx
            rw [rdW_set64_in _ _ _ _ _ (by rw [size_set64, h2]; exact hin1),
              rdW_set64_in _ _ _ _ _ (by rw [h2]; exact hin0)]
            rw [if_neg (fun h' => hpar j _ hjn hwe h'),
              if_neg (fun h' => by rw [← h'] at this; exact this hz)]
            exact this
        · have hfo := h5 j' (by omega) hv'
          refine foundW_keep _ _ N nb _ _ (nb + j * 2) hfo ?_ hz
            (fun e h' => hpar j _ hjn (walkW_lt _ _ _ (homeW_lt _ _ hN0)) h'.symm)
            (fun y hy1 hy2 => ?_)
          · intro h0
            rw [h0] at hv'
            have := UInt64.lt_iff_toNat_lt.mp hv'
            simp at this
          · rw [rdW_set64_in _ _ _ _ _ (by rw [size_set64, h2]; exact hin1),
              rdW_set64_in _ _ _ _ _ (by rw [h2]; exact hin0)]
            rw [if_neg (Ne.symm hy2), if_neg (Ne.symm hy1)]
    · -- a free or stale old slot
      rename_i hv
      rw [o1] at hv
      rw [ex2] at h
      refine ih (k + 1) mi mf (by omega) ⟨h1, h2, h3, h4, fun j' hj' hv' => ?_⟩ h
      by_cases hjk : j'.toNat = k
      · have : j' = UInt64.ofNat k := UInt64.toNat_inj.mp (by rw [hkj]; exact hjk)
        subst this; exact absurd hv' hv
      · exact h5 j' (by omega) hv'

end walk

end L.Arena
