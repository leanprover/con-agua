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

/-! ## The growth's numbers -/

section nat
variable (S : Schema) (m : Mem) (t : Word)

/-- **The growth's numbers**: with `n` slots at offset `o` (`L` words in all) and the room check
passed, the new table (`2 n` slots from `ns`) lies in the tier's half, apart from the old one
(`n` slots from `os`), and its offset `nb` is `8 n` or `0`. -/
theorem grow_nat (hG : GrowR S m) (ht : t ≤ 1) (hc : ¬ gchkW S.sa t m) :
    let L := (m.arr64 S.sa).size
    let n := (knW S.sa m t).toNat
    let o := (koW S.sa m t).toNat
    let nb := if o = 0 then 8 * n else 0
    (gnbW S.sa t m).toNat = nb ∧ (knW S.sa m t * 2).toNat = 2 * n ∧
    (knW S.sa m t * 2 * 2).toNat = 4 * n ∧ (knW S.sa m t >>> 1).toNat * 8 = 4 * n ∧
    (gobsW S.sa t m) = krW S.sa m t ∧
    4 ≤ (gnbsW S.sa t m).toNat ∧ (gnbsW S.sa t m).toNat + 4 * n ≤ L ∧
    (t = 0 → (gnbsW S.sa t m).toNat + 4 * n ≤ L / 2 ∧ (gnbsW S.sa t m).toNat = nb + 4) ∧
    (t = 1 → L / 2 ≤ (gnbsW S.sa t m).toNat ∧ (gnbsW S.sa t m).toNat = L - nb - 4 * n) ∧
    ((gnbsW S.sa t m).toNat + 4 * n ≤ (krW S.sa m t).toNat ∨
      (krW S.sa m t).toNat + 2 * n ≤ (gnbsW S.sa t m).toNat) ∧
    (t = 0 → 4 + nb + 2 * (2 * n) ≤ L / 2) ∧ (t = 1 → L / 2 + nb + 2 * (2 * n) ≤ L) ∧
    8 ≤ n ∧ n % 8 = 0 ∧ L < 2 ^ 62 := by
  intro L n o nb
  have hL := sa_len64_toNat S m hG.1
  have hl := lay S m hG t ht
  obtain ⟨hs, h0, h1⟩ := hG
  have hT : TierLay S m t := by rcases le_one_cases t ht with rfl | rfl <;> assumption
  obtain ⟨a1, a2, a3, a4, a5⟩ := hT
  have hn : n ≤ 2 ^ 60 := by
    rcases le_one_cases t ht with rfl | rfl
    · have := a4 rfl; omega
    · have := a5 rfl; omega
  have e2 : (knW S.sa m t * 2).toNat = 2 * n := by rw [UInt64.toNat_mul]; simp; omega
  have e4 : (knW S.sa m t * 2 * 2).toNat = 4 * n := by rw [UInt64.toNat_mul, e2]; simp; omega
  have eh : (knW S.sa m t >>> 1).toNat * 8 = 4 * n := by
    rw [UInt64.toNat_shiftRight]; simp; omega
  have eQ : (gQW S.sa t m).toNat = if t = 0 then L / 2 - 4 else L - L / 2 := by
    have eH : (m.len64 S.sa >>> 1).toNat = L / 2 := by
      rw [UInt64.toNat_shiftRight, hL]; simp [Nat.shiftRight_eq_div_pow, L]
    simp only [gQW]
    split
    · rename_i h; subst h
      have := a4 rfl
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, eH]; simp; omega), eH]; simp
    · rename_i h
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, eH, hL]; omega), eH, hL]
  have hQ : (gQW S.sa t m).toNat ≤ 2 ^ 61 := by rw [eQ]; split <;> omega
  -- the room check, as numbers
  have hcn : nb + 4 * n ≤ (gQW S.sa t m).toNat ∧ 8 * n < 2 ^ 64 := by
    simp only [gchkW, gnbW, UInt64.not_lt] at hc
    rw [UInt64.le_iff_toNat_le] at hc
    by_cases ho : koW S.sa m t = 0
    · have ho' : o = 0 := by simp [o, ho]
      simp only [ho, ↓reduceIte] at hc
      rw [UInt64.toNat_add, UInt64.toNat_mul, e2, e4] at hc
      simp only [nb, ho', ↓reduceIte]
      have h1 : (2 * n * 4) % 2 ^ 64 = 8 * n := by omega
      have h2 : (8 * n + 4 * n) % 2 ^ 64 = 12 * n := by omega
      simp only [UInt64.toNat_ofNat, show (4 : Word).toNat = 4 from rfl] at hc
      rw [show 2 * n * 4 % 18446744073709551616 = 8 * n by omega] at hc
      constructor
      · omega
      · omega
    · have ho' : o ≠ 0 := fun h => ho (UInt64.toNat_inj.mp (by simpa [o] using h))
      simp only [ho, ↓reduceIte] at hc
      rw [UInt64.toNat_add, e4] at hc
      simp only [nb, ho', ↓reduceIte]
      simp at hc; constructor <;> omega
  have enb : (gnbW S.sa t m).toNat = nb := by
    simp only [gnbW]
    by_cases ho : koW S.sa m t = 0
    · have ho' : o = 0 := by simp [o, ho]
      simp only [ho, ↓reduceIte, nb, ho']
      rw [UInt64.toNat_mul, e2]; simp; omega
    · have ho' : o ≠ 0 := fun h => ho (UInt64.toNat_inj.mp (by simpa [o] using h))
      simp only [ho, ↓reduceIte, nb, ho']; rfl
  have hob : gobsW S.sa t m = krW S.sa m t := rfl
  have hnb : nb = 8 * n ∨ nb = 0 := by simp only [nb]; split <;> simp
  have hnbo : (o = 0 → nb = 8 * n) ∧ (o ≠ 0 → nb = 0) := by simp only [nb]; constructor <;> intro h <;> simp [h]
  refine ⟨enb, e2, e4, eh, hob, ?_⟩
  rcases le_one_cases t ht with rfl | rfl
  · have a4 := a4 rfl
    rw [eQ] at hcn; simp only [↓reduceIte] at hcn
    have ens : (gnbsW S.sa 0 m).toNat = nb + 4 := by
      simp only [gnbsW, ↓reduceIte]; rw [UInt64.toNat_add, enb]; simp; omega
    have ekr : (krW S.sa m 0).toNat = o + 4 := by
      simp only [krW, ↓reduceIte]; rw [UInt64.toNat_add]; simp; omega
    rw [ens, ekr]
    refine ⟨by omega, by omega, fun _ => ⟨by omega, rfl⟩, fun h => absurd h (by decide), ?_,
      fun _ => by omega, fun h => absurd h (by decide), a1, a2, hs⟩
    rcases a3 with a3 | a3
    · have := hnbo.1 a3; omega
    · by_cases ho : o = 0
      · have := hnbo.1 ho; omega
      · have := hnbo.2 ho; omega
  · have a5 := a5 rfl
    rw [eQ] at hcn; simp only [show (1 : Word) ≠ 0 by decide, ↓reduceIte] at hcn
    have ens : (gnbsW S.sa 1 m).toNat = L - nb - 4 * n := by
      simp only [gnbsW, show (1 : Word) ≠ 0 by decide, ↓reduceIte]
      rw [UInt64.toNat_sub_of_le, UInt64.toNat_sub_of_le, hL, enb, e4]
      · rw [UInt64.le_iff_toNat_le, hL, enb]; omega
      · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le, hL, enb, e4]
        · omega
        · rw [UInt64.le_iff_toNat_le, hL, enb]; omega
    have ekr : (krW S.sa m 1).toNat = L - o - 2 * n := by
      have := hl.2.2.2.2 rfl
      simp only [krW, show (1 : Word) ≠ 0 by decide, ↓reduceIte]
      rw [UInt64.toNat_sub_of_le, UInt64.toNat_sub_of_le, hL]
      · rw [UInt64.toNat_mul]; simp; omega
      · rw [UInt64.le_iff_toNat_le, hL]; omega
      · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le, hL]
        · rw [UInt64.toNat_mul]; simp; omega
        · rw [UInt64.le_iff_toNat_le, hL]; omega
    rw [ens, ekr]
    refine ⟨by omega, by omega, fun h => absurd h (by decide), fun _ => ⟨by omega, rfl⟩, ?_,
      fun h => absurd h (by decide), fun _ => by omega, a1, a2, hs⟩
    rcases a3 with a3 | a3
    · have := hnbo.1 a3; omega
    · by_cases ho : o = 0
      · have := hnbo.1 ho; omega
      · have := hnbo.2 ho; omega

end nat

/-! ## A tier whose words stay -/

section keep
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)
  (KP : Mem → Word → Word → Word → Prop)

/-- **A tier stays represented when its count and offset words and its table's words stay**, and
only the slot array changes (the other tier's growth). -/
theorem tierR_keep (hS : S.WF) (hfr : RFrame S R hs) (hkf : KFrame S hs KP) (m m' : Mem)
    (t : Word) (ht : t ≤ 1) (tb : Tbl α (Idx k) δ) (hT : TierR S R hs KP m t tb) (hG : GrowR S m)
    (harr : ∀ a, a ≠ S.sa → m'.arr64 a = m.arr64 a)
    (hsz : (m'.arr64 S.sa).size = (m.arr64 S.sa).size)
    (hmeta : rdW (m'.arr64 S.sa) (t * 2) = rdW (m.arr64 S.sa) (t * 2) ∧
      rdW (m'.arr64 S.sa) (t * 2 + 1) = rdW (m.arr64 S.sa) (t * 2 + 1))
    (hslots : ∀ j, j < nSl S m t →
      rdW (m'.arr64 S.sa) (krW S.sa m t + j * 2) = rdW (m.arr64 S.sa) (krW S.sa m t + j * 2) ∧
      rdW (m'.arr64 S.sa) (krW S.sa m t + j * 2 + 1) =
        rdW (m.arr64 S.sa) (krW S.sa m t + j * 2 + 1)) :
    TierR S R hs KP m' t tb := by
  obtain ⟨hc', hcap, hrs, hrec, hsome, hback, hsl, hkp, hrun⟩ := hT
  have hn : nSl S m' t = nSl S m t := by simp only [nSl, knW, hmeta.1]
  have hk : krW S.sa m' t = krW S.sa m t := by
    simp only [krW, koW, knW, Mem.len64, hmeta.1, hmeta.2, hsz]
  have hctl : m'.arr64 CTL = m.arr64 CTL := harr CTL hS.sa_ctl.symm
  have hbase : baseW m' t = baseW m t := by simp only [baseW, hctl]
  have hsw : ∀ j, j < nSl S m t → slotW S m' t j = slotW S m t j := fun j hj => by
    simp only [slotW, slotV, hk, hbase, (hslots j hj).1]
  have hsk : ∀ j, j < nSl S m t → slotK S m' t j = slotK S m t j := fun j hj => by
    simp only [slotK, hk, (hslots j hj).2]
  have hout : OutEq S m m' :=
    ⟨fun b _ hb _ => harr b hb, by rw [hctl]⟩
  have hfe : ∀ i f, f < S.w → fld S m' t i f = fld S m t i f := fun i f _ => by
    simp only [fld, harr S.ra hS.ra_sa]
  have hfr' := fun i => hfr m m' t i hout (hfe i)
  have hn0 : 0 < nSl S m t :=
    UInt64.lt_iff_toNat_lt.mpr (by have := (lay S m hG t ht).1; simp; omega)
  refine ⟨by simp only [cntW, hctl]; exact hc', hcap, by rw [harr S.ra hS.ra_sa]; exact hrs,
    fun i a h => (hfr' i).1 a (hrec i a h), hsome, hback, ?_, ?_, ?_⟩
  · intro j hj; rw [hn] at hj; rw [hsw j hj]; exact hsl j hj
  · intro j hj hne
    rw [hn] at hj; rw [hsw j hj] at hne ⊢; rw [hsk j hj]
    exact hkf m m' t _ (hfe _) (hfr' _).2 _ (hkp j hj hne)
  · intro i hi
    obtain ⟨d, h1, h2⟩ := hrun i hi
    refine ⟨d, ?_, fun e he => ?_⟩
    · simp only [hn, homeS, (hfr' i).2]
      rw [hsw _ (walkW_lt _ _ _ (homeW_lt _ _ hn0))]; exact h1
    · simp only [hn, homeS, (hfr' i).2]
      rw [hsw _ (walkW_lt _ _ _ (homeW_lt _ _ hn0))]; exact h2 e he

end keep

/-! ## The growth keeps the relation -/

theorem rdW_gm1W (sa : ArrId) (t : Word) (m : Mem) (x : Word) (ht : t ≤ 1)
    (hsz : 4 ≤ (m.arr64 sa).size) :
    rdW ((gm1W sa t m).arr64 sa) x =
      if t * 2 + 1 = x then gnbW sa t m
      else if t * 2 = x then knW sa m t * 2 - SN0 else rdW (m.arr64 sa) x := by
  obtain ⟨a1, a2⟩ := meta_toNat t ht
  simp only [gm1W, rdW_set64, size_set64, true_and]
  simp only [show (t * 2 + 1).toNat < (m.arr64 sa).size by omega,
    show (t * 2).toNat < (m.arr64 sa).size by omega, and_true]

theorem word_ne_of_toNat {x y : Word} (h : x.toNat ≠ y.toNat) : x ≠ y := fun e => h (by rw [e])

section grow
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)
  (KP : Mem → Word → Word → Word → Prop)

/-- **The growth keeps the relation**: if `G` of every key word a slot of tier `t` may hold is the
node's hash, the memory after `kgrowM` represents the same tables. -/
theorem storeR_kgrow (hS : S.WF) (hfr : RFrame S R hs) (hkf : KFrame S hs KP)
    (G : Mem → Word → Word) (m m' : Mem) (t : Word) (ht : t ≤ 1)
    (hGh : ∀ mi : Mem, (∀ a, a ≠ S.sa → mi.arr64 a = m.arr64 a) →
      ∀ i K, KP m t i K → G mi K = hs m t i)
    (on : Bool) (tbP tbS : Tbl α (Idx k) δ) (hR : StoreR S R hs KP m on tbP tbS)
    (h : kgrowM S.sa G t m = some m') : StoreR S R hs KP m' on tbP tbS := by
  obtain ⟨⟨hctl, hb⟩, hfl, hT0, hT1, hG⟩ := hR
  have hc : ¬ gchkW S.sa t m := fun hc => by
    simp only [kgrowM, gchkW, gQW, gnbW] at h hc
    simp [hc] at h
  rw [kgrowM_eq _ _ _ _ hc] at h
  obtain ⟨enb, e2, e4, eh, hob, hns4, hnsL, hns0, hns1, hdis, hlay0, hlay1, h8, h8m, hszL⟩ :=
    grow_nat S m t hG ht hc
  have hl := lay S m hG t ht
  have hL := sa_len64_toNat S m hG.1
  -- the memories
  generalize hm1 : gm1W S.sa t m = m1 at h
  generalize hm2 : kzeroW S.sa (gnbsW S.sa t m) (knW S.sa m t >>> 1).toNat m1 = m2 at h
  have fr1 : GFr S.sa m m1 := by
    rw [← hm1]; exact (GFr.set64 _ _ _ _).trans (GFr.set64 _ _ _ _)
  have fr2 : GFr S.sa m1 m2 := by rw [← hm2]; exact kzeroW_fr _ _ _ _
  have hL4 : 4 ≤ (m.arr64 S.sa).size := by omega
  have rd1 := fun x => (hm1 ▸ rdW_gm1W S.sa t m x ht hL4 :
    rdW (m1.arr64 S.sa) x = _)
  have rd2 : ∀ y, rdW (m2.arr64 S.sa) y =
      if (gnbsW S.sa t m).toNat ≤ y.toNat ∧ y.toNat < (gnbsW S.sa t m).toNat + 4 * (knW S.sa m t).toNat
      then 0 else rdW (m1.arr64 S.sa) y := by
    intro y; rw [← hm2, kzeroW_rd S.sa _ _ _ (by omega) y]; rw [Nat.mul_comm, eh]
  -- the tier and its numbers
  have hTt : TierR S R hs KP m t (if t = 0 then tbP else tbS) := by
    rcases le_one_cases t ht with rfl | rfl
    · simpa using hT0
    · simpa using hT1
  generalize htb : (if t = 0 then tbP else tbS) = tb at hTt
  have hsa1 : (m1.arr64 S.sa).size = (m.arr64 S.sa).size := fr1.2.1 S.sa
  have hsa2 : (m2.arr64 S.sa).size = (m.arr64 S.sa).size := (fr2.2.1 S.sa).trans hsa1
  have hN0 : (0 : Word) < knW S.sa m t * 2 := UInt64.lt_iff_toNat_lt.mpr (by rw [e2]; simp; omega)
  have hN : ∀ j : Word, j < knW S.sa m t * 2 → j.toNat < 2 * (knW S.sa m t).toNat := fun j hj => by
    have := UInt64.lt_iff_toNat_lt.mp hj; rw [e2] at this; exact this
  have nadr : ∀ j : Word, j < knW S.sa m t * 2 →
      (gnbsW S.sa t m + j * 2).toNat = (gnbsW S.sa t m).toNat + 2 * j.toNat ∧
      (gnbsW S.sa t m + j * 2 + 1).toNat = (gnbsW S.sa t m).toNat + 2 * j.toNat + 1 := by
    intro j hj
    have := hN j hj
    have e1 : (gnbsW S.sa t m + j * 2).toNat = (gnbsW S.sa t m).toNat + 2 * j.toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
    refine ⟨e1, ?_⟩; rw [UInt64.toNat_add, e1]; simp; omega
  have hnS : nSl S m t = knW S.sa m t := rfl
  have oadr : ∀ j : Word, j.toNat < (knW S.sa m t).toNat → j < nSl S m t := fun j hj =>
    UInt64.lt_iff_toNat_lt.mpr hj
  -- a word outside the new table reads as in `m2`, then as in `m1`
  have outN : ∀ y : Word, (y.toNat < (gnbsW S.sa t m).toNat ∨
      (gnbsW S.sa t m).toNat + 4 * (knW S.sa m t).toNat ≤ y.toNat) →
      ∀ j, j < knW S.sa m t * 2 → y ≠ gnbsW S.sa t m + j * 2 ∧ y ≠ gnbsW S.sa t m + j * 2 + 1 := by
    intro y hy j hj
    obtain ⟨a1, a2⟩ := nadr j hj
    have := hN j hj
    exact ⟨word_ne_of_toNat (by rw [a1]; omega), word_ne_of_toNat (by rw [a2]; omega)⟩
  have rd21 : ∀ y : Word, (y.toNat < (gnbsW S.sa t m).toNat ∨
      (gnbsW S.sa t m).toNat + 4 * (knW S.sa m t).toNat ≤ y.toNat) →
      rdW (m2.arr64 S.sa) y = rdW (m1.arr64 S.sa) y := by
    intro y hy; rw [rd2]; rw [if_neg (by omega)]
  have rd10 : ∀ y : Word, 4 ≤ y.toNat → rdW (m1.arr64 S.sa) y = rdW (m.arr64 S.sa) y := by
    intro y hy
    obtain ⟨a1, a2⟩ := meta_toNat t ht
    rw [rd1, if_neg (word_ne_of_toNat (by omega)), if_neg (word_ne_of_toNat (by omega))]
  -- the walk
  have hW := kwalkW_inv S.sa G (KP m t) (hs m t) (knW S.sa m t * 2) (gnbsW S.sa t m)
    (rdW (m.arr64 CTL) SCB * t) (cntW S m t) (gobsW S.sa t m) (knW S.sa m t).toNat m2
    (m.arr64 S.sa) hN0
    (fun j hj mi hmi => by
      rw [hob]
      obtain ⟨a1, a2⟩ := kslot_toNat S m hG t ht j (oadr j hj)
      have hr4 := hl.2.1
      have hd := hdis
      refine ⟨?_, ?_⟩
      · rw [hmi _ (outN _ (by rw [a1]; omega)), rd21 _ (by rw [a1]; omega), rd10 _ (by omega)]
      · rw [hmi _ (outN _ (by rw [a2]; omega)), rd21 _ (by rw [a2]; omega), rd10 _ (by omega)])
    (fun j j' hj hj' h' => by
      have := congrArg UInt64.toNat h'
      rw [(nadr j hj).2, (nadr j' hj').1] at this; omega)
    (fun j j' hj hj' h' => by
      have := congrArg UInt64.toNat h'
      rw [(nadr j hj).1, (nadr j' hj').1] at this
      exact UInt64.toNat_inj.mp (by omega))
    (fun j hj => by
      obtain ⟨a1, a2⟩ := nadr j hj
      have := hN j hj
      rw [hsa2, a1, a2]; omega)
    (fun j hj hv => by
      rw [hob] at hv ⊢
      have hj' := oadr j hj
      have hcnt := hTt.1
      obtain ⟨-, -, -, -, -, -, hsl, hkp, -⟩ := hTt
      have e : slotW S m t j =
          rdW (m.arr64 S.sa) (krW S.sa m t + j * 2) - rdW (m.arr64 CTL) SCB * t := by
        simp only [slotW, slotV, slotRd, baseW, UInt64.not_le.mpr hv, ↓reduceIte]
      have hne : slotW S m t j ≠ 0 := by
        rw [e]; intro h0
        have := UInt64.lt_iff_toNat_lt.mp hv
        have := congrArg UInt64.toNat h0
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hv)] at this; simp [baseW] at *; omega
      refine ⟨?_, ?_⟩
      · have := hsl j hj'
        rw [e, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hv)] at this
        rw [hcnt]; omega
      · have := hkp j hj' hne
        rw [e] at this
        exact this)
    (fun mi hmi i K hK => hGh mi (fun a ha => (hmi a ha).trans ((fr2.1 a ha).trans (fr1.1 a ha))) i K hK)
    (by have := knW_toNat S m hG t ht; omega)
    (knW S.sa m t).toNat 0 m2 m' (by simp)
    ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun j hj => .inl (by
        rw [rd2, if_pos]; obtain ⟨a1, -⟩ := nadr j hj; have := hN j hj; rw [a1]; omega),
      fun j hj => absurd hj (by simp)⟩
    (by rw [show gobsW S.sa t m + UInt64.ofNat 0 * 2 = gobsW S.sa t m by simp]; exact h)
  obtain ⟨w1, w2, w3, w4, w5⟩ := hW
  -- the memory after: outside the slot array, the tier's words, the other words
  have arr' : ∀ a, a ≠ S.sa → m'.arr64 a = m.arr64 a := fun a ha =>
    (w1 a ha).trans ((fr2.1 a ha).trans (fr1.1 a ha))
  have sz' : (m'.arr64 S.sa).size = (m.arr64 S.sa).size := w2.trans hsa2
  have ctl' : m'.arr64 CTL = m.arr64 CTL := arr' CTL hS.sa_ctl.symm
  have out' : ∀ y : Word, (y.toNat < (gnbsW S.sa t m).toNat ∨
      (gnbsW S.sa t m).toNat + 4 * (knW S.sa m t).toNat ≤ y.toNat) → 4 ≤ y.toNat →
      rdW (m'.arr64 S.sa) y = rdW (m.arr64 S.sa) y :=
    fun y h1 h2 => by rw [w3 y (outN y h1), rd21 y h1, rd10 y h2]
  obtain ⟨mt0, mt1⟩ := meta_toNat t ht
  have mtn : rdW (m'.arr64 S.sa) (t * 2) = knW S.sa m t * 2 - SN0 := by
    rw [w3 _ (outN _ (by omega)), rd21 _ (by omega), rd1, if_neg (word_ne_of_toNat (by
      rcases le_one_cases t ht with rfl | rfl <;> decide)), if_pos rfl]
  have mto : rdW (m'.arr64 S.sa) (t * 2 + 1) = gnbW S.sa t m := by
    rw [w3 _ (outN _ (by omega)), rd21 _ (by omega), rd1, if_pos rfl]
  have kn' : knW S.sa m' t = knW S.sa m t * 2 := by
    simp only [knW] at mtn ⊢; rw [mtn]; exact UInt64.sub_add_cancel _ _
  have ko' : koW S.sa m' t = gnbW S.sa t m := mto
  have kr' : krW S.sa m' t = gnbsW S.sa t m := by
    simp only [krW, ko', kn', Mem.len64, sz', gnbsW]
  have base' : baseW m' t = baseW m t := by simp only [baseW, ctl']
  have sw' : ∀ j, slotW S m' t j =
      slotRd (rdW (m'.arr64 S.sa) (gnbsW S.sa t m + j * 2)) (rdW (m.arr64 CTL) SCB * t) :=
    fun j => by simp only [slotW, slotV, kr', baseW, ctl']
  have sk' : ∀ j, slotK S m' t j = rdW (m'.arr64 S.sa) (gnbsW S.sa t m + j * 2 + 1) :=
    fun j => by simp only [slotK, kr']
  have hn' : nSl S m' t = knW S.sa m t * 2 := kn'
  have hout : OutEq S m m' := ⟨fun b _ hb _ => arr' b hb, by rw [ctl']⟩
  have hfe : ∀ t' i f, f < S.w → fld S m' t' i f = fld S m t' i f := fun t' i f _ => by
    simp only [fld, arr' S.ra hS.ra_sa]
  have hfr' := fun t' i => hfr m m' t' i hout (hfe t' i)
  -- the grown tier
  have newT : TierR S R hs KP m' t tb := by
    obtain ⟨hc', hcap, hrs, hrec, hsome, hback, hsl, hkp, hrun⟩ := hTt
    refine ⟨by simp only [cntW, ctl']; exact hc', hcap, by rw [arr' S.ra hS.ra_sa]; exact hrs,
      fun i a h => (hfr' t i).1 a (hrec i a h), hsome, hback, ?_, ?_, ?_⟩
    · intro j hj; rw [hn'] at hj; rw [sw' j]
      rcases w4 j hj with h0 | ⟨hv, hle, -⟩
      · rw [h0]; simp [slotRd]
      · simp only [slotRd, UInt64.not_le.mpr hv, ↓reduceIte]
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hv), ← hc']; omega
    · intro j hj hne; rw [hn'] at hj; rw [sw' j] at hne ⊢; rw [sk' j]
      rcases w4 j hj with h0 | ⟨hv, hle, hK⟩
      · rw [h0] at hne; simp [slotRd] at hne
      · simp only [slotRd, UInt64.not_le.mpr hv, ↓reduceIte]
        exact hkf m m' t _ (hfe t _) (hfr' t _).2 _ hK
    · intro i hi
      obtain ⟨d, hd1, hd2⟩ := hrun i hi
      have hn0 : 0 < nSl S m t := UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
      have hjo := walkW_lt (nSl S m t) (homeS S m t (hs m t i)) d (homeW_lt _ _ hn0)
      generalize walkW (nSl S m t) (homeS S m t (hs m t i)) d = jo at hd1 hjo
      have hi27 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      have hv : rdW (m.arr64 CTL) SCB * t < rdW (m.arr64 S.sa) (krW S.sa m t + jo * 2) := by
        simp only [slotW, slotV, slotRd, baseW] at hd1
        apply Classical.byContradiction; intro hle
        simp only [UInt64.not_lt.mp hle, ↓reduceIte] at hd1
        have := congrArg UInt64.toNat hd1; rw [hi27] at this; simp at this
      have hvi : rdW (m.arr64 S.sa) (krW S.sa m t + jo * 2) - rdW (m.arr64 CTL) SCB * t - 1 = i := by
        simp only [slotW, slotV, slotRd, baseW, UInt64.not_le.mpr hv, ↓reduceIte] at hd1
        rw [hd1]; simp
      have hF := w5 jo (UInt64.lt_iff_toNat_lt.mp hjo) (by rw [hob]; exact hv)
      rw [hob, hvi] at hF
      obtain ⟨D, hD1, hD2⟩ := hF
      have hN0' : 0 < knW S.sa m t * 2 := hN0
      refine ⟨D, ?_, fun e he => ?_⟩
      · simp only [homeS, hn', (hfr' t i).2]
        rw [sw', hD1]
        simpa only [slotW, slotV, baseW] using hd1
      · simp only [homeS, hn', (hfr' t i).2]
        rw [sw']
        have hwe := walkW_lt (knW S.sa m t * 2) (homeW (hs m t i) (knW S.sa m t * 2)) e
          (homeW_lt _ _ hN0')
        rcases w4 _ hwe with h0 | ⟨hv', -, -⟩
        · exact absurd h0 (hD2 e he)
        · simp only [slotRd, UInt64.not_le.mpr hv', ↓reduceIte]
          intro h0
          have := congrArg UInt64.toNat h0
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hv')] at this
          have := UInt64.lt_iff_toNat_lt.mp hv'
          simp at *; omega
  -- the other tier
  have othW : ∀ t', t' ≤ 1 → t' ≠ t →
      (rdW (m'.arr64 S.sa) (t' * 2) = rdW (m.arr64 S.sa) (t' * 2) ∧
        rdW (m'.arr64 S.sa) (t' * 2 + 1) = rdW (m.arr64 S.sa) (t' * 2 + 1)) ∧
      ∀ j, j < nSl S m t' →
        rdW (m'.arr64 S.sa) (krW S.sa m t' + j * 2) = rdW (m.arr64 S.sa) (krW S.sa m t' + j * 2) ∧
        rdW (m'.arr64 S.sa) (krW S.sa m t' + j * 2 + 1) =
          rdW (m.arr64 S.sa) (krW S.sa m t' + j * 2 + 1) := by
    intro t' ht' hne
    obtain ⟨b0, b1⟩ := meta_toNat t' ht'
    have hmt : (t' * 2).toNat ≠ (t * 2).toNat ∧ (t' * 2).toNat ≠ (t * 2 + 1).toNat ∧
        (t' * 2 + 1).toNat ≠ (t * 2).toNat ∧ (t' * 2 + 1).toNat ≠ (t * 2 + 1).toNat := by
      rcases le_one_cases t ht with rfl | rfl <;> rcases le_one_cases t' ht' with rfl | rfl <;>
        first | exact absurd rfl hne | decide
    refine ⟨⟨?_, ?_⟩, fun j hj => ?_⟩
    · rw [w3 _ (outN _ (by omega)), rd21 _ (by omega), rd1,
        if_neg (word_ne_of_toNat hmt.2.1).symm, if_neg (word_ne_of_toNat hmt.1).symm]
    · rw [w3 _ (outN _ (by omega)), rd21 _ (by omega), rd1,
        if_neg (word_ne_of_toNat hmt.2.2.2).symm, if_neg (word_ne_of_toNat hmt.2.2.1).symm]
    · obtain ⟨a1, a2⟩ := kslot_toNat S m hG t' ht' j hj
      have hl' := lay S m hG t' ht'
      have hjn := UInt64.lt_iff_toNat_lt.mp hj
      have hreg : (krW S.sa m t').toNat + 2 * (nSl S m t').toNat ≤ (gnbsW S.sa t m).toNat ∨
          (gnbsW S.sa t m).toNat + 4 * (knW S.sa m t).toNat ≤ (krW S.sa m t').toNat := by
        rcases le_one_cases t ht with rfl | rfl <;> rcases le_one_cases t' ht' with rfl | rfl
        · exact absurd rfl hne
        · have := (hns0 rfl).1; have := hl'.2.2.2.2 rfl; omega
        · have := (hns1 rfl).1; have := hl'.2.2.2.1 rfl; omega
        · exact absurd rfl hne
      constructor
      · exact out' _ (by rw [a1]; omega) (by rw [a1]; omega)
      · exact out' _ (by rw [a2]; omega) (by rw [a2]; omega)
  have othT : ∀ t', t' ≤ 1 → t' ≠ t → ∀ tb' : Tbl α (Idx k) δ, TierR S R hs KP m t' tb' →
      TierR S R hs KP m' t' tb' := fun t' ht' hne tb' hT' =>
    tierR_keep S R hs KP hS hfr hkf m m' t' ht' tb' hT' hG arr' sz' (othW t' ht' hne).1
      (othW t' ht' hne).2
  -- the layout
  have layT : TierLay S m' t := by
    have hk2 : (knW S.sa m' t).toNat = 2 * (knW S.sa m t).toNat := by rw [kn', e2]
    have ho2 : (koW S.sa m' t).toNat = if (koW S.sa m t).toNat = 0 then
        8 * (knW S.sa m t).toNat else 0 := by rw [ko', enb]
    refine ⟨by omega, by omega, ?_, fun h0 => ?_, fun h1 => ?_⟩
    · rw [ho2, hk2]; split <;> omega
    · rw [ho2, hk2, sz']; have := hlay0 h0; omega
    · rw [ho2, hk2, sz']; have := hlay1 h1; omega
  have layO : ∀ t', t' ≤ 1 → t' ≠ t → TierLay S m t' → TierLay S m' t' := by
    intro t' ht' hne hL'
    obtain ⟨⟨c1, c2⟩, -⟩ := othW t' ht' hne
    simpa only [TierLay, knW, koW, c1, c2, sz'] using hL'
  have hG' : (m'.arr64 S.sa).size < 2 ^ 62 := by rw [sz']; exact hszL
  refine ⟨⟨by rw [ctl']; exact hctl, by rw [ctl']; exact hb⟩, by rw [ctl']; exact hfl, ?_⟩
  rcases le_one_cases t ht with rfl | rfl
  · simp only [↓reduceIte] at htb; subst htb
    exact ⟨newT, othT 1 (by decide) (by decide) _ hT1, hG', layT,
      layO 1 (by decide) (by decide) hG.2.2⟩
  · simp only [show (1 : Word) ≠ 0 by decide, ↓reduceIte] at htb; subst htb
    exact ⟨othT 0 (by decide) (by decide) _ hT0, newT, hG', layO 0 (by decide) (by decide) hG.2.1,
      layT⟩


end grow

end L.Arena
