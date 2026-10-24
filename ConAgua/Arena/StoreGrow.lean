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

/-- **The growth's numbers**: with `n` slots at offset `o` in tier `t`'s slot array (`L` words)
and the room check passed, the new table (`2 n` slots from `nb + 2`) lies in the array, apart
from the old one (`n` slots from `os`), and its offset `nb` is `8 n` or `0`. -/
theorem grow_nat (hG : GrowR S m) (ht : t ≤ 1) (hc : ¬ gchkW S.sa t m) :
    let L := (m.arr64 (tierA S.sa t)).size
    let n := (knW S.sa m t).toNat
    let o := (koW S.sa m t).toNat
    let nb := if o = 0 then 8 * n else 0
    (gnbW S.sa t m).toNat = nb ∧ (knW S.sa m t * 2).toNat = 2 * n ∧
    (knW S.sa m t * 2 * 2).toNat = 4 * n ∧ (knW S.sa m t >>> 1).toNat * 8 = 4 * n ∧
    (gobsW S.sa t m) = krW S.sa m t ∧
    (gnbsW S.sa t m).toNat = nb + 2 ∧ (gnbsW S.sa t m).toNat + 4 * n ≤ L ∧
    ((gnbsW S.sa t m).toNat + 4 * n ≤ (krW S.sa m t).toNat ∨
      (krW S.sa m t).toNat + 2 * n ≤ (gnbsW S.sa t m).toNat) ∧
    8 ≤ n ∧ n % 8 = 0 ∧ L < 2 ^ 61 := by
  intro L n o nb
  obtain ⟨hs, a1, a2, a3, a4⟩ := hG.tier S m t ht
  have hn : n < 2 ^ 60 := by omega
  have e2 : (knW S.sa m t * 2).toNat = 2 * n := by rw [UInt64.toNat_mul]; simp; omega
  have e4 : (knW S.sa m t * 2 * 2).toNat = 4 * n := by rw [UInt64.toNat_mul, e2]; simp; omega
  have eh : (knW S.sa m t >>> 1).toNat * 8 = 4 * n := by
    rw [UInt64.toNat_shiftRight]; simp; omega
  have hL : (m.len64 (tierA S.sa t)).toNat = L := by
    simp only [Mem.len64]; rw [UInt64.toNat_ofNat_of_lt']; simp only [UInt64.size]; omega
  have eQ : (gQW S.sa t m).toNat = L - 2 := by
    simp only [gQW]
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hL]; simp; omega), hL]; simp
  have hcn : nb + 4 * n ≤ L - 2 := by
    simp only [gchkW, gnbW, UInt64.not_lt] at hc
    rw [UInt64.le_iff_toNat_le, eQ] at hc
    by_cases ho : koW S.sa m t = 0
    · have ho' : o = 0 := by simp [o, ho]
      simp only [ho, ↓reduceIte] at hc
      rw [UInt64.toNat_add, UInt64.toNat_mul, e2, e4] at hc
      simp only [nb, ho', ↓reduceIte]
      simp only [UInt64.toNat_ofNat, show (4 : Word).toNat = 4 from rfl] at hc
      rw [show 2 * n * 4 % 18446744073709551616 = 8 * n by omega] at hc
      omega
    · have ho' : o ≠ 0 := fun h => ho (UInt64.toNat_inj.mp (by simpa [o] using h))
      simp only [ho, ↓reduceIte] at hc
      rw [UInt64.toNat_add, e4] at hc
      simp only [nb, ho', ↓reduceIte]
      simp at hc; omega
  have enb : (gnbW S.sa t m).toNat = nb := by
    simp only [gnbW]
    by_cases ho : koW S.sa m t = 0
    · have ho' : o = 0 := by simp [o, ho]
      simp only [ho, ↓reduceIte, nb, ho']
      rw [UInt64.toNat_mul, e2]; simp; omega
    · have ho' : o ≠ 0 := fun h => ho (UInt64.toNat_inj.mp (by simpa [o] using h))
      simp only [ho, ↓reduceIte, nb, ho']; rfl
  have hob : gobsW S.sa t m = krW S.sa m t := rfl
  have hnbo : (o = 0 → nb = 8 * n) ∧ (o ≠ 0 → nb = 0) := by
    simp only [nb]; constructor <;> intro h <;> simp [h]
  have ens : (gnbsW S.sa t m).toNat = nb + 2 := by
    simp only [gnbsW]; rw [UInt64.toNat_add, enb]; simp; omega
  have ekr : (krW S.sa m t).toNat = o + 2 := by
    simp only [krW]; rw [UInt64.toNat_add]; simp; omega
  refine ⟨enb, e2, e4, eh, hob, ens, by omega, ?_, a1, a2, hs⟩
  rw [ens, ekr]
  rcases a3 with a3 | a3
  · have := hnbo.1 a3; omega
  · by_cases ho : o = 0
    · have := hnbo.1 ho; omega
    · have := hnbo.2 ho; omega

end nat

/-! ## The growth keeps the relation -/

theorem rdW_gm1W (sa : ArrId) (t : Word) (m : Mem) (x : Word)
    (hsz : 2 ≤ (m.arr64 (tierA sa t)).size) :
    rdW ((gm1W sa t m).arr64 (tierA sa t)) x =
      if 1 = x then gnbW sa t m
      else if 0 = x then knW sa m t * 2 - SN0 else rdW (m.arr64 (tierA sa t)) x := by
  have h1 : (1 : Word).toNat < (m.arr64 (tierA sa t)).size := by simp; omega
  have h0 : (0 : Word).toNat < (m.arr64 (tierA sa t)).size := by simp; omega
  simp only [gm1W, rdW_set64, size_set64, true_and, h1, h0, and_true]

theorem word_ne_of_toNat {x y : Word} (h : x.toNat ≠ y.toNat) : x ≠ y := fun e => h (by rw [e])

section grow
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)
  (KP : Mem → Word → Word → Word → Prop)

/-- **The growth keeps the relation**: if `G` of every key word a slot of tier `t` may hold is the
node's hash, the memory after `kgrowM` represents the same tables. -/
theorem storeR_kgrow (hS : S.WF) (hfr : RFrame S R hs) (hkf : KFrame S hs KP)
    (G : Mem → Word → Word) (m m' : Mem) (t : Word) (ht : t ≤ 1)
    (hGh : ∀ mi : Mem, (∀ a, a ≠ tierA S.sa t → mi.arr64 a = m.arr64 a) →
      ∀ i K, KP m t i K → G mi K = hs m t i)
    (on : Bool) (tbP tbS : Tbl α (Idx k) δ) (hR : StoreR S R hs KP m on tbP tbS)
    (h : kgrowM S.sa G t m = some m') : StoreR S R hs KP m' on tbP tbS := by
  obtain ⟨⟨hctl, hb⟩, hfl, hT0, hT1, hG⟩ := hR
  have hc : ¬ gchkW S.sa t m := fun hc => by
    simp only [kgrowM, gchkW, gQW, gnbW] at h hc
    simp [hc] at h
  rw [kgrowM_eq _ _ _ _ hc] at h
  obtain ⟨enb, e2, e4, eh, hob, hns, hnsL, hdis, h8, h8m, hszL⟩ := grow_nat S m t hG ht hc
  have hl := lay S m hG t ht
  -- the memories
  generalize hm1 : gm1W S.sa t m = m1 at h
  generalize hm2 : kzeroW (tierA S.sa t) (gnbsW S.sa t m) (knW S.sa m t >>> 1).toNat m1 = m2 at h
  have fr1 : GFr (tierA S.sa t) m m1 := by
    rw [← hm1]; exact (GFr.set64 _ _ _ _).trans (GFr.set64 _ _ _ _)
  have fr2 : GFr (tierA S.sa t) m1 m2 := by rw [← hm2]; exact kzeroW_fr _ _ _ _
  have hL2 : 2 ≤ (m.arr64 (tierA S.sa t)).size := by omega
  have rd1 := fun x => (hm1 ▸ rdW_gm1W S.sa t m x hL2 :
    rdW (m1.arr64 (tierA S.sa t)) x = _)
  have rd2 : ∀ y, rdW (m2.arr64 (tierA S.sa t)) y =
      if (gnbsW S.sa t m).toNat ≤ y.toNat ∧ y.toNat < (gnbsW S.sa t m).toNat + 4 * (knW S.sa m t).toNat
      then 0 else rdW (m1.arr64 (tierA S.sa t)) y := by
    intro y; rw [← hm2, kzeroW_rd _ _ _ _ (by omega) y]; rw [Nat.mul_comm, eh]
  -- the tier and its numbers
  have hTt : TierR S R hs KP m t (if t = 0 then tbP else tbS) := by
    rcases le_one_cases t ht with rfl | rfl
    · simpa using hT0
    · simpa using hT1
  generalize htb : (if t = 0 then tbP else tbS) = tb at hTt
  have hsa1 : (m1.arr64 (tierA S.sa t)).size = (m.arr64 (tierA S.sa t)).size := fr1.2.1 _
  have hsa2 : (m2.arr64 (tierA S.sa t)).size = (m.arr64 (tierA S.sa t)).size := (fr2.2.1 _).trans hsa1
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
      rdW (m2.arr64 (tierA S.sa t)) y = rdW (m1.arr64 (tierA S.sa t)) y := by
    intro y hy; rw [rd2]; rw [if_neg (by omega)]
  have rd10 : ∀ y : Word, 2 ≤ y.toNat →
      rdW (m1.arr64 (tierA S.sa t)) y = rdW (m.arr64 (tierA S.sa t)) y := by
    intro y hy
    rw [rd1, if_neg (word_ne_of_toNat (by simp; omega)), if_neg (word_ne_of_toNat (by simp; omega))]
  -- the walk
  have hW := kwalkW_inv (tierA S.sa t) G (KP m t) (hs m t) (knW S.sa m t * 2) (gnbsW S.sa t m)
    (rdW (m.arr64 CTL) SCB * t) (cntW S m t) (gobsW S.sa t m) (knW S.sa m t).toNat m2
    (m.arr64 (tierA S.sa t)) hN0
    (fun j hj mi hmi => by
      rw [hob]
      obtain ⟨a1, a2⟩ := kslot_toNat S m hG t ht j (oadr j hj)
      have hr2 := hl.2.1
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
          rdW (m.arr64 (tierA S.sa t)) (krW S.sa m t + j * 2) - rdW (m.arr64 CTL) SCB * t := by
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
  -- the memory after: outside tier `t`'s slot array, its words
  have arr' : ∀ a, a ≠ tierA S.sa t → m'.arr64 a = m.arr64 a := fun a ha =>
    (w1 a ha).trans ((fr2.1 a ha).trans (fr1.1 a ha))
  have sz' : (m'.arr64 (tierA S.sa t)).size = (m.arr64 (tierA S.sa t)).size := w2.trans hsa2
  have ctl' : m'.arr64 CTL = m.arr64 CTL := arr' CTL (hS.sa_ctl' t).symm
  have h0 : (0 : Word).toNat < (gnbsW S.sa t m).toNat := by simp; omega
  have h1 : (1 : Word).toNat < (gnbsW S.sa t m).toNat := by simp; omega
  have mtn : rdW (m'.arr64 (tierA S.sa t)) 0 = knW S.sa m t * 2 - SN0 := by
    rw [w3 _ (outN _ (.inl h0)), rd21 _ (.inl h0), rd1, if_neg (by decide), if_pos rfl]
  have mto : rdW (m'.arr64 (tierA S.sa t)) 1 = gnbW S.sa t m := by
    rw [w3 _ (outN _ (.inl h1)), rd21 _ (.inl h1), rd1, if_pos rfl]
  have kn' : knW S.sa m' t = knW S.sa m t * 2 := by
    simp only [knW] at mtn ⊢; rw [mtn]; exact UInt64.sub_add_cancel _ _
  have ko' : koW S.sa m' t = gnbW S.sa t m := mto
  have kr' : krW S.sa m' t = gnbsW S.sa t m := by simp only [krW, ko', gnbsW]
  have sw' : ∀ j, slotW S m' t j =
      slotRd (rdW (m'.arr64 (tierA S.sa t)) (gnbsW S.sa t m + j * 2)) (rdW (m.arr64 CTL) SCB * t) :=
    fun j => by simp only [slotW, slotV, kr', baseW, ctl']
  have sk' : ∀ j, slotK S m' t j = rdW (m'.arr64 (tierA S.sa t)) (gnbsW S.sa t m + j * 2 + 1) :=
    fun j => by simp only [slotK, kr']
  have hn' : nSl S m' t = knW S.sa m t * 2 := kn'
  have hsat : ∀ b, b ≠ S.sa → b ≠ S.sa + 256 → b ≠ tierA S.sa t := fun b h1 h2 e => by
    rcases tierA_cases' S.sa t with e' | e' <;> rw [e'] at e <;> contradiction
  have hout : OutEq S m m' := ⟨fun b _ _ hb hb' _ => arr' b (hsat b hb hb'), by rw [ctl']⟩
  have hfe : ∀ t' i f, f < S.w → fld S m' t' i f = fld S m t' i f := fun t' i f _ => by
    simp only [fld, arr' _ (hS.ra_sa' t' t)]
  have hfr' := fun t' i => hfr m m' t' i hout (hfe t' i)
  -- the grown tier
  have newT : TierR S R hs KP m' t tb := by
    obtain ⟨hc', hcap, hrs, hrec, hsome, hback, hsl, hkp, hrun⟩ := hTt
    refine ⟨by simp only [cntW, ctl']; exact hc', hcap, by rw [arr' _ (hS.ra_sa' t t)]; exact hrs,
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
      have hn0 : 0 < nSl S m t := UInt64.lt_iff_toNat_lt.mpr (by simp [nSl]; omega)
      have hjo := walkW_lt (nSl S m t) (homeS S m t (hs m t i)) d (homeW_lt _ _ hn0)
      generalize walkW (nSl S m t) (homeS S m t (hs m t i)) d = jo at hd1 hjo
      have hi27 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      have hv : rdW (m.arr64 CTL) SCB * t < rdW (m.arr64 (tierA S.sa t)) (krW S.sa m t + jo * 2) := by
        simp only [slotW, slotV, slotRd, baseW] at hd1
        apply Classical.byContradiction; intro hle
        simp only [UInt64.not_lt.mp hle, ↓reduceIte] at hd1
        have := congrArg UInt64.toNat hd1; rw [hi27] at this; simp at this
      have hvi : rdW (m.arr64 (tierA S.sa t)) (krW S.sa m t + jo * 2) - rdW (m.arr64 CTL) SCB * t - 1 = i := by
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
  -- the other tier: its arrays are untouched
  have othT : ∀ t', t' ≤ 1 → t' ≠ t → ∀ tb' : Tbl α (Idx k) δ, TierR S R hs KP m t' tb' →
      TierR S R hs KP m' t' tb' := fun t' ht' hne tb' hT' =>
    tierR_mono S R hs KP m m' t' tb' (arr' _ (hS.ra_sa' t' t))
      (arr' _ (tierA_ne_tier _ ht' ht hne)) (by simp only [cntW, ctl'])
      (by simp only [baseW, ctl']) (fun i a h => (hfr' t' i).1 a h) (fun i => (hfr' t' i).2)
      (fun i K h => hkf m m' t' i (hfe t' i) (hfr' t' i).2 K h) hT'
  -- the layout
  have layT : TierLay S m' t := by
    have hk2 : (knW S.sa m' t).toNat = 2 * (knW S.sa m t).toNat := by rw [kn', e2]
    have ho2 : (koW S.sa m' t).toNat = if (koW S.sa m t).toNat = 0 then
        8 * (knW S.sa m t).toNat else 0 := by rw [ko', enb]
    refine ⟨by rw [sz']; exact hszL, by omega, by omega, ?_, ?_⟩
    · rw [ho2, hk2]; split <;> omega
    · rw [ko', hk2, sz']; have := hns; have := enb; omega
  have layO : ∀ t', t' ≤ 1 → t' ≠ t → TierLay S m t' → TierLay S m' t' := by
    intro t' ht' hne hL'
    simpa only [TierLay, knW, koW, arr' _ (tierA_ne_tier _ ht' ht hne)] using hL'
  refine ⟨⟨by rw [ctl']; exact hctl, by rw [ctl']; exact hb⟩, by rw [ctl']; exact hfl, ?_⟩
  rcases le_one_cases t ht with rfl | rfl
  · simp only [↓reduceIte] at htb; subst htb
    exact ⟨newT, othT 1 (by decide) (by decide) _ hT1, layT, layO 1 (by decide) (by decide) hG.2⟩
  · simp only [show (1 : Word) ≠ 0 by decide, ↓reduceIte] at htb; subst htb
    exact ⟨othT 0 (by decide) (by decide) _ hT0, newT, layO 0 (by decide) (by decide) hG.1, layT⟩

end grow

end L.Arena
