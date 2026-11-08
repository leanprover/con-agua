module

public import ConAgua.Arena.Env

@[expose] public section

/-!
# Readers and the words L reads

A record decoder reads a reader `R : Nat → Option Word`; L reads words by address. `RdOK R rd`
says that the word function `rd` is what L reads wherever `R` decodes a word (and that `R` decodes
nothing at or above `2^64`, so an address `q + c` does not wrap where `R` decodes at
`q.toNat + c.toNat`). The record pool's instance is `erRdOK`: `erecP` (both tiers) and L's tagged
read `EREC⦃a⦄` (`erRdT`); an array's is `RdOK.arr`: `aread b` and `rdW b`.
-/

open ConRon.Arena

namespace L.Arena

/-- `rd` is the word L reads wherever the reader `R` decodes one; `R` decodes below `2^64`. -/
structure RdOK (R : Nat → Option Word) (rd : Word → Word) : Prop where
  rd : ∀ a v, R a.toNat = some v → rd a = v
  lt : ∀ i v, R i = some v → i < 2 ^ 64

theorem RdOK.off {R : Nat → Option Word} {rd : Word → Word} (h : RdOK R rd)
    {q c : Word} {i : Nat} {w : Word} (hb : R i = some w) (hi : q.toNat + c.toNat = i) :
    rd (q + c) = w := by
  have hlt := h.lt _ _ hb
  have : (q + c).toNat = i := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
  exact h.rd _ _ (by rw [this]; exact hb)

/-- The same in `irRdW`'s argument order: the offset `c` read as the number `k`. -/
theorem RdOK.at {R : Nat → Option Word} {rd : Word → Word} (h : RdOK R rd) {q : Word} {w : Word}
    (c : Word) {k : Nat} (hc : c.toNat = k) (hb : R (q.toNat + k) = some w) : rd (q + c) = w :=
  h.off hb (by rw [hc])

/-- The same at a numeral offset `k`. -/
theorem RdOK.offN {R : Nat → Option Word} {rd : Word → Word} (h : RdOK R rd)
    {q : Word} {k : Nat} {w : Word} (hb : R (q.toNat + k) = some w) (hk : k < 2 ^ 64) :
    rd (q + UInt64.ofNat k) = w :=
  h.off hb (by simp; omega)

/-- An array and its plain read. -/
theorem RdOK.arr (b : Array Word) (hsz : b.size ≤ 2 ^ 64) : RdOK (aread b) (rdW b) where
  rd a v h := by simp only [aread_apply] at h; simp [rdW, h]
  lt i v h := by
    simp only [aread_apply] at h
    have := (Array.getElem?_eq_some_iff.mp h).1; omega

/-- **The tagged read `EREC⦃a⦄` L makes**, as a function of the address. -/
abbrev erRdT (m : Mem) (a : Word) : Word := rdW (m.arr64 (tierA EREC (a >>> 40))) (a &&& 0xFFFFFFFFFF)

theorem erRdT_of {m : Mem} (a v : Word) (h : erecP m a.toNat = some v) : erRdT m a = v := by
  obtain ⟨-, hget⟩ := erecP_tagRead h
  simp only [erRdT, rdW, hget, Option.getD_some]

/-- The record pool and L's tagged read. -/
theorem erRdOK (m : Mem) : RdOK (erecP m) (erRdT m) := ⟨erRdT_of, fun _ _ hv => erecP_lt64 hv⟩

/-- Two memories with the same record arrays (both tiers) read the same records. -/
theorem erRdT_congr {m m' : Mem} (h0 : m'.arr64 EREC = m.arr64 EREC)
    (h1 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC)) (x : Word) :
    rdW (m'.arr64 (tierA EREC (x >>> 40))) (x &&& 0xFFFFFFFFFF) = erRdT m x := by
  simp only [erRdT, tierA]; cases ((x >>> 40) &&& 1 != 0)
  · exact congrArg (rdW · _) h0
  · exact congrArg (rdW · _) h1

/-- A decoded slice has the slice's length. -/
theorem hslice?_lenR {k : IdxKind} {R : Nat → Option Word} {o c : Nat} {l : List (Idx k)}
    (h : hslice? R o c = some l) : l.length = c := by
  unfold hslice? at h
  have key : ∀ (xs : List Nat) (r : List (Idx k)), xs.mapM (fun j => hd? R (o + j)) = some r →
      r.length = xs.length := by
    intro xs
    induction xs with
    | nil => intro r h; simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
    | cons x xs ih =>
      intro r h
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨y, -, ys, hys, rfl⟩ := h
      simp [ih ys hys]
  simpa using key _ _ h

theorem decCV_words {a : Nat → Option Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    (∃ w, a q = some w ∧ w.toNat < 2 ^ 32 ∧ cv.name = decI w) ∧
    (∃ w, a (q + 2) = some w ∧ cv.levelParams.length = w.toNat) ∧
    (∃ w, a (q + 3) = some w ∧ w.toNat < 2 ^ 32 ∧ cv.type = decI w) := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨n, hn, l, hl, t, ht, hc⟩ := h
  cases Option.some.inj hc
  refine ⟨hd?_some hn, ?_, hd?_some ht⟩
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
  obtain ⟨o, ho, c, hc', hs⟩ := hl
  simp only [nat?, Option.map_eq_some_iff] at hc'
  obtain ⟨w, hw, rfl⟩ := hc'
  exact ⟨w, hw, by simpa using hslice?_lenR hs⟩

/-- Shape of a record whose `decCV` succeeds at `q + 1`, read at the words `q + 2`, `q + 3`, `q + 4`. -/
theorem decCV_rd {R : Nat → Option Word} {rd : Word → Word}
    (hR : RdOK R rd)
    {q : Word} {cv : IConstantVal} (h : decCV R (q.toNat + 1) = some cv) :
    hslice? R (rd (q + 2)).toNat (rd (q + 3)).toNat = some cv.levelParams ∧
    cv.levelParams.length = (rd (q + 3)).toNat ∧
    cv.type = decI (rd (q + 4)) ∧ (rd (q + 4)).toNat < 2 ^ 32 := by
  obtain ⟨-, ⟨w3, hw3, hlen⟩, ⟨w4, hw4, hl4, hty⟩⟩ := decCV_words h
  have e3 : rd (q + 3) = w3 := hR.off hw3 (by simp <;> omega)
  have e4 : rd (q + 4) = w4 := hR.off hw4 (by simp <;> omega)
  refine ⟨?_, by rw [e3]; exact hlen, by rw [e4]; exact hty, by rw [e4]; exact hl4⟩
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨n, hn, l, hl, t, ht, hc⟩ := h
  cases Option.some.inj hc
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
  obtain ⟨o, ho, c, hc', hs⟩ := hl
  simp only [nat?, Option.map_eq_some_iff] at ho hc'
  obtain ⟨w2, hw2, rfl⟩ := ho
  obtain ⟨w3', hw3', rfl⟩ := hc'
  have e2 : rd (q + 2) = w2 := hR.off hw2 (by simp <;> omega)
  have e3' : w3' = w3 := by
    have := hw3'.symm.trans hw3; exact Option.some.inj this
  subst e3'
  rw [e2, e3]
  exact hs

/-- The kind word of a decoded record, and what each kind decodes to. -/
theorem decCI_split {R : Nat → Option Word} {rd : Word → Word} {q : Word}
    (hR : RdOK R rd)
    {ci : IConstantInfo} (h : decCI R q.toNat = some ci) :
    (rd q = 1 → ∃ cv v hint, ci = .defnInfo cv v hint ∧ decCV R (q.toNat + 1) = some cv ∧
      v = decI (rd (q + 5)) ∧ (rd (q + 5)).toNat < 2 ^ 32) ∧
    (rd q ≠ 1 → ∀ cv v hint, ci ≠ .defnInfo cv v hint) ∧
    (rd q = 3 → ∃ cv caps, ci = .indInfo cv caps ∧ decCV R (q.toNat + 1) = some cv) ∧
    (rd q ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) ∧
    (rd q = 4 → ∃ cv np nf, ci = .ctorInfo cv np nf ∧ decCV R (q.toNat + 1) = some cv) ∧
    (rd q ≠ 4 → ∀ cv np nf, ci ≠ .ctorInfo cv np nf) := by
  cases hq : R q.toNat with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  have hrdq : rd q = w := hR.rd _ _ hq
  rw [hrdq]
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  by_cases w1 : w.toNat = 1
  · have wv : w = 1 := UInt64.toNat_inj.mp (by rw [w1]; rfl)
    subst wv
    simp only [show UInt64.toNat 1 = 1 from rfl, Option.bind_eq_some_iff] at h
    obtain ⟨cv, hcv, v, hv, hint, -, hc⟩ := h
    cases hc
    obtain ⟨vw, hvw, hvl, rfl⟩ := hd?_some hv
    have hlt := hR.lt _ _ hvw
    have e5n : (q + 5).toNat = q.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
    have e5 : rd (q + 5) = vw := hR.rd _ _ (by rw [e5n]; exact hvw)
    refine ⟨fun _ => ⟨cv, _, _, rfl, hcv, by rw [e5], by rw [e5]; exact hvl⟩, fun hn => absurd rfl hn,
      fun h3 => absurd h3 (by decide), fun _ _ _ => by simp, fun h4 => absurd h4 (by decide),
      fun _ _ _ _ => by simp⟩
  by_cases w3 : w.toNat = 3
  · have wv : w = 3 := UInt64.toNat_inj.mp (by rw [w3]; rfl)
    subst wv
    simp only [show UInt64.toNat 3 = 3 from rfl, Option.bind_eq_some_iff] at h
    obtain ⟨cv, hcv, caps, -, hc⟩ := h
    cases hc
    refine ⟨fun h1 => absurd h1 (by decide), fun _ _ _ _ => by simp, fun _ => ⟨cv, _, rfl, hcv⟩,
      fun hn => absurd rfl hn, fun h4 => absurd h4 (by decide), fun _ _ _ _ => by simp⟩
  by_cases w4 : w.toNat = 4
  · have wv : w = 4 := UInt64.toNat_inj.mp (by rw [w4]; rfl)
    subst wv
    simp only [show UInt64.toNat 4 = 4 from rfl, Option.bind_eq_some_iff] at h
    obtain ⟨cv, hcv, np, -, nf, -, hc⟩ := h
    cases hc
    refine ⟨fun h1 => absurd h1 (by decide), fun _ _ _ _ => by simp, fun h3 => absurd h3 (by decide),
      fun _ _ _ => by simp, fun _ => ⟨cv, _, _, rfl, hcv⟩, fun hn => absurd rfl hn⟩
  have n1 : w ≠ 1 := fun e => w1 (by rw [e]; rfl)
  have n3 : w ≠ 3 := fun e => w3 (by rw [e]; rfl)
  have n4 : w ≠ 4 := fun e => w4 (by rw [e]; rfl)
  refine ⟨fun e => absurd e n1, ?_, fun e => absurd e n3, ?_, fun e => absurd e n4, ?_⟩
  · intro _ cv v hint hc; subst hc
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h w1 w3 w4; simp [Option.bind_eq_some_iff] at h w1 w3 w4)
  · intro _ cv v hc; subst hc
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h w1 w3 w4; simp [Option.bind_eq_some_iff] at h w1 w3 w4)
  · intro _ cv v n hc; subst hc
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h w1 w3 w4; simp [Option.bind_eq_some_iff] at h w1 w3 w4)

/-- `decCI_split` at the record pool and L's tagged read. -/
theorem decCI_splitE {m : Mem} {q : Word} {ci : IConstantInfo} (h : decCI (erecP m) q.toNat = some ci) :
    (erRdT m q = 1 → ∃ cv v hint, ci = .defnInfo cv v hint ∧ decCV (erecP m) (q.toNat + 1) = some cv ∧
      v = decI (erRdT m (q + 5)) ∧ (erRdT m (q + 5)).toNat < 2 ^ 32) ∧
    (erRdT m q ≠ 1 → ∀ cv v hint, ci ≠ .defnInfo cv v hint) ∧
    (erRdT m q = 3 → ∃ cv caps, ci = .indInfo cv caps ∧ decCV (erecP m) (q.toNat + 1) = some cv) ∧
    (erRdT m q ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) ∧
    (erRdT m q = 4 → ∃ cv np nf, ci = .ctorInfo cv np nf ∧ decCV (erecP m) (q.toNat + 1) = some cv) ∧
    (erRdT m q ≠ 4 → ∀ cv np nf, ci ≠ .ctorInfo cv np nf) :=
  decCI_split (erRdOK m) h


end L.Arena
