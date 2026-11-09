module

public import ConAgua.Arena.QuotCiT
import ConAgua.Arena.RecFireCore
import ConAgua.Arena.TwinStep
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Canon

@[expose] public section

/-!
# A recursor's rules at new names: `rules_at_lps_go` (lane `ronsync2`, stage 3)

`rules_at_lps_go(ko, kc, us, o, rl, d)` refines `rulesAtLps` (`rulesGo_sim`): per rule the
right-hand side by `inst_lp` (`instStep`), a `.levels` fire by `fire_levels_at` (`fireStep`:
`ls_node`, `keys_push`, `sle_go` under `CoreS`, a fresh slice by `erec_alloc`/`spn_to_er`), then
the 11 record words written (`j1_inv`: one `wrER` into the region above the base, `wrER_fresh`).
With the twin's two name readbacks in front (`StageT.readNC`) it discharges `RulesAtSim`
(`rulesAtSim_of`), hence `QuotSims` (`quotSims_of''`).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-! ## Decoding -/

/-- The words of a level list decode back to it. -/
theorem hslice_of_lsWords {R : Nat → Option Word} :
    ∀ (hs : List LIdx) (o : Nat), (∀ j < hs.length, R (o + j) = (lsWords hs)[j]?) →
      hslice? R o hs.length = some hs
  | [], o, _ => by simp [hslice?]
  | u :: us, o, h => by
    rw [List.length_cons, hslice?_succ]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, lsWords, List.map_cons, List.getElem?_cons_zero] at h0
    have ht := hslice_of_lsWords us (o + 1) fun j hj => by
      have := h (j + 1) (by simp; omega)
      simpa [lsWords, Nat.add_assoc, Nat.add_comm 1 j] using this
    have hw : (u.word.toUInt64).toNat < 2 ^ 32 := by simp; exact u.word.toNat_lt
    simp only [hd?, h0, Option.bind_eq_bind, Option.bind_some, hw, ↓reduceIte, decI_word, ht,
      Option.pure_def]

/-- A rule's fire at new names: a `.levels` fire's slice replaced. -/
def fireAt : IRecRuleFire → List LIdx → IRecRuleFire
  | .levels _, hs => .levels hs
  | f, _ => f

theorem decRule_fields' {R : Nat → Option Word} {q : Nat} {rl : IRecRule} (h : decRule R q = some rl) :
    hd? R q = some rl.ctor ∧ nat? R (q + 1) = some rl.nfields ∧ hd? R (q + 8) = some rl.rhs := by
  unfold decRule at h
  cases h3 : nat? R (q + 3) with
  | none => simp [h3] at h
  | some t =>
    simp only [h3, Option.bind_eq_bind, Option.bind_some] at h
    match t, h with
    | 0, h =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨c, hc, nf, hnf, r, hr, rfl⟩ := h; exact ⟨hc, hnf, hr⟩
    | 1, h =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨_, -, _, -, c, hc, nf, hnf, r, hr, rfl⟩ := h; exact ⟨hc, hnf, hr⟩
    | 2, h =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨_, -, c, hc, nf, hnf, r, hr, rfl⟩ := h; exact ⟨hc, hnf, hr⟩
    | _ + 3, h => simp at h

/-- The words a decoded rule reads are there. -/
theorem decRule_defs {R : Nat → Option Word} {q : Nat} {rl : IRecRule} (h : decRule R q = some rl) :
    (∃ w, R q = some w) ∧ (∃ w, R (q + 1) = some w) ∧ (∃ w, R (q + 3) = some w) ∧
      (∃ w, R (q + 8) = some w) ∧
      (∀ lv, rl.fire = .levels lv → (∃ w, R (q + 4) = some w) ∧ (∃ w, R (q + 5) = some w)) ∧
      (∀ lv pins, rl.fire = .nested lv pins → (∃ w, R (q + 4) = some w) ∧
        (∃ w, R (q + 5) = some w) ∧ (∃ w, R (q + 6) = some w) ∧ (∃ w, R (q + 7) = some w)) := by
  have def_of_nat : ∀ i x, nat? R i = some x → ∃ w, R i = some w := fun i x hx => by
    simp only [nat?, Option.map_eq_some_iff] at hx; obtain ⟨w, hw, -⟩ := hx; exact ⟨w, hw⟩
  have def_of_hd : ∀ {k : IdxKind} i (x : Idx k), hd? R i = some x → ∃ w, R i = some w := fun i x hx => by
    simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx; obtain ⟨w, hw, -⟩ := hx; exact ⟨w, hw⟩
  have def_of_hl : ∀ {k : IdxKind} i (xs : List (Idx k)), hlist? R i = some xs →
      (∃ w, R i = some w) ∧ ∃ w, R (i + 1) = some w := fun i xs hx => by
    simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
    obtain ⟨o, ho, c, hc, -⟩ := hx; exact ⟨def_of_nat _ _ ho, def_of_nat _ _ hc⟩
  obtain ⟨hc, hn, hr⟩ := decRule_fields' h
  refine ⟨def_of_hd _ _ hc, def_of_nat _ _ hn, ?_, def_of_hd _ _ hr, ?_, ?_⟩
  · unfold decRule at h
    cases h3 : nat? R (q + 3) with
    | none => simp [h3] at h
    | some t => exact def_of_nat _ _ h3
  · intro lv hf
    unfold decRule at h
    cases h3 : nat? R (q + 3) with
    | none => simp [h3] at h
    | some t =>
    simp only [h3, Option.bind_eq_bind, Option.bind_some] at h
    match t, h with
    | 0, h =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨_, -, _, -, _, -, rfl⟩ := h; cases hf
    | 1, h =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨_, -, _, -, _, -, _, -, _, -, rfl⟩ := h; cases hf
    | 2, h =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨y, hy, -⟩ := h
      exact def_of_hl _ _ hy
    | _ + 3, h => simp at h
  · intro lv pins hf
    unfold decRule at h
    cases h3 : nat? R (q + 3) with
    | none => simp [h3] at h
    | some t =>
    simp only [h3, Option.bind_eq_bind, Option.bind_some] at h
    match t, h with
    | 0, h =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨_, -, _, -, _, -, rfl⟩ := h; cases hf
    | 1, h =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨y, hy, z, hz, -⟩ := h
      obtain ⟨h4, h5⟩ := def_of_hl _ _ hy
      obtain ⟨h6, h7⟩ := def_of_hl _ _ hz
      exact ⟨h4, by simpa [Nat.add_assoc] using h5, h6, by simpa [Nat.add_assoc] using h7⟩
    | 2, h =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨_, -, _, -, _, -, _, -, rfl⟩ := h; cases hf
    | _ + 3, h => simp at h

/-- **A rule record at new names**: the plain words copied, the right-hand side `x`, a `.levels`
fire's slice the fresh `(lo, ·)`; every other fire's words copied. -/
theorem decRule_atLps {R R' : Nat → Option Word} {q q' : Nat} {rl : IRecRule} {x lo : Word}
    {hs : List LIdx} (h : decRule R q = some rl) (hext : ArrExt R R')
    (hw : ∀ j, (j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 7) → ∀ v, R (q + j) = some v →
      R' (q' + j) = some v)
    (h4 : (∀ lv, rl.fire ≠ .levels lv) → ∀ v, R (q + 4) = some v → R' (q' + 4) = some v)
    (h8 : R' (q' + 8) = some x) (hx : x.toNat < 2 ^ 32)
    (hlv : ∀ lv, rl.fire = .levels lv → R' (q' + 4) = some lo ∧
      ∀ ln, R (q + 5) = some ln → hslice? R' lo.toNat ln.toNat = some hs) :
    decRule R' q' = some ⟨rl.ctor, rl.nfields, fireAt rl.fire hs, decI x⟩ := by
  have nat' : ∀ i, (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7) → ∀ y, nat? R (q + i) = some y →
      nat? R' (q' + i) = some y := by
    intro i hi y hy
    simp only [nat?, Option.map_eq_some_iff] at hy ⊢
    obtain ⟨v, hv, rfl⟩ := hy; exact ⟨v, hw i hi v hv, rfl⟩
  obtain ⟨hc, hn, -⟩ := decRule_fields' h
  have hc' : hd? R' q' = some rl.ctor := by
    simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hc ⊢
    obtain ⟨v, hv, e⟩ := hc; exact ⟨v, by simpa using hw 0 (by simp) v (by simpa using hv), e⟩
  have hn' : nat? R' (q' + 1) = some rl.nfields := nat' 1 (by simp) _ hn
  have hr' : hd? R' (q' + 8) = some (decI x : EIdx) := by
    simp only [hd?, h8, Option.bind_eq_bind, Option.bind_some, hx, ↓reduceIte]
  have tail : ∀ f : IRecRuleFire, (do
      let ctor ← hd? R' q'
      let nfields ← nat? R' (q' + 1)
      let rhs ← hd? R' (q' + 8)
      pure ({ ctor, nfields, fire := f, rhs } : IRecRule)) =
      some ⟨rl.ctor, rl.nfields, f, decI x⟩ := by
    intro f; simp only [hc', hn', hr', Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  have hlistc : ∀ {k : IdxKind} i, (i = 4 ∨ i = 6) → (∀ lv, rl.fire ≠ .levels lv) →
      ∀ xs : List (Idx k), hlist? R (q + i) = some xs → hlist? R' (q' + i) = some xs := by
    intro k i hi hnl xs hxs
    simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hxs ⊢
    obtain ⟨o, ho, c, hc, hsl⟩ := hxs
    refine ⟨o, ?_, c, ?_, hext.hslice? hsl⟩
    · rcases hi with rfl | rfl
      · simp only [nat?, Option.map_eq_some_iff] at ho ⊢
        obtain ⟨v, hv, rfl⟩ := ho; exact ⟨v, h4 hnl v hv, rfl⟩
      · exact nat' 6 (by simp) o ho
    · rcases hi with rfl | rfl
      · have := nat' 5 (by simp) c (by simpa [Nat.add_assoc] using hc)
        simpa [Nat.add_assoc] using this
      · have := nat' 7 (by simp) c (by simpa [Nat.add_assoc] using hc)
        simpa [Nat.add_assoc] using this
  unfold decRule at h ⊢
  cases h3 : nat? R (q + 3) with
  | none => simp [h3] at h
  | some t =>
    rw [nat' 3 (by simp) t h3]; rw [h3] at h
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some] at h ⊢
    match t, h with
    | 0, h =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨_, -, _, -, _, -, rfl⟩ := h
      exact tail _
    | 1, h =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨y, hy, z, hz, _, -, _, -, _, -, rfl⟩ := h
      have hnl : ∀ lv, IRecRuleFire.nested y z ≠ .levels lv := fun _ e => by cases e
      simp only [hlistc 4 (by simp) hnl y hy, hlistc 6 (by simp) hnl z hz, Option.bind_some]
      exact tail _
    | 2, h =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨y, hy, _, -, _, -, _, -, rfl⟩ := h
      obtain ⟨e4, hsl⟩ := hlv y rfl
      simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hy
      obtain ⟨o4, -, c5, hc5, -⟩ := hy
      simp only [nat?, Option.map_eq_some_iff] at hc5
      obtain ⟨v5, hv5, rfl⟩ := hc5
      have h5' := hw 5 (by simp) v5 (by simpa [Nat.add_assoc] using hv5)
      have hl' : hlist? R' (q' + 4) = some hs := by
        simp only [hlist?, nat?, e4, show q' + 4 + 1 = q' + 5 by omega, h5', Option.map_some,
          Option.bind_eq_bind, Option.bind_some, hsl v5 (by simpa [Nat.add_assoc] using hv5)]
      simp only [hl', Option.bind_some]
      exact tail _
    | _ + 3, h => simp at h

/-! ## The record words -/

/-- An `erec_put` continuation: the call returned, the memory is the put. -/
theorem putK {α : Type} {p : Prog} (hp : p.lookup "erec_put" = some erecPut) {n : Nat} {a v : Word}
    {m : Mem} {K : Option (List Word × Mem) → Option α} {z : α} (hK : K none = none)
    (h : K (callW p n "erec_put" [a, v] m) = some z) : ∃ r, K (some (r, erecPutMem m a v)) = some z := by
  cases h1 : callW p n "erec_put" [a, v] m with
  | none => rw [h1, hK] at h; cases h
  | some x =>
    obtain ⟨r, m'⟩ := x
    rw [h1] at h
    exact ⟨r, by rw [← callW_erecPut hp h1]; exact h⟩

theorem wrER_cons (m : Mem) (d x : Word) (ws : List Word) :
    wrER m d (x :: ws) = wrER (erecPutMem m d x) (d + 1) ws := rfl

theorem wrER_append (m : Mem) (d : Word) :
    ∀ (ws : List Word) (x : Word), wrER m d (ws ++ [x]) =
      erecPutMem (wrER m d ws) (d + UInt64.ofNat ws.length) x
  | [], x => by simp [wrER]
  | y :: ws, x => by
    simp only [List.cons_append, wrER_cons, wrER_append _ (d + 1) ws x, List.length_cons]
    congr 1
    rw [UInt64.add_assoc]; congr 1; apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_one]; omega

/-- **The 11 record words of a rule** (`j1`): one `wrER` at `d`, the copied words as each put
read them, then the next rule. -/
theorem j1_inv {p : Prog} (hp : p.lookup "erec_put" = some erecPut) {n : Nat}
    {ko kc us o l d rhs k lo : Word} {m m' : Mem} {res : List Word}
    (h : rulesAtLpsGoW.j1 p n ko kc us o l d rhs k lo m = some (res, m')) :
    ∃ w0 w1 w5 w6 w7 : Word, w0 = erRdT m o ∧ w1 = erRdT (wrER m d [w0]) (o + 1) ∧
      w5 = erRdT (wrER m d [w0, w1, 0, k, lo]) (o + 5) ∧
      w6 = erRdT (wrER m d [w0, w1, 0, k, lo, w5]) (o + 6) ∧
      w7 = erRdT (wrER m d [w0, w1, 0, k, lo, w5, w6]) (o + 7) ∧
      ∃ r', rulesAtLpsGoW p n (wrER m d [w0, w1, 0, k, lo, w5, w6, w7, rhs, 0, 0]) ko kc us (o + 11)
        (l - 1) (d + 11) = some (r', m') := by
  have rd : ∀ (X : Mem) (x : Word), rdW (X.arr64 (tierA EREC (x >>> 40))) (x &&& 1099511627775) =
      erRdT X x := fun _ _ => rfl
  rw [rulesAtLpsGoW.j1.arm1, rd] at h
  obtain ⟨_, h⟩ := putK hp (rulesAtLpsGoW.k_erec_put.none ..) h
  rw [rulesAtLpsGoW.k_erec_put.arm1, rd] at h
  obtain ⟨_, h⟩ := putK hp (rulesAtLpsGoW.k_erec_put_2.none ..) h
  rw [rulesAtLpsGoW.k_erec_put_2.arm1] at h
  obtain ⟨_, h⟩ := putK hp (rulesAtLpsGoW.k_erec_put_3.none ..) h
  rw [rulesAtLpsGoW.k_erec_put_3.arm1] at h
  obtain ⟨_, h⟩ := putK hp (rulesAtLpsGoW.k_erec_put_4.none ..) h
  rw [rulesAtLpsGoW.k_erec_put_4.arm1] at h
  obtain ⟨_, h⟩ := putK hp (rulesAtLpsGoW.k_erec_put_5.none ..) h
  rw [rulesAtLpsGoW.k_erec_put_5.arm1, rd] at h
  obtain ⟨_, h⟩ := putK hp (rulesAtLpsGoW.k_erec_put_6.none ..) h
  rw [rulesAtLpsGoW.k_erec_put_6.arm1, rd] at h
  obtain ⟨_, h⟩ := putK hp (rulesAtLpsGoW.k_erec_put_7.none ..) h
  rw [rulesAtLpsGoW.k_erec_put_7.arm1, rd] at h
  obtain ⟨_, h⟩ := putK hp (rulesAtLpsGoW.k_erec_put_8.none ..) h
  rw [rulesAtLpsGoW.k_erec_put_8.arm1] at h
  obtain ⟨_, h⟩ := putK hp (rulesAtLpsGoW.k_erec_put_9.none ..) h
  rw [rulesAtLpsGoW.k_erec_put_9.arm1] at h
  obtain ⟨_, h⟩ := putK hp (rulesAtLpsGoW.k_erec_put_10.none ..) h
  rw [rulesAtLpsGoW.k_erec_put_10.arm1] at h
  obtain ⟨_, h⟩ := putK hp (rulesAtLpsGoW.k_erec_put_11.none ..) h
  rw [rulesAtLpsGoW.k_erec_put_11.arm1] at h
  cases h2 : rulesAtLpsGoW p n _ ko kc us (o + 11) (l - 1) (d + 11) with
  | none => rw [h2] at h; simp [rulesAtLpsGoW.k_rules_at_lps_go.none] at h
  | some x =>
  obtain ⟨r', m''⟩ := x
  rw [h2, rulesAtLpsGoW.k_rules_at_lps_go.arm1, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, r', ?_⟩
  simp only [wrER, UInt64.add_assoc, UInt64.reduceAdd] at h2 ⊢
  exact h2

end L.Ind
