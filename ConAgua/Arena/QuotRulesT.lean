module

public import ConAgua.Arena.QuotCiT
public import ConAgua.Arena.InstLPSpec
import ConAgua.Arena.RecFireCore
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.InstLPRef
import ConAgua.Arena.LevelArena
import ConAgua.Arena.LevelEquiv
import ConAgua.Arena.LevelInternRef
import ConAgua.Arena.RecFireEnv
import ConAgua.Arena.WhnfIotaRecRefine
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

/-! ## The program -/

/-- The lookups the rules need beyond `CiProg`. -/
structure RulesProg (p : Prog) : Prop extends CiProg p where
  ls : LsProg p
  fireAt : p.lookup "fire_levels_at" = some fireLevelsAt
  spnToEr : p.lookup "spn_to_er" = some spnToEr
  rulesGo : p.lookup "rules_at_lps_go" = some rulesAtLpsGo

set_option maxRecDepth 20000 in
theorem keysPush_stageCore : "keys_push" ∈ stageCoreFns :=
  mem_stageCoreFns (List.mem_append_right _ (List.elem_iff.mp (by decide))) (by simp [coreLeafOnly])
set_option maxRecDepth 20000 in
theorem sleGo_stageCore : "sle_go" ∈ stageCoreFns :=
  mem_stageCoreFns (List.mem_append_right _ (List.elem_iff.mp (by decide))) (by simp [coreLeafOnly])

/-! ## Small facts -/

theorem erAllocW_mem {m m' : Mem} {k q : Word} (h : erAllocW m k = some (q, m')) : m' = erAllocMem m k := by
  unfold erAllocW at h
  by_cases c : rdW (m.arr64 CTL) 1 = 0
  · simp only [c, ↓reduceIte] at h
    split at h; · cases h
    split at h; · cases h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2, erAllocMem, if_pos c]
  · simp only [c, ↓reduceIte] at h
    split at h; · cases h
    split at h; · cases h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2, erAllocMem, if_neg c]

theorem erTopOf_put (m : Mem) (a v x : Word) : erTopOf (erecPutMem m a v) x = erTopOf m x := by
  simp only [erTopOf, erecTop, erecTop1, erecPutMem_ctl]

theorem erTopOf_wrER : ∀ (ws : List Word) (m : Mem) (d x : Word), erTopOf (wrER m d ws) x = erTopOf m x
  | [], _, _, _ => rfl
  | w :: ws, m, d, x => by rw [wrER_cons, erTopOf_wrER ws, erTopOf_put]

theorem IWGrow.topOf {m m' : Mem} (hg : IWGrow m m') (x : Word) : erTopOf m x ≤ erTopOf m' x := by
  unfold erTopOf; split
  · exact hg.er
  · exact hg.er1

section stage
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`StageT` across the stack top's write** (`CTL[136]`). -/
theorem StageT.ctl136 {m : Mem} {a : AState} (hT : StageT dn vis fe m a) (b : Word) :
    StageT dn vis fe (m.set64 CTL 136 b) a ∧ IWGrow m (m.set64 CTL 136 b) := by
  have hfr := MemFrame.setCtl m 136 b
  obtain ⟨M, hC⟩ := hT.core
  have hC' := hC.frame_stk hfr (by simp) (by simp)
  have hI : (m.set64 CTL 136 b).arr64 IW = m.arr64 IW := hfr.arr _ (by simp) (by decide)
  have hE' : (m.set64 CTL 136 b).arr64 EREC = m.arr64 EREC := hfr.arr _ (by simp) (by decide)
  have hE1' : (m.set64 CTL 136 b).arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hfr.arr _ (by simp) (by decide)
  have hP' : (m.set64 CTL 136 b).arr64 PINS = m.arr64 PINS := hfr.arr _ (by simp) (by decide)
  have h129' := hfr.ctl 129 (by decide)
  have h130' := hfr.ctl 130 (by decide)
  have h200' := hfr.ctl 200 (by decide)
  obtain ⟨hCR, hTw⟩ := hC'.checkR
  refine ⟨⟨⟨hCR, IWOK.frame hfr (by simp) (by simp) (by decide) (by decide) hT.stage.iw⟩, hTw,
    by simp only [pinW, hP']; exact hT.flag⟩, ?_⟩
  exact ⟨by simp [iwTop, h200'], by simp [erTop, h129'], fun i _ => by rw [hI], fun i _ => by rw [hE'],
    by simp [erecTop1, h130'], fun i _ => by rw [hE1']⟩

/-! ## `fire_levels_at` -/

/-- **`fire_levels_at(fo, fl, ko, kc, us)` refines `substLevelsAt`** under `StageT`: the
levels of the slice `(fo, fl)` substituted (keys the names of `(ko, kc)`, values `us`), as a fresh
slice above `m`'s top; `StageT` after. -/
theorem fireStep {p : Prog} (hP : RulesProg p) {n : Nat} {m m' : Mem} {a : AState}
    {fo fl ko kc us : Word} {r : List Word} {lvls : List LIdx} {lpsH : List NIdx}
    {lpsT : List ConLeche.Name} {usT : List ConLeche.Level}
    (hT : StageT dn vis fe m a) (hus : H us)
    (hl : hslice? (erecP m) ko.toNat kc.toNat = some lpsH)
    (hks : lpsH.mapM (denoteN a.store.ns) = some lpsT)
    (husT : denoteLs a.store.lss (decI us) = some usT)
    (hlv : hslice? (erecP m) fo.toNat fl.toNat = some lvls)
    (hd : ∀ u ∈ lvls, ∃ L, denoteL a.store.ls u = some L)
    (h : callW p n "fire_levels_at" [fo, fl, ko, kc, us] m = some (r, m')) :
    ∃ hs a', (substLevelsAt lpsT usT lvls).run a = .ok (hs, a') ∧ StageT dn vis fe m' a' ∧
      IWGrow m m' ∧ MemFrame quotA quotC m m' ∧ erTopOf m (r.headD 0) ≤ erOff (r.headD 0) ∧
      erOff (r.headD 0) + fl.toNat ≤ erTopOf m' (r.headD 0) ∧ (r.headD 0).toNat < 2 ^ 41 ∧
      hs.length = fl.toNat ∧
      ∀ j < fl.toNat, erecP m' ((r.headD 0).toNat + j) = (lsWords hs)[j]? := by
  have hqf := callW_quotFrame hP.quot (by decide) h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (fireLevelsAt_specW p hP.fireAt n _ fo fl ko kc us) h
  cases n with
  | zero => simp [fireLevelsAtW] at hW
  | succ n =>
  simp only [fireLevelsAtW] at hW
  obtain ⟨M, hC⟩ := hT.core
  -- `ls_node`
  cases h1 : callW p n "ls_node" [us] m with
  | none => rw [h1] at hW; simp [fireLevelsAtW.k_ls_node.none] at hW
  | some x1 =>
  obtain ⟨vs', mx⟩ := x1
  rw [h1, fireLevelsAtW.k_ls_node.arm1] at hW
  obtain ⟨s₁, hs₁m, hs₁, -, hv'⟩ :=
    triple_of_callW (lsNode_spec p hP.ls.ls_node n ⟨m, Locals.init []⟩ us) h1
  have hmx : mx = m := by rw [← hs₁m, hs₁]
  subst hmx
  obtain ⟨ids, hvw, hdl'⟩ := denoteLs_view a (decI us) usT husT
  obtain ⟨e₁, t₁, sl₁⟩ := lsNodeW_store hC.arena.base hus hvw
  rw [hv', e₁] at hW
  simp only [List.headD_cons, List.tail_cons] at hW
  -- `keys_push`
  cases h2 : callW p n "keys_push" [ko, kc] mx with
  | none => rw [h2] at hW; simp [fireLevelsAtW.k_keys_push.none] at hW
  | some x2 =>
  obtain ⟨bs, m₁⟩ := x2
  rw [h2] at hW
  obtain ⟨s₂, hs₂m, -, hW₂⟩ :=
    triple_of_callW (keysPush_spec p hP.ls.toLvSubProg n ⟨mx, Locals.init []⟩ ko kc) h2
  rw [hs₂m] at hW₂
  obtain ⟨hb, hks₁, hf₁, htop₁, hroom, -⟩ :=
    keysPushW_ok n mx m₁ ko kc (bs.headD 0) lpsH hl hC.spn hC.ctl136 hW₂
  have hk₁ := lp_nmsR_of_hslice a.store.lss.ls.ns m₁ SPN lpsH lpsT (bs.headD 0) kc hks₁
    (by have := hC.spn; omega) hks
  have hC₁ := hC.frame_stk hf₁ (by simp) (by simp)
  obtain ⟨hT₁, hg₁⟩ := StageT.of_core hP.core keysPush_stageCore h2 hT hC₁
  have herec₁ : erecP m₁ = erecP mx := erecP_frame hf₁ (by decide) (by decide) (by decide) (by decide)
  have hpool₁ : m₁.arr64 POOL = mx.arr64 POOL := hf₁.1 POOL (by simp [SPN, POOL]) (by decide)
  have hpool₁' : m₁.arr64 POOL1 = mx.arr64 POOL1 := hf₁.1 POOL1 (by simp [SPN, POOL1]) (by decide)
  have hpool₁v := vpool_congr hpool₁ hpool₁'
  have htopm₁ : m₁.top = mx.top := by simp only [top_rdW]; exact hf₁.ctl 0 (by simp)
  have hsz₁ : (m₁.arr64 SPN).size = (mx.arr64 SPN).size := hf₁.size SPN
  have hspn := hC.spn
  have hlen : (m₁.len64 SPN).toNat = (mx.arr64 SPN).size := by
    rw [← hsz₁]; exact L.Front.toNat_ofNat_size _ (by rw [hsz₁]; exact hspn)
  have hE : ILWEnv m₁ a (bs.headD 0) kc (tfld mx LVLS (tierW us) (idxW us) 0)
      (tfld mx LVLS (tierW us) (idxW us) 1) lpsT ids usT :=
    ⟨hk₁, by omega, by rw [hpool₁v]; exact sl₁, by rw [htopm₁]; exact t₁, hdl'⟩
  have hsp : rdW (m₁.arr64 CTL) 136 = spTop m₁ := rfl
  by_cases u1 : m₁.len64 SPN < spTop m₁
  · rw [fireLevelsAtW.k_keys_push.abort1 _ _ _ _ _ _ _ _ _ (by rw [hsp]; exact u1)] at hW; cases hW
  by_cases u2 : m₁.len64 SPN - spTop m₁ < fl
  · rw [fireLevelsAtW.k_keys_push.abort2 _ _ _ _ _ _ _ _ _ (by rw [hsp]; exact u1)
      (by rw [hsp]; exact u2)] at hW; cases hW
  rw [fireLevelsAtW.k_keys_push.arm1 _ _ _ _ _ _ _ _ _ (by rw [hsp]; exact u1)
    (by rw [hsp]; exact u2), hsp] at hW
  have u2' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp u2)
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp u1), hlen] at u2'
  have u1' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp u1)
  rw [hlen] at u1'
  -- `sle_go`
  cases h3 : callW p n "sle_go" [fo, fl, spTop m₁, bs.headD 0, kc, tfld mx LVLS (tierW us) (idxW us) 0,
      tfld mx LVLS (tierW us) (idxW us) 1] m₁ with
  | none => rw [h3] at hW; simp [fireLevelsAtW.k_sle_go.none] at hW
  | some x3 =>
  obtain ⟨xs, m₂⟩ := x3
  rw [h3, fireLevelsAtW.k_sle_go.arm1] at hW
  obtain ⟨s₃, hs₃m, -, hW₃⟩ :=
    triple_of_callW (sleGo_spec p hP.ls n ⟨m₁, Locals.init []⟩ _ _ _ _ _ _ _) h3
  rw [hs₃m] at hW₃
  obtain ⟨hs, a₃, hrun₂, hC₃, -, -, hsl₂, -, -⟩ :=
    sleElemW_core lvls n m₁ m₂ _ fo fl (spTop m₁) hC₁ hE (by rw [herec₁]; exact hlv) hd
      (Nat.le_refl _) (by rw [hsz₁]; omega) hW₃
  obtain ⟨hT₃, hg₃⟩ := StageT.of_core hP.core sleGo_stageCore h3 hT₁ hC₃
  have hlen₂ : hs.length = fl.toNat := by
    have := congrArg List.length hsl₂; simp [sliceL_length, lsWords] at this; omega
  -- `erec_alloc(fl)`
  cases h4 : callW p n "erec_alloc" [fl] m₂ with
  | none => rw [h4] at hW; simp [fireLevelsAtW.k_erec_alloc.none] at hW
  | some x4 =>
  obtain ⟨r4, m₄⟩ := x4
  rw [h4, fireLevelsAtW.k_erec_alloc.arm1] at hW
  have hA4 := callW_erecAlloc hP.erAlloc h4
  obtain ⟨hT₄, hg₄, hoff₄, htop₄, hd41⟩ := erAlloc_stageT hA4 hT₃
  have hqf4 := callW_quotFrame hP.quot (by decide) h4
  have hspn4 : m₄.arr64 SPN = m₂.arr64 SPN := by
    rw [erAllocW_mem hA4]; exact erAllocMem_arr _ _ (by decide)
  -- `spn_to_er(d, c, fl)`
  cases h5 : callW p n "spn_to_er" [r4.headD 0, spTop m₁, fl] m₄ with
  | none => rw [h5] at hW; simp [fireLevelsAtW.k_spn_to_er.none] at hW
  | some x5 =>
  obtain ⟨r5, m₅⟩ := x5
  rw [h5, fireLevelsAtW.k_spn_to_er.arm1, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, hm'⟩ := hW
  obtain ⟨s₅, rfl, -, hW₅⟩ := triple_of_callW (s₀ := ⟨m₄, Locals.init []⟩)
    (spnToEr_specW p hP.spnToEr n _ _ _ _) h5
  have e5 := spnToErW_eq hP.erPut fl.toNat n m₄ _ _ fl _ _ rfl hW₅
  generalize hws : (List.range fl.toNat).map (fun j => rdW (m₄.arr64 SPN) (spTop m₁ + UInt64.ofNat j)) = ws
    at e5
  have hwsl : ws = lsWords hs := by
    rw [← hws, ← hsl₂, hspn4]
    apply List.ext_getElem (by simp [sliceL_length])
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, sliceL, List.getElem_ofFn, rdW]
    congr 2
    simp only [List.length_map, List.length_range] at h1
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']
    have := hT₃.twin.spn
    omega
  have hcap4 := hT₄.stage.iw.topOf (r4.headD 0)
  obtain ⟨hS₅, hg₅, hf₅, hrd₅, -⟩ := wrER_fresh hT₃.stage ws m₄ _ (r4.headD 0) hT₄.stage hqf4 hg₄
    (by rw [hoff₄]; exact Nat.le_refl _) (by rw [htop₄, hoff₄, hwsl]; simp [lsWords, hlen₂]) hd41
  rw [← e5] at hS₅ hg₅ hrd₅
  have hT₅ : StageT dn vis fe s₅.mem a₃ := by rw [e5] at hS₅ ⊢; exact StageT.of_wrER hT₄ hS₅
  obtain ⟨hT₆, hg₆⟩ := hT₅.ctl136 (bs.headD 0)
  have hfr6 := MemFrame.setCtl s₅.mem 136 (bs.headD 0)
  have herec6 : erecP (s₅.mem.set64 CTL 136 (bs.headD 0)) = erecP s₅.mem :=
    erecP_frame hfr6 (by simp) (by simp) (by decide) (by decide)
  have htop6 : ∀ x, erTopOf (s₅.mem.set64 CTL 136 (bs.headD 0)) x = erTopOf s₅.mem x := fun x => by
    simp only [erTopOf, erecTop, erecTop1, hfr6.ctl 129 (by decide), hfr6.ctl 130 (by decide)]
  have htop5 : erTopOf s₅.mem (r4.headD 0) = erTopOf m₄ (r4.headD 0) := by rw [e5, erTopOf_wrER]
  rw [← hm']
  simp only [List.headD_cons]
  refine ⟨hs, a₃, hrun₂, hT₆, hg₁.trans (hg₃.trans (hg₅.trans hg₆)), hm' ▸ hqf, ?_, ?_, hd41, hlen₂, ?_⟩
  · rw [hoff₄]; exact (hg₁.trans hg₃).topOf _
  · rw [htop6, htop5, htop₄, hoff₄]; exact Nat.le_refl _
  · intro j hj
    rw [herec6, hrd₅ j (by rw [hwsl]; simp [lsWords, hlen₂]; exact hj), hwsl]

/-! ## Cells of the record pool -/

theorem erecP_alias (X : Mem) {i c : Nat} (hi : i < 2 ^ 64) (hc : c < 2 ^ 64)
    (h : i % 2 ^ 41 = c % 2 ^ 41) : erecP X i = erecP X c := by
  have h1 : i / 2 ^ 40 % 2 = c / 2 ^ 40 % 2 := by omega
  have h2 : i % 2 ^ 40 = c % 2 ^ 40 := by omega
  simp only [erecP, hi, hc, ↓reduceIte, h1, h2]

/-- A defined cell and an undefined one are different cells. -/
theorem cell_ne {X : Mem} {i c : Nat} (hi : erecP X i ≠ none) (hc : erecP X c = none)
    (hc64 : c < 2 ^ 64) : i % 2 ^ 41 ≠ c % 2 ^ 41 := by
  intro e
  have hi64 : i < 2 ^ 64 := by
    cases h : erecP X i with
    | none => exact absurd h hi
    | some w => exact L.Ind.erecP_lt64 h
  exact hi (by rw [erecP_alias X hi64 hc64 e]; exact hc)

/-- The cells at and above a tier's top are undefined. -/
theorem region_none {X : Mem} {d : Word} {j : Nat} (ht : erTopOf X d ≤ erOff d)
    (hj : erOff d + j < 2 ^ 40) (hd : d.toNat < 2 ^ 41) : erecP X (d.toNat + j) = none := by
  unfold erOff at hj ht
  have hlt : d.toNat + j < 2 ^ 64 := by omega
  have h1 : (d.toNat + j) / 2 ^ 40 % 2 = d.toNat / 2 ^ 40 % 2 := by omega
  have h2 : (d.toNat + j) % 2 ^ 40 = d.toNat % 2 ^ 40 + j := by omega
  unfold erTopOf at ht
  simp only [erecP, hlt, ↓reduceIte, h1, h2]
  by_cases hA : d.toNat / 2 ^ 40 % 2 = 0
  · simp only [hA, ↓reduceIte] at ht ⊢; rw [if_neg (by omega)]
  · simp only [hA, ↓reduceIte] at ht ⊢; rw [if_neg (by omega)]

/-- The cells below a tier's top are defined. -/
theorem region_def {X : Mem} (hI : IWOK X) {d : Word} {j : Nat} (ht : erOff d + j < erTopOf X d)
    (hd : d.toNat < 2 ^ 41) : erecP X (d.toNat + j) ≠ none := by
  obtain ⟨htop, hcap⟩ := hI.topOf d
  have hj : erOff d + j < 2 ^ 40 := by omega
  unfold erOff at ht hj
  have hlt : d.toNat + j < 2 ^ 64 := by omega
  have h1 : (d.toNat + j) / 2 ^ 40 % 2 = d.toNat / 2 ^ 40 % 2 := by omega
  have h2 : (d.toNat + j) % 2 ^ 40 = d.toNat % 2 ^ 40 + j := by omega
  unfold erTopOf erTier at htop; unfold erTopOf at ht
  simp only [erecP, hlt, ↓reduceIte, h1, h2]
  by_cases hA : d.toNat / 2 ^ 40 % 2 = 0
  · simp only [hA, ↓reduceIte] at ht htop ⊢
    rw [if_pos ht, Array.getElem?_eq_getElem (by omega)]; simp
  · simp only [hA, ↓reduceIte] at ht htop ⊢
    rw [if_pos ht, Array.getElem?_eq_getElem (by omega)]; simp

/-- A cell the base does not define is above its top: readers agreeing above it agree there. -/
theorem agree_cell {m₀ M Y : Mem} (hI : IWOK m₀) {c : Nat} (hc : erecP m₀ c = none)
    (hc41 : c < 2 ^ 41) (hA : AgreeAbove m₀ M Y) : erecP Y c = erecP M c := by
  have e : (UInt64.ofNat c).toNat = c := by simp; omega
  have := hA (UInt64.ofNat c) (Nat.le_of_not_lt fun hlt => by
    have hq := region_def (j := 0) hI (d := UInt64.ofNat c) (by simpa using hlt) (by rw [e]; exact hc41)
    rw [Nat.add_zero, e] at hq
    exact hq hc)
  rwa [e] at this

end stage

end L.Ind
