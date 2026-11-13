module

public import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.RecLayout.RuleDec
import ConAgua.Arena.IndInstallSpec.IcbiW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndDeclConsts

@[expose] public section

/-!
# A declaration's constants: the recursor rules refired (lane `ronsync2`, stage 3)

`rules_refire(d, s, cnt, kind, lo, ll, po, pl)` writes `cnt` 11-word rule records at `d`, each the
record at `s + 11 j` with the fire `(kind, lo, ll, po, pl)` (`{ · with fire := f }`, con-ron's
`blockRecs`): the memory is `wrER` of the records' words (`rrW_mem`), and each record decodes as
the rule refired (`decRule_refire`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The memory after one record's eleven `erec_put`s (each copy reads the memory of its time). -/
def rrMem (m1 : Mem) (q old k flo fll fpo fpl : Word) : Mem :=
  let m2 := erecPutMem m1 q (erRd m1 old)
  let m3 := erecPutMem m2 (q + 1) (erRd m2 (old + 1))
  let m9 := erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem m3 (q + 2) 0)
    (q + 3) k) (q + 4) flo) (q + 5) fll) (q + 6) fpo) (q + 7) fpl
  let m10 := erecPutMem m9 (q + 8) (erRd m9 (old + 8))
  erecPutMem (erecPutMem m10 (q + 9) 0) (q + 10) 0

/-- **The model of `rules_refire(d, s, cnt, k, lo, ll, po, pl)`** at exec fuel `n`. -/
l_model rr_spec (p : Prog) (hpu : p.lookup "erec_put" = some erecPut)
    (hp : p.lookup "rules_refire" = some rulesRefire)
  fns [hp ↦ rrW list]
  specs [erecPut_specM p hpu n]
  grind [arena_grind]

/-- `rrW`'s recursive arm by its memory `rrMem`. -/
theorem rrW_cons {n : Nat} {m : Mem} {d s cnt k lo ll po pl : Word} (h : cnt ≠ 0) :
    rrW (n + 1) m d s cnt k lo ll po pl =
      rrW.k_rules_refire (rrW n (rrMem m d s k lo ll po pl) (d + 11) (s + 11) (cnt - 1) k lo ll po pl) := by
  rw [rrW.arm2 (hc1 := h)]; rfl

/-! ## The written words -/

theorem rrMem_eq {m1 : Mem} {q old k flo fll fpo fpl : Word}
    (hfr : ∀ x ∈ [old, old + 1, old + 8], ErApart q 11 x) :
    rrMem m1 q old k flo fll fpo fpl = wrER m1 q [erRd m1 old, erRd m1 (old + 1), 0, k, flo, fll, fpo, fpl,
      erRd m1 (old + 8), 0, 0] := by
  have f0 : ∀ x ∈ [old, old + 1, old + 8], erTier x ≠ erTier q ∨ erOff x ≠ erOff q :=
    fun x hx => by simpa using hfr x hx 0 (by decide)
  have f1 : ∀ x ∈ [old, old + 1, old + 8], erTier x ≠ erTier (q + 1) ∨ erOff x ≠ erOff (q + 1) :=
    fun x hx => hfr x hx 1 (by decide)
  have f2 : ∀ x ∈ [old, old + 1, old + 8], erTier x ≠ erTier (q + 2) ∨ erOff x ≠ erOff (q + 2) :=
    fun x hx => hfr x hx 2 (by decide)
  have f3 : ∀ x ∈ [old, old + 1, old + 8], erTier x ≠ erTier (q + 3) ∨ erOff x ≠ erOff (q + 3) :=
    fun x hx => hfr x hx 3 (by decide)
  have f4 : ∀ x ∈ [old, old + 1, old + 8], erTier x ≠ erTier (q + 4) ∨ erOff x ≠ erOff (q + 4) :=
    fun x hx => hfr x hx 4 (by decide)
  have f5 : ∀ x ∈ [old, old + 1, old + 8], erTier x ≠ erTier (q + 5) ∨ erOff x ≠ erOff (q + 5) :=
    fun x hx => hfr x hx 5 (by decide)
  have f6 : ∀ x ∈ [old, old + 1, old + 8], erTier x ≠ erTier (q + 6) ∨ erOff x ≠ erOff (q + 6) :=
    fun x hx => hfr x hx 6 (by decide)
  have f7 : ∀ x ∈ [old, old + 1, old + 8], erTier x ≠ erTier (q + 7) ∨ erOff x ≠ erOff (q + 7) :=
    fun x hx => hfr x hx 7 (by decide)
  simp only [rrMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl, show q + 6 + 1 = q + 7 by ac_rfl,
    show q + 7 + 1 = q + 8 by ac_rfl, show q + 8 + 1 = q + 9 by ac_rfl,
    show q + 9 + 1 = q + 10 by ac_rfl]
  simp (disch := first
    | exact f0 _ (by simp) | exact f1 _ (by simp) | exact f2 _ (by simp) | exact f3 _ (by simp)
    | exact f4 _ (by simp) | exact f5 _ (by simp) | exact f6 _ (by simp) | exact f7 _ (by simp))
    only [erRd_erecPutMem_ne]

/-- One refired record's words. -/
def refireRec (m : Mem) (s k lo ll po pl : Word) : List Word :=
  [erRd m s, erRd m (s + 1), 0, k, lo, ll, po, pl, erRd m (s + 8), 0, 0]

/-- The words `rules_refire` writes: each source record refired. -/
def refireWords (m : Mem) (k lo ll po pl : Word) : Word → Nat → List Word
  | _, 0 => []
  | s, c + 1 => refireRec m s k lo ll po pl ++ refireWords m k lo ll po pl (s + 11) c

theorem refireWords_length (m : Mem) (k lo ll po pl : Word) :
    ∀ (s : Word) (c : Nat), (refireWords m k lo ll po pl s c).length = 11 * c
  | _, 0 => rfl
  | s, c + 1 => by
    simp [refireWords, refireRec, refireWords_length m k lo ll po pl (s + 11) c]; omega

theorem shift11 (s : Word) (j i : Nat) : s + 11 + UInt64.ofNat (11 * j + i) = s + UInt64.ofNat (11 * (j + 1) + i) := by
  rw [show 11 * (j + 1) + i = (11 * j + i) + 11 by omega, UInt64.ofNat_add (11 * j + i) 11]
  show _ = s + (_ + 11)
  ac_rfl

/-- The source words read the same: the written words agree. -/
theorem refireWords_congr {m m' : Mem} (k lo ll po pl : Word) :
    ∀ (s : Word) (c : Nat), (∀ j < c, ∀ i, (i = 0 ∨ i = 1 ∨ i = 8) → erRd m' (s + UInt64.ofNat (11 * j + i)) =
      erRd m (s + UInt64.ofNat (11 * j + i))) →
      refireWords m' k lo ll po pl s c = refireWords m k lo ll po pl s c
  | _, 0, _ => rfl
  | s, c + 1, h => by
    simp only [refireWords, refireRec]
    have h0 := h 0 (by omega) 0 (by simp)
    have h1 := h 0 (by omega) 1 (by simp)
    have h8 := h 0 (by omega) 8 (by simp)
    simp only [Nat.mul_zero, Nat.zero_add, show (UInt64.ofNat 0 : Word) = 0 from rfl, UInt64.add_zero,
      show (UInt64.ofNat 1 : Word) = 1 from rfl, show (UInt64.ofNat 8 : Word) = 8 from rfl] at h0 h1 h8
    rw [h0, h1, h8, refireWords_congr (m := m) (m' := m') k lo ll po pl (s + 11) c (fun j hj i hi => by
      rw [shift11]; exact h (j + 1) (by omega) i hi)]

/-- **`rules_refire` writes the refired records**: the memory is `wrER` of their words. -/
theorem rrW_mem (k lo ll po pl : Word) : ∀ (n : Nat) (m m' : Mem) (d s cnt : Word) (r : List Word),
    rrW n m d s cnt k lo ll po pl = some (r, m') →
    (∀ j < cnt.toNat, ∀ i, (i = 0 ∨ i = 1 ∨ i = 8) → ErApart d (11 * cnt.toNat) (s + UInt64.ofNat (11 * j + i))) →
    m' = wrER m d (refireWords m k lo ll po pl s cnt.toNat)
  | 0, _, _, _, _, _, _, h, _ => by simp [rrW] at h
  | n + 1, m, m', d, s, cnt, r, h, hfr => by
    by_cases h0 : cnt = 0
    · rw [rrW.arm1 (hc1 := h0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      subst h0; rw [← h.2]; simp [refireWords, wrER]
    rw [rrW_cons h0] at h
    have hl0 : cnt.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
    have hl1 : (cnt - 1).toNat = cnt.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
    rcases h2 : rrW n (rrMem m d s k lo ll po pl) (d + 11) (s + 11) (cnt - 1) k lo ll po pl with _ | ⟨r2, m2⟩ <;>
      simp only [h2, rrW.k_rules_refire, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    have hfr0 : ∀ x ∈ [s, s + 1, s + 8], ErApart d 11 x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · have := hfr 0 (by omega) 0 (by simp)
        simp only [Nat.mul_zero, Nat.zero_add, show (UInt64.ofNat 0 : Word) = 0 from rfl, UInt64.add_zero] at this
        exact this.mono (by omega)
      · exact (hfr 0 (by omega) 1 (by simp)).mono (by omega)
      · exact (hfr 0 (by omega) 8 (by simp)).mono (by omega)
    rw [rrMem_eq hfr0] at h2
    have h11 : d + 11 = d + UInt64.ofNat 11 := rfl
    have ih := rrW_mem k lo ll po pl n _ m2 (d + 11) (s + 11) (cnt - 1) r2 h2 (fun j hj i hi => by
      rw [h11, shift11]
      exact ErApart.shift (by rw [hl1] at hj; exact (hfr (j + 1) (by omega) i hi).mono (by omega)))
    rw [ih, hl1, refireWords_congr (m := m) k lo ll po pl (s + 11) (cnt.toNat - 1) (fun j hj i hi => by
      rw [shift11]
      exact erRd_wrER_ne _ _ _ _ ((hfr (j + 1) (by omega) i hi).mono (by simp; omega)))]
    conv => rhs; rw [show cnt.toNat = (cnt.toNat - 1) + 1 by omega]
    simp only [refireWords]
    rw [wrER_append]
    rfl

theorem refireWords_get (m : Mem) (k lo ll po pl : Word) : ∀ (s : Word) (c j i : Nat), j < c → i < 11 →
    (refireWords m k lo ll po pl s c)[11 * j + i]? =
      (refireRec m (s + UInt64.ofNat (11 * j)) k lo ll po pl)[i]?
  | _, 0, _, _, hj, _ => absurd hj (by omega)
  | s, c + 1, 0, i, _, hi => by
    simp only [refireWords, Nat.mul_zero, Nat.zero_add, show (UInt64.ofNat 0 : Word) = 0 from rfl, UInt64.add_zero]
    rw [List.getElem?_append_left (by simp [refireRec]; omega)]
  | s, c + 1, j + 1, i, hj, hi => by
    simp only [refireWords]
    rw [List.getElem?_append_right (by simp [refireRec]; omega)]
    have e : 11 * (j + 1) + i - (refireRec m s k lo ll po pl).length = 11 * j + i := by
      simp [refireRec]; omega
    rw [e, refireWords_get m k lo ll po pl (s + 11) c j i (by omega) hi]
    have := shift11 s j 0
    simp only [Nat.add_zero] at this
    rw [this]

/-! ## The refired records decode -/

/-- A fire `(kind, lo, ll, po, pl)` (slices in the record pool) decoding as `f`. -/
def FireAt (R : Nat → Option Word) (k lo ll po pl : Word) : IRecRuleFire → Prop
  | .plain => k = 0
  | .nested lv ps => k = 1 ∧ hslice? R lo.toNat ll.toNat = some lv ∧ hslice? R po.toNat pl.toNat = some ps
  | .levels _ => False

theorem FireAt.ext {R R' : Nat → Option Word} (hx : ArrExt R R') {k lo ll po pl : Word} {f : IRecRuleFire}
    (h : FireAt R k lo ll po pl f) : FireAt R' k lo ll po pl f := by
  cases f with
  | plain => exact h
  | nested lv ps => exact ⟨h.1, hx.hslice? h.2.1, hx.hslice? h.2.2⟩
  | levels _ => exact h.elim

/-- A rule record whose plain fields are copied and whose fire is `f`, its words at `q'`. -/
theorem decRule_refireAt {R R' : Nat → Option Word} {q q' : Nat} {rl : IRecRule} {k lo ll po pl : Word}
    {f : IRecRuleFire} (h : decRule R q = some rl)
    (h0 : R' q' = R q) (h1 : R' (q' + Rule.nfields.toNat) = R (q + Rule.nfields.toNat))
    (h8 : R' (q' + Rule.rhs.toNat) = R (q + Rule.rhs.toNat))
    (h3 : R' (q' + Rule.fire.toNat) = some k) (h4 : R' (q' + Rule.lvlsOff.toNat) = some lo)
    (h5 : R' (q' + Rule.lvlsLen.toNat) = some ll) (h6 : R' (q' + Rule.pinsOff.toNat) = some po)
    (h7 : R' (q' + Rule.pinsLen.toNat) = some pl) (hf : FireAt R' k lo ll po pl f) :
    decRule R' q' = some { rl with fire := f } := by
  cases f with
  | nested lv ps =>
    obtain ⟨rfl, hl, hp⟩ := hf
    exact decRule_nested h h0 h1 h8 h3 h4 h5 h6 h7 hl hp
  | levels _ => exact hf.elim
  | plain =>
    have hk : k = 0 := hf
    subst hk
    exact L.Arena.decRule_refire h h0 h1 h8 (show nat? R' _ = some 0 by simp [nat?, h3])

/-- **`rules_refire` into a fresh run, under the stage relation**: the run decodes as the source
rules, each refired. -/
theorem rrW_ok {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m m1 m' : Mem}
    {run o cnt k lo ll po pl : Word} {r : List Word} {rules : List IRecRule} {f : IRecRuleFire}
    (ha : erAllocW m (11 * cnt) = some (run, m1)) (hS : StageR vis fe m a) (hc : cnt.toNat < 2 ^ 32)
    (hd : decRules (erecP m) o.toNat cnt.toNat = some rules)
    (hf : FireAt (erecP m) k lo ll po pl f)
    (h : rrW n m1 run o cnt k lo ll po pl = some (r, m')) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decRules (erecP m') run.toNat cnt.toNat = some (rules.map fun rl => { rl with fire := f }) := by
  have hk : (11 * cnt).toNat = 11 * cnt.toNat := by
    rw [UInt64.toNat_mul]; simp; omega
  obtain ⟨-, hf1, -⟩ := erAllocW_spec ha hS.iw
  have hr1 : ∀ x, erRd m1 x = erRd m x := fun x => by
    unfold erRd; rw [hf1.arr _ (by simp) (by rw [tierA_EREC]; split <;> decide)]
  obtain ⟨hlen, hget⟩ := L.Arena.decRules_get hd
  -- the source words read
  have hword : ∀ j < cnt.toNat, ∀ i, (i = 0 ∨ i = 1 ∨ i = 8) → ∃ w,
      erecP m (o.toNat + 11 * j + i) = some w ∧ erRd m (o + UInt64.ofNat (11 * j + i)) = w ∧
      (o + UInt64.ofNat (11 * j + i)).toNat = o.toNat + 11 * j + i := by
    intro j hj i hi
    have hrj := hget j hj
    rw [List.getElem?_eq_getElem (by omega)] at hrj
    obtain ⟨hc0, hn0, hr0⟩ := decRule_fields hrj
    -- `rules_refire` copies the words by number
    change hd? _ (o.toNat + 11 * j) = _ at hc0
    change nat? _ (o.toNat + 11 * j + 1) = _ at hn0
    change hd? _ (o.toNat + 11 * j + 8) = _ at hr0
    have hw : ∃ w, erecP m (o.toNat + 11 * j + i) = some w := by
      rcases hi with rfl | rfl | rfl
      · obtain ⟨w, hw, -⟩ := hd?_some hc0; exact ⟨w, by simpa using hw⟩
      · simp only [nat?, Option.map_eq_some_iff] at hn0
        obtain ⟨w, hw, -⟩ := hn0; exact ⟨w, by simpa [Nat.add_assoc] using hw⟩
      · obtain ⟨w, hw, -⟩ := hd?_some hr0; exact ⟨w, by simpa [Nat.add_assoc] using hw⟩
    obtain ⟨w, hw⟩ := hw
    have hw' : erecP m (o.toNat + (11 * j + i)) = some w := by rw [← Nat.add_assoc]; exact hw
    obtain ⟨e1, e2⟩ := erRd_add hw' (by have := erecP_lt64 hw'; omega)
    exact ⟨w, hw, e1, by rw [e2]; omega⟩
  have hfr : ∀ j < cnt.toNat, ∀ i, (i = 0 ∨ i = 1 ∨ i = 8) →
      ErApart run (11 * cnt.toNat) (o + UInt64.ofNat (11 * j + i)) := by
    intro j hj i hi t ht
    obtain ⟨w, hw, -, he⟩ := hword j hj i hi
    exact erFresh ha hS.iw (x := o + UInt64.ofNat (11 * j + i)) (by rw [he]; exact hw) (by rw [hk]; exact ht)
  have hm' := rrW_mem k lo ll po pl n m1 m' run o cnt r h hfr
  subst hm'
  rw [refireWords_congr (m := m) (m' := m1) k lo ll po pl o cnt.toNat (fun _ _ _ _ => hr1 _)]
  obtain ⟨hS1, hg1, -, -, -, -, hget1⟩ := erRec_stage ha hS (refireWords m k lo ll po pl o cnt.toNat)
    (by rw [refireWords_length, hk])
  refine ⟨hS1, hg1, ?_⟩
  generalize hM : wrER m1 run (refireWords m k lo ll po pl o cnt.toNat) = M at hS1 hg1 hget1 ⊢
  have hext := IWGrow.ext hg1
  unfold decRules
  rw [← hlen, ← List.length_map (f := fun rl => { rl with fire := f })]
  apply mapM_range_some
  intro j hj
  simp only [List.length_map] at hj
  rw [hlen] at hj
  have hrj := hget j hj
  rw [List.getElem?_eq_getElem (by omega)] at hrj
  simp only [List.getElem_map]
  have g : ∀ i < 11, erecP M (run.toNat + 11 * j + i) =
      (refireRec m (o + UInt64.ofNat (11 * j)) k lo ll po pl)[i]? := fun i hi => by
    rw [Nat.add_assoc, hget1 (11 * j + i) (by rw [refireWords_length]; omega),
      refireWords_get m k lo ll po pl o cnt.toNat j i hj hi]
  have gw : ∀ i, (i = 0 ∨ i = 1 ∨ i = 8) → erecP M (run.toNat + 11 * j + i) = erecP m (o.toNat + 11 * j + i) := by
    intro i hi
    obtain ⟨w, hw, hrd, -⟩ := hword j hj i hi
    rw [hw]
    have hi11 : i < 11 := by omega
    rw [g i hi11]
    have e : o + UInt64.ofNat (11 * j) + UInt64.ofNat i = o + UInt64.ofNat (11 * j + i) := by
      rw [UInt64.ofNat_add]; ac_rfl
    rcases hi with rfl | rfl | rfl
    · simp only [refireRec, List.getElem?_cons_zero]
      rw [← hrd]; simp
    · simp only [refireRec]
      rw [← hrd, ← e]; rfl
    · simp only [refireRec]
      rw [← hrd, ← e]; rfl
  refine decRule_refireAt hrj (gw 0 (by simp)) (gw 1 (by simp)) (gw 8 (by simp)) (g 3 (by omega)) (g 4 (by omega))
    (g 5 (by omega)) (g 6 (by omega)) (g 7 (by omega)) (hf.ext hext)

end L.Ind

end
