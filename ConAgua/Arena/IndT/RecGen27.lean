import ConAgua.Arena.IndT.RecGen28
import ConAgua.Arena.RecGenSpec27

/-!
# `classCtorOf`, `classCtorsOf`, `classesCtors` under `StageC` (lane `indstaget`, helper `pds`)

`class_ctor_of`'s model (`cxoW`, the callees through the program's `callW`) and the two loops above
it, from `StageC` and the inputs' denotations con-ron's `classCtorOf_spec` asks; its twin side
transcribed from that spec's proof: `targetMajorAt` (`targetMajorAt_spec`), the entries' filter and
the minor slot (state kept), `openPisAtFvarsF` (`openPisAtFvarsF_run`), `classFieldsOf`
(`classFieldsOf_spec`), `classFieldsAgree` (`classFieldsAgree_refinesC`, con-ron's spec on its run),
`targetCtorAt` (`targetCtorAt_spec`, a `CSpec`), `instPisWith` (`instPisWith_spec`), the record (L
only).
-/

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtors dCtorNf dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Frames -/

theorem cnfW_afr : ∀ (k : Nat) (m m' : Mem) (nfo nfl nm q j rp r : Word),
    cnfW k m nfo nfl nm q j rp = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [cnfW] at h
  | k + 1, m, m', nfo, nfl, nm, q, j, rp, r, h => by
    by_cases hj : j < nfl
    · by_cases h1 : rdW (m.arr64 IW) (rdW (m.arr64 IW) (nfo + j)) = nm
      · by_cases h2 : (q + rp).toNat < (m.arr64 IW).size
        · rw [cnfW_hit (h := hj) (h1 := h1) (h2 := h2)] at h
          exact (set64IW_afr _ _ _).trans (cnfW_afr k _ _ _ _ _ _ _ _ _ h)
        · rw [cnfW_oob (h := hj) (h1 := h1) (h2 := h2)] at h; cases h
      · rw [cnfW_miss (h := hj) (h1 := h1)] at h
        exact cnfW_afr k _ _ _ _ _ _ _ _ _ h
    · rw [cnfW_exit (h := hj)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _

theorem cnfF_afr {n : Nat} {m m' : Mem} {nfo nfl nm : Word} {r : List Word}
    (h : cnfF n m nfo nfl nm = some (r, m')) : AFr m m' := by
  simp only [cnfF] at h
  cases hal : allocW m nfl with
  | none => rw [hal] at h; cases h
  | some x =>
  obtain ⟨q, m1⟩ := x
  rw [hal, cnfK1_some] at h
  cases hl : cnfW (n + 1) m1 nfo nfl nm q 0 0 with
  | none => rw [hl] at h; cases h
  | some y =>
  obtain ⟨rp, m2⟩ := y
  rw [hl, cnfK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (allocW_afr hal).trans (cnfW_afr _ _ _ _ _ _ _ _ _ _ hl)

theorem cfgW_afr : ∀ (n : Nat) (m m' : Mem) (mo ml io il i fo fl : Word) (r : List Word),
    cfgW n m mo ml io il i fo fl = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [cfgW] at h
  | n + 1, m, m', mo, ml, io, il, i, fo, fl, r, h => by
    by_cases hl : fl = 0
    · rw [cfgW_nil (h := hl)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [cfgW_cons (h := hl)] at h
    cases h1 : ftdF m [rdW (m.arr64 IW) fo] with
    | none => rw [h1] at h; simp [cfgK1] at h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1, cfgK1_some] at h
    refine (ftdF_afr h1).trans ?_
    cases h2 : noConstWf n m1 mo ml 0 0 (r1.headD 0) with
    | none => rw [h2] at h; simp [cfgK2] at h
    | some x2 =>
    obtain ⟨occ, m2⟩ := x2
    rw [h2, cfgK2_some] at h
    refine (noConstWf_afr h2).trans ?_
    -- after the kind: the record, the rest, the cons
    have tail : ∀ (r5 : List Word) (m5 : Mem), recW m2 1 [0] = some (r5, m5) ∨
        (∃ r4 m4 cls, piBW n m2 CWF (r1.headD 0) = some (r4, m4) ∧ recW m4 3 [1, cls, r4.tail.headD 0] =
          some (r5, m5)) → AFr m2 m5 := by
      rintro r5 m5 (h5 | ⟨r4, m4, cls, h4, h5⟩)
      · exact recW_afr h5
      · exact (piBW_afr _ _ _ _ _ _ h4).trans (recW_afr h5)
    cases h3 : cfhW n m2 io il i with
    | none => rw [h3] at h; simp [cfgK3] at h
    | some hcc =>
    obtain ⟨hc, cls⟩ := hcc
    rw [h3] at h
    have fin : ∀ (o5 : Option (List Word × Mem)), (∀ r5 m5, o5 = some (r5, m5) → AFr m2 m5) →
        cfgK5 n (fun m5 => cfgW n m5 mo ml io il (i + 1) (fo + 1) (fl - 1)) o5 = some (r, m') →
        AFr m2 m' := by
      intro o5 hA5 h5
      cases o5 with
      | none => simp [cfgK5] at h5
      | some x5 =>
      obtain ⟨r5, m5⟩ := x5
      rw [cfgK5_some] at h5
      cases h6 : cfgW n m5 mo ml io il (i + 1) (fo + 1) (fl - 1) with
      | none => rw [h6] at h5; simp [cfgK7] at h5
      | some x6 =>
      obtain ⟨r6, m6⟩ := x6
      rw [h6, cfgK7_some] at h5
      cases h7 : consW n m6 (r5.headD 0) (r6.headD 0) (r6.tail.headD 0) with
      | none => rw [h7] at h5; simp [cfgK6] at h5
      | some x7 =>
      obtain ⟨r7, m7⟩ := x7
      rw [h7, cfgK6_some] at h5
      simp only [Option.some.injEq, Prod.mk.injEq] at h5; rw [← h5.2]
      exact ((hA5 r5 m5 rfl).trans (cfgW_afr n _ _ _ _ _ _ _ _ _ _ h6)).trans (consW_afr h7)
    by_cases c0 : occ = 0 ∧ hc = 0
    · rw [cfgK3_ord (h := c0)] at h
      exact fin _ (fun r5 m5 e => tail r5 m5 (.inl e)) h
    by_cases c1 : occ ≠ 0 ∧ hc = 1
    · rw [cfgK3_rec (h0 := c0) (h := c1)] at h
      cases h4 : piBW n m2 CWF (r1.headD 0) with
      | none => rw [h4] at h; simp [cfgK4] at h
      | some x4 =>
      obtain ⟨r4, m4⟩ := x4
      rw [h4, cfgK4_some] at h
      exact fin _ (fun r5 m5 e => tail r5 m5 (.inr ⟨r4, m4, cls, h4, e⟩)) h
    · rw [cfgK3_bad (h0 := c0) (h := c1)] at h; cases h

theorem cfoW_afr {n : Nat} {m m' : Mem} {q io il i fo fl : Word} {r : List Word}
    (h : cfoW n m q io il i fo fl = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [cfoW] at h
  | succ n =>
  rw [cfoW_eq] at h
  cases h1 : memberNamesW n m q with
  | none => rw [h1] at h; simp [cfoK] at h
  | some x =>
  obtain ⟨r1, m1⟩ := x
  rw [h1, cfoK_some] at h
  cases h2 : cfgW n m1 (r1.headD 0) (r1.tail.headD 0) io il i fo fl with
  | none => rw [h2] at h; simp [cfgK6] at h
  | some y =>
  obtain ⟨r2, m2⟩ := y
  rw [h2, cfgK6_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
  exact (memberNamesW_afr h1).trans (cfgW_afr _ _ _ _ _ _ _ _ _ _ _ h2)

theorem tcW_afr {n : Nat} {m m' : Mem} {M c : Word} {r : List Word} (h : tcW n m M c = some (r, m')) :
    AFr m m' := by
  simp only [tcW] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
  cases h1 : cvLpsW n m c with
  | none => rw [h1] at h; simp [tcK1] at h
  | some x =>
  obtain ⟨r1, m1⟩ := x
  rw [h1] at h
  simp only [tcK1] at h
  refine (erToIwW_afr h1).trans ?_
  cases h2 : stubM "inst_lp_fast" m1 [CWF, r1.headD 0, r1.tail.headD 0, rdW (m.arr64 IW) (M + 1),
      rdW (m1.arr64 EREC) (c + 3)] with
  | none => rw [h2] at h; simp [tcK2] at h
  | some y =>
  obtain ⟨r2, m2⟩ := y
  rw [h2] at h
  simp only [tcK2, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]; exact stub_afr h2

end L.Ind
