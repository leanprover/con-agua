module

public import ConAgua.Arena.IndSumSpec.SumRules
public import ConAgua.Arena.IndSumSpec.TblProg
public import ConAgua.Arena.RecCheckSpec.TsrLook
import ConAgua.Arena.IndPosSpec.FgW
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndSim
import ConAgua.Arena.RecClassSpec.Classes
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import all ConAgua.Arena.RecCheck
import all ConAgua.Arena.IndSum
import ConAgua.L.WordOff

@[expose] public section

/-!
# TsrW

`efgW_mem`, `sumHslice_of_get`, `efW_stage`, `efgW_afr`, `efW_afr`, `nat?_shift` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The model of `er_from_iw(o, l)`** at exec fuel `n`. -/
l_model efF_spec (p : Prog) (hL : TsrLook p) (hpu : p.lookup "erec_put" = some erecPut)
  fns [hL.ef ↦ efF list]
  specs [erecAlloc_specW p hL.ea n, efgW_spec p hpu hL.efg n]
  grind [arena_grind]

/-- The copy loop writes the slice's words. -/
theorem efgW_mem (n : Nat) : ∀ (m m' : Mem) (q o l : Word) (r ws : List Word),
    efgW n m q o l = some (r, m') → SlR m o l ws → m' = wrER m q ws := by
  induction n with
  | zero => intro m m' q o l r ws h; simp [efgW] at h
  | succ n ih =>
  intro m m' q o l r ws h hs
  cases hs with
  | nil =>
    rw [efgW.arm1 n m q o 0 rfl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; rfl
  | cons hl hs' =>
    rw [efgW.arm2 n m q o l hl] at h
    rcases h2 : efgW n (erecPutMem m q (rdW (m.arr64 IW) o)) (q + 1) (o + 1) (l - 1) with _ | ⟨r2, m2⟩ <;>
      rw [h2] at h
    · cases h
    simp only [efgW.k_er_from_iw_go, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    simp only [wrER]
    exact ih _ _ _ _ _ _ _ h2 (hs'.congr (erecPutMem_iw m q _))

/-- Handle words at `q, q + 1, …` of a reader decode as the handle list. -/
theorem hsliceR_of_get {k : IdxKind} {R : Nat → Option Word} : ∀ (ws : List Word) (q : Nat),
    (∀ j < ws.length, R (q + j) = ws[j]?) → (∀ w ∈ ws, w.toNat < 2 ^ 32) →
    (hslice? R q ws.length : Option (List (Idx k))) = some (ws.map decI)
  | [], q, _, _ => by simp [hslice?]
  | w :: ws, q, h, hw => by
    simp only [List.length_cons, hslice?_succ, List.map_cons]
    have h0 : R q = some w := by simpa using h 0 (by simp)
    have ih := hsliceR_of_get (k := k) ws (q + 1) (fun j hj => by
      have := h (j + 1) (by simpa using hj); rw [show q + 1 + j = q + (j + 1) by omega]; simpa using this)
      (fun v hv => hw v (by simp [hv]))
    have hw0 : w.toNat < 2 ^ 32 := hw w (by simp)
    simp [hd?, h0, hw0, ih]

/-- Handle words at `q, q + 1, …` decode as the handle list. -/
theorem sumHslice_of_get {k : IdxKind} {a : Array Word} : ∀ (ws : List Word) (q : Nat),
    (∀ j < ws.length, a[q + j]? = ws[j]?) → (∀ w ∈ ws, H w) →
    (hslice? (aread a) q ws.length : Option (List (Idx k))) = some (ws.map decI)
  | [], q, _, _ => by simp [hslice?]
  | w :: ws, q, h, hw => by
    simp only [List.length_cons, hslice?_succ, List.map_cons]
    have h0 : a[q]? = some w := by simpa using h 0 (by simp)
    have ih := sumHslice_of_get (k := k) ws (q + 1) (fun j hj => by
      have := h (j + 1) (by simpa using hj); rw [show q + 1 + j = q + (j + 1) by omega]; simpa using this)
      (fun v hv => hw v (by simp [hv]))
    have hw0 : H w := hw w (by simp)
    simp [hd?, aread_apply, h0, hw0, ih]

/-- **`er_from_iw` under the stage relation**: a fresh `EREC` slice holding the `IW` handle list,
decoded in the record pool. -/
theorem efW_stage {vis : Word} {fe : IFEnv} {a : AState} (n : Nat)
    {m m' : Mem} {o l : Word} {r : List Word} {kk : IdxKind} {xs : List (Idx kk)}
    (h : efF (n + 1) m o l = some (r, m'))
    (hS : StageR vis fe m a) (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ r.tail.headD 0 = l ∧
      hslice? (erecP m') (r.headD 0).toNat l.toNat = some xs := by
  rw [efF.arm1] at h
  rcases ha : erAllocW m l with _ | ⟨q, m1⟩ <;>
    simp only [ha, efF.k_erec_alloc.none, efF.k_erec_alloc.arm1, reduceCtorEq] at h
  rcases h2 : efgW n m1 q o l with _ | ⟨r2, m2⟩ <;>
    simp only [h2, efF.k_er_from_iw_go.none, efF.k_er_from_iw_go.arm1, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨ws, hws, rfl, hw32⟩ := slR_of_decHL m l.toNat o.toNat xs hd
    (by have := hS.lt64 (x := iwTop m) (Nat.le_refl _); omega)
  simp only [UInt64.ofNat_toNat] at hws
  obtain ⟨-, hf1, -⟩ := erAllocW_spec ha hS.iw
  have hI1 : m1.arr64 IW = m.arr64 IW := hf1.arr IW (by simp) (by decide)
  rw [efgW_mem n m1 m2 q o l r2 ws h2 (hws.congr hI1)]
  have hlen := hws.length
  obtain ⟨hS1, hg1, -, -, -, -, hget⟩ := erRec_stage ha hS ws hlen.symm
  refine ⟨hS1, hg1, rfl, ?_⟩
  simp only [List.headD_cons]
  rw [← hlen]
  exact hsliceR_of_get ws q.toNat hget hw32

/-! ## The walk memos across the table's steps -/

theorem efgW_afr : ∀ (n : Nat) (m m' : Mem) (q o l : Word) (r : List Word),
    efgW n m q o l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [efgW] at h
  | n + 1, m, m', q, o, l, r, h => by
    simp only [efgW, efgW.k_er_from_iw_go.eq_def] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    · refine AFr.trans (AFr.of_frame (erecPutMem_frame m q (rdW (m.arr64 IW) o))) ?_
      afr_auto h [efgW_afr n _ _ _ _ _ _]

theorem efW_afr {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : efF (n + 1) m o l = some (r, m')) :
    AFr m m' := by
  simp only [efF, efF.k_erec_alloc.eq_def, efF.k_er_from_iw_go.eq_def] at h
  afr_auto h [erAllocW_afr, efgW_afr _ _ _ _ _ _ _]

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Rule records at another address -/

/-- The plain fields of a decoded rule record. -/
theorem decRule_fields {R : Nat → Option Word} {q : Nat} {rl : IRecRule} (h : decRule R q = some rl) :
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

/-- A rule record whose plain fields (words `0`, `1`, `8`) are copied and whose fire is a NESTED one
at slices the new reader decodes. -/
theorem decRule_nested {R R' : Nat → Option Word} {q q' : Nat} {rl : IRecRule} {lo ll po pl : Word}
    {lvls : List LIdx} {pins : List EIdx} (h : decRule R q = some rl)
    (h0 : R' q' = R q) (h1 : R' (q' + 1) = R (q + 1)) (h8 : R' (q' + 8) = R (q + 8))
    (h3 : R' (q' + 3) = some 1) (h4 : R' (q' + 4) = some lo) (h5 : R' (q' + 5) = some ll)
    (h6 : R' (q' + 6) = some po) (h7 : R' (q' + 7) = some pl)
    (hl : hslice? R' lo.toNat ll.toNat = some lvls) (hp : hslice? R' po.toNat pl.toNat = some pins) :
    decRule R' q' = some { rl with fire := .nested lvls pins } := by
  obtain ⟨hc, hn, hr⟩ := decRule_fields h
  have hc' : hd? R' q' = some rl.ctor := by rw [← hc]; simp only [hd?, h0]
  have hn' : nat? R' (q' + 1) = some rl.nfields := by rw [← hn]; simp only [nat?, h1]
  have hr' : hd? R' (q' + 8) = some rl.rhs := by rw [← hr]; simp only [hd?, h8]
  have hl' : hlist? R' (q' + 4) = some lvls := by
    simp only [hlist?, nat?, h4, show q' + 4 + 1 = q' + 5 by omega, h5, Option.map_some,
      Option.bind_eq_bind, Option.bind_some, hl]
  have hp' : hlist? R' (q' + 6) = some pins := by
    simp only [hlist?, nat?, h6, show q' + 6 + 1 = q' + 7 by omega, h7, Option.map_some,
      Option.bind_eq_bind, Option.bind_some, hp]
  have hk : nat? R' (q' + 3) = some 1 := by simp [nat?, h3]
  unfold decRule
  simp only [hk, Option.bind_eq_bind, Option.bind_some, hl', hp', hc', hn', hr', Option.pure_def]

/-! ## `generated_rules_remap` -/

/-- The memory after one rebuilt record's eleven `erec_put`s (each copy reads the memory of its time). -/
def rmMem (m1 : Mem) (q old flo fll fpo fpl : Word) : Mem :=
  let m2 := erecPutMem m1 q (erRd m1 old)
  let m3 := erecPutMem m2 (q + 1) (erRd m2 (old + 1))
  let m9 := erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem m3 (q + 2) 0)
    (q + 3) 1) (q + 4) flo) (q + 5) fll) (q + 6) fpo) (q + 7) fpl
  let m10 := erecPutMem m9 (q + 8) (erRd m9 (old + 8))
  erecPutMem (erecPutMem m10 (q + 9) 0) (q + 10) 0

/-- **The model of `generated_rule_nested`.** -/
l_model trn_spec (p : Prog) (hL : TsrLook p) (hpu : p.lookup "erec_put" = some erecPut)
  fns [hL.trn ↦ trnW list]
  specs [erecAlloc_specW p hL.ea n, erecPut_specM p hpu n]
  grind [arena_grind]

/-- `trnW` by its memory `rmMem`. -/
theorem trnW_eq (m : Mem) (old flo fll fpo fpl : Word) : trnW m old flo fll fpo fpl =
    match erAllocW m 11 with
    | none => none
    | some (q, m1) => some ([q], rmMem m1 q old flo fll fpo fpl) := by
  rw [trnW.arm1]; rcases erAllocW m 11 with _ | ⟨q, m1⟩ <;> rfl

l_model tsrm_spec (p : Prog) (hL : TsrLook p) (hpu : p.lookup "erec_put" = some erecPut)
  fns [hL.tsrm ↦ tsrmW]
  specs [trn_spec p hL hpu n, slCons_specW p hL.rc.rx.ha hL.ic hL.sc n]
  grind [arena_grind]

/-! ## The rebuilt record under the stage relation -/

/-- `x` is at none of the `k` places `q, q + 1, …` (the tagged addresses `erec_put` writes). -/
def ErApart (q : Word) (k : Nat) (x : Word) : Prop :=
  ∀ j < k, erTier x ≠ erTier (q + UInt64.ofNat j) ∨ erOff x ≠ erOff (q + UInt64.ofNat j)

theorem ErApart.mono {q x : Word} {k k' : Nat} (h : ErApart q k x) (hk : k' ≤ k) : ErApart q k' x :=
  fun j hj => h j (by omega)


theorem rmMem_eq {m1 : Mem} {q old flo fll fpo fpl : Word}
    (hfr : ∀ x ∈ [old, old + 1, old + 8], ErApart q 11 x) :
    rmMem m1 q old flo fll fpo fpl = wrER m1 q [erRd m1 old, erRd m1 (old + 1), 0, 1, flo, fll, fpo, fpl,
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
  simp only [rmMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl, show q + 6 + 1 = q + 7 by ac_rfl,
    show q + 7 + 1 = q + 8 by ac_rfl, show q + 8 + 1 = q + 9 by ac_rfl,
    show q + 9 + 1 = q + 10 by ac_rfl]
  simp (disch := first
    | exact f0 _ (by simp) | exact f1 _ (by simp) | exact f2 _ (by simp) | exact f3 _ (by simp)
    | exact f4 _ (by simp) | exact f5 _ (by simp) | exact f6 _ (by simp) | exact f7 _ (by simp))
    only [erRd_erecPutMem_ne]

theorem rmMem_frame (m : Mem) (q old flo fll fpo fpl : Word) :
    MemFrame [EREC, tier1 EREC] [] m (rmMem m q old flo fll fpo fpl) := by
  simp only [rmMem]
  repeat' refine MemFrame.trans ?_ (erecPutMem_frame _ _ _)
  exact MemFrame.refl _ _ _

/-- **One rebuilt rule record under the stage relation**: a fresh 11-word record, the old record's
plain fields, the NESTED fire at the given record-pool slices; all eleven words in the pool. -/
theorem rmRec_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m1 : Mem} {q old flo fll fpo fpl : Word} {rl : IRecRule} {lvls : List LIdx} {pins : List EIdx}
    (h : erAllocW m 11 = some (q, m1)) (hS : StageR vis fe m a) (hold : rlDec m old.toNat = some rl)
    (hl : hslice? (erecP m) flo.toNat fll.toNat = some lvls)
    (hp : hslice? (erecP m) fpo.toNat fpl.toNat = some pins) :
    StageR vis fe (rmMem m1 q old flo fll fpo fpl) a ∧ IWGrow m (rmMem m1 q old flo fll fpo fpl) ∧
      rlDec (rmMem m1 q old flo fll fpo fpl) q.toNat = some { rl with fire := .nested lvls pins } ∧
      ∀ i < 11, ∃ w, erecP (rmMem m1 q old flo fll fpo fpl) (q.toNat + i) = some w := by
  obtain ⟨hc, hn, hr⟩ := decRule_fields hold
  obtain ⟨w0, hw0, -, -⟩ := hd?_some hc
  obtain ⟨w1, hw1, -⟩ : ∃ w, erecP m (old.toNat + 1) = some w ∧ w.toNat = rl.nfields := by
    simp only [nat?, Option.map_eq_some_iff] at hn; exact hn
  obtain ⟨w8, hw8, -, -⟩ := hd?_some hr
  have r0 : erRd m old = w0 := (erRd_of_erecP hw0).1
  obtain ⟨r1, e1⟩ := erRd_add (j := 1) (cq := old) (m := m) hw1 (by decide)
  obtain ⟨r8, e8⟩ := erRd_add (j := 8) (cq := old) (m := m) hw8 (by decide)
  simp only [show (UInt64.ofNat 1 : Word) = 1 from rfl, show (UInt64.ofNat 8 : Word) = 8 from rfl]
    at r1 r8 e1 e8
  have hfr : ∀ x ∈ [old, old + 1, old + 8], ErApart q 11 x := by
    intro x hx j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact erFresh h hS.iw hw0 hj
    · exact erFresh h hS.iw (by rw [e1]; exact hw1) hj
    · exact erFresh h hS.iw (by rw [e8]; exact hw8) hj
  obtain ⟨-, hf1, -⟩ := erAllocW_spec h hS.iw
  have hr1 : ∀ x, erRd m1 x = erRd m x := fun x => by
    unfold erRd; rw [hf1.arr _ (by simp) (by rw [tierA_EREC]; split <;> decide)]
  rw [rmMem_eq hfr, hr1, hr1, hr1, r0, r1, r8]
  obtain ⟨hS', hg, -, -, -, -, hget⟩ :=
    erRec_stage h hS [w0, w1, 0, 1, flo, fll, fpo, fpl, w8, 0, 0] (by simp)
  have g : ∀ i (hi : i < 11), erecP (wrER m1 q [w0, w1, 0, 1, flo, fll, fpo, fpl, w8, 0, 0]) (q.toNat + i) =
      [w0, w1, 0, 1, flo, fll, fpo, fpl, w8, 0, 0][i]? := fun i hi => hget i (by simpa using hi)
  refine ⟨hS', hg, ?_, fun i hi => ⟨_, (g i hi).trans (List.getElem?_eq_getElem (by simpa using hi))⟩⟩
  have hext := IWGrow.ext hg
  refine decRule_nested hold (lo := flo) (ll := fll) (po := fpo) (pl := fpl)
    (by have := g 0 (by decide); simp only [Nat.add_zero] at this; rw [this, hw0]; rfl)
    (by rw [g 1 (by decide), hw1]; rfl) (by rw [g 8 (by decide), hw8]; rfl)
    (g 3 (by decide)) (g 4 (by decide)) (g 5 (by decide)) (g 6 (by decide)) (g 7 (by decide))
    (hext.hslice? hl) (hext.hslice? hp)

/-! ## `RuleWordsIn` of pointer slices -/

theorem decNL_get' {m : Mem} {o l : Nat} {xs : List Nat} (h : decNL m o l = some xs) :
    ∀ j < l, ∃ v, iwN m (o + j) = some v ∧ xs[j]? = some v := by
  have hp : decPL m some o l = some xs := by
    rw [decPL_eq_bind, h]
    simp only [Option.bind_some]
    clear h
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [List.mapM_cons, ih]
  intro j hj
  obtain ⟨v, y, hv, hy, hx⟩ := decPL_get l o xs hp j hj
  cases hy
  exact ⟨v, hv, hx⟩

theorem rec11_of_decNL {m : Mem} {o l : Nat} {ys : List Nat} (h : decNL m o l = some ys)
    (hall : ∀ v ∈ ys, ∀ i < 11, ∃ w, erecP m (v + i) = some w) : RuleWordsIn m o l := by
  intro j hj v hv i hi
  obtain ⟨v', hv', hx⟩ := decNL_get' h j hj
  rw [hv] at hv'; cases hv'
  exact hall v (List.mem_of_getElem? hx) i hi

theorem rec11_mem {m : Mem} {o l : Nat} {ys : List Nat} (h : decNL m o l = some ys) (hR : RuleWordsIn m o l) :
    ∀ v ∈ ys, ∀ i < 11, ∃ w, erecP m (v + i) = some w := by
  intro v hv i hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hl := decNL_length m h
  obtain ⟨v', hv', hx⟩ := decNL_get' h j (by omega)
  rw [List.getElem?_eq_getElem hj] at hx
  have e := Option.some.inj hx
  rw [e]
  exact hR j (by omega) _ hv' i hi


/-- A rule pointer consed onto a rule-pointer slice (`sl_cons`). -/
theorem consW_rl {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {rules : List IRecRule} {rl : IRecRule}
    (h : consW n m x o l = some (r, m')) (hS : StageR vis fe m a) (hb : o.toNat + l.toNat ≤ iwTop m)
    (hd : decPL m (rlDec m) o.toNat l.toNat = some rules) (hx : rlDec m x.toNat = some rl) :
    decPL m' (rlDec m') (r.headD 0).toNat (r.tail.headD 0).toNat = some (rl :: rules) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' ∧ StageR vis fe m' a ∧ IWGrow m m' ∧
      MFr [] [] m m' := by
  rw [decPL_eq_bind] at hd
  rcases hps : decNL m o.toNat l.toNat with _ | ps <;> rw [hps] at hd
  · cases hd
  simp only [Option.bind_some] at hd
  obtain ⟨hS', hg, hd', ht'⟩ := consW_stageN h hS hb hps
  have hext := IWGrow.ext hg
  refine ⟨?_, ht', hS', hg, consW_mfr h⟩
  rw [decPL_eq_bind, hd']
  simp only [Option.bind_some, List.mapM_cons]
  rw [show rlDec m' x.toNat = some rl from hext.decRule hx,
    ArrExt.mapM (f := rlDec m) (g := rlDec m') (fun _ _ hy => hext.decRule hy) _ _ hd]
  rfl

theorem decPL_rl_grow {m m' : Mem} (hg : IWGrow m m') {o l : Nat} {rules : List IRecRule}
    (hb : o + l ≤ iwTop m) (hd : decPL m (rlDec m) o l = some rules) : decPL m' (rlDec m') o l = some rules := by
  rw [decPL_eq_bind] at hd ⊢
  rcases hps : decNL m o l with _ | ps <;> rw [hps] at hd
  · cases hd
  have hps' : decNL m' o l = some ps := by
    rw [← hps]; simp only [decNL]; apply L.Ind.mapM_congr_of; intro j hj
    simp only [iwN, nat?, iwA, aread_apply, aread_apply]; rw [hg.iwGet _ (by simp at hj; omega)]
  rw [hps']
  simp only [Option.bind_some] at hd ⊢
  exact ArrExt.mapM (fun _ _ hy => (IWGrow.ext hg).decRule hy) _ _ hd

section rel
variable (fe : IFEnv) (vis : Word) (a : AState)

theorem tsrmW_ok (n : Nat) : ∀ {m m' : Mem} {ro rl flo fll fpo fpl : Word} {r : List Word}
    {rules : List IRecRule} {lvls : List LIdx} {pins : List EIdx},
    tsrmW n m ro rl flo fll fpo fpl = some (r, m') → StageR vis fe m a →
    decPL m (rlDec m) ro.toNat rl.toNat = some rules → ro.toNat + rl.toNat ≤ iwTop m →
    hslice? (erecP m) flo.toNat fll.toNat = some lvls → hslice? (erecP m) fpo.toNat fpl.toNat = some pins →
    decPL m' (rlDec m') (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (rules.map fun rl => { rl with fire := .nested lvls pins }) ∧
      RuleWordsIn m' (r.headD 0).toNat (r.tail.headD 0).toNat ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a ∧ IWGrow m m' := by
  induction n with
  | zero => intro m m' ro rl flo fll fpo fpl r rules lvls pins h; simp [tsrmW] at h
  | succ n ih =>
  intro m m' ro rl flo fll fpo fpl r rules lvls pins h hS hd hb hl hp
  by_cases h0 : rl = 0
  · rw [tsrmW.arm1 (hc1 := h0)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst h0
    have : rules = [] := by have := decPL_length _ hd; simpa using this
    subst this
    exact ⟨by simp [decPL], fun j hj => by simp at hj, by simp, hS, IWGrow.refl _⟩
  have hb64 := hS.lt64 hb
  obtain ⟨eo, el, hl0⟩ := slice_step h0 hb64
  obtain ⟨l', hl'⟩ : ∃ l', rl.toNat = l' + 1 := ⟨rl.toNat - 1, by omega⟩
  rw [hl'] at hd
  obtain ⟨pp, rl0, rest, rfl, hpp, hrl0, hrest⟩ := decPL_cons hd
  have hrd := iwN_rdW hpp (by omega)
  rw [UInt64.ofNat_toNat] at hrd
  rw [tsrmW.arm2 (hc1 := h0)] at h
  cases ha : erAllocW m 11 with
  | none =>
    rw [show trnW m (rdW (m.arr64 IW) ro) flo fll fpo fpl = none by simp [trnW_eq, ha],
      tsrmW.k_generated_rule_nested.none] at h; cases h
  | some x =>
  obtain ⟨q, m1⟩ := x
  rw [show trnW m (rdW (m.arr64 IW) ro) flo fll fpo fpl = some ([q], rmMem m1 q (rdW (m.arr64 IW) ro) flo fll fpo fpl)
    by simp [trnW_eq, ha], tsrmW.k_generated_rule_nested.arm1] at h
  simp only [List.headD_cons] at h
  rw [hrd.1] at h
  have hold : rlDec m (UInt64.ofNat pp : Word).toNat = some rl0 := by
    rw [UInt64.toNat_ofNat_of_lt' hrd.2]; exact hrl0
  obtain ⟨hS1, hg1, hq1, hw1⟩ := rmRec_stage ha hS hold hl hp
  generalize hM : rmMem m1 q (UInt64.ofNat pp) flo fll fpo fpl = M at h hS1 hg1 hq1 hw1
  rcases h2 : tsrmW n M (ro + 1) (rl - 1) flo fll fpo fpl with _ | ⟨rr, m2⟩ <;>
    simp only [h2, tsrmW.k_generated_rules_remap, reduceCtorEq] at h
  have hext := IWGrow.ext hg1
  obtain ⟨hd2, hR2, hb2, hS2, hg2⟩ := ih h2 hS1
    (decPL_rl_grow hg1 (by rw [eo, el]; omega) (by rw [eo, el, hl']; simpa using hrest))
    (by rw [eo, el]; have := hg1.iw; omega) (hext.hslice? hl) (hext.hslice? hp)
  rcases h3 : consW n m2 q (rr.headD 0) (rr.tail.headD 0) with _ | ⟨rc, m3⟩ <;>
    simp only [h3, tsrmW.k_sl_cons, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hd3, ht3, hS3, hg3, -⟩ := consW_rl h3 hS2 hb2 hd2 ((IWGrow.ext hg2).decRule hq1)
  rw [decPL_eq_bind] at hd2
  rcases hps : decNL m2 (rr.headD 0).toNat (rr.tail.headD 0).toNat with _ | ps <;> rw [hps] at hd2
  · cases hd2
  obtain ⟨-, -, hn3, -⟩ := consW_stageN h3 hS2 hb2 hps
  have hR3 : RuleWordsIn m3 (rc.headD 0).toNat (rc.tail.headD 0).toNat := by
    refine rec11_of_decNL hn3 fun v hv i hi => ?_
    rcases List.mem_cons.mp hv with rfl | hv
    · obtain ⟨w, hw⟩ := hw1 i hi
      exact ⟨w, IWGrow.ext (hg2.trans hg3) _ _ hw⟩
    · obtain ⟨w, hw⟩ := rec11_mem hps hR2 v hv i hi
      exact ⟨w, IWGrow.ext hg3 _ _ hw⟩
  exact ⟨by simpa using hd3, hR3, Nat.le_of_eq ht3, hS3, (hg1.trans hg2).trans hg3⟩

end rel

/-! ## The `abstract1` memo across the rules' writers -/

theorem ruleMem_afr (m : Mem) (q nm nF rO : Word) : AFr m (ruleMem m q nm nF rO) := by
  rw [ruleMem_eq]; exact wrER_afr _ m q

theorem rgoW_afr : ∀ (n : Nat) (m m' : Mem) (cO cL rO rL o : Word) (r : List Word),
    rgoW n m cO cL rO rL o = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, h => by simp [rgoW] at h
  | n + 1, m, m', cO, cL, rO, rL, o, r, h => by
    by_cases hz : cL = 0 ∨ rL = 0
    · rw [rgoW.arm1 (hc1 := hz)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    · rw [rgoW.arm2 (hc1 := hz)] at h
      rcases h2 : erAllocW m 11 with _ | ⟨q, m2⟩ <;>
        simp only [h2, rgoW.k_erec_alloc.none, rgoW.k_erec_alloc_some, reduceCtorEq] at h
      cases h3 : rgoW n ((ruleMem m2 q _ _ rO).set64 IW o q) (cO + 1) (cL - 1) (rO + 1) (rL - 1) (o + 1) with
      | none => rw [h3, rgoW.k_sum_rules_go.none] at h; cases h
      | some z =>
      obtain ⟨r3, m3⟩ := z
      rw [h3, rgoW.k_sum_rules_go.arm1] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      exact (erAllocW_afr h2).trans
        (((ruleMem_afr _ _ _ _ _).trans (set64IW_afr _ _ _)).trans (rgoW_afr n _ _ _ _ _ _ _ _ h3))

theorem rulesW_afr {n : Nat} {m m' : Mem} {cO cL rO rL : Word} {r : List Word}
    (h : rulesW (n + 1) m cO cL rO rL = some (r, m')) : AFr m m' := by
  rw [rulesW_succ] at h
  generalize hk : (if rL < cL then rL else cL) = k at h
  rcases h1 : allocW m k with _ | ⟨o, m1⟩ <;> simp only [h1, rulesW.k_iw_alloc.none, rulesW.k_iw_alloc.arm1, reduceCtorEq] at h
  rcases h2 : rgoW n m1 cO cL rO rL o with _ | ⟨r2, m2⟩ <;> simp only [h2, rulesW.k_sum_rules_go.none, rulesW.k_sum_rules_go.arm1, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (allocW_afr h1).trans (rgoW_afr n _ _ _ _ _ _ _ _ h2)

theorem tsrmW_afr : ∀ (n : Nat) {m m' : Mem} {ro rl flo fll fpo fpl : Word} {r : List Word},
    tsrmW n m ro rl flo fll fpo fpl = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [tsrmW] at h
  | n + 1, m, m', ro, rl, flo, fll, fpo, fpl, r, h => by
    by_cases h0 : rl = 0
    · rw [tsrmW.arm1 (hc1 := h0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [tsrmW.arm2 (hc1 := h0)] at h
    cases ha : erAllocW m 11 with
    | none =>
      rw [show trnW m (rdW (m.arr64 IW) ro) flo fll fpo fpl = none by simp [trnW_eq, ha],
        tsrmW.k_generated_rule_nested.none] at h; cases h
    | some x =>
    obtain ⟨q, m1⟩ := x
    rw [show trnW m (rdW (m.arr64 IW) ro) flo fll fpo fpl =
      some ([q], rmMem m1 q (rdW (m.arr64 IW) ro) flo fll fpo fpl) by simp [trnW_eq, ha],
      tsrmW.k_generated_rule_nested.arm1] at h
    have f1 : AFr m1 (rmMem m1 q (rdW (m.arr64 IW) ro) flo fll fpo fpl) := AFr.of_frame (rmMem_frame _ _ _ _ _ _ _)
    generalize rmMem m1 q (rdW (m.arr64 IW) ro) flo fll fpo fpl = M at h f1
    cases h2 : tsrmW n M (ro + 1) (rl - 1) flo fll fpo fpl with
    | none => simp only [List.headD_cons, h2] at h; simp [tsrmW.k_generated_rules_remap] at h
    | some x =>
    obtain ⟨rr, m2⟩ := x
    simp only [List.headD_cons, h2, tsrmW.k_generated_rules_remap.arm1] at h
    rcases h3 : consW n m2 q (rr.headD 0) (rr.tail.headD 0) with _ | ⟨rc, m3⟩ <;>
      simp only [h3, tsrmW.k_sl_cons, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact (erAllocW_afr ha).trans (f1.trans ((tsrmW_afr n h2).trans (consW_afr h3)))

/-! ## `generated_rules` -/

theorem poolSmall_of_stage {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    (h : StageR vis fe m a) : PoolSmall m := by
  have := h.check.arena.base.lit.1.cap
  unfold PoolSmall; omega

l_model tsr_spec (p : Prog) (hL : TsrLook p) (hpu : p.lookup "erec_put" = some erecPut)
  fns [hL.tsr ↦ tsrW]
  specs [rulesW_spec p hL.ea hpu hL.srg hL.rc.rx.ha hL.sr n, auxRuleFire_spec p hL.arf n, efF_spec p hL hpu n, tsrm_spec p hL hpu n]
  grind [arena_grind]

/-- A pointer-slice field `(off, len)` of a record decoded in the cut pools, at its word addresses. -/
theorem truncPl {α : Type} {f : Mem → Nat → Option α} {m : Mem} {w : Word} {i o l : Nat} {xs : List α}
    (ho : iwN (truncM m) (w.toNat + i) = some o) (hl : iwN (truncM m) (w.toNat + i + 1) = some l)
    (hd : decPL (truncM m) (f (truncM m)) o l = some xs) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    DecB (fun m' => decPL m' (f m') (rdW (m.arr64 IW) (w + UInt64.ofNat i)).toNat
      (rdW (m.arr64 IW) (w + UInt64.ofNat (i + 1))).toNat) m xs := by
  obtain ⟨-, hom⟩ := L.Ind.iwN_truncM_some ho
  obtain ⟨-, hlm⟩ := L.Ind.iwN_truncM_some hl
  obtain ⟨eo, to⟩ := rec2RdN (w := w) (k := i) hom hsz
  obtain ⟨el, tl⟩ := rec2RdN (w := w) (k := i + 1) (by simpa [Nat.add_assoc] using hlm) hsz
  show decPL (truncM m) (f (truncM m)) _ _ = some xs
  rw [eo, el, to, tl]; exact hd

section rel2
variable (fe : IFEnv) (vis : Word)

/-- **`generated_rules` refines `generatedRules`**: the rules at the returned slice, every record's
eleven words in the pool. -/
theorem tsrW_ok (n : Nat) {m m' : Mem} {a : AState} {rP M rhso rhsl : Word} {r : List Word}
    {TM : TargetMajor} {rhss : List EIdx}
    (h : tsrW n m rP M rhso rhsl = some (r, m')) (hS : StageR vis fe m a)
    (hM : DecB (fun m => decTM m M.toNat) m TM) (hrh : DecB (fun m => decHL m rhso.toNat rhsl.toNat) m rhss)
    (hA : AbsOK m) :
    ∃ rules a', (ConRon.Arena.generatedRules rP.toNat TM rhss).run a = .ok (rules, a') ∧
      decPL m' (rlDec m') (r.headD 0).toNat (r.tail.headD 0).toNat = some rules ∧
      RuleWordsIn m' (r.headD 0).toNat (r.tail.headD 0).toNat ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧
      AbsOK m' := by
  obtain _ | n := n
  · simp [tsrW] at h
  simp only [tsrW] at h
  have hsz := hS.iw.iwSize
  have hM0 : decTM (truncM m) M.toNat = some TM := hM
  -- the constructors' slice, the member word
  have hT := hM0
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hT
  obtain ⟨i0, -, l0, -, ds0, -, nP, -, nI, -, cs, hcs, k8, hk8, nfs0, -, pf0, -, hTM⟩ := hT
  have eCs : TM.ctors = cs := by rw [← hTM]
  have eMem : TM.member = decON k8 := by rw [← hTM]
  obtain ⟨co, cl, hco, hcl, hcsd⟩ := decAt_some hcs
  have hctors := truncPl (f := fun m => decCN m) (w := M) (i := 6) hco (by simpa [Nat.add_assoc] using hcl) hcsd hsz
  simp only [show UInt64.ofNat 6 = (6 : Word) from rfl, show UInt64.ofNat (6 + 1) = (7 : Word) from rfl] at hctors
  obtain ⟨hM8, hk8m⟩ := L.Ind.iwN_truncM_some hk8
  obtain ⟨e8, t8⟩ := rec2RdN (w := M) (k := 8) hk8m hsz
  simp only [show UInt64.ofNat 8 = (8 : Word) from rfl] at e8
  cases n with
  | zero => simp [rulesW, tsrW.k_sum_rules] at h
  | succ k =>
  cases h1 : rulesW (k + 1) m (rdW (m.arr64 IW) (M + 6)) (rdW (m.arr64 IW) (M + 7)) rhso rhsl with
  | none => rw [h1] at h; simp [tsrW.k_sum_rules] at h
  | some x =>
  obtain ⟨rs, m1⟩ := x
  rw [h1] at h
  obtain ⟨hS1, hg1, hd1, hR1, hb1⟩ := rulesW_ok k m _ _ rhso rhsl _ rhss rs m1 h1 hS hctors hrh
  have hA1 := rulesW_afr h1 hA
  have e8' : rdW (m1.arr64 IW) (M + 8) = UInt64.ofNat k8 := by
    rw [rdW_iw_grow hg1 (by rw [UInt64.toNat_add]; simp; omega), e8]
  by_cases hmem : rdW (m1.arr64 IW) (M + 8) ≠ 0
  · rw [tsrW.k_sum_rules.arm1 (hc1 := hmem)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hk0 : k8 ≠ 0 := by intro e; apply hmem; rw [e8', e]; rfl
    refine ⟨_, a, ?_, by simpa using hd1, by simpa using hR1, by simpa using hb1, hS1, hg1, hA1⟩
    simp only [ConRon.Arena.generatedRules, eCs, eMem, decON, hk0, ite_false]
    rfl
  rw [tsrW.k_sum_rules.arm2 (hc1 := Decidable.of_not_not hmem)] at h
  have hk0 : k8 = 0 := by
    have : rdW (m1.arr64 IW) (M + 8) = 0 := by simpa using hmem
    rw [e8'] at this; have := congrArg UInt64.toNat this; rwa [t8] at this
  rcases h2 : arfW (k + 1) m1 M rP with _ | ⟨rf, m2⟩ <;> simp only [h2, tsrW.k_aux_rule_fire, reduceCtorEq] at h
  obtain ⟨f, a2, run2, ⟨hS2, hg2, hdf⟩, hA2⟩ := arfW_sim (fun _ => none) vis fe (k + 1) m1 a M rP TM hS1
    (hM.grow (decTM_mono _) hg1) (L.Ind.poolSmall_of_stage hS1) hA1 (rf, m2) h2
  cases f with
  | plain => exact absurd hdf (by simp [decFire])
  | levels _ => exact absurd hdf (by simp [decFire])
  | nested lvls pins =>
  obtain ⟨-, ⟨hdl, hbl⟩, ⟨hdp, hbp⟩⟩ := hdf
  simp only [L.getD_one, L.getD_two, L.getD_three, L.getD_four, show (1 + 1 : Nat) = 2 from rfl,
    show (3 + 1 : Nat) = 4 from rfl] at hdl hbl hdp hbp
  rcases h3 : efF (k + 1) m2 (rf.tail.headD 0) (rf.tail.tail.headD 0) with _ | ⟨re, m3⟩ <;>
    simp only [h3, tsrW.k_er_from_iw, reduceCtorEq] at h
  obtain ⟨hS3, hg3, hre1, hsl3⟩ := efW_stage k h3 hS2 hdl hbl
  rcases h4 : efF (k + 1) m3 (rf.tail.tail.tail.headD 0) (rf.tail.tail.tail.tail.headD 0) with _ | ⟨rp, m4⟩ <;>
    simp only [h4, tsrW.k_er_from_iw_2, reduceCtorEq] at h
  obtain ⟨hS4, hg4, hrp1, hsl4⟩ := efW_stage k h4 hS3
    (by rw [decHL_grow hg3 hbp]; exact hdp) (by have := hg3.iw; omega)
  rcases h5 : tsrmW (k + 1) m4 (rs.headD 0) (rs.tail.headD 0) (re.headD 0) (re.tail.headD 0) (rp.headD 0)
      (rp.tail.headD 0) with _ | ⟨r5, m5⟩ <;> simp only [h5, tsrW.k_generated_rules_remap, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hg24 := (hg2.trans hg3).trans hg4
  rw [← hre1] at hsl3; rw [← hrp1] at hsl4
  obtain ⟨hd5, hR5, hb5, hS5, hg5⟩ := tsrmW_ok fe vis a2 (k + 1) h5 hS4
    (decPL_rl_grow hg24 (by have := hg1.2; omega) hd1)
    (by have := hg24.iw; omega) ((IWGrow.ext hg4).hslice? hsl3) hsl4
  refine ⟨_, a2, ?_, by simpa using hd5, by simpa using hR5, by simpa using hb5, hS5,
    (((hg1.trans hg2).trans hg3).trans hg4).trans hg5, tsrmW_afr _ h5 (efW_afr h4 (efW_afr h3 hA2))⟩
  simp only [ConRon.Arena.generatedRules, eCs, eMem, decON, hk0, ite_true]
  rw [StateT.run_bind, run2]; rfl

end rel2

end L.Ind

end

end
