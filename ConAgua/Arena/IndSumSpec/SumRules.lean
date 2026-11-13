module

public import ConAgua.Arena.IWFrame
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.IndSim
import ConAgua.Arena.RecLayout.RuleDec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.IndMaster
public import ConAgua.Arena.IndSum
public import ConAgua.Arena.SimLib
import all ConAgua.Arena.IndSum
public import ConAgua.Arena.StripTeleSpec
import ConAgua.L.ModelGen
import ConAgua.Arena.IndSumSpec.TblProg
import ConAgua.L.WordOff
import ConAgua.Arena.DeclCanonInfo

@[expose] public section

/-!
# SumRules: `ConRon.Arena.sumRules`

The refinement theorems `sumRules_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Shared pieces -/

/-- **A real callee's `RelW` fact as a `Sim`** of its model run. -/
theorem sumSim_of_relW {α : Type} {W : Mem → List Word → Option (List Word × Mem)} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    {m : Mem} {a : AState} (h : RelW W args pre op post) (hp : pre m a) :
    Sim (W m args) op a (fun r x m' a' => post m m' a' r x) :=
  fun r m' e => h m m' a r e hp

/-- **A pointer written right after a decoded prefix** extends it by the pointer's record. -/
theorem sumDecPL_write {α : Type} (m : Mem) (f : Nat → Option α) (o j : Nat) (w v : Word)
    (acc : List α) (x : α) (hw : w.toNat = o + j) (hsz : o + j < (m.arr64 IW).size)
    (h : decPL m f o j = some acc) (hx : f v.toNat = some x) :
    decPL (m.set64 IW w v) f o (j + 1) = some (acc ++ [x]) := by
  unfold decPL at h ⊢
  rw [List.range_succ, List.mapM_append]
  have e1 : (List.range j).mapM (fun i => do f (← iwN (m.set64 IW w v) (o + i))) =
      (List.range j).mapM (fun i => do f (← iwN m (o + i))) := by
    apply mapM_congr_of
    intro i hi
    have hi' : i < j := List.mem_range.mp hi
    simp only [iwN, nat?, iwA, aread_apply, set64IW_get]
    rw [ite_eq_right (by omega)]
  rw [e1, h]
  simp [iwN, nat?, iwA, aread_apply, set64IW_get, hw, hsz, hx]

/-- A handle at the head of a slice decoded below the top, as the model reads it. -/
theorem sumRd_of_decHL_truncM {m : Mem} {o l : Word} {x : EIdx} {xs : List EIdx}
    (h : decHL (truncM m) o.toNat l.toNat = some (x :: xs)) :
    ∃ w, rdW (m.arr64 IW) o = w ∧ w.toNat < 2 ^ 32 ∧ decI w = x ∧ o.toNat < iwTop m := by
  have hl : l.toNat = (l.toNat - 1) + 1 := by
    have := decHL_length (truncM m) h; simp at this; omega
  rw [hl] at h
  simp only [decHL, hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, List.cons.injEq] at h
  obtain ⟨y, hy, ys, -, rfl, -⟩ := h
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  split at hy
  · cases hy
    exact ⟨w, rdW_of_get? rfl hw', by assumption, rfl, hi⟩
  · cases hy

theorem sumDecHL_tail {m : Mem} {o l : Nat} {x : EIdx} {xs : List EIdx}
    (h : decHL m o (l + 1) = some (x :: xs)) : decHL m (o + 1) l = some xs := by
  simp only [decHL, hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, List.cons.injEq] at h
  obtain ⟨y, -, ys, hys, -, rfl⟩ := h
  exact hys

/-! ## `sum_rules_go`: the word model -/

/-- The memory after the rule record's eight field stores (the name read before them, the
right-hand side read from `IW` at its time). -/
def ruleMem (m : Mem) (q nm nF rO : Word) : Mem :=
  let m1 := erecPutMem (erecPutMem (erecPutMem m q nm) (q + Rule.nfields) nF) (q + Rule.fire) 0
  let m2 := erecPutMem (erecPutMem (erecPutMem m1 (q + Rule.lvlsOff) 0) (q + Rule.lvlsLen) 0)
    (q + Rule.pinsOff) 0
  let m3 := erecPutMem m2 (q + Rule.pinsLen) 0
  erecPutMem m3 (q + Rule.rhs) (rdW (m3.arr64 IW) rO)

/-- The stores are the rule's image (`Rule.img`). -/
theorem ruleMem_eq (m : Mem) (q nm nF rO : Word) :
    ruleMem m q nm nF rO = wrERo m q (Rule.img nm nF 0 0 0 0 0 (rdW (m.arr64 IW) rO)) := by
  -- the image's entries in order (the layout's numbers: a whole-record writer)
  simp [ruleMem, wrERo, Rule.img, recImg, Rule.ctor, Rule.nfields, Rule.fire, Rule.lvlsOff,
    Rule.lvlsLen, Rule.pinsOff, Rule.pinsLen, Rule.rhs, Rule.size, List.replicate, UInt64.add_assoc,
    erecPutMem_iw]

/-- **The model of `sum_rules_go(cO, cL, rO, rL, o)`** at exec fuel `n`. -/
l_model rgoW_spec (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hpu : p.lookup "erec_put" = some erecPut) (hp : p.lookup "sum_rules_go" = some sumRulesGoL)
  fns [hp ↦ rgoW list]
  specs [erecAlloc_specW p ha n, erecPut_specM p hpu n]
  grind [arena_grind]

/-- `rgoW`'s record by its memory `ruleMem`. -/
theorem rgoW.k_erec_alloc_some (n : Nat) (cO cL rO rL o cv nF q : Word) (m1 : Mem) :
    rgoW.k_erec_alloc n cO cL rO rL o cv nF (some (q, m1)) = rgoW.k_sum_rules_go
      (rgoW n ((ruleMem m1 q (erRd m1 cv) nF rO).set64 IW o q) (cO + 1) (cL - 1) (rO + 1) (rL - 1) (o + 1)) := by
  rw [rgoW.k_erec_alloc.arm1]; rfl

/-! ## `sum_rules`: the word model -/

/-- **The model of `sum_rules(cO, cL, rO, rL)`** at exec fuel `n`. -/
l_model rulesW_spec (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hpu : p.lookup "erec_put" = some erecPut) (hg : p.lookup "sum_rules_go" = some sumRulesGoL)
    (hia : p.lookup "iw_alloc" = some iwAlloc) (hp : p.lookup "sum_rules" = some sumRulesL)
  fns [hp ↦ rulesW list]
  specs [iwAlloc_specW p hia n, rgoW_spec p ha hpu hg n]
  grind [arena_grind]

/-- `rulesW` by its slice length `min rL cL`. -/
theorem rulesW_succ (n : Nat) (m : Mem) (cO cL rO rL : Word) : rulesW (n + 1) m cO cL rO rL =
    rulesW.k_iw_alloc n cO cL rO rL (if rL < cL then rL else cL)
      (allocW m (if rL < cL then rL else cL)) := by
  rw [rulesW.eq_2]; split <;> rfl

/-! ## The relation to the twin -/

/-- The rule decoder. -/
abbrev rlDec (m : Mem) (q : Nat) : Option IRecRule := decRule (erecP m) q

/-- The pointers `IW[o ‥ o + l)` point to rule records whose `Rule.size` words are all in the pool
(`rules_to_erec` copies all of them). -/
def RuleWordsIn (m : Mem) (o l : Nat) : Prop :=
  ∀ j < l, ∀ v, iwN m (o + j) = some v → ∀ i < Rule.size.toNat, ∃ w, erecP m (v + i) = some w

/-- **A plain rule record's decoding**, from its words. -/
theorem sumDecRule_words {R : Nat → Option Word} {q : Nat} {c nF rhs : Word}
    (h0 : R q = some c) (h1 : R (q + Rule.nfields.toNat) = some nF)
    (h3 : R (q + Rule.fire.toNat) = some 0) (h8 : R (q + Rule.rhs.toNat) = some rhs)
    (hc : c.toNat < 2 ^ 32) (hr : rhs.toNat < 2 ^ 32) :
    decRule R q = some { ctor := decI c, nfields := nF.toNat, fire := .plain, rhs := decI rhs } :=
  decRule_of (by simp [hd?, h0, hc]) (by simp [nat?, h1]) (by simp [hd?, h8, hr])
    (show nat? R _ = some 0 by simp [nat?, h3])

theorem rlDec_set_iw (m : Mem) (o v : Word) : rlDec (m.set64 IW o v) = rlDec m := by
  unfold rlDec
  rw [erecP_frame (MemFrame.set64 m IW (by decide) o v) (by decide) (by decide) (by simp) (by simp)]

theorem sumToNat_succ {w : Word} (h : w.toNat < 2 ^ 64 - 1) : (w + 1).toNat = w.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

theorem RuleWordsIn.grow {m m' : Mem} (hg : IWGrow m m') {o l : Nat} (h : RuleWordsIn m o l) (hb : o + l ≤ iwTop m) :
    RuleWordsIn m' o l := by
  intro j hj v hv i hi
  have hv' : iwN m (o + j) = some v := by
    simp only [iwN, nat?, iwA, aread_apply] at hv ⊢
    rw [← hg.iwGet (o + j) (by omega)]; exact hv
  obtain ⟨w, hw⟩ := h j hj v hv' i hi
  exact ⟨w, IWGrow.ext hg _ _ hw⟩

/-- **`sum_rules_go`'s model refines `sumRules`**: the rules written after the decoded prefix
`acc` of the result slice at `q0` (its next slot `o = q0 + j`), the slots allocated above `m0`'s
top. -/
theorem rgoW_ok {vis : Word} {fe : IFEnv} {a : AState}
    (n : Nat) : ∀ (m : Mem) (cO cL rO rL o : Word) (m0 : Mem) (q0 : Word) (j : Nat)
    (acc : List IRecRule) (cs : List (IConstantVal × Nat)) (rhss : List EIdx) (r : List Word) (m' : Mem),
    rgoW n m cO cL rO rL o = some (r, m') →
    StageR vis fe m a → IWGrow m0 m → iwTop m0 ≤ q0.toNat → o.toNat = q0.toNat + j →
    o.toNat + min cL.toNat rL.toNat ≤ iwTop m →
    decPL m (rlDec m) q0.toNat j = some acc → RuleWordsIn m q0.toNat j →
    DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) m0 cs →
    DecB (fun m => decHL m rO.toNat rL.toNat) m0 rhss →
    StageR vis fe m' a ∧ IWGrow m0 m' ∧
      decPL m' (rlDec m') q0.toNat (j + (sumRules cs rhss).length) = some (acc ++ sumRules cs rhss) ∧
      RuleWordsIn m' q0.toNat (j + (sumRules cs rhss).length) ∧
      (sumRules cs rhss).length = min cL.toNat rL.toNat ∧
      q0.toNat + j + (sumRules cs rhss).length ≤ iwTop m' := by
  induction n with
  | zero => intro m cO cL rO rL o m0 q0 j acc cs rhss r m' h; simp [rgoW] at h
  | succ n ih =>
  intro m cO cL rO rL o m0 q0 j acc cs rhss r m' h hS hg0 hq0 ho hroom hacc h11 hcs0 hrh0
  have hcs := DecB.grow (OMono.decPL decCN_mono _ _) hg0 hcs0
  have hrh := DecB.grow (OMono.decHL _ _) hg0 hrh0
  have hcl := decPL_length (m := truncM m) hcs
  have hrl := decHL_length (truncM m) hrh
  by_cases hz : cL = 0 ∨ rL = 0
  · rw [rgoW.arm1 n m cO cL rO rL o hz] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e : sumRules cs rhss = [] := by
      rcases hz with h | h
      · subst h; cases cs with | nil => simp [sumRules] | cons _ _ => simp at hcl
      · subst h; cases cs <;> cases rhss <;> simp_all [sumRules]
    rw [e]
    refine ⟨hS, hg0, by simpa using hacc, by simpa using h11, ?_, by simp; omega⟩
    rcases hz with h | h <;> simp [h]
  rw [rgoW.arm2 n m cO cL rO rL o hz] at h
  have hcL : cL ≠ 0 := fun h => hz (.inl h)
  have hrL : rL ≠ 0 := fun h => hz (.inr h)
  obtain ⟨L, hL⟩ : ∃ L, cL.toNat = L + 1 :=
    ⟨cL.toNat - 1, by have : cL.toNat ≠ 0 := fun e => hcL (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  obtain ⟨R, hR⟩ : ∃ R, rL.toNat = R + 1 :=
    ⟨rL.toNat - 1, by have : rL.toNat ≠ 0 := fun e => hrL (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hcs' : decPL (truncM m) (decCN (truncM m)) cO.toNat (L + 1) = some cs := by
    have := hcs; simp only [DecB, hL] at this; exact this
  cases cs with
  | nil => simp at hcl; omega
  | cons c cs =>
  cases rhss with
  | nil => simp at hrl; omega
  | cons rhs rhss =>
  obtain ⟨cv, nF⟩ := c
  obtain ⟨pv, hpv, hc⟩ := decPL_head hcs'
  have htail : DecB (fun m => decPL m (decCN m) (cO.toNat + 1) L) m0 cs := by
    have := hcs0; simp only [DecB, hL] at this; exact decPL_tail this
  obtain ⟨⟨cqN, hcq, hcv⟩, hnF⟩ := decCN_some hc
  obtain ⟨w, hw, hwv, hcO⟩ := rdW_of_iwN_truncM hpv
  have hcq' : iwN (truncM m) w.toNat = some cqN := by rw [hwv]; exact hcq
  obtain ⟨w2, hw2, hw2v, hpvlt⟩ := rdW_of_iwN_truncM hcq'
  have hw1 : (w + 1).toNat = pv + 1 := by
    have := hS.lt64 (x := iwTop m) (Nat.le_refl _)
    rw [hwv] at hpvlt; rw [UInt64.toNat_add, hwv]; simp; omega
  have hnF' : iwN (truncM m) (w + 1).toNat = some nF := by rw [hw1]; exact hnF
  obtain ⟨w3, hw3, hw3v, -⟩ := rdW_of_iwN_truncM hnF'
  have hcvE : decCV (erecP m) w2.toNat = some cv := by rw [hw2v]; exact decCVp_truncM hcv
  obtain ⟨wn, hwn, hwnl, hname⟩ := decCV_name hcvE
  have hwn' : erRd m w2 = wn := (erRd_of_erecP hwn).1
  have hrh' : decHL (truncM m) rO.toNat (R + 1) = some (rhs :: rhss) := by
    have := hrh; simp only [DecB, hR] at this; exact this
  have hrtail : DecB (fun m => decHL m (rO.toNat + 1) R) m0 rhss := by
    have := hrh0; simp only [DecB, hR] at this; exact sumDecHL_tail this
  obtain ⟨wr, hwr, hwrl, hwrd, hrO⟩ := sumRd_of_decHL_truncM (o := rO) (l := rL) (by rw [hR]; exact hrh')
  rw [hw, hw2, hw3] at h
  rcases hal : erAllocW m Rule.size with _ | ⟨q, m2⟩ <;> rw [hal] at h
  · rw [rgoW.k_erec_alloc.none] at h; cases h
  rw [rgoW.k_erec_alloc_some, ruleMem_eq] at h
  obtain ⟨-, hf2, -⟩ := erAllocW_spec hal hS.iw
  have hI2 : m2.arr64 IW = m.arr64 IW := hf2.arr IW (by simp) (by decide)
  have hr2 : erRd m2 w2 = erRd m w2 := by
    unfold erRd; rw [hf2.arr _ (by simp) (by rw [tierA_EREC]; split <;> decide)]
  rw [hI2, hr2, hwn', hwr] at h
  obtain ⟨hSM, hgM, -, -, -, -, hget⟩ :=
    erRecO_stage hal hS (Rule.img wn w3 0 0 0 0 0 wr) (Rule.img_length ..).symm
  have hq11 : ∀ i < Rule.size.toNat, ∃ w, erecP (wrERo m2 q (Rule.img wn w3 0 0 0 0 0 wr)) (q.toNat + i) = some w :=
    fun i hi => erRecO_words hal hS.iw _ (Rule.img_length ..).symm i (by rw [Rule.img_length]; exact hi)
  generalize hM : wrERo m2 q _ = M at hSM hgM hget hq11 h
  -- the record decodes from its fields
  have hrec : rlDec M q.toNat = some { ctor := decI wn, nfields := w3.toNat, fire := .plain, rhs := decI wr } :=
    sumDecRule_words (hget _ _ (Rule.img_ctor ..)) (hget _ _ (Rule.img_nf ..)) (hget _ _ (Rule.img_fk ..))
      (hget _ _ (Rule.img_rhs ..)) hwnl hwrl
  -- the pointer written
  have hoT : o.toNat < iwTop m := by simp only [Nat.min_def] at hroom; split at hroom <;> omega
  have hoS : o.toNat < (M.arr64 IW).size := by
    have h1 := hSM.iw.iw; have := hgM.iw; omega
  have haccM : decPL M (rlDec M) q0.toNat j = some acc :=
    _root_.L.Ind.decPL_grow hgM (fun q x h => ArrExt.decRule (IWGrow.ext hgM) h) _ _ _
      (by omega) hacc
  have hacc' := sumDecPL_write M (rlDec M) q0.toNat j o q acc _ ho (by omega) haccM hrec
  rw [← rlDec_set_iw M o q] at hacc'
  have h11' : RuleWordsIn (M.set64 IW o q) q0.toNat (j + 1) := by
    intro k hk v hv i hi
    have hE : erecP (M.set64 IW o q) = erecP M :=
      erecP_frame (MemFrame.set64 M IW (by decide) o q) (by decide) (by decide) (by simp) (by simp)
    rw [hE]
    simp only [iwN, nat?, iwA, aread_apply, set64IW_get, Option.map_eq_some_iff] at hv
    by_cases hkj : k < j
    · rw [ite_eq_right (by omega)] at hv
      have := (h11.grow hgM (by omega)) k hkj v (by simp only [iwN, nat?, iwA, aread_apply]; simpa using hv) i hi
      exact this
    · have hkj' : k = j := by omega
      subst hkj'
      rw [ite_eq_left (by omega)] at hv
      obtain ⟨x, hx, rfl⟩ := hv
      simp only [Option.some.injEq] at hx
      subst hx
      exact hq11 i hi
  have hS' := hSM.set_iw o q
  have hg0' : IWGrow m0 (M.set64 IW o q) := (hg0.trans hgM).set_iw o q (by omega)
  have htop' : iwTop (M.set64 IW o q) = iwTop M := by
    simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hlt : o.toNat < 2 ^ 64 - 1 := by have := hS.lt64 (x := iwTop m) (Nat.le_refl _); omega
  have hcO1 : (cO + 1).toNat = cO.toNat + 1 := sumToNat_succ (by have := hS.lt64 (x := iwTop m) (Nat.le_refl _); omega)
  have hrO1 : (rO + 1).toNat = rO.toNat + 1 := sumToNat_succ (by have := hS.lt64 (x := iwTop m) (Nat.le_refl _); omega)
  have hcL1 : (cL - 1).toNat = L := by rw [_root_.L.toNat_sub_one_of_ne hcL]; omega
  have hrL1 : (rL - 1).toNat = R := by rw [_root_.L.toNat_sub_one_of_ne hrL]; omega
  rcases h3 : rgoW n (M.set64 IW o q) (cO + 1) (cL - 1) (rO + 1) (rL - 1) (o + 1) with _ | ⟨r3, m3⟩ <;>
    rw [h3] at h
  · rw [rgoW.k_sum_rules_go.none] at h; cases h
  simp only [rgoW.k_sum_rules_go.arm1, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS3, hg3, hd3, h113, hl3, ht3⟩ := ih (M.set64 IW o q) (cO + 1) (cL - 1) (rO + 1) (rL - 1) (o + 1)
    m0 q0 (j + 1) _ cs rhss r3 m3 h3 hS' hg0' hq0 (by rw [sumToNat_succ hlt]; omega)
    (by rw [sumToNat_succ hlt, hcL1, hrL1, htop']; have := hgM.iw; simp only [Nat.min_def] at hroom ⊢
        split at hroom <;> split <;> omega)
    hacc' h11' (by rw [hcO1, hcL1]; exact htail) (by rw [hrO1, hrL1]; exact hrtail)
  have hsr : sumRules ((cv, nF) :: cs) (rhs :: rhss) =
      { ctor := decI wn, nfields := w3.toNat, fire := .plain, rhs := decI wr } :: sumRules cs rhss := by
    simp only [sumRules, ← hname, hw3v, hwrd]
  rw [hsr]
  refine ⟨hS3, hg3, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc, Nat.add_comm 1] using hd3
  · simpa [Nat.add_assoc, Nat.add_comm 1] using h113
  · simp only [List.length_cons, hl3, hcL1, hrL1, hL, hR]; omega
  · simp only [List.length_cons]; omega

/-- **`sum_rules`' model refines `sumRules`**: the rules in a fresh `IW` slice of `EREC` rule
pointers. -/
theorem rulesW_ok {vis : Word} {fe : IFEnv} {a : AState}
    (n : Nat) (m : Mem) (cO cL rO rL : Word) (cs : List (IConstantVal × Nat))
    (rhss : List EIdx) (r : List Word) (m' : Mem) (h : rulesW (n + 1) m cO cL rO rL = some (r, m'))
    (hS : StageR vis fe m a)
    (hcs : DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) m cs)
    (hrh : DecB (fun m => decHL m rO.toNat rL.toNat) m rhss) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decPL m' (rlDec m') (r.headD 0).toNat (r.tail.headD 0).toNat = some (sumRules cs rhss) ∧
      RuleWordsIn m' (r.headD 0).toNat (r.tail.headD 0).toNat ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  rw [rulesW_succ] at h
  generalize hk : (if rL < cL then rL else cL) = k at h
  have hkm : k.toNat = min cL.toNat rL.toNat := by
    subst hk; split
    · rename_i h; have := UInt64.lt_iff_toNat_lt.mp h; omega
    · rename_i h; have : ¬ rL.toNat < cL.toNat := fun e => h (UInt64.lt_iff_toNat_lt.mpr e); omega
  rcases hal : allocW m k with _ | ⟨o, m1⟩ <;> rw [hal] at h
  · rw [rulesW.k_iw_alloc.none] at h; cases h
  rw [rulesW.k_iw_alloc.arm1] at h
  rcases h2 : rgoW n m1 cO cL rO rL o with _ | ⟨r2, m2⟩ <;> rw [h2] at h
  · rw [rulesW.k_sum_rules_go.none] at h; cases h
  simp only [rulesW.k_sum_rules_go.arm1, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS1, hg1, hot, ht1⟩ := allocW_stage hal hS
  obtain ⟨hS', hg', hd', h11', hl', ht'⟩ := rgoW_ok n m1 cO cL rO rL o m o 0 [] cs rhss r2 m2 h2 hS1 hg1
    (by omega) (by simp) (by omega) (by simp [decPL]) (fun j hj => absurd hj (by omega)) hcs hrh
  refine ⟨hS', hg', ?_, ?_, ?_⟩
  · simpa [hkm, hl'] using hd'
  · simpa [hkm, hl'] using h11'
  · simp only [List.headD_cons, List.tail_cons]; omega

section census
variable (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
  (hpu : p.lookup "erec_put" = some erecPut)
  (hg : p.lookup "sum_rules_go" = some sumRulesGoL) (hia : p.lookup "iw_alloc" = some iwAlloc)
  (hp : p.lookup "sum_rules" = some sumRulesL)
include ha hpu hg hia hp

/-- **`sum_rules` refines `sumRules`**: from the stage relation and the constructor and
right-hand-side lists decoded below the tops, the rules in a fresh `IW` slice of pointers to
`EREC` rule records (`decRule`; all eleven words of each in the pool). -/
@[refines ConRon.Arena.sumRules]
theorem sumRules_refines (n : Nat) (s₀ : St) (a₀ : AState)
    (fe : IFEnv) (vis cO cL rO rL : Word) (cs : List (IConstantVal × Nat)) (rhss : List EIdx)
    (hS : StageR vis fe s₀.mem a₀)
    (hcs : DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) s₀.mem cs)
    (hrh : DecB (fun m => decHL m rO.toNat rL.toNat) s₀.mem rhss) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "sum_rules" [cO, cL, rO, rL]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      decPL s'.mem (rlDec s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat = some (sumRules cs rhss) ∧
      RuleWordsIn s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  refine triple_post (rulesW_spec p ha hpu hg hia hp (n + 1) s₀ cO cL rO rL) ?_
  rintro r s' ⟨hl, hm⟩
  exact ⟨hl, rulesW_ok n _ cO cL rO rL cs rhss r _ hm hS hcs hrh⟩

end census

end L.Ind

end
