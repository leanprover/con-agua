import ConAgua.Arena.IndSumSpec12
import ConAgua.Arena.IndRealAbsSim

/-!
# `check_sum_ctors` refines `checkSumCtors` (lane `indproofs2`)

All constructors' types, in list order. L: self-recursive on the slice; the head's `[cv, nF]` record
and its sorts header (`rec2`) are consed onto the rest's slices (`sl_cons`, docs/deviations.md D18),
so every word written lies above the old pool top and the results are carried as `DecB` facts.

`ctorX`: `check_sum_ctor`'s model at every exec fuel (it cannot return below fuel 3: its
`struct_ctor_resid_ok` call has no fuel left for `param_levels`).
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A word sum that does not wrap. -/
theorem sumAddNoOv {a b : Word} (h : ¬ a + b < a) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
  have := b.toNat_lt; have := a.toNat_lt
  rw [UInt64.toNat_add]; omega

/-! ## `check_sum_ctor` at every fuel -/

/-- `check_sum_ctor`'s model at exec fuel `k`. -/
def ctorX (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Option (List Word × Mem)
  | n + 3, m, vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvC, nF, cvTa =>
    ctorW cR n m vis0 vis T lo ll nP nIdx rs isP lg cvC nF cvTa
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none

set_option maxHeartbeats 4000000 in
theorem ctorX_spec (p : Prog) (hP : SumProg p) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St)
    (vis0 vis T lo ll nP nIdx rs isP lg cvC nF cvTa : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_ctor"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvC, nF, cvTa]
    ⦃fun r s' => LocEq s' s₀ ∧
      ctorX cR k s₀.mem vis0 vis T lo ll nP nIdx rs isP lg cvC nF cvTa = some (r, s'.mem); ⊤⦄ := by
  match k with
  | n + 3 => exact ctorW_spec p hP cR hcR n s₀ vis0 vis T lo ll nP nIdx rs isP lg cvC nF cvTa
  | 0 =>
    rw [invoke_eq _ hP.hctor]; simp only [callFn, checkSumCtorL]
    vcgen [exec] <;> grind
  | 1 =>
    rw [invoke_eq _ hP.hctor]; simp only [callFn, checkSumCtorL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        hcR 0 "check_constant_val", stripPis_specF p hP.strip 0,
        srW_spec p hP.ha hP.hc hP.hsc hP.hg hP.hpf hP.hpp hP.hip hP.hplg hP.hpl hP.hil hP.hcf hP.hcp hP.hic
          hP.hbf hP.hbp hP.hib hP.hpg hP.hps hP.heq hP.hsr hP.ad 0,
        callW_spec p 0 "open_pis_at_fvars_f", callW_spec p 0 "fvar_type_ds",
        callW_spec p 0 "check_struct_doms_at", callW_spec p 0 "check_sum_ctor_tail"] <;>
      finish (gen := 30) (instances := 5000) [srW]
  | 2 =>
    rw [invoke_eq _ hP.hctor]; simp only [callFn, checkSumCtorL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        hcR 1 "check_constant_val", stripPis_specF p hP.strip 1,
        srW_spec p hP.ha hP.hc hP.hsc hP.hg hP.hpf hP.hpp hP.hip hP.hplg hP.hpl hP.hil hP.hcf hP.hcp hP.hic
          hP.hbf hP.hbp hP.hib hP.hpg hP.hps hP.heq hP.hsr hP.ad 1,
        callW_spec p 1 "open_pis_at_fvars_f", callW_spec p 1 "fvar_type_ds",
        callW_spec p 1 "check_struct_doms_at", callW_spec p 1 "check_sum_ctor_tail"] <;>
      finish (gen := 30) (instances := 5000) [srW, srK1, plW]

/-! ## `check_sum_ctors`: the word model -/

/-- After the second `sl_cons`. -/
def sctsK6 (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m) => some ([r1.headD 0, r1.tail.headD 0, r2.headD 0, r2.tail.headD 0], m)
/-- After the first `sl_cons`. -/
def sctsK5 (n : Nat) (sH : Word) (rr : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => sctsK6 r1 (consW n m sH (rr.tail.tail.headD 0) (rr.tail.tail.tail.headD 0))
/-- After the rest. -/
def sctsK4 (n : Nat) (nC sH : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m) => sctsK5 n sH rr (consW n m nC (rr.headD 0) (rr.tail.headD 0))
/-- After the sorts header. -/
def sctsK3 (rest : Mem → Option (List Word × Mem)) (n : Nat) (nC : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rh, m) => sctsK4 n nC (rh.headD 0) (rest m)
/-- After the `[cv, nF]` record. -/
def sctsK2 (rest : Mem → Option (List Word × Mem)) (n : Nat) (r : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rn, m) => sctsK3 rest n (rn.headD 0) (recW m 2 [r.tail.headD 0, r.tail.tail.headD 0])
/-- After `check_sum_ctor`. -/
def sctsK1 (rest : Mem → Option (List Word × Mem)) (n : Nat) (nF : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => sctsK2 rest n r (recW m 2 [r.headD 0, nF])

/-- **The model of `check_sum_ctors(vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvTa, cO, cL)`** at
exec fuel `k`. -/
def sctsW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvTa, cO, cL =>
    if cL = 0 then some ([0, 0, 0, 0], m)
    else if nP + nIdx < nP then none
    else if nP + rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1) < nP then none
    else sctsK1 (fun m' => sctsW cR k m' vis0 vis T lo ll nP nIdx rs isP lg cvTa (cO + 1) (cL - 1)) k
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1))
      (ctorX cR k m vis0 vis T lo ll nP nIdx rs isP lg (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1)) cvTa)

section arms
variable (cR : CallM) (rest : Mem → Option (List Word × Mem)) (k : Nat) (m : Mem)
  (vis0 vis T lo ll nP nIdx rs isP lg cvTa cO cL nF nC sH : Word) (r rr r1 : List Word)
theorem sctsW_nil (h : cL = 0) :
    sctsW cR (k + 1) m vis0 vis T lo ll nP nIdx rs isP lg cvTa cO cL = some ([0, 0, 0, 0], m) := by
  simp [sctsW, h]
theorem sctsW_ov1 (h : cL ≠ 0) (h1 : nP + nIdx < nP) :
    sctsW cR (k + 1) m vis0 vis T lo ll nP nIdx rs isP lg cvTa cO cL = none := by
  simp [sctsW, h, h1]
theorem sctsW_ov2 (h : cL ≠ 0) (h1 : ¬ nP + nIdx < nP)
    (h2 : nP + rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1) < nP) :
    sctsW cR (k + 1) m vis0 vis T lo ll nP nIdx rs isP lg cvTa cO cL = none := by
  simp [sctsW, h, h1, h2]
theorem sctsW_cons (h : cL ≠ 0) (h1 : ¬ nP + nIdx < nP)
    (h2 : ¬ nP + rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1) < nP) :
    sctsW cR (k + 1) m vis0 vis T lo ll nP nIdx rs isP lg cvTa cO cL =
    sctsK1 (fun m' => sctsW cR k m' vis0 vis T lo ll nP nIdx rs isP lg cvTa (cO + 1) (cL - 1)) k
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1))
      (ctorX cR k m vis0 vis T lo ll nP nIdx rs isP lg (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1)) cvTa) := by
  simp [sctsW, h, h1, h2]
theorem sctsK6_some : sctsK6 r1 (some (r, m)) =
    some ([r1.headD 0, r1.tail.headD 0, r.headD 0, r.tail.headD 0], m) := rfl
theorem sctsK5_some : sctsK5 k sH rr (some (r1, m)) =
    sctsK6 r1 (consW k m sH (rr.tail.tail.headD 0) (rr.tail.tail.tail.headD 0)) := rfl
theorem sctsK4_some : sctsK4 k nC sH (some (rr, m)) = sctsK5 k sH rr (consW k m nC (rr.headD 0) (rr.tail.headD 0)) :=
  rfl
theorem sctsK3_some : sctsK3 rest k nC (some (r, m)) = sctsK4 k nC (r.headD 0) (rest m) := rfl
theorem sctsK2_some : sctsK2 rest k r (some (rr, m)) =
    sctsK3 rest k (rr.headD 0) (recW m 2 [r.tail.headD 0, r.tail.tail.headD 0]) := rfl
theorem sctsK1_some : sctsK1 rest k nF (some (r, m)) = sctsK2 rest k r (recW m 2 [r.headD 0, nF]) := rfl
end arms
attribute [ind_grind] sctsW_nil sctsW_ov1 sctsW_ov2 sctsW_cons sctsK6_some sctsK5_some sctsK4_some sctsK3_some sctsK2_some sctsK1_some

set_option maxHeartbeats 4000000 in
theorem sctsW_spec (p : Prog) (hP : SumProg p) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) : ∀ (s₀ : St)
    (vis0 vis T lo ll nP nIdx rs isP lg cvTa cO cL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_ctors"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvTa, cO, cL]
    ⦃fun r s' => LocEq s' s₀ ∧
      sctsW cR k s₀.mem vis0 vis T lo ll nP nIdx rs isP lg cvTa cO cL = some (r, s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ vis0 vis T lo ll nP nIdx rs isP lg cvTa cO cL
    rw [invoke_eq _ hP.hcs]; simp only [callFn, checkSumCtorsL]
    vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ vis0 vis T lo ll nP nIdx rs isP lg cvTa cO cL
    rw [invoke_eq _ hP.hcs]
    simp only [callFn, checkSumCtorsL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        ctorX_spec p hP cR hcR k, rec2_specW p hP.ha k hP.hrec2, slCons_specW p hP.ha hP.hc hP.hsc k, ih] <;>
      finish (gen := 30) (instances := 5000) [rdW_eq]

/-! ## The relation to the twin -/

/-- The sorts headers' decoder: a pointer to `[off, len]` of a level-handle slice. -/
abbrev sortsDec (m : Mem) (q : Nat) : Option (List LIdx) := decLH m (fun o l => decHL m o l) q

theorem sortsDec_mono (q : Nat) : OMono (fun m => sortsDec m q) :=
  OMono.decAt (fun o l => OMono.decHL o l) q

/-- A decoded pointer slice's numbers decode in the memory itself. -/
theorem sumDecNL_of_decB {α : Type} {f : Mem → Nat → Option α} {m : Mem} {o l : Nat} {ys : List α}
    (h : DecB (fun m => decPL m (f m) o l) m ys) :
    ∃ ps, decNL (truncM m) o l = some ps ∧ decNL m o l = some ps ∧ ps.mapM (f (truncM m)) = some ys := by
  have h' : decPL (truncM m) (f (truncM m)) o l = some ys := h
  rw [decPL_eq_bind] at h'
  cases hps : decNL (truncM m) o l with
  | none => rw [hps] at h'; cases h'
  | some ps =>
    rw [hps] at h'
    exact ⟨ps, rfl, (OMono.decNL o l).mono _ _ _ (IWGrow.truncExt (IWGrow.refl m)) hps, by simpa using h'⟩

/-- **Consing onto a decoded pointer slice** (`sl_cons`'s result, above the old top). -/
theorem sumDecB_cons {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q))
    {m m' : Mem} {o' l' : Nat} {x : Nat} {ps : List Nat} {y : α} {ys : List α}
    (hps : ps.mapM (f (truncM m)) = some ys) (hd' : decNL m' o' l' = some (x :: ps))
    (hb' : o' + l' ≤ iwTop m') (hg : IWGrow m m') (hy : DecB (fun m => f m x) m' y) :
    DecB (fun m => decPL m (f m) o' l') m' (y :: ys) := by
  have e2 : DecB (fun m => ps.mapM (f m)) m' ys := DecB.grow (OMono.mapM hf ps) hg hps
  show decPL (truncM m') (f (truncM m')) o' l' = some (y :: ys)
  rw [decPL_eq_bind, show decNL (truncM m') o' l' = some (x :: ps) from decNL_decB hd' hb']
  simp only [Option.bind_some, List.mapM_cons]
  rw [show f (truncM m') x = some y from hy, show ps.mapM (f (truncM m')) = some ys from e2]
  rfl

/-- **A `rec2` record under the stage relation**, its two words read below the new top. -/
theorem sumRec2 {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a0 : AState} {x y : Word} {r : List Word} (h : recW m 2 [x, y] = some (r, m'))
    (hS : StageR dn vis fe m a0) :
    StageR dn vis fe m' a0 ∧ IWGrow m m' ∧ iwN (truncM m') (r.headD 0).toNat = some x.toNat ∧
      iwN (truncM m') ((r.headD 0).toNat + 1) = some y.toNat := by
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage h hS rfl
  subst hr
  have hT : (rdW (m.arr64 CTL) 200).toNat = iwTop m := rfl
  refine ⟨hS', hg, ?_, ?_⟩
  · rw [List.headD_cons, iwN_truncM (by simp at htop; omega)]
    simp only [iwN, nat?, iwA]; rw [show (rdW (m.arr64 CTL) 200).toNat = (rdW (m.arr64 CTL) 200).toNat + 0 from rfl,
      hget 0 (by simp)]; rfl
  · rw [List.headD_cons, iwN_truncM (by simp at htop; omega)]
    simp only [iwN, nat?, iwA]; rw [hget 1 (by simp)]; rfl

/-- The `[cv, nF]` record of a constructor, decoded below the top. -/
theorem sumDecCN_of {m : Mem} {q cvw nF : Nat} {cv : IConstantVal}
    (h0 : iwN (truncM m) q = some cvw) (h1 : iwN (truncM m) (q + 1) = some nF)
    (hcv : DecB (fun m => decCVp m cvw) m cv) : DecB (fun m => decCN m q) m (cv, nF) := by
  show decCN (truncM m) q = some (cv, nF)
  simp only [decCN, h0, h1, Option.bind_eq_bind, Option.bind_some]
  rw [show decCVp (truncM m) cvw = some cv from hcv]; rfl

/-- A sorts header, decoded below the top. -/
theorem sumSortsDec_of {m : Mem} {q o l : Nat} {xs : List LIdx}
    (h0 : iwN (truncM m) q = some o) (h1 : iwN (truncM m) (q + 1) = some l)
    (hd : decHL m o l = some xs) (hb : o + l ≤ iwTop m) : DecB (fun m => sortsDec m q) m xs := by
  show decLH (truncM m) (fun o l => decHL (truncM m) o l) q = some xs
  simp only [decLH, decAt, h0, h1, Option.bind_eq_bind, Option.bind_some]
  rw [decHL_truncM hb]; exact hd

/-- **`check_sum_ctors`' model refines `checkSumCtors .verified`**, the pre-block environment being
the restriction of `fe` to `vis0`: the new constructor list and the sorts lists as fresh pointer
slices, decoded below the tops. -/
theorem sctsW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (vis0 T lo ll nP nIdx rs isP lg cvTaw : Word) (lps : List NIdx) (cvTa : IConstantVal)
    (hT : H T) (hrs : H rs) (k : Nat) :
    ∀ (m : Mem) (a : AState) (cO cL : Word) (cs : List (IConstantVal × Nat)),
    StageR dn vis fe m a → decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    DecB (fun m => decCVp m cvTaw.toNat) m cvTa →
    DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) m cs → AbsOK m →
    Sim (sctsW stubCall k m vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL)
      (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs)
        (isP != 0) (lg != 0) cvTa cs) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        DecB (fun m => decPL m (decCN m) (r.headD 0).toNat (r.tail.headD 0).toNat) m' x.1 ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧
        DecB (fun m => decPL m (sortsDec m) (r.tail.tail.headD 0).toNat
          (r.tail.tail.tail.headD 0).toNat) m' x.2 ∧
        (r.tail.tail.headD 0).toNat + (r.tail.tail.tail.headD 0).toNat ≤ iwTop m' ∧ AbsOK m') := by
  induction k with
  | zero => intro m a cO cL cs _ _ _ _ _ _; exact Sim.of_none
  | succ k ih =>
  intro m a cO cL cs hS hlps hlb hta hcs hA
  have hcl := decPL_length (m := truncM m) hcs
  by_cases hl : cL = 0
  · rw [sctsW_nil (h := hl)]
    have : cs = [] := by subst hl; cases cs with | nil => rfl | cons _ _ => simp at hcl
    subst this
    simp only [checkSumCtors]
    exact Sim.ret ⟨hS, IWGrow.refl _, by simp [DecB, decPL], by simp, by simp [DecB, decPL], by simp, hA⟩
  by_cases hov1 : nP + nIdx < nP
  · rw [sctsW_ov1 (h := hl) (h1 := hov1)]; exact Sim.of_none
  have hni : nP.toNat + nIdx.toNat < 2 ^ 64 := by rw [← sumAddNoOv hov1]; exact UInt64.toNat_lt _
  obtain ⟨L, hL⟩ : ∃ L, cL.toNat = L + 1 :=
    ⟨cL.toNat - 1, by have : cL.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hcs' : decPL (truncM m) (decCN (truncM m)) cO.toNat (L + 1) = some cs := by
    have := hcs; simp only [DecB, hL] at this; exact this
  cases cs with
  | nil => simp at hcl; omega
  | cons c cs =>
  obtain ⟨cv, nF⟩ := c
  obtain ⟨pv, hpv, hc⟩ := decPL_head hcs'
  have htail := decPL_tail hcs'
  obtain ⟨⟨cqN, hcq, hcv⟩, hnF⟩ := decCN_some hc
  obtain ⟨w, hw, hwv, hcO⟩ := rdW_of_iwN_truncM hpv
  have hcq' : iwN (truncM m) w.toNat = some cqN := by rw [hwv]; exact hcq
  obtain ⟨w2, hw2, hw2v, hpvlt⟩ := rdW_of_iwN_truncM hcq'
  have hT0 := hS.lt64 (x := iwTop m) (Nat.le_refl _)
  have hw1 : (w + 1).toNat = pv + 1 := by rw [UInt64.toNat_add, hwv]; simp; omega
  have hnF' : iwN (truncM m) (w + 1).toNat = some nF := by rw [hw1]; exact hnF
  obtain ⟨w3, hw3, hw3v, -⟩ := rdW_of_iwN_truncM hnF'
  by_cases hov2 : nP + rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1) < nP
  · rw [sctsW_ov2 (h := hl) (h1 := hov1) (h2 := hov2)]; exact Sim.of_none
  rw [sctsW_cons (h := hl) (h1 := hov1) (h2 := hov2)]
  rw [hw, hw3] at hov2
  rw [hw, hw2, hw3]
  have hcvB : DecB (fun m => decCVp m w2.toNat) m cv := by
    show decCVp (truncM m) w2.toNat = some cv; rw [hw2v]; exact hcv
  have hnf : nP.toNat + w3.toNat < 2 ^ 64 := by rw [← sumAddNoOv hov2]; exact UInt64.toNat_lt _
  -- the head constructor
  obtain hk | ⟨j, rfl⟩ : k < 3 ∨ ∃ j, k = j + 3 := by
    rcases Nat.lt_or_ge k 3 with h | h
    · exact .inl h
    · exact .inr ⟨k - 3, by omega⟩
  · have : ctorX stubCall k m vis0 vis T lo ll nP nIdx rs isP lg w2 w3 cvTaw = none := by
      match k, hk with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
    rw [this]; exact Sim.of_none
  subst hw3v
  simp only [checkSumCtors]
  refine Sim.bindK (K := sctsK1 _ (j + 3) w3) rfl (fun _ _ => rfl)
    (ctorW_ok j m a vis0 T lo ll nP nIdx rs isP lg w2 w3 cvTaw lps cv cvTa hS hT hlps hlb hcvB hta hrs
      hni hnf hA) fun r x m1 a1 hQ => ?_
  obtain ⟨hS1, hg1, hr0, hx1, hsorts, hsb, hA1⟩ := hQ
  obtain ⟨cvCa, sorts⟩ := x
  simp only at hx1 hsorts
  subst hx1
  rw [sctsK1_some]
  cases hn : recW m1 2 [r.headD 0, w3] with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨rn, m2⟩ := y
  rw [sctsK2_some]
  obtain ⟨hS2, hg2, hn0, hn1⟩ := sumRec2 hn hS1
  have hA2 : AbsOK m2 := recW_afr hn hA1
  cases hh : recW m2 2 [r.tail.headD 0, r.tail.tail.headD 0] with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨rh, m3⟩ := y
  rw [sctsK3_some]
  obtain ⟨hS3, hg3, hh0, hh1⟩ := sumRec2 hh hS2
  have hA3 : AbsOK m3 := recW_afr hh hA2
  have hg03 := (hg1.trans hg2).trans hg3
  have hcO1 : (cO + 1).toNat = cO.toNat + 1 := sumToNat_succ (by omega)
  have hcL1 : (cL - 1).toNat = L := by rw [sumToNat_pred hl]; omega
  refine Sim.bindK (K := sctsK4 (j + 3) (rn.headD 0) (rh.headD 0)) rfl (fun _ _ => rfl)
    (ih m3 a1 (cO + 1) (cL - 1) cs hS3 (by rw [decHL_grow hg03 hlb]; exact hlps)
      (by have := hg03.1; omega) (DecB.grow (OMono.decCVp _) hg03 hta)
      (by rw [hcO1, hcL1]; exact DecB.grow (OMono.decPL decCN_mono _ _) hg03 htail) hA3)
    fun rr y m4 a4 hQ => ?_
  obtain ⟨hS4, hg4, hD1, hb1, hD2, hb2, hA4⟩ := hQ
  obtain ⟨rest, srest⟩ := y
  simp only at hD1 hD2
  rw [sctsK4_some]
  obtain ⟨ps1, hps1t, hps1, hmap1⟩ := sumDecNL_of_decB hD1
  cases hc1 : consW (j + 3) m4 (rn.headD 0) (rr.headD 0) (rr.tail.headD 0) with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨r1, m5⟩ := y
  rw [sctsK5_some]
  obtain ⟨hS5, hg5, hd5, ht5⟩ := consW_stageN hc1 hS4 hb1 hps1
  obtain ⟨ps2, hps2t, hps2, hmap2⟩ := sumDecNL_of_decB hD2
  have hb2' : (rr.tail.tail.headD 0).toNat + (rr.tail.tail.tail.headD 0).toNat ≤ iwTop m5 := by
    have := hg5.1; omega
  cases hc2 : consW (j + 3) m5 (rh.headD 0) (rr.tail.tail.headD 0) (rr.tail.tail.tail.headD 0) with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨r2, m6⟩ := y
  rw [sctsK6_some]
  obtain ⟨hS6, hg6, hd6, ht6⟩ := consW_stageN hc2 hS5 hb2'
    ((OMono.decNL _ _).mono _ _ _ (IWGrow.truncExt hg5) hps2t)
  -- the head's records, decoded at the end
  have hy1 : DecB (fun m => decCN m (rn.headD 0).toNat) m5 (cvCa, w3.toNat) := by
    have h0 : DecB (fun m => decCN m (rn.headD 0).toNat) m2 (cvCa, w3.toNat) := by
      refine sumDecCN_of hn0 hn1 ?_
      rw [hr0]; exact DecB.grow (OMono.decCVp _) (hg1.trans hg2) hcvB
    exact DecB.grow (decCN_mono _) ((hg3.trans hg4).trans hg5) h0
  have hy2 : DecB (fun m => sortsDec m (rh.headD 0).toNat) m6 sorts := by
    have h0 : DecB (fun m => sortsDec m (rh.headD 0).toNat) m3 sorts :=
      sumSortsDec_of hh0 hh1 (by rw [decHL_grow (hg2.trans hg3) hsb]; exact hsorts)
        (by have := (hg2.trans hg3).1; omega)
    exact DecB.grow (sortsDec_mono _) ((hg4.trans hg5).trans hg6) h0
  have hg46 := hg5.trans hg6
  refine Sim.ret ⟨hS6, (hg03.trans hg4).trans hg46, ?_, ?_, ?_, ?_, consW_afr hc2 (consW_afr hc1 hA4)⟩
  · simp only [List.headD_cons, List.tail_cons]
    exact DecB.grow (OMono.decPL decCN_mono _ _) hg6
      (sumDecB_cons decCN_mono hmap1 hd5 (by omega) hg5 hy1)
  · simp only [List.headD_cons, List.tail_cons]; have := hg6.1; omega
  · simp only [List.headD_cons, List.tail_cons]
    exact sumDecB_cons sortsDec_mono hmap2 hd6 (by omega) hg46 hy2
  · simp only [List.headD_cons, List.tail_cons]; omega


/-- **`check_sum_ctors` refines `checkSumCtors .verified`** (through `check_sum_ctor`'s stubs), the
pre-block environment the restriction of `fe` to `vis0`: from the stage relation and the
constructor list decoded below the tops, the new constructor list and the sorts lists as fresh
pointer slices decoded below the tops. Under `StageR`; the census link is `checkSumCtors_refinesC`
(`IndT/Sum5.lean`). -/
theorem checkSumCtors_refines (p : Prog) (hP : SumProg p) (k : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL : Word) (lps : List NIdx) (cvTa : IConstantVal)
    (cs : List (IConstantVal × Nat)) (hS : StageR dn vis fe s₀.mem a₀) (hT : H T) (hrs : H rs)
    (hlps : decHL s₀.mem lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop s₀.mem)
    (hta : DecB (fun m => decCVp m cvTaw.toNat) s₀.mem cvTa)
    (hcs : DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) s₀.mem cs) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_ctors"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvTaw, cO, cL]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs)
        (isP != 0) (lg != 0) cvTa cs) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps
        nP.toNat nIdx.toNat (decI rs) (isP != 0) (lg != 0) cvTa cs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      DecB (fun m => decPL m (decCN m) (r.headD 0).toNat (r.tail.headD 0).toNat) s'.mem
        (AM.res (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat
          (decI rs) (isP != 0) (lg != 0) cvTa cs) a₀).1 ∧
      DecB (fun m => decPL m (sortsDec m) (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat)
        s'.mem (AM.res (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat
          nIdx.toNat (decI rs) (isP != 0) (lg != 0) cvTa cs) a₀).2; ⊤⦄ := by
  refine triple_post (sctsW_spec p hP stubCall (stubCall_spec p) k s₀ vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hok, hS', hg', hd1, -, hd2, -⟩ := (sctsW_ok vis0 T lo ll nP nIdx rs isP lg cvTaw lps cvTa hT hrs
    k _ a₀ cO cL cs hS hlps hlb hta hcs hA).run hm
  exact ⟨hl, hok, hS', hg', hd1, hd2⟩

end L.Ind
