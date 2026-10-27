import ConAgua.Arena.IndSumSpec.CtlW
import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# CtorX

`sumAddNoOv`, `ctorX`, `ctorX_spec`, `sctsK6`, `sctsK5`, `sctsK4` and the lemmas only they use.
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

end L.Ind

end
