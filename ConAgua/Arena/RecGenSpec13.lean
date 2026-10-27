import ConAgua.Arena.RecGenSpec2
import ConAgua.Arena.IndPosSpec.GgW2
import ConAgua.Arena.IndPosSpec.SgGoW

/-!
# `classKeyOf` (lane `indproofs3`, helper `indproofs3-pos-cls`)

`target_canon_params` (`replaceFVars (.canon pfvs)`, a `[3, pfvs]` map record, then the banked
walk), `class_key_canon` (its loop `class_key_canon_go`, a recursion writing into a fresh slice, as
`nest_seed_of_go`), `class_key_of` (the canonical key, then `class_key_of_closed`'s `allM`).
Every theorem takes the walk memos well formed in the memory at hand (`PosMR`) and returns them so.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The models -/

/-- **The model of `target_canon_params(pfo, pfl, e)`** at exec fuel `k + 1`. -/
def tcpPW (k : Nat) (m : Mem) (pfo pfl e : Word) : Option (Word × Mem) :=
  match posRecW m [3, if pfl = 0 then 0 else pfo, pfl] with
  | none => none
  | some (f, m1) => rxW k m1 f e

/-- `target_canon_params` at any exec fuel. -/
def tcpPWf : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | k + 1, m, pfo, pfl, e => tcpPW k m pfo pfl e

mutual
/-- **The model of `class_key_canon_go(po, pl, dO, dL, q, j)`.** -/
def ckgW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, po, pl, dO, dL, q, j =>
    if dL ≤ j then some m
    else ckgK k po pl dO dL q j (tcpPWf k m po pl (rdW (m.arr64 IW) (dO + j)))
/-- After `target_canon_params`: write, recurse. -/
def ckgK (k : Nat) (po pl dO dL q j : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (z, m2) => ckgW k (m2.set64 IW (q + j) z) po pl dO dL q (j + 1)
end

section arms
variable (k : Nat) (m m2 : Mem) (po pl dO dL q j z : Word)
theorem ckgW_done (h : dL ≤ j) : ckgW (k + 1) m po pl dO dL q j = some m := by simp [ckgW, h]
theorem ckgW_step (h : ¬ dL ≤ j) : ckgW (k + 1) m po pl dO dL q j =
    ckgK k po pl dO dL q j (tcpPWf k m po pl (rdW (m.arr64 IW) (dO + j))) := by simp [ckgW, h]
theorem ckgK_some : ckgK k po pl dO dL q j (some (z, m2)) =
    ckgW k (m2.set64 IW (q + j) z) po pl dO dL q (j + 1) := by rw [ckgK]
end arms
attribute [ind_grind] ckgW_done ckgW_step ckgK_some

/-- After the loop: the record. -/
def kcK (key q dL : Word) : Option Mem → Option (List Word × Mem)
  | none => none
  | some m2 => match posRecW m2 [rdW (m2.arr64 IW) key, rdW (m2.arr64 IW) (key + 1), q, dL] with
    | none => none
    | some (nk, m3) => some ([nk], m3)

/-- **The model of `class_key_canon(po, pl, key)`** at exec fuel `k + 1`. -/
def kcW (k : Nat) (m : Mem) (po pl key : Word) : Option (List Word × Mem) :=
  match allocW m (rdW (m.arr64 IW) (key + 3)) with
  | none => none
  | some (q, m1) => kcK key q (rdW (m.arr64 IW) (key + 3))
      (ckgW k m1 po pl (rdW (m.arr64 IW) (key + 2)) (rdW (m.arr64 IW) (key + 3)) q 0)

mutual
/-- **The model of `class_key_of_closed`**, with `bvar_b` the master's walk (`bvbW`). -/
def ckc2W : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, nP, o, l =>
    if l = 0 then some ([1], m)
    else ckc2K1 n nP o l (rdW (m.arr64 IW) o) (bvbW n m (rdW (m.arr64 IW) o) CWF)
/-- After `bvar_b`. -/
def ckc2K1 (n : Nat) (nP o l e : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m1) =>
    if rb ≠ 0 then some ([0], m1) else ckc2K2 n nP o l (fvbF m1 [CWF, e])
/-- After `fvar_b`. -/
def ckc2K2 (n : Nat) (nP o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m2) =>
    if nP < rf.headD 0 then some ([0], m2) else ckcK3 (ckc2W n m2 nP (o + 1) (l - 1))
end

section arms0
variable (n : Nat) (m m1 m2 : Mem) (nP o l e rb : Word) (rf : List Word)
theorem ckc2W_nil (hl : l = 0) : ckc2W (n + 1) m nP o l = some ([1], m) := by simp [ckc2W, hl]
theorem ckc2W_cons (hl : l ≠ 0) : ckc2W (n + 1) m nP o l =
    ckc2K1 n nP o l (rdW (m.arr64 IW) o) (bvbW n m (rdW (m.arr64 IW) o) CWF) := by simp [ckc2W, hl]
theorem ckc2K1_open (h : rb ≠ 0) : ckc2K1 n nP o l e (some (rb, m1)) = some ([0], m1) := by
  rw [ckc2K1, ite_eq_left h]
theorem ckc2K1_closed (h : ¬ rb ≠ 0) :
    ckc2K1 n nP o l e (some (rb, m1)) = ckc2K2 n nP o l (fvbF m1 [CWF, e]) := by
  rw [ckc2K1, ite_eq_right h]
theorem ckc2K2_open (h : nP < rf.headD 0) : ckc2K2 n nP o l (some (rf, m2)) = some ([0], m2) := by
  rw [ckc2K2, ite_eq_left h]
theorem ckc2K2_closed (h : ¬ nP < rf.headD 0) :
    ckc2K2 n nP o l (some (rf, m2)) = ckcK3 (ckc2W n m2 nP (o + 1) (l - 1)) := by
  rw [ckc2K2, ite_eq_right h]
end arms0
attribute [ind_grind] ckc2W_nil ckc2W_cons ckc2K1_open ckc2K1_closed ckc2K2_open ckc2K2_closed

/-- After `class_key_of_closed`. -/
def kofK2 (k2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else some ([k2], m)
/-- After `class_key_canon`. -/
def kofK1 (k : Nat) (nP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => kofK2 (r.headD 0) (ckc2W (k + 1) m nP (rdW (m.arr64 IW) (r.headD 0 + 2))
      (rdW (m.arr64 IW) (r.headD 0 + 3)))

/-- **The model of `class_key_of(nP, po, pl, key)`** at exec fuel `k + 2`. -/
def kofW (k : Nat) (m : Mem) (nP po pl key : Word) : Option (List Word × Mem) :=
  kofK1 k nP (kcW k m po pl key)

section arms2
variable (k : Nat) (m : Mem) (nP k2 : Word) (r : List Word)
theorem kofK2_fail (h : r.headD 0 = 0) : kofK2 k2 (some (r, m)) = none := by
  simp only [kofK2]; rw [ite_eq_left h]
theorem kofK2_ok (h : ¬ r.headD 0 = 0) : kofK2 k2 (some (r, m)) = some ([k2], m) := by
  simp only [kofK2]; rw [ite_eq_right h]
theorem kofK1_some : kofK1 k nP (some (r, m)) = kofK2 (r.headD 0) (ckc2W (k + 1) m nP
    (rdW (m.arr64 IW) (r.headD 0 + 2)) (rdW (m.arr64 IW) (r.headD 0 + 3))) := rfl
end arms2
attribute [ind_grind] kofK2_fail kofK2_ok kofK1_some

/-- The lookups of `class_key_of`. -/
structure KofProg (p : Prog) : Prop where
  rx : RxLook p
  h3 : p.lookup "rec3" = some rec3
  tcp : p.lookup "target_canon_params" = some targetCanonParams
  go : p.lookup "class_key_canon_go" = some classKeyCanonGo
  kc : p.lookup "class_key_canon" = some classKeyCanonL
  kcl : p.lookup "class_key_of_closed" = some classKeyOfClosed
  kof : p.lookup "class_key_of" = some classKeyOfL
  bvb : BvbProg p
  hf : HfF p

/-! ## The `vcgen` specs -/

section spec
variable {p : Prog} (L : KofProg p)
include L

theorem tcpP_spec (k : Nat) (s₀ : St) (pfo pfl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "target_canon_params" [pfo, pfl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ tcpPW k s₀.mem pfo pfl e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have hrx := (rxSpec_all p L.rx k).2.2.2.2.2.2.2
  rw [invoke_eq _ L.tcp]
  simp only [callFn, targetCanonParams]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      posRec3_specW p L.rx.ha L.h3 k, hrx] <;>
    finish (gen := 20) [tcpPW]

theorem tcpP_specF (k : Nat) (s₀ : St) (pfo pfl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "target_canon_params" [pfo, pfl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ tcpPWf k s₀.mem pfo pfl e = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases k with
  | zero => rw [invoke_eq _ L.tcp]; simp only [callFn, targetCanonParams]; vcgen [exec] <;> grind
  | succ k => exact tcpP_spec L k s₀ pfo pfl e

theorem ckg_spec (k : Nat) : ∀ (s₀ : St) (po pl dO dL q j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "class_key_canon_go" [po, pl, dO, dL, q, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ ckgW k s₀.mem po pl dO dL q j = some s'.mem; ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ po pl dO dL q j
    rw [invoke_eq _ L.go]; simp only [callFn, classKeyCanonGo]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ po pl dO dL q j
    rw [invoke_eq _ L.go]
    simp only [callFn, classKeyCanonGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        tcpP_specF L k, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem kc_spec (k : Nat) (s₀ : St) (po pl key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "class_key_canon" [po, pl, key]
    ⦃fun r s' => LocEq s' s₀ ∧ kcW k s₀.mem po pl key = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.kc]
  simp only [callFn, classKeyCanonL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      iwAlloc_specW p L.rx.ha k, ckg_spec L k, posRec4_specW p L.rx.ha L.rx.h4 k] <;>
    finish (gen := 20) [kcW, kcK, rdW_eq]

theorem ckc2_spec (k : Nat) : ∀ (s₀ : St) (nP o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "class_key_of_closed" [nP, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ckc2W k s₀.mem nP o l = some (r, s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ nP o l; rw [invoke_eq _ L.kcl]; simp only [callFn, classKeyOfClosed]
    vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ nP o l
    rw [invoke_eq _ L.kcl]
    simp only [callFn, classKeyOfClosed]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        bvarBL_spec p L.bvb k, fvbF_spec p L.hf k, ih] <;>
      finish (gen := 20)

theorem kof_spec (k : Nat) (s₀ : St) (nP po pl key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 2)) "class_key_of" [nP, po, pl, key]
    ⦃fun r s' => LocEq s' s₀ ∧ kofW k s₀.mem nP po pl key = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.kof]
  simp only [callFn, classKeyOfL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      kc_spec L k, ckc2_spec L (k + 1)] <;>
    finish (gen := 20) [kofW, rdW_eq]

end spec

/-! ## Class keys as nest keys (the same layout) -/

/-- A `NestKey` read as a `ClassKey`. -/
def ckOfNk (n : NestKey) : ClassKey := ⟨n.cname, n.lvls, n.ds⟩

theorem decCK_eq (m : Mem) (k : Nat) : decCK m k = (decNK m k).map ckOfNk := by
  simp only [decCK, decNK, Option.bind_eq_bind, Option.pure_def]
  cases (iwH m k : Option NIdx) <;> simp
  cases (iwH m (k + 1) : Option LsIdx) <;> simp
  cases (decAt m (decHL m) (k + 2) : Option (List EIdx)) <;> simp [ckOfNk]

theorem decCK_decB_nk {m : Mem} {k : Nat} {ck : ClassKey} (h : DecB (fun m => decCK m k) m ck) :
    ∃ nk, DecB (fun m => decNK m k) m nk ∧ ckOfNk nk = ck := by
  have h' : decCK (truncM m) k = some ck := h
  rw [decCK_eq, Option.map_eq_some_iff] at h'
  obtain ⟨nk, h1, h2⟩ := h'
  exact ⟨nk, h1, h2⟩

theorem decNK_decB_of_in {m : Mem} {k : Nat} {nk : NestKey} (h : decNK m k = some nk)
    (hin : NKIn m k (· < iwTop m)) : DecB (fun m => decNK m k) m nk := by
  show decNK (truncM m) k = some nk
  rw [(hin.agree (m' := truncM m) (fun i hi => by simpa [iwA] using truncM_iw_eq hi)).1]; exact h

theorem decCK_decB_of_nk {m : Mem} {k : Nat} {nk : NestKey} (h : DecB (fun m => decNK m k) m nk) :
    DecB (fun m => decCK m k) m (ckOfNk nk) := by
  show decCK (truncM m) k = some (ckOfNk nk)
  rw [decCK_eq]; have h' : decNK (truncM m) k = some nk := h; rw [h']; rfl

/-! ## The relational side -/

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem tcpPW_ok (k : Nat) (m m' : Mem) (a : AState) (pfo pfl e z : Word) (pfvs : List EIdx)
    (h : tcpPW k m pfo pfl e = some (z, m')) (hS : StageR dn vis fe m a)
    (hpf : decHL m pfo.toNat pfl.toNat = some pfvs) (hpb : pfo.toNat + pfl.toNat ≤ iwTop m) (he : H e)
    (hP : PosMR m) :
    ∃ a', (ConRon.Arena.targetCanonParams pfvs (decE e)).run a = .ok (decE z, a') ∧ H z ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ PosMR m' := by
  unfold tcpPW at h
  -- the openers' offset as recorded: `0` for an empty slice
  obtain ⟨po, hpo, hpf, hpb⟩ : ∃ po : Word, po = (if pfl = 0 then 0 else pfo) ∧
      decHL m po.toNat pfl.toNat = some pfvs ∧ po.toNat + pfl.toNat ≤ iwTop m := by
    by_cases h0 : pfl = 0
    · subst h0
      have hx : pfvs = [] := by simpa [decHL, hslice?] using hpf.symm
      subst hx
      exact ⟨0, by simp, by simp [decHL, hslice?], by simp⟩
    · exact ⟨pfo, by simp [h0], hpf, hpb⟩
  rw [← hpo] at h
  rcases hr1 : posRecW m [3, po, pfl] with _ | ⟨f, m1⟩ <;> simp only [hr1, reduceCtorEq] at h
  obtain ⟨hS1, hg1, hf1, ht1, hget1⟩ := posRecW_stage hr1 hS (by simp)
  simp only [List.length_cons, List.length_nil] at ht1
  have g0 := iwN_of_get (by simpa using hget1 0 (by simp))
  have g1 := iwN_of_get (by simpa using hget1 1 (by simp))
  have g2 := iwN_of_get (by simpa using hget1 2 (by simp))
  have hfm : FMOk m1 f.toNat (.canon pfvs) :=
    ⟨by simpa using g0, by omega, ⟨_, _, g1, g2, by rw [decHL_grow hg1 hpb]; exact hpf,
      by have := hg1.1; omega⟩⟩
  have hP1 := hP.fr (posRecW_mfr hr1)
  obtain ⟨M, G, g, hR⟩ := hP1.rf
  obtain ⟨a', hrun, hzH, M', G', hS', hg2, hR', -, -⟩ :=
    (rxOK_all dn fe vis k).2.2.2.2.2.2 m1 m' a f e _ z M G g h hS1 hfm he hR
  exact ⟨a', hrun, hzH, hS', hg1.trans hg2, hP1.setRf (rxW_mfr h) ⟨M', G', g, hR'⟩⟩

theorem ckgW_ok (k : Nat) :
    ∀ (m0 m m' : Mem) (a : AState) (po pl dO dL q j : Word) (pfvs ds acc : List EIdx),
    ckgW k m po pl dO dL q j = some m' → StageR dn vis fe m a → IWGrow m0 m → iwTop m0 ≤ q.toNat →
    q.toNat + dL.toNat ≤ iwTop m → decHL m0 po.toNat pl.toNat = some pfvs →
    po.toNat + pl.toNat ≤ iwTop m0 → decHL m0 dO.toNat dL.toNat = some ds →
    (∀ i < dL.toNat, dO.toNat + i < iwTop m0) → j.toNat ≤ dL.toNat →
    decHL m q.toNat j.toNat = some acc → PosMR m →
    ∃ ys a', ((ds.drop j.toNat).mapM (ConRon.Arena.targetCanonParams pfvs)).run a = .ok (ys, a') ∧
      decHL m' q.toNat dL.toNat = some (acc ++ ys) ∧ StageR dn vis fe m' a' ∧ IWGrow m0 m' ∧
      iwTop m ≤ iwTop m' ∧ PosMR m' := by
  induction k with
  | zero => intro m0 m m' a po pl dO dL q j pfvs ds acc h; simp [ckgW] at h
  | succ k ih =>
  intro m0 m m' a po pl dO dL q j pfvs ds acc h hS hg0 hq0 hql hpf hpb hds hdsb hj hacc hP
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hxl := decHL_length m0 hds
  by_cases hd : dL ≤ j
  · rw [ckgW_done (h := hd)] at h
    cases h
    have hjl : j.toNat = dL.toNat := by have := UInt64.le_iff_toNat_le.mp hd; omega
    refine ⟨[], a, ?_, by rw [← hjl]; simpa using hacc, hS, hg0, Nat.le_refl _, hP⟩
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  rw [ckgW_step (h := hd)] at h
  have hjl : j.toNat < dL.toNat := by
    have : ¬ dL.toNat ≤ j.toNat := fun e => hd (UInt64.le_iff_toNat_le.mpr e)
    omega
  have hoj := hdsb j.toNat hjl
  obtain ⟨hxH, hxd⟩ := rd_iwH (m := m) (p := dO) (i := j)
    (by rw [iwH_agree (RdS.of_grow hg0) hoj]; exact decHL_getI hds _ hjl) (by have := hg0.1; omega)
  generalize rdW (m.arr64 IW) (dO + j) = x at h hxH hxd
  cases k with
  | zero => simp [tcpPWf, ckgK] at h
  | succ k' =>
  simp only [tcpPWf] at h
  obtain ⟨⟨z, m2⟩, htc, h⟩ := of_K h (by simp only [ckgK])
  rw [ckgK_some] at h
  obtain ⟨a1, hr1, hzH, hS2, hg2, hP2⟩ := tcpPW_ok dn fe vis k' m m2 a po pl x z pfvs htc hS
    (by rw [decHL_grow hg0 hpb]; exact hpf) (by have := hg0.1; omega) hxH hP
  have hqj : (q + j).toNat = q.toNat + j.toNat := word_add_toNat (by omega)
  have hj1 : (j + 1).toNat = j.toNat + 1 := word_add_toNat (show j.toNat + 1 < 2 ^ 64 by have := dL.toNat_lt; omega)
  have hacc2 : decHL m2 q.toNat j.toNat = some acc := by rw [decHL_grow hg2 (by omega)]; exact hacc
  have hdec3 := decHL_write m2 q j z acc hzH hS2.2.2.2.1 (by have := hS2.2.1; have := hg2.1; omega) hacc2
  have hS3 := hS2.set_iw (q + j) z
  have hg03 : IWGrow m0 (m2.set64 IW (q + j) z) := (hg0.trans hg2).set_iw (q + j) z (by omega)
  have ht3 : iwTop (m2.set64 IW (q + j) z) = iwTop m2 := by
    simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  obtain ⟨ys, a', hrun, hdec', hS', hg', ht', hP'⟩ := ih m0 _ m' a1 po pl dO dL q (j + 1) pfvs ds
    (acc ++ [decE z]) h hS3 hg03 hq0 (by rw [ht3]; have := hg2.1; omega) hpf hpb hds hdsb
    (by rw [hj1]; omega) (by rw [hj1]; exact hdec3) (hP2.fr (MFr.set_iw _ _ _))
  refine ⟨decE z :: ys, a', ?_, by simpa using hdec', hS', hg', by have := hg2.1; omega, hP'⟩
  rw [List.drop_eq_getElem_cons (show j.toNat < ds.length by omega), List.mapM_cons]
  simp only [StateT.run_bind]
  rw [← hxd, show (decI x : EIdx) = decE x from rfl, hr1]
  simp only [except_ok_bind]
  rw [hj1] at hrun
  rw [hrun]
  rfl

/-- **`class_key_canon`'s model simulates `classKeyCanon`**: the key decoded below the tops, the
canonical parameters a slice below the top. -/
theorem kcW_ok (k : Nat) (m m' : Mem) (a : AState) (po pl key : Word) (r : List Word) (pfvs : List EIdx)
    (ck : ClassKey) (h : kcW k m po pl key = some (r, m')) (hS : StageR dn vis fe m a)
    (hpf : decHL m po.toNat pl.toNat = some pfvs) (hpb : po.toNat + pl.toNat ≤ iwTop m)
    (hk : DecB (fun m => decCK m key.toNat) m ck) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.classKeyCanon pfvs ck).run a = .ok (x, a') ∧ DecB (fun m => decCK m (r.headD 0).toNat) m' x ∧
      (r.headD 0).toNat + 4 ≤ iwTop m' ∧
      (rdW (m'.arr64 IW) (r.headD 0 + 2)).toNat + (rdW (m'.arr64 IW) (r.headD 0 + 3)).toNat ≤ iwTop m' ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PosMR m' := by
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨nk, hnk, rfl⟩ := decCK_decB_nk hk
  obtain ⟨hcH, hcd, huH, hud, hds, hdsb, hk4⟩ := pos2_nk_fields hnk htop
  unfold kcW at h
  rcases hal : allocW m (rdW (m.arr64 IW) (key + 3)) with _ | ⟨q, m1⟩ <;> simp only [hal, reduceCtorEq] at h
  obtain ⟨hS1, hg1, hqd, hroom, htop1⟩ := hS.alloc hal
  have hqt : q.toNat = iwTop m := by simp only [iwTop, hqd]
  obtain ⟨m2, hgo, h⟩ := of_K h rfl
  obtain ⟨ys, a2, hrun, hdec2, hS2, hg12, ht2, hP2⟩ := ckgW_ok dn fe vis k m m1 m2 a po pl _ _ q 0 pfvs nk.ds []
    hgo hS1 hg1 (by omega) (by omega) hpf hpb hds hdsb (by simp) (by simp [decHL, hslice?])
    (hP.fr (allocW_mfr hal))
  simp only [kcK] at h
  have e0 : rdW (m2.arr64 IW) key = rdW (m.arr64 IW) key := by
    simp only [rdW]; rw [hg12.2.2.1 _ (by omega)]
  have e1 : rdW (m2.arr64 IW) (key + 1) = rdW (m.arr64 IW) (key + 1) := by
    have e : (key + 1).toNat = key.toNat + 1 := word_add_toNat (by simp; omega)
    simp only [rdW]; rw [e, hg12.2.2.1 _ (by omega)]
  rw [e0, e1] at h
  rcases hr4 : posRecW m2 [rdW (m.arr64 IW) key, rdW (m.arr64 IW) (key + 1), q, rdW (m.arr64 IW) (key + 3)]
    with _ | ⟨nkw, m3⟩ <;> simp only [hr4, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS3, hg3, hk3, ht3, hget3⟩ := posRecW_stage hr4 hS2 (by simp)
  simp only [List.length_cons, List.length_nil] at ht3
  have hqb : q.toNat + (rdW (m.arr64 IW) (key + 3)).toNat ≤ iwTop m2 := by have := hg12.1; omega
  have hdk : decNK m3 nkw.toNat = some ⟨decI (rdW (m.arr64 IW) key), decI (rdW (m.arr64 IW) (key + 1)), ys⟩ :=
    decNK_of_words (by simpa using hget3 0 (by simp)) hcH (hget3 1 (by simp)) huH (hget3 2 (by simp))
      (hget3 3 (by simp)) (by rw [decHL_grow hg3 hqb]; simpa using hdec2)
  have hin : NKIn m3 nkw.toNat (· < iwTop m3) := by
    refine ⟨fun j hj => by omega, fun o l ho hl j hj => ?_⟩
    have e2 := iwN_of_get (m := m3) (by simpa using hget3 2 (by simp))
    have e3 := iwN_of_get (m := m3) (by simpa using hget3 3 (by simp))
    rw [e2] at ho; rw [e3] at hl
    cases ho; cases hl
    have := hg3.1; omega
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  have rk (j : Nat) (hj : j < 4) : rdW (m3.arr64 IW) (nkw + UInt64.ofNat j) =
      [rdW (m.arr64 IW) key, rdW (m.arr64 IW) (key + 1), q, rdW (m.arr64 IW) (key + 3)][j]'(by simpa using hj) := by
    have := hget3 j (by simpa using hj)
    have hj' : (UInt64.ofNat j : Word).toNat = j := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    have e : (nkw + UInt64.ofNat j).toNat = nkw.toNat + j := by rw [word_add_toNat (by rw [hj']; omega), hj']
    simp only [rdW, e]; rw [this, List.getElem?_eq_getElem]; rfl
  have r2 : rdW (m3.arr64 IW) (nkw + 2) = q := rk 2 (by decide)
  have r3 : rdW (m3.arr64 IW) (nkw + 3) = rdW (m.arr64 IW) (key + 3) := rk 3 (by decide)
  refine ⟨ckOfNk ⟨decI (rdW (m.arr64 IW) key), decI (rdW (m.arr64 IW) (key + 1)), ys⟩, a2, ?_,
    decCK_decB_of_nk (decNK_decB_of_in hdk hin), by simp only [List.headD_cons]; omega,
    by simp only [List.headD_cons]; rw [r2, r3]; have := hg3.1; omega, hS3, hg12.trans hg3, hP2.fr (posRecW_mfr hr4)⟩
  simp only [ConRon.Arena.classKeyCanon, StateT.run_bind, ckOfNk]
  rw [show (0 : Word).toNat = 0 from rfl, List.drop_zero] at hrun
  rw [hrun]
  simp only [except_ok_bind, hcd, hud]
  rfl

theorem ckc2W_mfr : ∀ (n : Nat) (m m' : Mem) (nP o l : Word) (r : List Word),
    ckc2W n m nP o l = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [ckc2W] at h
  | n + 1, m, m', nP, o, l, r, h => by
    by_cases hl : l = 0
    · rw [ckc2W_nil n m nP o l hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [ckc2W_cons n m nP o l hl] at h
    obtain ⟨⟨rb, m1⟩, h1, h⟩ := of_K h (by simp only [ckc2K1])
    refine (bvbW_mfr h1).trans ?_
    by_cases hb : rb ≠ 0
    · rw [ckc2K1_open (h := hb)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [ckc2K1_closed (h := hb)] at h
    obtain ⟨⟨rf, m2⟩, h2, h⟩ := of_K h (by simp only [ckc2K2])
    refine (MFr.ofFvbF h2).trans ?_
    by_cases hf : nP < rf.headD 0
    · rw [ckc2K2_open (h := hf)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [ckc2K2_closed (h := hf)] at h
    obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl
    rw [ckcK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact ckc2W_mfr n _ _ _ _ _ _ h3

theorem ckc2W_ok (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (nP o l : Word) (xs : List EIdx) (r : List Word),
    ckc2W n m nP o l = some (r, m') → StageR dn vis fe m a → decHL m o.toNat l.toNat = some xs →
    o.toNat + l.toNat < 2 ^ 64 → o.toNat + l.toNat ≤ iwTop m →
    ∃ b a', (xs.allM (keyClosedTest nP.toNat)).run a = .ok (b, a') ∧
      KeepPost dn vis fe decW0B m m' a' r b := by
  induction n with
  | zero => intro m m' a nP o l xs r h; simp [ckc2W] at h
  | succ n ih =>
    intro m m' a nP o l xs r h hS hd hb ht
    by_cases hl : l = 0
    · subst hl
      rw [ckc2W_nil n m nP o 0 rfl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : xs = [] := by simpa [decHL, hslice?] using hd.symm
      subst this
      exact ⟨true, a, rfl, hS, IWGrow.refl m, by simp [decW0B]⟩
    · obtain ⟨w, xs', rfl, hw, hw32, hd'⟩ := decHL_cons hd hl hb
      obtain ⟨hsum, -⟩ := toNat_succ_of_lt hb hl
      rw [ckc2W_cons n m nP o l hl, hw] at h
      obtain ⟨⟨rb, m1⟩, h2, h⟩ := of_K h (by simp only [ckc2K1])
      obtain ⟨a1, hrun1, hS1, hg1, -⟩ := bvbW_stageW dn vis fe hS n coreWalkFuel CWF (.inl (Nat.le_of_eq CWF_eq)) w rb hw32 h2
      by_cases hz : rb ≠ 0
      · rw [ckc2K1_open n m1 nP o l w rb hz] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hk : rb.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp (by simpa using e))
        refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
        simp only [List.allM_cons, StateT.run_bind, keyClosedTest]
        rw [show (decI w : EIdx) = decE w from rfl, hrun1]
        simp only [bind, Except.bind, hk, bne_iff_ne, ne_eq, not_false_eq_true, ite_true]
        rfl
      · rw [ckc2K1_closed n m1 nP o l w rb hz] at h
        have hk : rb.toNat = 0 := by rw [show rb = 0 by simpa using hz]; rfl
        obtain ⟨⟨rf, m2⟩, h3, h⟩ := of_K h (by simp only [ckc2K2])
        obtain ⟨kf, a2, hrun2, hS2, hg2, hkf⟩ := fvbF_ok dn vis fe CWF w hw32 m1 m2 a1 rf h3 hS1
        rw [CWF_eq] at hrun2
        have hg12 := hg1.trans hg2
        have hlt : (nP < rf.headD 0) ↔ ¬ kf ≤ nP.toNat := by
          rw [UInt64.lt_iff_toNat_lt, hkf]; omega
        have hrunT : (keyClosedTest nP.toNat (decI w)).run a = .ok (decide (kf ≤ nP.toNat), a2) := by
          simp only [keyClosedTest, StateT.run_bind]
          rw [show (decI w : EIdx) = decE w from rfl, hrun1]
          simp only [bind, Except.bind, hk, bne_self_eq_false, Bool.false_eq_true, ite_false]
          simp only [StateT.bind, StateT.run] at hrun2 ⊢
          rw [show (decE w : EIdx) = decI w from rfl, hrun2]
          rfl
        by_cases hn' : nP < rf.headD 0
        · rw [ckc2K2_open n m2 nP o l rf hn'] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          have hn'' := hlt.mp hn'
          refine ⟨false, a2, ?_, hS2, hg12, by simp [decW0B]⟩
          simp only [List.allM_cons, StateT.run_bind]
          rw [hrunT]
          simp only [bind, Except.bind, hn'', decide_false, Bool.false_eq_true, ite_false]
          rfl
        · rw [ckc2K2_closed n m2 nP o l rf hn'] at h
          have hn'' : kf ≤ nP.toNat := by have := mt hlt.mpr hn'; omega
          obtain ⟨⟨r4, m3⟩, h4, h⟩ := of_K h rfl
          rw [ckcK3_some] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          obtain ⟨b3, a3, hrun3, hS3, hg3, hd3, hd31⟩ := ih m2 m3 a2 nP (o + 1) (l - 1) xs' r4 h4 hS2
            (by rw [decHL_grow hg12 (by omega)]; exact hd') (by omega) (by have := hg12.1; omega)
          refine ⟨b3, a3, ?_, hS3, hg12.trans hg3, by simpa [decW0B] using And.intro hd3 hd31⟩
          simp only [List.allM_cons, StateT.run_bind]
          rw [hrunT]
          simp only [bind, Except.bind, hn'', decide_true, ite_true]
          exact hrun3

/-- **`class_key_of`'s model simulates `classKeyOf`.** -/
theorem kofW_ok (k : Nat) (m m' : Mem) (a : AState) (nP po pl key : Word) (r : List Word)
    (pfvs : List EIdx) (ck : ClassKey) (h : kofW k m nP po pl key = some (r, m')) (hS : StageR dn vis fe m a)
    (hpf : decHL m po.toNat pl.toNat = some pfvs) (hpb : po.toNat + pl.toNat ≤ iwTop m)
    (hk : DecB (fun m => decCK m key.toNat) m ck) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.classKeyOf nP.toNat pfvs ck).run a = .ok (x, a') ∧
      DecB (fun m => decCK m (r.headD 0).toNat) m' x ∧ (r.headD 0).toNat + 4 ≤ iwTop m' ∧
      (rdW (m'.arr64 IW) (r.headD 0 + 2)).toNat + (rdW (m'.arr64 IW) (r.headD 0 + 3)).toNat ≤ iwTop m' ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PosMR m' := by
  unfold kofW at h
  obtain ⟨⟨r1, m1⟩, hc, h⟩ := of_K h rfl
  rw [kofK1_some] at h
  obtain ⟨x1, a1, hrun1, hd1, hb1, hds1, hS1, hg1, hP1⟩ := kcW_ok dn fe vis k m m1 a po pl key r1 pfvs ck hc hS hpf hpb hk hP
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨nk, hnk, rfl⟩ := decCK_decB_nk hd1
  obtain ⟨-, -, -, -, hds, -, -⟩ := pos2_nk_fields hnk htop1
  obtain ⟨⟨r2, m2⟩, hcl, h⟩ := of_K h rfl
  obtain ⟨b, a2, hrun2, hS2, hg2, hb2, -⟩ := ckc2W_ok dn fe vis (k + 1) m1 m2 a1 nP _ _ nk.ds r2 hcl hS1 hds
    (by omega) hds1
  by_cases h0 : r2.headD 0 = 0
  · rw [kofK2_fail (h := h0)] at h; cases h
  rw [kofK2_ok (h := h0)] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hbt : b = true := by rw [← hb2]; exact bne_iff_ne.mpr h0
  subst hbt
  refine ⟨ckOfNk nk, a2, ?_, ?_, by simpa using (by have := hg2.1; omega : (r1.headD 0).toNat + 4 ≤ iwTop m2), ?_,
    hS2, hg1.trans hg2, hP1.fr (ckc2W_mfr _ _ _ _ _ _ _ hcl)⟩
  · simp only [ConRon.Arena.classKeyOf, StateT.run_bind]
    rw [hrun1]
    simp only [except_ok_bind]
    have e : (ckOfNk nk).ds = nk.ds := rfl
    have hr2' : ((ckOfNk nk).ds.allM fun x => do
        if (← bvarB coreWalkFuel x) != 0 then pure false
        else pure ((← fvarB coreWalkFuel x) ≤ nP.toNat)).run a1 = .ok (true, a2) := hrun2
    rw [hr2']
    rfl
  · simpa using hd1.grow (decCK_mono _) hg2
  · have ek (j : Word) (hj : j.toNat < 4) :
        rdW (m2.arr64 IW) (r1.headD 0 + j) = rdW (m1.arr64 IW) (r1.headD 0 + j) := by
      simp only [rdW, word_add_toNat (show (r1.headD 0).toNat + j.toNat < 2 ^ 64 by omega)]
      rw [hg2.2.2.1 _ (by omega)]
    simp only [List.headD_cons]; rw [ek 2 (by decide), ek 3 (by decide)]; have := hg2.1; omega

end rel

/-! ## Census -/

section census
variable {p : Prog} (L : KofProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
include L

/-- **`target_canon_params` refines `targetCanonParams`** (`replace_fvars` through its `mk_app_n`
stub): the parameters a slice below the top, the walk memos well formed before and after. -/
@[refines ConRon.Arena.targetCanonParams]
theorem targetCanonParams_refinesP (k : Nat) (s₀ : St) (a₀ : AState) (pfo pfl e : Word) (pfvs : List EIdx)
    (hS : StageR dn vis fe s₀.mem a₀) (hpf : decHL s₀.mem pfo.toNat pfl.toNat = some pfvs)
    (hpb : pfo.toNat + pfl.toNat ≤ iwTop s₀.mem) (he : H e) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "target_canon_params" [pfo, pfl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀ ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀ ∧ H (r.headD 0) ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post (tcpP_spec L k s₀ pfo pfl e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hH, hS', hg, hP'⟩ := tcpPW_ok dn fe vis k _ _ a₀ pfo pfl e _ pfvs hm hS hpf hpb he hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres], hH, by rw [hst]; exact hS', hg, hP'⟩

/-- **`class_key_canon` refines `classKeyCanon`** (through `replace_fvars`' stub): the key decoded
below the tops, the canonical parameters a slice below the top; the canonical key a fresh record
decoded below the tops, its parameter slice below the top. -/
@[refines ConRon.Arena.classKeyCanon]
theorem classKeyCanon_refines (k : Nat) (s₀ : St) (a₀ : AState) (po pl key : Word) (pfvs : List EIdx)
    (ck : ClassKey) (hS : StageR dn vis fe s₀.mem a₀) (hpf : decHL s₀.mem po.toNat pl.toNat = some pfvs)
    (hpb : po.toNat + pl.toNat ≤ iwTop s₀.mem) (hk : DecB (fun m => decCK m key.toNat) s₀.mem ck)
    (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "class_key_canon" [po, pl, key]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classKeyCanon pfvs ck) a₀ ∧
      DecB (fun m => decCK m (r.headD 0).toNat) s'.mem (AM.res (ConRon.Arena.classKeyCanon pfvs ck) a₀) ∧
      (r.headD 0).toNat + 4 ≤ iwTop s'.mem ∧
      (rdW (s'.mem.arr64 IW) (r.headD 0 + 2)).toNat + (rdW (s'.mem.arr64 IW) (r.headD 0 + 3)).toNat ≤
        iwTop s'.mem ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classKeyCanon pfvs ck) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post (kc_spec L k s₀ po pl key) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, h1, h2, h3, h4, h5, h6⟩ := kcW_ok dn fe vis k _ _ a₀ po pl key r pfvs ck hm hS hpf hpb hk hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact h1, h2, h3, by rw [hst]; exact h4, h5, h6⟩

/-- **`class_key_of` refines `classKeyOf`** (through `replace_fvars`' and `fvar_b`'s stubs;
`bvar_b` the master's walk, at exec fuel below `coreWalkFuel`). -/
@[refines ConRon.Arena.classKeyOf]
theorem classKeyOf_refines (k : Nat) (s₀ : St) (a₀ : AState)
    (nP po pl key : Word) (pfvs : List EIdx) (ck : ClassKey) (hS : StageR dn vis fe s₀.mem a₀)
    (hpf : decHL s₀.mem po.toNat pl.toNat = some pfvs) (hpb : po.toNat + pl.toNat ≤ iwTop s₀.mem)
    (hk : DecB (fun m => decCK m key.toNat) s₀.mem ck) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 2)) "class_key_of" [nP, po, pl, key]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classKeyOf nP.toNat pfvs ck) a₀ ∧
      DecB (fun m => decCK m (r.headD 0).toNat) s'.mem (AM.res (ConRon.Arena.classKeyOf nP.toNat pfvs ck) a₀) ∧
      (r.headD 0).toNat + 4 ≤ iwTop s'.mem ∧
      (rdW (s'.mem.arr64 IW) (r.headD 0 + 2)).toNat + (rdW (s'.mem.arr64 IW) (r.headD 0 + 3)).toNat ≤
        iwTop s'.mem ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classKeyOf nP.toNat pfvs ck) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post (kof_spec L k s₀ nP po pl key) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, h1, h2, h3, h4, h5, h6⟩ :=
    kofW_ok dn fe vis k _ _ a₀ nP po pl key r pfvs ck hm hS hpf hpb hk hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact h1, h2, h3, by rw [hst]; exact h4, h5, h6⟩

end census

end L.Ind
