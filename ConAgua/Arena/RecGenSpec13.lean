import ConAgua.Arena.RecGenSpec2
import ConAgua.Arena.IndPosSpec7
import ConAgua.Arena.IndPosMemo
import ConAgua.Arena.IndPos2SpecO

/-!
# `classKeyOf` (lane `indproofs3`, helper `indproofs3-pos-cls`)

`target_canon_params` (`replaceFVars (.canon pfvs)`, a `[3, pfvs]` map record, then the banked
walk), `class_key_canon` (its loop `class_key_canon_go`, a recursion writing into a fresh slice, as
`nest_seed_of_go`), `class_key_of` (the canonical key, then `class_key_of_closed`'s `allM`).
Every theorem takes the walk memos well formed in the memory at hand (`PosMR`) and returns them so.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The models -/

/-- **The model of `target_canon_params(pfo, pfl, e)`** at exec fuel `k + 1`. -/
def tcpW (k : Nat) (m : Mem) (pfo pfl e : Word) : Option (Word × Mem) :=
  match posRecW m [3, pfo, pfl] with
  | none => none
  | some (f, m1) => rxW k m1 f e

/-- `target_canon_params` at any exec fuel. -/
def tcpWf : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | k + 1, m, pfo, pfl, e => tcpW k m pfo pfl e

mutual
/-- **The model of `class_key_canon_go(po, pl, dO, dL, q, j)`.** -/
def ckgW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, po, pl, dO, dL, q, j =>
    if dL ≤ j then some m
    else ckgK k po pl dO dL q j (tcpWf k m po pl (rdW (m.arr64 IW) (dO + j)))
/-- After `target_canon_params`: write, recurse. -/
def ckgK (k : Nat) (po pl dO dL q j : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (z, m2) => ckgW k (m2.set64 IW (q + j) z) po pl dO dL q (j + 1)
end

section arms
variable (k : Nat) (m m2 : Mem) (po pl dO dL q j z : Word)
theorem ckgW_done (h : dL ≤ j) : ckgW (k + 1) m po pl dO dL q j = some m := by simp [ckgW, h]
theorem ckgW_step (h : ¬ dL ≤ j) : ckgW (k + 1) m po pl dO dL q j =
    ckgK k po pl dO dL q j (tcpWf k m po pl (rdW (m.arr64 IW) (dO + j))) := by simp [ckgW, h]
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

/-- After `class_key_of_closed`. -/
def kofK2 (k2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else some ([k2], m)
/-- After `class_key_canon`. -/
def kofK1 (k : Nat) (nP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => kofK2 (r.headD 0) (ckcW (k + 1) m nP (rdW (m.arr64 IW) (r.headD 0 + 2))
      (rdW (m.arr64 IW) (r.headD 0 + 3)))

/-- **The model of `class_key_of(nP, po, pl, key)`** at exec fuel `k + 2`. -/
def kofW (k : Nat) (m : Mem) (nP po pl key : Word) : Option (List Word × Mem) :=
  kofK1 k nP (kcW k m po pl key)

section arms2
variable (k : Nat) (m : Mem) (nP k2 : Word) (r : List Word)
theorem kofK2_fail (h : r.headD 0 = 0) : kofK2 k2 (some (r, m)) = none := by
  simp only [kofK2]; rw [if_pos h]
theorem kofK2_ok (h : ¬ r.headD 0 = 0) : kofK2 k2 (some (r, m)) = some ([k2], m) := by
  simp only [kofK2]; rw [if_neg h]
theorem kofK1_some : kofK1 k nP (some (r, m)) = kofK2 (r.headD 0) (ckcW (k + 1) m nP
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

/-! ## The `vcgen` specs -/

section spec
variable {p : Prog} (L : KofProg p)
include L

theorem tcp_spec (k : Nat) (s₀ : St) (pfo pfl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "target_canon_params" [pfo, pfl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ tcpW k s₀.mem pfo pfl e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have hrx := (rxSpec_all p L.rx k).2.2.2.2.2.2.2
  rw [invoke_eq _ L.tcp]
  simp only [callFn, targetCanonParams]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      posRec3_specW p L.rx.ha L.h3 k, hrx] <;>
    finish (gen := 20) [tcpW]

theorem tcp_specF (k : Nat) (s₀ : St) (pfo pfl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "target_canon_params" [pfo, pfl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ tcpWf k s₀.mem pfo pfl e = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases k with
  | zero => rw [invoke_eq _ L.tcp]; simp only [callFn, targetCanonParams]; vcgen [exec] <;> grind
  | succ k => exact tcp_spec L k s₀ pfo pfl e

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
        tcp_specF L k, ih] <;>
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

theorem kof_spec (k : Nat) (s₀ : St) (nP po pl key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 2)) "class_key_of" [nP, po, pl, key]
    ⦃fun r s' => LocEq s' s₀ ∧ kofW k s₀.mem nP po pl key = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.kof]
  simp only [callFn, classKeyOfL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      kc_spec L k, classKeyOfClosed_spec p L.kcl (k + 1)] <;>
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

theorem tcpW_ok (k : Nat) (m m' : Mem) (a : AState) (pfo pfl e z : Word) (pfvs : List EIdx)
    (h : tcpW k m pfo pfl e = some (z, m')) (hS : StageR dn vis fe m a)
    (hpf : decHL m pfo.toNat pfl.toNat = some pfvs) (hpb : pfo.toNat + pfl.toNat ≤ iwTop m) (he : H e)
    (hP : PosMR m) :
    ∃ a', (ConRon.Arena.targetCanonParams pfvs (decE e)).run a = .ok (decE z, a') ∧ H z ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ PosMR m' := by
  unfold tcpW at h
  cases hr1 : posRecW m [3, pfo, pfl] with
  | none => rw [hr1] at h; cases h
  | some p1 =>
  obtain ⟨f, m1⟩ := p1
  rw [hr1] at h
  simp only at h
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
  | zero => simp [tcpWf, ckgK] at h
  | succ k' =>
  simp only [tcpWf] at h
  cases htc : tcpW k' m po pl x with
  | none => rw [htc] at h; simp [ckgK] at h
  | some p2 =>
  obtain ⟨z, m2⟩ := p2
  rw [htc, ckgK_some] at h
  obtain ⟨a1, hr1, hzH, hS2, hg2, hP2⟩ := tcpW_ok dn fe vis k' m m2 a po pl x z pfvs htc hS
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
  simp only [except_ok_bind, StateT.run_bind]
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
  cases hal : allocW m (rdW (m.arr64 IW) (key + 3)) with
  | none => rw [hal] at h; cases h
  | some p1 =>
  obtain ⟨q, m1⟩ := p1
  rw [hal] at h
  simp only at h
  obtain ⟨hS1, hg1, hqd, hroom, htop1⟩ := hS.alloc hal
  have hqt : q.toNat = iwTop m := by simp only [iwTop, hqd]
  cases hgo : ckgW k m1 po pl (rdW (m.arr64 IW) (key + 2)) (rdW (m.arr64 IW) (key + 3)) q 0 with
  | none => rw [hgo] at h; simp [kcK] at h
  | some m2 =>
  rw [hgo] at h
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
  cases hr4 : posRecW m2 [rdW (m.arr64 IW) key, rdW (m.arr64 IW) (key + 1), q, rdW (m.arr64 IW) (key + 3)] with
  | none => rw [hr4] at h; simp at h
  | some p4 =>
  obtain ⟨nkw, m3⟩ := p4
  rw [hr4] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
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
  have r2 : rdW (m3.arr64 IW) (nkw + 2) = q := by
    have := hget3 2 (by simp)
    have e : (nkw + 2).toNat = nkw.toNat + 2 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; simp at this; rw [this]; rfl
  have r3 : rdW (m3.arr64 IW) (nkw + 3) = rdW (m.arr64 IW) (key + 3) := by
    have := hget3 3 (by simp)
    have e : (nkw + 3).toNat = nkw.toNat + 3 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; simp at this; rw [this]; rfl
  refine ⟨ckOfNk ⟨decI (rdW (m.arr64 IW) key), decI (rdW (m.arr64 IW) (key + 1)), ys⟩, a2, ?_,
    decCK_decB_of_nk (decNK_decB_of_in hdk hin), by simp only [List.headD_cons]; omega,
    by simp only [List.headD_cons]; rw [r2, r3]; have := hg3.1; omega, hS3, hg12.trans hg3, hP2.fr (posRecW_mfr hr4)⟩
  simp only [ConRon.Arena.classKeyCanon, StateT.run_bind, ckOfNk]
  rw [show (0 : Word).toNat = 0 from rfl, List.drop_zero] at hrun
  rw [hrun]
  simp only [except_ok_bind, hcd, hud]
  rfl

end rel

end L.Ind
