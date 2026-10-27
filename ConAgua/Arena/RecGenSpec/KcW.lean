import ConAgua.Arena.RecCheckSpec.EeW2
import ConAgua.Arena.RecGenSpec.CkcW
import ConAgua.Arena.RecGenSpec.KofProg

/-!
# KcW

`tcpPW`, `tcpPWf`, `ckgW`, `ckgK`, `ckgW_done`, `ckgW_step` and the lemmas only they use.
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

end spec

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

end rel

end L.Ind

end
