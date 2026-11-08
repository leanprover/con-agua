module

public import ConAgua.Arena.RecGenSpec.CkcW
public import ConAgua.Arena.RecGenSpec.KofProg
import ConAgua.Arena.IndPosSpec.GgW2
import ConAgua.Arena.IndPosSpec.SgGoW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPosSpec.DecNHFields
import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndPosSpec.MapOKStep
import ConAgua.Arena.IndPosSpec.PosmemoRxMfr
import ConAgua.Arena.IndPosSpec.Rx
public import ConAgua.Arena.IndPosSpec.BvbWMfr
import all ConAgua.Arena.RecCheck
import all ConAgua.Arena.RecGen

@[expose] public section

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

/-- `class_key_canon` at any exec fuel. -/
def kcWf : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | k + 1, m, po, pl, key => kcW k m po pl key

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
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
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
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        tcpP_specF L k, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem kc_spec (k : Nat) (s₀ : St) (po pl key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "class_key_canon" [po, pl, key]
    ⦃fun r s' => LocEq s' s₀ ∧ kcW k s₀.mem po pl key = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.kc]
  simp only [callFn, classKeyCanonL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      iwAlloc_specW p L.rx.ha k, ckg_spec L k, posRec4_specW p L.rx.ha L.rx.h4 k] <;>
    finish (gen := 20) [kcW, kcK, rdW_eq]

theorem kc_specF (k : Nat) (s₀ : St) (po pl key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "class_key_canon" [po, pl, key]
    ⦃fun r s' => LocEq s' s₀ ∧ kcWf k s₀.mem po pl key = some (r, s'.mem); ⊤⦄ := by
  cases k with
  | zero => rw [invoke_eq _ L.kc]; simp only [callFn, classKeyCanonL]; vcgen [exec] <;> grind
  | succ k => exact kc_spec L k s₀ po pl key

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
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
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
    (h : tcpPW k m pfo pfl e = some (z, m')) (hS : StageR vis fe m a)
    (hpf : decHL m pfo.toNat pfl.toNat = some pfvs) (hpb : pfo.toNat + pfl.toNat ≤ iwTop m) (he : H e)
    (hP : PosMR m) :
    ∃ a', (ConRon.Arena.targetCanonParams pfvs (decE e)).run a = .ok (decE z, a') ∧ H z ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ PosMR m' := by
  sorry

theorem ckgW_ok (k : Nat) :
    ∀ (m0 m m' : Mem) (a : AState) (po pl dO dL q j : Word) (pfvs ds acc : List EIdx),
    ckgW k m po pl dO dL q j = some m' → StageR vis fe m a → IWGrow m0 m → iwTop m0 ≤ q.toNat →
    q.toNat + dL.toNat ≤ iwTop m → decHL m0 po.toNat pl.toNat = some pfvs →
    po.toNat + pl.toNat ≤ iwTop m0 → decHL m0 dO.toNat dL.toNat = some ds →
    (∀ i < dL.toNat, dO.toNat + i < iwTop m0) → j.toNat ≤ dL.toNat →
    decHL m q.toNat j.toNat = some acc → PosMR m →
    ∃ ys a', ((ds.drop j.toNat).mapM (ConRon.Arena.targetCanonParams pfvs)).run a = .ok (ys, a') ∧
      decHL m' q.toNat dL.toNat = some (acc ++ ys) ∧ StageR vis fe m' a' ∧ IWGrow m0 m' ∧
      iwTop m ≤ iwTop m' ∧ PosMR m' := by
  sorry

/-- **`class_key_canon`'s model simulates `classKeyCanon`**: the key decoded below the tops, the
canonical parameters a slice below the top. -/
theorem kcW_ok (k : Nat) (m m' : Mem) (a : AState) (po pl key : Word) (r : List Word) (pfvs : List EIdx)
    (ck : ClassKey) (h : kcW k m po pl key = some (r, m')) (hS : StageR vis fe m a)
    (hpf : decHL m po.toNat pl.toNat = some pfvs) (hpb : po.toNat + pl.toNat ≤ iwTop m)
    (hk : DecB (fun m => decCK m key.toNat) m ck) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.classKeyCanon pfvs ck).run a = .ok (x, a') ∧ DecB (fun m => decCK m (r.headD 0).toNat) m' x ∧
      (r.headD 0).toNat + 4 ≤ iwTop m' ∧
      (rdW (m'.arr64 IW) (r.headD 0 + 2)).toNat + (rdW (m'.arr64 IW) (r.headD 0 + 3)).toNat ≤ iwTop m' ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ PosMR m' := by
  sorry

end rel

end L.Ind

end
