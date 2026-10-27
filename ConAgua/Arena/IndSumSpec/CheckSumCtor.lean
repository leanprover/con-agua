import ConAgua.Arena.IndSumSpec.CtlK1
import ConAgua.Arena.IndSumSpec.FieldDomsResolve
import ConAgua.Arena.IndSumSpec.StructCtorResidOk
import ConAgua.Arena.RecGenSpec.CruleProg

/-!
# CheckSumCtor

`ctlK8_no`, `ctlK7_no`, `ctlK6_no`, `ctlK3_big`, `ctlK1_no`, `sumGetD1` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL xo xl xb hd xfn ao al e : Word)
  (r : List Word)
theorem ctlK8_no (h : r.headD 0 = 0) : ctlK8 cR n vis isP lg rs nP nF xo xl ao al (some (r, m)) = none := by
  simp only [ctlK8]; rw [ite_eq_left h]
theorem ctlK7_no (h : r.headD 0 = 0) :
    ctlK7 cR n vis0 vis isP lg rs nP nF xo xl ao al (some (r, m)) = none := by simp only [ctlK7]; rw [ite_eq_left h]
theorem ctlK6_no (h : xfn ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0) :
    ctlK6 cR n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn ao al m (some e) = none := by
  simp only [ctlK6]; rw [ite_eq_left h]
theorem ctlK3_big (h : 4294967296 ≤ hd) :
    ctlK3 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (some (hd, m)) = none := by simp only [ctlK3]; rw [ite_eq_left h]
theorem ctlK1_no (h : r.headD 0 = 0) :
    ctlK1 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL (some (r, m)) = none := by simp only [ctlK1]; rw [ite_eq_left h]
end arms
attribute [ind_grind] ctlK8_no ctlK7_no ctlK6_no ctlK3_big ctlK1_no

theorem sumGetD1 (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> rfl
theorem sumGetD2 (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> rfl
theorem sumGetD0 (r : List Word) : r.getD 0 0 = r.headD 0 := by
  rcases r with _ | ⟨a, r⟩ <;> rfl

/-- `param_levels` as a `Sim`. -/
theorem plSim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat) (m : Mem)
    (a : AState) (o l : Word) (lps : List NIdx) (hS : StageR dn vis fe m a)
    (hd : decHL m o.toNat l.toNat = some lps) (hb : o.toNat + l.toNat ≤ iwTop m) :
    Sim (plW k m o l) (paramLevels lps) a (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      H (r.headD 0) ∧ decI (r.headD 0) = x) := fun r m' e => by
  obtain ⟨x, a', h1, h2⟩ := plW_ok dn vis fe k m m' a o l lps r e hS hd (hS.lt64 hb) hb
  exact ⟨x, a', h1, h2⟩

/-- `intern_const` as a `Sim`. -/
theorem ceSim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (m : Mem) (a : AState)
    (f x : Word) (hS : StageR dn vis fe m a) (hf : H f) (hx : H x) :
    Sim (ceinternW m f x) (internE (.const (decI (k := .name) f) (decI (k := .levels) x))) a
      (fun r e m' a' => e = decI r ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := fun r m' e => by
  obtain ⟨a', h1, h2, h3⟩ := internConst_stage hS f x hf hx e
  exact ⟨_, a', h1, rfl, h2, h3⟩

/-- `field_doms_resolve` as a `Sim`. -/
theorem fdrSim {dn : NIdx → Option ConLeche.Name} {v : Word} {fe : IFEnv} (n : Nat) (m : Mem)
    (a : AState) (o l : Word) (xs : List EIdx) (hS : StageR dn v fe m a)
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) (hA : AbsOK m) :
    Sim (fdrW n m v o l) (fieldDomsResolve fe xs) a
      (fun r b m' a' => KeepPost dn v fe decW0B m m' a' r b ∧ AbsOK m') := fun r m' e => by
  obtain ⟨x, a', h1, h2⟩ := fdrW_ok dn fe n m m' a v o l xs r e hS hd (hS.lt64 hb) hb hA
  exact ⟨x, a', h1, h2⟩

/-- `idx_args_resolve` as a `Sim`. -/
theorem iarSim {dn : NIdx → Option ConLeche.Name} {v : Word} {fe : IFEnv} (n : Nat) (m : Mem)
    (a : AState) (o l : Word) (xs : List EIdx) (hS : StageR dn v fe m a)
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) (hA : AbsOK m) :
    Sim (iarW n m v o l) (idxArgsResolve fe xs) a
      (fun r b m' a' => KeepPost dn v fe decW0B m m' a' r b ∧ AbsOK m') := fun r m' e => by
  obtain ⟨x, a', h1, h2⟩ := iarW_ok dn fe n m m' a v o l xs r e hS hd (hS.lt64 hb) hb hA
  exact ⟨x, a', h1, h2⟩

/-- A callee run at the pre-block view `vis0` (the restriction), back at `vis`. -/
theorem sumKeep_restrict {dn : NIdx → Option ConLeche.Name} {vis vis0 : Word} {fe : IFEnv}
    {m m' : Mem} {a' : AState} {r : List Word} {b : Bool} (hv : fe.visibleBelow = vis.toNat)
    (h : KeepPost dn vis0 (fe.restrictTo vis0.toNat) decW0B m m' a' r b) :
    StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0 != 0) = b :=
  ⟨h.1.unrestrict hv, h.2.1, h.2.2.1⟩

/-- After the type former's opened telescope. -/
def ctorK6 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rq, m) => if rq.headD 0 = 0 then none
    else ctorK7 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB
      (ftdsF m [rq.tail.headD 0, rq.tail.tail.headD 0])
/-- After the constructor's opened telescope. -/
def ctorK5 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m) => if rc.headD 0 = 0 then none
    else ctorK6 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC (rc.tail.headD 0) (rc.tail.tail.headD 0)
      (rc.tail.tail.tail.headD 0) (cR (n + 2) "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (cvTa + 3), 0] m)
/-- After `struct_ctor_resid_ok`. -/
def ctorK4 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m) => if rr.headD 0 = 0 then none
    else ctorK5 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
      (cR (n + 2) "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (cvC + 3), 0] m)
/-- After `strip_pis`. -/
def ctorK3 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs', m) => if rs'.headD 0 = 0 then none
    else ctorK4 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
      (srW (n + 2) m T lo ll nP nF nIdx (rs'.tail.tail.tail.headD 0))
/-- After `check_constant_val`. -/
def ctorK2 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => ctorK3 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
      (stripF 6 m [nP + nF, rdW (m.arr64 EREC) (cvC + 3)])

/-- **The model of `check_sum_ctor(vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvC, nF, cvTa)`**
(its callees at exec fuel `n + 2`). -/
def ctorW (cR : CallM) (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg cvC nF cvTa : Word) :
    Option (List Word × Mem) :=
  ctorK2 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (cR (n + 2) "check_constant_val" [vis, cvC] m)

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa cqO cqL cqB : Word)
  (r : List Word)
theorem ctorK6_no (h : r.headD 0 = 0) :
    ctorK6 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB (some (r, m)) = none := by
  simp only [ctorK6]; rw [ite_eq_left h]
theorem ctorK5_no (h : r.headD 0 = 0) :
    ctorK5 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) = none := by
  simp only [ctorK5]; rw [ite_eq_left h]
theorem ctorK4_no (h : r.headD 0 = 0) :
    ctorK4 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) = none := by
  simp only [ctorK4]; rw [ite_eq_left h]
theorem ctorK3_no (h : r.headD 0 = 0) :
    ctorK3 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) = none := by
  simp only [ctorK3]; rw [ite_eq_left h]
end arms
attribute [ind_grind] ctorK6_no ctorK5_no ctorK4_no ctorK3_no

/-! ## `check_sum_ctor`: the relation to the twin -/

/-- **`checkSumCtor` is its head followed by `cscTailT`** (definitionally). -/
theorem checkSumCtor_eq (fe₀ fe : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx)
    (isProp large : Bool) (cvC : IConstantVal) (nF : Nat) (cvTa : IConstantVal) :
    checkSumCtor V fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa = (do
      checkConstantVal V fe cvC
      let (_, cbody) ← unwrapOr (← stripPis (nP + nF) cvC.type)
        (.notImplemented "direct sum: constructor telescope")
      unless ← structCtorResidOk T lps nP nF nIdx cbody do
        fail (.invalid "direct sum: invalid constructor return type")
      let cq ← unwrapOr (← openPisAtFvarsF nP cvC.type 0)
        (.notImplemented "direct sum: constructor telescope")
      let tq ← unwrapOr (← openPisAtFvarsF nP cvTa.type 0)
        (.notImplemented "direct sum: type former telescope")
      let tdoms ← fvarTypeDs tq.1
      checkStructDomsAt V fe 0 cq.1 tdoms nP
      cscTailT fe₀ fe T lps nP nIdx resSort isProp large cvC nF cq) := by
  rfl

/-- A constant's type word, read where the model reads it. -/
theorem sumTypeWord {m : Mem} {q : Word} {cv : IConstantVal} (h : decCVp m q.toNat = some cv)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) :
    ∃ w, rdW (m.arr64 EREC) (q + 3) = w ∧ H w ∧ decI w = cv.type := by
  have ht := decCV_type h
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at ht
  obtain ⟨w, hw, hx⟩ := ht
  split at hx
  · have hx' := Option.some.inj hx
    have hlt : q.toNat + 3 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp hw).1
    refine ⟨w, rdW_of_get? ?_ hw, by assumption, hx'⟩
    rw [sum_toNat_add (by simp; omega)]; rfl
  · cases hx

end L.Ind

end
