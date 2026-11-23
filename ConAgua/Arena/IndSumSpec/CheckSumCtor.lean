module

public import ConAgua.Arena.IndSumSpec.SumProg
import ConAgua.Arena.IndSumSpec.FieldDomsResolve
import ConAgua.Arena.IndSumSpec.StructCtorResidOk
import ConAgua.Arena.IndSim
import ConAgua.Arena.RecLayout.CIDec
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.Arena.IndSumSpec.ColW
public import ConAgua.Arena.IndSumSpec.StructProjArgP

@[expose] public section

/-!
# CheckSumCtor

The callees of `check_sum_ctor(_tail)` as `Sim`s, `checkSumCtor_eq`, `sumTypeWord`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- `param_levels` as a `Sim`. -/
theorem plSim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat) (m : Mem)
    (a : AState) (o l : Word) (lps : List NIdx) (hS : StageR vis fe m a)
    (hd : decHL m o.toNat l.toNat = some lps) (hb : o.toNat + l.toNat ≤ iwTop m) :
    Sim (plW k m o l) (paramLevels lps) a (fun r x m' a' => StageR vis fe m' a' ∧ IWGrow m m' ∧
      H (r.headD 0) ∧ decI (r.headD 0) = x) := fun r m' e => by
  obtain ⟨x, a', h1, h2⟩ := plW_ok dn vis fe k m m' a o l lps r e hS hd (hS.lt64 hb) hb
  exact ⟨x, a', h1, h2⟩

/-- `intern_const` as a `Sim`. -/
theorem ceSim {vis : Word} {fe : IFEnv} (m : Mem) (a : AState)
    (f x : Word) (hS : StageR vis fe m a) (hf : H f) (hx : H x) :
    Sim (ceinternW m f x) (internE (.const (decI (k := .name) f) (decI (k := .levels) x))) a
      (fun r e m' a' => e = decI r ∧ StageR vis fe m' a' ∧ IWGrow m m') := fun r m' e => by
  obtain ⟨a', h1, h2, h3⟩ := internConst_stage hS f x hf hx e
  exact ⟨_, a', h1, rfl, h2, h3⟩

/-- `field_doms_resolve` as a `Sim`. -/
theorem fdrSim {v : Word} {fe : IFEnv} (n : Nat) (m : Mem)
    (a : AState) (o l : Word) (xs : List EIdx) (hS : StageR v fe m a)
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) (hA : AbsOK m) :
    Sim (fdrW n m v o l) (fieldDomsResolve fe xs) a
      (fun r b m' a' => KeepPost v fe decW0B m m' a' r b ∧ AbsOK m') := fun r m' e => by
  obtain ⟨x, a', h1, h2⟩ := fdrW_ok fe n m m' a v o l xs r e hS hd (hS.lt64 hb) hb hA
  exact ⟨x, a', h1, h2⟩

/-- `idx_args_resolve` as a `Sim`. -/
theorem iarSim {v : Word} {fe : IFEnv} (n : Nat) (m : Mem)
    (a : AState) (o l : Word) (xs : List EIdx) (hS : StageR v fe m a)
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) (hA : AbsOK m) :
    Sim (iarW n m v o l) (idxArgsResolve fe xs) a
      (fun r b m' a' => KeepPost v fe decW0B m m' a' r b ∧ AbsOK m') := fun r m' e => by
  obtain ⟨x, a', h1, h2⟩ := iarW_ok fe n m m' a v o l xs r e hS hd (hS.lt64 hb) hb hA
  exact ⟨x, a', h1, h2⟩

/-- **`checkSumCtor` is its head followed by `cscTailT`** (definitionally). -/
theorem checkSumCtor_eq (fe₀ fe : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx)
    (isProp large : Bool) (cvC : IConstantVal) (nF : Nat) (cvTa : IConstantVal) :
    checkSumCtor V fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa = (do
      checkConstantVal V fe cvC false false false
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
      cscTailT fe₀ fe T lps nP nIdx resSort isProp large nF cq) := by
  rfl

/-- A constant's type word, read where the model reads it. -/
theorem sumTypeWord {m : Mem} {q : Word} {cv : IConstantVal} (h : decCVp m q.toNat = some cv) :
    ∃ w, erRd m (q + CV.type) = w ∧ H w ∧ decI w = cv.type := by
  obtain ⟨-, -, -, -, hty, hlt⟩ := decCV_rd (erRdOK m) (show decCV (erecP m) q.toNat = some cv from h)
  exact ⟨_, rfl, hlt, hty.symm⟩

end L.Ind

end
