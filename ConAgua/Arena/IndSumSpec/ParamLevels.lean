module

import ConAgua.Arena.IndSumSpec.Row
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
public import ConAgua.Arena.RecCheckSpec.PtrNamesWDec
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.Arena.IndPosSpec.NoGoStep
public import ConAgua.Arena.IndSumSpec.ColW

@[expose] public section

/-!
# ParamLevels: `ConRon.Arena.paramLevels`

The refinement theorems `paramLevels_refines` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section census
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hg : p.lookup "sl_get" = some slGet)
  (hpf : p.lookup "param_find" = some paramFind) (hpp : p.lookup "param_push" = some paramPush)
  (hip : p.lookup "intern_param" = some internParam)
  (hp : p.lookup "param_levels_go" = some paramLevelsGoL)
include ha hc hsc hg hpf hpp hip hp

/-- **`param_levels` refines `paramLevels`** under the stage relation (through the stub
`intern_ls_iw`). -/
@[refines ConRon.Arena.paramLevels]
theorem paramLevels_refines (hq : p.lookup "param_levels" = some paramLevelsL) (hil : IlF p) (k : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (o l : Word)
    (lps : List NIdx) (hS : StageR vis fe s₀.mem a₀)
    (hd : decHL s₀.mem o.toNat l.toNat = some lps) (hb : o.toNat + l.toNat < 2 ^ 64)
    (ht : o.toNat + l.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "param_levels" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (paramLevels lps) a₀ ∧
      StageR vis fe s'.mem (AM.st (paramLevels lps) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      H (r.headD 0) ∧ decI (r.headD 0) = AM.res (paramLevels lps) a₀; ⊤⦄ := by
  refine triple_post (plW_spec p ha hc hsc hg hpf hpp hip hp hq hil k s₀ o l) ?_
  rintro r s' ⟨hl, hm⟩
  cases k with
  | zero => cases hm
  | succ k =>
  rw [plW_succ] at hm
  obtain ⟨r1, m1, h1, hm⟩ := kSome_inv hm rfl (fun _ _ => rfl)
  rw [plK4_some] at hm
  obtain ⟨r2, m2, h2, hm⟩ := kSome_inv hm rfl (fun _ _ => rfl)
  rw [plK5_some] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  obtain ⟨us, a1, hrun1, hS1, hg1, hd1, -⟩ := plgW_ok dn vis fe k _ _ _ _ _ _ _ h1 hS hd hb ht
  obtain ⟨x, a2, hrun2, hS2, hg2, hH, hx⟩ :=
    ilF_ok vis fe (r1.headD 0) (r1.tail.headD 0) us m1 _ a1 r2 h2 ⟨hS1, hd1⟩
  have hrun : (paramLevels lps).run a₀ = .ok (x, a2) := by
    simp only [paramLevels, StateT.run_bind, hrun1]
    exact hrun2
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS2, hg1.trans hg2, by simpa using hH, by rw [hres]; simpa using hx⟩

end census

end L.Ind

end

end

section

namespace ConRon.Arena
open ConLeche

/-- `targetMajorOf`'s member branch, verbatim. -/
def tmoMemT (p : BlockShape) (pfvs fvs args : List EIdx) (I : NIdx) (us : LsIdx) (t : Nat) :
    AM TargetMajor := do
  -- a MEMBER: at the block's levels and parameters
  let ms ← unwrapOr p.members[t]? (.internal "target rec: member")
  let blvls ← paramLevels p.lps
  let pf := fvs.take p.nP
  if us == blvls && args.take p.nP == pf then
    pure { ind := I, lvls := us, ds := pf, nPc := p.nP, nIdx := ms.nIdx,
           ctors := ms.ctors, member := some t, nfs := [], pfvs := pfvs }
  else
    fail (.invalid "target rec: the recursor's major premise is not the member at its \
      parameters and its index binders")

/-- `targetMajorOf`'s outside branch, verbatim. -/
def tmoOutT (mode : CheckMode) (fe : IFEnv) (p : BlockShape) (pfvs args : List EIdx) (I : NIdx) (us : LsIdx) :
    AM TargetMajor := do
  -- an OUTSIDE inductive (a nested block's container)
  let q ← pinQuot
  if I == q then
    fail (.invalid "target rec: the recursor's major is Quot, which is no inductive")
  else
    match ← targetCtorsOf fe I with
    | none => fail (.invalid "target rec: the recursor's major is not a stored inductive")
    | some (nPc, ctors) => do
      let ds := args.take nPc
      if ds.length != nPc then
        fail (.invalid "target rec: the major's parameters mention more than the \
          recursor's parameters")
      else
        let closed ← ds.allM fun x => do
          if (← bvarB coreWalkFuel x) != 0 then pure false
          else pure (decide ((← fvarB coreWalkFuel x) ≤ p.nP))
        if !closed then
          fail (.invalid "target rec: the major's parameters mention more than the \
            recursor's parameters")
        else
          let names := p.memberNames
          unless ← ds.anyM (fun x => nestOcc names 0 0 x) do
            fail (.invalid "target rec: the recursor's major is an outside inductive \
              at an instantiation that is no auxiliary type of the block (official \
              generates no such auxiliary recursor: `elim_nested_inductive`, \
              `is_nested`)")
          let (nIdx, sI) ← targetOutsideInst mode fe I us ds
          unless ← liftFueled "level comparison" (← lvlEq? sI p.resSort) do
            fail (.invalid "target rec: the recursor's major lives in another \
              universe than the block (Q1)")
          pure { ind := I, lvls := us, ds := ds, nPc := nPc, nIdx := nIdx,
                 ctors := ctors, member := none, nfs := [], pfvs := pfvs }

/-- `targetMajorOf`'s outside branch after the parameter checks, verbatim. -/
def tmoTailT (mode : CheckMode) (fe : IFEnv) (p : BlockShape) (pfvs ds : List EIdx) (nPc : Nat)
    (ctors : List (IConstantVal × Nat)) (I : NIdx) (us : LsIdx) : AM TargetMajor := do
  let (nIdx, sI) ← targetOutsideInst mode fe I us ds
  unless ← liftFueled "level comparison" (← lvlEq? sI p.resSort) do
    fail (.invalid "target rec: the recursor's major lives in another \
      universe than the block (Q1)")
  pure { ind := I, lvls := us, ds := ds, nPc := nPc, nIdx := nIdx,
         ctors := ctors, member := none, nfs := [], pfvs := pfvs }

theorem targetMajorOf_eq (mode : CheckMode) (fe : IFEnv) (p : BlockShape) (pfvs fvs : List EIdx)
    (mty : EIdx) :
    targetMajorOf mode fe p pfvs fvs mty = (do
      let args ← getAppArgs coreWalkFuel mty
      let hd ← getAppFn coreWalkFuel mty
      if hd.tag == ETag.const then
        match ← viewConst hd with
        | none => failDanglingE
        | some (I, us) =>
          match p.memberNames.findIdx? (· == I) with
          | some t => tmoMemT p pfvs fvs args I us t
          | none => tmoOutT mode fe p pfvs args I us
      else
        fail (.invalid "target rec: the recursor's major premise is not an inductive's \
          application")) := by rfl

end ConRon.Arena

namespace L.Ind

open L.Arena
open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-! ## Frames -/

/-- `mk_target_major`'s model is a record write. -/
theorem mkTMW_eq (m : Mem) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word) :
    mkTMW m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 =
      (posRecW m [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]).map (fun x => ([x.1], x.2)) := by
  simp only [mkTMW, posRecW]
  cases allocW m 13 with
  | none => rfl
  | some x => obtain ⟨q, m1⟩ := x; simp [tmWr, wrIW, UInt64.add_assoc]

/-- A word of a slice decoded below the tops, at its word address. -/
theorem tmRdAt {m : Mem} {o i : Word} {v : Nat} (h : iwN m (o.toNat + i.toNat) = some v)
    (hb : o.toNat + i.toNat < 2 ^ 64) : rdW (m.arr64 IW) (o + i) = UInt64.ofNat v ∧ v < 2 ^ 64 := by
  have h1 := rd_iwN h hb
  have h2 : v < 2 ^ 64 := by rw [← h1]; exact UInt64.toNat_lt _
  exact ⟨by rw [← h1, UInt64.ofNat_toNat], h2⟩

theorem iwN_val_lt {m : Mem} {i v : Nat} (h : iwN m i = some v) : v < 2 ^ 64 := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, -, rfl⟩ := h
  exact w.toNat_lt

theorem iwN_of_trunc {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) : iwN m i = some v ∧ i < iwTop m := by
  have hi := partsIwLt h
  rw [iwN_truncM hi] at h
  exact ⟨h, hi⟩

theorem take_min_len {α : Type} (xs : List α) (k l : Nat) (h : xs.length = l) :
    xs.take (min k l) = xs.take k := by
  by_cases hk : k ≤ l
  · rw [Nat.min_eq_left hk]
  · rw [Nat.min_eq_right (by omega), ← h, List.take_length, List.take_of_length_le (by omega)]

end L.Ind

end
