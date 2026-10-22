import ConAgua.Arena.RecGenSpec15

/-!
# `targetMajorOf` (lane `indproofs3`, helper `indproofs3-pos-cls`): the twin's two branches
-/

namespace ConRon.Arena
open ConLeche

/-- `targetMajorOf`'s member branch, verbatim. -/
def tmoMemT (p : BlockShape) (ctorsAs : List (List (IConstantVal × Nat))) (pfvs fvs args : List EIdx)
    (I : NIdx) (us : LsIdx) (t : Nat) : AM TargetMajor := do
  -- a MEMBER: at the block's levels and parameters
  let ms ← unwrapOr p.members[t]? (.internal "target rec: member")
  let ctorsA ← unwrapOr ctorsAs[t]? (.internal "target rec: member constructors")
  let blvls ← paramLevels p.lps
  let pf := fvs.take p.nP
  if us == blvls && args.take p.nP == pf then
    pure { ind := I, lvls := us, ds := pf, nPc := p.nP, nIdx := ms.nIdx,
           ctors := ctorsA, member := some t, nfs := [], pfvs := pfvs }
  else
    fail (.invalid "target rec: the recursor's major premise is not the member at its \
      parameters and its index binders")

/-- `targetMajorOf`'s outside branch, verbatim. -/
def tmoOutT (fe : IFEnv) (p : BlockShape) (pfvs args : List EIdx) (I : NIdx) (us : LsIdx) :
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
          let (nIdx, sI) ← targetOutsideInst fe I us ds
          unless ← liftFueled "level comparison" (← lvlEq? sI p.resSort) do
            fail (.invalid "target rec: the recursor's major lives in another \
              universe than the block (Q1)")
          pure { ind := I, lvls := us, ds := ds, nPc := nPc, nIdx := nIdx,
                 ctors := ctors, member := none, nfs := [], pfvs := pfvs }

theorem targetMajorOf_eq (fe : IFEnv) (p : BlockShape) (ctorsAs : List (List (IConstantVal × Nat)))
    (pfvs fvs : List EIdx) (mty : EIdx) :
    targetMajorOf fe p ctorsAs pfvs fvs mty = (do
      let args ← getAppArgs coreWalkFuel mty
      let hd ← getAppFn coreWalkFuel mty
      if hd.tag == ETag.const then
        match ← viewConst hd with
        | none => failDanglingE
        | some (I, us) =>
          match p.memberNames.findIdx? (· == I) with
          | some t => tmoMemT p ctorsAs pfvs fvs args I us t
          | none => tmoOutT fe p pfvs args I us
      else
        fail (.invalid "target rec: the recursor's major premise is not an inductive's \
          application")) := rfl

end ConRon.Arena

namespace L.Ind

open L.Arena
open ConRon.Arena

set_option experimental.vcgen true
set_option linter.deprecated false

/-! ## Frames -/

theorem pinternW_mfr {m m' : Mem} {u r : Word} (h : pinternW m u = some (r, m')) : MFr [] [] m m' := by
  rw [pinternW_eq] at h
  exact MFr.of_low ⟨_, _, internM_frame _ paramSch_wf _ _ _ _ _ _ _ _ h, by simp [paramSch, PREC, PSLOT],
    by simp [paramSch]⟩

theorem plgW_mfr : ∀ (k : Nat) (m m' : Mem) (o l : Word) (r : List Word), plgW k m o l = some (r, m') →
    MFr [] [] m m'
  | 0, _, _, _, _, _, h => by simp [plgW] at h
  | k + 1, m, m', o, l, r, h => by
    by_cases hl : l = 0
    · rw [plgW_nil k m o l hl] at h
      cases ha : allocW m 0 with
      | none => rw [ha] at h; cases h
      | some x =>
        obtain ⟨q, m1⟩ := x
        rw [ha, plK0_some] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]; exact allocW_mfr ha
    rw [plgW_cons k m o l hl] at h
    cases h1 : pinternW m (rdW (m.arr64 IW) o) with
    | none => rw [h1] at h; simp [plK1] at h
    | some x =>
    obtain ⟨u, m1⟩ := x
    rw [h1] at h
    by_cases hb : 4294967296 ≤ u
    · rw [plK1_big (h := hb)] at h; cases h
    rw [plK1_ok (h := hb)] at h
    refine (pinternW_mfr h1).trans ?_
    cases h2 : plgW k m1 (o + 1) (l - 1) with
    | none => rw [h2] at h; simp [plK2] at h
    | some y =>
    obtain ⟨r2, m2⟩ := y
    rw [h2, plK2_some] at h
    refine (plgW_mfr k _ _ _ _ _ h2).trans ?_
    cases h3 : consW k m2 u (r2.headD 0) (r2.tail.headD 0) with
    | none => rw [h3] at h; simp [plK3] at h
    | some z =>
    obtain ⟨r3, m3⟩ := z
    rw [h3, plK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact consW_mfr h3

theorem plW_mfr {k : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : plW k m o l = some (r, m')) :
    MFr [] [] m m' := by
  cases k with
  | zero => simp [plW] at h
  | succ k =>
  rw [plW_succ] at h
  cases h1 : plgW k m o l with
  | none => rw [h1] at h; simp [plW.plK4] at h
  | some x =>
  obtain ⟨r1, m1⟩ := x
  rw [h1, plK4_some] at h
  refine (plgW_mfr k _ _ _ _ _ h1).trans ?_
  cases h2 : stubM "intern_ls_iw" m1 [r1.headD 0, r1.tail.headD 0] with
  | none => rw [h2] at h; simp [plW.plK5] at h
  | some y =>
  obtain ⟨r2, m2⟩ := y
  rw [h2, plK5_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]; exact MFr.ofStub h2

/-! ## A fresh `TargetMajor` record, decoded below the tops -/

theorem decTM_decB_of {m : Mem} {q : Nat} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word}
    {ds pfvs : List EIdx} {ctors : List (IConstantVal × Nat)} {nfs : List NestCtorNf}
    (hq : q + 13 ≤ iwTop m)
    (h0 : (m.arr64 IW)[q]? = some a0) (h1 : (m.arr64 IW)[q + 1]? = some a1)
    (h2 : (m.arr64 IW)[q + 2]? = some a2) (h3 : (m.arr64 IW)[q + 3]? = some a3)
    (h4 : (m.arr64 IW)[q + 4]? = some a4) (h5 : (m.arr64 IW)[q + 5]? = some a5)
    (h6 : (m.arr64 IW)[q + 6]? = some a6) (h7 : (m.arr64 IW)[q + 7]? = some a7)
    (h8 : (m.arr64 IW)[q + 8]? = some a8) (h9 : (m.arr64 IW)[q + 9]? = some a9)
    (h10 : (m.arr64 IW)[q + 10]? = some a10) (h11 : (m.arr64 IW)[q + 11]? = some a11)
    (h12 : (m.arr64 IW)[q + 12]? = some a12)
    (hI : a0.toNat < 2 ^ 32) (hu : a1.toNat < 2 ^ 32)
    (hds : DecB (fun m => decHL m a2.toNat a3.toNat) m ds)
    (hct : DecB (fun m => decPL m (decCN m) a6.toNat a7.toNat) m ctors)
    (hnf : DecB (fun m => decPL m (decNCN m) a9.toNat a10.toNat) m nfs)
    (hpf : DecB (fun m => decHL m a11.toNat a12.toNat) m pfvs) :
    DecB (fun m => decTM m q) m
      { ind := decI a0, lvls := decI a1, ds := ds, nPc := a4.toNat, nIdx := a5.toNat,
        ctors := ctors, member := decON a8.toNat, nfs := nfs, pfvs := pfvs } := by
  have t : ∀ j, j < 13 → ∀ a, (m.arr64 IW)[q + j]? = some a → (iwA (truncM m))[q + j]? = some a :=
    fun j hj a h => by rw [truncM_iw_eq (by omega)]; exact h
  have r0 := t 0 (by omega) _ h0; have r1 := t 1 (by omega) _ h1; have r2 := t 2 (by omega) _ h2
  have r3 := t 3 (by omega) _ h3; have r4 := t 4 (by omega) _ h4; have r5 := t 5 (by omega) _ h5
  have r6 := t 6 (by omega) _ h6; have r7 := t 7 (by omega) _ h7; have r8 := t 8 (by omega) _ h8
  have r9 := t 9 (by omega) _ h9; have r10 := t 10 (by omega) _ h10; have r11 := t 11 (by omega) _ h11
  have r12 := t 12 (by omega) _ h12
  have hds' : decHL (truncM m) a2.toNat a3.toNat = some ds := hds
  have hct' : decPL (truncM m) (decCN (truncM m)) a6.toNat a7.toNat = some ctors := hct
  have hnf' : decPL (truncM m) (decNCN (truncM m)) a9.toNat a10.toNat = some nfs := hnf
  have hpf' : decHL (truncM m) a11.toNat a12.toNat = some pfvs := hpf
  show decTM (truncM m) q = _
  simp only [Nat.add_zero] at r0
  simp only [decTM, bind, pure, iwH, hd?, iwN, nat?, decAt]
  simp [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, hI, hu, hds', hct', hnf', hpf']

end L.Ind
