import ConAgua.Arena.RecCheckSpec.PtrNamesWDec
import ConAgua.Arena.RecGenSpec.DecTMDecBOf
import ConAgua.Arena.IndInstallSpec.CapsProg
import ConAgua.Arena.IndInstallSpec.DecCNS
import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
import ConAgua.Arena.IndInstallSpec.NestCtx
import ConAgua.Arena.IndInstallSpec.NhW
import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndSumSpec.DecHLTake
import ConAgua.Arena.IndGrindAttr

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
    (lps : List NIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hd : decHL s₀.mem o.toNat l.toNat = some lps) (hb : o.toNat + l.toNat < 2 ^ 64)
    (ht : o.toNat + l.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "param_levels" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (paramLevels lps) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (paramLevels lps) a₀) ∧ IWGrow s₀.mem s'.mem ∧
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
    ilF_ok dn vis fe (r1.headD 0) (r1.tail.headD 0) us m1 _ a1 r2 h2 ⟨hS1, hd1⟩
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

/-- `targetMajorOf`'s outside branch after the parameter checks, verbatim. -/
def tmoTailT (fe : IFEnv) (p : BlockShape) (pfvs ds : List EIdx) (nPc : Nat)
    (ctors : List (IConstantVal × Nat)) (I : NIdx) (us : LsIdx) : AM TargetMajor := do
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
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-! ## Frames -/

theorem pinternW_mfrP {m m' : Mem} {u r : Word} (h : pinternW m u = some (r, m')) : MFr [] [] m m' := by
  exact MFr.of_low ⟨_, _, consInternM_frame paramCS_wf h, by simp [tier1, tierOff, ConsSch.wset, paramCS, PREC, PSLOT],
    by simp [paramCS]⟩

theorem plgW_mfrP : ∀ (k : Nat) (m m' : Mem) (o l : Word) (r : List Word), plgW k m o l = some (r, m') →
    MFr [] [] m m'
  | 0, _, _, _, _, _, h => by simp [plgW] at h
  | k + 1, m, m', o, l, r, h => by
    by_cases hl : l = 0
    · rw [plgW_nil k m o l hl] at h
      obtain ⟨⟨q, m1⟩, ha, h⟩ := of_K h rfl
      rw [plK0_some] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact allocW_mfr ha
    rw [plgW_cons k m o l hl] at h
    obtain ⟨⟨u, m1⟩, h1, h⟩ := of_K h (by simp only [plK1])
    by_cases hb : 4294967296 ≤ u
    · rw [plK1_big (h := hb)] at h; cases h
    rw [plK1_ok (h := hb)] at h
    refine (pinternW_mfrP h1).trans ?_
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl
    rw [plK2_some] at h
    refine (plgW_mfrP k _ _ _ _ _ h2).trans ?_
    obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl
    rw [plK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact consW_mfr h3

theorem plW_mfrP {k : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : plW k m o l = some (r, m')) :
    MFr [] [] m m' := by
  cases k with
  | zero => simp [plW] at h
  | succ k =>
  rw [plW_succ] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
  rw [plK4_some] at h
  refine (plgW_mfrP k _ _ _ _ _ h1).trans ?_
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl
  rw [plK5_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]; exact MFr.of_frame (ilF_frame h2) (by simp [tier1, tierOff, POOL, POOL1, LSREC, LSSLOT, LSHP]) (by simp)

def tmmK3 (p : Prog) (n : Nat) (I us fvo fl2 nP nidx co cl t pfo pfl blvls : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if us ≠ blvls then none else if r.headD 0 = 0 then none
      else tmmK4 (callW p n "mk_target_major" [I, us, fvo, fl2, nP, nidx, co, cl, t + 1, 0, 0, pfo, pfl] m)
def tmmK2 (p : Prog) (n : Nat) (I us fvo fl2 nP nidx co cl t pfo pfl ao al2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => tmmK3 p n I us fvo fl2 nP nidx co cl t pfo pfl (r.headD 0)
      (callW p n "sl_eq" [ao, al2, fvo, fl2] m)
def tmmK1 (p : Prog) (n : Nat) (I us fvo fl2 nP nidx co cl t pfo pfl ao al2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => tmmK2 p n I us fvo fl2 nP nidx co cl t pfo pfl ao al2
      (callW p n "param_levels" [r.headD 0, r.tail.headD 0] m)

/-- **The model of `target_major_of_member`** at exec fuel `n + 1`. -/
def tmmW (p : Prog) (n : Nat) (m : Mem) (pp cao cal pfo pfl fvo fvl ao al I us t : Word) :
    Option (List Word × Mem) :=
  if rdW (m.arr64 IW) (pp + 1) ≤ t then none
  else if cal ≤ t then none
  else tmmK1 p n I us fvo (if rdW (m.arr64 IW) (pp + 4) < fvl then rdW (m.arr64 IW) (pp + 4) else fvl)
    (rdW (m.arr64 IW) (pp + 4)) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) pp + t) + 1))
    (rdW (m.arr64 IW) (rdW (m.arr64 IW) (cao + t))) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (cao + t) + 1)) t pfo pfl ao
    (if rdW (m.arr64 IW) (pp + 4) < al then rdW (m.arr64 IW) (pp + 4) else al)
    (callW p n "block_shape_lps" [pp] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (I us fvo fl2 nP nidx co cl t pfo pfl ao al2 blvls : Word)
  (r : List Word)
theorem tmmK1_some : tmmK1 p n I us fvo fl2 nP nidx co cl t pfo pfl ao al2 (some (r, m)) =
    tmmK2 p n I us fvo fl2 nP nidx co cl t pfo pfl ao al2 (callW p n "param_levels" [r.headD 0, r.tail.headD 0] m) :=
  rfl
theorem tmmK2_some : tmmK2 p n I us fvo fl2 nP nidx co cl t pfo pfl ao al2 (some (r, m)) =
    tmmK3 p n I us fvo fl2 nP nidx co cl t pfo pfl (r.headD 0) (callW p n "sl_eq" [ao, al2, fvo, fl2] m) := rfl
theorem tmmK3_some : tmmK3 p n I us fvo fl2 nP nidx co cl t pfo pfl blvls (some (r, m)) =
    if us ≠ blvls then none else if r.headD 0 = 0 then none
      else tmmK4 (callW p n "mk_target_major" [I, us, fvo, fl2, nP, nidx, co, cl, t + 1, 0, 0, pfo, pfl] m) := rfl
theorem tmmK4_some : tmmK4 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
attribute [ind_grind] tmmK1_some tmmK2_some tmmK3_some tmmK4_some

set_option maxHeartbeats 4000000 in
theorem tmm_spec (p : Prog) (hp : p.lookup "target_major_of_member" = some targetMajorOfMember) (n : Nat)
    (s₀ : St) (pp cao cal pfo pfl fvo fvl ao al I us t : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "target_major_of_member" [pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, I, us, t]
    ⦃fun r s' => LocEq s' s₀ ∧ tmmW p n s₀.mem pp cao cal pfo pfl fvo fvl ao al I us t = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetMajorOfMember]
  vcgen [exec, step, L.evalE_spec, evalC, evalArgs, setLoc, setLocs,
    callW_spec p n "block_shape_lps", callW_spec p n "param_levels", callW_spec p n "sl_eq",
    callW_spec p n "mk_target_major"]
  all_goals simp_all [LocEq, Expr.pval, L.Arena.rd64_rdWC, BinOp.eval, Cmp.eval, Cmp.evalW, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal,
    Sig.retOr, tmmW, tmmK1_some, tmmK2_some, tmmK3_some, tmmK4_some, -UInt64.not_lt, -UInt64.not_le]

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

/-- Across `block_shape_lps`. -/
theorem lpsW_mfrP {n : Nat} {m m' : Mem} {q : Word} {r : List Word} (h : lpsW n m q = some (r, m')) :
    MFr [] [] m m' := by
  cases n with
  | zero => simp [lpsW] at h
  | succ n =>
    simp only [lpsW] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact MFr.refl _ _ _
    · exact erToIwW_mfr h

/-- **`target_major_of_member`'s model simulates `targetMajorOf`'s member branch.** -/
theorem tmmW_sim {p : Prog} (hP : TmmProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (n : Nat) {m : Mem} {a : AState} {pp cao cal pfo pfl fvo fvl ao al I us t : Word} {bs : BlockShape}
    {css : List (List (IConstantVal × Nat))} {pfvs fvs args : List EIdx}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcss : PSlR decCNS css cao cal m) (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs)
    (hfv : DecB (fun m => decHL m fvo.toNat fvl.toNat) m fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop m)
    (hag : DecB (fun m => decHL m ao.toNat al.toNat) m args) (hagb : ao.toNat + al.toNat ≤ iwTop m)
    (hI : H I) (hus : H us) (hPm : PosMR m) :
    Sim (tmmW p n m pp cao cal pfo pfl fvo fvl ao al I us t)
      (tmoMemT bs css pfvs fvs args (decI I) (decI us) t.toNat) a
      (fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
        IWGrow m m' ∧ PosMR m') := by
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hqt
  obtain ⟨mo, ml, hmo, hml, hmd, -⟩ := partsAt decMS_mono hmem
  obtain ⟨hw0, -, -⟩ := partsIwRd hmo (w := pp) rfl
  obtain ⟨hw1, -, -⟩ := partsIwRd hml (w := pp + 1) (by rw [UInt64.toNat_add]; simp; omega)
  rw [UInt64.ofNat_toNat] at hw0 hw1
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  unfold tmmW
  rw [hw1]
  by_cases h1 : ml ≤ t
  · rw [ite_eq_left h1]; exact Sim.of_none
  rw [ite_eq_right h1]
  by_cases h2 : cal ≤ t
  · rw [ite_eq_left h2]; exact Sim.of_none
  rw [ite_eq_right h2]
  have htl : t.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h1)
  have htc : t.toNat < cal.toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h2)
  have hml0 : ml ≠ 0 := fun e => by rw [e] at htl; simp at htl
  -- the members
  have hmd' : decPL (truncM m) (decMS (truncM m)) mo.toNat ml.toNat = some bs.members := hmd
  obtain ⟨hlenM, hgetM⟩ := pos2_decPL_trunc hmd'
  obtain ⟨vt, hvt1, hvt2, hvtl, hvt3⟩ := hgetM t.toNat htl
  obtain ⟨v0, hv01, hv02, hv0l, hv03⟩ := hgetM 0 (by omega)
  obtain ⟨rt, -⟩ := tmRdAt (o := mo) (i := t) hvt2 (by omega)
  have rt0 : rdW (m.arr64 IW) mo = UInt64.ofNat v0 := by
    have := tmRdAt (o := mo) (i := 0) (by simpa using hv02) (by simp; omega); simpa using this.1
  obtain ⟨⟨cvq, hcvq, hcvT⟩, hni, -⟩ := decMS_some hv03
  obtain ⟨⟨-, -, -⟩, hnit, -⟩ := decMS_some hvt3
  obtain ⟨hcvq', hcvqlt⟩ := iwN_of_trunc hcvq
  have hv0b : v0 < 2 ^ 64 := iwN_val_lt hv02
  have rc0 : rdW (m.arr64 IW) (UInt64.ofNat v0) = UInt64.ofNat cvq := by
    have := tmRdAt (o := UInt64.ofNat v0) (i := 0) (by rw [UInt64.toNat_ofNat_of_lt' hv0b]; simpa using hcvq')
      (by rw [UInt64.toNat_ofNat_of_lt' hv0b]; simp; omega)
    simpa using this.1
  obtain ⟨hnit', hnitlt⟩ := iwN_of_trunc hnit
  have hvtb : vt < 2 ^ 64 := iwN_val_lt hvt2
  have rni : rdW (m.arr64 IW) (UInt64.ofNat vt + 1) = UInt64.ofNat (bs.members[t.toNat]'hvtl).nIdx := by
    have := tmRdAt (o := UInt64.ofNat vt) (i := 1) (by rw [UInt64.toNat_ofNat_of_lt' hvtb]; simpa using hnit')
      (by rw [UInt64.toNat_ofNat_of_lt' hvtb]; simp; omega)
    simpa using this.1
  -- the constructors
  have hcd : decPL (truncM m) (decCNS (truncM m)) cao.toNat cal.toNat = some css := hcss.1
  obtain ⟨hlenC, hgetC⟩ := pos2_decPL_trunc hcd
  obtain ⟨vc, hvc1, hvc2, hvcl, hvc3⟩ := hgetC t.toNat htc
  obtain ⟨rc, -⟩ := tmRdAt (o := cao) (i := t) hvc2 (by omega)
  have hvc3' : decAt (truncM m) (decPL (truncM m) (decCN (truncM m))) vc = some (css[t.toNat]'hvcl) := hvc3
  obtain ⟨co, cl, hco, hcl, hcsd, -⟩ := partsAt decCN_mono hvc3'
  have hvcb : vc < 2 ^ 64 := iwN_val_lt hvc2
  obtain ⟨hco', hcolt⟩ := iwN_of_trunc hco
  obtain ⟨hcl', hcllt⟩ := iwN_of_trunc hcl
  have rco : rdW (m.arr64 IW) (UInt64.ofNat vc) = co := by
    have := tmRdAt (o := UInt64.ofNat vc) (i := 0) (by rw [UInt64.toNat_ofNat_of_lt' hvcb]; simpa using hco')
      (by rw [UInt64.toNat_ofNat_of_lt' hvcb]; simp; omega)
    simpa using this.1
  have rcl : rdW (m.arr64 IW) (UInt64.ofNat vc + 1) = cl := by
    have := tmRdAt (o := UInt64.ofNat vc) (i := 1) (by rw [UInt64.toNat_ofNat_of_lt' hvcb]; simpa using hcl')
      (by rw [UInt64.toNat_ofNat_of_lt' hvcb]; simp; omega)
    simpa using this.1
  rw [hw0, rt, rni, rc, rco, rcl, hnpw]
  simp only [tmoMemT, List.getElem?_eq_getElem hvtl, List.getElem?_eq_getElem hvcl, unwrapOr, pure_bind]
  -- `block_shape_lps`
  refine Sim.mstep (K := tmmK1 p n I us fvo _ _ _ co cl t pfo pfl ao _) rfl (fun _ _ => rfl) fun r1 m1 e1 => ?_
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeLps_spec p hP.alloc hP.erCopy hP.erToIw hP.lps n _ pp) e1
  obtain ⟨hS1, hg1, hlps1, htop1⟩ := lpsW_ok' hW1 hS hq
  have hf1 := lpsW_mfrP hW1
  rw [tmmK1_some]
  have hT1 : iwTop s1.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  refine Sim.bindK (K := tmmK2 p n I us fvo _ _ _ co cl t pfo pfl ao _)
    (body := fun r2 m2 => tmmK3 p n I us fvo _ _ _ co cl t pfo pfl (r2.headD 0) (callW p n "sl_eq" [ao, _, fvo, _] m2))
    rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow s1.mem m' ∧ H (r.headD 0) ∧ decI (r.headD 0) = x ∧
      MFr [] [] s1.mem m') ?_ ?_
  · intro r2 m2 e2
    obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
      (plW_spec p hP.alloc hP.copy hP.cons hP.get hP.pfind hP.ppush hP.iparam hP.plgo hP.pl hP.il n _ _ _) e2
    obtain ⟨s2', hs2', -, hok, hS2, hg2, hH2, hd2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
      (paramLevels_refines p hP.alloc hP.copy hP.cons hP.get hP.pfind hP.ppush hP.iparam hP.plgo hP.pl hP.il n _ a dn
        vis fe _ _ _ hS1 hlps1 (by omega) htop1) e2
    rw [hs2'] at hS2 hg2
    exact ⟨_, _, partsRunOfOk hok, hS2, hg2, hH2, hd2, plW_mfrP hW2⟩
  rintro r2 blv m2 a2 ⟨hS2, hg2, hH2, hd2, hf2⟩
  have hg02 := hg1.trans hg2
  -- the parameter prefixes
  have hnpe : (UInt64.ofNat bs.nP : Word).toNat = bs.nP := UInt64.toNat_ofNat_of_lt' hnpb
  have hmin : ∀ x : Word, (if UInt64.ofNat bs.nP < x then UInt64.ofNat bs.nP else x).toNat = min bs.nP x.toNat := by
    intro x
    have := @UInt64.lt_iff_toNat_lt (UInt64.ofNat bs.nP) x
    split <;> rename_i hx <;> simp only [hx, hnpe, true_iff, false_iff] at this ⊢ <;> omega
  have hagT : decHL (truncM m) ao.toNat al.toNat = some args := hag
  have hfvT : decHL (truncM m) fvo.toNat fvl.toNat = some fvs := hfv
  have hal := decHL_length _ hagT
  have hfl := decHL_length _ hfvT
  have htakeA : DecB (fun m => decHL m ao.toNat (min bs.nP al.toNat)) m (args.take bs.nP) := by
    show decHL (truncM m) _ _ = _
    rw [decHL_take hagT _ (Nat.min_le_right _ _)]
    congr 1; exact take_min_len _ _ _ hal
  have htakeF : DecB (fun m => decHL m fvo.toNat (min bs.nP fvl.toNat)) m (fvs.take bs.nP) := by
    show decHL (truncM m) _ _ = _
    rw [decHL_take hfvT _ (Nat.min_le_right _ _)]
    congr 1; exact take_min_len _ _ _ hfl
  -- `sl_eq`
  refine Sim.mstep (K := tmmK3 p n I us fvo _ _ _ co cl t pfo pfl (r2.headD 0)) rfl
    (fun r m₁ => tmmK3_some p n m₁ I us fvo _ _ _ co cl t pfo pfl (r2.headD 0) r) fun r3 m3 e3 => ?_
  obtain ⟨s3, rfl, -, hm3, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (slEq_spec p hP.eq n _ ao _ fvo _) e3
  simp only at hm3
  have hA2 : decHL m2 ao.toNat (min bs.nP al.toNat) = some (args.take bs.nP) :=
    htakeA.stab (OMono.decHL _ _) m2 hg02
  have hF2 : decHL m2 fvo.toNat (min bs.nP fvl.toNat) = some (fvs.take bs.nP) :=
    htakeF.stab (OMono.decHL _ _) m2 hg02
  obtain ⟨ws1, hsl1, hws1, hlt1⟩ := slR_of_decHL m2 _ _ _ hA2 (by omega)
  obtain ⟨ws2, hsl2, hws2, hlt2⟩ := slR_of_decHL m2 _ _ _ hF2 (by omega)
  have eA : UInt64.ofNat (min bs.nP al.toNat) = (if UInt64.ofNat bs.nP < al then UInt64.ofNat bs.nP else al) :=
    UInt64.toNat_inj.mp (by rw [hmin, UInt64.toNat_ofNat_of_lt' (show min bs.nP al.toNat < 2 ^ 64 by omega)])
  have eF : UInt64.ofNat (min bs.nP fvl.toNat) = (if UInt64.ofNat bs.nP < fvl then UInt64.ofNat bs.nP else fvl) :=
    UInt64.toNat_inj.mp (by rw [hmin, UInt64.toNat_ofNat_of_lt' (show min bs.nP fvl.toNat < 2 ^ 64 by omega)])
  rw [UInt64.ofNat_toNat, eA] at hsl1
  rw [UInt64.ofNat_toNat, eF] at hsl2
  have heq := eqW_ok n m2 _ _ _ _ _ ws1 ws2 hsl1 hsl2 hW3
  by_cases hu : us ≠ r2.headD 0
  · rw [ite_eq_left hu]; exact Sim.of_none
  rw [ite_eq_right hu]
  have hu' : us = r2.headD 0 := by simpa using hu
  by_cases h3 : r3.headD 0 = 0
  · rw [ite_eq_left h3]; exact Sim.of_none
  rw [ite_eq_right h3]
  have hws : ws1 = ws2 := Decidable.byContradiction fun hne => h3 (by rwa [ite_eq_right hne] at heq)
  have hc : (decI us == blv && args.take bs.nP == fvs.take bs.nP) = true := by
    rw [← hd2, hu', hws1, hws2, hws]; simp
  simp only [hc, ite_true]
  -- the record
  refine Sim.mstep (K := tmmK4) rfl (fun _ _ => rfl) fun r4 m4 e4 => ?_
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (mkTargetMajor_spec p hP.alloc hP.mkTm n _ _ _ _ _ _ _ _ _ _ _ _ _ _) e4
  rw [mkTMW_eq, Option.map_eq_some_iff] at hW4
  obtain ⟨⟨q, m4'⟩, hpr, he⟩ := hW4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  rw [hm3] at hpr
  obtain ⟨hS4, hg4, hq4, ht4, hget4⟩ := posRecW_stage hpr hS2 (by simp)
  simp only [List.length_cons, List.length_nil] at ht4
  have hg04 := hg02.trans hg4
  have hnidb : (bs.members[t.toNat]'hvtl).nIdx < 2 ^ 64 := iwN_val_lt hnit'
  have ht1 : (t + 1).toNat = t.toNat + 1 := word_add_toNat (by rw [show (1 : Word).toNat = 1 from rfl]; omega)
  have hdec := decTM_decB_of (m := s4.mem) (q := q.toNat) (by omega)
    (by simpa using hget4 0 (by simp)) (by simpa using hget4 1 (by simp)) (by simpa using hget4 2 (by simp))
    (by simpa using hget4 3 (by simp)) (by simpa using hget4 4 (by simp)) (by simpa using hget4 5 (by simp))
    (by simpa using hget4 6 (by simp)) (by simpa using hget4 7 (by simp)) (by simpa using hget4 8 (by simp))
    (by simpa using hget4 9 (by simp)) (by simpa using hget4 10 (by simp)) (by simpa using hget4 11 (by simp))
    (by simpa using hget4 12 (by simp)) hI hus
    (by rw [← eF, UInt64.toNat_ofNat_of_lt' (show min bs.nP fvl.toNat < 2 ^ 64 by omega)]
        exact htakeF.grow (OMono.decHL _ _) hg04)
    (hcsd.grow (OMono.decPL decCN_mono _ _) hg04)
    (show decPL (truncM s4.mem) (decNCN (truncM s4.mem)) (0 : Word).toNat (0 : Word).toNat = some [] by
      simp [decPL])
    (hpf.grow (OMono.decHL _ _) hg04)
  rw [hnpe, UInt64.toNat_ofNat_of_lt' hnidb, ht1] at hdec
  exact Sim.ret ⟨by simpa [decON] using hdec, hS4, hg04,
    (((hPm.fr hf1).fr hf2).fr (posRecW_mfr hpr))⟩

end L.Ind

end
