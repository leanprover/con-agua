module

public import ConAgua.Arena.IndDeclConstsFormers
public import ConAgua.Arena.IndPartsSpec.AllCtors
public import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndDeclConsts

import ConAgua.L.ModelGen

@[expose] public section

/-!
# A declaration's constants: the constructors (lane `ronsync2`, stage 3)

`block_ctors_go(nP, c.off, c.len)` and `block_ctors(p)` refine con-ron's `blockCtors`
(`Arena/Install.lean`, pure): every member's constructors (`block_shape_all_ctors`,
`blockShapeAllCtors_refines`), each an `.ctorInfo` record (`ctor_info_rec`, `ciRec_stage`), consed
into an `IW` slice of `EREC` constant records (`sl_cons`, `consW_ci`). Models in the continuation
style of `bfgW`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `block_ctors`. -/
structure DcCtorsProg (p : Prog) : Prop extends FormersProg p where
  ctorInfo : p.lookup "ctor_info_rec" = some ctorInfoRecL
  numCtors : p.lookup "num_ctors_of" = some numCtorsOf
  ctorsCopy : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy
  allCtorsGo : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo
  allCtors : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors
  bcg : p.lookup "block_ctors_go" = some blockCtorsGo
  bc : p.lookup "block_ctors" = some blockCtors

/-! ## `block_ctors_go` -/

/-- **The model of `block_ctors_go(nP, co, cl)`** at exec fuel `n`. -/
l_model bcg_spec (p : Prog) (hp : p.lookup "block_ctors_go" = some blockCtorsGo)
  fns [hp ↦ bcgW list]
  specs [callW_spec p n "ctor_info_rec", callW_spec p n "sl_cons"]
  grind [arena_grind]

/-- `ctor_info_rec`'s run, as its model. -/
theorem ciCall {p : Prog} (hP : DcCtorsProg p) {n : Nat} {m m' : Mem} {cv nP nF : Word} {r : List Word}
    (h : callW p n "ctor_info_rec" [cv, nP, nF] m = some (r, m')) : ciRecW m cv nP nF = some (r.headD 0, m') := by
  obtain ⟨s', rfl, -, hK⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ciRec_specW p hP.erAlloc hP.erPut hP.ctorInfo n _ cv nP nF) h
  exact hK

/-- The twin's constructors of a constructor list. -/
def ctorsOf (N : Nat) (cs : List (IConstantVal × Nat)) : List IConstantInfo :=
  cs.map fun c => .ctorInfo c.1 N c.2

/-- **`block_ctors_go` refines the constructors' records**: an `IW` slice of `EREC` constant
records below the pool's top. -/
theorem bcgW_ok {p : Prog} (hP : DcCtorsProg p) (nP : Word) (a : AState) (vis : Word) (fe : IFEnv)
    (n : Nat) :
    ∀ (m m' : Mem) (co cl : Word) (cs : List (IConstantVal × Nat)) (r : List Word),
    StageR vis fe m a → PSlR decCN cs co cl m → bcgW p n m nP co cl = some (r, m') →
    decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some (ctorsOf nP.toNat cs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a ∧ IWGrow m m' := by
  induction n with
  | zero => intro m m' co cl cs r _ _ h; simp [bcgW] at h
  | succ n ih =>
  intro m m' co cl cs r hS hcs h
  by_cases hl : cl = 0
  · rw [bcgW.arm1 p n m nP co cl hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : cs = [] := by
      have h := hcs.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact ⟨by simp [decPL, ctorsOf], by simp, hS, IWGrow.refl m⟩
  obtain ⟨q, ⟨cv, nF⟩, rest, rfl, hw, hqb, hdc, hrest⟩ := partsPSl_cons hcs hl
  rw [bcgW.arm2 p n m nP co cl hl, hw] at h
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hdc' : decCN (truncM m) q = some (cv, nF) := hdc
  obtain ⟨⟨cqN, hcq, hcv⟩, hnF⟩ := decCN_some hdc'
  rw [← hq'] at hcq
  obtain ⟨w2, hw2, hw2v, hqlt⟩ := rdW_of_iwN_truncM hcq
  have hw1 : (UInt64.ofNat q + 1 : Word).toNat = q + 1 := by
    have := hS.iw.iwSize; have := hS.iw.iw; rw [UInt64.toNat_add, hq']; simp; omega
  have hnF' : iwN (truncM m) (UInt64.ofNat q + 1 : Word).toNat = some nF := by rw [hw1]; exact hnF
  obtain ⟨w3, hw3, hw3v, -⟩ := rdW_of_iwN_truncM hnF'
  rw [hw2, hw3] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [bcgW.k_ctor_info_rec.none])
  rw [bcgW.k_ctor_info_rec.arm1] at h
  have hcvE : decCV (erecP m) w2.toNat = some cv := by rw [hw2v]; exact decCVp_truncM hcv
  obtain ⟨hS1, hg1, hci⟩ := ciRec_stage (ciCall hP h1) hS hcvE
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [bcgW.k_block_ctors_go.none])
  obtain ⟨hd3, hb3, hS3, hg3⟩ := ih m1 m3 (co + 1) (cl - 1) rest r3 hS1 (hrest.grow decCN_mono hg1) h3
  rw [bcgW.k_block_ctors_go.arm1] at h
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [bcgW.k_sl_cons.none])
  rw [bcgW.k_sl_cons.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hd5, hb5, hS5, hg5⟩ := consW_ci (consCall hP.toFormersProg h4) hS3 hb3 hd3
    (hg3.ext.decCI hci)
  refine ⟨by simpa [ctorsOf, hw3v] using hd5, by simp only [List.headD_cons, List.tail_cons]; omega, hS5,
    hg1.trans (hg3.trans hg5)⟩

/-! ## `block_ctors` -/

/-- **The model of `block_ctors(p)`** at exec fuel `n`. -/
l_model dbct_spec (p : Prog) (hp : p.lookup "block_ctors" = some blockCtors)
  fns [hp ↦ dbctW list]
  specs [callW_spec p n "block_shape_all_ctors", callW_spec p n "block_ctors_go"]
  grind [arena_grind]

theorem getD_one_eq (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, _⟩⟩ <;> rfl

/-- The shape's `nP` word (`p + 4`), in any memory grown into. -/
theorem shape_nP {m : Mem} {pp : Word} {bs : BlockShape} (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (h9 : pp.toNat + 9 ≤ iwTop m) {m' : Mem} (hg : IWGrow m m') :
    (rdW (m'.arr64 IW) (pp + 4)).toNat = bs.nP := by
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨-, -, hnp, -⟩ := decBS_some hqt
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have e4 : (pp + 4).toNat = pp.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  rw [← e4] at hnp
  obtain ⟨w, hw, hwv, hlt⟩ := rdW_of_iwN_truncM hnp
  have : rdW (m'.arr64 IW) (pp + 4) = rdW (m.arr64 IW) (pp + 4) := by
    simp only [rdW]; rw [hg.iwGet _ hlt]
  rw [this, hw, hwv]

/-- **`block_ctors` refines `blockCtors`** (pure in the twin): an `IW` slice of `EREC` constant
records below the pool's top. -/
theorem dbctW_ok {p : Prog} (hP : DcCtorsProg p) {n : Nat} {m m' : Mem} {pp : Word}
    {bs : BlockShape} {r : List Word} {a : AState} {vis : Word} {fe : IFEnv}
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (hsrc : ShapeSrc m pp) (h : dbctW p n m pp = some (r, m')) :
    decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (ConRon.Arena.blockCtors bs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a ∧ IWGrow m m' := by
  rcases n with _ | n
  · simp [dbctW] at h
  rw [dbctW.arm1] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [dbctW.k_block_shape_all_ctors.none])
  rw [dbctW.k_block_shape_all_ctors.arm1] at h
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [dbctW.k_block_ctors_go.none])
  rw [dbctW.k_block_ctors_go.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s1, rfl, -, hS1, hg1, hd1, hb1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeAllCtors_refines p hP.alloc hP.iwCopy hP.numCtors hP.ctorsCopy hP.allCtorsGo hP.allCtors n
      _ a (fun _ => none) vis fe pp bs hS hq) h1
  simp only [getD_one_eq] at hd1 hb1
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  have hnP := shape_nP hq hq9 hg1
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (bcg_spec p hP.bcg n _ _ _ _) h2
  obtain ⟨hd, hbd, hS2, hg2⟩ := bcgW_ok hP _ a vis fe n _ _ _ _ _ _ hS1 ⟨hd1, hb1⟩ hW2
  refine ⟨?_, by simpa using hbd, hS2, hg1.trans hg2⟩
  rw [hnP] at hd
  simpa [ConRon.Arena.blockCtors, ctorsOf] using hd

end L.Ind

end
