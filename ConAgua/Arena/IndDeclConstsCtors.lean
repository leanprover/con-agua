module

public import ConAgua.Arena.IndDeclConstsFormers
public import ConAgua.Arena.IndPartsSpec.AllCtors
public import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndDeclConsts

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

mutual
/-- **The model of `block_ctors_go(nP, co, cl)`** at exec fuel `n`. -/
def bcgW (p : Prog) : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, nP, co, cl =>
    if cl = 0 then some ([0, 0], m)
    else bcgK1 p n nP co cl (callW p n "ctor_info_rec"
      [rdW (m.arr64 IW) (rdW (m.arr64 IW) co), nP, rdW (m.arr64 IW) (rdW (m.arr64 IW) co + 1)] m)
/-- After the record: the rest. -/
def bcgK1 (p : Prog) (n : Nat) (nP co cl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bfgK3 p n (r.headD 0) (bcgW p n m nP (co + 1) (cl - 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (nP co cl : Word) (r : List Word)
theorem bcgW_nil (h : cl = 0) : bcgW p (n + 1) m nP co cl = some ([0, 0], m) := by
  simp [bcgW, h]
theorem bcgW_cons (h : cl ≠ 0) : bcgW p (n + 1) m nP co cl = bcgK1 p n nP co cl (callW p n "ctor_info_rec"
      [rdW (m.arr64 IW) (rdW (m.arr64 IW) co), nP, rdW (m.arr64 IW) (rdW (m.arr64 IW) co + 1)] m) := by
  simp [bcgW, h]
theorem bcgK1_some : bcgK1 p n nP co cl (some (r, m)) =
    bfgK3 p n (r.headD 0) (bcgW p n m nP (co + 1) (cl - 1)) := by simp [bcgK1]
end arms
attribute [ind_grind] bcgW_nil bcgW_cons bcgK1_some

theorem bcg_spec (p : Prog) (hp : p.lookup "block_ctors_go" = some blockCtorsGo) (n : Nat) :
    ∀ (s₀ : St) (nP co cl : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_ctors_go" [nP, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ bcgW p n s₀.mem nP co cl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ nP co cl; rw [invoke_eq _ hp]; simp only [callFn, blockCtorsGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ nP co cl
    rw [invoke_eq _ hp]
    simp only [callFn, blockCtorsGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "ctor_info_rec", callW_spec p n "sl_cons", ih] <;>
      finish (gen := 20) [rdW_eq]

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
  · rw [bcgW_nil p n m nP co cl hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : cs = [] := by
      have h := hcs.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact ⟨by simp [decPL, ctorsOf], by simp, hS, IWGrow.refl m⟩
  obtain ⟨q, ⟨cv, nF⟩, rest, rfl, hw, hqb, hdc, hrest⟩ := partsPSl_cons hcs hl
  rw [bcgW_cons p n m nP co cl hl, hw] at h
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
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [bcgK1])
  rw [bcgK1_some] at h
  have hcvE : decCV (erecP m) w2.toNat = some cv := by rw [hw2v]; exact decCVp_truncM hcv
  obtain ⟨hS1, hg1, hci⟩ := ciRec_stage (ciCall hP h1) hS hcvE
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [bfgK3])
  obtain ⟨hd3, hb3, hS3, hg3⟩ := ih m1 m3 (co + 1) (cl - 1) rest r3 hS1 (hrest.grow decCN_mono hg1) h3
  rw [bfgK3_some] at h
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [bfgK4])
  rw [bfgK4_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hd5, hb5, hS5, hg5⟩ := consW_ci (consCall hP.toFormersProg h4) hS3 hb3 hd3
    (hg3.ext.decCI hci)
  refine ⟨by simpa [ctorsOf, hw3v] using hd5, by simp only [List.headD_cons, List.tail_cons]; omega, hS5,
    hg1.trans (hg3.trans hg5)⟩

/-! ## `block_ctors` -/

/-- After the constructor list: the records. -/
def dbctK (p : Prog) (n : Nat) (pp : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bfgK4 (callW p n "block_ctors_go" [rdW (m.arr64 IW) (pp + 4), r.headD 0, r.tail.headD 0] m)

/-- **The model of `block_ctors(p)`** at exec fuel `n`. -/
def dbctW (p : Prog) : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, pp => dbctK p n pp (callW p n "block_shape_all_ctors" [pp] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp : Word) (r : List Word)
theorem dbctW_succ : dbctW p (n + 1) m pp = dbctK p n pp (callW p n "block_shape_all_ctors" [pp] m) := rfl
theorem dbctK_some : dbctK p n pp (some (r, m)) =
    bfgK4 (callW p n "block_ctors_go" [rdW (m.arr64 IW) (pp + 4), r.headD 0, r.tail.headD 0] m) := rfl
end arms
attribute [ind_grind] dbctW_succ dbctK_some

theorem dbct_spec (p : Prog) (hp : p.lookup "block_ctors" = some blockCtors) (n : Nat)
    (s₀ : St) (pp : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_ctors" [pp]
    ⦃fun r s' => LocEq s' s₀ ∧ dbctW p n s₀.mem pp = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCtors]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "block_shape_all_ctors", callW_spec p n "block_ctors_go"] <;>
      finish (gen := 20)

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
  rw [dbctW_succ] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [dbctK])
  rw [dbctK_some] at h
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [bfgK4])
  rw [bfgK4_some] at h
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
