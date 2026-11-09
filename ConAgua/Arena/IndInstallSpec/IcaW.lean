module

public import ConAgua.Arena.IndInstallSpec.CapsProg
public import ConAgua.Arena.IndInstallSpec.IcbiW
import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndSumSpec.ConsSumCtors
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.L.WordOff
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndInstallSpec.BlockCapsAt
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
public import ConAgua.Arena.RecSim
public import ConRon.Arena.Inductives.BlockInstall
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# IcaW

`capsHead`, `capsHead_spec`, `capsOne`, `capsOne_spec`, `icaK7`, `icaK6` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The word models -/

/-- `block_caps_head`'s results. -/
def capsHead (m : Mem) (pp mi : Word) : List Word :=
  if rdW (m.arr64 IW) (pp + 1) ≤ mi then [0, 0, 0, 0, 0]
  else
    let ms := rdW (m.arr64 IW) (rdW (m.arr64 IW) pp + mi)
    if rdW (m.arr64 IW) (ms + 3) = 0 then [0, 0, 0, ms, rdW (m.arr64 IW) (ms + 1)]
    else [rdW (m.arr64 IW) (ms + 2), rdW (m.arr64 IW) (ms + 3), Cmp.evalW .eq (rdW (m.arr64 IW) (ms + 3)) 1, ms,
      rdW (m.arr64 IW) (ms + 1)]

theorem capsHead_spec (p : Prog) (hp : p.lookup "block_caps_head" = some blockCapsHead) (n : Nat)
    (s₀ : St) (pp mi : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "block_caps_head" [pp, mi]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r = capsHead s₀.mem pp mi; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCapsHead]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
    finish (gen := 20) [capsHead, rdW_eq]

/-- `block_caps_one`'s results. -/
def capsOne (m : Mem) (pp ms isRec : Word) : List Word :=
  let nIdx := rdW (m.arr64 IW) (ms + 1)
  let c := rdW (m.arr64 IW) (rdW (m.arr64 IW) (ms + 2))
  let nF := rdW (m.arr64 IW) (c + 1)
  [Cmp.evalW .eq nIdx 0 &&& Cmp.evalW .eq isRec 0,
   erRd m (rdW (m.arr64 IW) c), rdW (m.arr64 IW) (pp + 4), nF,
   Cmp.evalW .eq nIdx 0 &&& Cmp.evalW .eq nF 0 &&& Cmp.evalW .eq isRec 0]

theorem capsOne_spec (p : Prog) (hp : p.lookup "block_caps_one" = some blockCapsOne) (n : Nat)
    (s₀ : St) (pp ms isRec : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "block_caps_one" [pp, ms, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r = capsOne s₀.mem pp ms isRec; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCapsOne]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
    finish (gen := 20) [capsOne, rdW_eq, erRd]

/-- After the first and second `rec5`. -/
def icaK7 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([q], m)
def icaK6 (q a0 a1 np c0 c1 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => icaK7 q (recW m 5 [a0, a1, np, c0, c1])
def icaK5b (w2 nIdx a0 a1 np c0 c1 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rq, m) => icaK6 (rq.headD 0) a0 a1 np c0 c1 (recW m 5 [w2, nIdx, 0, 0, 0])
/-- After the second copy: the record, three `rec5`s. -/
def icaK5 (pp w0 w1 w2 w3 w4 nIdx a0 a1 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => icaK5b w2 nIdx a0 a1 (rdW (m5.arr64 IW) (pp + 4)) (r5.headD 0) (r5.tail.headD 0)
      (recW m5 5 [w0, w1, w2, w3, w4])
/-- After the ctor names. -/
def icaK4 (p : Prog) (n : Nat) (pp w0 w1 w2 w3 w4 nIdx a0 a1 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => icaK5 pp w0 w1 w2 w3 w4 nIdx a0 a1
      (callW p n "block_caps_at_er_copy" [r4.headD 0, r4.tail.headD 0] m4)
/-- After the member names' copy. -/
def icaK3 (p : Prog) (n : Nat) (pp coff clen w0 w1 w2 w3 w4 nIdx : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => icaK4 p n pp w0 w1 w2 w3 w4 nIdx (r3.headD 0) (r3.tail.headD 0)
      (callW p n "block_caps_ctor_names" [coff, clen] m3)
/-- After the member names. -/
def icaK2 (p : Prog) (n : Nat) (pp coff clen w0 w1 w2 w3 w4 nIdx : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => icaK3 p n pp coff clen w0 w1 w2 w3 w4 nIdx
      (callW p n "block_caps_at_er_copy" [r2.headD 0, r2.tail.headD 0] m2)

/-- **The model of `block_caps_fin`** (body fuel `n`). -/
def icfW (p : Prog) (n : Nat) (m : Mem) (pp coff clen w0 w1 w2 w3 w4 nIdx : Word) :
    Option (List Word × Mem) :=
  icaK2 p n pp coff clen w0 w1 w2 w3 w4 nIdx (callW p n "block_shape_member_names" [pp] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp coff clen w0 w1 w2 w3 w4 nIdx a0 a1 np c0 c1 q : Word)
  (r : List Word)
theorem icaK2_some : icaK2 p n pp coff clen w0 w1 w2 w3 w4 nIdx (some (r, m)) =
    icaK3 p n pp coff clen w0 w1 w2 w3 w4 nIdx
      (callW p n "block_caps_at_er_copy" [r.headD 0, r.tail.headD 0] m) := rfl
theorem icaK3_some : icaK3 p n pp coff clen w0 w1 w2 w3 w4 nIdx (some (r, m)) =
    icaK4 p n pp w0 w1 w2 w3 w4 nIdx (r.headD 0) (r.tail.headD 0)
      (callW p n "block_caps_ctor_names" [coff, clen] m) := rfl
theorem icaK4_some : icaK4 p n pp w0 w1 w2 w3 w4 nIdx a0 a1 (some (r, m)) =
    icaK5 pp w0 w1 w2 w3 w4 nIdx a0 a1
      (callW p n "block_caps_at_er_copy" [r.headD 0, r.tail.headD 0] m) := rfl
theorem icaK5_some : icaK5 pp w0 w1 w2 w3 w4 nIdx a0 a1 (some (r, m)) =
    icaK5b w2 nIdx a0 a1 (rdW (m.arr64 IW) (pp + 4)) (r.headD 0) (r.tail.headD 0)
      (recW m 5 [w0, w1, w2, w3, w4]) := rfl
theorem icaK5b_some : icaK5b w2 nIdx a0 a1 np c0 c1 (some (r, m)) =
    icaK6 (r.headD 0) a0 a1 np c0 c1 (recW m 5 [w2, nIdx, 0, 0, 0]) := rfl
theorem icaK6_some : icaK6 q a0 a1 np c0 c1 (some (r, m)) = icaK7 q (recW m 5 [a0, a1, np, c0, c1]) := rfl
theorem icaK7_some : icaK7 q (some (r, m)) = some ([q], m) := rfl
end arms
attribute [ind_grind] icaK2_some icaK3_some icaK4_some icaK5_some icaK5b_some icaK6_some icaK7_some

theorem icf_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (hr5 : p.lookup "rec5" = some rec5)
    (hp : p.lookup "block_caps_fin" = some blockCapsFin) (n : Nat) (s₀ : St)
    (pp coff clen w0 w1 w2 w3 w4 nIdx : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "block_caps_fin"
      [pp, coff, clen, w0, w1, w2, w3, w4, nIdx]
    ⦃fun r s' => LocEq s' s₀ ∧ icfW p n s₀.mem pp coff clen w0 w1 w2 w3 w4 nIdx = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCapsFin]
  vcgen [exec, step, L.evalE_spec, evalC, evalArgs, setLoc, setLocs,
    callW_spec p n "block_shape_member_names", callW_spec p n "block_caps_at_er_copy",
    callW_spec p n "block_caps_ctor_names", rec5_specW p ha n hr5]
  all_goals simp_all [LocEq, Expr.pval, L.Arena.rd64_rdWC, BinOp.eval, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal,
    Sig.retOr, -UInt64.not_lt, -UInt64.not_le,
    icfW, icaK2_some, icaK3_some, icaK4_some, icaK5_some, icaK5b_some, icaK6_some, icaK7_some]

/-- The returned pointer. -/
def icaKF : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- After the branch words: the record. -/
def icaKW (p : Prog) (n : Nat) (pp coff clen nIdx : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ws, m) => icaKF (callW p n "block_caps_fin" [pp, coff, clen, ws.headD 0, ws.tail.headD 0,
      ws.tail.tail.headD 0, ws.tail.tail.tail.headD 0, ws.tail.tail.tail.tail.headD 0, nIdx] m)
/-- After `block_caps_head`. -/
def icaKH (p : Prog) (n : Nat) (pp isRec : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (h, m) => icaKW p n pp (h.headD 0) (h.tail.headD 0) (h.tail.tail.tail.tail.headD 0)
      (if h.tail.tail.headD 0 = 1 then callW p n "block_caps_one" [pp, h.tail.tail.tail.headD 0, isRec] m
       else some ([0, 0, 0, 0, 0], m))

/-- **The model of `block_caps_at(p, mi, is_rec)`** (body fuel `n`). -/
def icaW (p : Prog) (n : Nat) (m : Mem) (pp mi isRec : Word) : Option (List Word × Mem) :=
  icaKH p n pp isRec (callW p n "block_caps_head" [pp, mi] m)

section arms2
variable (p : Prog) (n : Nat) (m : Mem) (pp coff clen nIdx isRec : Word) (ws r : List Word)
theorem icaKF_some : icaKF (some (r, m)) = some ([r.headD 0], m) := rfl
theorem icaKW_some : icaKW p n pp coff clen nIdx (some (ws, m)) =
    icaKF (callW p n "block_caps_fin" [pp, coff, clen, ws.headD 0, ws.tail.headD 0,
      ws.tail.tail.headD 0, ws.tail.tail.tail.headD 0, ws.tail.tail.tail.tail.headD 0, nIdx] m) := rfl
theorem icaKH_one (h : r.tail.tail.headD 0 = 1) : icaKH p n pp isRec (some (r, m)) =
    icaKW p n pp (r.headD 0) (r.tail.headD 0) (r.tail.tail.tail.tail.headD 0)
      (callW p n "block_caps_one" [pp, r.tail.tail.tail.headD 0, isRec] m) := by
  simp only [icaKH, h, ↓reduceIte]
theorem icaKH_rest (h : ¬ r.tail.tail.headD 0 = 1) : icaKH p n pp isRec (some (r, m)) =
    icaKW p n pp (r.headD 0) (r.tail.headD 0) (r.tail.tail.tail.tail.headD 0) (some ([0, 0, 0, 0, 0], m)) := by
  simp only [icaKH, h, ↓reduceIte]
end arms2
attribute [ind_grind] icaKF_some icaKW_some icaKH_one icaKH_rest

set_option maxHeartbeats 1600000 in
theorem ica_spec (p : Prog) (hp : p.lookup "block_caps_at" = some blockCapsAt) (n : Nat)
    (s₀ : St) (pp mi isRec : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "block_caps_at" [pp, mi, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ icaW p n s₀.mem pp mi isRec = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCapsAt]
  vcgen [exec, step, L.evalE_spec, evalC, evalArgs, setLoc, setLocs,
    callW_spec p n "block_caps_head", callW_spec p n "block_caps_one", callW_spec p n "block_caps_fin"]
  all_goals simp_all [LocEq, Expr.pval, L.Arena.rd64_rdWC, BinOp.eval, Cmp.eval, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal,
    Sig.retOr, -UInt64.not_lt, -UInt64.not_le,
    icaW, icaKH, icaKF_some, icaKW_some]

end L.Ind

end

end

section

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- Words `ws` at `IW[q‥]`, below the top. -/
def CapsWords (m : Mem) (q : Nat) (ws : List Word) : Prop :=
  q + ws.length ≤ iwTop m ∧ ∀ i < ws.length, iwA m (q + i) = ws[i]?

/-- A handle slice of the record pool in use (both tiers, below their tops: `erA`). -/
def ESl (m : Mem) (o l : Word) (xs : List NIdx) : Prop :=
  hslice? (erA m) o.toNat l.toNat = some xs

theorem CapsWords.grow {m m' : Mem} {q : Nat} {ws : List Word} (h : CapsWords m q ws)
    (hg : IWGrow m m') : CapsWords m' q ws :=
  ⟨Nat.le_trans h.1 hg.iw, fun i hi => by
    simp only [iwA, aread_apply, aread_apply]; rw [hg.iwGet _ (by have := h.1; omega)]; exact h.2 i hi⟩

theorem ESl.grow {m m' : Mem} {o l : Word} {xs : List NIdx} (h : ESl m o l xs) (hg : IWGrow m m') :
    ESl m' o l xs := by
  exact hg.erecGrow.ext.hslice? h

theorem ctorNamesW_room {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : ctorNamesW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    iwTop m + l.toNat ≤ (m.arr64 IW).size := by
  unfold ctorNamesW at h
  cases hal : allocW m l with
  | none => rw [hal] at h; cases h
  | some x =>
    obtain ⟨hq, -, hr⟩ := allocW_facts hal hsz
    simp only [iwTop]; rw [hq] at hr; exact hr

/-- An `EREC` copy of an `IW` handle slice, under the stage relation. -/
theorem installErCopy {p : Prog} (hP : CapsProg p) {n : Nat}
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {o l : Word} {r : List Word} {xs : List NIdx}
    (h : callW p n "block_caps_at_er_copy" [o, l] m = some (r, m')) (hS : StageR vis fe m a)
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ ESl m' (r.headD 0) (r.tail.headD 0) xs := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockCapsAtErCopy_spec p hP.erAlloc hP.erCopyGo hP.erPut hP.erCopy n _ o l) h
  simp only at hW
  obtain ⟨q, m1, ha, rfl, hm'⟩ := capsErCopyW_post hW
  rw [hm']
  obtain ⟨hS', hg, -, -, -, -, hW3⟩ := erRec_stage ha hS _ (ieWords_length _ _ _).symm
  refine ⟨hS', hg, ?_⟩
  simp only [List.headD_cons, List.tail_cons, ESl]
  have hI := hS.iw.iw
  rw [← (show hslice? (iwA m) o.toNat l.toNat = some xs from hd)]; unfold hslice?
  refine mapM_congr_range _ fun j hj => ?_
  have hj' : j < l.toNat := List.mem_range.mp hj
  have h3 := hW3 j (by rw [ieWords_length]; exact hj')
  rw [ieWords_get _ _ _ _ hj'] at h3
  have hin : o.toNat + j < (m.arr64 IW).size := by omega
  have hoj : (o + UInt64.ofNat j).toNat = o.toNat + j := by
    have := hS.iw.iwSize; simp [UInt64.toNat_add, UInt64.toNat_ofNat]; omega
  simp only [hd?, erA, h3, iwA, aread_apply, rdW, hoj, Array.getElem?_eq_getElem hin, Option.getD_some]

theorem installRec5
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {ws r : List Word}
    (h : recW m 5 ws = some (r, m')) (hS : StageR vis fe m a) (hl : ws.length = 5) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ r = [rdW (m.arr64 CTL) 200] ∧
      (rdW (m.arr64 CTL) 200).toNat = iwTop m ∧ CapsWords m' (iwTop m) ws ∧ iwTop m' = iwTop m + 5 := by
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage h hS (by rw [hl]; rfl)
  refine ⟨hS', hg, hr, rfl, ⟨by rw [htop, hl]; exact Nat.le_refl _, fun i hi => ?_⟩, by rw [htop, hl]⟩
  exact hget i hi

/-- **`block_caps_fin`'s record**: the stage relation kept, the 15 words at the returned pointer,
the member names and the ctor names as `EREC` slices below the record pool's top. -/
theorem icfW_ok {p : Prog} (hP : CapsProg p) {n : Nat}
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState}
    {pp coff clen w0 w1 w2 w3 w4 nIdx : Word} {r : List Word} {bs : BlockShape}
    {cs : List (IConstantVal × Nat)}
    (h : icfW p n m pp coff clen w0 w1 w2 w3 w4 nIdx = some (r, m'))
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcs : PSlR decCN cs coff clen m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ ∃ aq al cq cl : Word,
      CapsWords m' (r.headD 0).toNat
        [w0, w1, w2, w3, w4, w2, nIdx, 0, 0, 0, aq, al, UInt64.ofNat bs.nP, cq, cl] ∧
      ESl m' aq al bs.memberNames ∧ ESl m' cq cl (cs.map (·.1.name)) := by
  obtain ⟨hI1, hE1, hsz, hEs, hcl⟩ := hS.iw
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, hptr1⟩ := partsShapeFacts hq hsrc
  have hptr0 : ∀ o l j v, iwN m pp.toNat = some o → iwN m (pp.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v < iwTop m :=
    fun o l j v h1 h2 h3 h4 => by have := hptr1 o l j v h1 h2 h3 h4; omega
  have hkw := partsShapeK hq' hq9
  have hkb : bs.k < 2 ^ 64 := by
    have : bs.k = (UInt64.ofNat bs.k).toNat := by
      obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hq').1
      have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']
      rw [UInt64.toNat_ofNat_of_lt' this.2]
    rw [this]; exact UInt64.toNat_lt _
  unfold icfW at h
  -- the member names
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl; rw [icaK2_some] at h
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_spec p hP.alloc hP.namesCopy hP.names n _ pp) h1
  simp only at hW1; subst hs1
  obtain ⟨hr1, hd1, hg1, hf1, ht1⟩ := memberNamesW_dec hW1 hsz hcl hq' (by omega) hsrc hptr0
  have hS1 : StageR vis fe s1.mem a := stage_frame_iw hS hf1 (by
    have := memberNamesW_room hW1 hsz; rw [hkw, UInt64.toNat_ofNat_of_lt' hkb] at this
    simp only [iwTop] at this ht1 ⊢; omega)
  subst hr1
  simp only [List.headD_cons, List.tail_cons] at h
  -- their `EREC` copy
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl; rw [icaK3_some] at h
  obtain ⟨hS2, hg2, hE2⟩ := installErCopy hP h2 hS1
    (by rw [UInt64.toNat_ofNat_of_lt' hkb]; exact hd1)
    (by rw [UInt64.toNat_ofNat_of_lt' hkb]; omega)
  -- the ctor names
  have hcs2 := hcs.grow decCN_mono (hg1.trans hg2)
  obtain ⟨hI2, hE2', hsz2, hEs2, hcl2⟩ := hS2.iw
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl; rw [icaK4_some] at h
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (blockCapsCtorNames_spec p hP.alloc hP.namesCopy hP.ctorNames n _ coff clen) h3
  simp only at hW3; subst hs3
  have hcsd : decPL (truncM m2) (decCN (truncM m2)) coff.toNat clen.toNat = some cs := hcs2.1
  have hlen := decPL_length _ hcsd
  obtain ⟨hr3, hd3, hg3, hf3, ht3⟩ := ctorNamesW_dec hW3 hsz2 hcl2 hcs2.2 (cs.map (·.1))
    (by simp [hlen]) (fun j hj => by
      obtain ⟨v, y, hv, hy, hget⟩ := decPL_get clen.toNat coff.toNat cs hcsd j hj
      obtain ⟨⟨a', hva, hcv⟩, -⟩ := decCN_some hy
      obtain ⟨hvlt, hv'⟩ := rec2IwN_trunc hv
      obtain ⟨hvlt2, hva'⟩ := rec2IwN_trunc hva
      have hj' : j < cs.length := by omega
      have hy' : cs[j] = y := by simpa [List.getElem?_eq_getElem hj'] using hget
      refine ⟨v, a', hv', by omega, hva', ?_⟩
      simp only [List.getElem_map, hy']
      exact DecB.get (f := fun m => decCVp m a') (OMono.decCVp _) hcv)
  have hS3 : StageR vis fe s3.mem a := stage_frame_iw hS2 hf3 (by
    have := ctorNamesW_room hW3 hsz2; simp only [iwTop] at this ht3 ⊢; omega)
  subst hr3
  simp only [List.headD_cons, List.tail_cons, List.map_map] at h hd3
  -- their `EREC` copy
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h rfl; rw [icaK5_some] at h
  obtain ⟨hS4, hg4, hE4⟩ := installErCopy hP h4 hS3 hd3 (by omega)
  have hg04 := ((hg1.trans hg2).trans hg3).trans hg4
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords hg04 hq hq9
  rw [hnpw] at h
  -- the three records
  obtain ⟨⟨r5, m5⟩, h5, h⟩ := of_K h rfl; rw [icaK5b_some] at h
  obtain ⟨hS5, hg5, hr5, hq5, hw5, ht5⟩ := installRec5 h5 hS4 rfl
  obtain ⟨⟨r6, m6⟩, h6, h⟩ := of_K h rfl; rw [icaK6_some] at h
  obtain ⟨hS6, hg6, -, -, hw6, ht6⟩ := installRec5 h6 hS5 rfl
  obtain ⟨⟨r7, m7⟩, h7, h⟩ := of_K h rfl; rw [icaK7_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS7, hg7, -, -, hw7, ht7⟩ := installRec5 h7 hS6 rfl
  have hg47 := (hg5.trans hg6).trans hg7
  refine ⟨hS7, hg04.trans hg47, r2.headD 0, r2.tail.headD 0, r4.headD 0, r4.tail.headD 0, ?_,
    (hE2.grow (hg3.trans hg4)).grow hg47, hE4.grow hg47⟩
  subst hr5
  simp only [List.headD_cons]
  rw [hq5]
  have w5' := (hw5.grow (hg6.trans hg7))
  have w6' := hw6.grow hg7
  refine ⟨by simp only [List.length_cons, List.length_nil] at *; omega, fun i hi => ?_⟩
  simp only [List.length_cons, List.length_nil] at hi
  rcases Nat.lt_or_ge i 5 with hi5 | hi5
  · have := w5'.2 i (by simpa using hi5)
    rw [this]
    rcases i with _ | _ | _ | _ | _ | i <;> first | rfl | omega
  rcases Nat.lt_or_ge i 10 with hi10 | hi10
  · have := w6'.2 (i - 5) (by simp; omega)
    rw [show iwTop m4 + i = iwTop m5 + (i - 5) by omega, this]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | rfl | omega
  · have := hw7.2 (i - 10) (by simp; omega)
    rw [show iwTop m4 + i = iwTop m6 + (i - 10) by omega, this]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | rfl | omega

/-- **`decCaps` of 15 words** (words `7`‥`9`, the removed `sortZ`, are `0` and unread). -/
theorem installDecCaps {a : Nat → Option Word} {e : Nat}
    {w0 w1 w2 w3 w4 w5 w6 aq al np cq cl : Word} {xs ys : List NIdx}
    (h : ∀ i < 15, a (e + i) = [w0, w1, w2, w3, w4, w5, w6, 0, 0, 0, aq, al, np, cq, cl][i]?)
    (hw1 : H w1) (hx : hslice? a aq.toNat al.toNat = some xs) (hy : hslice? a cq.toNat cl.toNat = some ys) :
    decCaps a e = some
      { eta := w0 != 0, etaCtor := decI w1, etaParams := w2.toNat, etaFields := w3.toNat,
        unitlike := w4 != 0, unitParams := w5.toNat, all := xs, nparams := np.toNat, nIdx := w6.toNat,
        ctors := ys } := by
  have e0 := h 0 (by decide); have e1 := h 1 (by decide); have e2 := h 2 (by decide)
  have e3 := h 3 (by decide); have e4 := h 4 (by decide); have e5 := h 5 (by decide)
  have e6 := h 6 (by decide); have e10 := h 10 (by decide); have e11 := h 11 (by decide)
  have e12 := h 12 (by decide); have e13 := h 13 (by decide); have e14 := h 14 (by decide)
  simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ] at e0 e1 e2 e3 e4 e5 e6
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at e10 e11 e12 e13 e14
  have hw1' : w1.toNat < 2 ^ 32 := hw1
  unfold decCaps
  simp only [bool?, hd?, nat?, hlist?, e0, e1, e2, e3, e4, e5, e6, e10, e12, e13,
    show e + 10 + 1 = e + 11 by omega, show e + 13 + 1 = e + 14 by omega, e11, e14, Option.map_some,
    hw1', ite_true, hx, hy, bind, Option.bind_some, pure]

/-! ## `block_caps_at`'s relation -/

theorem installEvalW3 (c1 c2 c3 : Cmp) (a1 b1 a2 b2 a3 b3 : Word) :
    (Cmp.evalW c1 a1 b1 &&& Cmp.evalW c2 a2 b2 &&& Cmp.evalW c3 a3 b3 != 0) =
      (c1.eval a1 b1 && c2.eval a2 b2 && c3.eval a3 b3) := by
  unfold Cmp.evalW
  cases c1.eval a1 b1 <;> cases c2.eval a2 b2 <;> cases c3.eval a3 b3 <;> decide

theorem installEvalW2 (c1 c2 : Cmp) (a1 b1 a2 b2 : Word) :
    (Cmp.evalW c1 a1 b1 &&& Cmp.evalW c2 a2 b2 != 0) = (c1.eval a1 b1 && c2.eval a2 b2) := by
  unfold Cmp.evalW
  cases c1.eval a1 b1 <;> cases c2.eval a2 b2 <;> decide

theorem installOfNatBeq {x c : Nat} (hx : x < 2 ^ 64) (hc : c < 2 ^ 64) :
    (UInt64.ofNat x == UInt64.ofNat c) = (x == c) := by
  by_cases h : x = c
  · subst h; simp
  · have : UInt64.ofNat x ≠ UInt64.ofNat c := fun e => h (by
      have := congrArg UInt64.toNat e
      rwa [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hc] at this)
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

/-- A pure callee's run: the memory unchanged, the result its model. -/
theorem installPureCall {p : Prog} {n : Nat} {f : FnName} {args : List Word} {m m' : Mem}
    {R r : List Word}
    (h : ⦃fun st => st = (⟨m, Locals.init []⟩ : St)⦄ invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' ⟨m, Locals.init []⟩ ∧ s'.mem = m ∧ r = R; ⊤⦄)
    (hc : callW p n f args m = some (r, m')) : r = R ∧ m' = m := by
  obtain ⟨s', rfl, -, h1, h2⟩ := triple_of_callW h hc
  exact ⟨h2, h1⟩

/-- **`block_caps_fin`'s run: the record.** A capability record with the branch words, the index
count, the member names and the ctor names. -/
theorem installCapsTail {p : Prog} (hP : CapsProg p) (n : Nat)
    {vis : Word} {fe : IFEnv} {m m2 : Mem} {a : AState} {pp coff clen w0 w1 w2 w3 w4 nIdx : Word}
    {r2 : List Word} {bs : BlockShape} {cs : List (IConstantVal × Nat)}
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcs : PSlR decCN cs coff clen m) (hw1 : H w1)
    (h2 : callW p (n + 1) "block_caps_fin" [pp, coff, clen, w0, w1, w2, w3, w4, nIdx] m = some (r2, m2)) :
    StageR vis fe m2 a ∧ IWGrow m m2 ∧ CapsAt m2 (r2.headD 0).toNat
      { eta := w0 != 0, etaCtor := decI w1, etaParams := w2.toNat, etaFields := w3.toNat,
        unitlike := w4 != 0, unitParams := w2.toNat, all := bs.memberNames, nparams := bs.nP,
        nIdx := nIdx.toNat, ctors := cs.map (·.1.name) } := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (icf_spec p hP.alloc hP.rec5 hP.fin n _ pp coff clen w0 w1 w2 w3 w4 nIdx) h2
  simp only at hW
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨-, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  obtain ⟨hS2, hg2, aq, al, cq, cl, hcw, hEa, hEc⟩ := icfW_ok hP hW hS hq hsrc hcs
  refine ⟨hS2, hg2, by have := hcw.1; simpa using this, fun a e ha he => ?_⟩
  have hd := installDecCaps (a := a) (e := e) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (w5 := w2) (w6 := nIdx) (aq := aq) (al := al) (np := UInt64.ofNat bs.nP) (cq := cq) (cl := cl)
    (fun i hi => (ha i hi).trans (hcw.2 i (by simpa using hi))) hw1 (he.hslice? hEa) (he.hslice? hEc)
  rw [hd, UInt64.toNat_ofNat_of_lt' hnpb]

/-- **`block_caps_at`'s model refines `blockCapsAt`** (pure in the twin): the stage relation kept,
the capability record at the returned pointer. -/
theorem icaW_ok {p : Prog} (hP : CapsProg p) (n : Nat)
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {pp mi isRec : Word} {bs : BlockShape} {b : Bool}
    {r : List Word} (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hb : (isRec != 0) = b) (h : icaW p n m pp mi isRec = some (r, m')) (hS : StageR vis fe m a) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      CapsAt m' (r.headD 0).toNat (ConRon.Arena.blockCapsAt bs mi.toNat b) := by
  rcases n with _ | n
  · rw [icaW, callW_zero] at h; cases h
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, -⟩ := partsShapeFacts hq hsrc
  have hkw := partsShapeK hq' hq9
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdm, hob⟩ := partsAt decMS_mono hmem
  have hdm' : decPL (truncM m) (decMS (truncM m)) o.toNat l.toNat = some bs.members := hdm
  have hlk : bs.k = l.toNat := decPL_length _ hdm'
  have hkb : bs.k < 2 ^ 64 := by rw [hlk]; exact l.toNat_lt
  obtain ⟨hw0, -, -⟩ := partsIwRd ho (w := pp) rfl
  rw [UInt64.ofNat_toNat] at hw0
  -- the record, shared by the branches
  have hfin : ∀ (ws : List Word) (cs : List (IConstantVal × Nat)) (coff clen nIdx : Word) (R : IIndCaps),
      PSlR decCN cs coff clen m → H (ws.tail.headD 0) →
      R =
        { eta := ws.headD 0 != 0, etaCtor := decI (ws.tail.headD 0),
          etaParams := (ws.tail.tail.headD 0).toNat, etaFields := (ws.tail.tail.tail.headD 0).toNat,
          unitlike := ws.tail.tail.tail.tail.headD 0 != 0, unitParams := (ws.tail.tail.headD 0).toNat,
          all := bs.memberNames, nparams := bs.nP, nIdx := nIdx.toNat, ctors := cs.map (·.1.name) } →
      icaKW p (n + 1) pp coff clen nIdx (some (ws, m)) = some (r, m') →
      StageR vis fe m' a ∧ IWGrow m m' ∧ CapsAt m' (r.headD 0).toNat R := by
    intro ws cs coff clen nIdx R hcs hw1 hR hK
    rw [icaKW_some] at hK
    obtain ⟨⟨r2, m2⟩, h2, hK⟩ := of_K hK rfl
    rw [icaKF_some] at hK
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hK)
    obtain ⟨hS2, hg2, hca⟩ := installCapsTail hP n hS hq hsrc hcs hw1 h2
    subst hR
    exact ⟨hS2, hg2, by simpa using hca⟩
  unfold icaW at h
  obtain ⟨⟨r0, m0⟩, h0, h⟩ := of_K h rfl
  obtain ⟨hr0, hm0⟩ := installPureCall (capsHead_spec p hP.head n _ pp mi) h0
  subst m0; subst r0
  unfold ConRon.Arena.blockCapsAt
  dsimp only
  rcases Nat.lt_or_ge mi.toNat bs.k with hmi | hmi
  case inr =>
    have hnone : bs.members[mi.toNat]? = none :=
        List.getElem?_eq_none (by unfold BlockShape.k at hmi; omega)
    have hh : capsHead m pp mi = [0, 0, 0, 0, 0] := by
      unfold capsHead; rw [ite_eq_left]
      rw [hkw, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hkb]; omega
    rw [hh, icaKH_rest (h := by decide)] at h
    simp only [hnone]
    exact hfin [0, 0, 0, 0, 0] [] 0 0 0 _ (PSlR.nil decCN m) (by decide) rfl h
  -- member `mi`
  have hl0 : l.toNat ≠ 0 := by omega
  have hob' : o.toNat + l.toNat ≤ iwTop m := hob.resolve_left (fun h => hl0 (by rw [h]; rfl))
  obtain ⟨v, hv, hmsd⟩ := decPL_getH (truncM m) hdm' mi.toNat (by omega)
  generalize hmsh : bs.members[mi.toNat]'(by rw [decPL_length _ hdm']; omega) = msh at hmsd
  have hsome : bs.members[mi.toNat]? = some msh := by rw [← hmsh]; exact List.getElem?_eq_getElem _
  simp only [hsome]
  have hom : (o + mi).toNat = o.toNat + mi.toNat := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hwv, hvb, hvlt⟩ := partsIwRd hv (w := o + mi) hom
  have hv' : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hvb
  obtain ⟨⟨cvp, hcvp, hcvT⟩, -, hni, hct⟩ := decMS_some hmsd
  obtain ⟨co, cl, hco, hcl, hcd, hcb⟩ := partsAt decCN_mono hct
  have hv3 : v + 3 < iwTop m := partsIwLt hcl
  obtain ⟨hw2, -, -⟩ := partsIwRd hco (w := UInt64.ofNat v + 2) (by rw [UInt64.toNat_add, hv']; simp; omega)
  obtain ⟨hw3, -, -⟩ := partsIwRd hcl (w := UInt64.ofNat v + 3) (by rw [UInt64.toNat_add, hv']; simp; omega)
  obtain ⟨hw1n, hnb, -⟩ := partsIwRd hni (w := UInt64.ofNat v + 1) (by rw [UInt64.toNat_add, hv']; simp; omega)
  rw [UInt64.ofNat_toNat] at hw2 hw3
  have hnI : (UInt64.ofNat msh.nIdx : Word).toNat = msh.nIdx := UInt64.toNat_ofNat_of_lt' hnb
  have hcd' : decPL (truncM m) (decCN (truncM m)) co.toNat cl.toNat = some msh.ctors := hcd
  have hlenc : msh.ctors.length = cl.toNat := decPL_length _ hcd'
  have hhd : capsHead m pp mi = if cl = 0 then [0, 0, 0, UInt64.ofNat v, UInt64.ofNat msh.nIdx]
      else [co, cl, Cmp.evalW .eq cl 1, UInt64.ofNat v, UInt64.ofNat msh.nIdx] := by
    unfold capsHead
    rw [ite_eq_right (by rw [hkw, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hkb]; omega)]
    simp only [hw0, hwv, hw2, hw3, hw1n]
  rcases hcs : msh.ctors with _ | ⟨c, _ | ⟨c2, cs⟩⟩
  · -- no constructor
    have hcl0 : cl = 0 := by
      apply UInt64.toNat_inj.mp; rw [← hlenc, hcs]; rfl
    rw [hhd, ite_eq_left hcl0, icaKH_rest (h := by simp)] at h
    exact hfin [0, 0, 0, 0, 0] [] 0 0 (UInt64.ofNat msh.nIdx) _ (PSlR.nil decCN m) (by decide) (by rw [hnI]; rfl) h
  · -- one constructor
    have hcl1 : cl = 1 := by apply UInt64.toNat_inj.mp; rw [← hlenc, hcs]; rfl
    subst hcl1
    rw [hhd, ite_eq_right (by decide), icaKH_one (h := rfl)] at h
    obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
    obtain ⟨hr1, hm1⟩ := installPureCall (capsOne_spec p hP.one n _ pp (UInt64.ofNat v) isRec) h1
    subst m1; subst r1
    -- the constructor's words
    obtain ⟨cp, hcp, hcd0⟩ := decPL_getH (truncM m) hcd' 0 (by decide)
    simp only [hcs, List.getElem_cons_zero, Nat.add_zero] at hcd0 hcp
    obtain ⟨⟨cvp2, hcvp2, hcv2⟩, hnF⟩ := decCN_some hcd0
    obtain ⟨hwc, hcpb, -⟩ := partsIwRd hcp (w := co) rfl
    have hcp' : (UInt64.ofNat cp : Word).toNat = cp := UInt64.toNat_ofNat_of_lt' hcpb
    obtain ⟨hwcv, hcvb, -⟩ := partsIwRd hcvp2 (w := UInt64.ofNat cp) hcp'
    have hcpN : cp + 1 < iwTop m := partsIwLt hnF
    obtain ⟨hwnF, hnFb, -⟩ := partsIwRd hnF (w := UInt64.ofNat cp + 1) (by rw [UInt64.toNat_add, hcp']; simp; omega)
    obtain ⟨hn32, hnm⟩ := partsCVName (IWGrow.refl m) hcv2 hcvb
    have hcb1 : co.toNat + (1 : Word).toNat ≤ iwTop m := hcb.resolve_left (by decide)
    refine hfin (capsOne m pp (UInt64.ofNat v) isRec) [c] co 1 (UInt64.ofNat msh.nIdx) _
      ⟨by rw [← hcs]; exact hcd, hcb1⟩
      (by simp only [capsOne, List.headD_cons, List.tail_cons, hw2, hwc, hwcv]; exact hn32) ?_ h
    simp only [capsOne, List.headD_cons, List.tail_cons, hw2, hwc, hwcv, hw1n, hwnF, hnpw,
      hnm, installEvalW3, installEvalW2]
    have e1 : (UInt64.ofNat msh.nIdx == (0 : Word)) = (msh.nIdx == 0) := installOfNatBeq (c := 0) hnb (by decide)
    have e2 : (UInt64.ofNat c.snd == (0 : Word)) = (c.snd == 0) := installOfNatBeq (c := 0) hnFb (by decide)
    have e4 : (isRec == 0) = !b := by rw [← hb]; simp [bne]
    simp only [Cmp.eval, e1, e2, e4, UInt64.toNat_ofNat_of_lt' hnpb, hnI,
      UInt64.toNat_ofNat_of_lt' hnFb, List.map_cons, List.map_nil]
    by_cases h1 : msh.nIdx = 0 <;> by_cases h2 : c.snd = 0 <;> cases b <;> simp [h1, h2, bne]
  · -- two or more
    have hcl2 : 2 ≤ cl.toNat := by rw [← hlenc, hcs]; simp
    have hne0 : cl ≠ 0 := fun e => by rw [e] at hcl2; simp at hcl2
    have hne1 : Cmp.evalW .eq cl 1 ≠ 1 := by
      have : cl ≠ 1 := fun e => by rw [e] at hcl2; simp at hcl2
      simp [Cmp.evalW, Cmp.eval, this]
    rw [hhd, ite_eq_right hne0, icaKH_rest (h := by simpa using hne1)] at h
    have hbd : co.toNat + cl.toNat ≤ iwTop m := hcb.resolve_left hne0
    exact hfin [0, 0, 0, 0, 0] (c :: c2 :: cs) co cl (UInt64.ofNat msh.nIdx) _ ⟨by rw [← hcs]; exact hcd, hbd⟩ (by decide)
      (by rw [hnI]; rfl) h

/-- **`block_caps_at` refines `blockCapsAt`, as a call** (`icaW_ok`). -/
theorem blockCapsAt_ok {p : Prog} (hP : CapsProg p) (n : Nat)
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {pp mi isRec : Word} {bs : BlockShape} {b : Bool}
    {r : List Word} (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hb : (isRec != 0) = b) (h : callW p n "block_caps_at" [pp, mi, isRec] m = some (r, m'))
    (hS : StageR vis fe m a) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      CapsAt m' (r.headD 0).toNat (ConRon.Arena.blockCapsAt bs mi.toNat b) := by
  rcases n with _ | k
  · rw [callW_zero] at h; cases h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ica_spec p hP.caps k _ pp mi isRec) h
  exact icaW_ok hP k hq hsrc hb hW hS

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `ind_info_rec` -/

/-- The record's words, read in the memory before the allocation. -/
def iirWs (m : Mem) (cv caps : Word) : List Word :=
  [3, erRd m cv, erRd m (cv + 1), erRd m (cv + 2), erRd m (cv + 3), rdW (m.arr64 IW) caps, rdW (m.arr64 IW) (caps + 1), rdW (m.arr64 IW) (caps + 2), rdW (m.arr64 IW) (caps + 3), rdW (m.arr64 IW) (caps + 4), rdW (m.arr64 IW) (caps + 5), rdW (m.arr64 IW) (caps + 6), rdW (m.arr64 IW) (caps + 7), rdW (m.arr64 IW) (caps + 8), rdW (m.arr64 IW) (caps + 9), rdW (m.arr64 IW) (caps + 10), rdW (m.arr64 IW) (caps + 11), rdW (m.arr64 IW) (caps + 12), rdW (m.arr64 IW) (caps + 13), rdW (m.arr64 IW) (caps + 14)]

/- `(ematch := 8)`: a depth, not a search. With the locals read in one step (`L/LocNF.lean`),
each of the five stores' addresses meets `wrER`'s in a later E-matching round than before, past
the default five rounds. -/
theorem erPut5_spec (p : Prog) (hpu : p.lookup "erec_put" = some erecPut)
    (hp : p.lookup "er_put5" = some erPut5) (n : Nat) (s₀ : St)
    (d x0 x1 x2 x3 x4 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "er_put5" [d, x0, x1, x2, x3, x4]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = wrER s₀.mem d [x0, x1, x2, x3, x4]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erPut5]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, erecPut_specW p hpu n] <;>
    finish (ematch := 8) [wrER, UInt64.add_assoc]

/-- The model of `ind_info_rec(cv, caps)`. -/
def iirW (m : Mem) (cv caps : Word) : Option (Word × Mem) :=
  match erAllocW m 20 with
  | none => none
  | some (q, m1) => some (q, wrER m1 q (iirWs m cv caps))

def iirK4 (p : Prog) (n : Nat) (caps q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m4) => iirK5 q (callW p n "er_put5" [q + 15, rdW (m4.arr64 IW) (caps + 10),
      rdW (m4.arr64 IW) (caps + 11), rdW (m4.arr64 IW) (caps + 12), rdW (m4.arr64 IW) (caps + 13),
      rdW (m4.arr64 IW) (caps + 14)] m4)
def iirK3 (p : Prog) (n : Nat) (caps q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m3) => iirK4 p n caps q (callW p n "er_put5" [q + 10, rdW (m3.arr64 IW) (caps + 5),
      rdW (m3.arr64 IW) (caps + 6), rdW (m3.arr64 IW) (caps + 7), rdW (m3.arr64 IW) (caps + 8),
      rdW (m3.arr64 IW) (caps + 9)] m3)
def iirK2 (p : Prog) (n : Nat) (caps q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => iirK3 p n caps q (callW p n "er_put5" [q + 5, rdW (m2.arr64 IW) caps,
      rdW (m2.arr64 IW) (caps + 1), rdW (m2.arr64 IW) (caps + 2), rdW (m2.arr64 IW) (caps + 3),
      rdW (m2.arr64 IW) (caps + 4)] m2)
/-- After the allocation: the four writes. -/
def iirK (p : Prog) (n : Nat) (cv caps : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m1) => iirK2 p n caps q (callW p n "er_put5" [q, 3, erRd m1 cv,
      erRd m1 (cv + 1), erRd m1 (cv + 2), erRd m1 (cv + 3)] m1)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (cv caps q : Word) (r : List Word)
theorem iirK5_some : iirK5 q (some (r, m)) = some ([q], m) := rfl
theorem iirK4_some : iirK4 p n caps q (some (r, m)) = iirK5 q (callW p n "er_put5" [q + 15,
    rdW (m.arr64 IW) (caps + 10), rdW (m.arr64 IW) (caps + 11), rdW (m.arr64 IW) (caps + 12),
    rdW (m.arr64 IW) (caps + 13), rdW (m.arr64 IW) (caps + 14)] m) := rfl
theorem iirK3_some : iirK3 p n caps q (some (r, m)) = iirK4 p n caps q (callW p n "er_put5" [q + 10,
    rdW (m.arr64 IW) (caps + 5), rdW (m.arr64 IW) (caps + 6), rdW (m.arr64 IW) (caps + 7),
    rdW (m.arr64 IW) (caps + 8), rdW (m.arr64 IW) (caps + 9)] m) := rfl
theorem iirK2_some : iirK2 p n caps q (some (r, m)) = iirK3 p n caps q (callW p n "er_put5" [q + 5,
    rdW (m.arr64 IW) caps, rdW (m.arr64 IW) (caps + 1), rdW (m.arr64 IW) (caps + 2),
    rdW (m.arr64 IW) (caps + 3), rdW (m.arr64 IW) (caps + 4)] m) := rfl
theorem iirK_some : iirK p n cv caps (some (q, m)) = iirK2 p n caps q (callW p n "er_put5" [q, 3,
    erRd m cv, erRd m (cv + 1), erRd m (cv + 2), erRd m (cv + 3)] m) := rfl
end arms
attribute [ind_grind] iirK5_some iirK4_some iirK3_some iirK2_some iirK_some

theorem iir_specK (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hp : p.lookup "ind_info_rec" = some indInfoRec) (n : Nat) (s₀ : St) (cv caps : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ind_info_rec" [cv, caps]
    ⦃fun r s' => LocEq s' s₀ ∧ iirK p n cv caps (erAllocW s₀.mem 20) = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, indInfoRec]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      erecAlloc_specW p ha n, callW_spec p n "er_put5"] <;>
    finish (gen := 40) (instances := 20000) [rdW_eq, erRd]

theorem wrER_IW (m : Mem) (q : Word) (ws : List Word) : (wrER m q ws).arr64 IW = m.arr64 IW :=
  (wrER_frame ws m q).1 IW (by simp [EREC, IW]) (by decide)

theorem erAllocW_arr {m m1 : Mem} {k q : Word} (h : erAllocW m k = some (q, m1)) :
    m1.arr64 IW = m.arr64 IW ∧ ∀ x, erRd m1 x = erRd m x := by
  have hc : ∀ b : TieredArray, b ≠ CTL → m1.arr64 b = m.arr64 b := by
    intro b hb
    simp only [erAllocW] at h
    split at h
    · split at h; · cases h
      split at h; · cases h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      simp only [erAllocMem]; rw [if_pos (by assumption)]; exact Mem.arr64_set64_ne _ _ _ _ _ hb
    · split at h; · cases h
      split at h; · cases h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      simp only [erAllocMem]; rw [if_neg (by assumption)]; exact Mem.arr64_set64_ne _ _ _ _ _ hb
  refine ⟨hc _ (by decide), fun x => ?_⟩
  unfold erRd; rw [hc _ (by rw [tierA_EREC]; split <;> decide)]

/-- `ind_info_rec`'s four writes are the record written at once. -/
theorem iirK_eq {p : Prog} (hpu : p.lookup "erec_put" = some erecPut)
    (hp : p.lookup "er_put5" = some erPut5) {n : Nat} {m m' : Mem}
    {cv caps : Word} {r : List Word} (h : iirK p (n + 1) cv caps (erAllocW m 20) = some (r, m')) :
    ∃ q, r = [q] ∧ iirW m cv caps = some (q, m') := by
  have put : ∀ (mm : Mem) (d x0 x1 x2 x3 x4 : Word) (rr : List Word) (mm' : Mem),
      callW p (n + 1) "er_put5" [d, x0, x1, x2, x3, x4] mm = some (rr, mm') →
      mm' = wrER mm d [x0, x1, x2, x3, x4] := by
    intro mm d x0 x1 x2 x3 x4 rr mm' hc
    obtain ⟨s', rfl, -, h2⟩ := triple_of_callW (s₀ := ⟨mm, Locals.init []⟩)
      (erPut5_spec p hpu hp n _ d x0 x1 x2 x3 x4) hc
    exact h2
  unfold iirW
  rcases h1 : erAllocW m 20 with _ | ⟨q, m1⟩
  · rw [h1] at h; cases h
  obtain ⟨hI1, hE1⟩ := erAllocW_arr h1
  rw [h1, iirK_some] at h
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl; rw [iirK2_some] at h
  have e2 := put _ _ _ _ _ _ _ _ _ h2
  have i2 : m2.arr64 IW = m.arr64 IW := by rw [e2, wrER_IW, hI1]
  rw [i2] at h
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl; rw [iirK3_some] at h
  have e3 := put _ _ _ _ _ _ _ _ _ h3
  have i3 : m3.arr64 IW = m.arr64 IW := by rw [e3, wrER_IW, i2]
  rw [i3] at h
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h rfl; rw [iirK4_some] at h
  have e4 := put _ _ _ _ _ _ _ _ _ h4
  have i4 : m4.arr64 IW = m.arr64 IW := by rw [e4, wrER_IW, i3]
  rw [i4] at h
  obtain ⟨⟨r5, m5⟩, h5, h⟩ := of_K h rfl; rw [iirK5_some] at h
  have e5 := put _ _ _ _ _ _ _ _ _ h5
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  refine ⟨q, rfl, ?_⟩
  simp only [hE1] at e2
  subst e2 e3 e4 e5
  have hw : iirWs m cv caps = [3, erRd m cv, erRd m (cv + 1), erRd m (cv + 2), erRd m (cv + 3)] ++
      ([rdW (m.arr64 IW) caps, rdW (m.arr64 IW) (caps + 1), rdW (m.arr64 IW) (caps + 2),
        rdW (m.arr64 IW) (caps + 3), rdW (m.arr64 IW) (caps + 4)] ++
      ([rdW (m.arr64 IW) (caps + 5), rdW (m.arr64 IW) (caps + 6), rdW (m.arr64 IW) (caps + 7),
        rdW (m.arr64 IW) (caps + 8), rdW (m.arr64 IW) (caps + 9)] ++
       [rdW (m.arr64 IW) (caps + 10), rdW (m.arr64 IW) (caps + 11), rdW (m.arr64 IW) (caps + 12),
        rdW (m.arr64 IW) (caps + 13), rdW (m.arr64 IW) (caps + 14)])) := rfl
  dsimp only
  rw [hw, wrER_append, wrER_append, wrER_append]
  simp only [List.length_cons, List.length_nil]
  rw [show q + UInt64.ofNat 5 + UInt64.ofNat 5 = q + 10 by rw [UInt64.add_assoc]; rfl,
    show q + UInt64.ofNat 5 = q + 5 from rfl,
    show q + 10 + UInt64.ofNat 5 = q + 15 by rw [UInt64.add_assoc]; rfl]

/-- **`ind_info_rec` under the stage relation**: a fresh `.indInfo` record of the constant at `cv`
(decoded below the tops) and the capability record at `caps`. -/
theorem iirW_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cv caps q : Word} {cvv : IConstantVal} {c : IIndCaps}
    (h : iirW m cv caps = some (q, m')) (hS : StageR vis fe m a)
    (hcv : DecB (fun m => decCVp m cv.toNat) m cvv) (hcp : CapsAt m caps.toNat c) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') q.toNat = some (.indInfo cvv c) := by
  unfold iirW at h
  rcases h1 : erAllocW m 20 with _ | ⟨q1, m1⟩
  · rw [h1] at h; cases h
  rw [h1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS', hg, -, -, -, -, hget⟩ := erRec_stage h1 hS (iirWs m cv caps) (by simp [iirWs])
  have hlen : (iirWs m cv caps).length = 20 := by simp [iirWs]
  rw [hlen] at hget
  generalize hM : wrER m1 q1 (iirWs m cv caps) = M at hS' hg hget
  -- the constant's words
  have hcvE : decCV (erecP m) cv.toNat = some cvv := decCVp_truncM hcv
  have hcv0 := hcvE
  simp only [decCV, hlist?, bind, Option.bind_eq_some_iff, pure] at hcv0
  obtain ⟨nm, hnm, lps, ⟨lo, hlo, ll, hll, -⟩, t, ht, -⟩ := hcv0
  obtain ⟨w0, hw0, -, -⟩ := hd?_some hnm
  obtain ⟨w1, hw1, -⟩ : ∃ w, erecP m (cv.toNat + 1) = some w ∧ w.toNat = lo := by
    simp only [nat?, Option.map_eq_some_iff] at hlo; exact hlo
  obtain ⟨w2, hw2, -⟩ : ∃ w, erecP m (cv.toNat + 2) = some w ∧ w.toNat = ll := by
    simp only [nat?, Option.map_eq_some_iff, Nat.add_assoc] at hll; exact hll
  obtain ⟨w3, hw3, -, -⟩ := hd?_some ht
  have r0 : erRd m cv = w0 := (erRd_of_erecP (by simpa using hw0)).1
  obtain ⟨r1, -⟩ := erRd_add (j := 1) (cq := cv) (m := m) hw1 (by decide)
  obtain ⟨r2, -⟩ := erRd_add (j := 2) (cq := cv) (m := m) hw2 (by decide)
  obtain ⟨r3, -⟩ := erRd_add (j := 3) (cq := cv) (m := m) hw3 (by decide)
  simp only [show (UInt64.ofNat 1 : Word) = 1 from rfl, show (UInt64.ofNat 2 : Word) = 2 from rfl,
    show (UInt64.ofNat 3 : Word) = 3 from rfl] at r1 r2 r3
  have hw : ∀ i, i < 4 → erecP M (q1.toNat + 1 + i) = erecP M (cv.toNat + i) := by
    intro i hi
    rw [Nat.add_assoc, hget (1 + i) (by omega)]
    rcases i with _ | _ | _ | _ | i
    · rw [IWGrow.ext hg _ _ (by simpa using hw0)]; simp [iirWs, r0]
    · rw [IWGrow.ext hg _ _ hw1]; simp [iirWs, r1]
    · rw [IWGrow.ext hg _ _ hw2]; simp [iirWs, r2]
    · rw [IWGrow.ext hg _ _ hw3]; simp [iirWs, r3]
    · omega
  have hcv' : decCV (erecP M) (q1.toNat + 1) = some cvv := by
    rw [decCV_shift (by simpa using hw 0 (by decide)) (by simpa using hw 1 (by decide))
      (by simpa [Nat.add_assoc] using hw 2 (by decide)) (by simpa [Nat.add_assoc] using hw 3 (by decide))]
    exact ArrExt.decCV (IWGrow.ext hg) hcvE
  -- the capability record's words
  have hc15 := hcp.1
  have hcaps : decCaps (erecP M) (q1.toNat + 5) = some c := by
    refine hcp.2 (erecP M) (q1.toNat + 5) (fun i hi => ?_) (IWGrow.ext hg)
    rw [show q1.toNat + 5 + i = q1.toNat + (5 + i) by omega, hget (5 + i) (by omega)]
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have hIsz : iwTop m ≤ (m.arr64 IW).size := hS.iw.iw
    have gen : ∀ w : Word, w.toNat = caps.toNat + i →
        (iirWs m cv caps)[5 + i]? = some (rdW (m.arr64 IW) w) →
        (iirWs m cv caps)[5 + i]? = iwA m (caps.toNat + i) := fun w hw h => by
      rw [h, ← hw]; simp only [iwA, aread_apply, rdW]; rw [Array.getElem?_eq_getElem (by omega)]; simp
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    all_goals first
      | omega
      | exact gen _ rfl rfl
      | exact gen _ (by rw [UInt64.toNat_add]; simp; omega) rfl
  have n0 : nat? (erecP M) q1.toNat = some 3 := by
    have := hget 0 (by decide); simp only [Nat.add_zero] at this
    simp [nat?, this, iirWs]
  refine ⟨hS', hg, ?_⟩
  simp only [decCI, Option.bind_eq_bind, n0, Option.bind_some, hcv', hcaps, Option.pure_def]

section arms
variable (p : Prog) (n : Nat) (m : Mem) (p1 isRec o l vis i : Word) (r : List Word)
theorem icbiW_zero : icbiW p 0 m p1 isRec o l vis i = none := by simp [icbiW]
end arms
/-- `ind_info_rec`'s run, at any fuel. -/
theorem installIirRun {p : Prog} (hP : ConsIndsProg p) {n : Nat} {m m' : Mem} {cv caps : Word}
    {r : List Word} (h : callW p n "ind_info_rec" [cv, caps] m = some (r, m')) :
    ∃ q, r = [q] ∧ iirW m cv caps = some (q, m') := by
  rcases n with _ | k
  · rw [callW_zero] at h; cases h
  obtain ⟨s', rfl, -, hK⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iir_specK p hP.erAlloc hP.iir k _ cv caps) h
  rcases k with _ | j
  · exfalso
    cases h1 : erAllocW m 20 with
    | none => simp only [h1] at hK; cases hK
    | some x => obtain ⟨q, m1⟩ := x; simp only [h1, iirK_some, callW_zero] at hK; cases hK
  exact iirK_eq hP.recP.put hP.put5 hK

/-- **`cons_block_inds`' model refines `consBlockInds`** (pure in the twin): each member's former
pushed with its capability record `blockCapsAt bs i isRec`, the stage relation at the returned view. -/
theorem icbiW_ok {p : Prog} (hP : ConsIndsProg p) (p1 isRec : Word) (bs : BlockShape) (b : Bool)
    (hb : (isRec != 0) = b) (a : AState) (n : Nat) :
    ∀ (m m' : Mem) (vis : Word) (fe : IFEnv) (o l i : Word) (cvs : List IConstantVal) (r : List Word),
    StageR vis fe m a → DecB (fun m => decBS m p1.toNat) m bs → ShapeSrc m p1 →
    PSlR decCVp cvs o l m → i.toNat + l.toNat < 2 ^ 64 →
    icbiW p n m p1 isRec o l vis i = some (r, m') →
    StageR (r.headD 0) (ConRon.Arena.consBlockInds bs b cvs i.toNat fe) m' a ∧ IWGrow m m' := by
  induction n with
  | zero => intro m m' vis fe o l i cvs r _ _ _ _ _ h; rw [icbiW_zero] at h; cases h
  | succ n ih =>
  intro m m' vis fe o l i cvs r hS hq hsrc hcvs hil h
  by_cases hl : l = 0
  · rw [icbiW_nil p n m p1 isRec o l vis i hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : cvs = [] := by
      have h := hcvs.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact ⟨hS, IWGrow.refl m⟩
  obtain ⟨q, cv, rest, rfl, hw, hqb, hdcv, hrest⟩ := partsPSl_cons hcvs hl
  rw [icbiW_cons p n m p1 isRec o l vis i hl] at h
  simp only [ConRon.Arena.consBlockInds]
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [icbiK1])
  rw [icbiK1_some] at h
  obtain ⟨hS1, hg1, hca⟩ := blockCapsAt_ok hP.toCapsProg n hq hsrc hb h1 hS
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [icbiK2])
  rw [icbiK2_some] at h
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hlpos : 0 < l.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  have hol : o.toNat < iwTop m := by have := hcvs.2; omega
  have hw1 : rdW (m1.arr64 IW) o = UInt64.ofNat q := by
    rw [← hw]; simp only [rdW]; rw [hg1.iwGet _ hol]
  rw [hw1] at h2
  obtain ⟨q2, rfl, hW2⟩ := installIirRun hP h2
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  obtain ⟨hS2, hg2, hci⟩ := iirW_stage hW2 hS1 (by rw [hq']; exact hdcv.grow (OMono.decCVp _) hg1) hca
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [icbiK3])
  rw [icbiK3_some] at h
  simp only [List.headD_cons] at h3
  obtain ⟨hS3, hg3⟩ := envPush_stage hP.recP.rs hP.recP.push h3 hS2 hci
  have hg13 := (hg1.trans hg2).trans hg3
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hl1 : (l - 1).toNat = l.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [icbiK4])
  rw [icbiK4_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hrec := ih m3 m4 (r3.headD 0) _ (o + 1) (l - 1) (i + 1) rest r4 hS3
    (hq.grow (decBS_mono _) hg13) (partsHsrc_grow hg13 hq9 hsrc)
    (hrest.grow (fun q => OMono.decCVp q) hg13) (by omega) h4
  rw [hi1] at hrec
  exact ⟨by simpa using hrec.1, hg13.trans hrec.2⟩

/-- **`cons_block_inds` refines `consBlockInds`** (pure in the twin): the formers pushed, each with
its capability record, the stage relation at the returned view; the twin's state unchanged. -/
@[refines ConRon.Arena.consBlockInds]
theorem consBlockInds_refines (p : Prog) (hP : ConsIndsProg p) (n : Nat) (s₀ : St) (a : AState)
    (vis : Word) (fe : IFEnv) (p1 isRec o l i : Word) (bs : BlockShape) (b : Bool)
    (cvs : List IConstantVal) (hb : (isRec != 0) = b) (hS : StageR vis fe s₀.mem a)
    (hq : DecB (fun m => decBS m p1.toNat) s₀.mem bs) (hsrc : ShapeSrc s₀.mem p1)
    (hcvs : PSlR decCVp cvs o l s₀.mem) (hil : i.toNat + l.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_block_inds" [p1, isRec, o, l, vis, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      StageR (r.headD 0) (ConRon.Arena.consBlockInds bs b cvs i.toNat fe) s'.mem a ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ :=
  triple_post (icbi_spec p hP.cbi n s₀ p1 isRec o l vis i) fun r s' ⟨hl, hm⟩ =>
    ⟨hl, icbiW_ok hP p1 isRec bs b hb a n _ _ vis fe o l i cvs r hS hq hsrc hcvs hil hm⟩

end L.Ind

end

end
