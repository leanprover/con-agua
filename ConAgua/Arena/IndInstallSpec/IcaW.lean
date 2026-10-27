import ConAgua.Arena.IndInstallSpec.CapsProg
import ConAgua.Arena.IndInstallSpec.IcbiW
import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndPartsSpec.PartsPSlCons

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
  if rdW (m.arr64 IW) (pp + 1) ≤ mi then [0, 0, 0, 0]
  else
    let ms := rdW (m.arr64 IW) (rdW (m.arr64 IW) pp + mi)
    if rdW (m.arr64 IW) (ms + 3) = 0 then [0, 0, 0, ms]
    else [rdW (m.arr64 IW) (ms + 2), rdW (m.arr64 IW) (ms + 3), Cmp.evalW .eq (rdW (m.arr64 IW) (ms + 3)) 1, ms]

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
  let isP := Cmp.evalW .ne (rdW (m.arr64 IW) (pp + 8)) 0
  [Cmp.evalW .eq nIdx 0 &&& Cmp.evalW .eq isP 0 &&& Cmp.evalW .eq isRec 0,
   rdW (m.arr64 EREC) (rdW (m.arr64 IW) c), rdW (m.arr64 IW) (pp + 4), nF,
   Cmp.evalW .eq nIdx 0 &&& Cmp.evalW .eq nF 0 &&& Cmp.evalW .eq isRec 0,
   Cmp.evalW .eq (rdW (m.arr64 IW) (pp + 1)) 1 &&& Cmp.evalW .eq nF 0 &&& isP]

theorem capsOne_spec (p : Prog) (hp : p.lookup "block_caps_one" = some blockCapsOne) (n : Nat)
    (s₀ : St) (pp ms isRec : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "block_caps_one" [pp, ms, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r = capsOne s₀.mem pp ms isRec; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCapsOne]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
    finish (gen := 20) [capsOne, rdW_eq]

/-- After the first and second `rec5`. -/
def icaK7 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([q], m)
def icaK6 (q a0 a1 np c0 c1 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => icaK7 q (recW m 5 [a0, a1, np, c0, c1])
def icaK5b (w2 w6 z0 z1 z2 a0 a1 np c0 c1 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rq, m) => icaK6 (rq.headD 0) a0 a1 np c0 c1 (recW m 5 [w2, w6, z0, z1, z2])
/-- After the second copy: the record, three `rec5`s. -/
def icaK5 (pp w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => icaK5b w2 w6 z0 z1 z2 a0 a1 (rdW (m5.arr64 IW) (pp + 4)) (r5.headD 0) (r5.tail.headD 0)
      (recW m5 5 [w0, w1, w2, w3, w4])
/-- After the ctor names. -/
def icaK4 (p : Prog) (n : Nat) (pp w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => icaK5 pp w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1
      (callW p n "block_caps_at_er_copy" [r4.headD 0, r4.tail.headD 0] m4)
/-- After the member names' copy. -/
def icaK3 (p : Prog) (n : Nat) (pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => icaK4 p n pp w0 w1 w2 w3 w4 w6 z0 z1 z2 (r3.headD 0) (r3.tail.headD 0)
      (callW p n "block_caps_ctor_names" [coff, clen] m3)
/-- After the member names. -/
def icaK2 (p : Prog) (n : Nat) (pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => icaK3 p n pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2
      (callW p n "block_caps_at_er_copy" [r2.headD 0, r2.tail.headD 0] m2)

/-- **The model of `block_caps_fin`** (body fuel `n`). -/
def icfW (p : Prog) (n : Nat) (m : Mem) (pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 : Word) :
    Option (List Word × Mem) :=
  icaK2 p n pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 (callW p n "block_shape_member_names" [pp] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1 np c0 c1 q : Word)
  (r : List Word)
theorem icaK2_some : icaK2 p n pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 (some (r, m)) =
    icaK3 p n pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2
      (callW p n "block_caps_at_er_copy" [r.headD 0, r.tail.headD 0] m) := rfl
theorem icaK3_some : icaK3 p n pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 (some (r, m)) =
    icaK4 p n pp w0 w1 w2 w3 w4 w6 z0 z1 z2 (r.headD 0) (r.tail.headD 0)
      (callW p n "block_caps_ctor_names" [coff, clen] m) := rfl
theorem icaK4_some : icaK4 p n pp w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1 (some (r, m)) =
    icaK5 pp w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1
      (callW p n "block_caps_at_er_copy" [r.headD 0, r.tail.headD 0] m) := rfl
theorem icaK5_some : icaK5 pp w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1 (some (r, m)) =
    icaK5b w2 w6 z0 z1 z2 a0 a1 (rdW (m.arr64 IW) (pp + 4)) (r.headD 0) (r.tail.headD 0)
      (recW m 5 [w0, w1, w2, w3, w4]) := rfl
theorem icaK5b_some : icaK5b w2 w6 z0 z1 z2 a0 a1 np c0 c1 (some (r, m)) =
    icaK6 (r.headD 0) a0 a1 np c0 c1 (recW m 5 [w2, w6, z0, z1, z2]) := rfl
theorem icaK6_some : icaK6 q a0 a1 np c0 c1 (some (r, m)) = icaK7 q (recW m 5 [a0, a1, np, c0, c1]) := rfl
theorem icaK7_some : icaK7 q (some (r, m)) = some ([q], m) := rfl
end arms
attribute [ind_grind] icaK2_some icaK3_some icaK4_some icaK5_some icaK5b_some icaK6_some icaK7_some

theorem icf_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (hr5 : p.lookup "rec5" = some rec5)
    (hp : p.lookup "block_caps_fin" = some blockCapsFin) (n : Nat) (s₀ : St)
    (pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "block_caps_fin"
      [pp, coff, clen, w0, w1, w2, w3, w4, w6, z0, z1, z2]
    ⦃fun r s' => LocEq s' s₀ ∧ icfW p n s₀.mem pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 = some (r, s'.mem); ⊤⦄ := by
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

/-- After `lv_zero_caps`: the record. -/
def icaK1 (p : Prog) (n : Nat) (pp coff clen : Word) (ws : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => icaKF (callW p n "block_caps_fin" [pp, coff, clen, ws.headD 0, ws.tail.headD 0,
      ws.tail.tail.headD 0, ws.tail.tail.tail.headD 0, ws.tail.tail.tail.tail.headD 0,
      ws.tail.tail.tail.tail.tail.headD 0, r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0] m1)
/-- After the branch words. -/
def icaKW (p : Prog) (n : Nat) (pp coff clen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ws, m) => icaK1 p n pp coff clen ws (callW p n "lv_zero_caps" [rdW (m.arr64 IW) (pp + 6)] m)
/-- After `block_caps_head`. -/
def icaKH (p : Prog) (n : Nat) (pp isRec : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (h, m) => icaKW p n pp (h.headD 0) (h.tail.headD 0)
      (if h.tail.tail.headD 0 = 1 then callW p n "block_caps_one" [pp, h.tail.tail.tail.headD 0, isRec] m
       else some ([0, 0, 0, 0, 0, 0], m))

/-- **The model of `block_caps_at(p, mi, is_rec)`** (body fuel `n`). -/
def icaW (p : Prog) (n : Nat) (m : Mem) (pp mi isRec : Word) : Option (List Word × Mem) :=
  icaKH p n pp isRec (callW p n "block_caps_head" [pp, mi] m)

section arms2
variable (p : Prog) (n : Nat) (m : Mem) (pp coff clen isRec : Word) (ws r : List Word)
theorem icaK1_some : icaK1 p n pp coff clen ws (some (r, m)) =
    icaKF (callW p n "block_caps_fin" [pp, coff, clen, ws.headD 0, ws.tail.headD 0,
      ws.tail.tail.headD 0, ws.tail.tail.tail.headD 0, ws.tail.tail.tail.tail.headD 0,
      ws.tail.tail.tail.tail.tail.headD 0, r.headD 0, r.tail.headD 0, r.tail.tail.headD 0] m) := rfl
theorem icaKF_some : icaKF (some (r, m)) = some ([r.headD 0], m) := rfl
theorem icaKW_some : icaKW p n pp coff clen (some (ws, m)) =
    icaK1 p n pp coff clen ws (callW p n "lv_zero_caps" [rdW (m.arr64 IW) (pp + 6)] m) := rfl
theorem icaKH_one (h : r.tail.tail.headD 0 = 1) : icaKH p n pp isRec (some (r, m)) =
    icaKW p n pp (r.headD 0) (r.tail.headD 0)
      (callW p n "block_caps_one" [pp, r.tail.tail.tail.headD 0, isRec] m) := by
  simp only [icaKH, h, ↓reduceIte]
theorem icaKH_rest (h : ¬ r.tail.tail.headD 0 = 1) : icaKH p n pp isRec (some (r, m)) =
    icaKW p n pp (r.headD 0) (r.tail.headD 0) (some ([0, 0, 0, 0, 0, 0], m)) := by
  simp only [icaKH, h, ↓reduceIte]
end arms2
attribute [ind_grind] icaK1_some icaKF_some icaKW_some icaKH_one icaKH_rest

set_option maxHeartbeats 1600000 in
theorem ica_spec (p : Prog) (hp : p.lookup "block_caps_at" = some blockCapsAt) (n : Nat)
    (s₀ : St) (pp mi isRec : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "block_caps_at" [pp, mi, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ icaW p n s₀.mem pp mi isRec = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCapsAt]
  vcgen [exec, step, L.evalE_spec, evalC, evalArgs, setLoc, setLocs,
    callW_spec p n "block_caps_head", callW_spec p n "block_caps_one",
    callW_spec p n "lv_zero_caps", callW_spec p n "block_caps_fin"]
  all_goals simp_all [LocEq, Expr.pval, L.Arena.rd64_rdWC, BinOp.eval, Cmp.eval, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal,
    Sig.retOr, -UInt64.not_lt, -UInt64.not_le,
    icaW, icaKH, icaK1_some, icaKF_some, icaKW_some]

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
  q + ws.length ≤ iwTop m ∧ ∀ i < ws.length, (iwA m)[q + i]? = ws[i]?

/-- A handle slice of the record pool below its top. -/
def ESl (m : Mem) (o l : Word) (xs : List NIdx) : Prop :=
  o.toNat + l.toNat ≤ erTop m ∧ hslice? (erA m) o.toNat l.toNat = some xs

theorem CapsWords.grow {m m' : Mem} {q : Nat} {ws : List Word} (h : CapsWords m q ws)
    (hg : IWGrow m m') : CapsWords m' q ws :=
  ⟨Nat.le_trans h.1 hg.1, fun i hi => by
    simp only [iwA]; rw [hg.2.2.1 _ (by have := h.1; omega)]; exact h.2 i hi⟩

theorem installHslice_ext {a b : Array Word} {o l : Nat} {xs : List NIdx}
    (he : ∀ j < l, b[o + j]? = a[o + j]?) (h : hslice? a o l = some xs) : hslice? b o l = some xs := by
  rw [← h]; unfold hslice?
  refine mapM_congr_range _ fun j hj => ?_
  have : j < l := List.mem_range.mp hj
  simp only [hd?, he j this]

theorem ESl.grow {m m' : Mem} {o l : Word} {xs : List NIdx} (h : ESl m o l xs) (hg : IWGrow m m') :
    ESl m' o l xs :=
  ⟨Nat.le_trans h.1 hg.2.1, installHslice_ext (fun j hj => by
    simp only [erA]; rw [hg.2.2.2 _ (by have := h.1; omega)]) h.2⟩

/-- An `IW` handle slice copied into `EREC` words. -/
theorem installHslice_copy {a b : Array Word} {o e l : Nat} {xs : List NIdx}
    (he : ∀ j < l, b[e + j]? = a[o + j]?) (h : hslice? a o l = some xs) : hslice? b e l = some xs := by
  rw [← h]; unfold hslice?
  refine mapM_congr_range _ fun j hj => ?_
  have : j < l := List.mem_range.mp hj
  simp only [hd?, he j this]

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
theorem installErCopy {p : Prog} (hP : CapsProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {o l : Word} {r : List Word} {xs : List NIdx}
    (h : callW p n "block_caps_at_er_copy" [o, l] m = some (r, m')) (hS : StageR dn vis fe m a)
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ ESl m' (r.headD 0) (r.tail.headD 0) xs := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockCapsAtErCopy_spec p hP.erAlloc hP.erCopyGo hP.erCopy n _ o l) h
  simp only at hW
  obtain ⟨hI1, hE1, hsz, hEs, hcl⟩ := hS.2
  obtain ⟨hr, htq, hcp, hf, hlow, htop, hroom, -⟩ := capsErCopyW_post hW hsz hEs (by omega) (by omega)
  obtain ⟨hS', hg⟩ := StageR.erec hS hf hlow (by omega) (by omega)
  refine ⟨hS', hg, ?_⟩
  subst hr
  simp only [List.headD_cons, List.tail_cons]
  refine ⟨by rw [htq, htop]; exact Nat.le_refl _, ?_⟩
  rw [htq]
  exact installHslice_copy (a := iwA m) (o := o.toNat) (fun j hj => hcp j hj) hd

theorem installRec5 {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {ws r : List Word}
    (h : recW m 5 ws = some (r, m')) (hS : StageR dn vis fe m a) (hl : ws.length = 5) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ r = [rdW (m.arr64 CTL) 200] ∧
      (rdW (m.arr64 CTL) 200).toNat = iwTop m ∧ CapsWords m' (iwTop m) ws ∧ iwTop m' = iwTop m + 5 := by
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage h hS (by rw [hl]; rfl)
  refine ⟨hS', hg, hr, rfl, ⟨by rw [htop, hl]; exact Nat.le_refl _, fun i hi => ?_⟩, by rw [htop, hl]⟩
  exact hget i hi

/-- **`block_caps_fin`'s record**: the stage relation kept, the 15 words at the returned pointer,
the member names and the ctor names as `EREC` slices below the record pool's top. -/
theorem icfW_ok {p : Prog} (hP : CapsProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState}
    {pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 : Word} {r : List Word} {bs : BlockShape}
    {cs : List (IConstantVal × Nat)}
    (h : icfW p n m pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 = some (r, m'))
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcs : PSlR decCN cs coff clen m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ ∃ aq al cq cl : Word,
      CapsWords m' (r.headD 0).toNat
        [w0, w1, w2, w3, w4, w2, w6, z0, z1, z2, aq, al, UInt64.ofNat bs.nP, cq, cl] ∧
      ESl m' aq al bs.memberNames ∧ ESl m' cq cl (cs.map (·.1.name)) := by
  obtain ⟨hI1, hE1, hsz, hEs, hcl⟩ := hS.2
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
  have hS1 : StageR dn vis fe s1.mem a := stage_frame_iw hS hf1 (by
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
  obtain ⟨hI2, hE2', hsz2, hEs2, hcl2⟩ := hS2.2
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
  have hS3 : StageR dn vis fe s3.mem a := stage_frame_iw hS2 hf3 (by
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

theorem installDecPW {a : Array Word} {dn : NIdx → Option ConLeche.Name} {e : Nat} {z0 z1 z2 : Word}
    (h7 : a[e + 7]? = some z0) (h8 : a[e + 8]? = some z1) (h9 : a[e + 9]? = some z2) :
    decPW a dn (e + 7) = pwWords dn a z0 z1 z2 := by
  unfold decPW pwWords
  simp only [nat?, hlist?, h7, show e + 7 + 1 = e + 8 by omega, show e + 8 + 1 = e + 9 by omega, h8, h9,
    Option.map_some, bind, Option.bind_some]
  rfl

/-- **`decCaps` of 15 words.** -/
theorem installDecCaps {a : Array Word} {dn : NIdx → Option ConLeche.Name} {e : Nat}
    {w0 w1 w2 w3 w4 w5 w6 z0 z1 z2 aq al np cq cl : Word} {z : ConLeche.PropWhen} {xs ys : List NIdx}
    (h : ∀ i < 15, a[e + i]? = [w0, w1, w2, w3, w4, w5, w6, z0, z1, z2, aq, al, np, cq, cl][i]?)
    (hw1 : H w1) (hz : pwWords dn a z0 z1 z2 = some z) (hx : hslice? a aq.toNat al.toNat = some xs)
    (hy : hslice? a cq.toNat cl.toNat = some ys) :
    decCaps a dn e = some (IIndCaps.mk (w0 != 0) (decI w1) w2.toNat w3.toNat (w4 != 0) w5.toNat
      (w6 != 0) z xs np.toNat ys) := by
  have g : ∀ i (hi : i < 15), a[e + i]? = some ([w0, w1, w2, w3, w4, w5, w6, z0, z1, z2, aq, al, np, cq, cl][i]'(by simpa using hi)) :=
    fun i hi => by rw [h i hi]; simp
  have e0 := g 0 (by decide); have e1 := g 1 (by decide); have e2 := g 2 (by decide)
  have e3 := g 3 (by decide); have e4 := g 4 (by decide); have e5 := g 5 (by decide)
  have e6 := g 6 (by decide); have e7 := g 7 (by decide); have e8 := g 8 (by decide)
  have e9 := g 9 (by decide); have e10 := g 10 (by decide); have e11 := g 11 (by decide)
  have e12 := g 12 (by decide); have e13 := g 13 (by decide); have e14 := g 14 (by decide)
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2 e3 e4 e5 e6 e7
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at e8 e9 e10 e11 e12 e13 e14
  have hpw := installDecPW (dn := dn) e7 e8 e9
  unfold decCaps
  rw [hpw, hz]
  simp only [bool?, hd?, nat?, hlist?, e0, e1, e2, e3, e4, e5, e6, e10, e12, e13,
    show e + 10 + 1 = e + 11 by omega, show e + 13 + 1 = e + 14 by omega, e11, e14, Option.map_some,
    hw1, ite_true, hx, hy, bind, Option.bind_some, pure]

/-! ## `block_caps_at`'s relation -/

theorem installEvalW3 (c1 c2 c3 : Cmp) (a1 b1 a2 b2 a3 b3 : Word) :
    (Cmp.evalW c1 a1 b1 &&& Cmp.evalW c2 a2 b2 &&& Cmp.evalW c3 a3 b3 != 0) =
      (c1.eval a1 b1 && c2.eval a2 b2 && c3.eval a3 b3) := by
  unfold Cmp.evalW
  cases c1.eval a1 b1 <;> cases c2.eval a2 b2 <;> cases c3.eval a3 b3 <;> decide

theorem installOfNatBeq {x c : Nat} (hx : x < 2 ^ 64) (hc : c < 2 ^ 64) :
    (UInt64.ofNat x == UInt64.ofNat c) = (x == c) := by
  by_cases h : x = c
  · subst h; simp
  · have : UInt64.ofNat x ≠ UInt64.ofNat c := fun e => h (by
      have := congrArg UInt64.toNat e
      rwa [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hc] at this)
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

theorem installNeEval (w : Word) : Cmp.eval .eq (Cmp.evalW .ne w 0) 0 = !(w != 0) := by
  unfold Cmp.evalW; cases h : Cmp.eval .ne w 0 <;> simp_all [Cmp.eval]

/-- A pure callee's run: the memory unchanged, the result its model. -/
theorem installPureCall {p : Prog} {n : Nat} {f : FnName} {args : List Word} {m m' : Mem}
    {R r : List Word}
    (h : ⦃fun st => st = (⟨m, Locals.init []⟩ : St)⦄ invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' ⟨m, Locals.init []⟩ ∧ s'.mem = m ∧ r = R; ⊤⦄)
    (hc : callW p n f args m = some (r, m')) : r = R ∧ m' = m := by
  obtain ⟨s', rfl, -, h1, h2⟩ := triple_of_callW h hc
  exact ⟨h2, h1⟩

/-- **After `lv_zero_caps`: the record.** `block_caps_fin`'s run gives a capability record with the
branch words, the zero-ness, the member names and the ctor names. -/
theorem installCapsTail {p : Prog} (hP : CapsProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m m1 m2 : Mem} {a : AState} {pp coff clen w0 w1 w2 w3 w4 w6 : Word}
    {r1 r2 : List Word} {bs : BlockShape} {lv : ConLeche.Level} {cs : List (IConstantVal × Nat)}
    (hS1 : StageR dn vis fe m1 a) (hg1 : IWGrow m m1) (hz : decZC dn m1 r1 lv)
    (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcs : PSlR decCN cs coff clen m1) (hw1 : H w1)
    (h2 : callW p (n + 1) "block_caps_fin" [pp, coff, clen, w0, w1, w2, w3, w4, w6, r1.headD 0,
      r1.tail.headD 0, r1.tail.tail.headD 0] m1 = some (r2, m2)) :
    StageR dn vis fe m2 a ∧ IWGrow m m2 ∧ CapsAt dn m2 (r2.headD 0).toNat
      (IIndCaps.mk (w0 != 0) (decI w1) w2.toNat w3.toNat (w4 != 0) w2.toNat (w6 != 0)
        (ConLeche.Level.zeronessOf lv) bs.memberNames bs.nP (cs.map (·.1.name))) := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (icf_spec p hP.alloc hP.rec5 hP.fin n _ pp coff clen w0 w1 w2 w3 w4 w6 _ _ _) h2
  simp only at hW
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨-, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  obtain ⟨hS2, hg2, aq, al, cq, cl, hcw, hEa, hEc⟩ :=
    icfW_ok hP hW hS1 (hq.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc) hcs
  refine ⟨hS2, hg1.trans hg2, by have := hcw.1; simpa using this, fun a e ha he => ?_⟩
  have hag : ∀ i < erTop m1, a[i]? = (erA m1)[i]? := fun i hi => by
    rw [he i (Nat.lt_of_lt_of_le hi hg2.2.1)]; simp only [erA]; rw [hg2.2.2.2 i hi]
  have hd := installDecCaps (dn := dn) (e := e) (a := a)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w2) (w6 := w6)
    (z0 := r1.headD 0) (z1 := r1.tail.headD 0) (z2 := r1.tail.tail.headD 0) (aq := aq) (al := al)
    (np := UInt64.ofNat bs.nP) (cq := cq) (cl := cl)
    (fun i hi => (ha i hi).trans (hcw.2 i (by simpa using hi))) hw1 (hz a hag)
    (installHslice_ext (fun j hj => he _ (by have := hEa.1; omega)) hEa.2)
    (installHslice_ext (fun j hj => he _ (by have := hEc.1; omega)) hEc.2)
  rw [hd, UInt64.toNat_ofNat_of_lt' hnpb]

/-- **`block_caps_at`'s model refines `blockCapsAt`**, from a refinement `hLZ` of its one
twin-visible callee `lv_zero_caps` at the entry memory and state (the twin's only effect is that
`readLevelM`), whose extra post `T` on the twin's state is passed through. -/
theorem icaW_simG {p : Prog} (hP : CapsProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp mi isRec : Word} {bs : BlockShape} {b : Bool}
    {T : AState → Prop}
    (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hb : (isRec != 0) = b)
    (hLZ : ∀ k, Sim (callW p k "lv_zero_caps" [rdW (m.arr64 IW) (pp + 6)] m) (readLevelM bs.resSort) a
      (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decZC dn m' r x) ∧ T a')) :
    Sim (icaW p n m pp mi isRec) (ConRon.Arena.blockCapsAt bs mi.toNat b) a
      (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ CapsAt dn m' (r.headD 0).toNat x) ∧
        T a') := by
  rcases n with _ | n
  · rw [icaW, callW_zero]; exact Sim.of_none
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, -⟩ := partsShapeFacts hq hsrc
  have hkw := partsShapeK hq' hq9
  obtain ⟨hnpw, hnpb, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, hpr⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdm, hob⟩ := partsAt decMS_mono hmem
  have hdm' : decPL (truncM m) (decMS (truncM m)) o.toNat l.toNat = some bs.members := hdm
  have hlk : bs.k = l.toNat := decPL_length _ hdm'
  have hkb : bs.k < 2 ^ 64 := by rw [hlk]; exact l.toNat_lt
  obtain ⟨hw0, -, -⟩ := partsIwRd ho (w := pp) rfl
  rw [UInt64.ofNat_toNat] at hw0
  -- the lv_zero_caps step and the record, shared by the branches
  have hlz : ∀ (ws : List Word) (cs : List (IConstantVal × Nat)) (coff clen : Word)
      (R : ConLeche.Level → IIndCaps), PSlR decCN cs coff clen m → H (ws.tail.headD 0) →
      (∀ lv, R lv = IIndCaps.mk (ws.headD 0 != 0) (decI (ws.tail.headD 0)) (ws.tail.tail.headD 0).toNat
        (ws.tail.tail.tail.headD 0).toNat (ws.tail.tail.tail.tail.headD 0 != 0)
        (ws.tail.tail.headD 0).toNat (ws.tail.tail.tail.tail.tail.headD 0 != 0)
        (ConLeche.Level.zeronessOf lv) bs.memberNames bs.nP (cs.map (·.1.name))) →
      Sim (icaKW p (n + 1) pp coff clen (some (ws, m)))
        (readLevelM bs.resSort >>= fun l => pure (R l)) a
        (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ CapsAt dn m' (r.headD 0).toNat x) ∧
          T a') := by
    intro ws cs coff clen R hcs hw1 hR
    rw [icaKW_some]
    refine Sim.bindK (K := icaK1 p (n + 1) pp coff clen ws) (body := fun r1 m1 => icaKF (callW p (n + 1)
        "block_caps_fin" [pp, coff, clen, ws.headD 0, ws.tail.headD 0, ws.tail.tail.headD 0,
          ws.tail.tail.tail.headD 0, ws.tail.tail.tail.tail.headD 0, ws.tail.tail.tail.tail.tail.headD 0,
          r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0] m1)) rfl (fun _ _ => rfl)
      (hLZ (n + 1)) ?_
    rintro r1 lv m1 a1 ⟨⟨hS1, hg1, hz⟩, hT1⟩
    refine Sim.mstep (K := icaKF) rfl (fun _ _ => rfl) fun r2 m2 h2 => ?_
    obtain ⟨hS2, hg2, hca⟩ := installCapsTail hP n hS1 hg1 hz hq hsrc (hcs.grow decCN_mono hg1) hw1 h2
    refine Sim.ret ⟨⟨hS2, hg2, ?_⟩, hT1⟩
    rw [hR]; simpa using hca
  unfold icaW
  refine Sim.mstep (K := icaKH p (n + 1) pp isRec) rfl (fun _ _ => rfl) fun r0 m0 h0 => ?_
  obtain ⟨hr0, hm0⟩ := installPureCall (capsHead_spec p hP.head n _ pp mi) h0
  subst m0; subst r0
  unfold ConRon.Arena.blockCapsAt
  dsimp only
  rcases Nat.lt_or_ge mi.toNat bs.k with hmi | hmi
  case inr =>
    have hnone : bs.members[mi.toNat]? = none :=
        List.getElem?_eq_none (by unfold BlockShape.k at hmi; omega)
    have hh : capsHead m pp mi = [0, 0, 0, 0] := by
      unfold capsHead; rw [ite_eq_left]
      rw [hkw, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hkb]; omega
    rw [hh, icaKH_rest (h := by decide)]
    simp only [hnone]
    exact hlz [0, 0, 0, 0, 0, 0] [] 0 0 _ (PSlR.nil decCN m) (by decide) (fun _ => rfl)
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
  obtain ⟨⟨cvp, hcvp, hcvT⟩, hni, hct⟩ := decMS_some hmsd
  obtain ⟨co, cl, hco, hcl, hcd, hcb⟩ := partsAt decCN_mono hct
  have hv3 : v + 3 < iwTop m := partsIwLt hcl
  obtain ⟨hw2, -, -⟩ := partsIwRd hco (w := UInt64.ofNat v + 2) (by rw [UInt64.toNat_add, hv']; simp; omega)
  obtain ⟨hw3, -, -⟩ := partsIwRd hcl (w := UInt64.ofNat v + 3) (by rw [UInt64.toNat_add, hv']; simp; omega)
  obtain ⟨hw1n, hnb, -⟩ := partsIwRd hni (w := UInt64.ofNat v + 1) (by rw [UInt64.toNat_add, hv']; simp; omega)
  rw [UInt64.ofNat_toNat] at hw2 hw3
  have hcd' : decPL (truncM m) (decCN (truncM m)) co.toNat cl.toNat = some msh.ctors := hcd
  have hlenc : msh.ctors.length = cl.toNat := decPL_length _ hcd'
  have hhd : capsHead m pp mi = if cl = 0 then [0, 0, 0, UInt64.ofNat v]
      else [co, cl, Cmp.evalW .eq cl 1, UInt64.ofNat v] := by
    unfold capsHead
    rw [ite_eq_right (by rw [hkw, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hkb]; omega)]
    simp only [hw0, hwv, hw2, hw3]
  rcases hcs : msh.ctors with _ | ⟨c, _ | ⟨c2, cs⟩⟩
  · -- no constructor
    have hcl0 : cl = 0 := by
      apply UInt64.toNat_inj.mp; rw [← hlenc, hcs]; rfl
    rw [hhd, ite_eq_left hcl0, icaKH_rest (h := by simp)]
    exact hlz [0, 0, 0, 0, 0, 0] [] 0 0 _ (PSlR.nil decCN m) (by decide) (fun _ => rfl)
  · -- one constructor
    have hcl1 : cl = 1 := by apply UInt64.toNat_inj.mp; rw [← hlenc, hcs]; rfl
    subst hcl1
    rw [hhd, ite_eq_right (by decide), icaKH_one (h := rfl)]
    refine Sim.mstep (K := icaKW p (n + 1) pp co 1) rfl (fun _ _ => rfl) fun r1 m1 h1 => ?_
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
    -- the `isProp` word
    have hpr' := hpr
    simp only [iwB, bool?, Option.map_eq_some_iff] at hpr'
    obtain ⟨w8, hw8, hw8p⟩ := hpr'
    obtain ⟨-, hw8i⟩ := truncM_iw_get hw8
    have h8 : (pp + 8).toNat = pp.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
    have hrw8 : rdW (m.arr64 IW) (pp + 8) = w8 := rdW_of_get? h8.symm (by simpa [iwA] using hw8i)
    have hcb1 : co.toNat + (1 : Word).toNat ≤ iwTop m := hcb.resolve_left (by decide)
    refine hlz (capsOne m pp (UInt64.ofNat v) isRec) [c] co 1 _ ⟨by rw [← hcs]; exact hcd, hcb1⟩
      (by simp only [capsOne, List.headD_cons, List.tail_cons, hw2, hwc, hwcv]; exact hn32)
      (fun lv => ?_)
    simp only [capsOne, List.headD_cons, List.tail_cons, hw2, hwc, hwcv, hw1n, hwnF, hnpw, hkw, hrw8,
      hnm, installEvalW3, installNeEval]
    have e1 : (UInt64.ofNat msh.nIdx == (0 : Word)) = (msh.nIdx == 0) := installOfNatBeq (c := 0) hnb (by decide)
    have e2 : (UInt64.ofNat c.snd == (0 : Word)) = (c.snd == 0) := installOfNatBeq (c := 0) hnFb (by decide)
    have e3 : (UInt64.ofNat bs.k == (1 : Word)) = (bs.k == 1) := installOfNatBeq (c := 1) hkb (by decide)
    have e4 : (isRec == 0) = !b := by rw [← hb]; simp [bne]
    simp only [Cmp.eval, e1, e2, e3, e4, hw8p, UInt64.toNat_ofNat_of_lt' hnpb,
      UInt64.toNat_ofNat_of_lt' hnFb, List.map_cons, List.map_nil]
    by_cases h1 : msh.nIdx = 0 <;> by_cases h2 : c.snd = 0 <;> cases bs.isProp <;> cases b <;> simp [h1, h2, bne]
  · -- two or more
    have hcl2 : 2 ≤ cl.toNat := by rw [← hlenc, hcs]; simp
    have hne0 : cl ≠ 0 := fun e => by rw [e] at hcl2; simp at hcl2
    have hne1 : Cmp.evalW .eq cl 1 ≠ 1 := by
      have : cl ≠ 1 := fun e => by rw [e] at hcl2; simp at hcl2
      simp [Cmp.evalW, Cmp.eval, this]
    rw [hhd, ite_eq_right hne0, icaKH_rest (h := by simpa using hne1)]
    have hbd : co.toNat + cl.toNat ≤ iwTop m := hcb.resolve_left hne0
    exact hlz [0, 0, 0, 0, 0, 0] (c :: c2 :: cs) co cl _ ⟨by rw [← hcs]; exact hcd, hbd⟩ (by decide)
      (fun _ => rfl)

/-- **`block_caps_at` refines `blockCapsAt`, as a call** (`icaW_simG`: from a refinement of its
`lv_zero_caps` call, whose extra post `T` is passed through). -/
theorem blockCapsAt_simG {p : Prog} (hP : CapsProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp mi isRec : Word} {bs : BlockShape} {b : Bool}
    {T : AState → Prop}
    (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp) (hb : (isRec != 0) = b)
    (hLZ : ∀ k, Sim (callW p k "lv_zero_caps" [rdW (m.arr64 IW) (pp + 6)] m) (readLevelM bs.resSort) a
      (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decZC dn m' r x) ∧ T a')) :
    Sim (callW p n "block_caps_at" [pp, mi, isRec] m) (ConRon.Arena.blockCapsAt bs mi.toNat b) a
      (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ CapsAt dn m' (r.headD 0).toNat x) ∧
        T a') := by
  intro r m' e
  rcases n with _ | k
  · rw [callW_zero] at e; cases e
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ica_spec p hP.caps k _ pp mi isRec) e
  exact icaW_simG hP k hq hsrc hb hLZ r _ hW

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
  [3, rdW (m.arr64 EREC) cv, rdW (m.arr64 EREC) (cv + 1), rdW (m.arr64 EREC) (cv + 2), rdW (m.arr64 EREC) (cv + 3), rdW (m.arr64 IW) caps, rdW (m.arr64 IW) (caps + 1), rdW (m.arr64 IW) (caps + 2), rdW (m.arr64 IW) (caps + 3), rdW (m.arr64 IW) (caps + 4), rdW (m.arr64 IW) (caps + 5), rdW (m.arr64 IW) (caps + 6), rdW (m.arr64 IW) (caps + 7), rdW (m.arr64 IW) (caps + 8), rdW (m.arr64 IW) (caps + 9), rdW (m.arr64 IW) (caps + 10), rdW (m.arr64 IW) (caps + 11), rdW (m.arr64 IW) (caps + 12), rdW (m.arr64 IW) (caps + 13), rdW (m.arr64 IW) (caps + 14)]

theorem erPut5_spec (p : Prog) (hp : p.lookup "er_put5" = some erPut5) (n : Nat) (s₀ : St)
    (d x0 x1 x2 x3 x4 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "er_put5" [d, x0, x1, x2, x3, x4]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = wrER s₀.mem d [x0, x1, x2, x3, x4]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erPut5]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
    finish [wrER, UInt64.add_assoc]

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
  | some (q, m1) => iirK2 p n caps q (callW p n "er_put5" [q, 3, rdW (m1.arr64 EREC) cv,
      rdW (m1.arr64 EREC) (cv + 1), rdW (m1.arr64 EREC) (cv + 2), rdW (m1.arr64 EREC) (cv + 3)] m1)

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
    rdW (m.arr64 EREC) cv, rdW (m.arr64 EREC) (cv + 1), rdW (m.arr64 EREC) (cv + 2),
    rdW (m.arr64 EREC) (cv + 3)] m) := rfl
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
    finish (gen := 40) (instances := 20000) [rdW_eq]

theorem wrER_IW (m : Mem) (q : Word) (ws : List Word) : (wrER m q ws).arr64 IW = m.arr64 IW :=
  (wrER_frame ws m q).1 IW (by simp [EREC, IW]) (by decide)

theorem erAllocW_arr {m m1 : Mem} {k q : Word} (h : erAllocW m k = some (q, m1)) :
    m1.arr64 IW = m.arr64 IW ∧ m1.arr64 EREC = m.arr64 EREC := by
  simp only [erAllocW] at h; split at h; · cases h
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  simp only [erAllocMem]
  exact ⟨Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)⟩

/-- `ind_info_rec`'s four writes are the record written at once. -/
theorem iirK_eq {p : Prog} (hp : p.lookup "er_put5" = some erPut5) {n : Nat} {m m' : Mem}
    {cv caps : Word} {r : List Word} (h : iirK p (n + 1) cv caps (erAllocW m 20) = some (r, m')) :
    ∃ q, r = [q] ∧ iirW m cv caps = some (q, m') := by
  have put : ∀ (mm : Mem) (d x0 x1 x2 x3 x4 : Word) (rr : List Word) (mm' : Mem),
      callW p (n + 1) "er_put5" [d, x0, x1, x2, x3, x4] mm = some (rr, mm') →
      mm' = wrER mm d [x0, x1, x2, x3, x4] := by
    intro mm d x0 x1 x2 x3 x4 rr mm' hc
    obtain ⟨s', rfl, -, h2⟩ := triple_of_callW (s₀ := ⟨mm, Locals.init []⟩)
      (erPut5_spec p hp n _ d x0 x1 x2 x3 x4) hc
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
  rw [hE1] at e2
  subst e2 e3 e4 e5
  have hw : iirWs m cv caps = [3, rdW (m.arr64 EREC) cv, rdW (m.arr64 EREC) (cv + 1),
      rdW (m.arr64 EREC) (cv + 2), rdW (m.arr64 EREC) (cv + 3)] ++
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
(decoded below the tops) and the capability record at `caps`; its name word a handle. -/
theorem iirW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cv caps q : Word} {cvv : IConstantVal} {c : IIndCaps}
    (h : iirW m cv caps = some (q, m')) (hS : StageR dn vis fe m a)
    (hcv : DecB (fun m => decCVp m cv.toNat) m cvv) (hcp : CapsAt dn m caps.toNat c) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') dn q.toNat = some (.indInfo cvv c) ∧ H (rdW (m'.arr64 EREC) (q + 1)) := by
  unfold iirW at h
  rcases h1 : erAllocW m 20 with _ | ⟨q1, m1⟩
  · rw [h1] at h; cases h
  rw [h1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS', hg, hq, htop, hget⟩ := erRec_stage h1 hS (iirWs m cv caps) (by simp [iirWs])
  have hlen : (iirWs m cv caps).length = 20 := by simp [iirWs]
  rw [hlen] at htop hget
  generalize hM : wrER m1 q1 (iirWs m cv caps) = M at hS' hg htop hget
  obtain ⟨-, hEtop, -, hEsz, -⟩ := hS.2
  obtain ⟨-, hEtop', -, hEsz', -⟩ := hS'.2
  have hP : ∀ j, j < 20 → (erecP M)[q1.toNat + j]? = (iirWs m cv caps)[j]? := fun j hj => by
    rw [erecP_getE (by omega)]; exact hget j hj
  -- the constant's words
  have hcvE : decCV (erecP m) cv.toNat = some cvv := decCVp_truncM hcv
  have h3 : (erecP m)[cv.toNat + 3]? ≠ none := by
    have := decCV_type hcvE; intro e; simp [hd?, e] at this
  have hcq : cv.toNat + 4 ≤ erTop m := by
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h3; have := erecP_lt hv; omega
  have c1 : (cv + 1).toNat = cv.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have c2 : (cv + 2).toNat = cv.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have c3 : (cv + 3).toNat = cv.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have hw : ∀ i, i < 4 → (erecP M)[q1.toNat + 1 + i]? = (erecP M)[cv.toNat + i]? := by
    intro i hi
    rw [show q1.toNat + 1 + i = q1.toNat + (i + 1) by omega, hP (i + 1) (by omega),
      erecP_getE (by omega), hg.2.2.2 _ (by omega)]
    have hlt : cv.toNat + i < (m.arr64 EREC).size := by simp only [erTop] at hEtop hcq; omega
    rcases i with _ | _ | _ | _ | i
    all_goals first
      | omega
      | (simp only [Nat.add_zero, Nat.zero_add] at hlt ⊢
         simp only [iirWs, List.getElem?_cons_succ, List.getElem?_cons_zero, rdW, c1, c2, c3,
          Array.getElem?_eq_getElem hlt, Option.getD_some])
  have hcv' : decCV (erecP M) (q1.toNat + 1) = some cvv := by
    rw [decCV_shift (by simpa using hw 0 (by decide)) (by simpa using hw 1 (by decide))
      (by simpa [Nat.add_assoc] using hw 2 (by decide)) (by simpa [Nat.add_assoc] using hw 3 (by decide))]
    exact ArrExt.decCV (IWGrow.erecPExtR hg) hcvE
  -- the capability record's words
  have hc15 := hcp.1
  have hIsz : iwTop m ≤ (m.arr64 IW).size := hS.2.1
  have hcaps : decCaps (erecP M) dn (q1.toNat + 5) = some c := by
    refine hcp.2 (erecP M) (q1.toNat + 5) (fun i hi => ?_) (fun i hi => ?_)
    · rw [show q1.toNat + 5 + i = q1.toNat + (5 + i) by omega, hP (5 + i) (by omega)]
      have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
      have gen : ∀ w : Word, w.toNat = caps.toNat + i →
          (iirWs m cv caps)[5 + i]? = some (rdW (m.arr64 IW) w) →
          (iirWs m cv caps)[5 + i]? = (iwA m)[caps.toNat + i]? := fun w hw h => by
        rw [h, ← hw]; simp only [iwA, rdW]; rw [Array.getElem?_eq_getElem (by omega)]; simp
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
      all_goals first
        | omega
        | exact gen _ rfl rfl
        | exact gen _ (by rw [UInt64.toNat_add]; simp; omega) rfl
    · rw [erecP_getE (by omega)]; simp only [erA]; exact hg.2.2.2 i hi
  have n0 : nat? (erecP M) q1.toNat = some 3 := by
    have := hP 0 (by decide); simp only [Nat.add_zero] at this
    simp [nat?, this, iirWs]
  refine ⟨hS', hg, ?_, ?_⟩
  · simp only [decCI, Option.bind_eq_bind, n0, Option.bind_some, hcv', hcaps, Option.pure_def]
  · have hq1 : (q1 + 1).toNat = q1.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have := hget 1 (by decide)
    rw [rdW_of_get? hq1.symm this]
    have := (partsCVName (IWGrow.refl m) hcv cv.toNat_lt).1
    simpa [iirWs] using this

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
  exact iirK_eq hP.put5 hK

/-- **`cons_block_inds`' model refines `consBlockInds`**, from a refinement `hLZ` of the
`lv_zero_caps` call of each member's `block_caps_at` at every state of the loop's invariant `T`
(`T` holds after it). -/
theorem icbiW_simG {p : Prog} (hP : ConsIndsProg p) (dn : NIdx → Option ConLeche.Name)
    (p1 isRec : Word) (bs : BlockShape) (b : Bool) (hb : (isRec != 0) = b) {T : AState → Prop}
    (hLZ : ∀ (k : Nat) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv), StageR dn vis fe m a → T a →
      DecB (fun m => decBS m p1.toNat) m bs → ShapeSrc m p1 →
      Sim (callW p k "lv_zero_caps" [rdW (m.arr64 IW) (p1 + 6)] m) (readLevelM bs.resSort) a
        (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decZC dn m' r x) ∧ T a'))
    (n : Nat) :
    ∀ (m : Mem) (a : AState) (vis : Word) (fe : IFEnv) (o l i : Word) (cvs : List IConstantVal),
    StageR dn vis fe m a → T a → DecB (fun m => decBS m p1.toNat) m bs → ShapeSrc m p1 →
    PSlR decCVp cvs o l m → i.toNat + l.toNat < 2 ^ 64 →
    Sim (icbiW p n m p1 isRec o l vis i) (ConRon.Arena.consBlockInds bs b cvs i.toNat fe) a
      (fun r x m' a' => (StageR dn (r.headD 0) x m' a' ∧ IWGrow m m') ∧ T a') := by
  induction n with
  | zero => intro m a vis fe o l i cvs _ _ _ _ _ _; rw [icbiW_zero]; exact Sim.of_none
  | succ n ih =>
  intro m a vis fe o l i cvs hS hT0 hq hsrc hcvs hil
  by_cases hl : l = 0
  · rw [icbiW_nil p n m p1 isRec o l vis i hl]
    have : cvs = [] := by
      have h := hcvs.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact Sim.ret ⟨⟨hS, IWGrow.refl m⟩, hT0⟩
  obtain ⟨q, cv, rest, rfl, hw, hqb, hdcv, hrest⟩ := partsPSl_cons hcvs hl
  rw [icbiW_cons p n m p1 isRec o l vis i hl]
  simp only [ConRon.Arena.consBlockInds]
  refine Sim.bindK (K := icbiK1 p n p1 isRec o l vis i) (body := fun r1 m1 => icbiK2 p n p1 isRec o l vis i
      (callW p n "ind_info_rec" [rdW (m1.arr64 IW) o, r1.headD 0] m1)) (by simp [icbiK1])
      (fun r m₁ => icbiK1_some p n m₁ p1 isRec o l vis i r)
    (blockCapsAt_simG hP.toCapsProg n hq hsrc hb (fun k => hLZ k m a vis fe hS hT0 hq hsrc)) ?_
  rintro r1 caps m1 a1 ⟨⟨hS1, hg1, hca⟩, hT1⟩
  refine Sim.mstep (K := icbiK2 p n p1 isRec o l vis i) (by simp [icbiK2])
    (fun r m₁ => icbiK2_some p n m₁ p1 isRec o l vis i r) fun r2 m2 h2 => ?_
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hlpos : 0 < l.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  have hol : o.toNat < iwTop m := by have := hcvs.2; omega
  have hw1 : rdW (m1.arr64 IW) o = UInt64.ofNat q := by
    rw [← hw]; simp only [rdW]; rw [hg1.2.2.1 _ hol]
  rw [hw1] at h2
  obtain ⟨q2, rfl, hW2⟩ := installIirRun hP h2
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  obtain ⟨hS2, hg2, hci, hname⟩ := iirW_stage hW2 hS1 (by rw [hq']; exact hdcv.grow (OMono.decCVp _) hg1) hca
  refine Sim.mstep (K := icbiK3 p n p1 isRec o l i) (by simp [icbiK3])
    (fun r m₁ => icbiK3_some p n m₁ p1 isRec o l i r) fun r3 m3 h3 => ?_
  simp only [List.headD_cons] at h3
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (envPush_specW p hP.recP n _ vis q2 hname) h3
  obtain ⟨hS3, hg3⟩ := envPushW_ok hW3 hS2 hci
  have hg13 := (hg1.trans hg2).trans hg3
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hl1 : (l - 1).toNat = l.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  have hrec := ih s3.mem a1 (r3.headD 0) (fe.push (.indInfo cv caps)) (o + 1) (l - 1) (i + 1) rest hS3 hT1
    (hq.grow (decBS_mono _) hg13) (partsHsrc_grow hg13 hq9 hsrc)
    (hrest.grow (fun q => OMono.decCVp q) hg13) (by omega)
  rw [hi1] at hrec
  refine Sim.post (K := icbiK4) rfl (fun _ _ => rfl) hrec ?_
  rintro r x m' a' ⟨⟨hS', hg'⟩, hT'⟩
  exact ⟨⟨hS', hg13.trans hg'⟩, hT'⟩

end L.Ind

end

end
