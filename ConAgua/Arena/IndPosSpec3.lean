import ConAgua.Arena.IndPosSpec2
import ConAgua.Arena.MemoBank
import ConAgua.Arena.IndSim

/-! # `replaceFVars` and its maps (lane `indproofs2`, helper `pos`)

`fvMapAt`, `nestHoleImg`, `replaceFVarsGo`, `replaceFVars`: one mutual block in the twin (well-founded
on the map's rank); in L, eight functions, the memo banked (`rf_bank_enter`/`rf_bank_leave`,
`MemoBank.lean`). Word models by exec fuel (`rx*W`), the L specs by `vcgen`, then the relational
lemma by strong induction on the exec fuel. -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Small callees as word models -/

/-- `nest_ctx_hi_at(ctx, nf)`. -/
def hiW (m : Mem) (ctx nf : Word) : Word :=
  rdW (m.arr64 IW) (ctx + 4) + rdW (m.arr64 IW) (ctx + 1) + nf

theorem hiAt_specW (p : Prog) (hp : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt) (n : Nat) (s₀ : St)
    (ctx nf : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctx_hi_at" [ctx, nf]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = hiW s₀.mem ctx nf; ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtxHiAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;> finish [hiW, rdW_eq]

/-- `nest_key_map(dsOff, dsLen, hoOff, hoLen, i)`. -/
def kmW (m : Mem) (dO dL hO hL i : Word) : Word × Word :=
  if i < dL then (1, rdW (m.arr64 IW) (dO + i))
  else if i - dL < hL then (1, rdW (m.arr64 IW) (hO + (i - dL))) else (0, 0)

theorem keyMap_specW (p : Prog) (hp : p.lookup "nest_key_map" = some nestKeyMap) (n : Nat) (s₀ : St)
    (dO dL hO hL i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_key_map" [dO, dL, hO, hL, i]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = (kmW s₀.mem dO dL hO hL i).1 ∧
      r.tail.headD 0 = (kmW s₀.mem dO dL hO hL i).2; ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestKeyMap]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;> finish [kmW, rdW_eq]

/-- `fv_map_at`'s erase arm after `pin_word(53)`. -/
def erK3 : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (v, m2) => some (1, v, m2)
def erK2 (i : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (s, m1) => if 4294967296 ≤ s then none else erK3 (fvinternW m1 i s)
def erK1 (m : Mem) (i : Word) : Option Word → Option (Word × Word × Mem)
  | none => none
  | some z => erK2 i (sointernW m z)

/-- `nest_hole_img_root(ctx, i)`. -/
def rtK2 : Option (List Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (r, m2) => some (1, r.headD 0, m2)
def rtK1 (ctx : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (hd, m1) =>
    if 4294967296 ≤ hd then none
    else rtK2 (mknF m1 [hd, rdW (m1.arr64 IW) (ctx + 7), rdW (m1.arr64 IW) (ctx + 8)])
def rxRootW (m : Mem) (ctx i : Word) : Option (Word × Word × Mem) :=
  if rdW (m.arr64 IW) (ctx + 4) ≤ i ∧ i < hiW m ctx 0 then
    rtK1 ctx (ceinternW m (getDW m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1))
      (i - rdW (m.arr64 IW) (ctx + 4)) 0) (rdW (m.arr64 IW) (ctx + 10)))
  else some (0, 0, m)

section arms
variable (m m1 m2 : Mem) (ctx i s v hd : Word) (z : Word) (r : List Word)
theorem erK3_some : erK3 (some (v, m2)) = some (1, v, m2) := rfl
theorem erK2_big (h : 4294967296 ≤ s) : erK2 i (some (s, m1)) = none := by simp [erK2, h]
theorem erK2_ok (h : ¬ 4294967296 ≤ s) : erK2 i (some (s, m1)) = erK3 (fvinternW m1 i s) := by
  simp only [erK2]; rw [ite_eq_right h]
theorem erK1_some : erK1 m i (some z) = erK2 i (sointernW m z) := rfl
theorem rtK2_some : rtK2 (some (r, m2)) = some (1, r.headD 0, m2) := rfl
theorem rtK1_big (h : 4294967296 ≤ hd) : rtK1 ctx (some (hd, m1)) = none := by simp [rtK1, h]
theorem rtK1_ok (h : ¬ 4294967296 ≤ hd) : rtK1 ctx (some (hd, m1)) =
    rtK2 (mknF m1 [hd, rdW (m1.arr64 IW) (ctx + 7), rdW (m1.arr64 IW) (ctx + 8)]) := by
  simp only [rtK1]; rw [ite_eq_right h]
theorem rxRootW_in (h : rdW (m.arr64 IW) (ctx + 4) ≤ i ∧ i < hiW m ctx 0) : rxRootW m ctx i =
    rtK1 ctx (ceinternW m (getDW m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1))
      (i - rdW (m.arr64 IW) (ctx + 4)) 0) (rdW (m.arr64 IW) (ctx + 10))) := by
  simp only [rxRootW]; rw [ite_eq_left h]
theorem rxRootW_out (h : ¬ (rdW (m.arr64 IW) (ctx + 4) ≤ i ∧ i < hiW m ctx 0)) :
    rxRootW m ctx i = some (0, 0, m) := by simp only [rxRootW]; rw [ite_eq_right h]
end arms
attribute [ind_grind] erK3_some erK2_big erK2_ok erK1_some rtK2_some rtK1_big rtK1_ok rxRootW_in
  rxRootW_out

/-! ## The mutual block's word models -/

/-- The non-recursive continuations. -/
def frK5 : Option (List Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (r, m5) => some (1, r.headD 0, m5)
def frK4 (q l : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (hd, m4) => if 4294967296 ≤ hd then none else frK5 (mknF m4 [hd, q, l])
def pfrK3 (kp : Word) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (q, l, m3) => frK4 q l (ceinternW m3 (rdW (m3.arr64 IW) kp) (rdW (m3.arr64 IW) (kp + 1)))
def dsB (q l : Word) : Option Mem → Option (Word × Word × Mem)
  | none => none
  | some m2 => some (q, l, m2)
def rxK1 (s : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => if 4294967296 ≤ r then none else some (r, m1.set64 CTL 219 s)
def rxH (h : Word) : Option (Word × Word × Mem) → Option (Word × Mem)
  | none => none
  | some (ok, r, m1) => some ((if ok ≠ 0 then r else h), m1)
def rxG5 (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 => some (r, m2)
def rxG4 (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => rxG5 r (msetG rfSch m1 h (rdW (m1.arr64 CTL) 219 <<< 32) r)
def rxB2 (g a2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x2, m2) => rpMkW m2 g a2 x2 0 0 0
def rxL3 (a2 x2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (c2, m3) => rpMkW m3 7 a2 x2 c2 0 0
def rxP1 (x y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (a2, m1) => rpMkW m1 9 a2 0 0 y x

mutual
/-- `fv_map_at(f, i)`. -/
def rxMapW : Nat → Mem → Word → Word → Option (Word × Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, f, i =>
    if rdW (m.arr64 IW) f = 0 then
      rxImgW n m (rdW (m.arr64 IW) (f + 1)) (rdW (m.arr64 IW) (f + 2)) (rdW (m.arr64 IW) (f + 3))
        (rdW (m.arr64 IW) (f + 4)) i
    else if rdW (m.arr64 IW) f = 1 then
      some ((kmW m (rdW (m.arr64 IW) (f + 1)) (rdW (m.arr64 IW) (f + 2)) (rdW (m.arr64 IW) (f + 3))
        (rdW (m.arr64 IW) (f + 4)) i).1, (kmW m (rdW (m.arr64 IW) (f + 1)) (rdW (m.arr64 IW) (f + 2))
        (rdW (m.arr64 IW) (f + 3)) (rdW (m.arr64 IW) (f + 4)) i).2, m)
    else if rdW (m.arr64 IW) f = 2 then erK1 m i (pinWordV m 53)
    else if i < rdW (m.arr64 IW) (f + 2) then
      some (1, rdW (m.arr64 IW) (rdW (m.arr64 IW) (f + 1) + i), m)
    else some (0, 0, m)
/-- `nest_hole_img(ctx, progOff, progLen, n, i)`. -/
def rxImgW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, ctx, po, pl, nn, i =>
    if nn = 0 then rxRootW m ctx i
    else if i = hiW m ctx (nn - 1) then rxFrameW n m ctx po pl (nn - 1) i
    else rxImgW n m ctx po pl (nn - 1) i
/-- `nest_hole_img_frame(ctx, progOff, progLen, n1, i)`. -/
def rxFrameW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, ctx, po, pl, n1, _ =>
    if n1 < pl then pfrK1 n ctx po pl n1 (some (rdW (m.arr64 IW) (po + n1), m))
    else frK0 n ctx po pl n1 (posRecW m [0, 0, 0, 0])
def frK0 (n : Nat) (ctx po pl n1 : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (k, m1) => pfrK1 n ctx po pl n1 (posRecW m1 [k, 0])
def pfrK1 (n : Nat) (ctx po pl n1 : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (h, m1) => pfrK2 n (rdW (m1.arr64 IW) h) (posRecW m1 [0, ctx, po, pl, n1])
def pfrK2 (n : Nat) (kp : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (f, m2) => pfrK3 kp (rxDsW n m2 f (rdW (m2.arr64 IW) (kp + 2)) (rdW (m2.arr64 IW) (kp + 3)))
/-- `nest_hole_img_ds(f, dsOff, dsLen)`. -/
def rxDsW : Nat → Mem → Word → Word → Word → Option (Word × Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, f, o, l => dsA n f o l (allocW m l)
def dsA (n : Nat) (f o l : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (q, m1) => dsB q l (rxDsGoW n m1 f o l q 0)
/-- `nest_hole_img_ds_go(f, dsOff, dsLen, q, j)`. -/
def rxDsGoW : Nat → Mem → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, f, o, l, q, j =>
    if l ≤ j then some m else dgK n f o l q j (rxW n m f (rdW (m.arr64 IW) (o + j)))
def dgK (n : Nat) (f o l q j : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (r, m1) => rxDsGoW n (m1.set64 IW (q + j) r) f o l q (j + 1)
/-- `replace_fvars(f, e)`. -/
def rxW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, f, e =>
    if 4294967296 ≤ rdW (m.arr64 CTL) 218 + 1 then none
    else rxK1 (rdW (m.arr64 CTL) 219) (rxGoW n (benterG 218 m) f CWF e)
/-- `replace_fvars_go(f, fuel, h)`. -/
def rxGoW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, f, fu, h => if fu = 0 then none else rxG1 n m f fu h (eViewW m h)
def rxG1 (n : Nat) (m : Mem) (f fu h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 ∨ v.headD 0 = 3 then some (h, m)
  else if v.headD 0 = 1 then rxH h (rxMapW n m f (v.tail.headD 0))
  else rxG3 n m f fu h v (mfindG rfSch m h (rdW (m.arr64 CTL) 219 <<< 32))
def rxG3 (n : Nat) (m : Mem) (f fu h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 RFM) (fr.tail.headD 0 * 4 + 3), m)
  else rxG4 h (rxNodeW n m f (fu - 1) (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
/-- `replace_fvars_node(f, fuel1, g, x, y, z)`. -/
def rxNodeW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, f, f1, g, x, y, z =>
    if g = 4 ∨ g = 5 ∨ g = 6 then rxB1 n f f1 g x y (rxGoW n m f f1 x)
    else if g = 7 then rxL1 n f f1 x y z (rxGoW n m f f1 x)
    else rxP1 x y (rxGoW n m f f1 z)
def rxB1 (n : Nat) (f f1 g _x y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (a2, m1) => rxB2 g a2 (rxGoW n m1 f f1 y)
def rxL1 (n : Nat) (f f1 _x y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (a2, m1) => rxL2 n f f1 z a2 (rxGoW n m1 f f1 y)
def rxL2 (n : Nat) (f f1 z a2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x2, m2) => rxL3 a2 x2 (rxGoW n m2 f f1 z)
end

end L.Ind

namespace L.Ind

open L.Arena

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (f i ctx po pl nn n1 k h kp q l o j r s e fu f1 g x y z a2 x2 c2 v0 hd ok : Word)
  (v fr rr : List Word)
theorem rxMapW_img (ht : rdW (m.arr64 IW) f = 0) : rxMapW (n + 1) m f i =
    rxImgW n m (rdW (m.arr64 IW) (f + 1)) (rdW (m.arr64 IW) (f + 2)) (rdW (m.arr64 IW) (f + 3))
      (rdW (m.arr64 IW) (f + 4)) i := by simp [rxMapW, ht]
theorem rxMapW_km (ht : rdW (m.arr64 IW) f = 1) : rxMapW (n + 1) m f i =
    some ((kmW m (rdW (m.arr64 IW) (f + 1)) (rdW (m.arr64 IW) (f + 2)) (rdW (m.arr64 IW) (f + 3))
        (rdW (m.arr64 IW) (f + 4)) i).1, (kmW m (rdW (m.arr64 IW) (f + 1)) (rdW (m.arr64 IW) (f + 2))
        (rdW (m.arr64 IW) (f + 3)) (rdW (m.arr64 IW) (f + 4)) i).2, m) := by simp [rxMapW, ht]
theorem rxMapW_er (ht : rdW (m.arr64 IW) f = 2) : rxMapW (n + 1) m f i = erK1 m i (pinWordV m 53) := by
  simp [rxMapW, ht]
theorem rxMapW_cin (h0 : ¬ rdW (m.arr64 IW) f = 0) (h1 : ¬ rdW (m.arr64 IW) f = 1)
    (h2 : ¬ rdW (m.arr64 IW) f = 2) (hi : i < rdW (m.arr64 IW) (f + 2)) :
    rxMapW (n + 1) m f i = some (1, rdW (m.arr64 IW) (rdW (m.arr64 IW) (f + 1) + i), m) := by
  simp [rxMapW, h0, h1, h2, hi]
theorem rxMapW_cout (h0 : ¬ rdW (m.arr64 IW) f = 0) (h1 : ¬ rdW (m.arr64 IW) f = 1)
    (h2 : ¬ rdW (m.arr64 IW) f = 2) (hi : ¬ i < rdW (m.arr64 IW) (f + 2)) :
    rxMapW (n + 1) m f i = some (0, 0, m) := by
  simp [rxMapW, h0, h1, h2, hi]
theorem rxImgW_root (h0 : nn = 0) : rxImgW (n + 1) m ctx po pl nn i = rxRootW m ctx i := by
  simp [rxImgW, h0]
theorem rxImgW_frame (h0 : ¬ nn = 0) (hh : i = hiW m ctx (nn - 1)) :
    rxImgW (n + 1) m ctx po pl nn i = rxFrameW n m ctx po pl (nn - 1) i := by
  simp only [rxImgW]; rw [ite_eq_right h0, ite_eq_left hh]
theorem rxImgW_next (h0 : ¬ nn = 0) (hh : ¬ i = hiW m ctx (nn - 1)) :
    rxImgW (n + 1) m ctx po pl nn i = rxImgW n m ctx po pl (nn - 1) i := by
  simp only [rxImgW]; rw [ite_eq_right h0, ite_eq_right hh]
theorem rxFrameW_in (hn : n1 < pl) : rxFrameW (n + 1) m ctx po pl n1 i =
    pfrK1 n ctx po pl n1 (some (rdW (m.arr64 IW) (po + n1), m)) := by simp [rxFrameW, hn]
theorem rxFrameW_def (hn : ¬ n1 < pl) : rxFrameW (n + 1) m ctx po pl n1 i =
    frK0 n ctx po pl n1 (posRecW m [0, 0, 0, 0]) := by simp [rxFrameW, hn]
theorem frK0_some : frK0 n ctx po pl n1 (some (k, m1)) = pfrK1 n ctx po pl n1 (posRecW m1 [k, 0]) := by
  rw [frK0]
theorem pfrK1_some : pfrK1 n ctx po pl n1 (some (h, m1)) =
    pfrK2 n (rdW (m1.arr64 IW) h) (posRecW m1 [0, ctx, po, pl, n1]) := by rw [pfrK1]
theorem pfrK2_some : pfrK2 n kp (some (f, m2)) =
    pfrK3 kp (rxDsW n m2 f (rdW (m2.arr64 IW) (kp + 2)) (rdW (m2.arr64 IW) (kp + 3))) := by rw [pfrK2]
theorem pfrK3_some : pfrK3 kp (some (q, l, m3)) =
    frK4 q l (ceinternW m3 (rdW (m3.arr64 IW) kp) (rdW (m3.arr64 IW) (kp + 1))) := rfl
theorem frK4_big (hb : 4294967296 ≤ hd) : frK4 q l (some (hd, m4)) = none := by simp [frK4, hb]
theorem frK4_ok (hb : ¬ 4294967296 ≤ hd) : frK4 q l (some (hd, m4)) = frK5 (mknF m4 [hd, q, l]) := by
  simp only [frK4]; rw [ite_eq_right hb]
theorem frK5_some : frK5 (some (rr, m5)) = some (1, rr.headD 0, m5) := rfl
theorem rxDsW_succ : rxDsW (n + 1) m f o l = dsA n f o l (allocW m l) := by simp [rxDsW]
theorem dsA_some : dsA n f o l (some (q, m1)) = dsB q l (rxDsGoW n m1 f o l q 0) := by rw [dsA]
theorem dsB_some : dsB q l (some m2) = some (q, l, m2) := rfl
theorem rxDsGoW_done (hj : l ≤ j) : rxDsGoW (n + 1) m f o l q j = some m := by simp [rxDsGoW, hj]
theorem rxDsGoW_step (hj : ¬ l ≤ j) : rxDsGoW (n + 1) m f o l q j =
    dgK n f o l q j (rxW n m f (rdW (m.arr64 IW) (o + j))) := by simp [rxDsGoW, hj]
theorem dgK_some : dgK n f o l q j (some (r, m1)) = rxDsGoW n (m1.set64 IW (q + j) r) f o l q (j + 1) := by
  rw [dgK]
theorem rxW_big (hb : 4294967296 ≤ rdW (m.arr64 CTL) 218 + 1) : rxW (n + 1) m f e = none := by
  simp [rxW, hb]
theorem rxW_ok (hb : ¬ 4294967296 ≤ rdW (m.arr64 CTL) 218 + 1) :
    rxW (n + 1) m f e = rxK1 (rdW (m.arr64 CTL) 219) (rxGoW n (benterG 218 m) f CWF e) := by
  simp only [rxW]; rw [ite_eq_right hb]
theorem rxK1_big (hb : 4294967296 ≤ r) : rxK1 s (some (r, m1)) = none := by simp [rxK1, hb]
theorem rxK1_ok (hb : ¬ 4294967296 ≤ r) : rxK1 s (some (r, m1)) = some (r, m1.set64 CTL 219 s) := by
  simp only [rxK1]; rw [ite_eq_right hb]
theorem rxGoW_abort (hf : fu = 0) : rxGoW (n + 1) m f fu h = none := by simp [rxGoW, hf]
theorem rxGoW_view (hf : fu ≠ 0) : rxGoW (n + 1) m f fu h = rxG1 n m f fu h (eViewW m h) := by
  simp [rxGoW, hf]
theorem rxG1_abort (hv : v = []) : rxG1 n m f fu h v = none := by simp [rxG1, hv]
theorem rxG1_leaf (hv : v ≠ []) (hg : v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 ∨ v.headD 0 = 3) :
    rxG1 n m f fu h v = some (h, m) := by simp only [rxG1]; rw [ite_eq_right hv, ite_eq_left hg]
theorem rxG1_fvar (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 ∨ v.headD 0 = 3))
    (h1 : v.headD 0 = 1) : rxG1 n m f fu h v = rxH h (rxMapW n m f (v.tail.headD 0)) := by
  simp only [rxG1]; rw [ite_eq_right hv, ite_eq_right hg, ite_eq_left h1]
theorem rxG1_node (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 ∨ v.headD 0 = 3))
    (h1 : ¬ v.headD 0 = 1) :
    rxG1 n m f fu h v = rxG3 n m f fu h v (mfindG rfSch m h (rdW (m.arr64 CTL) 219 <<< 32)) := by
  simp only [rxG1]; rw [ite_eq_right hv, ite_eq_right hg, ite_eq_right h1]
theorem rxH_some : rxH h (some (ok, r, m1)) = some ((if ok ≠ 0 then r else h), m1) := rfl
theorem rxG3_abort (hr : fr = []) : rxG3 n m f fu h v fr = none := by simp [rxG3, hr]
theorem rxG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    rxG3 n m f fu h v fr = some (rdW (m.arr64 RFM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [rxG3]; rw [ite_eq_right hr, ite_eq_left hh]
theorem rxG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    rxG3 n m f fu h v fr = rxG4 h (rxNodeW n m f (fu - 1) (v.headD 0) (v.tail.headD 0)
      (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [rxG3]; rw [ite_eq_right hr, ite_eq_right hh]
theorem rxG4_some : rxG4 h (some (r, m1)) = rxG5 r (msetG rfSch m1 h (rdW (m1.arr64 CTL) 219 <<< 32) r) := rfl
theorem rxG5_some : rxG5 r (some m2) = some (r, m2) := rfl
theorem rxNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) : rxNodeW (n + 1) m f f1 g x y z =
    rxB1 n f f1 g x y (rxGoW n m f f1 x) := by simp only [rxNodeW]; rw [ite_eq_left hg]
theorem rxNodeW_let (hg : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (h7 : g = 7) : rxNodeW (n + 1) m f f1 g x y z =
    rxL1 n f f1 x y z (rxGoW n m f f1 x) := by simp only [rxNodeW]; rw [ite_eq_right hg, ite_eq_left h7]
theorem rxNodeW_proj (hg : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (h7 : ¬ g = 7) : rxNodeW (n + 1) m f f1 g x y z =
    rxP1 x y (rxGoW n m f f1 z) := by simp only [rxNodeW]; rw [ite_eq_right hg, ite_eq_right h7]
theorem rxB1_some : rxB1 n f f1 g x y (some (a2, m1)) = rxB2 g a2 (rxGoW n m1 f f1 y) := by rw [rxB1]
theorem rxB2_some : rxB2 g a2 (some (x2, m2)) = rpMkW m2 g a2 x2 0 0 0 := rfl
theorem rxL1_some : rxL1 n f f1 x y z (some (a2, m1)) = rxL2 n f f1 z a2 (rxGoW n m1 f f1 y) := by rw [rxL1]
theorem rxL2_some : rxL2 n f f1 z a2 (some (x2, m2)) = rxL3 a2 x2 (rxGoW n m2 f f1 z) := by rw [rxL2]
theorem rxL3_some : rxL3 a2 x2 (some (c2, m3)) = rpMkW m3 7 a2 x2 c2 0 0 := rfl
theorem rxP1_some : rxP1 x y (some (a2, m1)) = rpMkW m1 9 a2 0 0 y x := rfl
end arms
attribute [ind_grind] rxMapW_img rxMapW_km rxMapW_er rxMapW_cin rxMapW_cout rxImgW_root rxImgW_frame
  rxImgW_next rxFrameW_in rxFrameW_def frK0_some pfrK1_some pfrK2_some pfrK3_some frK4_big frK4_ok frK5_some
  rxDsW_succ dsA_some dsB_some rxDsGoW_done rxDsGoW_step dgK_some rxW_big rxW_ok rxK1_big rxK1_ok
  rxGoW_abort rxGoW_view rxG1_abort rxG1_leaf rxG1_fvar rxG1_node rxH_some rxG3_abort rxG3_hit rxG3_miss
  rxG4_some rxG5_some rxNodeW_bin rxNodeW_let rxNodeW_proj rxB1_some rxB2_some rxL1_some rxL2_some
  rxL3_some rxP1_some

end L.Ind

namespace L.Ind

open L.Arena

/-- The lookups of the `replaceFVars` block. -/
structure RxLook (p : Prog) : Prop where
  ad : AdF p
  hl : AhLook p
  hk : MkLook p
  cf : p.lookup "const_find" = some constFind
  cp : p.lookup "const_push" = some constPush
  ci : p.lookup "intern_const" = some internConst
  ha : p.lookup "iw_alloc" = some iwAlloc
  h2 : p.lookup "rec2" = some rec2
  h4 : p.lookup "rec4" = some rec4
  h5 : p.lookup "rec5" = some rec5
  gd : p.lookup "sl_getd" = some slGetD
  hi : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt
  km : p.lookup "nest_key_map" = some nestKeyMap
  rff : p.lookup "rf_find" = some (memoFindG rfSch)
  rfp : p.lookup "rf_put" = some (memoPutG rfSch)
  rfe : p.lookup "rf_bank_enter" = some (bankEnterG 218)
  rfl' : p.lookup "rf_bank_leave" = some (bankLeaveG 218)
  fma : p.lookup "fv_map_at" = some fvMapAt
  rt : p.lookup "nest_hole_img_root" = some nestHoleImgRoot
  dsg : p.lookup "nest_hole_img_ds_go" = some nestHoleImgDsGo
  ds : p.lookup "nest_hole_img_ds" = some nestHoleImgDs
  fr : p.lookup "nest_hole_img_frame" = some nestHoleImgFrame
  img : p.lookup "nest_hole_img" = some nestHoleImg
  nd : p.lookup "replace_fvars_node" = some replaceFVarsNode
  go : p.lookup "replace_fvars_go" = some replaceFVarsGo
  rf : p.lookup "replace_fvars" = some replaceFVars

section spec
variable (p : Prog) (L : RxLook p)

include L in
theorem rxRoot_spec (n : Nat) (s₀ : St) (ctx i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_hole_img_root" [ctx, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxRootW s₀.mem ctx i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ L.rt, callFn, nestHoleImgRoot]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        hiAt_specW p L.hi n, slGetD_specW p L.gd n, internConst_spec p L.cf L.cp L.ci n,
        mknF_spec p L.ad n] <;>
      finish (gen := 20) [rdW_eq]

/-- The specs of the block at exec fuel `n`. -/
def RxSpec (n : Nat) : Prop :=
  (∀ (s₀ : St) (f i : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "fv_map_at" [f, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxMapW n s₀.mem f i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (ctx po pl nn i : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_hole_img" [ctx, po, pl, nn, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxImgW n s₀.mem ctx po pl nn i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (ctx po pl n1 i : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_hole_img_frame" [ctx, po, pl, n1, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxFrameW n s₀.mem ctx po pl n1 i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f o l : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_hole_img_ds" [f, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ rxDsW n s₀.mem f o l = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f o l q j : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_hole_img_ds_go" [f, o, l, q, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ rxDsGoW n s₀.mem f o l q j = some s'.mem; ⊤⦄) ∧
  (∀ (s₀ : St) (f fu h : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "replace_fvars_go" [f, fu, h]
    ⦃fun r s' => LocEq s' s₀ ∧ rxGoW n s₀.mem f fu h = some (r.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f f1 g x y z : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "replace_fvars_node" [f, f1, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ rxNodeW n s₀.mem f f1 g x y z = some (r.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f e : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "replace_fvars" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ rxW n s₀.mem f e = some (r.headD 0, s'.mem); ⊤⦄)

include L in
theorem rxSpec_zero : RxSpec p 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros
  · rw [invoke_eq _ L.fma]; simp only [callFn, fvMapAt]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.img]; simp only [callFn, nestHoleImg]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.fr]; simp only [callFn, nestHoleImgFrame]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.ds]; simp only [callFn, nestHoleImgDs]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.dsg]; simp only [callFn, nestHoleImgDsGo]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.go]; simp only [callFn, replaceFVarsGo]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.nd]; simp only [callFn, replaceFVarsNode]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.rf]; simp only [callFn, replaceFVars]; vcgen [exec] <;> grind

end spec

section step
variable (p : Prog) (L : RxLook p) (n : Nat) (ih : RxSpec p n)
include L ih

theorem rxMap_step (s₀ : St) (f i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "fv_map_at" [f, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxMapW (n + 1) s₀.mem f i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, hImg, -, -, -, -, -, -⟩ := ih
  simp only [invoke_eq _ L.fma, callFn, fvMapAt]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, hImg,
      keyMap_specW p L.km n, pinWord_specV p L.hl.hpw n, internSort_spec p L.hl.hsf L.hl.hsp L.hl.his n,
      internFVar_spec p L.hl.hff L.hl.hfp L.hl.hif n] <;>
    finish (gen := 20) [rdW_eq]

theorem rxImg_step (s₀ : St) (ctx po pl nn i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_hole_img" [ctx, po, pl, nn, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxImgW (n + 1) s₀.mem ctx po pl nn i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, hImg, hFr, -, -, -, -, -⟩ := ih
  simp only [invoke_eq _ L.img, callFn, nestHoleImg]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, hImg, hFr,
      rxRoot_spec p L n, hiAt_specW p L.hi n] <;>
    finish (gen := 20) [rdW_eq]

theorem rxFrame_step (s₀ : St) (ctx po pl n1 i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_hole_img_frame" [ctx, po, pl, n1, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxFrameW (n + 1) s₀.mem ctx po pl n1 i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, -, -, hDs, -, -, -, -⟩ := ih
  simp only [invoke_eq _ L.fr, callFn, nestHoleImgFrame]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, hDs,
      posRec2_specW p L.ha L.h2 n, posRec4_specW p L.ha L.h4 n, posRec5_specW p L.ha L.h5 n,
      internConst_spec p L.cf L.cp L.ci n, mknF_spec p L.ad n] <;>
    finish (gen := 20) [rdW_eq]

theorem rxDs_step (s₀ : St) (f o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_hole_img_ds" [f, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ rxDsW (n + 1) s₀.mem f o l = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, -, -, -, hDg, -, -, -⟩ := ih
  simp only [invoke_eq _ L.ds, callFn, nestHoleImgDs]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hDg, iwAlloc_specW p L.ha n] <;>
    finish (gen := 20)

theorem rxDsGo_step (s₀ : St) (f o l q j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_hole_img_ds_go" [f, o, l, q, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ rxDsGoW (n + 1) s₀.mem f o l q j = some s'.mem; ⊤⦄ := by
  obtain ⟨-, -, -, -, hDg, -, -, hRf⟩ := ih
  simp only [invoke_eq _ L.dsg, callFn, nestHoleImgDsGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, hDg, hRf] <;>
    finish (gen := 20) [rdW_eq]

theorem rxGo_step (s₀ : St) (f fu h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "replace_fvars_go" [f, fu, h]
    ⦃fun r s' => LocEq s' s₀ ∧ rxGoW (n + 1) s₀.mem f fu h = some (r.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨hMap, -, -, -, -, -, hNd, -⟩ := ih
  simp only [invoke_eq _ L.go, callFn, replaceFVarsGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p L.hl.hv n, hMap, memoFindG_spec rfSch p _ L.rff n,
      memoPutG_spec rfSch p _ L.rfp n, hNd] <;> finish (gen := 20) [St.setLocs_mem', rdW_eq]

theorem rxNode_step (s₀ : St) (f f1 g x y z : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "replace_fvars_node" [f, f1, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ rxNodeW (n + 1) s₀.mem f f1 g x y z = some (r.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, -, -, -, -, hGo, -, -⟩ := ih
  have hk := L.hk
  simp only [invoke_eq _ L.nd, callFn, replaceFVarsNode]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hGo,
      mkApp_spec p hk.hd hk.appF hk.appP hk.appI hk.appM n,
      mkLam_spec p hk.hd hk.lamF hk.lamP hk.lamI hk.lamM n,
      mkForall_spec p hk.hd hk.forF hk.forP hk.forI hk.forM n,
      mkLet_spec p hk.hd hk.ltF hk.ltP hk.ltI hk.ltM n,
      mkProj_spec p hk.hd hk.prjF hk.prjP hk.prjI hk.prjM n] <;> finish (gen := 20) [St.setLocs_mem']

theorem rxRf_step (s₀ : St) (f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "replace_fvars" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ rxW (n + 1) s₀.mem f e = some (r.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, -, -, -, -, hGo, -, -⟩ := ih
  simp only [invoke_eq _ L.rf, callFn, replaceFVars]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hGo,
      bankEnterG_spec 218 p _ L.rfe n, bankLeaveG_spec 218 p _ L.rfl' n] <;> finish (gen := 20)

end step

theorem rxSpec_all (p : Prog) (L : RxLook p) (n : Nat) : RxSpec p n := by
  induction n with
  | zero => exact rxSpec_zero p L
  | succ n ih =>
    exact ⟨rxMap_step p L n ih, rxImg_step p L n ih, rxFrame_step p L n ih, rxDs_step p L n ih,
      rxDsGo_step p L n ih, rxGo_step p L n ih, rxNode_step p L n ih, rxRf_step p L n ih⟩

end L.Ind

/-! ## The relational side: the banked memo's invariant -/

namespace L.Ind

open L.Arena

theorem rfK_h2 : ∀ k1 k2, bmKey.ok k1 k2 → k2.toNat < 2 ^ 32 := fun _ _ h => by rw [h.2]; decide

/-- The banked memo's keys: a handle and the generation. -/
def rfK : MemoKey (EIdx × Word) := genKey bmKey rfK_h2

/-- The word values denote handles. -/
def rfV (_ : Mem) (w : Word) (v : EIdx) : Prop := v = decE w

theorem rfSch_wf : rfSch.WF := ⟨by decide, by decide⟩

/-- **The banked memo's invariant**: the whole map `M`, the last generation `G`, the current `g`. -/
def RfInv (m : Mem) (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word) : Prop :=
  MemoRV rfSch rfK rfV m M ∧ BankW 218 m G g ∧ Fresh M G

/-- A writer that leaves the memo's array and its stamp and bank words alone. -/
def RfFr (m m' : Mem) : Prop :=
  ∃ (A : List ArrId) (C : List Word), MemFrame A C m m' ∧ RFM ∉ A ∧ (208 : Word) ∉ C ∧
    (218 : Word) ∉ C ∧ (219 : Word) ∉ C

theorem RfFr.refl (m : Mem) : RfFr m m := ⟨[], [], MemFrame.refl _ _ _, by simp, by simp, by simp, by simp⟩

theorem RfFr.trans {m₁ m₂ m₃ : Mem} (h₁ : RfFr m₁ m₂) (h₂ : RfFr m₂ m₃) : RfFr m₁ m₃ := by
  obtain ⟨A₁, C₁, f₁, a₁, c₁, d₁, e₁⟩ := h₁
  obtain ⟨A₂, C₂, f₂, a₂, c₂, d₂, e₂⟩ := h₂
  exact ⟨A₁ ++ A₂, C₁ ++ C₂, (f₁.mono (fun b hb => List.mem_append_left _ hb) (fun x hx => List.mem_append_left _ hx)).trans
    (f₂.mono (fun b hb => List.mem_append_right _ hb) (fun x hx => List.mem_append_right _ hx)),
    by simp [a₁, a₂], by simp [c₁, c₂], by simp [d₁, d₂], by simp [e₁, e₂]⟩

theorem RfFr.of_low {m m' : Mem} (h : LowFr m m') : RfFr m m' := by
  obtain ⟨A, C, hf, hA, hC⟩ := h
  exact ⟨A, C, hf, fun hh => by have := hA _ hh; simp [RFM] at this,
    fun hh => by have := hC _ hh; simp at this, fun hh => by have := hC _ hh; simp at this,
    fun hh => by have := hC _ hh; simp at this⟩

theorem RfFr.of_iw {m m' : Mem} (h : MemFrame [IW] [200] m m') : RfFr m m' :=
  ⟨_, _, h, by simp [RFM, IW], by simp, by simp, by simp⟩

theorem RfFr.set_iw (m : Mem) (x v : Word) : RfFr m (m.set64 IW x v) := RfFr.of_iw (set64IW_frame m x v)

theorem RfFr.ofMknF {m m' : Mem} {args r : List Word} (h : mknF m args = some (r, m')) : RfFr m m' :=
  ⟨_, _, mknF_frame h, by simp [RFM, SPN, AREC, ASLOT, ADER], by simp, by simp, by simp⟩

theorem RfInv.frame {m m' : Mem} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (h : RfInv m M G g)
    (hf : RfFr m m') : RfInv m' M G g := by
  obtain ⟨A, C, hfr, hA, hC, h218, h219⟩ := hf
  obtain ⟨hR, ⟨hB1, hB2, hgG, hGl, hsz⟩, hF⟩ := h
  refine ⟨memoRV_frame rfSch rfSch_wf rfK rfV A C hA hC m m' hfr (fun _ _ h => h) M hR,
    ⟨by rw [hfr.2.1 218 h218]; exact hB1, by rw [show (218 : Word) + 1 = 219 from rfl, hfr.2.1 219 h219]; exact hB2,
      hgG, hGl, by rw [hfr.2.2.1]; exact hsz⟩, hF⟩

theorem ceinternW_low {m m' : Mem} {f x r : Word} (h : ceinternW m f x = some (r, m')) : LowFr m m' := by
  exact ⟨_, _, (ceinternW_frame (hI := h)), by simp [CREC, CSLOT, CLP], by simp⟩

theorem posRecW_fr {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m')) : RfFr m m' := by
  simp only [posRecW] at h
  rcases hal : allocW m (UInt64.ofNat ws.length) with _ | ⟨q1, m1⟩ <;> rw [hal] at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  simp only [allocW] at hal
  split at hal; · simp at hal
  split at hal; · simp at hal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hal)
  exact RfFr.of_iw ((allocMem_frame m _).trans (wrIW_frame _ _ _))

theorem allocW_fr {m m' : Mem} {k q : Word} (h : allocW m k = some (q, m')) : RfFr m m' := by
  simp only [allocW] at h
  split at h; · simp at h
  split at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact RfFr.of_iw (allocMem_frame m k)

/-- The map at the generations up to `G` is unchanged. -/
def GKeep (M M' : Std.HashMap (EIdx × Word) EIdx) (G : Word) : Prop :=
  ∀ (k : EIdx) (gen : Word), gen ≤ G → M'[(k, gen)]? = M[(k, gen)]?

theorem GKeep.refl (M : Std.HashMap (EIdx × Word) EIdx) (G : Word) : GKeep M M G := fun _ _ _ => rfl

theorem GKeep.trans {M₁ M₂ M₃ : Std.HashMap (EIdx × Word) EIdx} {G G' : Word} (h₁ : GKeep M₁ M₂ G)
    (h₂ : GKeep M₂ M₃ G') (hG : G ≤ G') : GKeep M₁ M₃ G :=
  fun k gen hg => (h₂ k gen (UInt64.le_trans hg hG)).trans (h₁ k gen hg)

theorem GKeep.bank {M M' : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (h : GKeep M M' G) (hg : g ≤ G)
    {mp : Std.HashMap EIdx EIdx} (hb : Bank M g mp) : Bank M' g mp :=
  fun k => (hb k).trans (h k g hg).symm

/-- An optional handle as `(ok, e)`. -/
def OptE (r0 r1 : Word) : Option EIdx → Prop
  | none => r0 = 0
  | some e => r0 ≠ 0 ∧ decE r1 = e

end L.Ind

namespace L.Ind

open L.Arena

/-- **A `FvMap` record at `f`** (IndIface's layout `[tag, …]`), its reads below the top. -/
def FMOk (m : Mem) (f : Nat) : FvMap → Prop
  | .holeImg ctx prog n => iwN m f = some 0 ∧ f + 5 ≤ iwTop m ∧
      (∃ c, iwN m (f + 1) = some c ∧ decCtx m c = some ctx ∧ CtxIn m c (· < iwTop m)) ∧
      (∃ po pl, iwN m (f + 2) = some po ∧ iwN m (f + 3) = some pl ∧ HSl m po pl prog) ∧
      iwN m (f + 4) = some n ∧ ctx.nP + ctx.names.length + n < 2 ^ 64
  | .keyMap ds holes => iwN m f = some 1 ∧ f + 5 ≤ iwTop m ∧
      (∃ o l, iwN m (f + 1) = some o ∧ iwN m (f + 2) = some l ∧ decHL m o l = some ds ∧ o + l ≤ iwTop m) ∧
      (∃ o l, iwN m (f + 3) = some o ∧ iwN m (f + 4) = some l ∧ decHL m o l = some holes ∧ o + l ≤ iwTop m)
  | .erase => iwN m f = some 2 ∧ f + 1 ≤ iwTop m
  | .canon pfvs => iwN m f = some 3 ∧ f + 3 ≤ iwTop m ∧
      (∃ o l, iwN m (f + 1) = some o ∧ iwN m (f + 2) = some l ∧ decHL m o l = some pfvs ∧ o + l ≤ iwTop m)

theorem posIwN_grow {m m' : Mem} (hg : IWGrow m m') {i : Nat} (hi : i < iwTop m) : iwN m' i = iwN m i :=
  iwN_agree (RdS.of_grow hg) hi

theorem FMOk.grow {m m' : Mem} {f : Nat} {fm : FvMap} (h : FMOk m f fm) (hg : IWGrow m m') : FMOk m' f fm := by
  have ht := hg.1
  cases fm with
  | holeImg ctx prog n =>
    obtain ⟨h0, hb, ⟨c, hc, hdc, hci⟩, ⟨po, pl, hpo, hpl, hs⟩, hn, hlt⟩ := h
    obtain ⟨e, hci'⟩ := hci.grow hg
    exact ⟨by rw [posIwN_grow hg (by omega)]; exact h0, by omega,
      ⟨c, by rw [posIwN_grow hg (by omega)]; exact hc, by rw [e]; exact hdc, hci'⟩,
      ⟨po, pl, by rw [posIwN_grow hg (by omega)]; exact hpo, by rw [posIwN_grow hg (by omega)]; exact hpl, hs.grow hg⟩,
      by rw [posIwN_grow hg (by omega)]; exact hn, hlt⟩
  | keyMap ds holes =>
    obtain ⟨h0, hb, ⟨o, l, ho, hl, hd, hol⟩, ⟨o2, l2, ho2, hl2, hd2, hol2⟩⟩ := h
    exact ⟨by rw [posIwN_grow hg (by omega)]; exact h0, by omega,
      ⟨o, l, by rw [posIwN_grow hg (by omega)]; exact ho, by rw [posIwN_grow hg (by omega)]; exact hl,
        by rw [decHL_grow hg hol]; exact hd, by omega⟩,
      ⟨o2, l2, by rw [posIwN_grow hg (by omega)]; exact ho2, by rw [posIwN_grow hg (by omega)]; exact hl2,
        by rw [decHL_grow hg hol2]; exact hd2, by omega⟩⟩
  | erase =>
    obtain ⟨h0, hb⟩ := h
    exact ⟨by rw [posIwN_grow hg (by omega)]; exact h0, by omega⟩
  | canon pfvs =>
    obtain ⟨h0, hb, ⟨o, l, ho, hl, hd, hol⟩⟩ := h
    exact ⟨by rw [posIwN_grow hg (by omega)]; exact h0, by omega,
      ⟨o, l, by rw [posIwN_grow hg (by omega)]; exact ho, by rw [posIwN_grow hg (by omega)]; exact hl,
        by rw [decHL_grow hg hol]; exact hd, by omega⟩⟩

/-! ### The twin's node step, with its arms named -/

def rfArm (f : FvMap) (memo : Std.HashMap EIdx EIdx) (fuel : Nat) (h : EIdx) :
    ENodeView → AM (EIdx × Std.HashMap EIdx EIdx)
  | .app a x => do
    let (a2, m) ← ConRon.Arena.replaceFVarsGo f memo fuel a
    let (x2, m2) ← ConRon.Arena.replaceFVarsGo f m fuel x
    let r ← internAppE a2 x2
    pure (r, m2)
  | .lam t body => do
    let (t2, m) ← ConRon.Arena.replaceFVarsGo f memo fuel t
    let (b2, m2) ← ConRon.Arena.replaceFVarsGo f m fuel body
    let r ← internLamE t2 b2
    pure (r, m2)
  | .forallE t body => do
    let (t2, m) ← ConRon.Arena.replaceFVarsGo f memo fuel t
    let (b2, m2) ← ConRon.Arena.replaceFVarsGo f m fuel body
    let r ← internForallEE t2 b2
    pure (r, m2)
  | .letE t val body => do
    let (t2, m) ← ConRon.Arena.replaceFVarsGo f memo fuel t
    let (v2, m2) ← ConRon.Arena.replaceFVarsGo f m fuel val
    let (b2, m3) ← ConRon.Arena.replaceFVarsGo f m2 fuel body
    let r ← internLetEE t2 v2 b2
    pure (r, m3)
  | .proj s i x => do
    let (x2, m) ← ConRon.Arena.replaceFVarsGo f memo fuel x
    let r ← internProjE s i x2
    pure (r, m)
  | _ => pure (h, memo)

theorem replaceFVarsGo_succ' (f : FvMap) (memo : Std.HashMap EIdx EIdx) (fuel : Nat) (h : EIdx) :
    ConRon.Arena.replaceFVarsGo f memo (fuel + 1) h = (do
      let v ← view h
      match v with
      | .bvar _ => pure (h, memo)
      | .sort _ => pure (h, memo)
      | .lit _ => pure (h, memo)
      | .const _ _ => pure (h, memo)
      | .fvar i _ =>
        match ← ConRon.Arena.fvMapAt f i with
        | some r => pure (r, memo)
        | none => pure (h, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← rfArm f memo fuel h v
          pure (r, m.insert h r)) := by
  rw [ConRon.Arena.replaceFVarsGo.eq_2]
  congr 1
  funext v
  cases v with
  | app a' x' => simp only [rfArm, bind_assoc, pure_bind]; rfl
  | lam t body => simp only [rfArm, bind_assoc, pure_bind]; rfl
  | forallE t body => simp only [rfArm, bind_assoc, pure_bind]; rfl
  | letE t v' body => simp only [rfArm, bind_assoc, pure_bind]; rfl
  | proj s i x => simp only [rfArm, bind_assoc, pure_bind]; rfl
  | bvar _ => rfl
  | sort _ => rfl
  | lit _ => rfl
  | fvar _ _ => rfl
  | const _ _ => rfl

end L.Ind

namespace L.Ind

open L.Arena

/-! ### The statements, by exec fuel -/

section stmts
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- The common post: the stage relation, the pool grown, the memo's invariant at the same current
generation, the map unchanged up to the old last generation. -/
def RxPost (m m' : Mem) (a' : AState) (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word) : Prop :=
  ∃ M' G', StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RfInv m' M' G' g ∧ GKeep M M' G ∧ G ≤ G'

/-- A frame's hole, read back (`nestHoleImg`'s hit arm). -/
def frameTwin (c : NestCtx) (prog : List NestHole) (n1 : Nat) : AM (Option EIdx) := do
  let h := prog.getD n1 default
  let ds ← h.key.ds.mapM fun x => ConRon.Arena.replaceFVars (.holeImg c prog n1) x
  let hd ← internConstE h.key.cname h.key.lvls
  let r ← mkAppN hd ds
  pure (some r)

theorem nestHoleImg_succ (c : NestCtx) (prog : List NestHole) (n1 i : Nat) :
    ConRon.Arena.nestHoleImg c prog (n1 + 1) i =
      if (i == c.hiAt n1) = true then frameTwin c prog n1 else ConRon.Arena.nestHoleImg c prog n1 i := by
  rw [ConRon.Arena.nestHoleImg.eq_2]; rfl

def MapOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (f i : Word) (fm : FvMap) (r0 r1 : Word) (M : Std.HashMap (EIdx × Word) EIdx)
    (G g : Word), rxMapW n m f i = some (r0, r1, m') → StageR dn vis fe m a → FMOk m f.toNat fm →
    RfInv m M G g →
    ∃ x a', (ConRon.Arena.fvMapAt fm i.toNat).run a = .ok (x, a') ∧ OptE r0 r1 x ∧
      RxPost dn fe vis m m' a' M G g

def ImgOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx po pl nn i : Word) (c : NestCtx) (prog : List NestHole) (r0 r1 : Word)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word), rxImgW n m ctx po pl nn i = some (r0, r1, m') →
    StageR dn vis fe m a → decCtx m ctx.toNat = some c → CtxIn m ctx.toNat (· < iwTop m) →
    HSl m po.toNat pl.toNat prog → c.nP + c.names.length + nn.toNat < 2 ^ 64 → RfInv m M G g →
    ∃ x a', (ConRon.Arena.nestHoleImg c prog nn.toNat i.toNat).run a = .ok (x, a') ∧ OptE r0 r1 x ∧
      RxPost dn fe vis m m' a' M G g

def FrOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (ctx po pl n1 i : Word) (c : NestCtx) (prog : List NestHole) (r0 r1 : Word)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word), rxFrameW n m ctx po pl n1 i = some (r0, r1, m') →
    StageR dn vis fe m a → decCtx m ctx.toNat = some c → CtxIn m ctx.toNat (· < iwTop m) →
    HSl m po.toNat pl.toNat prog → c.nP + c.names.length + n1.toNat + 1 < 2 ^ 64 → RfInv m M G g →
    ∃ x a', (frameTwin c prog n1.toNat).run a = .ok (x, a') ∧ OptE r0 r1 x ∧ RxPost dn fe vis m m' a' M G g

def DsOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (f o l q l' : Word) (fm : FvMap) (xs : List EIdx)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word), rxDsW n m f o l = some (q, l', m') →
    StageR dn vis fe m a → FMOk m f.toNat fm → decHL m o.toNat l.toNat = some xs →
    (∀ j < l.toNat, o.toNat + j < iwTop m) → RfInv m M G g →
    ∃ ys a', (xs.mapM fun x => ConRon.Arena.replaceFVars fm x).run a = .ok (ys, a') ∧
      decHL m' q.toNat l'.toNat = some ys ∧ q.toNat + l'.toNat ≤ iwTop m' ∧ RxPost dn fe vis m m' a' M G g

def DsGoOK (n : Nat) : Prop :=
  ∀ (m0 m m' : Mem) (a : AState) (f o l q j : Word) (fm : FvMap) (xs acc : List EIdx)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word), rxDsGoW n m f o l q j = some m' →
    StageR dn vis fe m a → IWGrow m0 m → iwTop m0 ≤ q.toNat → q.toNat + l.toNat ≤ iwTop m →
    FMOk m0 f.toNat fm → decHL m0 o.toNat l.toNat = some xs → (∀ j < l.toNat, o.toNat + j < iwTop m0) →
    j.toNat ≤ l.toNat → decHL m q.toNat j.toNat = some acc → RfInv m M G g →
    ∃ ys a', ((xs.drop j.toNat).mapM fun x => ConRon.Arena.replaceFVars fm x).run a = .ok (ys, a') ∧
      decHL m' q.toNat l.toNat = some (acc ++ ys) ∧ StageR dn vis fe m' a' ∧ IWGrow m0 m' ∧
      iwTop m ≤ iwTop m' ∧ ∃ M' G', RfInv m' M' G' g ∧ GKeep M M' G ∧ G ≤ G'

/-- The map unchanged up to `G` except at the current generation. -/
def GKeepX (M M' : Std.HashMap (EIdx × Word) EIdx) (G g : Word) : Prop :=
  ∀ (k : EIdx) (gen : Word), gen ≤ G → gen ≠ g → M'[(k, gen)]? = M[(k, gen)]?

def GoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (f fu h : Word) (fm : FvMap) (mp : Std.HashMap EIdx EIdx) (r : Word)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word), rxGoW n m f fu h = some (r, m') →
    StageR dn vis fe m a → FMOk m f.toNat fm → H h → RfInv m M G g → Bank M g mp →
    ∃ mp' a' M' G', (ConRon.Arena.replaceFVarsGo fm mp fu.toNat (decE h)).run a = .ok ((decE r, mp'), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RfInv m' M' G' g ∧ Bank M' g mp' ∧ GKeepX M M' G g ∧ G ≤ G'

def RfOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (f e : Word) (fm : FvMap) (r : Word) (M : Std.HashMap (EIdx × Word) EIdx)
    (G g : Word), rxW n m f e = some (r, m') → StageR dn vis fe m a → FMOk m f.toNat fm → H e →
    RfInv m M G g →
    ∃ a', (ConRon.Arena.replaceFVars fm (decE e)).run a = .ok (decE r, a') ∧ H r ∧
      RxPost dn fe vis m m' a' M G g

end stmts

end L.Ind

namespace L.Ind

open L.Arena

/-! ### Word reads and small facts -/

theorem rdIW0 {m : Mem} {f : Word} {v : Nat} (h : iwN m f.toNat = some v) : (rdW (m.arr64 IW) f).toNat = v := by
  simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  simp [rdW, hw]

theorem rdIW {m : Mem} {f : Word} {i v : Nat} (h : iwN m (f.toNat + i) = some v) (hb : f.toNat + i < 2 ^ 64)
    (hi : i < 2 ^ 64) : (rdW (m.arr64 IW) (f + UInt64.ofNat i)).toNat = v :=
  rd_iwN (by rwa [UInt64.toNat_ofNat_of_lt' hi]) (by rwa [UInt64.toNat_ofNat_of_lt' hi])

/-- `nest_key_map` decodes `nestKeyMap`. -/
theorem kmW_ok {m : Mem} {dO dL hO hL i : Word} {ds holes : List EIdx}
    (hds : decHL m dO.toNat dL.toNat = some ds) (hho : decHL m hO.toNat hL.toNat = some holes)
    (h1 : dO.toNat + dL.toNat < 2 ^ 64) (h2 : hO.toNat + hL.toNat < 2 ^ 64) :
    OptE (kmW m dO dL hO hL i).1 (kmW m dO dL hO hL i).2 (ConRon.Arena.nestKeyMap ds holes i.toNat) := by
  have hdl : ds.length = dL.toNat := decHL_length m hds
  have hhl : holes.length = hL.toNat := decHL_length m hho
  unfold kmW ConRon.Arena.nestKeyMap
  by_cases hc1 : i < dL
  · have hc1' : i.toNat < dL.toNat := UInt64.lt_iff_toNat_lt.mp hc1
    obtain ⟨hH, hd⟩ := rd_iwH (p := dO) (i := i) (decHL_getI hds i.toNat hc1') (by omega)
    simp only [hc1, hc1', hdl, ite_true, List.getElem?_eq_getElem (show i.toNat < ds.length by omega)]
    exact ⟨by simp, hd⟩
  · have hc1' : ¬ i.toNat < dL.toNat := fun e => hc1 (UInt64.lt_iff_toNat_lt.mpr e)
    have hsub : (i - dL).toNat = i.toNat - dL.toNat :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
    simp only [hc1, hc1', hdl, ite_false]
    by_cases hc2 : i - dL < hL
    · have hc2' : i.toNat - dL.toNat < hL.toNat := by rw [← hsub]; exact UInt64.lt_iff_toNat_lt.mp hc2
      obtain ⟨hH, hd⟩ := rd_iwH (p := hO) (i := i - dL) (by rw [hsub]; exact decHL_getI hho _ hc2')
        (by rw [hsub]; omega)
      simp only [hc2, ite_true, List.getElem?_eq_getElem (show i.toNat - dL.toNat < holes.length by omega)]
      exact ⟨by simp, by rw [decE_eq, hd]⟩
    · have hc2' : ¬ i.toNat - dL.toNat < hL.toNat := fun e => hc2 (by
        rw [UInt64.lt_iff_toNat_lt, hsub]; exact e)
      simp only [hc2, ite_false, List.getElem?_eq_none (show holes.length ≤ i.toNat - dL.toNat by omega)]
      rfl

theorem RfInv.post {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m' : Mem} {a' : AState}
    {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (hR : RfInv m M G g) (hS : StageR dn vis fe m' a')
    (hg : IWGrow m m') (hf : RfFr m m') : RxPost dn fe vis m m' a' M G g :=
  ⟨M, G, hS, hg, hR.frame hf, GKeep.refl _ _, UInt64.le_refl _⟩

theorem RxPost.trans {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m1 m2 : Mem}
    {a1 a2 : AState} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word}
    (h₁ : RxPost dn fe vis m m1 a1 M G g)
    (h₂ : ∀ M1 G1, RfInv m1 M1 G1 g → G ≤ G1 → ∃ M2 G2, StageR dn vis fe m2 a2 ∧ IWGrow m1 m2 ∧
      RfInv m2 M2 G2 g ∧ GKeep M1 M2 G1 ∧ G1 ≤ G2) :
    RxPost dn fe vis m m2 a2 M G g := by
  obtain ⟨M1, G1, -, hg1, hR1, hk1, hG1⟩ := h₁
  obtain ⟨M2, G2, hS2, hg2, hR2, hk2, hG2⟩ := h₂ M1 G1 hR1 hG1
  exact ⟨M2, G2, hS2, hg1.trans hg2, hR2, hk1.trans hk2 hG1, UInt64.le_trans hG1 hG2⟩

section steps
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem mapOK_step (n : Nat) (hImg : ImgOK dn fe vis n) : MapOK dn fe vis (n + 1) := by
  intro m m' a f i fm r0 r1 M G g h hS hfm hR
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  cases fm with
  | holeImg ctx prog nn =>
    obtain ⟨h0, hb, ⟨c, hc, hdc, hci⟩, ⟨po, pl, hpo, hpl, hs⟩, hn, hlt⟩ := hfm
    have e0 : rdW (m.arr64 IW) f = 0 := UInt64.toNat_inj.mp (by rw [rdIW0 h0]; rfl)
    rw [rxMapW_img n m f i e0] at h
    have rc := rdIW (i := 1) (by simpa using hc) (by omega) (by decide)
    have rpo := rdIW (i := 2) (by simpa using hpo) (by omega) (by decide)
    have rpl := rdIW (i := 3) (by simpa using hpl) (by omega) (by decide)
    have rn := rdIW (i := 4) (by simpa using hn) (by omega) (by decide)
    simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
      show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at rc rpo rpl rn
    obtain ⟨x, a', hrun, hout, hpost⟩ := hImg m m' a _ _ _ _ i ctx prog r0 r1 M G g h hS
      (by rw [rc]; exact hdc) (by rw [rc]; exact hci) (by rw [rpo, rpl]; exact hs) (by rw [rn]; exact hlt) hR
    refine ⟨x, a', ?_, hout, hpost⟩
    rw [ConRon.Arena.fvMapAt.eq_1, ← rn]; exact hrun
  | keyMap ds holes =>
    obtain ⟨h0, hb, ⟨o, l, ho, hl, hd, hol⟩, ⟨o2, l2, ho2, hl2, hd2, hol2⟩⟩ := hfm
    have e1 : rdW (m.arr64 IW) f = 1 := UInt64.toNat_inj.mp (by rw [rdIW0 h0]; rfl)
    simp only [rxMapW_km n m f i e1, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have r1 := rdIW (i := 1) (by simpa using ho) (by omega) (by decide)
    have r2 := rdIW (i := 2) (by simpa using hl) (by omega) (by decide)
    have r3 := rdIW (i := 3) (by simpa using ho2) (by omega) (by decide)
    have r4 := rdIW (i := 4) (by simpa using hl2) (by omega) (by decide)
    simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
      show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at r1 r2 r3 r4
    refine ⟨_, a, ?_, kmW_ok (by rw [r1, r2]; exact hd) (by rw [r3, r4]; exact hd2) (by omega) (by omega),
      hR.post hS (IWGrow.refl _) (RfFr.refl _)⟩
    rw [ConRon.Arena.fvMapAt.eq_def]; rfl
  | erase =>
    obtain ⟨h0, hb⟩ := hfm
    have e2 : rdW (m.arr64 IW) f = 2 := UInt64.toNat_inj.mp (by rw [rdIW0 h0]; rfl)
    rw [rxMapW_er n m f i e2] at h
    rcases hpw : pinWordV m 53 with _ | z <;> rw [hpw] at h; · simp [erK1] at h
    rw [erK1_some] at h
    obtain ⟨hzl, hzH⟩ := pinZero_stage hS hpw
    rcases hso : sointernW m z with _ | ⟨s, m1⟩ <;> rw [hso] at h; · simp [erK2] at h
    by_cases hsb : 4294967296 ≤ s
    · rw [erK2_big (h := hsb)] at h; simp at h
    rw [erK2_ok (h := hsb)] at h
    obtain ⟨a1, hr1, hS1, hg1⟩ := internSort_stage hS z hzH hso
    rcases hfv : fvinternW m1 i s with _ | ⟨v, m2⟩ <;> rw [hfv] at h; · simp [erK3] at h
    simp only [erK3_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨a2, hr2, hS2, hg2⟩ := internFVar_stage hS1 i s (lt_of_notbig hsb) hfv
    refine ⟨some (decE v), a2, ?_, ⟨by simp, rfl⟩,
      hR.post hS2 (hg1.trans hg2) (RfFr.of_low ((sointernW_low hso).trans (fvinternW_low hfv)))⟩
    simp only [ConRon.Arena.fvMapAt.eq_def, StateT.run_bind, hzl, except_ok_bind, ConRon.Arena.internSortE, ConRon.Arena.internFVarE, hr1, hr2]
    rfl
  | canon pfvs =>
    obtain ⟨h0, hb, ⟨o, l, ho, hl, hd, hol⟩⟩ := hfm
    have hn0 : ¬ rdW (m.arr64 IW) f = 0 := fun e => by have := rdIW0 h0; rw [e] at this; simp at this
    have hn1 : ¬ rdW (m.arr64 IW) f = 1 := fun e => by have := rdIW0 h0; rw [e] at this; simp at this
    have hn2 : ¬ rdW (m.arr64 IW) f = 2 := fun e => by have := rdIW0 h0; rw [e] at this; simp at this
    have r1 := rdIW (i := 1) (by simpa using ho) (by omega) (by decide)
    have r2 := rdIW (i := 2) (by simpa using hl) (by omega) (by decide)
    simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl] at r1 r2
    have hpl := decHL_length m hd
    by_cases hi : i < rdW (m.arr64 IW) (f + 2)
    · rw [rxMapW_cin n m f i hn0 hn1 hn2 hi] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hi' : i.toNat < l := by rw [← r2]; exact UInt64.lt_iff_toNat_lt.mp hi
      obtain ⟨hH, hdd⟩ := rd_iwH (p := rdW (m.arr64 IW) (f + 1)) (i := i) (by rw [r1]; exact decHL_getI hd _ hi')
        (by rw [r1]; omega)
      refine ⟨pfvs[i.toNat]?, a, ?_, ?_, hR.post hS (IWGrow.refl _) (RfFr.refl _)⟩
      · rw [ConRon.Arena.fvMapAt.eq_def]; rfl
      · rw [List.getElem?_eq_getElem (by omega)]; exact ⟨by simp, hdd⟩
    · rw [rxMapW_cout n m f i hn0 hn1 hn2 hi] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hi' : ¬ i.toNat < l := fun e => hi (by rw [UInt64.lt_iff_toNat_lt, r2]; exact e)
      refine ⟨pfvs[i.toNat]?, a, ?_, ?_, hR.post hS (IWGrow.refl _) (RfFr.refl _)⟩
      · rw [ConRon.Arena.fvMapAt.eq_def]; rfl
      · rw [List.getElem?_eq_none (by omega)]; rfl

theorem rootOK (m m' : Mem) (a : AState) (ctx i : Word) (c : NestCtx) (prog : List NestHole) (r0 r1 : Word)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word) (h : rxRootW m ctx i = some (r0, r1, m'))
    (hS : StageR dn vis fe m a) (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m))
    (hb : c.nP + c.names.length < 2 ^ 64) (hR : RfInv m M G g) :
    ∃ x a', (ConRon.Arena.nestHoleImg c prog 0 i.toNat).run a = .ok (x, a') ∧ OptE r0 r1 x ∧
      RxPost dn fe vis m m' a' M G g := by
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hn, hn', hpa, hpa', hnP, hlvH, hlv, -, -, h11⟩ := ctx_fields hc hin htop
  have hlen := decHL_length m hn
  have hhi : (hiW m ctx 0).toNat = c.nP + c.names.length := by
    simp only [hiW]
    rw [word_add_toNat (by rw [word_add_toNat (by omega)]; simp; omega), word_add_toNat (by omega), hnP, hlen]
    simp
  rw [ConRon.Arena.nestHoleImg.eq_1]
  by_cases hin2 : rdW (m.arr64 IW) (ctx + 4) ≤ i ∧ i < hiW m ctx 0
  · have h1 : c.nP ≤ i.toNat := by rw [← hnP]; exact UInt64.le_iff_toNat_le.mp hin2.1
    have h2 : i.toNat < c.nP + c.names.length := by rw [← hhi]; exact UInt64.lt_iff_toNat_lt.mp hin2.2
    rw [ite_eq_left (by simp only [Bool.and_eq_true, decide_eq_true_eq, ConRon.Arena.NestCtx.hiAt, Nat.add_zero]; exact ⟨h1, decide_eq_true h2⟩)]
    rw [rxRootW_in m ctx i hin2] at h
    have hsub : (i - rdW (m.arr64 IW) (ctx + 4)).toNat = i.toNat - c.nP := by
      rw [UInt64.toNat_sub_of_le _ _ hin2.1, hnP]
    have hgd : getDW m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (i - rdW (m.arr64 IW) (ctx + 4)) 0 =
        rdW (m.arr64 IW) (rdW (m.arr64 IW) ctx + (i - rdW (m.arr64 IW) (ctx + 4))) := by
      simp only [getDW]; rw [ite_eq_right (fun e => by have := UInt64.le_iff_toNat_le.mp e; omega)]
    rw [hgd] at h
    obtain ⟨hnmH, hnmd⟩ := rd_iwH (p := rdW (m.arr64 IW) ctx) (i := i - rdW (m.arr64 IW) (ctx + 4))
      (by rw [hsub]; exact decHL_getI hn _ (by omega)) (by rw [hsub]; have := hn' (i.toNat - c.nP) (by omega); omega)
    generalize rdW (m.arr64 IW) (rdW (m.arr64 IW) ctx + (i - rdW (m.arr64 IW) (ctx + 4))) = nm at h hnmH hnmd
    rcases hci : ceinternW m nm (rdW (m.arr64 IW) (ctx + 10)) with _ | ⟨hd, m1⟩ <;> rw [hci] at h; · simp [rtK1] at h
    by_cases hdb : 4294967296 ≤ hd
    · rw [rtK1_big (h := hdb)] at h; simp at h
    rw [rtK1_ok (h := hdb)] at h
    obtain ⟨a1, hr1, hS1, hg1⟩ := internConst_stage hS nm _ hnmH hlvH hci
    have hiw : m1.arr64 IW = m.arr64 IW := lowFr_iw (ceinternW_low hci)
    rw [hiw] at h
    rcases hst : mknF m1 [hd, rdW (m.arr64 IW) (ctx + 7), rdW (m.arr64 IW) (ctx + 8)] with _ | ⟨rr, m2⟩ <;> rw [hst] at h; · simp [rtK2] at h
    simp only [rtK2_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨x, a2, hr2, hS2, hg2, hx1, hx2⟩ := mknF_ok dn vis fe hd _ _ (lt_of_notbig hdb) c.params m1 m2 a1 rr hst
      ⟨hS1, by simp only [decHL, iwA, hiw]; exact hpa⟩
    refine ⟨some x, a2, ?_, ⟨by simp, by rw [← hx2]; rfl⟩,
      hR.post hS2 (hg1.trans hg2) ((RfFr.of_low (ceinternW_low hci)).trans (RfFr.ofMknF hst))⟩
    have hnm' : c.names.getD (i.toNat - c.nP) default = decI nm := by
      rw [hnmd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    simp only [hnm', ConRon.Arena.internConstE, StateT.run_bind, ← hlv, hr1, except_ok_bind, show (decE hd : EIdx) = decI hd from rfl, hr2]
    rfl
  · rw [rxRootW_out m ctx i hin2] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have : ¬ (c.nP ≤ i.toNat ∧ i.toNat < c.nP + c.names.length) := fun ⟨e1, e2⟩ => hin2
      ⟨UInt64.le_iff_toNat_le.mpr (by rw [hnP]; exact e1), UInt64.lt_iff_toNat_lt.mpr (by rw [hhi]; exact e2)⟩
    rw [ite_eq_right (by simp only [Bool.and_eq_true, decide_eq_true_eq, ConRon.Arena.NestCtx.hiAt, Nat.add_zero]; exact fun ⟨e1, e2⟩ => this ⟨e1, of_decide_eq_true e2⟩)]
    exact ⟨none, a, rfl, rfl, hR.post hS (IWGrow.refl _) (RfFr.refl _)⟩

theorem imgOK_step (n : Nat) (hImg : ImgOK dn fe vis n) (hFr : FrOK dn fe vis n) : ImgOK dn fe vis (n + 1) := by
  intro m m' a ctx po pl nn i c prog r0 r1 M G g h hS hc hin hs hb hR
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hn, -, -, -, hnP, -, -, -, -, h11⟩ := ctx_fields hc hin htop
  have hlen := decHL_length m hn
  by_cases h0 : nn = 0
  · rw [rxImgW_root (h0 := h0)] at h
    subst h0
    exact rootOK dn fe vis m m' a ctx i c prog r0 r1 M G g h hS hc hin (by simpa using hb) hR
  have hnn : nn.toNat ≠ 0 := toNat_ne_zero' h0
  have hn1 : (nn - 1).toNat = nn.toNat - 1 := toNat_sub_one' h0
  have hhi : (hiW m ctx (nn - 1)).toNat = c.hiAt (nn.toNat - 1) := by
    simp only [hiW, ConRon.Arena.NestCtx.hiAt]
    rw [word_add_toNat (by rw [word_add_toNat (by omega)]; omega), word_add_toNat (by omega), hnP, hlen, hn1]
  obtain ⟨n1, hn1'⟩ : ∃ n1, nn.toNat = n1 + 1 := ⟨nn.toNat - 1, by omega⟩
  rw [hn1', nestHoleImg_succ]
  by_cases hh : i = hiW m ctx (nn - 1)
  · rw [rxImgW_frame (h0 := h0) (hh := hh)] at h
    have : (i.toNat == c.hiAt n1) = true := by
      rw [hh, hhi, hn1']; simp
    rw [ite_eq_left this]
    have := hFr m m' a ctx po pl (nn - 1) i c prog r0 r1 M G g h hS hc hin hs (by rw [hn1]; omega) hR
    rwa [hn1, hn1'] at this
  · rw [rxImgW_next (h0 := h0) (hh := hh)] at h
    have : ¬ (i.toNat == c.hiAt n1) = true := by
      intro e; apply hh; apply UInt64.toNat_inj.mp; rw [hhi, hn1', Nat.add_sub_cancel]; simp at e; exact e
    rw [ite_eq_right this]
    have := hImg m m' a ctx po pl (nn - 1) i c prog r0 r1 M G g h hS hc hin hs (by rw [hn1]; omega) hR
    rwa [hn1, hn1'] at this

end steps

end L.Ind
