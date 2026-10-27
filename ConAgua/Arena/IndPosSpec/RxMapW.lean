import ConAgua.Arena.IndPosSpec.CtxFields
import ConAgua.Arena.IndPosSpec.MkLook
import ConAgua.Arena.IndRealSpine
import ConAgua.Arena.IndPosSpec.MatesW
import ConAgua.Arena.IndGrindAttr

/-!
# RxMapW

`hiW`, `kmW`, `erK3`, `erK2`, `erK1`, `rtK2` and the lemmas only they use.
-/

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

/-- `nest_key_map(dsOff, dsLen, hoOff, hoLen, i)`. -/
def kmW (m : Mem) (dO dL hO hL i : Word) : Word × Word :=
  if i < dL then (1, rdW (m.arr64 IW) (dO + i))
  else if i - dL < hL then (1, rdW (m.arr64 IW) (hO + (i - dL))) else (0, 0)

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
theorem erK2_ok (h : ¬ 4294967296 ≤ s) : erK2 i (some (s, m1)) = erK3 (fvinternW m1 i s) := by
  simp only [erK2]; rw [ite_eq_right h]
theorem erK1_some : erK1 m i (some z) = erK2 i (sointernW m z) := rfl
theorem rtK2_some : rtK2 (some (r, m2)) = some (1, r.headD 0, m2) := rfl
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
attribute [ind_grind] erK3_some erK2_ok erK1_some rtK2_some rtK1_ok rxRootW_in rxRootW_out

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
theorem rxW_ok (hb : ¬ 4294967296 ≤ rdW (m.arr64 CTL) 218 + 1) :
    rxW (n + 1) m f e = rxK1 (rdW (m.arr64 CTL) 219) (rxGoW n (benterG 218 m) f CWF e) := by
  simp only [rxW]; rw [ite_eq_right hb]
theorem rxK1_ok (hb : ¬ 4294967296 ≤ r) : rxK1 s (some (r, m1)) = some (r, m1.set64 CTL 219 s) := by
  simp only [rxK1]; rw [ite_eq_right hb]
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
attribute [ind_grind] rxMapW_img rxMapW_km rxMapW_er rxMapW_cin rxMapW_cout rxImgW_root rxImgW_frame rxImgW_next rxFrameW_in rxFrameW_def frK0_some pfrK1_some pfrK2_some pfrK3_some frK4_ok frK5_some rxDsW_succ dsA_some dsB_some rxDsGoW_done rxDsGoW_step dgK_some rxW_ok rxK1_ok rxGoW_view rxG1_abort rxG1_leaf rxG1_fvar rxG1_node rxH_some rxG3_hit rxG3_miss rxG4_some rxG5_some rxNodeW_bin rxNodeW_let rxNodeW_proj rxB1_some rxB2_some rxL1_some rxL2_some rxL3_some rxP1_some

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

theorem RfInv.frame {m m' : Mem} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (h : RfInv m M G g)
    (hf : RfFr m m') : RfInv m' M G g := by
  obtain ⟨A, C, hfr, hA, hC, h218, h219⟩ := hf
  obtain ⟨hR, ⟨hB1, hB2, hgG, hGl, hsz⟩, hF⟩ := h
  refine ⟨memoRV_frame rfSch rfSch_wf rfK rfV A C hA hC m m' hfr (fun _ _ h => h) M hR,
    ⟨by rw [hfr.2.1 218 h218]; exact hB1, by rw [show (218 : Word) + 1 = 219 from rfl, hfr.2.1 219 h219]; exact hB2,
      hgG, hGl, by rw [hfr.2.2.1]; exact hsz⟩, hF⟩

theorem ceinternW_low {m m' : Mem} {f x r : Word} (h : ceinternW m f x = some (r, m')) : LowFr m m' := by
  exact ⟨_, _, (ceinternW_frame (hI := h)), by simp [tier1, tierOff, CREC, CSLOT, CLP], by simp⟩

/-- The map at the generations up to `G` is unchanged. -/
def GKeep (M M' : Std.HashMap (EIdx × Word) EIdx) (G : Word) : Prop :=
  ∀ (k : EIdx) (gen : Word), gen ≤ G → M'[(k, gen)]? = M[(k, gen)]?

theorem GKeep.trans {M₁ M₂ M₃ : Std.HashMap (EIdx × Word) EIdx} {G G' : Word} (h₁ : GKeep M₁ M₂ G)
    (h₂ : GKeep M₂ M₃ G') (hG : G ≤ G') : GKeep M₁ M₃ G :=
  fun k gen hg => (h₂ k gen (UInt64.le_trans hg hG)).trans (h₁ k gen hg)

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

theorem RxPost.trans {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m1 m2 : Mem}
    {a1 a2 : AState} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word}
    (h₁ : RxPost dn fe vis m m1 a1 M G g)
    (h₂ : ∀ M1 G1, RfInv m1 M1 G1 g → G ≤ G1 → ∃ M2 G2, StageR dn vis fe m2 a2 ∧ IWGrow m1 m2 ∧
      RfInv m2 M2 G2 g ∧ GKeep M1 M2 G1 ∧ G1 ≤ G2) :
    RxPost dn fe vis m m2 a2 M G g := by
  obtain ⟨M1, G1, -, hg1, hR1, hk1, hG1⟩ := h₁
  obtain ⟨M2, G2, hS2, hg2, hR2, hk2, hG2⟩ := h₂ M1 G1 hR1 hG1
  exact ⟨M2, G2, hS2, hg1.trans hg2, hR2, hk1.trans hk2 hG1, UInt64.le_trans hG1 hG2⟩

end L.Ind

end
