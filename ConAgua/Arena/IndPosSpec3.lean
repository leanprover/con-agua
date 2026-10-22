import ConAgua.Arena.IndPosSpec2
import ConAgua.Arena.MemoBank

/-! # `replaceFVars` and its maps (lane `indproofs2`, helper `pos`)

`fvMapAt`, `nestHoleImg`, `replaceFVarsGo`, `replaceFVars`: one mutual block in the twin (well-founded
on the map's rank); in L, eight functions, the memo banked (`rf_bank_enter`/`rf_bank_leave`,
`MemoBank.lean`). Word models by exec fuel (`rx*W`), the L specs by `vcgen`, then the relational
lemma by strong induction on the exec fuel. -/

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
  rw [invoke_eq _ hp]
  simp only [callFn, nestCtxHiAt]
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
  rw [invoke_eq _ hp]
  simp only [callFn, nestKeyMap]
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
    else rtK2 (stubM "mk_app_n" m1 [hd, rdW (m1.arr64 IW) (ctx + 7), rdW (m1.arr64 IW) (ctx + 8)])
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
  simp only [erK2]; rw [if_neg h]
theorem erK1_some : erK1 m i (some z) = erK2 i (sointernW m z) := rfl
theorem rtK2_some : rtK2 (some (r, m2)) = some (1, r.headD 0, m2) := rfl
theorem rtK1_big (h : 4294967296 ≤ hd) : rtK1 ctx (some (hd, m1)) = none := by simp [rtK1, h]
theorem rtK1_ok (h : ¬ 4294967296 ≤ hd) : rtK1 ctx (some (hd, m1)) =
    rtK2 (stubM "mk_app_n" m1 [hd, rdW (m1.arr64 IW) (ctx + 7), rdW (m1.arr64 IW) (ctx + 8)]) := by
  simp only [rtK1]; rw [if_neg h]
theorem rxRootW_in (h : rdW (m.arr64 IW) (ctx + 4) ≤ i ∧ i < hiW m ctx 0) : rxRootW m ctx i =
    rtK1 ctx (ceinternW m (getDW m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1))
      (i - rdW (m.arr64 IW) (ctx + 4)) 0) (rdW (m.arr64 IW) (ctx + 10))) := by
  simp only [rxRootW]; rw [if_pos h]
theorem rxRootW_out (h : ¬ (rdW (m.arr64 IW) (ctx + 4) ≤ i ∧ i < hiW m ctx 0)) :
    rxRootW m ctx i = some (0, 0, m) := by simp only [rxRootW]; rw [if_neg h]
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
  | some (hd, m4) => if 4294967296 ≤ hd then none else frK5 (stubM "mk_app_n" m4 [hd, q, l])
def frK3 (kp : Word) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
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
    if n1 < pl then frK1 n ctx po pl n1 (some (rdW (m.arr64 IW) (po + n1), m))
    else frK0 n ctx po pl n1 (posRecW m [0, 0, 0, 0])
def frK0 (n : Nat) (ctx po pl n1 : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (k, m1) => frK1 n ctx po pl n1 (posRecW m1 [k, 0])
def frK1 (n : Nat) (ctx po pl n1 : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (h, m1) => frK2 n (rdW (m1.arr64 IW) h) (posRecW m1 [0, ctx, po, pl, n1])
def frK2 (n : Nat) (kp : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (f, m2) => frK3 kp (rxDsW n m2 f (rdW (m2.arr64 IW) (kp + 2)) (rdW (m2.arr64 IW) (kp + 3)))
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
def rxB1 (n : Nat) (f f1 g x y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (a2, m1) => rxB2 g a2 (rxGoW n m1 f f1 y)
def rxL1 (n : Nat) (f f1 x y z : Word) : Option (Word × Mem) → Option (Word × Mem)
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
  simp only [rxImgW]; rw [if_neg h0, if_pos hh]
theorem rxImgW_next (h0 : ¬ nn = 0) (hh : ¬ i = hiW m ctx (nn - 1)) :
    rxImgW (n + 1) m ctx po pl nn i = rxImgW n m ctx po pl (nn - 1) i := by
  simp only [rxImgW]; rw [if_neg h0, if_neg hh]
theorem rxFrameW_in (hn : n1 < pl) : rxFrameW (n + 1) m ctx po pl n1 i =
    frK1 n ctx po pl n1 (some (rdW (m.arr64 IW) (po + n1), m)) := by simp [rxFrameW, hn]
theorem rxFrameW_def (hn : ¬ n1 < pl) : rxFrameW (n + 1) m ctx po pl n1 i =
    frK0 n ctx po pl n1 (posRecW m [0, 0, 0, 0]) := by simp [rxFrameW, hn]
theorem frK0_some : frK0 n ctx po pl n1 (some (k, m1)) = frK1 n ctx po pl n1 (posRecW m1 [k, 0]) := by
  rw [frK0]
theorem frK1_some : frK1 n ctx po pl n1 (some (h, m1)) =
    frK2 n (rdW (m1.arr64 IW) h) (posRecW m1 [0, ctx, po, pl, n1]) := by rw [frK1]
theorem frK2_some : frK2 n kp (some (f, m2)) =
    frK3 kp (rxDsW n m2 f (rdW (m2.arr64 IW) (kp + 2)) (rdW (m2.arr64 IW) (kp + 3))) := by rw [frK2]
theorem frK3_some : frK3 kp (some (q, l, m3)) =
    frK4 q l (ceinternW m3 (rdW (m3.arr64 IW) kp) (rdW (m3.arr64 IW) (kp + 1))) := rfl
theorem frK4_big (hb : 4294967296 ≤ hd) : frK4 q l (some (hd, m4)) = none := by simp [frK4, hb]
theorem frK4_ok (hb : ¬ 4294967296 ≤ hd) : frK4 q l (some (hd, m4)) = frK5 (stubM "mk_app_n" m4 [hd, q, l]) := by
  simp only [frK4]; rw [if_neg hb]
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
  simp only [rxW]; rw [if_neg hb]
theorem rxK1_big (hb : 4294967296 ≤ r) : rxK1 s (some (r, m1)) = none := by simp [rxK1, hb]
theorem rxK1_ok (hb : ¬ 4294967296 ≤ r) : rxK1 s (some (r, m1)) = some (r, m1.set64 CTL 219 s) := by
  simp only [rxK1]; rw [if_neg hb]
theorem rxGoW_abort (hf : fu = 0) : rxGoW (n + 1) m f fu h = none := by simp [rxGoW, hf]
theorem rxGoW_view (hf : fu ≠ 0) : rxGoW (n + 1) m f fu h = rxG1 n m f fu h (eViewW m h) := by
  simp [rxGoW, hf]
theorem rxG1_abort (hv : v = []) : rxG1 n m f fu h v = none := by simp [rxG1, hv]
theorem rxG1_leaf (hv : v ≠ []) (hg : v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 ∨ v.headD 0 = 3) :
    rxG1 n m f fu h v = some (h, m) := by simp only [rxG1]; rw [if_neg hv, if_pos hg]
theorem rxG1_fvar (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 ∨ v.headD 0 = 3))
    (h1 : v.headD 0 = 1) : rxG1 n m f fu h v = rxH h (rxMapW n m f (v.tail.headD 0)) := by
  simp only [rxG1]; rw [if_neg hv, if_neg hg, if_pos h1]
theorem rxG1_node (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 ∨ v.headD 0 = 3))
    (h1 : ¬ v.headD 0 = 1) :
    rxG1 n m f fu h v = rxG3 n m f fu h v (mfindG rfSch m h (rdW (m.arr64 CTL) 219 <<< 32)) := by
  simp only [rxG1]; rw [if_neg hv, if_neg hg, if_neg h1]
theorem rxH_some : rxH h (some (ok, r, m1)) = some ((if ok ≠ 0 then r else h), m1) := rfl
theorem rxG3_abort (hr : fr = []) : rxG3 n m f fu h v fr = none := by simp [rxG3, hr]
theorem rxG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    rxG3 n m f fu h v fr = some (rdW (m.arr64 RFM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [rxG3]; rw [if_neg hr, if_pos hh]
theorem rxG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    rxG3 n m f fu h v fr = rxG4 h (rxNodeW n m f (fu - 1) (v.headD 0) (v.tail.headD 0)
      (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [rxG3]; rw [if_neg hr, if_neg hh]
theorem rxG4_some : rxG4 h (some (r, m1)) = rxG5 r (msetG rfSch m1 h (rdW (m1.arr64 CTL) 219 <<< 32) r) := rfl
theorem rxG5_some : rxG5 r (some m2) = some (r, m2) := rfl
theorem rxNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) : rxNodeW (n + 1) m f f1 g x y z =
    rxB1 n f f1 g x y (rxGoW n m f f1 x) := by simp only [rxNodeW]; rw [if_pos hg]
theorem rxNodeW_let (hg : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (h7 : g = 7) : rxNodeW (n + 1) m f f1 g x y z =
    rxL1 n f f1 x y z (rxGoW n m f f1 x) := by simp only [rxNodeW]; rw [if_neg hg, if_pos h7]
theorem rxNodeW_proj (hg : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (h7 : ¬ g = 7) : rxNodeW (n + 1) m f f1 g x y z =
    rxP1 x y (rxGoW n m f f1 z) := by simp only [rxNodeW]; rw [if_neg hg, if_neg h7]
theorem rxB1_some : rxB1 n f f1 g x y (some (a2, m1)) = rxB2 g a2 (rxGoW n m1 f f1 y) := by rw [rxB1]
theorem rxB2_some : rxB2 g a2 (some (x2, m2)) = rpMkW m2 g a2 x2 0 0 0 := rfl
theorem rxL1_some : rxL1 n f f1 x y z (some (a2, m1)) = rxL2 n f f1 z a2 (rxGoW n m1 f f1 y) := by rw [rxL1]
theorem rxL2_some : rxL2 n f f1 z a2 (some (x2, m2)) = rxL3 a2 x2 (rxGoW n m2 f f1 z) := by rw [rxL2]
theorem rxL3_some : rxL3 a2 x2 (some (c2, m3)) = rpMkW m3 7 a2 x2 c2 0 0 := rfl
theorem rxP1_some : rxP1 x y (some (a2, m1)) = rpMkW m1 9 a2 0 0 y x := rfl
end arms
attribute [ind_grind] rxMapW_img rxMapW_km rxMapW_er rxMapW_cin rxMapW_cout rxImgW_root rxImgW_frame
  rxImgW_next rxFrameW_in rxFrameW_def frK0_some frK1_some frK2_some frK3_some frK4_big frK4_ok frK5_some
  rxDsW_succ dsA_some dsB_some rxDsGoW_done rxDsGoW_step dgK_some rxW_big rxW_ok rxK1_big rxK1_ok
  rxGoW_abort rxGoW_view rxG1_abort rxG1_leaf rxG1_fvar rxG1_node rxH_some rxG3_abort rxG3_hit rxG3_miss
  rxG4_some rxG5_some rxNodeW_bin rxNodeW_let rxNodeW_proj rxB1_some rxB2_some rxL1_some rxL2_some
  rxL3_some rxP1_some

end L.Ind

namespace L.Ind

open L.Arena

/-- The lookups of the `replaceFVars` block. -/
structure RxLook (p : Prog) : Prop where
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
  rw [invoke_eq _ L.rt]
  simp only [callFn, nestHoleImgRoot]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        hiAt_specW p L.hi n, slGetD_specW p L.gd n, internConst_spec p L.cf L.cp L.ci n,
        stubM_spec p "mk_app_n" n] <;>
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
  rw [invoke_eq _ L.fma]
  simp only [callFn, fvMapAt]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, hImg,
      keyMap_specW p L.km n, pinWord_specV p L.hl.hpw n, internSort_spec p L.hl.hsf L.hl.hsp L.hl.his n,
      internFVar_spec p L.hl.hff L.hl.hfp L.hl.hif n] <;>
    finish (gen := 20) [rdW_eq]

theorem rxImg_step (s₀ : St) (ctx po pl nn i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_hole_img" [ctx, po, pl, nn, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxImgW (n + 1) s₀.mem ctx po pl nn i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, hImg, hFr, -, -, -, -, -⟩ := ih
  rw [invoke_eq _ L.img]
  simp only [callFn, nestHoleImg]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, hImg, hFr,
      rxRoot_spec p L n, hiAt_specW p L.hi n] <;>
    finish (gen := 20) [rdW_eq]

theorem rxFrame_step (s₀ : St) (ctx po pl n1 i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_hole_img_frame" [ctx, po, pl, n1, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxFrameW (n + 1) s₀.mem ctx po pl n1 i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, -, -, hDs, -, -, -, -⟩ := ih
  rw [invoke_eq _ L.fr]
  simp only [callFn, nestHoleImgFrame]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, hDs,
      rec2_specW p L.ha L.h2 n, rec4_specW p L.ha L.h4 n, rec5_specW p L.ha L.h5 n,
      internConst_spec p L.cf L.cp L.ci n, stubM_spec p "mk_app_n" n] <;>
    finish (gen := 20) [rdW_eq]

theorem rxDs_step (s₀ : St) (f o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_hole_img_ds" [f, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ rxDsW (n + 1) s₀.mem f o l = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, -, -, -, hDg, -, -, -⟩ := ih
  rw [invoke_eq _ L.ds]
  simp only [callFn, nestHoleImgDs]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hDg, iwAlloc_specW p L.ha n] <;>
    finish (gen := 20)

theorem rxDsGo_step (s₀ : St) (f o l q j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_hole_img_ds_go" [f, o, l, q, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ rxDsGoW (n + 1) s₀.mem f o l q j = some s'.mem; ⊤⦄ := by
  obtain ⟨-, -, -, -, hDg, -, -, hRf⟩ := ih
  rw [invoke_eq _ L.dsg]
  simp only [callFn, nestHoleImgDsGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, hDg, hRf] <;>
    finish (gen := 20) [rdW_eq]

theorem rxGo_step (s₀ : St) (f fu h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "replace_fvars_go" [f, fu, h]
    ⦃fun r s' => LocEq s' s₀ ∧ rxGoW (n + 1) s₀.mem f fu h = some (r.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨hMap, -, -, -, -, -, hNd, -⟩ := ih
  rw [invoke_eq _ L.go]
  simp only [callFn, replaceFVarsGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p L.hl.hv n, hMap, memoFindG_spec rfSch p _ L.rff n,
      memoPutG_spec rfSch p _ L.rfp n, hNd] <;> finish (gen := 20) [St.setLocs_mem', rdW_eq]

theorem rxNode_step (s₀ : St) (f f1 g x y z : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "replace_fvars_node" [f, f1, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ rxNodeW (n + 1) s₀.mem f f1 g x y z = some (r.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, -, -, -, -, hGo, -, -⟩ := ih
  have hk := L.hk
  rw [invoke_eq _ L.nd]
  simp only [callFn, replaceFVarsNode]
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
  rw [invoke_eq _ L.rf]
  simp only [callFn, replaceFVars]
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
