import ConAgua.Arena.IndPosSpec.CfW
import ConAgua.Arena.IndPosSpec.NbKeyK2
import ConAgua.Arena.IndRealNames
import ConAgua.Arena.IndGrindAttr

/-!
# NbPosW

`nwsWf`, `MW17`, `nbAppK2`, `nbAppK1`, `nbFrameK5`, `nbFrameK4` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `nest_walk_stack` at any exec fuel. -/
def nwsWf : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | n + 1, m, ctx, off, l, po, pl => nwsW n m ctx off l po pl
  | _, _, _, _, _, _, _ => none

abbrev MW17 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
def nbAppK2 (n : Nat) (contF : MW11) (vis ctx fu po pl kb hi ns aO aL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rh, m2) =>
    if eViewW m2 (rh.headD 0) = [] then none
    else if (eViewW m2 (rh.headD 0)).headD 0 = 1 then
      nbAppK4 ns (pfW n m2 vis ctx po pl kb hi ((eViewW m2 (rh.headD 0)).tail.headD 0) aO aL)
    else if (eViewW m2 (rh.headD 0)).headD 0 = 3 then
      nbAppK5 contF m2 vis ctx fu po pl kb ns aO aL (eViewW m2 (rh.headD 0))
        (containsW n m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) ((eViewW m2 (rh.headD 0)).tail.headD 0))
    else none
def nbAppK1 (n : Nat) (contF : MW11) (vis ctx fu po pl kb hi w ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m1) => nbAppK2 n contF vis ctx fu po pl kb hi ns (ra.headD 0) (ra.tail.headD 0)
      (gafF m1 [CWF, w])

def nbFrameK5 (k : Nat) (ctorsF : MW19) (vis ctx fu hi us dO dL nPc gO gL ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rp, m5) => nbFrameK6 k ctorsF vis ctx fu hi us dO dL gO gL ns (rp.headD 0) (rp.tail.headD 0)
      (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0)
      (gcW k m5 vis nPc (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0) 0 0)
def nbFrameK4 (k : Nat) (ctorsF : MW19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m4) => nbFrameK5 k ctorsF vis ctx fu hi us dO dL nPc gO gL ns
      (fgW k m4 hi us dO dL gO gL po pl 0 0)
def nbFrameK3 (cR : CallM) (k : Nat) (ctorsF : MW19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m3) => nbFrameK4 k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns
      (cR k "infer_type_core" [vis, hi, ra.headD 0] m3)
def nbFrameK2 (cR : CallM) (k : Nat) (ctorsF : MW19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hc, m2) =>
    if 4294967296 ≤ hc then none
    else nbFrameK3 cR k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (mknF m2 [hc, dO, dL])
def nbFrameK1 (cR : CallM) (k : Nat) (ctorsF : MW19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rn, m1) =>
    if 4294967296 ≤ rn.headD 0 then none
    else nbFrameK2 cR k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (ceinternW m1 (rn.headD 0) us)

mutual
/-- `nest_pos(vis, ctx, fuel, progOff, progLen, dep, kb, e, ns)`. -/
def nbPosW (cR : CallM) : Nat → MW9
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, ctx, fu, po, pl, dep, kb, e, ns =>
    if fu = 0 then none
    else nbPosK1 n (nbBindW cR n) (nbAppW cR n) vis ctx (fu - 1) po pl dep kb e ns (nhiW m ctx pl)
      (cR n "whnf_top" [vis, dep, e] m)
/-- `nest_pos_bind(vis, ctx, fuel, progOff, progLen, dep, kb, w, ns)`. -/
def nbBindW (cR : CallM) : Nat → MW9
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, ctx, fu, po, pl, dep, kb, w, ns =>
    if eViewW m w = [] then none
    else nbBindK1 (nbPosW cR n) vis ctx fu po pl dep kb (eViewW m w) ns
      (noConstWf n m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx pl) ((eViewW m w).tail.headD 0))
/-- `nest_pos_app(vis, ctx, fuel, progOff, progLen, kb, hi, w, ns)`. -/
def nbAppW (cR : CallM) : Nat → MW9
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, ctx, fu, po, pl, kb, hi, w, ns =>
    nbAppK1 n (nbContW cR n) vis ctx fu po pl kb hi w ns (gaaF m [CWF, w])
/-- `nest_cont(vis, ctx, fuel, progOff, progLen, kb, n, us, argsOff, argsLen, ns)`. -/
def nbContW (cR : CallM) : Nat → MW11
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, fu, po, pl, kb, nn, us, aO, aL, ns =>
    nbContK1 cR k (nbKeyW cR k) vis ctx fu po pl kb nn us aO aL ns (ntWf k m vis nn)
/-- `nest_cont_key(vis, ctx, fuel, progOff, progLen, kb, n, us, dsOff, dsLen, nPc, cty, ns)`. -/
def nbKeyW (cR : CallM) : Nat → MW13
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns =>
    nbKeyK1 k (nbNewW cR k) vis ctx fu po pl kb nn us dO dL nPc cty ns (posRecW m [nn, us, dO, dL])
/-- `nest_cont_new(vis, ctx, fuel, progOff, progLen, kb, n, us, dsOff, dsLen, nPc, cty, ns)`. -/
def nbNewW (cR : CallM) : Nat → MW13
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns =>
    nbNewK1 cR k (nbFrameW cR k) vis ctx fu kb nn us dO dL nPc cty ns (nwsWf k m ctx dO dL po pl)
/-- `nest_frame(vis, ctx, fuel, progOff, progLen, hi, us, dsOff, dsLen, nPc, grpOff, grpLen, ns)`. -/
def nbFrameW (cR : CallM) : Nat → MW13
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, fu, po, pl, hi, us, dO, dL, nPc, gO, gL, ns =>
    nbFrameK1 cR k (nbCtorsW cR k) vis ctx fu po pl hi us dO dL nPc gO gL ns
      (if gL = 0 then naF m [] else some ([rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m))
/-- `nest_ctors(vis, ctx, root, fuel, progOff, progLen, hi, us, dsOff, dsLen, namesOff, namesLen,
holesOff, holesLen, csOff, csLen, ns, outsOff, outsLen)`. -/
def nbCtorsW (cR : CallM) : Nat → MW19
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cO, cL, ns, oO, oL =>
    if cL = 0 then some ([oO, oL, ns], m)
    else nbCtorsK1 k (nbCtorsW cR k) vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL
      (nbOneW cR k m vis ctx root fu po pl hi us dO dL no nl hO hL (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1)) ns)
/-- `nest_ctors_one(vis, ctx, root, fuel, progOff, progLen, hi, us, dsOff, dsLen, namesOff,
namesLen, holesOff, holesLen, cv, nF, ns)`. -/
def nbOneW (cR : CallM) : Nat → MW17
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cv, nF, ns =>
    nbOneK1 k (nbWalkW cR k) vis ctx root fu po pl hi us dO dL cv nF ns (p2ctW cR k m vis no nl us dO dL hO hL cv hi)
/-- `nest_ctors_walk(vis, ctx, root, fuel, progOff, progLen, hi, nF, crest, ns)`. -/
def nbWalkW (cR : CallM) : Nat → MW10
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, root, fu, po, pl, hi, nF, crest, ns =>
    if root ≠ 0 then nbWalkK1 k (nbFieldsW cR k) vis ctx po pl hi nF crest ns (wfWf k m crest)
    else nbWalkK2 k hi (nbFieldsW cR k m vis ctx fu po pl hi nF 0 crest ns 0 0 0 0)
/-- `nest_fields(vis, ctx, fuel, progOff, progLen, base, nF, j, cur, ns, ksOff, ksLen, ndsOff,
ndsLen)`. -/
def nbFieldsW (cR : CallM) : Nat → MW14
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, fu, po, pl, base, nF, j, cur, ns, kO, kL, dO, dL =>
    if nF = 0 then some ([kO, kL, dO, dL, cur, ns], m)
    else if cur >>> 28 ≠ 6 then none
    else if base + j < base then none
    else if base + j + 1 = 0 then none
    else if eViewW m cur = [] then none
    else nbFieldsK1 k (nbFieldsW cR k) vis ctx fu po pl base nF j kO kL dO dL (eViewW m cur)
      (nbPosW cR k m vis ctx fu po pl (base + j) 0 ((eViewW m cur).tail.headD 0) ns)
end

theorem nbPosW_succ (cR : CallM) (n : Nat) (m : Mem) (vis ctx fu po pl dep kb e ns : Word) :
    nbPosW cR (n + 1) m vis ctx fu po pl dep kb e ns =
      if fu = 0 then none
      else nbPosK1 n (nbBindW cR n) (nbAppW cR n) vis ctx (fu - 1) po pl dep kb e ns (nhiW m ctx pl)
        (cR n "whnf_top" [vis, dep, e] m) := by
  rw [nbPosW]
theorem nbBindW_succ (cR : CallM) (n : Nat) (m : Mem) (vis ctx fu po pl dep kb w ns : Word) :
    nbBindW cR (n + 1) m vis ctx fu po pl dep kb w ns =
      if eViewW m w = [] then none
      else nbBindK1 (nbPosW cR n) vis ctx fu po pl dep kb (eViewW m w) ns
        (noConstWf n m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
          (nhiW m ctx pl) ((eViewW m w).tail.headD 0)) := by
  rw [nbBindW]
theorem nbAppW_succ (cR : CallM) (n : Nat) (m : Mem) (vis ctx fu po pl kb hi w ns : Word) :
    nbAppW cR (n + 1) m vis ctx fu po pl kb hi w ns = nbAppK1 n (nbContW cR n) vis ctx fu po pl kb hi w ns (gaaF m [CWF, w]) := by
  rw [nbAppW]
theorem nbContW_succ (cR : CallM) (k : Nat) (m : Mem) (vis ctx fu po pl kb nn us aO aL ns : Word) :
    nbContW cR (k + 1) m vis ctx fu po pl kb nn us aO aL ns = nbContK1 cR k (nbKeyW cR k) vis ctx fu po pl kb nn us aO aL ns (ntWf k m vis nn) := by
  rw [nbContW]
theorem nbKeyW_succ (cR : CallM) (k : Nat) (m : Mem) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word) :
    nbKeyW cR (k + 1) m vis ctx fu po pl kb nn us dO dL nPc cty ns = nbKeyK1 k (nbNewW cR k) vis ctx fu po pl kb nn us dO dL nPc cty ns (posRecW m [nn, us, dO, dL]) := by
  rw [nbKeyW]
theorem nbNewW_succ (cR : CallM) (k : Nat) (m : Mem) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word) :
    nbNewW cR (k + 1) m vis ctx fu po pl kb nn us dO dL nPc cty ns = nbNewK1 cR k (nbFrameW cR k) vis ctx fu kb nn us dO dL nPc cty ns (nwsWf k m ctx dO dL po pl) := by
  rw [nbNewW]
theorem nbFrameW_succ (cR : CallM) (k : Nat) (m : Mem) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) :
    nbFrameW cR (k + 1) m vis ctx fu po pl hi us dO dL nPc gO gL ns =
nbFrameK1 cR k (nbCtorsW cR k) vis ctx fu po pl hi us dO dL nPc gO gL ns
        (if gL = 0 then naF m [] else some ([rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m)) := by
  rw [nbFrameW]
theorem nbCtorsW_succ (cR : CallM) (k : Nat) (m : Mem) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL : Word) :
    nbCtorsW cR (k + 1) m vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL =
      if cL = 0 then some ([oO, oL, ns], m)
      else nbCtorsK1 k (nbCtorsW cR k) vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL
        (nbOneW cR k m vis ctx root fu po pl hi us dO dL no nl hO hL (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO))
          (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1)) ns) := by
  rw [nbCtorsW]
theorem nbOneW_succ (cR : CallM) (k : Nat) (m : Mem) (vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns : Word) :
    nbOneW cR (k + 1) m vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns = nbOneK1 k (nbWalkW cR k) vis ctx root fu po pl hi us dO dL cv nF ns (p2ctW cR k m vis no nl us dO dL hO hL cv hi) := by
  rw [nbOneW]
theorem nbWalkW_succ (cR : CallM) (k : Nat) (m : Mem) (vis ctx root fu po pl hi nF crest ns : Word) :
    nbWalkW cR (k + 1) m vis ctx root fu po pl hi nF crest ns =
      if root ≠ 0 then nbWalkK1 k (nbFieldsW cR k) vis ctx po pl hi nF crest ns (wfWf k m crest)
      else nbWalkK2 k hi (nbFieldsW cR k m vis ctx fu po pl hi nF 0 crest ns 0 0 0 0) := by
  rw [nbWalkW]
theorem nbFieldsW_succ (cR : CallM) (k : Nat) (m : Mem) (vis ctx fu po pl base nF j cur ns kO kL dO dL : Word) :
    nbFieldsW cR (k + 1) m vis ctx fu po pl base nF j cur ns kO kL dO dL =
      if nF = 0 then some ([kO, kL, dO, dL, cur, ns], m)
      else if cur >>> 28 ≠ 6 then none
      else if base + j < base then none
      else if base + j + 1 = 0 then none
      else if eViewW m cur = [] then none
      else nbFieldsK1 k (nbFieldsW cR k) vis ctx fu po pl base nF j kO kL dO dL (eViewW m cur)
        (nbPosW cR k m vis ctx fu po pl (base + j) 0 ((eViewW m cur).tail.headD 0) ns) := by
  rw [nbFieldsW]
attribute [ind_grind] nbPosW_succ nbBindW_succ nbAppW_succ nbContW_succ nbKeyW_succ nbNewW_succ nbFrameW_succ nbCtorsW_succ nbOneW_succ nbWalkW_succ nbFieldsW_succ

attribute [irreducible] nbPosW nbBindW nbAppW nbContW nbKeyW nbNewW nbFrameW nbCtorsW nbOneW nbWalkW
  nbFieldsW

end L.Ind

end
