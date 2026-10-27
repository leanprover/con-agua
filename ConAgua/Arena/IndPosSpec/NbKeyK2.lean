import ConAgua.Arena.IndPosSpec.GgW
import ConAgua.Arena.IndPosSpec.MW9
import ConAgua.Arena.IndPosSpec.NcnW
import ConAgua.Arena.IndPosSpec.NestContParamsClosed
import ConAgua.Arena.IndPosSpec.P2ctK1

/-!
# NbKeyK2

`wfWf`, `ncnWf`, `nbBindK6`, `nbBindK5`, `nbBindK4`, `nbBindK3` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Callees at any exec fuel -/

/-- `whnf_walk_fuel` at any exec fuel. -/
def wfWf : Nat → Mem → Word → Option (List Word × Mem)
  | n + 2, m, e => match wfW n m e with
    | none => none
    | some (r, m1) => some ([r], m1)
  | _, _, _ => none

/-- `nest_ctor_nf` at any exec fuel. -/
def ncnWf : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | k + 1, m, ctx, po, pl, us, dO, dL, cv, closed => match ncnW k m ctx po pl us dO dL cv closed with
    | none => none
    | some (r, m1) => some ([r], m1)
  | _, _, _, _, _, _, _, _, _, _ => none

def nbBindK6 (k ns2 : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (z, m6) => if 4294967296 ≤ z then none else some ([k, z, ns2], m6)
def nbBindK5 (a k ns2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m5) => nbBindK6 k ns2 (mkForallW m5 a (r.headD 0))
def nbBindK4 (dep a : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m4) => nbBindK5 a (r.headD 0) (r.tail.tail.headD 0)
      (abF m4 [CWF, r.tail.headD 0, dep, 0])
def nbBindK3 (posF : MW9) (vis ctx fu po pl dep kb : Word) (v : List Word) (ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => nbBindK4 dep (v.tail.headD 0) (posF m3 vis ctx fu po pl (dep + 1) (kb + 1) (r.headD 0) ns)
def nbBindK2 (posF : MW9) (vis ctx fu po pl dep kb : Word) (v : List Word) (ns : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (fv, m2) =>
    if 4294967296 ≤ fv then none
    else nbBindK3 posF vis ctx fu po pl dep kb v ns (i1F m2 [CWF, v.tail.tail.headD 0, fv, 0])
def nbBindK1 (posF : MW9) (vis ctx fu po pl dep kb : Word) (v : List Word) (ns : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (o, m1) =>
    if o ≠ 0 then none
    else if dep + 1 = 0 then none
    else if kb + 1 = 0 then none
    else nbBindK2 posF vis ctx fu po pl dep kb v ns (fvinternW m1 dep (v.tail.headD 0))

def nbPosK3 (w e ns : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (o, m3) => if o ≠ 0 then some ([0, w, ns], m3) else some ([0, e, ns], m3)
def nbPosK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m3)
def nbPosK5 (w : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([r.headD 0, w, r.tail.headD 0], m3)
def nbPosK2 (n : Nat) (bindF appF : MW9) (vis ctx fu po pl dep kb e ns hi w : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (o, m2) =>
    if o = 0 then nbPosK3 w e ns (noConstWf n m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1))
      (rdW (m2.arr64 IW) (ctx + 4)) hi e)
    else if w >>> 28 = 6 then nbPosK4 (bindF m2 vis ctx fu po pl dep kb w ns)
    else nbPosK5 w (appF m2 vis ctx fu po pl kb hi w ns)
def nbPosK1 (n : Nat) (bindF appF : MW9) (vis ctx fu po pl dep kb e ns hi : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => nbPosK2 n bindF appF vis ctx fu po pl dep kb e ns hi (r.headD 0)
      (noConstWf n m1 (rdW (m1.arr64 IW) ctx) (rdW (m1.arr64 IW) (ctx + 1)) (rdW (m1.arr64 IW) (ctx + 4)) hi
        (r.headD 0))

def nbAppK4 (ns : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([r.headD 0, ns], m3)
def nbAppK6 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([r.headD 0, r.tail.headD 0], m3)
def nbAppK5 (contF : MW11) (m2 : Mem) (vis ctx fu po pl kb ns aO aL : Word) (v : List Word) :
    Option Word → Option (List Word × Mem)
  | none => none
  | some o => if o ≠ 0 then none
    else nbAppK6 (contF m2 vis ctx fu po pl kb (v.tail.headD 0) (v.tail.tail.headD 0) aO aL ns)
def nbContK4 (keyF : MW13) (vis ctx fu po pl kb nn us aO aL ns nPc : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if aL ≠ nPc + r4.headD 0 then none
    else nbAppK6 (keyF m4 vis ctx fu po pl kb nn us aO nPc nPc (r4.tail.headD 0) ns)
def nbContK3 (cR : CallM) (k : Nat) (keyF : MW13) (vis ctx fu po pl kb nn us aO aL ns nPc hp : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (key, m3) => nbContK4 keyF vis ctx fu po pl kb nn us aO aL ns nPc (nitWf cR k m3 vis ctx hp key)
def nbContK2 (cR : CallM) (k : Nat) (keyF : MW13) (vis ctx fu po pl kb nn us aO aL ns nPc hp : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => nbContK3 cR k keyF vis ctx fu po pl kb nn us aO aL ns nPc hp (posRecW m2 [nn, us, aO, nPc])
def nbContK1 (cR : CallM) (k : Nat) (keyF : MW13) (vis ctx fu po pl kb nn us aO aL ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then none
    else if aL < r.tail.headD 0 then none
    else nbContK2 cR k keyF vis ctx fu po pl kb nn us aO aL ns (r.tail.headD 0) (nhiW m1 ctx pl)
      (p2ccW k m1 ctx (nhiW m1 ctx pl) nn aO (r.tail.headD 0) (aO + r.tail.headD 0) (aL - r.tail.headD 0))

def nbKeyK2 (k : Nat) (newF : MW13) (vis ctx fu po pl kb nn us dO dL nPc cty ns key : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) =>
    if r.headD 0 ≠ 0 then
      match nkcW k m2 (rdW (m2.arr64 IW) ns) (rdW (m2.arr64 IW) (ns + 1)) key with
      | none => none
      | some b => if b ≠ 0 then some ([nestedW kb, ns], m2)
        else nbAppK6 (newF m2 vis ctx fu po pl kb nn us dO dL nPc cty ns)
    else nbAppK6 (newF m2 vis ctx fu po pl kb nn us dO dL nPc cty ns)
def nbKeyK1 (k : Nat) (newF : MW13) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (key, m1) =>
    match nkcW k m1 (rdW (m1.arr64 IW) (ns + 2)) (rdW (m1.arr64 IW) (ns + 3)) key with
    | none => none
    | some b => if b ≠ 0 then none
      else nbKeyK2 k newF vis ctx fu po pl kb nn us dO dL nPc cty ns key (dcWf k m1 ctx dO dL)

def nbNewK9 (k : Nat) (ctx kb us dO dL ns gO gL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m9) => nbAppK6 (cfW k m9 ctx us dO dL gO gL (r.headD 0) (rdW (m9.arr64 IW) (ns + 2))
      (rdW (m9.arr64 IW) (ns + 3)) kb)
def nbNewK8 (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL hw gO gL : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ns1, m8) => nbNewK9 k ctx kb us dO dL ns gO gL
      (frameF m8 vis ctx fu wO wL hw us dO dL nPc gO gL ns1)
def nbNewK7 (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL hw gO gL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m7) => nbNewK8 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL
      (posRecW m7 [rdW (m7.arr64 IW) ns, rdW (m7.arr64 IW) (ns + 1), ra.headD 0, ra.tail.headD 0,
        rdW (m7.arr64 IW) (ns + 4), rdW (m7.arr64 IW) (ns + 5)])
def nbNewK6 (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL hw gO gL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m6) => nbNewK7 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL
      (appendW k m6 (ra.headD 0) (ra.tail.headD 0) (rdW (m6.arr64 IW) (ns + 2)) (rdW (m6.arr64 IW) (ns + 3)))
def nbNewK5 (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL hw : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rg, m5) => nbNewK6 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw (rg.headD 0) (rg.tail.headD 0)
      (caW k m5 us dO dL (rg.headD 0) (rg.tail.headD 0) 0 0)
def nbNewK4 (cR : CallM) (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL mO mL hw : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (g0, m4) => nbNewK5 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw
      (ggW cR k m4 vis ctx hw us dO dL mO mL (g0.headD 0) (g0.tail.headD 0))
def nbNewK3 (cR : CallM) (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL mO mL hw : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (pr, m3) => nbNewK4 cR k frameF vis ctx fu kb us dO dL nPc ns wO wL mO mL hw (new1W m3 pr)
def nbNewK2 (cR : CallM) (k : Nat) (frameF : MW13) (vis ctx fu kb nn us dO dL nPc cty ns wO wL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rm, m2) => nbNewK3 cR k frameF vis ctx fu kb us dO dL nPc ns wO wL (rm.headD 0) (rm.tail.headD 0)
      (nhiW m2 ctx wL) (posRecW m2 [nn, cty])
def nbNewK1 (cR : CallM) (k : Nat) (frameF : MW13) (vis ctx fu kb nn us dO dL nPc cty ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rw, m1) => nbNewK2 cR k frameF vis ctx fu kb nn us dO dL nPc cty ns (rw.headD 0) (rw.tail.headD 0)
      (nfmW k m1 vis nn)

def nbFrameK8 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m8) => some ([r.tail.tail.headD 0], m8)
def nbFrameK7 (ctorsF : MW19) (vis ctx fu hi us dO dL gL ns p2O p2L nO nL cO cL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rh, m7) =>
    if hi + gL < hi then none
    else if dL + gL < dL then none
    else nbFrameK8 (ctorsF m7 vis ctx 0 fu p2O p2L (hi + gL) us dO dL nO nL (rh.headD 0) (rh.tail.headD 0)
      cO cL ns 0 0)
def nbFrameK6 (k : Nat) (ctorsF : MW19) (vis ctx fu hi us dO dL gO gL ns p2O p2L nO nL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m6) => nbFrameK7 ctorsF vis ctx fu hi us dO dL gL ns p2O p2L nO nL (rc.headD 0) (rc.tail.headD 0)
      (fhW k m6 hi gO gL 0 0)
def nbCtorsK3 (ctorsF : MW19) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => ctorsF m3 vis ctx root fu po pl hi us dO dL no nl hO hL (cO + 1) (cL - 1) ns2
      (r.headD 0) (r.tail.headD 0)
def nbCtorsK2 (k : Nat) (ctorsF : MW19) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL ns2 : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rec, m2) => nbCtorsK3 ctorsF vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns2 (snocW k m2 oO oL rec)
def nbCtorsK1 (k : Nat) (ctorsF : MW19) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => nbCtorsK2 k ctorsF vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL
      (r.tail.tail.tail.headD 0) (posRecW m1 [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0])

def nbOneK7 (ksO ksL closed : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m7) => some ([ksO, ksL, closed, q], m7)
def nbOneK6 (ksO ksL closed ns2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m6) => nbOneK7 ksO ksL closed (posRecW m6 [rdW (m6.arr64 IW) ns2, rdW (m6.arr64 IW) (ns2 + 1),
      rdW (m6.arr64 IW) (ns2 + 2), rdW (m6.arr64 IW) (ns2 + 3), r.headD 0, r.tail.headD 0])
def nbOneK5 (k : Nat) (ksO ksL closed ns2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m5) => nbOneK6 ksO ksL closed ns2
      (snocW k m5 (rdW (m5.arr64 IW) (ns2 + 4)) (rdW (m5.arr64 IW) (ns2 + 5)) (r.headD 0))
def nbOneK4 (k : Nat) (ctx po pl us dO dL cv ksO ksL closed ns2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m4) =>
    if r.headD 0 = 0 then none
    else nbOneK5 k ksO ksL closed ns2 (ncnWf k m4 ctx po pl us dO dL cv closed)
def nbOneK3 (k : Nat) (ctx po pl hi us dO dL cv ksO ksL cur closed ns2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) =>
    if r.headD 0 ≠ 0 then none
    else nbOneK4 k ctx po pl us dO dL cv ksO ksL closed ns2 (roW k m3 ctx hi cur)
def nbOneK2 (k : Nat) (ctx po pl hi us dO dL cv nF : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rw, m2) => nbOneK3 k ctx po pl hi us dO dL cv (rw.headD 0) (rw.tail.headD 0) (rw.tail.tail.headD 0)
      (rw.tail.tail.tail.headD 0) (rw.tail.tail.tail.tail.headD 0)
      (u4W k m2 (rw.headD 0) nF (rw.tail.tail.tail.headD 0) 0)
def nbOneK1 (k : Nat) (walkF : MW10) (vis ctx root fu po pl hi us dO dL cv nF ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m1) => nbOneK2 k ctx po pl hi us dO dL cv nF
      (walkF m1 vis ctx root fu po pl hi nF (rc.headD 0) ns)

def nbWalkK3 (ksO ksL cur ns : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([ksO, ksL, cur, r.headD 0, ns], m3)
def nbWalkK2 (k : Nat) (hi : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => nbWalkK3 (r.headD 0) (r.tail.headD 0) (r.tail.tail.tail.tail.headD 0)
      (r.tail.tail.tail.tail.tail.headD 0)
      (closeW k m2 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) hi (r.tail.tail.tail.tail.headD 0))
def nbWalkK1 (k : Nat) (fieldsF : MW14) (vis ctx po pl hi nF crest ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m1) => nbWalkK2 k hi (fieldsF m1 vis ctx (rf.headD 0) po pl hi nF 0 crest ns 0 0 0 0)

def nbFieldsK5 (fieldsF : MW14) (vis ctx fu po pl base nF j ns2 b kO kL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rd, m5) => fieldsF m5 vis ctx fu po pl base (nF - 1) (j + 1) b ns2 kO kL (rd.headD 0) (rd.tail.headD 0)
def nbFieldsK4 (k : Nat) (fieldsF : MW14) (vis ctx fu po pl base nF j dO dL nd ns2 b : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rk, m4) => nbFieldsK5 fieldsF vis ctx fu po pl base nF j ns2 b (rk.headD 0) (rk.tail.headD 0)
      (snocW k m4 dO dL nd)
def nbFieldsK3 (k : Nat) (fieldsF : MW14) (vis ctx fu po pl base nF j kO kL dO dL kd nd ns2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m3) => nbFieldsK4 k fieldsF vis ctx fu po pl base nF j dO dL nd ns2 (rb.headD 0) (snocW k m3 kO kL kd)
def nbFieldsK2 (k : Nat) (fieldsF : MW14) (vis ctx fu po pl base nF j kO kL dO dL : Word) (v : List Word)
    (kd nd ns2 : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (fv, m2) =>
    if 4294967296 ≤ fv then none
    else nbFieldsK3 k fieldsF vis ctx fu po pl base nF j kO kL dO dL kd nd ns2
      (i1F m2 [CWF, v.tail.tail.headD 0, fv, 0])
def nbFieldsK1 (k : Nat) (fieldsF : MW14) (vis ctx fu po pl base nF j kO kL dO dL : Word) (v : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rp, m1) => nbFieldsK2 k fieldsF vis ctx fu po pl base nF j kO kL dO dL v (rp.headD 0) (rp.tail.headD 0)
      (rp.tail.tail.headD 0) (fvinternW m1 (base + j) (v.tail.headD 0))

end L.Ind

end
