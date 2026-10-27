import ConAgua.Arena.IndPos2SpecM
import ConAgua.Arena.IndRealNames

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the word models of the
mutual block (`nest_pos`, `nest_pos_bind`, `nest_pos_app`, `nest_cont`, `nest_cont_key`,
`nest_cont_new`, `nest_frame`, `nest_ctors`, `nest_ctors_one`, `nest_ctors_walk`, `nest_fields`),
each at exec fuel `n + 1` over its callees at `n`. -/


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

/-- `nest_walk_stack` at any exec fuel. -/
def nwsWf : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | n + 1, m, ctx, off, l, po, pl => nwsW n m ctx off l po pl
  | _, _, _, _, _, _, _ => none

/-! ## The block's models

The continuations take the block's functions they call (at the caller's fuel `n`) as arguments, so
that the block itself is a structural recursion on the exec fuel. -/

/-! Model types: a memory and `k` words. -/
abbrev MW9 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
abbrev MW10 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
abbrev MW11 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
abbrev MW13 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
abbrev MW14 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
abbrev MW17 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
abbrev MW19 := Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)

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

/-! ## The models' arms -/

theorem nbBindK6_some (k ns2 : Word) (z : Word) (m6 : Mem) :
    nbBindK6 k ns2 (some (z, m6)) = if 4294967296 ≤ z then none else some ([k, z, ns2], m6) := rfl
theorem nbBindK5_some (a k ns2 : Word) (r : List Word) (m5 : Mem) :
    nbBindK5 a k ns2 (some (r, m5)) = nbBindK6 k ns2 (mkForallW m5 a (r.headD 0)) := rfl
theorem nbBindK4_some (dep a : Word) (r : List Word) (m4 : Mem) :
    nbBindK4 dep a (some (r, m4)) = nbBindK5 a (r.headD 0) (r.tail.tail.headD 0)
      (abF m4 [CWF, r.tail.headD 0, dep, 0]) := rfl
theorem nbBindK3_some (posF : MW9) (vis ctx fu po pl dep kb : Word) (v : List Word) (ns : Word) (r : List Word) (m3 : Mem) :
    nbBindK3 posF vis ctx fu po pl dep kb v ns (some (r, m3)) = nbBindK4 dep (v.tail.headD 0) (posF m3 vis ctx fu po pl (dep + 1) (kb + 1) (r.headD 0) ns) := rfl
theorem nbBindK2_some (posF : MW9) (vis ctx fu po pl dep kb : Word) (v : List Word) (ns : Word) (fv : Word) (m2 : Mem) :
    nbBindK2 posF vis ctx fu po pl dep kb v ns (some (fv, m2)) =
    if 4294967296 ≤ fv then none
    else nbBindK3 posF vis ctx fu po pl dep kb v ns (i1F m2 [CWF, v.tail.tail.headD 0, fv, 0]) := rfl
theorem nbBindK1_some (posF : MW9) (vis ctx fu po pl dep kb : Word) (v : List Word) (ns : Word) (o : Word) (m1 : Mem) :
    nbBindK1 posF vis ctx fu po pl dep kb v ns (some (o, m1)) =
    if o ≠ 0 then none
    else if dep + 1 = 0 then none
    else if kb + 1 = 0 then none
    else nbBindK2 posF vis ctx fu po pl dep kb v ns (fvinternW m1 dep (v.tail.headD 0)) := rfl
theorem nbPosK3_some (w e ns : Word) (o : Word) (m3 : Mem) :
    nbPosK3 w e ns (some (o, m3)) = if o ≠ 0 then some ([0, w, ns], m3) else some ([0, e, ns], m3) := rfl
theorem nbPosK4_some (r : List Word) (m3 : Mem) :
    nbPosK4 (some (r, m3)) = some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m3) := rfl
theorem nbPosK5_some (w : Word) (r : List Word) (m3 : Mem) :
    nbPosK5 w (some (r, m3)) = some ([r.headD 0, w, r.tail.headD 0], m3) := rfl
theorem nbPosK2_some (n : Nat) (bindF appF : MW9) (vis ctx fu po pl dep kb e ns hi w : Word) (o : Word) (m2 : Mem) :
    nbPosK2 n bindF appF vis ctx fu po pl dep kb e ns hi w (some (o, m2)) =
    if o = 0 then nbPosK3 w e ns (noConstWf n m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1))
      (rdW (m2.arr64 IW) (ctx + 4)) hi e)
    else if w >>> 28 = 6 then nbPosK4 (bindF m2 vis ctx fu po pl dep kb w ns)
    else nbPosK5 w (appF m2 vis ctx fu po pl kb hi w ns) := rfl
theorem nbPosK1_some (n : Nat) (bindF appF : MW9) (vis ctx fu po pl dep kb e ns hi : Word) (r : List Word) (m1 : Mem) :
    nbPosK1 n bindF appF vis ctx fu po pl dep kb e ns hi (some (r, m1)) = nbPosK2 n bindF appF vis ctx fu po pl dep kb e ns hi (r.headD 0)
      (noConstWf n m1 (rdW (m1.arr64 IW) ctx) (rdW (m1.arr64 IW) (ctx + 1)) (rdW (m1.arr64 IW) (ctx + 4)) hi
        (r.headD 0)) := rfl
theorem nbAppK4_some (ns : Word) (r : List Word) (m3 : Mem) :
    nbAppK4 ns (some (r, m3)) = some ([r.headD 0, ns], m3) := rfl
theorem nbAppK6_some (r : List Word) (m3 : Mem) :
    nbAppK6 (some (r, m3)) = some ([r.headD 0, r.tail.headD 0], m3) := rfl
theorem nbAppK5_some (contF : MW11) (m2 : Mem) (vis ctx fu po pl kb ns aO aL : Word) (v : List Word) (o : Word) :
    nbAppK5 contF m2 vis ctx fu po pl kb ns aO aL v (some o) = if o ≠ 0 then none
    else nbAppK6 (contF m2 vis ctx fu po pl kb (v.tail.headD 0) (v.tail.tail.headD 0) aO aL ns) := rfl
theorem nbAppK2_some (n : Nat) (contF : MW11) (vis ctx fu po pl kb hi ns aO aL : Word) (rh : List Word) (m2 : Mem) :
    nbAppK2 n contF vis ctx fu po pl kb hi ns aO aL (some (rh, m2)) =
    if eViewW m2 (rh.headD 0) = [] then none
    else if (eViewW m2 (rh.headD 0)).headD 0 = 1 then
      nbAppK4 ns (pfW n m2 vis ctx po pl kb hi ((eViewW m2 (rh.headD 0)).tail.headD 0) aO aL)
    else if (eViewW m2 (rh.headD 0)).headD 0 = 3 then
      nbAppK5 contF m2 vis ctx fu po pl kb ns aO aL (eViewW m2 (rh.headD 0))
        (containsW n m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) ((eViewW m2 (rh.headD 0)).tail.headD 0))
    else none := rfl
theorem nbAppK1_some (n : Nat) (contF : MW11) (vis ctx fu po pl kb hi w ns : Word) (ra : List Word) (m1 : Mem) :
    nbAppK1 n contF vis ctx fu po pl kb hi w ns (some (ra, m1)) = nbAppK2 n contF vis ctx fu po pl kb hi ns (ra.headD 0) (ra.tail.headD 0)
      (gafF m1 [CWF, w]) := rfl
theorem nbContK4_some (keyF : MW13) (vis ctx fu po pl kb nn us aO aL ns nPc : Word) (r4 : List Word) (m4 : Mem) :
    nbContK4 keyF vis ctx fu po pl kb nn us aO aL ns nPc (some (r4, m4)) =
    if aL ≠ nPc + r4.headD 0 then none
    else nbAppK6 (keyF m4 vis ctx fu po pl kb nn us aO nPc nPc (r4.tail.headD 0) ns) := rfl
theorem nbContK3_some (cR : CallM) (k : Nat) (keyF : MW13) (vis ctx fu po pl kb nn us aO aL ns nPc hp : Word) (key : Word) (m3 : Mem) :
    nbContK3 cR k keyF vis ctx fu po pl kb nn us aO aL ns nPc hp (some (key, m3)) = nbContK4 keyF vis ctx fu po pl kb nn us aO aL ns nPc (nitWf cR k m3 vis ctx hp key) := rfl
theorem nbContK2_some (cR : CallM) (k : Nat) (keyF : MW13) (vis ctx fu po pl kb nn us aO aL ns nPc hp : Word) (w_ : List Word) (m2 : Mem) :
    nbContK2 cR k keyF vis ctx fu po pl kb nn us aO aL ns nPc hp (some (w_, m2)) = nbContK3 cR k keyF vis ctx fu po pl kb nn us aO aL ns nPc hp (posRecW m2 [nn, us, aO, nPc]) := rfl
theorem nbContK1_some (cR : CallM) (k : Nat) (keyF : MW13) (vis ctx fu po pl kb nn us aO aL ns : Word) (r : List Word) (m1 : Mem) :
    nbContK1 cR k keyF vis ctx fu po pl kb nn us aO aL ns (some (r, m1)) =
    if r.headD 0 = 0 then none
    else if aL < r.tail.headD 0 then none
    else nbContK2 cR k keyF vis ctx fu po pl kb nn us aO aL ns (r.tail.headD 0) (nhiW m1 ctx pl)
      (p2ccW k m1 ctx (nhiW m1 ctx pl) nn aO (r.tail.headD 0) (aO + r.tail.headD 0) (aL - r.tail.headD 0)) := rfl
theorem nbKeyK2_some (k : Nat) (newF : MW13) (vis ctx fu po pl kb nn us dO dL nPc cty ns key : Word) (r : List Word) (m2 : Mem) :
    nbKeyK2 k newF vis ctx fu po pl kb nn us dO dL nPc cty ns key (some (r, m2)) =
    if r.headD 0 ≠ 0 then
      match nkcW k m2 (rdW (m2.arr64 IW) ns) (rdW (m2.arr64 IW) (ns + 1)) key with
      | none => none
      | some b => if b ≠ 0 then some ([nestedW kb, ns], m2)
        else nbAppK6 (newF m2 vis ctx fu po pl kb nn us dO dL nPc cty ns)
    else nbAppK6 (newF m2 vis ctx fu po pl kb nn us dO dL nPc cty ns) := rfl
theorem nbKeyK1_some (k : Nat) (newF : MW13) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word) (key : Word) (m1 : Mem) :
    nbKeyK1 k newF vis ctx fu po pl kb nn us dO dL nPc cty ns (some (key, m1)) =
    match nkcW k m1 (rdW (m1.arr64 IW) (ns + 2)) (rdW (m1.arr64 IW) (ns + 3)) key with
    | none => none
    | some b => if b ≠ 0 then none
      else nbKeyK2 k newF vis ctx fu po pl kb nn us dO dL nPc cty ns key (dcWf k m1 ctx dO dL) := rfl
theorem nbNewK9_some (k : Nat) (ctx kb us dO dL ns gO gL : Word) (r : List Word) (m9 : Mem) :
    nbNewK9 k ctx kb us dO dL ns gO gL (some (r, m9)) = nbAppK6 (cfW k m9 ctx us dO dL gO gL (r.headD 0) (rdW (m9.arr64 IW) (ns + 2))
      (rdW (m9.arr64 IW) (ns + 3)) kb) := rfl
theorem nbNewK8_some (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL hw gO gL : Word) (ns1 : Word) (m8 : Mem) :
    nbNewK8 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL (some (ns1, m8)) = nbNewK9 k ctx kb us dO dL ns gO gL
      (frameF m8 vis ctx fu wO wL hw us dO dL nPc gO gL ns1) := rfl
theorem nbNewK7_some (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL hw gO gL : Word) (ra : List Word) (m7 : Mem) :
    nbNewK7 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL (some (ra, m7)) = nbNewK8 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL
      (posRecW m7 [rdW (m7.arr64 IW) ns, rdW (m7.arr64 IW) (ns + 1), ra.headD 0, ra.tail.headD 0,
        rdW (m7.arr64 IW) (ns + 4), rdW (m7.arr64 IW) (ns + 5)]) := rfl
theorem nbNewK6_some (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL hw gO gL : Word) (ra : List Word) (m6 : Mem) :
    nbNewK6 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL (some (ra, m6)) = nbNewK7 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL
      (appendW k m6 (ra.headD 0) (ra.tail.headD 0) (rdW (m6.arr64 IW) (ns + 2)) (rdW (m6.arr64 IW) (ns + 3))) := rfl
theorem nbNewK5_some (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL hw : Word) (rg : List Word) (m5 : Mem) :
    nbNewK5 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw (some (rg, m5)) = nbNewK6 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw (rg.headD 0) (rg.tail.headD 0)
      (caW k m5 us dO dL (rg.headD 0) (rg.tail.headD 0) 0 0) := rfl
theorem nbNewK4_some (cR : CallM) (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL mO mL hw : Word) (g0 : List Word) (m4 : Mem) :
    nbNewK4 cR k frameF vis ctx fu kb us dO dL nPc ns wO wL mO mL hw (some (g0, m4)) = nbNewK5 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw
      (ggW cR k m4 vis ctx hw us dO dL mO mL (g0.headD 0) (g0.tail.headD 0)) := rfl
theorem nbNewK3_some (cR : CallM) (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL mO mL hw : Word) (pr : Word) (m3 : Mem) :
    nbNewK3 cR k frameF vis ctx fu kb us dO dL nPc ns wO wL mO mL hw (some (pr, m3)) = nbNewK4 cR k frameF vis ctx fu kb us dO dL nPc ns wO wL mO mL hw (new1W m3 pr) := rfl
theorem nbNewK2_some (cR : CallM) (k : Nat) (frameF : MW13) (vis ctx fu kb nn us dO dL nPc cty ns wO wL : Word) (rm : List Word) (m2 : Mem) :
    nbNewK2 cR k frameF vis ctx fu kb nn us dO dL nPc cty ns wO wL (some (rm, m2)) = nbNewK3 cR k frameF vis ctx fu kb us dO dL nPc ns wO wL (rm.headD 0) (rm.tail.headD 0)
      (nhiW m2 ctx wL) (posRecW m2 [nn, cty]) := rfl
theorem nbNewK1_some (cR : CallM) (k : Nat) (frameF : MW13) (vis ctx fu kb nn us dO dL nPc cty ns : Word) (rw : List Word) (m1 : Mem) :
    nbNewK1 cR k frameF vis ctx fu kb nn us dO dL nPc cty ns (some (rw, m1)) = nbNewK2 cR k frameF vis ctx fu kb nn us dO dL nPc cty ns (rw.headD 0) (rw.tail.headD 0)
      (nfmW k m1 vis nn) := rfl
theorem nbFrameK8_some (r : List Word) (m8 : Mem) :
    nbFrameK8 (some (r, m8)) = some ([r.tail.tail.headD 0], m8) := rfl
theorem nbFrameK7_some (ctorsF : MW19) (vis ctx fu hi us dO dL gL ns p2O p2L nO nL cO cL : Word) (rh : List Word) (m7 : Mem) :
    nbFrameK7 ctorsF vis ctx fu hi us dO dL gL ns p2O p2L nO nL cO cL (some (rh, m7)) =
    if hi + gL < hi then none
    else if dL + gL < dL then none
    else nbFrameK8 (ctorsF m7 vis ctx 0 fu p2O p2L (hi + gL) us dO dL nO nL (rh.headD 0) (rh.tail.headD 0)
      cO cL ns 0 0) := rfl
theorem nbFrameK6_some (k : Nat) (ctorsF : MW19) (vis ctx fu hi us dO dL gO gL ns p2O p2L nO nL : Word) (rc : List Word) (m6 : Mem) :
    nbFrameK6 k ctorsF vis ctx fu hi us dO dL gO gL ns p2O p2L nO nL (some (rc, m6)) = nbFrameK7 ctorsF vis ctx fu hi us dO dL gL ns p2O p2L nO nL (rc.headD 0) (rc.tail.headD 0)
      (fhW k m6 hi gO gL 0 0) := rfl
theorem nbFrameK5_some (k : Nat) (ctorsF : MW19) (vis ctx fu hi us dO dL nPc gO gL ns : Word) (rp : List Word) (m5 : Mem) :
    nbFrameK5 k ctorsF vis ctx fu hi us dO dL nPc gO gL ns (some (rp, m5)) = nbFrameK6 k ctorsF vis ctx fu hi us dO dL gO gL ns (rp.headD 0) (rp.tail.headD 0)
      (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0)
      (gcW k m5 vis nPc (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0) 0 0) := rfl
theorem nbFrameK4_some (k : Nat) (ctorsF : MW19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) (w_ : List Word) (m4 : Mem) :
    nbFrameK4 k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (some (w_, m4)) = nbFrameK5 k ctorsF vis ctx fu hi us dO dL nPc gO gL ns
      (fgW k m4 hi us dO dL gO gL po pl 0 0) := rfl
theorem nbFrameK3_some (cR : CallM) (k : Nat) (ctorsF : MW19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) (ra : List Word) (m3 : Mem) :
    nbFrameK3 cR k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (some (ra, m3)) = nbFrameK4 k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns
      (cR k "infer_type_core" [vis, hi, ra.headD 0] m3) := rfl
theorem nbFrameK2_some (cR : CallM) (k : Nat) (ctorsF : MW19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) (hc : Word) (m2 : Mem) :
    nbFrameK2 cR k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (some (hc, m2)) =
    if 4294967296 ≤ hc then none
    else nbFrameK3 cR k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (mknF m2 [hc, dO, dL]) := rfl
theorem nbFrameK1_some (cR : CallM) (k : Nat) (ctorsF : MW19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) (rn : List Word) (m1 : Mem) :
    nbFrameK1 cR k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (some (rn, m1)) =
    if 4294967296 ≤ rn.headD 0 then none
    else nbFrameK2 cR k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (ceinternW m1 (rn.headD 0) us) := rfl
theorem nbCtorsK3_some (ctorsF : MW19) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns2 : Word) (r : List Word) (m3 : Mem) :
    nbCtorsK3 ctorsF vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns2 (some (r, m3)) = ctorsF m3 vis ctx root fu po pl hi us dO dL no nl hO hL (cO + 1) (cL - 1) ns2
      (r.headD 0) (r.tail.headD 0) := rfl
theorem nbCtorsK2_some (k : Nat) (ctorsF : MW19) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL ns2 : Word) (rec : Word) (m2 : Mem) :
    nbCtorsK2 k ctorsF vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL ns2 (some (rec, m2)) = nbCtorsK3 ctorsF vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns2 (snocW k m2 oO oL rec) := rfl
theorem nbCtorsK1_some (k : Nat) (ctorsF : MW19) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL : Word) (r : List Word) (m1 : Mem) :
    nbCtorsK1 k ctorsF vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL (some (r, m1)) = nbCtorsK2 k ctorsF vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL
      (r.tail.tail.tail.headD 0) (posRecW m1 [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0]) := rfl
theorem nbOneK7_some (ksO ksL closed : Word) (q : Word) (m7 : Mem) :
    nbOneK7 ksO ksL closed (some (q, m7)) = some ([ksO, ksL, closed, q], m7) := rfl
theorem nbOneK6_some (ksO ksL closed ns2 : Word) (r : List Word) (m6 : Mem) :
    nbOneK6 ksO ksL closed ns2 (some (r, m6)) = nbOneK7 ksO ksL closed (posRecW m6 [rdW (m6.arr64 IW) ns2, rdW (m6.arr64 IW) (ns2 + 1),
      rdW (m6.arr64 IW) (ns2 + 2), rdW (m6.arr64 IW) (ns2 + 3), r.headD 0, r.tail.headD 0]) := rfl
theorem nbOneK5_some (k : Nat) (ksO ksL closed ns2 : Word) (r : List Word) (m5 : Mem) :
    nbOneK5 k ksO ksL closed ns2 (some (r, m5)) = nbOneK6 ksO ksL closed ns2
      (snocW k m5 (rdW (m5.arr64 IW) (ns2 + 4)) (rdW (m5.arr64 IW) (ns2 + 5)) (r.headD 0)) := rfl
theorem nbOneK4_some (k : Nat) (ctx po pl us dO dL cv ksO ksL closed ns2 : Word) (r : List Word) (m4 : Mem) :
    nbOneK4 k ctx po pl us dO dL cv ksO ksL closed ns2 (some (r, m4)) =
    if r.headD 0 = 0 then none
    else nbOneK5 k ksO ksL closed ns2 (ncnWf k m4 ctx po pl us dO dL cv closed) := rfl
theorem nbOneK3_some (k : Nat) (ctx po pl hi us dO dL cv ksO ksL cur closed ns2 : Word) (r : List Word) (m3 : Mem) :
    nbOneK3 k ctx po pl hi us dO dL cv ksO ksL cur closed ns2 (some (r, m3)) =
    if r.headD 0 ≠ 0 then none
    else nbOneK4 k ctx po pl us dO dL cv ksO ksL closed ns2 (roW k m3 ctx hi cur) := rfl
theorem nbOneK2_some (k : Nat) (ctx po pl hi us dO dL cv nF : Word) (rw : List Word) (m2 : Mem) :
    nbOneK2 k ctx po pl hi us dO dL cv nF (some (rw, m2)) = nbOneK3 k ctx po pl hi us dO dL cv (rw.headD 0) (rw.tail.headD 0) (rw.tail.tail.headD 0)
      (rw.tail.tail.tail.headD 0) (rw.tail.tail.tail.tail.headD 0)
      (u4W k m2 (rw.headD 0) nF (rw.tail.tail.tail.headD 0) 0) := rfl
theorem nbOneK1_some (k : Nat) (walkF : MW10) (vis ctx root fu po pl hi us dO dL cv nF ns : Word) (rc : List Word) (m1 : Mem) :
    nbOneK1 k walkF vis ctx root fu po pl hi us dO dL cv nF ns (some (rc, m1)) = nbOneK2 k ctx po pl hi us dO dL cv nF
      (walkF m1 vis ctx root fu po pl hi nF (rc.headD 0) ns) := rfl
theorem nbWalkK3_some (ksO ksL cur ns : Word) (r : List Word) (m3 : Mem) :
    nbWalkK3 ksO ksL cur ns (some (r, m3)) = some ([ksO, ksL, cur, r.headD 0, ns], m3) := rfl
theorem nbWalkK2_some (k : Nat) (hi : Word) (r : List Word) (m2 : Mem) :
    nbWalkK2 k hi (some (r, m2)) = nbWalkK3 (r.headD 0) (r.tail.headD 0) (r.tail.tail.tail.tail.headD 0)
      (r.tail.tail.tail.tail.tail.headD 0)
      (closeW k m2 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) hi (r.tail.tail.tail.tail.headD 0)) := rfl
theorem nbWalkK1_some (k : Nat) (fieldsF : MW14) (vis ctx po pl hi nF crest ns : Word) (rf : List Word) (m1 : Mem) :
    nbWalkK1 k fieldsF vis ctx po pl hi nF crest ns (some (rf, m1)) = nbWalkK2 k hi (fieldsF m1 vis ctx (rf.headD 0) po pl hi nF 0 crest ns 0 0 0 0) := rfl
theorem nbFieldsK5_some (fieldsF : MW14) (vis ctx fu po pl base nF j ns2 b kO kL : Word) (rd : List Word) (m5 : Mem) :
    nbFieldsK5 fieldsF vis ctx fu po pl base nF j ns2 b kO kL (some (rd, m5)) = fieldsF m5 vis ctx fu po pl base (nF - 1) (j + 1) b ns2 kO kL (rd.headD 0) (rd.tail.headD 0) := rfl
theorem nbFieldsK4_some (k : Nat) (fieldsF : MW14) (vis ctx fu po pl base nF j dO dL nd ns2 b : Word) (rk : List Word) (m4 : Mem) :
    nbFieldsK4 k fieldsF vis ctx fu po pl base nF j dO dL nd ns2 b (some (rk, m4)) = nbFieldsK5 fieldsF vis ctx fu po pl base nF j ns2 b (rk.headD 0) (rk.tail.headD 0)
      (snocW k m4 dO dL nd) := rfl
theorem nbFieldsK3_some (k : Nat) (fieldsF : MW14) (vis ctx fu po pl base nF j kO kL dO dL kd nd ns2 : Word) (rb : List Word) (m3 : Mem) :
    nbFieldsK3 k fieldsF vis ctx fu po pl base nF j kO kL dO dL kd nd ns2 (some (rb, m3)) = nbFieldsK4 k fieldsF vis ctx fu po pl base nF j dO dL nd ns2 (rb.headD 0) (snocW k m3 kO kL kd) := rfl
theorem nbFieldsK2_some (k : Nat) (fieldsF : MW14) (vis ctx fu po pl base nF j kO kL dO dL : Word) (v : List Word) (kd nd ns2 : Word) (fv : Word) (m2 : Mem) :
    nbFieldsK2 k fieldsF vis ctx fu po pl base nF j kO kL dO dL v kd nd ns2 (some (fv, m2)) =
    if 4294967296 ≤ fv then none
    else nbFieldsK3 k fieldsF vis ctx fu po pl base nF j kO kL dO dL kd nd ns2
      (i1F m2 [CWF, v.tail.tail.headD 0, fv, 0]) := rfl
theorem nbFieldsK1_some (k : Nat) (fieldsF : MW14) (vis ctx fu po pl base nF j kO kL dO dL : Word) (v : List Word) (rp : List Word) (m1 : Mem) :
    nbFieldsK1 k fieldsF vis ctx fu po pl base nF j kO kL dO dL v (some (rp, m1)) = nbFieldsK2 k fieldsF vis ctx fu po pl base nF j kO kL dO dL v (rp.headD 0) (rp.tail.headD 0)
      (rp.tail.tail.headD 0) (fvinternW m1 (base + j) (v.tail.headD 0)) := rfl
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
attribute [ind_grind] nbBindK6_some nbBindK5_some nbBindK4_some nbBindK3_some nbBindK2_some nbBindK1_some
  nbPosK3_some nbPosK4_some nbPosK5_some nbPosK2_some nbPosK1_some nbAppK4_some nbAppK6_some nbAppK5_some
  nbAppK2_some nbAppK1_some nbContK4_some nbContK3_some nbContK2_some nbContK1_some nbKeyK2_some nbKeyK1_some
  nbNewK9_some nbNewK8_some nbNewK7_some nbNewK6_some nbNewK5_some nbNewK4_some nbNewK3_some nbNewK2_some
  nbNewK1_some nbFrameK8_some nbFrameK7_some nbFrameK6_some nbFrameK5_some nbFrameK4_some nbFrameK3_some
  nbFrameK2_some nbFrameK1_some nbCtorsK3_some nbCtorsK2_some nbCtorsK1_some nbOneK7_some nbOneK6_some
  nbOneK5_some nbOneK4_some nbOneK3_some nbOneK2_some nbOneK1_some nbWalkK3_some nbWalkK2_some nbWalkK1_some
  nbFieldsK5_some nbFieldsK4_some nbFieldsK3_some nbFieldsK2_some nbFieldsK1_some nbPosW_succ nbBindW_succ
  nbAppW_succ nbContW_succ nbKeyW_succ nbNewW_succ nbFrameW_succ nbCtorsW_succ nbOneW_succ nbWalkW_succ
  nbFieldsW_succ

attribute [irreducible] nbPosW nbBindW nbAppW nbContW nbKeyW nbNewW nbFrameW nbCtorsW nbOneW nbWalkW
  nbFieldsW

end L.Ind
