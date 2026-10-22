import ConAgua.Arena.IndPos2SpecM

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the word models of the
mutual block (`nest_pos`, `nest_pos_bind`, `nest_pos_app`, `nest_cont`, `nest_cont_key`,
`nest_cont_new`, `nest_frame`, `nest_ctors`, `nest_ctors_one`, `nest_ctors_walk`, `nest_fields`),
each at exec fuel `n + 1` over its callees at `n`. -/

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

/-- A model's type with `k` word arguments. -/
@[reducible] def WFn : Nat → Type
  | 0 => Option (List Word × Mem)
  | k + 1 => Word → WFn k

/-- A model's type: a memory and `k` words. -/
abbrev MW (k : Nat) := Mem → WFn k

def nbBindK6 (k ns2 : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (z, m6) => if 4294967296 ≤ z then none else some ([k, z, ns2], m6)
def nbBindK5 (a k ns2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m5) => nbBindK6 k ns2 (mkForallW m5 a (r.headD 0))
def nbBindK4 (dep a : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m4) => nbBindK5 a (r.headD 0) (r.tail.tail.headD 0)
      (stubM "abstract1_fast" m4 [CWF, r.tail.headD 0, dep, 0])
def nbBindK3 (posF : MW 9) (vis ctx fu po pl dep kb : Word) (v : List Word) (ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => nbBindK4 dep (v.tail.headD 0) (posF m3 vis ctx fu po pl (dep + 1) (kb + 1) (r.headD 0) ns)
def nbBindK2 (posF : MW 9) (vis ctx fu po pl dep kb : Word) (v : List Word) (ns : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (fv, m2) =>
    if 4294967296 ≤ fv then none
    else nbBindK3 posF vis ctx fu po pl dep kb v ns (stubM "instantiate1_fast" m2 [CWF, v.tail.tail.headD 0, fv, 0])
def nbBindK1 (posF : MW 9) (vis ctx fu po pl dep kb : Word) (v : List Word) (ns : Word) :
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
def nbPosK2 (n : Nat) (bindF appF : MW 9) (vis ctx fu po pl dep kb e ns hi w : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (o, m2) =>
    if o = 0 then nbPosK3 w e ns (noConstWf n m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1))
      (rdW (m2.arr64 IW) (ctx + 4)) hi e)
    else if w >>> 28 = 6 then nbPosK4 (bindF m2 vis ctx fu po pl dep kb w ns)
    else nbPosK5 w (appF m2 vis ctx fu po pl kb hi w ns)
def nbPosK1 (n : Nat) (bindF appF : MW 9) (vis ctx fu po pl dep kb e ns hi : Word) :
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
def nbAppK5 (contF : MW 11) (m2 : Mem) (vis ctx fu po pl kb ns aO aL : Word) (v : List Word) :
    Option Word → Option (List Word × Mem)
  | none => none
  | some o => if o ≠ 0 then none
    else nbAppK6 (contF m2 vis ctx fu po pl kb (v.tail.headD 0) (v.tail.tail.headD 0) aO aL ns)
def nbAppK2 (n : Nat) (contF : MW 11) (vis ctx fu po pl kb hi ns aO aL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rh, m2) =>
    if (eViewW m2 (rh.headD 0)).headD 0 = 1 then
      nbAppK4 ns (pfW n m2 vis ctx po pl kb hi ((eViewW m2 (rh.headD 0)).tail.headD 0) aO aL)
    else if (eViewW m2 (rh.headD 0)).headD 0 = 3 then
      nbAppK5 contF m2 vis ctx fu po pl kb ns aO aL (eViewW m2 (rh.headD 0))
        (containsW n m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) ((eViewW m2 (rh.headD 0)).tail.headD 0))
    else none
def nbAppK1 (n : Nat) (contF : MW 11) (vis ctx fu po pl kb hi w ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m1) => nbAppK2 n contF vis ctx fu po pl kb hi ns (ra.headD 0) (ra.tail.headD 0)
      (stubM "get_app_fn_f" m1 [CWF, w])

def nbContK4 (keyF : MW 13) (vis ctx fu po pl kb nn us aO aL ns nPc : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if aL ≠ nPc + r4.headD 0 then none
    else nbAppK6 (keyF m4 vis ctx fu po pl kb nn us aO nPc nPc (r4.tail.headD 0) ns)
def nbContK3 (k : Nat) (keyF : MW 13) (vis ctx fu po pl kb nn us aO aL ns nPc hp : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (key, m3) => nbContK4 keyF vis ctx fu po pl kb nn us aO aL ns nPc (nitWf k m3 vis ctx hp key)
def nbContK2 (k : Nat) (keyF : MW 13) (vis ctx fu po pl kb nn us aO aL ns nPc hp : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => nbContK3 k keyF vis ctx fu po pl kb nn us aO aL ns nPc hp (posRecW m2 [nn, us, aO, nPc])
def nbContK1 (k : Nat) (keyF : MW 13) (vis ctx fu po pl kb nn us aO aL ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then none
    else if aL < r.tail.headD 0 then none
    else nbContK2 k keyF vis ctx fu po pl kb nn us aO aL ns (r.tail.headD 0) (nhiW m1 ctx pl)
      (p2ccW k m1 ctx (nhiW m1 ctx pl) nn aO (r.tail.headD 0) (aO + r.tail.headD 0) (aL - r.tail.headD 0))

def nbKeyK2 (k : Nat) (newF : MW 13) (vis ctx fu po pl kb nn us dO dL nPc cty ns key : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) =>
    if r.headD 0 ≠ 0 then
      match nkcW k m2 (rdW (m2.arr64 IW) ns) (rdW (m2.arr64 IW) (ns + 1)) key with
      | none => none
      | some b => if b ≠ 0 then some ([nestedW kb, ns], m2)
        else nbAppK6 (newF m2 vis ctx fu po pl kb nn us dO dL nPc cty ns)
    else nbAppK6 (newF m2 vis ctx fu po pl kb nn us dO dL nPc cty ns)
def nbKeyK1 (k : Nat) (newF : MW 13) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word) :
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
def nbNewK8 (k : Nat) (frameF : MW 13) (vis ctx fu kb us dO dL nPc ns wO wL hw gO gL : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ns1, m8) => nbNewK9 k ctx kb us dO dL ns gO gL
      (frameF m8 vis ctx fu wO wL hw us dO dL nPc gO gL ns1)
def nbNewK7 (k : Nat) (frameF : MW 13) (vis ctx fu kb us dO dL nPc ns wO wL hw gO gL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m7) => nbNewK8 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL
      (posRecW m7 [rdW (m7.arr64 IW) ns, rdW (m7.arr64 IW) (ns + 1), ra.headD 0, ra.tail.headD 0,
        rdW (m7.arr64 IW) (ns + 4), rdW (m7.arr64 IW) (ns + 5)])
def nbNewK6 (k : Nat) (frameF : MW 13) (vis ctx fu kb us dO dL nPc ns wO wL hw gO gL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m6) => nbNewK7 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL
      (appendW k m6 (ra.headD 0) (ra.tail.headD 0) (rdW (m6.arr64 IW) (ns + 2)) (rdW (m6.arr64 IW) (ns + 3)))
def nbNewK5 (k : Nat) (frameF : MW 13) (vis ctx fu kb us dO dL nPc ns wO wL hw : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rg, m5) => nbNewK6 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw (rg.headD 0) (rg.tail.headD 0)
      (caW k m5 us dO dL (rg.headD 0) (rg.tail.headD 0) 0 0)
def nbNewK4 (k : Nat) (frameF : MW 13) (vis ctx fu kb us dO dL nPc ns wO wL mO mL hw : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (g0, m4) => nbNewK5 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw
      (ggW k m4 vis ctx hw us dO dL mO mL (g0.headD 0) (g0.tail.headD 0))
def nbNewK3 (k : Nat) (frameF : MW 13) (vis ctx fu kb us dO dL nPc ns wO wL mO mL hw : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (pr, m3) => nbNewK4 k frameF vis ctx fu kb us dO dL nPc ns wO wL mO mL hw (new1W m3 pr)
def nbNewK2 (k : Nat) (frameF : MW 13) (vis ctx fu kb nn us dO dL nPc cty ns wO wL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rm, m2) => nbNewK3 k frameF vis ctx fu kb us dO dL nPc ns wO wL (rm.headD 0) (rm.tail.headD 0)
      (nhiW m2 ctx wL) (posRecW m2 [nn, cty])
def nbNewK1 (k : Nat) (frameF : MW 13) (vis ctx fu kb nn us dO dL nPc cty ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rw, m1) => nbNewK2 k frameF vis ctx fu kb nn us dO dL nPc cty ns (rw.headD 0) (rw.tail.headD 0)
      (nfmW k m1 vis nn)

def nbFrameK8 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m8) => some ([r.tail.tail.headD 0], m8)
def nbFrameK7 (ctorsF : MW 19) (vis ctx fu hi us dO dL gL ns p2O p2L nO nL cO cL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rh, m7) =>
    if hi + gL < hi then none
    else nbFrameK8 (ctorsF m7 vis ctx 0 fu p2O p2L (hi + gL) us dO dL nO nL (rh.headD 0) (rh.tail.headD 0)
      cO cL ns 0 0)
def nbFrameK6 (k : Nat) (ctorsF : MW 19) (vis ctx fu hi us dO dL gO gL ns p2O p2L nO nL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m6) => nbFrameK7 ctorsF vis ctx fu hi us dO dL gL ns p2O p2L nO nL (rc.headD 0) (rc.tail.headD 0)
      (fhW k m6 hi gO gL 0 0)
def nbFrameK5 (k : Nat) (ctorsF : MW 19) (vis ctx fu hi us dO dL nPc gO gL ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rp, m5) => nbFrameK6 k ctorsF vis ctx fu hi us dO dL gO gL ns (rp.headD 0) (rp.tail.headD 0)
      (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0)
      (gcW k m5 vis nPc (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0) 0 0)
def nbFrameK4 (k : Nat) (ctorsF : MW 19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m4) => nbFrameK5 k ctorsF vis ctx fu hi us dO dL nPc gO gL ns
      (fgW k m4 hi us dO dL gO gL po pl 0 0)
def nbFrameK3 (k : Nat) (ctorsF : MW 19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m3) => nbFrameK4 k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns
      (stubM "infer_type_core" m3 [vis, hi, ra.headD 0])
def nbFrameK2 (k : Nat) (ctorsF : MW 19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hc, m2) =>
    if 4294967296 ≤ hc then none
    else nbFrameK3 k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (stubM "mk_app_n_f" m2 [hc, dO, dL])
def nbFrameK1 (k : Nat) (ctorsF : MW 19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rn, m1) =>
    if 4294967296 ≤ rn.headD 0 then none
    else nbFrameK2 k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (ceinternW m1 (rn.headD 0) us)

def nbCtorsK3 (ctorsF : MW 19) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => ctorsF m3 vis ctx root fu po pl hi us dO dL no nl hO hL (cO + 1) (cL - 1) ns2
      (r.headD 0) (r.tail.headD 0)
def nbCtorsK2 (k : Nat) (ctorsF : MW 19) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL ns2 : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rec, m2) => nbCtorsK3 ctorsF vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns2 (snocW k m2 oO oL rec)
def nbCtorsK1 (k : Nat) (ctorsF : MW 19) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL : Word) :
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
def nbOneK1 (k : Nat) (walkF : MW 10) (vis ctx root fu po pl hi us dO dL cv nF ns : Word) :
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
def nbWalkK1 (k : Nat) (fieldsF : MW 14) (vis ctx po pl hi nF crest ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m1) => nbWalkK2 k hi (fieldsF m1 vis ctx (rf.headD 0) po pl hi nF 0 crest ns 0 0 0 0)

def nbFieldsK5 (fieldsF : MW 14) (vis ctx fu po pl base nF j ns2 b kO kL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rd, m5) => fieldsF m5 vis ctx fu po pl base (nF - 1) (j + 1) b ns2 kO kL (rd.headD 0) (rd.tail.headD 0)
def nbFieldsK4 (k : Nat) (fieldsF : MW 14) (vis ctx fu po pl base nF j dO dL nd ns2 b : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rk, m4) => nbFieldsK5 fieldsF vis ctx fu po pl base nF j ns2 b (rk.headD 0) (rk.tail.headD 0)
      (snocW k m4 dO dL nd)
def nbFieldsK3 (k : Nat) (fieldsF : MW 14) (vis ctx fu po pl base nF j kO kL dO dL kd nd ns2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m3) => nbFieldsK4 k fieldsF vis ctx fu po pl base nF j dO dL nd ns2 (rb.headD 0) (snocW k m3 kO kL kd)
def nbFieldsK2 (k : Nat) (fieldsF : MW 14) (vis ctx fu po pl base nF j kO kL dO dL : Word) (v : List Word)
    (kd nd ns2 : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (fv, m2) =>
    if 4294967296 ≤ fv then none
    else nbFieldsK3 k fieldsF vis ctx fu po pl base nF j kO kL dO dL kd nd ns2
      (stubM "instantiate1_fast" m2 [CWF, v.tail.tail.headD 0, fv, 0])
def nbFieldsK1 (k : Nat) (fieldsF : MW 14) (vis ctx fu po pl base nF j kO kL dO dL : Word) (v : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rp, m1) => nbFieldsK2 k fieldsF vis ctx fu po pl base nF j kO kL dO dL v (rp.headD 0) (rp.tail.headD 0)
      (rp.tail.tail.headD 0) (fvinternW m1 (base + j) (v.tail.headD 0))

mutual
/-- `nest_pos(vis, ctx, fuel, progOff, progLen, dep, kb, e, ns)`. -/
def nbPosW : Nat → MW 9
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, ctx, fu, po, pl, dep, kb, e, ns =>
    if fu = 0 then none
    else nbPosK1 n (nbBindW n) (nbAppW n) vis ctx (fu - 1) po pl dep kb e ns (nhiW m ctx pl)
      (stubM "whnf_top" m [vis, dep, e])
/-- `nest_pos_bind(vis, ctx, fuel, progOff, progLen, dep, kb, w, ns)`. -/
def nbBindW : Nat → MW 9
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, ctx, fu, po, pl, dep, kb, w, ns =>
    nbBindK1 (nbPosW n) vis ctx fu po pl dep kb (eViewW m w) ns
      (noConstWf n m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx pl) ((eViewW m w).tail.headD 0))
/-- `nest_pos_app(vis, ctx, fuel, progOff, progLen, kb, hi, w, ns)`. -/
def nbAppW : Nat → MW 9
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, ctx, fu, po, pl, kb, hi, w, ns =>
    nbAppK1 n (nbContW n) vis ctx fu po pl kb hi w ns (stubM "get_app_args_f" m [CWF, w])
/-- `nest_cont(vis, ctx, fuel, progOff, progLen, kb, n, us, argsOff, argsLen, ns)`. -/
def nbContW : Nat → MW 11
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, fu, po, pl, kb, nn, us, aO, aL, ns =>
    nbContK1 k (nbKeyW k) vis ctx fu po pl kb nn us aO aL ns (ntWf k m vis nn)
/-- `nest_cont_key(vis, ctx, fuel, progOff, progLen, kb, n, us, dsOff, dsLen, nPc, cty, ns)`. -/
def nbKeyW : Nat → MW 13
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns =>
    nbKeyK1 k (nbNewW k) vis ctx fu po pl kb nn us dO dL nPc cty ns (posRecW m [nn, us, dO, dL])
/-- `nest_cont_new(vis, ctx, fuel, progOff, progLen, kb, n, us, dsOff, dsLen, nPc, cty, ns)`. -/
def nbNewW : Nat → MW 13
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns =>
    nbNewK1 k (nbFrameW k) vis ctx fu kb nn us dO dL nPc cty ns (nwsWf k m ctx dO dL po pl)
/-- `nest_frame(vis, ctx, fuel, progOff, progLen, hi, us, dsOff, dsLen, nPc, grpOff, grpLen, ns)`. -/
def nbFrameW : Nat → MW 13
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, fu, po, pl, hi, us, dO, dL, nPc, gO, gL, ns =>
    nbFrameK1 k (nbCtorsW k) vis ctx fu po pl hi us dO dL nPc gO gL ns
      (if gL = 0 then stubM "intern_nanon" m [] else some ([rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m))
/-- `nest_ctors(vis, ctx, root, fuel, progOff, progLen, hi, us, dsOff, dsLen, namesOff, namesLen,
holesOff, holesLen, csOff, csLen, ns, outsOff, outsLen)`. -/
def nbCtorsW : Nat → MW 19
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cO, cL, ns, oO, oL =>
    if cL = 0 then some ([oO, oL, ns], m)
    else nbCtorsK1 k (nbCtorsW k) vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL
      (nbOneW k m vis ctx root fu po pl hi us dO dL no nl hO hL (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1)) ns)
/-- `nest_ctors_one(vis, ctx, root, fuel, progOff, progLen, hi, us, dsOff, dsLen, namesOff,
namesLen, holesOff, holesLen, cv, nF, ns)`. -/
def nbOneW : Nat → MW 17
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cv, nF, ns =>
    nbOneK1 k (nbWalkW k) vis ctx root fu po pl hi us dO dL cv nF ns (p2ctW k m vis no nl us dO dL hO hL cv hi)
/-- `nest_ctors_walk(vis, ctx, root, fuel, progOff, progLen, hi, nF, crest, ns)`. -/
def nbWalkW : Nat → MW 10
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, root, fu, po, pl, hi, nF, crest, ns =>
    if root ≠ 0 then nbWalkK1 k (nbFieldsW k) vis ctx po pl hi nF crest ns (wfWf k m crest)
    else nbWalkK2 k hi (nbFieldsW k m vis ctx fu po pl hi nF 0 crest ns 0 0 0 0)
/-- `nest_fields(vis, ctx, fuel, progOff, progLen, base, nF, j, cur, ns, ksOff, ksLen, ndsOff,
ndsLen)`. -/
def nbFieldsW : Nat → MW 14
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, fu, po, pl, base, nF, j, cur, ns, kO, kL, dO, dL =>
    if nF = 0 then some ([kO, kL, dO, dL, cur, ns], m)
    else if cur >>> 28 ≠ 6 then none
    else if base + j < base then none
    else if base + j + 1 = 0 then none
    else nbFieldsK1 k (nbFieldsW k) vis ctx fu po pl base nF j kO kL dO dL (eViewW m cur)
      (nbPosW k m vis ctx fu po pl (base + j) 0 ((eViewW m cur).tail.headD 0) ns)
end

end L.Ind
