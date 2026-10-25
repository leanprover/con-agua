import ConAgua.Arena.PromoteProg

/-!
# Tests of the promotion in the L interpreter

Terms are built in the scratch tier (`CTL[1] = 1`), promoted, and compared with the same terms
built afterwards in the persistent tier (`CTL[1] = 0`): hash-consing makes equal terms equal
handles. The whole program: the promotion, the stores, `mk_*`, `e_view`, `lv_node`, `ls_node`,
`erec_alloc`, the environment.
-/

open ConRon.Arena

namespace L.Arena

/-- A memory with 150 word arrays of 256 zeros (the pool holds `"ab"` at 0, top 2), `CTL` 256
words, the scratch flag `sc`. -/
def promoteMem (sc : Word) : Mem :=
  { words := withTiers <| ((Array.replicate 150 (Array.replicate 256 0)).set! 1
      (((Array.replicate 256 0).set! 1 sc).set! 0 2)).set! 0
      (((Array.replicate 256 0).set! 0 97).set! 1 98) }

/-- Run `f`; the first result and the memory. -/
def pRun (f : FnName) (args : List Word) (m : Mem) : Option (Word × Mem) :=
  match run promoteProg 10000 f args m with
  | .ok (r, m') => some (r.headD 0, m')
  | .error _ => none

/-- Set the scratch flag. -/
def setSc (m : Mem) (sc : Word) : Mem := m.set64 CTL 1 sc

/-- A builder: the term `app (const `a` [succ zero]) (lam (sort (max zero (param `b`))) (bvar 0))`
with the name `a` the string slice `(0, 1)`, `b` the number `7` under `a`. -/
def buildT (m : Mem) : Option (Word × Mem) := do
  let (an, m) ← pRun "intern_nanon" [] m
  let (a, m) ← pRun "intern_nstr" [an, 0, 1] m
  let (b, m) ← pRun "intern_nnum" [a, 7] m
  let (z, m) ← pRun "intern_zero" [] m
  let (s, m) ← pRun "intern_succ" [z] m
  let (pb, m) ← pRun "intern_param" [b] m
  let (mx, m) ← pRun "intern_max" [z, pb] m
  let top := rdW (m.arr64 CTL) 0
  let m := (m.set64 POOL top s).set64 CTL 0 (top + 1)
  let (us, m) ← pRun "intern_ls" [top, 1] m
  let (c, m) ← pRun "intern_const" [a, us] m
  let (so, m) ← pRun "intern_sort" [mx] m
  let (v, m) ← pRun "intern_bvar" [0] m
  let (l, m) ← pRun "mk_lam" [so, v] m
  pRun "mk_app" [c, l] m

/- Built in the scratch tier the term is a scratch handle; promoted it is a persistent handle,
the same one the persistent build gives; promoting again hits the memo. -/
#guard
  match buildT (promoteMem 1) with
  | none => false
  | some (t, m) =>
    (t >>> 27) &&& 1 == 1 &&
    match pRun "promote_e" [L.Ind.CWF, t] m with
    | none => false
    | some (r, m) =>
      (r >>> 27) &&& 1 == 0 &&
      (match pRun "promote_e" [L.Ind.CWF, t] m with
       | some (r', _) => r' == r | none => false) &&
      (match buildT (setSc m 0) with
       | some (e, _) => e == r | none => false)

end L.Arena
