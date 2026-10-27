import ConAgua.Arena.RecCheckSpec.EeW
import ConAgua.Arena.RecCheckSpec.TcmF

/-!
# K53Look

`K53Look`, `tkaK7`, `tkaK6`, `tkaK5`, `tkaK4`, `tkaK3` and the lemmas only they use.
-/

noncomputable section

/-!
# `RecCheck`: `targetK53`, the L side (lane `indproofs3`, helper `rec`)

K.53′ at one recorded field: `strip_pis` (stub), the telescope check (`target_k53_tele`: both sides
erased by `erase_each`, compared by `sl_eq`), the head check (`target_k53_heads`: `get_app_fn_f`,
`get_app_args_f` stubs, `e_view`), the argument check (`target_k53_args`: erased indices, the
leaf's class `intern_const` + `mk_app_n_f` (stub) + `nest_occ`, then `target_class_match`).
L: `erase_each` is the twin's `mapM` as a self-recursion consing each result (`sl_cons`, D18); a
handle guard after `intern_const` (`mk_app_n_f`'s contract takes a handle).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `target_k53`. -/
structure K53Look (p : Prog) : Prop where
  tmn : TmnLook p
  hv : p.lookup "e_view" = some eView
  ad : AdF p
  sc : p.lookup "sl_contains" = some slContains
  nf : p.lookup "no_find" = some (memoFindG noSch)
  np : p.lookup "no_put" = some (memoPutG noSch)
  ngo : p.lookup "nest_occ_go" = some nestOccGo
  nnode : p.lookup "nest_occ_node" = some nestOccNode
  ncl : p.lookup "no_clear" = some (memoClearG noSch)
  no : p.lookup "nest_occ" = some nestOcc
  cf : p.lookup "const_find" = some constFind
  cp : p.lookup "const_push" = some constPush
  ic : p.lookup "intern_const" = some internConst
  eq : p.lookup "sl_eq" = some slEq
  ee : p.lookup "erase_each" = some eraseEach
  tte : p.lookup "target_k53_tele" = some targetK53Tele
  tkh : p.lookup "target_k53_heads" = some targetK53Heads
  tka : p.lookup "target_k53_args" = some targetK53Args
  tk : p.lookup "target_k53" = some targetK53
  strip : StripProg p

def tkaK7 (cR : CallM) (n : Nat) (vis q fto ftl Mc usp lao lpl : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (occ, m) =>
    if occ = 0 then some ([0], m)
    else tkaK8 (tcmF cR n m vis q fto ftl (rdW (m.arr64 IW) (Mc + 11)) (rdW (m.arr64 IW) (Mc + 12))
      (rdW (m.arr64 IW) (Mc + 1)) (rdW (m.arr64 IW) (Mc + 2)) (rdW (m.arr64 IW) (Mc + 3)) usp lao lpl)

def tkaK6 (cR : CallM) (n : Nat) (vis q fto ftl Mc usp lao lpl app : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rn, m) => tkaK7 cR n vis q fto ftl Mc usp lao lpl (noF n m (rn.headD 0) (rn.tail.headD 0) 0 0 app)

def tkaK5 (cR : CallM) (n : Nat) (vis q fto ftl Mc usp lao lpl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m) => tkaK6 cR n vis q fto ftl Mc usp lao lpl (ra.headD 0) (memberNamesW n m q)

def tkaK4 (cR : CallM) (vis q fto ftl Mc usp lao lpl : Word) (n : Nat) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hd, m) =>
    if 4294967296 ≤ hd then none
    else tkaK5 cR n vis q fto ftl Mc usp lao lpl (mknF m [hd, lao, lpl])

def tkaK3 (cR : CallM) (n : Nat) (vis q fto ftl Mc ip usp lao lal K : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some e =>
    if e = 0 then some ([0], m)
    else tkaK4 cR vis q fto ftl Mc usp lao (if lal < K then lal else K) n (ceinternW m ip usp)

def tkaK2 (cR : CallM) (n : Nat) (vis q fto ftl Mc ip usp lao lal K : Word) (r1 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m) => tkaK3 cR n vis q fto ftl Mc ip usp lao lal K m
      (eqW n m (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0))

def tkaK1 (cR : CallM) (n : Nat) (vis q fto ftl Mc ip usp lao lal mao mal K : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => tkaK2 cR n vis q fto ftl Mc ip usp lao lal K r1
      (eeW n m (if mal < K then mao else mao + K) (if mal < K then 0 else mal - K))

/-- **The model of `target_k53_args`** (exec fuel; `K` the class's parameter count, read once). -/
def tkaW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, q, fto, ftl, Mc, ip, usp, lao, lal, mao, mal =>
    tkaK1 cR n vis q fto ftl Mc ip usp lao lal mao mal (rdW (m.arr64 IW) (Mc + 4))
      (eeW n m (if lal < rdW (m.arr64 IW) (Mc + 4) then lao else lao + rdW (m.arr64 IW) (Mc + 4))
        (if lal < rdW (m.arr64 IW) (Mc + 4) then 0 else lal - rdW (m.arr64 IW) (Mc + 4)))

end L.Ind

end
end
