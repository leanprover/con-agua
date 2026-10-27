import ConAgua.Arena.RecCheckSpec.K53Look
import ConAgua.Arena.RecCheckSpec.TkhK5

/-!
# TkhK2

`tkhK4`, `tkhK3`, `tkhK2`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

def tkhK4 (cR : CallM) (n : Nat) (vis q fto ftl Mc ip usp ii : Word) (ra : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m) =>
    if ip ≠ ii then some ([0], m)
    else if ra.tail.headD 0 ≠ rb.tail.headD 0 then some ([0], m)
    else tkhK5 (tkaW cR n m vis q fto ftl Mc ip usp (ra.headD 0) (ra.tail.headD 0) (rb.headD 0) (rb.tail.headD 0))

def tkhK3 (cR : CallM) (n : Nat) (vis q fto ftl Mc majDom ip usp ii : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m) => tkhK4 cR n vis q fto ftl Mc ip usp ii ra (gaaF m [CWF, majDom])

def tkhK2 (cR : CallM) (n : Nat) (vis q fto ftl Mc leafW majDom lh : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rm, m) =>
    if lh >>> 28 ≠ 3 then some ([0], m)
    else if rm.headD 0 >>> 28 ≠ 3 then some ([0], m)
    else if eViewW m lh = [] then none
    else if eViewW m (rm.headD 0) = [] then none
    else tkhK3 cR n vis q fto ftl Mc majDom ((eViewW m lh).tail.headD 0) ((eViewW m lh).tail.tail.headD 0)
      ((eViewW m (rm.headD 0)).tail.headD 0) (gaaF m [CWF, leafW])

end L.Ind

end
