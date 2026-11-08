module

import ConAgua.Arena.WhnfIotaRecRefine
import ConRon.Bridge.Grind
public import ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# Where a firing rule's names and levels read back (lane `defeq2`)

`rec_fire_levels` (`RecFireLevelsOK`) reads the recursor's level parameters, the constructor's
(a plain rule) or the rule's stored levels (a nested one) back. The ι block knows where they come
from (`FireEnv`: a recursor and a constructor of the environment, state-free), so at the call the
readbacks follow from `StoreDen` (`constLps`, `recRules`): `lpsDen_of`, `fireCore_of`.
-/

open ConRon.Arena

namespace L.Arena

/-- A constructor record's `ConstantVal`. -/
theorem decCI_ctorInfo_cv {b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {cvj : IConstantVal} {np nf : Nat} (h : decCI (aread b) q = some (.ctorInfo cvj np nf)) :
    decCV (aread b) (q + 1) = some cvj := by
  sorry

/-- **A rule record's fire datum at its words**: kind `0` plain, else nested with its levels the
slice at words 4, 5. -/
theorem decRule_fireE {b : Array Word} {q : Word} {rl : IRecRule} (hsz : b.size < 2 ^ 63)
    (h : decRule (aread b) q.toNat = some rl) :
    (rdW b (q + 3) = 0 ∧ rl.fire = .plain) ∨
    (rdW b (q + 3) ≠ 0 ∧ ∃ lvls pins, rl.fire = .nested lvls pins ∧
      hslice? (aread b) (rdW b (q + 4)).toNat (rdW b (q + 5)).toNat = some lvls) := by
  sorry
variable {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word} {fe : IFEnv}
  {M : ModeMaps} {eb : Word}

/-- The recursor's level parameters read back. -/
theorem lpsDen_of (hS : CoreS dn m a vis fe M eb) {lps : List NIdx} {rule : IRecRule}
    {cvj : IConstantVal} (hfe : FireEnv fe lps rule cvj) :
    ∃ ks, lps.mapM (denoteN a.store.ns) = some ks := by
  sorry

/-- **The fire datum at the rule's and the constructor's words reads back.** -/
theorem fireCore_of (hS : CoreS dn m a vis fe M eb) {lps : List NIdx} {rule : IRecRule}
    {cvj : IConstantVal} {np nf : Nat} {rl ctorP : Word}
    (hrule : decRule (erecP m) rl.toNat = some rule)
    (hci : decCI (erecP m) ctorP.toNat = some (.ctorInfo cvj np nf))
    (hfe : FireEnv fe lps rule cvj) :
    FireCore m a (rdW (m.arr64 EREC) (rl + 3)) (rdW (m.arr64 EREC) (rl + 4))
      (rdW (m.arr64 EREC) (rl + 5)) (rdW (m.arr64 EREC) (ctorP + 2))
      (rdW (m.arr64 EREC) (ctorP + 3)) rule cvj.levelParams := by
  sorry

end L.Arena
