module

import ConAgua.Arena.RecLayout.RuleDec
import ConRon.Bridge.Grind
public import ConAgua.Arena.WhnfIota
import ConAgua.Arena.RecLayout.CIDec

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

variable {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word} {fe : IFEnv}
  {M : ModeMaps} {eb : Word}

/-- The recursor's level parameters read back. -/
theorem lpsDen_of (hS : CoreS dn m a vis fe M eb) {lps : List NIdx} {rule : IRecRule}
    {cvj : IConstantVal} (hfe : FireEnv fe lps rule cvj) :
    ∃ ks, lps.mapM (denoteN a.store.ns) = some ks := by
  obtain ⟨⟨c, cv, mI, rP, isK, rules, hf, rfl, -⟩, -⟩ := hfe
  exact hS.den.constLps c _ hf

/-- **The fire datum at the rule's and the constructor's words reads back.** -/
theorem fireCore_of (hS : CoreS dn m a vis fe M eb) {lps : List NIdx} {rule : IRecRule}
    {cvj : IConstantVal} {np nf : Nat} {rl ctorP : Word}
    (hrule : decRule (erecP m) rl.toNat = some rule)
    {fam : NIdx} (hci : decCI (erecP m) ctorP.toNat = some (.ctorInfo cvj np nf fam))
    (hfe : FireEnv fe lps rule cvj) :
    FireCore m a (erRd m (rl + Rule.fire)) (erRd m (rl + Rule.lvlsOff)) (erRd m (rl + Rule.lvlsLen))
      (erRd m (ctorP + (CI.cv + CV.lpsOff))) (erRd m (ctorP + (CI.cv + CV.lpsLen))) rule cvj.levelParams := by
  obtain ⟨⟨c, cv, mI, rP, isK, rules, hf, -, hmem⟩, ⟨cj, np', nf', fam', hfj⟩⟩ := hfe
  rcases decRule_fireE (erRdOK m) hrule with ⟨h0, hpl⟩ | ⟨h0, lvls, hk, hsl⟩
  · obtain ⟨-, -, hlp, -⟩ := decCV_rd_ci (erRdOK m) (decCI_ctorInfo_iff.mp hci).2.1
    exact .inl ⟨h0, hpl, hlp, hS.den.constLps cj _ hfj⟩
  · refine .inr ⟨h0, lvls, hk, hsl, ?_⟩
    rcases hk with hk | ⟨pins, hn⟩
    · exact hS.den.recLevels c cv mI rP isK rules hf rule hmem lvls hk
    · exact hS.den.recRules c cv mI rP isK rules hf rule hmem lvls pins hn

end L.Arena
