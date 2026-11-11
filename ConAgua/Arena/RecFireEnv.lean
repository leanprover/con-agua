module

import ConAgua.Arena.WhnfIotaRecRefine
import ConRon.Bridge.Grind
public import ConAgua.Arena.WhnfIota
import ConAgua.Arena.EtaRescueRef

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

/-- **A rule record's fire datum at its words**: kind `0` plain, `1` nested with its levels the
slice at words 4, 5 (and its pins at 6, 7), `2` levels. -/
theorem decRule_fireE {R : Nat → Option Word} {rd : Word → Word} {q : Word} {rl : IRecRule}
    (hR : RdOK R rd) (h : decRule R q.toNat = some rl) :
    (rd (q + 3) = 0 ∧ rl.fire = .plain) ∨
    (rd (q + 3) ≠ 0 ∧ ∃ lvls, (rl.fire = .levels lvls ∨ ∃ pins, rl.fire = .nested lvls pins) ∧
      hslice? R (rd (q + 4)).toNat (rd (q + 5)).toNat = some lvls) := by
  simp only [decRule, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨kd, hkd, h⟩ := h
  simp only [nat?, Option.map_eq_some_iff] at hkd
  obtain ⟨w3, hw3, rfl⟩ := hkd
  have e3 : rd (q + 3) = w3 := hR.at 3 rfl hw3
  rcases hk : w3.toNat with _ | _ | _ | k
  · rw [hk] at h
    simp only [Option.bind_some] at h
    exact .inl ⟨by rw [e3]; exact UInt64.toNat_inj.mp (by rw [hk]; rfl), (decRule_tail h).1⟩
  · rw [hk] at h
    cases hlv : hlist? (k := .level) R (q.toNat + 4) with
    | none => rw [hlv] at h; simp at h
    | some lv =>
    cases hp : hlist? (k := .expr) R (q.toNat + 6) with
    | none => rw [hlv, hp] at h; simp at h
    | some pins =>
    rw [hlv, hp] at h
    simp only [Option.bind_some] at h
    refine .inr ⟨by rw [e3]; intro h0; rw [h0] at hk; simp at hk, lv,
      .inr ⟨pins, (decRule_tail h).1⟩, ?_⟩
    simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hlv
    obtain ⟨o, ⟨w4, hw4, rfl⟩, c, ⟨w5, hw5, rfl⟩, hs⟩ := hlv
    rw [hR.at 4 rfl hw4, hR.at 5 rfl (by rw [← hw5]; congr 1)]
    exact hs
  · rw [hk] at h
    cases hlv : hlist? (k := .level) R (q.toNat + 4) with
    | none => rw [hlv] at h; simp at h
    | some lv =>
    rw [hlv] at h
    simp only [Option.bind_some] at h
    refine .inr ⟨by rw [e3]; intro h0; rw [h0] at hk; simp at hk, lv, .inl (decRule_tail h).1, ?_⟩
    simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hlv
    obtain ⟨o, ⟨w4, hw4, rfl⟩, c, ⟨w5, hw5, rfl⟩, hs⟩ := hlv
    rw [hR.at 4 rfl hw4, hR.at 5 rfl (by rw [← hw5]; congr 1)]
    exact hs
  · rw [hk] at h
    simp at h

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
    (hci : decCI (erecP m) ctorP.toNat = some (.ctorInfo cvj np nf))
    (hfe : FireEnv fe lps rule cvj) :
    FireCore m a (erRd m (rl + 3)) (erRd m (rl + 4)) (erRd m (rl + 5)) (erRd m (ctorP + 2))
      (erRd m (ctorP + 3)) rule cvj.levelParams := by
  obtain ⟨⟨c, cv, mI, rP, isK, rules, hf, -, hmem⟩, ⟨cj, np', nf', hfj⟩⟩ := hfe
  rcases decRule_fireE (erRdOK m) hrule with ⟨h0, hpl⟩ | ⟨h0, lvls, hk, hsl⟩
  · obtain ⟨-, -, hlp, -⟩ := decCV_rd1 (erRdOK m) (L.Arena.decCI_ctor_cv hci)
    exact .inl ⟨h0, hpl, hlp, hS.den.constLps cj _ hfj⟩
  · refine .inr ⟨h0, lvls, hk, hsl, ?_⟩
    rcases hk with hk | ⟨pins, hn⟩
    · exact hS.den.recLevels c cv mI rP isK rules hf rule hmem lvls hk
    · exact hS.den.recRules c cv mI rP isK rules hf rule hmem lvls pins hn

end L.Arena
