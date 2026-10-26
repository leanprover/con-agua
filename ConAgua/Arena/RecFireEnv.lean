import ConAgua.Arena.WhnfIotaRecRefine

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
    {cvj : IConstantVal} {np nf : Nat} (h : decCI b dn q = some (.ctorInfo cvj np nf)) :
    decCV b (q + 1) = some cvj := by
  cases hq : b[q]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
  all_goals (rw [hk] at h; simp [Option.bind_eq_some_iff] at h)
  obtain ⟨cv, hcv, _, _, _, _, rfl, rfl, rfl⟩ := h
  exact hcv

/-- **A rule record's fire datum at its words**: kind `0` plain, else nested with its levels the
slice at words 4, 5. -/
theorem decRule_fireE {b : Array Word} {q : Word} {rl : IRecRule} (hsz : b.size < 2 ^ 63)
    (h : decRule b q.toNat = some rl) :
    (rdW b (q + 3) = 0 ∧ rl.fire = .plain) ∨
    (rdW b (q + 3) ≠ 0 ∧ ∃ lvls pins, rl.fire = .nested lvls pins ∧
      hslice? b (rdW b (q + 4)).toNat (rdW b (q + 5)).toNat = some lvls) := by
  simp only [decRule, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨kd, hkd, h⟩ := h
  simp only [nat?, Option.map_eq_some_iff] at hkd
  obtain ⟨w3, hw3, rfl⟩ := hkd
  have e3 : rdW b (q + 3) = w3 := irRdW hsz 3 rfl hw3
  rcases hk : w3.toNat with _ | _ | k
  · rw [hk] at h
    simp only [Option.bind_some] at h
    exact .inl ⟨by rw [e3]; exact UInt64.toNat_inj.mp (by rw [hk]; rfl), (decRule_tail h).1⟩
  · rw [hk] at h
    cases hlv : hlist? (k := .level) b (q.toNat + 4) with
    | none => rw [hlv] at h; simp at h
    | some lv =>
    cases hp : hlist? (k := .expr) b (q.toNat + 6) with
    | none => rw [hlv, hp] at h; simp at h
    | some pins =>
    rw [hlv, hp] at h
    simp only [Option.bind_some] at h
    refine .inr ⟨by rw [e3]; intro h0; rw [h0] at hk; simp at hk, lv, pins, (decRule_tail h).1, ?_⟩
    simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hlv
    obtain ⟨o, ⟨w4, hw4, rfl⟩, c, ⟨w5, hw5, rfl⟩, hs⟩ := hlv
    rw [irRdW hsz 4 rfl hw4, irRdW hsz 5 rfl (by rw [← hw5]; congr 1)]
    exact hs
  · rw [hk] at h
    simp at h

section
variable {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word} {fe : IFEnv}
  {M : ModeMaps} {eb : Word}

/-- The recursor's level parameters read back. -/
theorem lpsDen_of (hS : CoreS dn m a vis fe M eb) {lps : List NIdx} {rule : IRecRule}
    {cvj : IConstantVal} (hfe : FireEnv fe lps rule cvj) :
    ∃ ks, lps.mapM (denoteN a.store.ns) = some ks := by
  obtain ⟨⟨c, cv, mI, rP, rules, hf, rfl, -⟩, -⟩ := hfe
  exact hS.den.constLps c _ hf

/-- **The fire datum at the rule's and the constructor's words reads back.** -/
theorem fireCore_of (hS : CoreS dn m a vis fe M eb) {lps : List NIdx} {rule : IRecRule}
    {cvj : IConstantVal} {np nf : Nat} {rl ctorP : Word}
    (hrule : decRule (m.arr64 EREC) rl.toNat = some rule)
    (hci : decCI (m.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj np nf))
    (hfe : FireEnv fe lps rule cvj) :
    FireCore m a (rdW (m.arr64 EREC) (rl + 3)) (rdW (m.arr64 EREC) (rl + 4))
      (rdW (m.arr64 EREC) (rl + 5)) (rdW (m.arr64 EREC) (ctorP + 2))
      (rdW (m.arr64 EREC) (ctorP + 3)) rule cvj.levelParams := by
  obtain ⟨⟨c, cv, mI, rP, rules, hf, -, hmem⟩, ⟨cj, np', nf', hfj⟩⟩ := hfe
  rcases decRule_fireE hS.erec hrule with ⟨h0, hpl⟩ | ⟨h0, lvls, pins, hn, hsl⟩
  · obtain ⟨-, -, hlp, -⟩ := decCV_rd1 hS.erec (decCI_ctorInfo_cv hci)
    exact .inl ⟨h0, hpl, hlp, hS.den.constLps cj _ hfj⟩
  · exact .inr ⟨h0, lvls, pins, hn, hsl, hS.den.recRules c cv mI rP rules hf rule hmem lvls pins hn⟩

end

end L.Arena
