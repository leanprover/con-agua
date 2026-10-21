import ConAgua.Arena.WhnfCoreRefine
open L L.Arena ConRon.Arena
namespace L.Arena
theorem hd?_eq {k : IdxKind} {a : Array Word} {i : Nat} {x : Idx k} (h : hd? a i = some x) :
    ∃ w, a[i]? = some w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  cases e : a[i]? with
  | none => simp [hd?, e] at h
  | some w => simp [hd?, e] at h; exact ⟨w, rfl, h.1, h.2.symm⟩

theorem decCV_type {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    ∃ w, a[q + 3]? = some w ∧ w.toNat < 2 ^ 32 ∧ cv.type = decI w := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨n, -, ls, -, ty, ht, hc⟩ := h
  cases hc
  obtain ⟨w, hw, hl, rfl⟩ := hd?_eq ht
  exact ⟨w, hw, hl, rfl⟩

theorem decCI_ctor' {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI a dn q.toNat = some ci) (hsz : a.size < 2 ^ 63) :
    (rdW a q = 4 → ∃ cv np nf, ci = .ctorInfo cv np nf ∧ cv.type = decI (rdW a (q + 4)) ∧
      (rdW a (q + 4)).toNat < 2 ^ 32) ∧
    (rdW a q ≠ 4 → ∀ cv np nf, ci ≠ .ctorInfo cv np nf) := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  have hlt : q.toNat < a.size := by
    rcases Nat.lt_or_ge q.toNat a.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at hq
  have h4 : (q + 4).toNat = q.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have hrd : rdW a q = w := by simp [rdW, hq]
  rw [hrd]
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  constructor
  · intro hw; subst hw
    simp only [show UInt64.toNat 4 = 4 from rfl, Option.bind_eq_some_iff] at h
    obtain ⟨cv, hcv, np, -, nf, -, hc⟩ := h
    cases hc
    obtain ⟨tw, htw, htl, hty⟩ := decCV_type hcv
    have hrd4 : rdW a (q + 4) = tw := by
      simp only [rdW, h4]; rw [show q.toNat + 4 = q.toNat + 1 + 3 by omega, htw]; rfl
    exact ⟨cv, _, _, rfl, by rw [hrd4]; exact hty, by rw [hrd4]; exact htl⟩
  · intro hw cv np nf hc
    subst hc
    have hne : w.toNat ≠ 4 := fun e => hw (UInt64.toNat_inj.mp (by rw [e]; rfl))
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h hne; simp [Option.bind_eq_some_iff] at h hne)
end L.Arena
