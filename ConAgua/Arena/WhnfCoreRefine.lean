import ConAgua.Arena.WhnfCoreSlot

/-!
# Refinements of `WhnfCore.lean`'s functions (other than the slot and the loop)

The callW pattern of `WhnfCoreSlot.lean`, one function at a time.

* Environment reads: `env_find`'s flag `≠ 0` means the name has a row (`envFind_found`), and every
  row decodes (`EnvR.found_some`): the L code may read the record's words where the twin matches
  on the decoded constant (`decCI_ctor`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `env_find`: a found row is a row -/

theorem envFind_found (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hp : p.lookup "env_find" = some envFindL)
    (n : Nat) (s₀ : St) (vis w : Word) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_find" [w, vis]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      (r.headD 0 ≠ 0 → rowTag w ≤ 2 ∧ rowC s₀.mem w ≠ 0 ∧ r.tail.headD 0 = rowP s₀.mem w); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, envFindL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, envRowGet_spec p hx hg n] <;>
      finish

/-- **Every row of the index decodes.** -/
theorem EnvR.found_some {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : rowTag w ≤ 2)
    (hc : rowC m w ≠ 0) : ∃ ci, decCI (m.arr64 EREC) dn (rowP m w).toNat = some ci := by
  have hn : (decI w : NIdx).word.toUInt64 = w := (word_decI _ w hw).mpr rfl
  have hk := h.keys (decI w) (by rw [hn]; exact ht)
  have hv := h.vals (decI w) (by rw [hn]; exact ht) (by rw [hn]; exact hc)
  rw [hn] at hk hv
  cases e : fe.idx[(decI w : NIdx)]? with
  | none => simp [e, rowW, hc] at hk
  | some q => rw [e] at hv; exact ⟨q.2, hv.symm⟩

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

/-- The kind word of a decoded constant record says whether it is a constructor, and a
constructor's type is the handle at `q + 4`. -/
theorem decCI_ctor {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
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
