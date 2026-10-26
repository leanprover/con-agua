import ConAgua.Arena.PromoteCIRef5

/-!
# `promote_rule` refines `promoteRule`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem nat?_get {a : Array Word} {i x : Nat} (h : nat? a i = some x) :
    ∃ w, a[i]? = some w ∧ w.toNat = x := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, hw, rfl⟩

theorem bool?_get {a : Array Word} {i : Nat} {x : Bool} (h : bool? a i = some x) :
    ∃ w, a[i]? = some w ∧ (w != 0) = x := by
  simp only [bool?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, hw, rfl⟩

/-- The words a decoded rule record reads. -/
theorem pmDecRule_words {a : Array Word} {q : Nat} {rl : IRecRule} (h : decRule a q = some rl) :
    ∃ w0 w1 w2 w8 w9 w10 : Word, a[q]? = some w0 ∧ w0.toNat < 2 ^ 32 ∧ rl.ctor = decI w0 ∧
      a[q + 1]? = some w1 ∧ w1.toNat = rl.nfields ∧ a[q + 2]? = some w2 ∧
      w2.toNat = rl.ctorParams ∧ a[q + 8]? = some w8 ∧ w8.toNat < 2 ^ 32 ∧ rl.rhs = decI w8 ∧
      a[q + 9]? = some w9 ∧ (w9 != 0) = rl.k ∧ a[q + 10]? = some w10 ∧ (w10 != 0) = rl.eta := by
  unfold decRule at h
  cases hk : nat? a (q + 3) with
  | none => simp [hk] at h
  | some t =>
    simp only [hk, Option.bind_eq_bind, Option.bind_some] at h
    rcases t with _ | _ | t
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨c, hc, nf, hnf, cpr, hcp, r, hr, kb, hkb, eb, heb, rfl⟩ := h
      obtain ⟨w0, e0, l0, rfl⟩ := hd?_some hc
      obtain ⟨w1, e1, rfl⟩ := nat?_get hnf
      obtain ⟨w2, e2, rfl⟩ := nat?_get hcp
      obtain ⟨w8, e8, l8, rfl⟩ := hd?_some hr
      obtain ⟨w9, e9, rfl⟩ := bool?_get hkb
      obtain ⟨w10, e10, rfl⟩ := bool?_get heb
      exact ⟨w0, w1, w2, w8, w9, w10, e0, l0, rfl, e1, rfl, e2, rfl, e8, l8, rfl, e9, rfl, e10, rfl⟩
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨l1, hl1, l2, hl2, c, hc, nf, hnf, cpr, hcp, r, hr, kb, hkb, eb, heb, rfl⟩ := h
      obtain ⟨w0, e0, l0, rfl⟩ := hd?_some hc
      obtain ⟨w1, e1, rfl⟩ := nat?_get hnf
      obtain ⟨w2, e2, rfl⟩ := nat?_get hcp
      obtain ⟨w8, e8, l8, rfl⟩ := hd?_some hr
      obtain ⟨w9, e9, rfl⟩ := bool?_get hkb
      obtain ⟨w10, e10, rfl⟩ := bool?_get heb
      exact ⟨w0, w1, w2, w8, w9, w10, e0, l0, rfl, e1, rfl, e2, rfl, e8, l8, rfl, e9, rfl, e10, rfl⟩
    · simp at h

theorem FireWords.mono {A B : Array Word} (h : ArrExt A B) {k q b r y : Word} {fire : IRecRuleFire}
    (hf : FireWords A k q b r y fire) : FireWords B k q b r y fire := by
  rcases hf with hf | ⟨hk, lv, ps, rfl, h1, h2⟩
  · exact Or.inl hf
  · exact Or.inr ⟨hk, lv, ps, rfl, h.hslice? h1, h.hslice? h2⟩

theorem decFire_of_words {A : Array Word} {d : Nat} {k q b r y : Word} {fire : IRecRuleFire}
    (h3 : A[d + 3]? = some k) (h4 : A[d + 4]? = some q) (h5 : A[d + 5]? = some b)
    (h6 : A[d + 6]? = some r) (h7 : A[d + 7]? = some y) (hf : FireWords A k q b r y fire) :
    decFire A d = some fire := by
  unfold decFire
  have n3 : nat? A (d + 3) = some k.toNat := by simp [nat?, h3]
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, lv, ps, rfl, h1, h2⟩
  · simp [n3]
  · have n3' : nat? A (d + 3) = some 1 := by simpa using n3
    have l1 : hlist? A (d + 4) = some lv := by
      simp [hlist?, nat?, h4, h5, h1]
    have l2 : hlist? A (d + 6) = some ps := by
      simp [hlist?, nat?, h6, h7, h2]
    simp [n3', l1, l2]

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem peAt_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (u : EIdx)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hd? (erecP m) addr.toNat = some u) (hc : callW p n "pe_at" [f, addr] m = some (r, m')) :
    AtOk (promoteE pm f.toNat u) decE m a (r.headD 0) m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (peAt_spec p hp n ⟨m, Locals.init []⟩ f addr) hc
  simp only at hW
  rw [hs'] at hW
  obtain ⟨w, hw, hwl, rfl⟩ := hd?_some hu
  have hw' := erecP_get hw
  simp only [peAtW] at hW
  obtain ⟨⟨r₁, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm1, hr1, -⟩ := rd1_call p hp hca
  rw [rd1W_of hsz (by simpa using hw')] at hr1
  subst hr1
  obtain rfl := hm1.symm
  obtain ⟨⟨r₂, m₂⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have key : PEOk (promoteE pm f.toNat (decE w)) m a pm (r₂.headD 0) m₂ :=
    (pe_rel p hp n).1 m a pm f w r₂ m₂ hD hP hwl hcb
  obtain ⟨a', pm', hrun, hD', hP', hpw, hcp, hfr, htk⟩ := key
  rw [← hr]
  exact ⟨a', pm', hrun, hD', hP', hpw, hcp, hfr, htk⟩

end rel

end L.Arena
