module

public import ConAgua.Arena.ErecRd

@[expose] public section

/-!
# A projection table record's words: the decoder's facts

The facts about `decTbl` (`Arena/EnvRec.lean`) that proofs use, stated over the named offsets of
`RecLayout/Tbl.lean`: what a decoded table says about each word (`decTbl_eq_some`; at L's word
addresses, `decTbl_rd`, and through the environment's handle, the address plus one,
`decTbl_rd1`), and the table built from its words (`decTbl_of`). Proofs use these instead of
unfolding `decTbl` or an offset, so that a change of the layout ends here.
-/

open ConRon.Arena

namespace L.Arena

/-- **A decoded `IProjTable`, word by word.** -/
theorem decTbl_eq_some {R : Nat → Option Word} {p : Nat} {t : IProjTable} :
    decTbl R p = some t ↔
      hd? R (p + ProjTbl.structName.toNat) = some t.structName ∧
      hlist? R (p + ProjTbl.lpsOff.toNat) = some t.levelParams ∧
      nat? R (p + ProjTbl.numParams.toNat) = some t.numParams ∧
      hd? R (p + ProjTbl.ctor.toNat) = some t.ctor ∧
      nat? R (p + ProjTbl.numFields.toNat) = some t.numFields ∧
      hlist? R (p + ProjTbl.bodiesOff.toNat) = some t.bodies.toList := by
  rcases t with ⟨sn, lps, np, ct, nf, bs⟩
  simp only [decTbl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, IProjTable.mk.injEq]
  constructor
  · rintro ⟨_, h1, _, h2, _, h3, _, h4, _, h5, _, h6, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨h1, h2, h3, h4, h5, by simpa using h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨_, h1, _, h2, _, h3, _, h4, _, h5, _, h6, rfl, rfl, rfl, rfl, rfl, by simp⟩

/-- The table built from its words. -/
theorem decTbl_of {R : Nat → Option Word} {p : Nat} {t : IProjTable}
    (h1 : hd? R (p + ProjTbl.structName.toNat) = some t.structName)
    (h2 : hlist? R (p + ProjTbl.lpsOff.toNat) = some t.levelParams)
    (h3 : nat? R (p + ProjTbl.numParams.toNat) = some t.numParams)
    (h4 : hd? R (p + ProjTbl.ctor.toNat) = some t.ctor)
    (h5 : nat? R (p + ProjTbl.numFields.toNat) = some t.numFields)
    (h6 : hlist? R (p + ProjTbl.bodiesOff.toNat) = some t.bodies.toList) : decTbl R p = some t :=
  decTbl_eq_some.mpr ⟨h1, h2, h3, h4, h5, h6⟩

/-- **A table's words decode** (a writer's field words, its two slices given). -/
theorem decTbl_of_words {R : Nat → Option Word} {p : Nat} {sn lo ll np c nf bo bl : Word}
    {lps : List NIdx} {bs : Array EIdx}
    (h2 : R (p + ProjTbl.structName.toNat) = some sn) (h3 : R (p + ProjTbl.lpsOff.toNat) = some lo)
    (h4 : R (p + ProjTbl.lpsLen.toNat) = some ll) (h5 : R (p + ProjTbl.numParams.toNat) = some np)
    (h6 : R (p + ProjTbl.ctor.toNat) = some c) (h7 : R (p + ProjTbl.numFields.toNat) = some nf)
    (h9 : R (p + ProjTbl.bodiesOff.toNat) = some bo) (h10 : R (p + ProjTbl.bodiesLen.toNat) = some bl)
    (hsn : sn.toNat < 2 ^ 32) (hc : c.toNat < 2 ^ 32) (hl : hslice? R lo.toNat ll.toNat = some lps)
    (hb : hslice? R bo.toNat bl.toNat = some bs.toList) :
    decTbl R p = some ⟨decI sn, lps, np.toNat, decI c, nf.toNat, bs⟩ := by
  have h4' : R (p + ProjTbl.lpsOff.toNat + 1) = some ll := by
    rw [Nat.add_assoc, ← ProjTbl.lpsLen_toNat]; exact h4
  have h10' : R (p + ProjTbl.bodiesOff.toNat + 1) = some bl := by
    rw [Nat.add_assoc, ← ProjTbl.bodiesLen_toNat]; exact h10
  exact decTbl_of (by simp only [hd?, h2, Option.bind_some]; simp [hsn]) (by simp [hlist?, nat?, h3, h4', hl])
    (by simp [nat?, h5]) (by simp [hd?, h6, hc]) (by simp [nat?, h7]) (by simp [hlist?, nat?, h9, h10', hb])

/-- **A decoded `IProjTable` at L's word addresses** `q + ProjTbl.f` (any reader `R` with its word
read `rd`: the record pool, an array). -/
theorem decTbl_rd {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {t : IProjTable} (h : decTbl R q.toNat = some t) :
    (rd (q + ProjTbl.structName)).toNat < 2 ^ 32 ∧ t.structName = decI (rd (q + ProjTbl.structName)) ∧
    hslice? R (rd (q + ProjTbl.lpsOff)).toNat (rd (q + ProjTbl.lpsLen)).toNat = some t.levelParams ∧
    t.numParams = (rd (q + ProjTbl.numParams)).toNat ∧
    (rd (q + ProjTbl.ctor)).toNat < 2 ^ 32 ∧ t.ctor = decI (rd (q + ProjTbl.ctor)) ∧
    t.numFields = (rd (q + ProjTbl.numFields)).toNat ∧
    hslice? R (rd (q + ProjTbl.bodiesOff)).toNat (rd (q + ProjTbl.bodiesLen)).toNat = some t.bodies.toList := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := decTbl_eq_some.mp h
  obtain ⟨w1, hw1, hl1, e1⟩ := hd?_some h1
  obtain ⟨w4, hw4, hl4, e4⟩ := hd?_some h4
  obtain ⟨w3, hw3, e3⟩ : ∃ w, R (q.toNat + ProjTbl.numParams.toNat) = some w ∧ w.toNat = t.numParams := by
    simpa [nat?] using h3
  obtain ⟨w5, hw5, e5⟩ : ∃ w, R (q.toNat + ProjTbl.numFields.toNat) = some w ∧ w.toNat = t.numFields := by
    simpa [nat?] using h5
  have sl : ∀ {k : IdxKind} (o l : Word), l.toNat = o.toNat + 1 → ∀ {xs : List (Idx k)},
      hlist? R (q.toNat + o.toNat) = some xs →
      hslice? R (rd (q + o)).toNat (rd (q + l)).toNat = some xs := fun o l hl xs hx => by
    simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hx
    obtain ⟨_, ⟨wo, hwo, rfl⟩, _, ⟨wl, hwl, rfl⟩, hs⟩ := hx
    rw [hR.at _ rfl hwo, hR.at _ hl (by rw [← Nat.add_assoc]; exact hwl)]
    exact hs
  rw [hR.at _ rfl hw1, hR.at _ rfl hw4, hR.at _ rfl hw3, hR.at _ rfl hw5]
  exact ⟨hl1, e1, sl _ _ ProjTbl.lpsLen_toNat h2, e3.symm, hl4, e4, e5.symm,
    sl _ _ ProjTbl.bodiesLen_toNat h6⟩

/-- **The words of a decoded table** as the readers of a found table use them: the level-parameter
count, the parameter count, the constructor, the field count. -/
theorem decTbl_words {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {t : IProjTable} (h : decTbl R q.toNat = some t) :
    t.levelParams.length = (rd (q + ProjTbl.lpsLen)).toNat ∧
    t.numParams = (rd (q + ProjTbl.numParams)).toNat ∧
    (rd (q + ProjTbl.ctor)).toNat < 2 ^ 32 ∧ t.ctor = decI (rd (q + ProjTbl.ctor)) ∧
    t.numFields = (rd (q + ProjTbl.numFields)).toNat := by
  obtain ⟨-, -, hl, hp, hw, hc, hf, -⟩ := decTbl_rd hR h
  exact ⟨hslice?_lenR hl, hp, hw, hc, hf⟩

/-- A field's address through the environment's handle `tq` (the record's address plus one). -/
theorem tbl_handle_add (tq f : Word) : tq - 1 + f = tq + (f - 1) := by
  rw [UInt64.sub_eq_add_neg, UInt64.sub_eq_add_neg, UInt64.add_assoc, UInt64.add_comm (-1) f]

/-- **A decoded `IProjTable` through the environment's handle** `tq` (the record at `tq - 1`, the
fields at `tq + (ProjTbl.f - 1)`, as L reads them). -/
theorem decTbl_rd1 {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {tq : Word}
    {t : IProjTable} (h0 : tq ≠ 0) (h : decTbl R (tq.toNat - 1) = some t) :
    t.numParams = (rd (tq + (ProjTbl.numParams - 1))).toNat ∧
    (rd (tq + (ProjTbl.ctor - 1))).toNat < 2 ^ 32 ∧ t.ctor = decI (rd (tq + (ProjTbl.ctor - 1))) ∧
    t.numFields = (rd (tq + (ProjTbl.numFields - 1))).toNat := by
  have hq : (tq - 1).toNat = tq.toNat - 1 := by
    have : (1 : Word) ≤ tq := by
      have : tq.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simp [e]))
      rw [UInt64.le_iff_toNat_le]; simp; omega
    rw [UInt64.toNat_sub_of_le _ _ this]; rfl
  rw [← hq] at h
  obtain ⟨-, -, -, hp, hw, hc, hf, -⟩ := decTbl_rd hR h
  simp only [tbl_handle_add] at hp hw hc hf
  exact ⟨hp, hw, hc, hf⟩

end L.Arena
