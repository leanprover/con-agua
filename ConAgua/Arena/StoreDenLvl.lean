import ConAgua.Arena.StoreDen

/-!
# Interned levels read back (lane `defeq2`)

`LvlAll` (every valid level handle reads back) across `internLNode`, and the readback of an
interned level list across `internLsNode`. A cons-table hit names a node with the probed view
(under `ArenaR`, the tables' `TierR` clauses); a push appends a node whose view is the interned
one and raises the node count, so the new handle reads back through its children, and old handles
keep their readbacks (`LExt`).
-/

open ConRon.Arena

namespace L.Arena

/-! ## A cons-table hit under `TierR` -/

/-- **A cons hit of a tier names a node of that tier** with the probed record, and the handle
carries the schema's tag and the tier's bit. -/
theorem tierR_cons_hit {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] {S : Schema}
    {R : Mem → Word → Word → α → Prop} {hs : Mem → Word → Word → Word} {m : Mem} {t : Word}
    {tb : Tbl α (Idx k) δ} (hT : TierR S R hs m t tb) (hg : S.tag.toNat < 16) (ht : t ≤ 1)
    {a : α} {x : Idx k} (hc : tb.cons[a]? = some x) :
    tb.nodes[x.idxNat]? = some a ∧ x.tag = S.tag ∧ x.isPersistent = (t == 0) := by
  have h6 := hT.2.2.2.2.2.1 a x hc
  have hix_nat : (hix x).toNat = x.idxNat := by
    simp only [hix]
    have : x.idxNat < 2 ^ 27 := by
      simp only [Idx.idxNat, Idx.index]; have := UInt32.toNat_mod x.word 134217728
      simp at this ⊢; omega
    simp; omega
  rw [hix_nat] at h6
  refine ⟨h6, ?_⟩
  have h5 := hT.2.2.2.2.1 (hix x) a (by rw [hix_nat]; exact h6)
  rw [hc] at h5
  have hx := Option.some.inj h5
  have hi : x.idxNat < 2 ^ 27 := by
    simp only [Idx.idxNat, Idx.index]; simp; omega
  have ht' : t.toNat ≤ 1 := by rw [UInt64.le_iff_toNat_le] at ht; simpa using ht
  have hw : x.word.toNat = S.tag.toNat * 268435456 + t.toNat * 134217728 + x.idxNat := by
    have := congrArg Idx.word hx
    rw [this]
    simp only [decI, hdW, hix]
    simp [UInt64.toNat_toUInt32]
    omega
  constructor
  · apply UInt32.toNat_inj.mp
    simp only [Idx.tag, UInt32.toNat_div]; simp; omega
  · simp only [Idx.isPersistent, Idx.tier]
    have e1 : (x.word / 134217728 % 2 = 0) ↔ (t = 0) := by
      rw [← UInt32.toNat_inj, ← UInt64.toNat_inj]
      simp only [UInt32.toNat_mod, UInt32.toNat_div]; simp; omega
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact e1

set_option linter.unusedSimpArgs false in
/-- **Under `ArenaR`, a level cons hit names a node with the probed view.** -/
theorem lview_of_find {m : Mem} {a : AState} (hR : ArenaR m a) {v : LNodeView} {i : LIdx}
    (hf : a.store.ls.find? v = some i) : a.store.ls.view i = some v := by
  simp only [EStore.ls, LStore.find?] at hf ⊢
  split at hf
  · rename_i j hp
    cases hf
    cases v <;> simp only [LTables.find?, Tbl.find?] at hp
    · obtain ⟨hn, htag, hpers⟩ := tierR_cons_hit hR.zero.2.2.1 (by decide) (by decide) hp
      simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, zeroSch, LTag.zero, LTag.succ,
        LTag.max, LTag.imax, LTag.param]
    · obtain ⟨hn, htag, hpers⟩ := tierR_cons_hit hR.succ.2.2.1 (by decide) (by decide) hp
      simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, succSch, LTag.zero, LTag.succ,
        LTag.max, LTag.imax, LTag.param]
    · obtain ⟨hn, htag, hpers⟩ := tierR_cons_hit hR.max.2.2.1 (by decide) (by decide) hp
      simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, maxSch, LTag.zero, LTag.succ,
        LTag.max, LTag.imax, LTag.param]
    · obtain ⟨hn, htag, hpers⟩ := tierR_cons_hit hR.imax.2.2.1 (by decide) (by decide) hp
      simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, imaxSch, LTag.zero, LTag.succ,
        LTag.max, LTag.imax, LTag.param]
    · obtain ⟨hn, htag, hpers⟩ := tierR_cons_hit hR.param.2.2.1 (by decide) (by decide) hp
      simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, paramSch, LTag.zero, LTag.succ,
        LTag.max, LTag.imax, LTag.param]
  · by_cases hon : a.store.lss.ls.scratchOn = true
    · simp only [hon, ↓reduceIte] at hf
      cases v <;> simp only [LTables.find?, Tbl.find?] at hf
      · obtain ⟨hn, htag, hpers⟩ := tierR_cons_hit hR.zero.2.2.2 (by decide) (by decide) hf
        simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, zeroSch, LTag.zero, LTag.succ,
          LTag.max, LTag.imax, LTag.param, hon]
      · obtain ⟨hn, htag, hpers⟩ := tierR_cons_hit hR.succ.2.2.2 (by decide) (by decide) hf
        simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, succSch, LTag.zero, LTag.succ,
          LTag.max, LTag.imax, LTag.param, hon]
      · obtain ⟨hn, htag, hpers⟩ := tierR_cons_hit hR.max.2.2.2 (by decide) (by decide) hf
        simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, maxSch, LTag.zero, LTag.succ,
          LTag.max, LTag.imax, LTag.param, hon]
      · obtain ⟨hn, htag, hpers⟩ := tierR_cons_hit hR.imax.2.2.2 (by decide) (by decide) hf
        simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, imaxSch, LTag.zero, LTag.succ,
          LTag.max, LTag.imax, LTag.param, hon]
      · obtain ⟨hn, htag, hpers⟩ := tierR_cons_hit hR.param.2.2.2 (by decide) (by decide) hf
        simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, paramSch, LTag.zero, LTag.succ,
          LTag.max, LTag.imax, LTag.param, hon]
    · simp [hon] at hf

end L.Arena
