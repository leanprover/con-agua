import ConAgua.Front.IndApplyRefine5
import ConAgua.Arena.LevelArena
import ConRon.Bridge.Promote.Walk
import ConRon.Bridge.StateOK
import ConRon.Bridge.Frontend.Rel

/-!
# The apply step of an `inductive` line against the twin, VI: `kExpected?`

`kExpW_twin`: `vi_k_expected` against the twin's `kExpected?` match: a block that is not one type
with one constructor is `some false` (`1`); else the sort at the end of the type's telescope is read
back (`readLevel`) and compared with `zero` by `Level.isEquiv` — in L by `lv_equiv` against a heap
`zero` node, which agrees with the twin because the name store is well formed (`StateOK`: `nameN`
is a `NameRel`, `equivW_ok`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open L.Ind (eViewW eViewW_ok ViewR)


namespace L.Front.Ind

/-- A sort's level, under the store's well-formedness, reads back. -/
theorem denoteL_of_sort {a : AState} (hok : ConRon.Bridge.StateOK a) {r : EIdx} {s : LIdx}
    (h : a.store.view r = some (.sort s)) : ∃ L, denoteL a.store.ls s = some L := by
  obtain ⟨rk, hw⟩ := hok.wf
  have := (hw.lchildOK r _ h s (by simp [ENodeView.lchildren])).1
  exact ConRon.Bridge.denoteL_of_view (LStoreWF'.of_wf hw.lss.ls) this

theorem readLevel_run' {a : AState} {s : LIdx} {L : ConLeche.Level} (h : denoteL a.store.ls s = some L) :
    (readLevel s).run a = .ok (L, a) := by
  rw [show (readLevel s).run a = (match denoteL a.store.ls s with
    | some l => (pure l : AM ConLeche.Level)
    | none => fail (.internal "arena: dangling level handle")).run a from rfl, h]
  rfl

theorem encO_two (o : Option Bool) : encO o = 2 ↔ o = some true := by
  cases o with
  | none => simp [encO]
  | some x => cases x <;> simp [encO]

/-- **`vi_k_expected` against the twin's `kExpected?`.** -/
theorem kExpW_twin {n : Nat} {m m' : Mem} {a : AState} (hR : ArenaR m a)
    (hok : ConRon.Bridge.StateOK a) {to tn tyt oo fuel ke : Word}
    (h : kExpW n m to tn tyt oo fuel = some (ke, m')) :
    MemFrame [LH] [192] m m' ∧
    ((tn ≠ 1 ∨ rdW (m.arr64 IFR) (to + 4) ≠ 1) → ke = 1) ∧
    (tn = 1 → rdW (m.arr64 IFR) (to + 4) = 1 →
      ∃ r v, (ConRon.Arena.Frontend.piResultD fuel.toNat (decE (rdW (m.arr64 IFL) tyt))).run a = .ok (r, a) ∧
        (view r).run a = .ok (v, a) ∧ ((∀ s, v ≠ .sort s) → ke = 0) ∧
        ∀ s, v = .sort s → ∃ L, (readLevel s).run a = .ok (L, a) ∧
          ke = if rdW (m.arr64 IFR) (rdW (m.arr64 IFL) oo + 4) = 0 ∧
            ConLeche.Level.isEquiv L .zero = some true then 2 else 1) := by
  cases n with
  | zero => simp [kExpW] at h
  | succ n =>
  simp only [kExpW] at h
  split at h
  · rename_i htn
    cases h
    exact ⟨MemFrame.refl _ _ _, fun _ => rfl, fun h1 => absurd h1 htn⟩
  rename_i htn
  have htn' : tn = 1 := Classical.byContradiction htn
  split at h
  · rename_i hc
    cases h
    exact ⟨MemFrame.refl _ _ _, fun _ => rfl, fun _ h2 => absurd h2 hc⟩
  rename_i hc
  have hc' : rdW (m.arr64 IFR) (to + 4) = 1 := Classical.byContradiction hc
  rcases hp : piResW n m fuel (rdW (m.arr64 IFL) tyt) with _ | r <;> simp only [hp, keK1, reduceCtorEq] at h
  have hrun := piResW_ok m a hR n fuel _ r hp
  split at h; cases h; rename_i hne
  obtain ⟨v, hv, hvr⟩ := view_ok' m a hR r hne
  split at h
  · rename_i h2
    cases h
    refine ⟨MemFrame.refl _ _ _, fun h1 => by rcases h1 with h1 | h1 <;> contradiction,
      fun _ _ => ⟨decE r, v, hrun, hv, fun _ => rfl, fun s hs => ?_⟩⟩
    rw [hs] at hvr
    exact absurd (viewR_head hvr) h2
  rename_i h2
  have h2' : (eViewW m r).headD 0 = 2 := Classical.byContradiction h2
  obtain ⟨hvs, hsw⟩ := viewR_sort hvr h2'
  have hview : a.store.view (decE r) = some (.sort (decI ((eViewW m r).tail.headD 0))) := by
    have := eViewW_ok m a hR r hne
    obtain ⟨v', hv', hr'⟩ := this
    rw [hv']; congr 1
    exact (viewR_sort hr' h2').1
  obtain ⟨L, hL⟩ := denoteL_of_sort hok hview
  rcases hl : lhMkW (m.set64 CTL 192 0) 0 0 0 with _ | ⟨z, m₂⟩ <;> simp only [hl, keK2, reduceCtorEq] at h
  rcases he : equivW n m₂ ((eViewW m r).tail.headD 0) z with _ | ⟨x, m₃⟩ <;> simp only [he, keK3, reduceCtorEq] at h
  -- both levels are related on `m₂`
  have hR₁ : ArenaR (m.set64 CTL 192 0) a := ArenaR.frame (by decide) c192_not_arena (reset_frame m) hR
  obtain ⟨hx1, hx2, -⟩ := lhMkW_ext hl
  have hR₂ : ArenaR m₂ a := ArenaR.frame lh_not_arena c192_not_arena hx1.memFrame hR₁
  have hN := nameN_rel _ (ConRon.Bridge.Frontend.nsWF_of_StateOK hok)
  have hls := denoteL_lvR hR₂ (decI ((eViewW m r).tail.headD 0)) L hL
  rw [decI_word_self _ hsw] at hls
  have hz : LvR (nameN a.store.lss.ls.ns) m₂ z .zero := .zero hx2
  obtain ⟨hx3, hxe⟩ := equivW_ok hN n m₂ m₃ _ _ x L .zero hls hz he
  have hf : MemFrame [LH] [192] m m₃ :=
    ((reset_frame m).mono (by simp) (by simp)).trans (hx1.memFrame.trans hx3.memFrame)
  have hfr : rdW (m₃.arr64 IFR) (rdW (m.arr64 IFL) oo + 4) = rdW (m.arr64 IFR) (rdW (m.arr64 IFL) oo + 4) := by
    rw [hf.1 IFR (by decide) (by decide)]
  rw [hfr] at h
  have hke : ke = if rdW (m.arr64 IFR) (rdW (m.arr64 IFL) oo + 4) = 0 ∧
      ConLeche.Level.isEquiv L .zero = some true then 2 else 1 := by
    split at h
    · rename_i hq
      cases h
      rw [if_pos ⟨hq.1, (encO_two _).mp (hxe ▸ hq.2)⟩]
    · rename_i hq
      cases h
      rw [if_neg (fun hh => hq ⟨hh.1, by rw [hxe]; exact (encO_two _).mpr hh.2⟩)]
  have hm' : m' = m₃ := by split at h <;> (cases h; rfl)
  subst hm'
  refine ⟨hf, fun h1 => by rcases h1 with h1 | h1 <;> contradiction,
    fun _ _ => ⟨decE r, v, hrun, hv, fun hns => absurd hvs (hns _), fun s hs => ?_⟩⟩
  rw [hvs] at hs
  simp only [ENodeView.sort.injEq] at hs
  subst hs
  exact ⟨L, readLevel_run' hL, hke⟩

end L.Front.Ind
