import ConAgua.Arena.WhnfBase
import ConAgua.Arena.StoreDenLvl

/-!
# The level tables only grow (lane `defeq2`)

`LvlCnt m m'` (`WhnfBase.lean`, a field of `PoolGrew`): the scratch flag is kept and no level
table's count drops. A frame that avoids those `CTL` words keeps it trivially; a level interning
grows one table, so under `ArenaR` at both ends (the counts are the twin tables' sizes, `TierR`)
it follows from the twin's `LStore.intern` growing its tables (`lvlCnt_of_arena`).
-/

open ConRon.Arena

namespace L.Arena

/-- Every level table of a tier at least as large. -/
structure LTGrow (t t' : LTables) : Prop where
  zeros : t.zeros.nodes.size ≤ t'.zeros.nodes.size
  succs : t.succs.nodes.size ≤ t'.succs.nodes.size
  maxs : t.maxs.nodes.size ≤ t'.maxs.nodes.size
  imaxs : t.imaxs.nodes.size ≤ t'.imaxs.nodes.size
  params : t.params.nodes.size ≤ t'.params.nodes.size

theorem LTGrow.refl (t : LTables) : LTGrow t t := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem LTGrow.push (t : LTables) (v : LNodeView) (d : LDer) (tier : UInt32) :
    LTGrow t (t.push v d tier).1 := by
  cases v <;> simp only [LTables.push, Tbl.push] <;>
    exact ⟨by simp, by simp, by simp, by simp, by simp⟩

theorem LTGrow.intern (st : LStore) (v : LNodeView) :
    LTGrow st.pers (st.intern v).1.pers ∧ LTGrow st.scr (st.intern v).1.scr := by
  unfold LStore.intern
  split
  · exact ⟨LTGrow.refl _, LTGrow.refl _⟩
  · split
    · split
      · exact ⟨LTGrow.refl _, LTGrow.refl _⟩
      · exact ⟨LTGrow.refl _, LTGrow.push _ _ _ _⟩
    · exact ⟨LTGrow.push _ _ _ _, LTGrow.refl _⟩

theorem cnt_le {S : Schema} {m m' : Mem} {t x : Word} {n n' : Nat} (h1 : (cntW S m t).toNat = n)
    (h2 : (cntW S m' t).toNat = n') (hn : n ≤ n') (hx : S.ca + t = x) :
    (rdW (m.arr64 CTL) x).toNat ≤ (rdW (m'.arr64 CTL) x).toNat := by
  subst hx; simp only [cntW] at h1 h2; omega

/-- **Level-table growth from the twin**: under `ArenaR` at both ends, a kept scratch flag and
twin level tables that only grew give `LvlCnt`. -/
theorem lvlCnt_of_arena {m m' : Mem} {a a' : AState} (hR : ArenaR m a) (hR' : ArenaR m' a')
    (hflag : rdW (m'.arr64 CTL) 1 = rdW (m.arr64 CTL) 1)
    (hp : LTGrow a.store.lss.ls.pers a'.store.lss.ls.pers)
    (hs : LTGrow a.store.lss.ls.scr a'.store.lss.ls.scr) : LvlCnt m m' := by
  refine ⟨hflag, fun x hx => ?_⟩
  simp only [lvlCtlW, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hflag]; exact Nat.le_refl _
  · exact cnt_le hR.succ.2.2.1.1 hR'.succ.2.2.1.1 hp.succs (by decide)
  · exact cnt_le hR.succ.2.2.2.1 hR'.succ.2.2.2.1 hs.succs (by decide)
  · exact cnt_le hR.zero.2.2.1.1 hR'.zero.2.2.1.1 hp.zeros (by decide)
  · exact cnt_le hR.zero.2.2.2.1 hR'.zero.2.2.2.1 hs.zeros (by decide)
  · exact cnt_le hR.max.2.2.1.1 hR'.max.2.2.1.1 hp.maxs (by decide)
  · exact cnt_le hR.max.2.2.2.1 hR'.max.2.2.2.1 hs.maxs (by decide)
  · exact cnt_le hR.imax.2.2.1.1 hR'.imax.2.2.1.1 hp.imaxs (by decide)
  · exact cnt_le hR.imax.2.2.2.1 hR'.imax.2.2.2.1 hs.imaxs (by decide)
  · exact cnt_le hR.param.2.2.1.1 hR'.param.2.2.1.1 hp.params (by decide)
  · exact cnt_le hR.param.2.2.2.1 hR'.param.2.2.2.1 hs.params (by decide)

/-- **A level interning grows the level tables** (a hit changes nothing, a miss is
`LStore.intern`). -/
theorem LTGrow.internLNode {a a' : AState} {v : LNodeView} {h : LIdx}
    (hrun : (internLNode v).run a = .ok (h, a')) :
    LTGrow a.store.lss.ls.pers a'.store.lss.ls.pers ∧ LTGrow a.store.lss.ls.scr a'.store.lss.ls.scr := by
  rcases internLNode_run_cases hrun with ⟨-, rfl⟩ | ⟨-, -, he, -⟩
  · exact ⟨LTGrow.refl _, LTGrow.refl _⟩
  · have e : a'.store.lss.ls = (a.store.lss.ls.intern v).1 := he
    rw [e]; exact LTGrow.intern _ _

end L.Arena
