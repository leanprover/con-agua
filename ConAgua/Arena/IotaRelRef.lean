module

public import ConAgua.Arena.IotaRelModels
public import ConAgua.Arena.IotaFrameRef
public import ConAgua.Arena.CoreLevels
public import ConAgua.Arena.IndRealFvt
public import ConAgua.Arena.IndRealBle
public import ConRon.Bridge.Inductives.IotaRead
import all ConAgua.Arena.CoreLevels
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.Core.Walks.PropRead

@[expose] public section

/-!
# The ι reading rule, part 2: the refinements of the comparisons (lane ronsync8)

Each L function of `IotaRel.lean` against its twin (`ConRon/Arena/Inductives/IotaRead.lean`). The
statements are runs: a returning L run (its generated model) from `StageR vis feR` (the L view of
the index `feR` the function reads) and con-ron's invariant `CheckOK false env fe` (the twin's
caches and store, at the entry index `fe`) is the twin's `.ok` run, the stage kept, the pool
grown, the results decoding the twin's, and a `CoreStep` (the invariant after, the store grown).

This file: the levels (`lvl_eq`, `lvls_eq` against `readLevelM`/`readLevelsM` and `isEquiv`), and
`expr_lvl_eq` (`lvlEq`).
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-! ## The twin's reads -/

theorem viewSort_run' {a : AState} {h : EIdx} :
    (viewSort h).run a = .ok (a.store.viewSort h, a) := by
  simp [viewSort, StateT.run_get]; rfl

theorem viewConst_run' {a : AState} {h : EIdx} :
    (viewConst h).run a = .ok (a.store.viewConst h, a) := by
  simp [viewConst, StateT.run_get]; rfl

theorem viewApp_run' {a : AState} {h : EIdx} :
    (viewApp h).run a = .ok (a.store.viewApp h, a) := by
  simp [viewApp, StateT.run_get]; rfl

theorem viewLet_run' {a : AState} {h : EIdx} :
    (viewLet h).run a = .ok (a.store.viewLet h, a) := by
  simp [viewLet, StateT.run_get]; rfl

theorem viewProj_run' {a : AState} {h : EIdx} :
    (viewProj h).run a = .ok (a.store.viewProj h, a) := by
  simp [viewProj, StateT.run_get]; rfl

theorem viewBVar_run' {a : AState} {h : EIdx} :
    (viewBVar h).run a = .ok (a.store.viewBVar h, a) := by
  simp [viewBVar, StateT.run_get]; rfl

theorem viewLsLen_run' {a : AState} {h : LsIdx} :
    (viewLsLen h).run a = .ok (a.store.lss.viewLen h, a) := by
  simp [viewLsLen, StateT.run_get]; rfl

/-! ## `lvl_eq`, `lvls_eq` against the twin's readbacks -/

section lv
variable {p : Prog} {env : ConLeche.Env} {fe feR : IFEnv} {vis : Word}

/-- The twin state after a level readback. -/
abbrev withRL (a : AState) (X : Std.HashMap LIdx ConLeche.Level) : AState :=
  { a with caches := { a.caches with readLC := X } }

/-- **`lvl_eq(u, v)` against the twin's two readbacks**: at handles whose readbacks are defined, a
returning run answers `encO (isEquiv lu lv)`, the twin reads both levels (only `readLC` changes),
the stage is kept, and con-ron's invariant holds after. -/
theorem lvlEq_step (hL : LvlCacheProg p) {n : Nat} {m m' : Mem} {a : AState} {r : List Word}
    (hS : StageR vis feR m a) (hok : ConRon.Bridge.CheckOK false env fe a) {u v : Word}
    (hu : HW u) (hv : HW v) {lu lv : ConLeche.Level} (hdu : denoteL a.store.ls (decI u) = some lu)
    (hdv : denoteL a.store.ls (decI v) = some lv)
    (hc : callW p n "lvl_eq" [u, v] m = some (r, m')) :
    ∃ a1 a2, (readLevelM (decI u)).run a = .ok (lu, a1) ∧ (readLevelM (decI v)).run a1 = .ok (lv, a2) ∧
      r.headD 0 = encO (ConLeche.Level.isEquiv lu lv) ∧ StageR vis feR m' a2 ∧ IWGrow m m' ∧
      ConRon.Bridge.CoreStep env fe a a2 := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lvlEq_spec p hL.lev hL.equiv hL.lvleq n _ u v) hc
  rcases n with _ | n
  · simp [lvlEqW] at hW
  simp only [lvlEqW] at hW
  have hR₀ : ArenaR (m.set64 CTL 192 0) a :=
    ArenaR.frame (by decide) c192_not_arena (reset_frame m) hS.check.arena.base
  have hwu : (decI u : LIdx).word.toUInt64 = u := (word_decI _ u hu).mpr rfl
  have hwv : (decI v : LIdx).word.toUInt64 = v := (word_decI _ v hv).mpr rfl
  have hl' := denoteL_lvR hR₀ (decI u) lu hdu
  have hr' := denoteL_lvR hR₀ (decI v) lv hdv
  rw [hwu] at hl'; rw [hwv] at hr'
  have hnwf : NStoreWF a.store.lss.ls.ns := by
    obtain ⟨rk, w⟩ := hok.state.wf; obtain ⟨rk', w'⟩ := w.lss.ls; exact w'.ns
  obtain ⟨hx, hz⟩ := equivW_ok (nameN_rel _ hnwf) n _ _ _ _ _ _ _ hl' hr' hW
  have hf : MemFrame [LH] [192] m s'.mem :=
    ((reset_frame m).mono (by simp) (by simp)).trans hx.memFrame
  obtain ⟨hS1, hg⟩ := hS.frame_hi hf
    (fun b hb => by simp only [List.mem_singleton] at hb; subst hb; decide)
    (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; decide) (by decide) (by decide)
  obtain ⟨X, h1, hX⟩ := readLevelM_run' a (decI u) lu hdu hok.caches.readL
  have hok1 := ConRon.Bridge.Core.CheckOK.ofReadL (s1 := withRL a X) hok rfl rfl rfl rfl hX
  obtain ⟨Y, h2, hY⟩ := readLevelM_run' (withRL a X) (decI v) lv hdv hX
  have hok2 := ConRon.Bridge.Core.CheckOK.ofReadL (s1 := withRL (withRL a X) Y) hok1 rfl rfl rfl rfl hY
  exact ⟨_, _, h1, h2, hz, hS1.withReadLC Y |>.withReadLC Y, hg, ⟨hok2, Ext.refl _, rfl⟩⟩

/-- The twin state after a level-list readback. -/
abbrev withRLs (a : AState) (X : Std.HashMap LsIdx (List ConLeche.Level)) : AState :=
  { a with caches := { a.caches with readLsC := X } }

theorem StageR.withReadLsC {m : Mem} {a : AState} (hS : StageR vis feR m a)
    (X : Std.HashMap LsIdx (List ConLeche.Level)) : StageR vis feR m (withRLs a X) :=
  ⟨⟨hS.check.arena.caches_irrel _, let ⟨M, hM⟩ := hS.check.core; ⟨M, hM.readLsC X⟩, hS.check.pins,
    hS.check.env, hS.check.mode⟩, hS.iw⟩

/-- **`lvls_eq(us, vs)` against the twin's two list readbacks** (`lvl_eq_step` for lists). -/
theorem lvlsEq_step (hL : LvlCacheProg p) {n : Nat} {m m' : Mem} {a : AState} {r : List Word}
    (hS : StageR vis feR m a) (hok : ConRon.Bridge.CheckOK false env fe a) {us vs : Word}
    (hu : HW us) (hv : HW vs) {lu lv : List ConLeche.Level}
    (hdu : denoteLs a.store.lss (decI us) = some lu) (hdv : denoteLs a.store.lss (decI vs) = some lv)
    (hc : callW p n "lvls_eq" [us, vs] m = some (r, m')) :
    ∃ a1 a2, (readLevelsM (decI us)).run a = .ok (lu, a1) ∧ (readLevelsM (decI vs)).run a1 = .ok (lv, a2) ∧
      r.headD 0 = encO (ConLeche.Level.isEquivList lu lv) ∧ StageR vis feR m' a2 ∧ IWGrow m m' ∧
      ConRon.Bridge.CoreStep env fe a a2 := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lvlsEq_spec p hL.lev hL.equiv hL.equivs hL.lsnode hL.lvlseq n _ us vs) hc
  rcases n with _ | n
  · simp [lvlsEqW] at hW
  have hR := hS.check.arena.base
  obtain ⟨ids₁, hv₁, hd₁⟩ := denoteLs_view a (decI us) lu hdu
  obtain ⟨ids₂, hv₂, hd₂⟩ := denoteLs_view a (decI vs) lv hdv
  obtain ⟨e₁, t₁, s₁⟩ := lsNodeW_store hR hu hv₁
  obtain ⟨e₂, t₂, s₂⟩ := lsNodeW_store hR hv hv₂
  have hu0 : lsNodeW m us ≠ [] := by rw [e₁]; simp
  have hv0 : lsNodeW m vs ≠ [] := by rw [e₂]; simp
  rw [lvlsEqW.arm1 _ _ _ _ hu0 hv0, e₁, e₂] at hW
  simp only [List.headD_cons, List.tail_cons] at hW
  have hR₀ : ArenaR (m.set64 CTL 192 0) a :=
    ArenaR.frame (by decide) c192_not_arena (reset_frame m) hR
  have hpool : (m.set64 CTL 192 0).arr64 POOL = m.arr64 POOL :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hpool1 : (m.set64 CTL 192 0).arr64 POOL1 = m.arr64 POOL1 :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hpoolv := vpool_congr hpool hpool1
  have htop := hR.lit.1.top41
  have hl₁ := lvsR_of_slice hR₀ ids₁ lu _ _ (by rw [hpoolv]; exact s₁) (by omega) hd₁
  have hl₂ := lvsR_of_slice hR₀ ids₂ lv _ _ (by rw [hpoolv]; exact s₂) (by omega) hd₂
  have hnwf : NStoreWF a.store.lss.ls.ns := by
    obtain ⟨rk, w⟩ := hok.state.wf; obtain ⟨rk', w'⟩ := w.lss.ls; exact w'.ns
  obtain ⟨hx, hz⟩ := equivsW_ok (nameN_rel _ hnwf) n _ _ _ _ _ _ _ _ _ hl₁ hl₂ hW
  have hf : MemFrame [LH] [192] m s'.mem :=
    ((reset_frame m).mono (by simp) (by simp)).trans hx.memFrame
  obtain ⟨hS1, hg⟩ := hS.frame_hi hf
    (fun b hb => by simp only [List.mem_singleton] at hb; subst hb; decide)
    (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; decide) (by decide) (by decide)
  obtain ⟨X, h1, hX⟩ := readLevelsM_run' a (decI us) lu hdu hok.caches.readLs
  have hok1 := ConRon.Bridge.Core.CheckOK.ofReadLs (s1 := withRLs a X) hok rfl rfl rfl rfl hX
  obtain ⟨Y, h2, hY⟩ := readLevelsM_run' (withRLs a X) (decI vs) lv hdv hX
  have hok2 := ConRon.Bridge.Core.CheckOK.ofReadLs (s1 := withRLs (withRLs a X) Y) hok1 rfl rfl rfl rfl hY
  exact ⟨_, _, h1, h2, hz, (hS1.withReadLsC X).withReadLsC Y, hg, ⟨hok2, Ext.refl _, rfl⟩⟩

end lv

end L.Ind
