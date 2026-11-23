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

/-! ## The twin's projections off a view -/

/-- A projection read off the tier its handle names, from the view. -/
theorem irProj {α : Type} {st : EStore} {i : EIdx} {v : ENodeView} {x : α}
    {g : ETables → EIdx → Option α}
    (hg : ∀ t : ETables, t.get i = some v → g t i = some x) (h : st.view i = some v) :
    (if i.isPersistent then g st.pers i else if st.scratchOn then g st.scr i else none) = some x := by
  simp only [EStore.view] at h
  split at h
  · rw [ite_eq_left (by assumption)]; exact hg _ h
  · rw [ite_eq_right (by assumption)]
    split at h
    · rw [ite_eq_left (by assumption)]; exact hg _ h
    · cases h

theorem irViewSort {st : EStore} {i : EIdx} {u : LIdx} (ht : i.tag = ETag.sort)
    (h : st.view i = some (.sort u)) : st.viewSort i = some u :=
  irProj (g := ETables.getSort) (fun t h => by
    unfold ETables.get at h; unfold ETables.getSort
    simp only [ht, ETag.bvar, ETag.fvar, ETag.sort] at h
    revert h; cases t.sorts.node? i.idxNat <;> simp) h

theorem irViewConst {st : EStore} {i : EIdx} {n : NIdx} {us : LsIdx} (ht : i.tag = ETag.const)
    (h : st.view i = some (.const n us)) : st.viewConst i = some (n, us) :=
  irProj (g := ETables.getConst) (fun t h => by
    unfold ETables.get at h; unfold ETables.getConst
    simp only [ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const] at h
    revert h; cases t.consts.node? i.idxNat <;> simp) h

theorem irViewBVar {st : EStore} {i : EIdx} {k : Nat} (ht : i.tag = ETag.bvar)
    (h : st.view i = some (.bvar k)) : st.viewBVar i = some k :=
  irProj (g := ETables.getBVar) (fun t h => by
    unfold ETables.get at h; unfold ETables.getBVar
    simp only [ht, ETag.bvar] at h
    revert h; cases t.bvars.node? i.idxNat <;> simp) h

theorem irViewApp {st : EStore} {i f x : EIdx} (h : st.view i = some (.app f x)) :
    st.viewApp i = some (f, x) :=
  irProj (g := ETables.getApp) (fun t h => by
    unfold ETables.get at h; unfold ETables.getApp
    repeat' (first | (simp at h; done) | split at h)
    all_goals (revert h; cases t.apps.node? i.idxNat <;> simp_all)) h

theorem irViewLet {st : EStore} {i ty v b : EIdx} (h : st.view i = some (.letE ty v b)) :
    st.viewLet i = some (ty, v, b) :=
  irProj (g := ETables.getLet) (fun t h => by
    unfold ETables.get at h; unfold ETables.getLet
    repeat' (first | (simp at h; done) | split at h)
    all_goals (revert h; cases t.lets.node? i.idxNat <;> simp_all)) h

theorem irViewProj {st : EStore} {i : EIdx} {n : NIdx} {k : Nat} {e : EIdx}
    (h : st.view i = some (.proj n k e)) : st.viewProj i = some (n, k, e) :=
  irProj (g := ETables.getProj) (fun t h => by
    unfold ETables.get at h; unfold ETables.getProj
    repeat' (first | (simp at h; done) | split at h)
    all_goals (revert h; cases t.projs.node? i.idxNat <;> simp_all)) h

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

/-! ## `expr_lvl_eq` refines `lvlEq` -/

section lvleq
variable {p : Prog} {env : ConLeche.Env} {fe feR : IFEnv} {vis : Word}

theorem decE_beq (x y : Word) (hx : HW x) (hy : HW y) : (decE x == decE y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · have : decE x ≠ decE y := fun e => h (decI_inj hx hy e)
    simp [h, this]

theorem decE_tag_beq2 (x y : Word) (hx : HW x) (hy : HW y) :
    ((decE x).tag == (decE y).tag) = decide (tagW x = tagW y) := by
  rw [decE_tag x hx, decE_tag y hy]
  have h1 := tagW_lt x hx; have h2 := tagW_lt y hy
  by_cases h : tagW x = tagW y
  · simp [h]
  · have : (tagW x).toUInt32 ≠ (tagW y).toUInt32 := fun e => h (by
      apply UInt64.toNat_inj.mp
      have := congrArg UInt32.toNat e
      simp only [UInt64.toNat_toUInt32] at this
      omega)
    simp [h, this]

theorem sort_lvl_den {st : EStore} (hwf : StoreWF st) {h : EIdx} {u : LIdx}
    (hv : st.view h = some (.sort u)) : ∃ l, denoteL st.ls u = some l := by
  obtain ⟨rk, w⟩ := hwf
  exact denoteL_of_viewW w.lss.ls (w.lchildOK h _ hv u (by simp [ENodeView.lchildren])).1

theorem const_lvls_den {st : EStore} (hwf : StoreWF st) {h : EIdx} {n : NIdx} {us : LsIdx}
    (hv : st.view h = some (.const n us)) : ∃ ls, denoteLs st.lss us = some ls := by
  obtain ⟨rk, w⟩ := hwf
  have hs := (w.lschildOK h _ hv us (by simp [ENodeView.lschildren])).1
  obtain ⟨ids, hids⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨xs, hxs⟩ := denoteLs_of_viewW w.lss hids
  exact ⟨xs, by simp only [denoteLs, hids, hxs]⟩

/-! ## `e_view`'s words, per tag -/

theorem irVR_const {r : List Word} {v : ENodeView} (hr : ViewR r v) (h : r.headD 0 = 3) :
    v = .const (decI (r.tail.headD 0)) (decI (r.tail.tail.headD 0)) ∧ HW (r.tail.headD 0) ∧
      HW (r.tail.tail.headD 0) := by
  cases v <;> simp only [ViewR, h] at hr <;> (try (exfalso; revert hr; decide)) <;>
    (try (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide))
  obtain ⟨-, h1, h2, h3, h4⟩ := hr
  rw [L.getD_one] at h1 h2; rw [L.getD_two] at h3 h4
  exact ⟨by rw [h2, h4], h1, h3⟩

theorem irVR_two {r : List Word} {v : ENodeView} (hr : ViewR r v) (h : r.headD 0 = 4 ∨ r.headD 0 = 5 ∨ r.headD 0 = 6) :
    HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) ∧
      ((r.headD 0 = 4 ∧ v = .app (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0))) ∨
       (r.headD 0 = 5 ∧ v = .lam (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0))) ∨
       (r.headD 0 = 6 ∧ v = .forallE (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0)))) := by
  cases v <;> simp only [ViewR] at hr
  all_goals first
    | (exfalso; obtain ⟨h0, -⟩ := hr; rw [h0] at h; revert h; decide)
    | (exfalso; rw [hr] at h; revert h; decide)
    | skip
  all_goals obtain ⟨h0, h1, h2, h3, h4⟩ := hr
  all_goals rw [L.getD_one] at h1 h2; rw [L.getD_two] at h3 h4
  · exact ⟨h1, h3, .inl ⟨h0, by rw [h2, h4]⟩⟩
  · exact ⟨h1, h3, .inr (.inl ⟨h0, by rw [h2, h4]⟩)⟩
  · exact ⟨h1, h3, .inr (.inr ⟨h0, by rw [h2, h4]⟩)⟩

theorem irVR_let {r : List Word} {v : ENodeView} (hr : ViewR r v) (h : r.headD 0 = 7) :
    v = .letE (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0)) (decE (r.tail.tail.tail.headD 0)) ∧
      HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) ∧ HW (r.tail.tail.tail.headD 0) := by
  cases v <;> simp only [ViewR, h] at hr <;> (try (exfalso; revert hr; decide)) <;>
    (try (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide))
  obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := hr
  rw [L.getD_one] at h1 h2; rw [L.getD_two] at h3 h4; rw [L.getD_three] at h5 h6
  exact ⟨by rw [h2, h4, h6], h1, h3, h5⟩

theorem irVR_proj {r : List Word} {v : ENodeView} (hr : ViewR r v) (h : r.headD 0 = 9) :
    v = .proj (decI (r.tail.headD 0)) (r.tail.tail.headD 0).toNat (decE (r.tail.tail.tail.headD 0)) ∧
      HW (r.tail.headD 0) ∧ HW (r.tail.tail.tail.headD 0) := by
  cases v <;> simp only [ViewR, h] at hr <;> (try (exfalso; revert hr; decide)) <;>
    (try (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide))
  obtain ⟨-, h1, h2, h3, h5, h6⟩ := hr
  rw [L.getD_one] at h1 h2; rw [L.getD_two] at h3; rw [L.getD_three] at h5 h6
  exact ⟨by rw [h2, h3, h6], h1, h5⟩

theorem decW0B_enc (m : Mem) (o : Option Bool) :
    decW0B m [if encO o = 2 then 1 else 0] (o == some true) := by
  rcases o with _ | _ | _ <;> simp [decW0B, encO]

theorem irOfNat2 : UInt64.ofNat 2 = 2 := rfl
theorem irOfNat3 : UInt64.ofNat 3 = 3 := rfl
theorem irOfNat4 : UInt64.ofNat 4 = 4 := rfl
theorem irOfNat5 : UInt64.ofNat 5 = 5 := rfl
theorem irOfNat6 : UInt64.ofNat 6 = 6 := rfl
theorem irOfNat7 : UInt64.ofNat 7 = 7 := rfl
theorem irOfNat9 : UInt64.ofNat 9 = 9 := rfl

theorem irTagB (x : Word) (hx : HW x) (t : UInt32) (k : Nat) (ht : t = UInt32.ofNat k) (hk : k < 16) :
    ((decE x).tag == t) = decide (tagW x = UInt64.ofNat k) := by
  subst ht; exact decE_tag_beq x hx k hk

/-- **`expr_lvl_eq(x, y, fu)` refines `lvlEq fu x y`**. -/
theorem exprLvlEq_run (hev : p.lookup "e_view" = some eView) (hL : LvlCacheProg p) :
    ∀ (n : Nat) (m m' : Mem) (a : AState) (x y fu : Word) (r : List Word),
      exprLvlEqW p n m x y fu = some (r, m') → StageR vis feR m a →
      ConRon.Bridge.CheckOK false env fe a → HW x → HW y →
      ∃ b a', (lvlEq fu.toNat (decE x) (decE y)).run a = .ok (b, a') ∧ StageR vis feR m' a' ∧
        IWGrow m m' ∧ decW0B m' r b ∧ ConRon.Bridge.CoreStep env fe a a'
  | 0, m, m', a, x, y, fu, r, hW, _, _, _, _ => by rw [exprLvlEqW.eq_1] at hW; cases hW
  | n + 1, m, m', a, x, y, fu, r, hW, hS, hok, hx, hy => by
    by_cases hf0 : fu = 0
    · rw [exprLvlEqW.abort1 _ _ _ _ _ _ hf0] at hW; cases hW
    obtain ⟨k, hk⟩ : ∃ k, fu.toNat = k + 1 :=
      ⟨fu.toNat - 1, by have : fu.toNat ≠ 0 := fun h => hf0 (UInt64.toNat_inj.mp (by simpa using h)); omega⟩
    have hk1 : (fu - 1).toNat = k := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    rw [hk]
    simp only [lvlEq]
    by_cases hxy : x = y
    · rw [exprLvlEqW.arm1 _ _ _ _ _ _ hf0 hxy] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨true, a, ?_, hS, IWGrow.refl _, by simp [decW0B], ConRon.Bridge.CoreStep.refl hok⟩
      simp [hxy]; rfl
    have e1 : (decE x == decE y) = false := by rw [decE_beq x y hx hy]; simp [hxy]
    by_cases htg' : tagW x ≠ tagW y
    · rw [exprLvlEqW.arm2 _ _ _ _ _ _ hf0 hxy htg'] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B], ConRon.Bridge.CoreStep.refl hok⟩
      simp [e1, decE_tag_beq2 x y hx hy, htg']; rfl
    have htg : tagW x = tagW y := Classical.not_not.mp htg'
    have e2 : ((decE x).tag == (decE y).tag) = true := by rw [decE_tag_beq2 x y hx hy]; simp [htg]
    have hR := hS.check.arena.base
    by_cases h2 : tagW x = 2
    · rw [exprLvlEqW.arm3 _ _ _ _ _ _ hf0 hxy htg h2] at hW
      rcases c1 : callW p n "e_view" [x] m with _ | ⟨r1, m1⟩
      · rw [c1, exprLvlEqW.k_e_view.eq_1] at hW; cases hW
      rw [c1, exprLvlEqW.k_e_view.arm1] at hW
      obtain ⟨hm1, v1, hv1, hr1, ht1⟩ := eView_callW_view hev hR c1
      subst m1
      obtain ⟨rfl, hu1⟩ := viewR_sort hr1 (by rw [ht1, h2])
      rcases c2 : callW p n "e_view" [y] m with _ | ⟨r2, m2⟩
      · rw [c2] at hW; simp [exprLvlEqW.k_e_view_2] at hW
      rw [c2, exprLvlEqW.k_e_view_2.arm1] at hW
      obtain ⟨hm2, v2, hv2, hr2, ht2⟩ := eView_callW_view hev hR c2
      subst m2
      obtain ⟨rfl, hu2⟩ := viewR_sort hr2 (by rw [ht2, ← htg, h2])
      obtain ⟨lu, hdu⟩ := sort_lvl_den hok.state.wf hv1
      obtain ⟨lv, hdv⟩ := sort_lvl_den hok.state.wf hv2
      rcases c3 : callW p n "lvl_eq" [r1.tail.headD 0, r2.tail.headD 0] m with _ | ⟨r3, m3⟩
      · rw [c3, exprLvlEqW.k_lvl_eq.none] at hW; cases hW
      obtain ⟨a1, a2, h1, h2', h3, hS3, hg3, hc3⟩ := lvlEq_step hL hS hok hu1 hu2 hdu hdv c3
      rw [c3, exprLvlEqW.k_lvl_eq.arm1] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have es : (Idx.tag (decE x) == ETag.sort) = true := by
        rw [show ETag.sort = UInt32.ofNat 2 from rfl, decE_tag_beq x hx 2 (by decide)]; simp [h2]
      refine ⟨lu.isEquiv lv == some true, a2, ?_, hS3, hg3, ?_, hc3⟩
      · simp only [e1, e2, es, ite_true, Bool.false_eq_true, ite_false]
        rw [StateT.run_bind, viewSort_run', irViewSort (by rw [decE_tag x hx, h2]; rfl) hv1,
          except_ok_bind, StateT.run_bind, viewSort_run',
          irViewSort (by rw [decE_tag y hy, ← htg, h2]; rfl) hv2, except_ok_bind]
        dsimp only
        rw [StateT.run_bind, h1, except_ok_bind, StateT.run_bind, h2', except_ok_bind]
        rfl
      · rw [h3]; exact decW0B_enc _ _
    have tb := irTagB x hx
    have es : (Idx.tag (decE x) == ETag.sort) = false := by
      rw [tb ETag.sort 2 rfl (by decide)]; simpa using h2
    by_cases h3 : tagW x = 3
    · rw [exprLvlEqW.arm4 _ _ _ _ _ _ hf0 hxy htg h2 h3] at hW
      rcases c1 : callW p n "e_view" [x] m with _ | ⟨r1, m1⟩
      · rw [c1, exprLvlEqW.k_e_view_3.none] at hW; cases hW
      rw [c1, exprLvlEqW.k_e_view_3.arm1] at hW
      obtain ⟨hm1, v1, hv1, hr1, ht1⟩ := eView_callW_view hev hR c1
      subst m1
      obtain ⟨rfl, hn1, hu1⟩ := irVR_const hr1 (by rw [ht1, h3])
      rcases c2 : callW p n "e_view" [y] m with _ | ⟨r2, m2⟩
      · rw [c2, exprLvlEqW.k_e_view_4.none] at hW; cases hW
      obtain ⟨hm2, v2, hv2, hr2, ht2⟩ := eView_callW_view hev hR c2
      subst m2
      obtain ⟨rfl, hn2, hu2⟩ := irVR_const hr2 (by rw [ht2, ← htg, h3])
      rw [c2] at hW
      have ec : (Idx.tag (decE x) == ETag.const) = true := by
        rw [tb ETag.const 3 rfl (by decide)]; simpa using h3
      have tw : (decE x).tag = ETag.const := by rw [decE_tag x hx, h3]; rfl
      have tw' : (decE y).tag = ETag.const := by rw [decE_tag y hy, ← htg, h3]; rfl
      have hpre : (viewConst (decE x)).run a =
          .ok (some (decI (r1.tail.headD 0), decI (r1.tail.tail.headD 0)), a) := by
        rw [viewConst_run', irViewConst tw hv1]
      have hpre' : (viewConst (decE y)).run a =
          .ok (some (decI (r2.tail.headD 0), decI (r2.tail.tail.headD 0)), a) := by
        rw [viewConst_run', irViewConst tw' hv2]
      by_cases hne : r1.tail.headD 0 ≠ r2.tail.headD 0
      · rw [exprLvlEqW.k_e_view_4.arm1 _ _ _ _ _ _ hne] at hW
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B], ConRon.Bridge.CoreStep.refl hok⟩
        simp only [e1, e2, es, ec, ite_true, Bool.false_eq_true, ite_false]
        rw [StateT.run_bind, hpre, except_ok_bind, StateT.run_bind, hpre', except_ok_bind]
        dsimp only
        have : (decI (r1.tail.headD 0) == (decI (r2.tail.headD 0) : NIdx)) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => hne (decI_inj hn1 hn2 e)
        simp only [this, Bool.false_eq_true, ite_false]; rfl
      have heq : r1.tail.headD 0 = r2.tail.headD 0 := Classical.not_not.mp hne
      rw [exprLvlEqW.k_e_view_4.arm2 _ _ _ _ _ _ heq] at hW
      obtain ⟨ls1, hd1⟩ := const_lvls_den hok.state.wf hv1
      obtain ⟨ls2, hd2⟩ := const_lvls_den hok.state.wf hv2
      rcases c3 : callW p n "lvls_eq" [r1.tail.tail.headD 0, r2.tail.tail.headD 0] m with _ | ⟨r3, m3⟩
      · rw [c3, exprLvlEqW.k_lvl_eq.none] at hW; cases hW
      obtain ⟨a1, a2, h1, h2', h3', hS3, hg3, hc3⟩ := lvlsEq_step hL hS hok hu1 hu2 hd1 hd2 c3
      rw [c3, exprLvlEqW.k_lvl_eq.arm1] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨ConLeche.Level.isEquivList ls1 ls2 == some true, a2, ?_, hS3, hg3, by rw [h3']; exact decW0B_enc _ _, hc3⟩
      simp only [e1, e2, es, ec, ite_true, Bool.false_eq_true, ite_false]
      rw [StateT.run_bind, hpre, except_ok_bind, StateT.run_bind, hpre', except_ok_bind]
      dsimp only
      simp only [heq, beq_self_eq_true, ite_true]
      rw [StateT.run_bind, h1, except_ok_bind, StateT.run_bind, h2', except_ok_bind]
      rfl
    have ec : (Idx.tag (decE x) == ETag.const) = false := by
      rw [tb ETag.const 3 rfl (by decide)]; simpa using h3
    by_cases h456 : tagW x = 4 ∨ tagW x = 5 ∨ tagW x = 6
    · rw [exprLvlEqW.arm5 _ _ _ _ _ _ hf0 hxy htg h2 h3 h456] at hW
      rcases c1 : callW p n "e_view" [x] m with _ | ⟨r1, m1⟩
      · rw [c1, exprLvlEqW.k_e_view_5.none] at hW; cases hW
      rw [c1, exprLvlEqW.k_e_view_5.arm1] at hW
      obtain ⟨hm1, v1, hv1, hr1, ht1⟩ := eView_callW_view hev hR c1
      subst m1
      obtain ⟨ha1, hb1, hv1'⟩ := irVR_two hr1 (by rw [ht1]; exact h456)
      rcases c2 : callW p n "e_view" [y] m with _ | ⟨r2, m2⟩
      · rw [c2, exprLvlEqW.k_e_view_6.none] at hW; cases hW
      obtain ⟨hm2, v2, hv2, hr2, ht2⟩ := eView_callW_view hev hR c2
      subst m2
      obtain ⟨ha2, hb2, hv2'⟩ := irVR_two hr2 (by rw [ht2, ← htg]; exact h456)
      rw [c2, exprLvlEqW.k_e_view_6.eq_2] at hW
      rcases c3 : exprLvlEqW p n m (r1.tail.headD 0) (r2.tail.headD 0) (fu - 1) with _ | ⟨r3, m3⟩
      · rw [c3, exprLvlEqW.k_expr_lvl_eq.none] at hW; cases hW
      obtain ⟨b3, a3, h3r, hS3, hg3, hd3, hc3⟩ := exprLvlEq_run hev hL n _ _ _ _ _ _ _ c3 hS hok ha1 ha2
      rw [hk1] at h3r
      obtain ⟨b, a', hrec, hpost⟩ : ∃ b a', (do
          let z ← lvlEq k (decE (r1.tail.headD 0)) (decE (r2.tail.headD 0))
          if z = true then lvlEq k (decE (r1.tail.tail.headD 0)) (decE (r2.tail.tail.headD 0))
          else pure false : AM Bool).run a = .ok (b, a') ∧
          StageR vis feR m' a' ∧ IWGrow m m' ∧ decW0B m' r b ∧ ConRon.Bridge.CoreStep env fe a a' := by
        rw [StateT.run_bind, h3r, except_ok_bind]
        by_cases hz : r3.headD 0 = 0
        · rw [c3, exprLvlEqW.k_expr_lvl_eq.arm1 _ _ _ _ _ _ _ hz] at hW
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
          have hb3 : b3 = false := by have := hd3.1; rw [hz] at this; simpa using this.symm
          subst hb3
          exact ⟨false, a3, rfl, hS3, hg3, by simp [decW0B], hc3⟩
        rw [c3, exprLvlEqW.k_expr_lvl_eq.arm2 _ _ _ _ _ _ _ hz] at hW
        have hb3 : b3 = true := by rw [← hd3.1]; exact bne_iff_ne.mpr hz
        subst hb3
        rcases c4 : exprLvlEqW p n m3 (r1.tail.tail.headD 0) (r2.tail.tail.headD 0) (fu - 1) with _ | ⟨r4, m4⟩
        · rw [c4, exprLvlEqW.k_expr_lvl_eq_2.none] at hW; cases hW
        obtain ⟨b4, a4, h4r, hS4, hg4, hd4, hc4⟩ :=
          exprLvlEq_run hev hL n _ _ _ _ _ _ _ c4 hS3 hc3.ok hb1 hb2
        rw [hk1] at h4r
        rw [c4, exprLvlEqW.k_expr_lvl_eq_2.arm1] at hW
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        exact ⟨b4, a4, by simpa using h4r, hS4, hg3.trans hg4, hd4, hc3.trans hc4⟩
      refine ⟨b, a', ?_, hpost⟩
      simp only [e1, e2, es, ec, Bool.false_eq_true, ite_false, ite_true]
      have t4 := tb ETag.app 4 rfl (by decide)
      have t5 := tb ETag.lam 5 rfl (by decide)
      have t6 := tb ETag.forallE 6 rfl (by decide)
      rcases hv1' with ⟨g1, rfl⟩ | ⟨g1, rfl⟩ | ⟨g1, rfl⟩ <;>
        rcases hv2' with ⟨g2, rfl⟩ | ⟨g2, rfl⟩ | ⟨g2, rfl⟩ <;>
        (rw [ht1] at g1; rw [ht2, ← htg] at g2; rw [g1] at g2) <;>
        (try (exfalso; revert g2; decide)) <;> rw [g1] at t4 t5 t6 <;>
        simp only [irOfNat4, irOfNat5, irOfNat6] at t4 t5 t6
      · simp only [t4, decide_true, ite_true]
        rw [StateT.run_bind, viewApp_run', irViewApp hv1, except_ok_bind, StateT.run_bind,
          viewApp_run', irViewApp hv2, except_ok_bind]
        exact hrec
      · simp only [t4, t5, t6, decide_true, Bool.true_or, ite_true,
          show decide ((5 : Word) = 4) = false from rfl, Bool.false_eq_true, ite_false]
        rw [StateT.run_bind, viewBind_run', ConRon.Bridge.viewBind_of_view hv1 (Or.inl rfl), except_ok_bind,
          StateT.run_bind, viewBind_run', ConRon.Bridge.viewBind_of_view hv2 (Or.inl rfl), except_ok_bind]
        exact hrec
      · simp only [t4, t5, t6, decide_true, Bool.or_true, ite_true,
          show decide ((6 : Word) = 4) = false from rfl, show decide ((6 : Word) = 5) = false from rfl,
          Bool.false_eq_true, ite_false]
        rw [StateT.run_bind, viewBind_run', ConRon.Bridge.viewBind_of_view hv1 (Or.inr rfl), except_ok_bind,
          StateT.run_bind, viewBind_run', ConRon.Bridge.viewBind_of_view hv2 (Or.inr rfl), except_ok_bind]
        exact hrec
    sorry

end lvleq

end L.Ind
