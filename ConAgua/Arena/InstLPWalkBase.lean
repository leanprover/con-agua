import ConAgua.Arena.CoreWalks
import ConAgua.Arena.InstLP
import ConAgua.Arena.LevelInternRef
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The `instLP` walk under `CoreS`: the invariants and the steps

The walk's refinement (`InstLPWalkRef*.lean`) runs under `CoreS` and three more facts:

* `ILWMemo m a`: the three walk memos (arrays 52‥54) hold the twin's maps `instLPC`,
  `instLPLC`, `instLPLsC` (handle values below `2^32`), and the two level memos' values read back;
* `ILWEnv`: the substitution's keys are a name slice on the spine stack below its top, its values
  a level slice of the pool below the pool top, read back as `ks`/`vs`;
* across every step the twin's level stores only grow and the name store stays (`ILWGrow`).

Each L step keeps them: an expression interning (the twin keeps its caches, pins, memos and level
stores), a level interning (`lv_sub_int`: `LvlStep`), a list interning (`spn_ls`: the pool grows,
`LsStep`), a memo write, a stack write above the top.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## The level memos' keys and values -/

theorem lpSch_wf : lpSch.WF := ⟨by decide, by decide⟩
theorem lplSch_wf : lplSch.WF := ⟨by decide, by decide⟩
theorem lplsSch_wf : lplsSch.WF := ⟨by decide, by decide⟩

/-! ## The invariants -/

/-- **The walk memos hold the twin's maps.** -/
structure ILWMemo (m : Mem) (a : AState) : Prop where
  lp : MemoRV lpSch lfKey VH m a.memos.instLPC
  lpl : MemoRV lplSch ilKey VI m a.memos.instLPLC
  lpls : MemoRV lplsSch ilKey VI m a.memos.instLPLsC
  lplDen : ∀ k v : LIdx, a.memos.instLPLC[k]? = some v → ∃ l, denoteL a.store.ls v = some l
  lplsDen : ∀ k v : LsIdx, a.memos.instLPLsC[k]? = some v → ∃ ls, denoteLs a.store.lss v = some ls

/-- **The twin's level stores only grew, the name store is kept.** -/
structure ILWGrow (a a' : AState) : Prop where
  ext : LsExt a.store.lss a'.store.lss
  ns : a'.store.lss.ls.ns = a.store.lss.ls.ns

theorem ILWGrow.refl (a : AState) : ILWGrow a a := ⟨LsExt.refl _, rfl⟩

theorem ILWGrow.trans {a₁ a₂ a₃ : AState} (h₁ : ILWGrow a₁ a₂) (h₂ : ILWGrow a₂ a₃) : ILWGrow a₁ a₃ :=
  ⟨h₁.ext.trans h₂.ext, h₂.ns.trans h₁.ns⟩

theorem ILWGrow.of_lss {a a' : AState} (h : a'.store.lss = a.store.lss) : ILWGrow a a' :=
  ⟨by rw [h]; exact LsExt.refl _, by rw [h]⟩

/-- **The substitution**: the keys on the stack below its top, the values in the pool below its
top. -/
structure ILWEnv (m : Mem) (a : AState) (ko kc vo vc : Word) (ks : List Name) (us : List LIdx)
    (vs : List Level) : Prop where
  keys : NmsR (nameN a.store.lss.ls.ns) m SPN ko kc ks
  ktop : ko.toNat + kc.toNat ≤ (spTop m).toNat
  vals : sliceL (vpool m) vo.toNat vc.toNat = lsWords us
  vtop : vo.toNat + vc.toNat ≤ m.top.toNat
  vden : denoteLList a.store.ls us = some vs

/-- A name slice survives a writer that keeps the array below a bound past it. -/
theorem NmsR.of_below {N : Word → Name → Prop} {m m' : Mem} {A : ArrId} {t : Nat} (ht : t < 2 ^ 64)
    (hb : ∀ i : Word, i.toNat < t → rdW (m'.arr64 A) i = rdW (m.arr64 A) i) :
    ∀ {o k : Word} {xs : List Name}, NmsR N m A o k xs → o.toNat + k.toNat ≤ t →
      NmsR N m' A o k xs := by
  intro o k xs h ht
  induction h with
  | nil => exact .nil
  | @cons o k x xs hk0 hx _ ih =>
    have hk1 : 1 ≤ k.toNat := by
      rcases Nat.eq_zero_or_pos k.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hk0
      · omega
    have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_succ_lt (by omega)
    have hkm : (k - 1).toNat = k.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    exact .cons hk0 (by rw [hb o (by omega)]; exact hx) (ih (by rw [ho1, hkm]; omega))

/-- **The substitution survives a step** that keeps the stack below its top, only grows the pool
and the twin's level stores. -/
theorem ILWEnv.keep {m m' : Mem} {a a' : AState} {ko kc vo vc : Word} {ks : List Name}
    {us : List LIdx} {vs : List Level} (h : ILWEnv m a ko kc vo vc ks us vs) (hk : StackKept m m')
    (hg : ILWGrow a a') : ILWEnv m' a' ko kc vo vc ks us vs := by
  refine ⟨?_, by rw [hk.top]; exact h.ktop, ?_, Nat.le_trans h.vtop hk.pool.top,
    denoteLList_mono hg.ext.ls _ _ h.vden⟩
  · rw [hg.ns]
    exact NmsR.of_below (t := (spTop m).toNat) (spTop m).toNat_lt
      (fun i hi => hk.below i (UInt64.lt_iff_toNat_lt.mpr hi)) h.keys h.ktop
  · rw [Agree.sliceL _ _ _ _ _ hk.pool.below h.vtop]; exact h.vals

/-! ## The twin's walk memos -/

theorem instLPGet_run (k : EIdx × Nat) (a : AState) : (instLPGet k).run a = .ok (a.memos.instLPC[k]?, a) :=
  rfl
theorem instLPSet_run (k : EIdx × Nat) (r : EIdx) (a : AState) :
    (instLPSet k r).run a =
      .ok ((), { a with memos := { a.memos with instLPC := a.memos.instLPC.insert k r } }) := rfl
theorem instLPLGet_run (h : LIdx) (a : AState) : (instLPLGet h).run a = .ok (a.memos.instLPLC[h]?, a) :=
  rfl
theorem instLPLSet_run (h r : LIdx) (a : AState) :
    (instLPLSet h r).run a =
      .ok ((), { a with memos := { a.memos with instLPLC := a.memos.instLPLC.insert h r } }) := rfl
theorem instLPLsGet_run (h : LsIdx) (a : AState) :
    (instLPLsGet h).run a = .ok (a.memos.instLPLsC[h]?, a) := rfl
theorem instLPLsSet_run (h r : LsIdx) (a : AState) :
    (instLPLsSet h r).run a =
      .ok ((), { a with memos := { a.memos with instLPLsC := a.memos.instLPLsC.insert h r } }) := rfl
theorem instLPClear_run (a : AState) :
    instLPClear.run a =
      .ok ((), { a with memos := { a.memos with instLPC := ∅, instLPLC := ∅, instLPLsC := ∅ } }) := rfl

section steps
variable {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
  {M : ModeMaps} {eb : Word}

/-- **`CoreS` does not read the walk's three memos.** -/
theorem CoreS.lpMemos (hS : CoreS dn m a vis fe M eb) (X : Std.HashMap (EIdx × Nat) EIdx)
    (Y : Std.HashMap LIdx LIdx) (Z : Std.HashMap LsIdx LsIdx) :
    CoreS dn m { a with memos := { a.memos with instLPC := X, instLPLC := Y, instLPLsC := Z } } vis fe M eb := by
  obtain ⟨hR, hD⟩ := hS.arena
  exact ⟨⟨⟨hR.lit, hR.app, hR.sort, hR.const, hR.letE, hR.bvar, hR.fvar, hR.lam, hR.forallE, hR.proj,
    hR.zero, hR.succ, hR.max, hR.imax, hR.param, hR.ls, hR.nanon, hR.nstr, hR.nnum,
    ⟨hR.memos.bvar, hR.memos.lift, hR.memos.inst1, hR.memos.fvar⟩, hR.zeroHp, hR.paramHp,
    hR.succHp, hR.maxHp, hR.imaxHp, hR.lsHp, hR.sortLp, hR.constLp, hR.fvarLp⟩,
    DerR.of_store _ _ _ hD rfl⟩, hS.core, hS.pins, hS.env, hS.readL, hS.readLs, hS.nwf, hS.erec, hS.spn,
    hS.memos, hS.bstk, hS.den.caches rfl rfl rfl, hS.mode⟩

set_option maxRecDepth 8000 in
/-- **A write of one of the walk's memos** (`find; put` or `clear`) keeps `CoreS`, the walk
memos given. -/
theorem CoreS.frameLP (S : MemoSch) (h3 : S = lpSch ∨ S = lplSch ∨ S = lplsSch)
    (hS : CoreS dn m a vis fe M eb) (hf : MemFrame [S.arr] [S.cs, S.cs + 1] m m')
    (hmem : CoreMemos m') : CoreS dn m' a vis fe M eb ∧ StackKept m m' := by
  rcases h3 with rfl | rfl | rfl <;>
  exact hS.of_walk ⟨hS.arena.1.frame
      (by simp [arenaArrs, storeArrs, memoArrs, LPMEMO, LPLMEMO, LPLSMEMO, BMEMO, LMEMO, IMEMO, FRMEMO])
      (by simp [arenaCtl, storeCtl, memoCtl]) hf,
    DerR.frameM _ _ m m' hf (by simp [LPMEMO, LPLMEMO, LPLSMEMO]) a hS.arena.2⟩
    rfl hf (by simp [LPMEMO, LPLMEMO, LPLSMEMO])
    (by simp) hmem
    (by simp [LPMEMO, LPLMEMO, LPLSMEMO, POOL])
    (by simp)
    (by simp [tier1, tierOff, LPMEMO, LPLMEMO, LPLSMEMO, SOREC, CREC])
    (by simp)

end steps

/-! ## The walk memos across the steps -/

theorem vstable_VH : VStable lpSch VH := fun _ _ _ _ _ h => h
theorem vstable_VI {k : IdxKind} (S : MemoSch) : VStable S (VI (k := k)) := fun _ _ _ _ _ h => h

/-- **The walk memos across a writer of other arrays**, the twin's memos kept and its level stores
grown. -/
theorem ILWMemo.frame {A : List ArrId} {C : List Word} {m m' : Mem} {a a' : AState}
    (h : ILWMemo m a) (hf : MemFrame A C m m')
    (hA : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A)
    (hC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C)
    (hme : a'.memos = a.memos) (hg : ILWGrow a a') : ILWMemo m' a' := by
  refine ⟨?_, ?_, ?_, fun k v hk => ?_, fun k v hk => ?_⟩
  · rw [hme]; exact memoRV_frame lpSch lpSch_wf lfKey VH A C hA.1 hC.1 m m' hf (fun _ _ h => h) _ h.lp
  · rw [hme]; exact memoRV_frame lplSch lplSch_wf ilKey _ A C hA.2.1 hC.2.1 m m' hf (fun _ _ h => h) _ h.lpl
  · rw [hme]; exact memoRV_frame lplsSch lplsSch_wf ilKey _ A C hA.2.2 hC.2.2 m m' hf (fun _ _ h => h) _ h.lpls
  · rw [hme] at hk; obtain ⟨l, hl⟩ := h.lplDen k v hk; exact ⟨l, hg.ext.ls.lvl _ _ hl⟩
  · rw [hme] at hk; obtain ⟨l, hl⟩ := h.lplsDen k v hk; exact ⟨l, hg.ext.lst _ _ hl⟩

/-- **An arm's result recorded** in `instLPC`. -/
theorem ILWMemo.setLP {m m' : Mem} {a : AState} (h : ILWMemo m a) (hw r : Word) (hh : HW hw) (hr : HW r)
    (hs : msetG lpSch m hw 0 r = some m') :
    ILWMemo m' { a with memos := { a.memos with
      instLPC := a.memos.instLPC.insert (decE hw, 0) (decE r) } } := by
  have hf := msetG_frame lpSch lpSch_wf m m' hw 0 r hs
  exact ⟨memoRV_set lpSch lpSch_wf lfKey VH vstable_VH m _ h.lp hw 0 r hh (decE r) ⟨rfl, hr⟩ m' hs,
    memoRV_frame lplSch lplSch_wf ilKey _ _ _ (by simp [LPMEMO, LPLMEMO]) (by simp) m m' hf (fun _ _ h => h) _ h.lpl,
    memoRV_frame lplsSch lplsSch_wf ilKey _ _ _ (by simp [LPMEMO, LPLSMEMO]) (by simp) m m' hf (fun _ _ h => h) _ h.lpls,
    h.lplDen, h.lplsDen⟩

/-- **A level substitution recorded** in `instLPLC`, its value reading back. -/
theorem ILWMemo.setLPL {m m' : Mem} {a : AState} (h : ILWMemo m a) (u r : Word) (hu : HW u) (hr : HW r)
    (hd : ∃ l, denoteL a.store.ls (decI r) = some l) (hs : msetG lplSch m u 0 r = some m') :
    ILWMemo m' { a with memos := { a.memos with
      instLPLC := a.memos.instLPLC.insert (decI u) (decI r) } } := by
  have hf := msetG_frame lplSch lplSch_wf m m' u 0 r hs
  refine ⟨memoRV_frame lpSch lpSch_wf lfKey VH _ _ (by simp [LPMEMO, LPLMEMO]) (by simp) m m' hf (fun _ _ h => h) _ h.lp,
    memoRV_set lplSch lplSch_wf ilKey _ (vstable_VI _) m _ h.lpl u 0 r ⟨hu, rfl⟩ (decI r) ⟨rfl, hr⟩ m' hs,
    memoRV_frame lplsSch lplsSch_wf ilKey _ _ _ (by simp [LPLMEMO, LPLSMEMO]) (by simp) m m' hf (fun _ _ h => h) _ h.lpls,
    fun k v hk => ?_, h.lplsDen⟩
  simp only [Std.HashMap.getElem?_insert] at hk
  split at hk
  · cases hk; exact hd
  · exact h.lplDen k v hk

/-- **A level-list substitution recorded** in `instLPLsC`, its value reading back. -/
theorem ILWMemo.setLPLs {m m' : Mem} {a : AState} (h : ILWMemo m a) (u r : Word) (hu : HW u) (hr : HW r)
    (hd : ∃ ls, denoteLs a.store.lss (decI r) = some ls) (hs : msetG lplsSch m u 0 r = some m') :
    ILWMemo m' { a with memos := { a.memos with
      instLPLsC := a.memos.instLPLsC.insert (decI u) (decI r) } } := by
  have hf := msetG_frame lplsSch lplsSch_wf m m' u 0 r hs
  refine ⟨memoRV_frame lpSch lpSch_wf lfKey VH _ _ (by simp [LPMEMO, LPLSMEMO]) (by simp) m m' hf (fun _ _ h => h) _ h.lp,
    memoRV_frame lplSch lplSch_wf ilKey _ _ _ (by simp [LPLMEMO, LPLSMEMO]) (by simp) m m' hf (fun _ _ h => h) _ h.lpl,
    memoRV_set lplsSch lplsSch_wf ilKey _ (vstable_VI _) m _ h.lpls u 0 r ⟨hu, rfl⟩ (decI r) ⟨rfl, hr⟩ m' hs,
    h.lplDen, fun k v hk => ?_⟩
  simp only [Std.HashMap.getElem?_insert] at hk
  split at hk
  · cases hk; exact hd
  · exact h.lplsDen k v hk

/-! ## The clears -/

theorem ILWMemo.lpMemos {m : Mem} {a : AState} (h : ILWMemo m a) : LPMemos m :=
  ⟨⟨_, h.lp⟩, ⟨_, h.lpl⟩, ⟨_, h.lpls⟩⟩

/-- Another memo's clear keeps a memo. -/
theorem memoRV_clear_other {κ : Type} [BEq κ] [Hashable κ] {ν : Type}
    (S T : MemoSch) (hT : T.WF) (K : MemoKey κ) (VR : Mem → Word → ν → Prop) {m : Mem}
    {mp : Std.HashMap κ ν} (hne : T.arr ≠ CTL ∧ T.cs ≠ S.cs ∧ T.cs ≠ S.cs + 1)
    (hV : ∀ m₁ m₂ w v, VR m₁ w v → VR m₂ w v) (h : MemoRV T K VR m mp) :
    MemoRV T K VR (mclearG S m) mp :=
  memoRV_frame T hT K VR [] [S.cs, S.cs + 1] (by simp)
    (by simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]; exact hne.2) m _
    (mclearG_frame S m) (fun w v => hV m _ w v) mp h

theorem lp_ne_lpl : LPMEMO ≠ CTL ∧ lpSch.cs ≠ lplSch.cs ∧ lpSch.cs ≠ lplSch.cs + 1 := by decide
theorem lp_ne_lpls : LPMEMO ≠ CTL ∧ lpSch.cs ≠ lplsSch.cs ∧ lpSch.cs ≠ lplsSch.cs + 1 := by decide
theorem lpl_ne_lp : LPLMEMO ≠ CTL ∧ lplSch.cs ≠ lpSch.cs ∧ lplSch.cs ≠ lpSch.cs + 1 := by decide
theorem lpl_ne_lpls : LPLMEMO ≠ CTL ∧ lplSch.cs ≠ lplsSch.cs ∧ lplSch.cs ≠ lplsSch.cs + 1 := by decide
theorem lpls_ne_lp : LPLSMEMO ≠ CTL ∧ lplsSch.cs ≠ lpSch.cs ∧ lplsSch.cs ≠ lpSch.cs + 1 := by decide
theorem lpls_ne_lpl : LPLSMEMO ≠ CTL ∧ lplsSch.cs ≠ lplSch.cs ∧ lplsSch.cs ≠ lplSch.cs + 1 := by decide

/-- **The three clears** (`ilp_clear`, `ilpl_clear`, `ilpls_clear`, in this order) leave the
three memos empty. -/
theorem ilw_clears {m : Mem} (h : LPMemos m)
    (h1 : rdW (m.arr64 CTL) lpSch.cs + 2 ≠ 0)
    (h2 : rdW ((mclearG lpSch m).arr64 CTL) lplSch.cs + 2 ≠ 0)
    (h3 : rdW ((mclearG lplSch (mclearG lpSch m)).arr64 CTL) lplsSch.cs + 2 ≠ 0) (a : AState) :
    ILWMemo (mclearG lplsSch (mclearG lplSch (mclearG lpSch m)))
      { a with memos := { a.memos with instLPC := ∅, instLPLC := ∅, instLPLsC := ∅ } } := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ := h
  have x1 := memoRV_clear lpSch lpSch_wf lfKey VH m x hx h1
  have y1 := memoRV_clear_other lpSch lplSch lplSch_wf ilKey VI lpl_ne_lp (fun _ _ _ _ h => h) hy
  have z1 := memoRV_clear_other lpSch lplsSch lplsSch_wf ilKey VI lpls_ne_lp (fun _ _ _ _ h => h) hz
  have x2 := memoRV_clear_other lplSch lpSch lpSch_wf lfKey VH lp_ne_lpl (fun _ _ _ _ h => h) x1
  have y2 := memoRV_clear lplSch lplSch_wf ilKey VI _ y y1 h2
  have z2 := memoRV_clear_other lplSch lplsSch lplsSch_wf ilKey VI lpls_ne_lpl (fun _ _ _ _ h => h) z1
  exact ⟨memoRV_clear_other lplsSch lpSch lpSch_wf lfKey VH lp_ne_lpls (fun _ _ _ _ h => h) x2,
    memoRV_clear_other lplsSch lplSch lplSch_wf ilKey VI lpl_ne_lpls (fun _ _ _ _ h => h) y2,
    memoRV_clear lplsSch lplsSch_wf ilKey VI _ z z2 h3,
    fun k v hk => by simp at hk, fun k v hk => by simp at hk⟩

/-! ## The expression interning steps -/

/-- The twin's walk memos. -/
def memP (a : AState) : Memos := a.memos

theorem keeps_memP_internNodeE (v : ENodeView) : Keeps memP (internNodeE v) := by prim_keeps internNodeE
theorem keeps_memP_internLamE (ty b : EIdx) : Keeps memP (internLamE ty b) := by prim_keeps internLamE
theorem keeps_memP_internForallEE (ty b : EIdx) : Keeps memP (internForallEE ty b) := by
  prim_keeps internForallEE
theorem keeps_memP_internE (v : ENodeView) : Keeps memP (internE v) := by
  cases v <;> simp only [internE] <;>
    first | exact keeps_memP_internNodeE _ | exact keeps_memP_internLamE _ _ | exact keeps_memP_internForallEE _ _

/-- **The walk's invariants across an expression interning** (the twin keeps its memos and level
stores; the memory write avoids the walk memos). -/
theorem ILWMemo.of_internE {m m' : Mem} {a : AState} {v : ENodeView} {A : List ArrId} {C : List Word}
    (h : ILWMemo m a) (hok : AM.ok (internE v) a) (hf : MemFrame A C m m')
    (hA : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A := by decide)
    (hC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C := by decide) :
    ILWMemo m' (AM.st (internE v) a) ∧ ILWGrow a (AM.st (internE v) a) := by
  have hrun := AM.run_of_ok _ _ hok
  have hk := Keeps.run (keepsW_internE v) hrun
  have hme : (AM.st (internE v) a).memos = a.memos := Keeps.run (keeps_memP_internE v) hrun
  simp only [cpl, Prod.mk.injEq] at hk
  have hg := ILWGrow.of_lss hk.2.2
  exact ⟨h.frame hf hA hC hme hg, hg⟩

/-! ## The level arms' statements (helper `whnf4-ilp-lev`) -/

/-- **`sl_memo(u, …)` refines `substLMemoAt ks vs u`** under the walk's invariants, `u` a stored
level that reads back; the result reads back too. -/
def SlMemoOK (p : Prog) : Prop :=
  ∀ (n : Nat) (m m' : Mem) (a : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb u ko kc vo vc : Word) (ks : List Name) (us : List LIdx) (vs : List Level)
    (rs : List Word),
    CoreS dn m a vis fe M eb → ILWMemo m a → ILWEnv m a ko kc vo vc ks us vs → HW u →
    (∃ l, denoteL a.store.ls (decI u) = some l) →
    callW p n "sl_memo" [u, ko, kc, vo, vc] m = some (rs, m') →
    ∃ a', (substLMemoAt ks vs (decI u)).run a = .ok (decI (rs.headD 0), a') ∧
      CoreAfter dn m m' a' vis fe M eb ∧ ILWMemo m' a' ∧ ILWGrow a a' ∧ HW (rs.headD 0) ∧
      ∃ l, denoteL a'.store.ls (decI (rs.headD 0)) = some l

/-- **`sls_memo(w, …)` refines `substLsMemoAt ks vs w`** under the walk's invariants, `w` a stored
level list that reads back; the result reads back too. -/
def SlsMemoOK (p : Prog) : Prop :=
  ∀ (n : Nat) (m m' : Mem) (a : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb w ko kc vo vc : Word) (ks : List Name) (us : List LIdx) (vs : List Level)
    (rs : List Word),
    CoreS dn m a vis fe M eb → ILWMemo m a → ILWEnv m a ko kc vo vc ks us vs → HW w →
    (∃ ls, denoteLs a.store.lss (decI w) = some ls) →
    callW p n "sls_memo" [w, ko, kc, vo, vc] m = some (rs, m') →
    ∃ a', (substLsMemoAt ks vs (decI w)).run a = .ok (decI (rs.headD 0), a') ∧
      CoreAfter dn m m' a' vis fe M eb ∧ ILWMemo m' a' ∧ ILWGrow a a' ∧ HW (rs.headD 0) ∧
      ∃ ls, denoteLs a'.store.lss (decI (rs.headD 0)) = some ls
