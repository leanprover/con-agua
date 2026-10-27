import ConAgua.Arena.LevelIntern
import ConAgua.Arena.PromoteLRef
import ConAgua.Arena.MemoTree
import ConAgua.Front.StateDR
import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.Rom

/-!
# `lv_intern` refines `internLevel` of the level its pointer denotes

By induction on the level (`LvR`), as `RomLevel.lean`'s `romLevelW_ok`, with two facts the ROM
reader does not need:

* **A stored name re-interns to itself** (`internName_denote_run`): the twin's `internLevel`
  re-interns a `param`'s name, read back from a handle; under `NStoreWF` (`consP`/`consS`/`fresh`)
  the probe finds the handle, and the state does not change.
* **Interning keeps every level pointer's view** (`ViewsKept`): a store handle's by the twin's
  `LStore.view_intern_mono` (L's view of a handle is the arena's, `lvNodeW_view`/`lvNodeW_store`),
  a heap node's because the stores do not write the heap. So the second child's `LvR` survives
  the first child's interning (`LvR.of_view`).
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

open L.Rom (StoreA StoreC frame_store)

/-! ## A stored name re-interns to itself -/

theorem NStore.find?_of_view {st : NStore} (hwf : NStoreWF st) {i : NIdx} {v : NNodeView}
    (hv : st.view i = some v) : st.find? v = some i := by
  obtain ⟨rk, w⟩ := hwf
  unfold NStore.view at hv
  unfold NStore.find?
  by_cases hp : i.isPersistent = true
  · rw [ite_eq_left hp] at hv
    have : st.pers.find? v = some i := (w.consP v i).mpr ⟨by simp [NStore.view, hp, hv], hp⟩
    rw [this]
  · rw [ite_eq_right hp] at hv
    by_cases hon : st.scratchOn = true
    · rw [ite_eq_left hon] at hv
      have hvi : st.view i = some v := by simp [NStore.view, hp, hon, hv]
      have hs : st.scr.find? v = some i := (w.consS v i).mpr ⟨hvi, by simpa using hp⟩
      rw [w.fresh v i hs, ite_eq_left hon, hs]
    · rw [ite_eq_right hon] at hv; cases hv

/-- **`internNNode` at a stored node's view returns the node and changes nothing.** -/
theorem internNNode_view_run (a : AState) (hwf : NStoreWF a.store.lss.ls.ns) {i : NIdx}
    {v : NNodeView} (hv : a.store.lss.ls.ns.view i = some v) : (internNNode v).run a = .ok (i, a) := by
  have hf := NStore.find?_of_view hwf hv
  simp only [internNNode, EStore.ns] at *
  simp [StateT.run_bind, StateT.run_get, hf]; rfl

/-- **A stored name re-interns to itself**: the twin's `internName` of a handle's readback. -/
theorem internName_denote_run (a : AState) (hwf : NStoreWF a.store.lss.ls.ns) :
    ∀ (f : Nat) (i : NIdx) (nm : Name), denoteNAux a.store.lss.ls.ns f i = some nm →
      (internName nm).run a = .ok (i, a) := by
  intro f
  induction f with
  | zero => intro i nm h; simp [denoteNAux] at h
  | succ f ih =>
    intro i nm h
    simp only [denoteNAux, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    cases v with
    | anonymous =>
      simp only [Option.some.injEq] at h; subst h
      exact internNNode_view_run a hwf hv
    | str p _ | num p _ =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨q, hq, rfl⟩ := h
      have hp := ih p q hq
      simp only [internName, StateT.run_bind, hp]
      exact internNNode_view_run a hwf hv

theorem internName_nameN_run (a : AState) (hwf : NStoreWF a.store.lss.ls.ns) {w : Word} {nm : Name}
    (h : nameN a.store.lss.ls.ns w nm) : (internName nm).run a = .ok (decI w, a) :=
  internName_denote_run a hwf _ _ _ h.2

/-! ## Interning a level node keeps the level views and the name store -/

/-- What a level interning step keeps of the twin's store. -/
def LKeep (a a' : AState) : Prop :=
  (∀ (j : LIdx) (v : LNodeView), a.store.lss.ls.view j = some v → a'.store.lss.ls.view j = some v) ∧
    a'.store.lss.ls.ns = a.store.lss.ls.ns

theorem LKeep.refl (a : AState) : LKeep a a := ⟨fun _ _ h => h, rfl⟩

theorem LKeep.trans {a₁ a₂ a₃ : AState} (h₁ : LKeep a₁ a₂) (h₂ : LKeep a₂ a₃) : LKeep a₁ a₃ :=
  ⟨fun j v h => h₂.1 j v (h₁.1 j v h), h₂.2.trans h₁.2⟩

theorem LStore.intern_ns (st : LStore) (w : LNodeView) : (st.intern w).1.ns = st.ns := by
  simp only [LStore.intern]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

theorem internLNode_keep (w : LNodeView) (a a' : AState) (i : LIdx)
    (h : (internLNode w).run a = .ok (i, a')) : LKeep a a' := by
  unfold internLNode at h
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
  split at h
  · simp only [StateT.run_pure] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact LKeep.refl _
  · split at h <;> split at h <;> first
      | (simp only [StateT.bind, StateT.pure, StateT.run,
          bind, Except.bind, pure, Except.pure] at h
         injection h with h
         obtain ⟨-, rfl⟩ := Prod.mk.inj h
         exact ⟨fun j v hv => LStore.view_intern_mono _ w hv, LStore.intern_ns _ w⟩)
      | simp [fail, throwThe, MonadExceptOf.throw, StateT.run, bind, StateT.lift,
          Except.bind] at h

/-! ## Level pointers keep their views across the store's interning -/

/-- The level store's arrays: every level interning writes only there. -/
abbrev lvArrs : List ArrId := [ZREC, ZSLOT, SREC, SSLOT, MREC, MSLOT, IREC, ISLOT, PREC, PSLOT, SHP, MHP, IHP,
  tier1 ZREC, tier1 ZSLOT, tier1 SREC, tier1 SSLOT, tier1 MREC, tier1 MSLOT, tier1 IREC, tier1 ISLOT,
  tier1 PREC, tier1 PSLOT, tier1 SHP, tier1 MHP, tier1 IHP]
/-- The level store's counts. -/
abbrev lvCtl : List Word := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

section
set_option maxRecDepth 4000
theorem lvSch_sub : (∀ b ∈ [zeroSch.ra, tier1 zeroSch.ra, zeroSch.sa, tier1 zeroSch.sa], b ∈ lvArrs) ∧ (∀ x ∈ [zeroSch.ca, zeroSch.ca + 1], x ∈ lvCtl) ∧
    (∀ b ∈ [succSch.ra, tier1 succSch.ra, succSch.sa, tier1 succSch.sa, SHP, tier1 SHP], b ∈ lvArrs) ∧ (∀ x ∈ [succSch.ca, succSch.ca + 1], x ∈ lvCtl) ∧
    (∀ b ∈ [maxSch.ra, tier1 maxSch.ra, maxSch.sa, tier1 maxSch.sa, MHP, tier1 MHP], b ∈ lvArrs) ∧ (∀ x ∈ [maxSch.ca, maxSch.ca + 1], x ∈ lvCtl) ∧
    (∀ b ∈ [imaxSch.ra, tier1 imaxSch.ra, imaxSch.sa, tier1 imaxSch.sa, IHP, tier1 IHP], b ∈ lvArrs) ∧ (∀ x ∈ [imaxSch.ca, imaxSch.ca + 1], x ∈ lvCtl) ∧
    (∀ b ∈ [paramSch.ra, tier1 paramSch.ra, paramSch.sa, tier1 paramSch.sa], b ∈ lvArrs) ∧ (∀ x ∈ [paramSch.ca, paramSch.ca + 1], x ∈ lvCtl) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [lvArrs, lvCtl, zeroSch, succSch, maxSch, imaxSch, paramSch, ZREC, ZSLOT, SREC, SSLOT, SHP, MREC, MSLOT, MHP, IREC, ISLOT, IHP, PREC, PSLOT]
end


/-- Every level pointer that views keeps its view. -/
def ViewsKept (m m' : Mem) : Prop := ∀ q, lvNodeW m q ≠ [] → lvNodeW m' q = lvNodeW m q

theorem ViewsKept.refl (m : Mem) : ViewsKept m m := fun _ _ => rfl

theorem ViewsKept.trans {m₁ m₂ m₃ : Mem} (h₁ : ViewsKept m₁ m₂) (h₂ : ViewsKept m₂ m₃) :
    ViewsKept m₁ m₃ := fun q hq => by
  rw [h₂ q (by rw [h₁ q hq]; exact hq), h₁ q hq]

theorem viewsKept_of {m m' : Mem} {a a' : AState} (hR : ArenaR m a) (hR' : ArenaR m' a')
    (hk : LKeep a a') (hf : MemFrame lvArrs lvCtl m m') : ViewsKept m m' := by
  intro q hq
  by_cases hb : q >>> 32 = 0
  · have hh : q.toNat < 2 ^ 32 := by
      have := congrArg UInt64.toNat hb
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow] at this
      have := q.toNat_lt; omega
    obtain ⟨v, hv⟩ := lvNodeW_view hR hh hq
    rw [lvNodeW_store hR hh hv, lvNodeW_store hR' hh (hk.1 _ _ hv)]
  · have hLH : m'.arr64 LH = m.arr64 LH := hf.1 LH (by simp [tier1, tierOff, lvArrs, ZREC, ZSLOT, SREC, SSLOT, SHP, MREC, MSLOT, MHP, IREC, ISLOT, IHP, PREC, PSLOT, LH]) (by decide)
    have h192 : rdW (m'.arr64 CTL) 192 = rdW (m.arr64 CTL) 192 := hf.2.1 192 (by simp [lvCtl])
    rw [lvNodeW_heap m' q hb, lvNodeW_heap m q hb, hLH, h192]

/-! ## The refinement -/


/-- One node interned by a store function: the twin's step, the frame, the handle bound. -/
theorem liNode_ok (op : AM LIdx) (W : Mem → Option (Word × Mem))
    (hop : ∀ m a w m', ArenaD m a → W m = some (w, m') →
      AM.ok op a ∧ ArenaD m' (AM.st op a) ∧ AM.res op a = decI w ∧ MemFrame lvArrs lvCtl m m')
    (m : Mem) (a : AState) (h : Word) (m' : Mem) (hA : ArenaD m a)
    (hW : liNodeK (W m) = some (h, m')) :
    AM.ok op a ∧ ArenaD m' (AM.st op a) ∧ AM.res op a = decI h ∧ h.toNat < 2 ^ 32 ∧
      MemFrame lvArrs lvCtl m m' := by
  cases hI : W m with
  | none => rw [hI] at hW; simp [liNodeK] at hW
  | some r =>
    obtain ⟨w, m₁⟩ := r
    rw [hI] at hW
    simp only [liNodeK] at hW
    split at hW
    · simp at hW
    rename_i hlt
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨ok, hR, res, hf⟩ := hop m a _ _ hA hI
    exact ⟨ok, hR, res, by simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt, hf⟩

/-- The twin facts of a node step, as a run. -/
theorem node_run {op : AM LIdx} {a : AState} (ok : AM.ok op a) : op.run a = .ok (AM.res op a, AM.st op a) :=
  AM.run_of_ok _ _ ok

/-- **What a successful `lv_intern` gives.** -/
def LIOk (L : Level) (m : Mem) (a : AState) (h : Word) (m' : Mem) : Prop :=
  ∃ a', (internLevel L).run a = .ok (decI h, a') ∧ ArenaD m' a' ∧ h.toNat < 2 ^ 32 ∧
    MemFrame lvArrs lvCtl m m' ∧ LKeep a a' ∧ ViewsKept m m'

set_option linter.constructorNameAsVariable false in
/-- **The model of `lv_intern` refines `internLevel`** of the level the pointer denotes. -/
@[refines ConRon.Arena.internLevel]
theorem lvInternW_ok (L : Level) :
    ∀ (n : Nat) (m : Mem) (a : AState) (q h : Word) (m' : Mem),
    ArenaD m a → NStoreWF a.store.lss.ls.ns → LvR (nameN a.store.lss.ls.ns) m q L →
    lvInternW n m q = some (h, m') → LIOk L m a h m' := by
  induction L with
  | zero =>
    intro n m a q h m' hA hwf hl hW
    cases n with
    | zero => simp [lvInternW] at hW
    | succ n =>
    have hg : lvG m q = 0 := by cases hl; simp_all [lvG]
    rw [lvInternW_zero n m q hg] at hW
    obtain ⟨ok, hR, res, hlt, hf⟩ := liNode_ok (internLNode .zero) zinternW
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.zero_A m a hA w m' hI
        exact ⟨ok, hR, res, hf.mono lvSch_sub.1 lvSch_sub.2.1⟩)
      m a h m' hA hW
    have hrun := node_run ok
    rw [res] at hrun
    have hk := internLNode_keep _ _ _ _ hrun
    exact ⟨_, hrun, hR, hlt, hf, hk, viewsKept_of hA.1 hR.1 hk hf⟩
  | param nm =>
    intro n m a q h m' hA hwf hl hW
    cases n with
    | zero => simp [lvInternW] at hW
    | succ n =>
    obtain ⟨x, b, hv, hn⟩ : ∃ x b, lvNodeW m q = [4, x, b] ∧ nameN a.store.lss.ls.ns x nm := by
      cases hl with
      | param hv hn => exact ⟨_, _, hv, hn⟩
    have hg : lvG m q = 4 := by simp [lvG, hv]
    have hx : lvA m q = x := by simp [lvA, hv]
    rw [lvInternW_param n m q (by rw [hg]; decide) hg, hx] at hW
    obtain ⟨ok, hR, res, hlt, hf⟩ := liNode_ok (internLNode (.param (decI x))) (fun m => pinternW m x)
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.param_A m a hA w m' x hn.1 hI
        exact ⟨ok, hR, res, hf.mono lvSch_sub.2.2.2.2.2.2.2.2.1 lvSch_sub.2.2.2.2.2.2.2.2.2⟩)
      m a h m' hA hW
    have hrun := node_run ok
    rw [res] at hrun
    have hk := internLNode_keep _ _ _ _ hrun
    have hN := internName_nameN_run a hwf hn
    refine ⟨_, ?_, hR, hlt, hf, hk, viewsKept_of hA.1 hR.1 hk hf⟩
    show (internName nm >>= fun hn => internLNode (.param hn)).run a = _
    rw [StateT.run_bind, hN]; exact hrun
  | succ u ih =>
    intro n m a q h m' hA hwf hl hW
    cases n with
    | zero => simp [lvInternW] at hW
    | succ n =>
    obtain ⟨x, hv, hu⟩ : ∃ x, lvNodeW m q = [1, x, 0] ∧ LvR (nameN a.store.lss.ls.ns) m x u := by
      cases hl with
      | succ hv hu => exact ⟨_, hv, hu⟩
    have hg : lvG m q = 1 := by simp [lvG, hv]
    rw [lvInternW_rec n m q (by rw [hg]; decide) (by rw [hg]; decide), hg,
      show lvA m q = x by simp [lvA, hv]] at hW
    cases hU : lvInternW n m x with
    | none => rw [hU] at hW; simp [liOneK] at hW
    | some r =>
    obtain ⟨hu', m₁⟩ := r
    rw [hU, liOneK_succ n _ _ _ _ rfl] at hW
    obtain ⟨a₁, hrun₁, hA₁, hlt₁, hf₁, hk₁, hvk₁⟩ := ih n m a x hu' m₁ hA hwf hu hU
    obtain ⟨ok, hR, res, hlt, hf⟩ := liNode_ok (internLNode (.succ (decI hu'))) (fun m => sinternW m hu')
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.succ_A m a hA w m' hu' hlt₁ hI
        exact ⟨ok, hR, res, hf.mono lvSch_sub.2.2.1 lvSch_sub.2.2.2.1⟩)
      m₁ a₁ h m' hA₁ hW
    have hrun := node_run ok
    rw [res] at hrun
    have hk := internLNode_keep _ _ _ _ hrun
    refine ⟨_, ?_, hR, hlt, hf₁.trans hf, hk₁.trans hk, hvk₁.trans (viewsKept_of hA₁.1 hR.1 hk hf)⟩
    show (internLevel u >>= fun hu => internLNode (.succ hu)).run a = _
    rw [StateT.run_bind, hrun₁]; exact hrun
  | max u v ihu ihv =>
    intro n m a q h m' hA hwf hl hW
    cases n with
    | zero => simp [lvInternW] at hW
    | succ n =>
    obtain ⟨x, y, hv, hu, hvv⟩ : ∃ x y, lvNodeW m q = [2, x, y] ∧ LvR (nameN a.store.lss.ls.ns) m x u ∧
        LvR (nameN a.store.lss.ls.ns) m y v := by
      cases hl with
      | max hv hu hw => exact ⟨_, _, hv, hu, hw⟩
    have hg : lvG m q = 2 := by simp [lvG, hv]
    rw [lvInternW_rec n m q (by rw [hg]; decide) (by rw [hg]; decide), hg,
      show lvA m q = x by simp [lvA, hv], show lvB m q = y by simp [lvB, hv]] at hW
    cases hU : lvInternW n m x with
    | none => rw [hU] at hW; simp [liOneK] at hW
    | some r =>
    obtain ⟨hu', m₁⟩ := r
    rw [hU, liOneK_two n _ _ _ _ (by decide)] at hW
    obtain ⟨a₁, hrun₁, hA₁, hlt₁, hf₁, hk₁, hvk₁⟩ := ihu n m a x hu' m₁ hA hwf hu hU
    have hwf₁ : NStoreWF a₁.store.lss.ls.ns := hk₁.2 ▸ hwf
    have hvv₁ : LvR (nameN a₁.store.lss.ls.ns) m₁ y v := by
      rw [hk₁.2]; exact LvR.of_view hvk₁ hvv
    cases hV : lvInternW n m₁ y with
    | none => rw [hV] at hW; simp [liTwoK] at hW
    | some r =>
    obtain ⟨hv', m₂⟩ := r
    rw [hV, liTwoK_max _ _ _ _ rfl] at hW
    obtain ⟨a₂, hrun₂, hA₂, hlt₂, hf₂, hk₂, hvk₂⟩ := ihv n m₁ a₁ y hv' m₂ hA₁ hwf₁ hvv₁ hV
    obtain ⟨ok, hR, res, hlt, hf⟩ := liNode_ok (internLNode (.max (decI hu') (decI hv')))
      (fun m => minternW m hu' hv')
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.max_A m a hA w m' hu' hv' hlt₁ hlt₂ hI
        exact ⟨ok, hR, res, hf.mono lvSch_sub.2.2.2.2.1 lvSch_sub.2.2.2.2.2.1⟩)
      m₂ a₂ h m' hA₂ hW
    have hrun := node_run ok
    rw [res] at hrun
    have hk := internLNode_keep _ _ _ _ hrun
    refine ⟨_, ?_, hR, hlt, hf₁.trans (hf₂.trans hf), hk₁.trans (hk₂.trans hk),
      hvk₁.trans (hvk₂.trans (viewsKept_of hA₂.1 hR.1 hk hf))⟩
    show (internLevel u >>= fun hu => internLevel v >>= fun hv => internLNode (.max hu hv)).run a = _
    rw [StateT.run_bind, hrun₁]; simp only [except_ok_bind]
    rw [StateT.run_bind, hrun₂]; exact hrun
  | imax u v ihu ihv =>
    intro n m a q h m' hA hwf hl hW
    cases n with
    | zero => simp [lvInternW] at hW
    | succ n =>
    obtain ⟨x, y, hv, hu, hvv⟩ : ∃ x y, lvNodeW m q = [3, x, y] ∧ LvR (nameN a.store.lss.ls.ns) m x u ∧
        LvR (nameN a.store.lss.ls.ns) m y v := by
      cases hl with
      | imax hv hu hw => exact ⟨_, _, hv, hu, hw⟩
    have hg : lvG m q = 3 := by simp [lvG, hv]
    rw [lvInternW_rec n m q (by rw [hg]; decide) (by rw [hg]; decide), hg,
      show lvA m q = x by simp [lvA, hv], show lvB m q = y by simp [lvB, hv]] at hW
    cases hU : lvInternW n m x with
    | none => rw [hU] at hW; simp [liOneK] at hW
    | some r =>
    obtain ⟨hu', m₁⟩ := r
    rw [hU, liOneK_two n _ _ _ _ (by decide)] at hW
    obtain ⟨a₁, hrun₁, hA₁, hlt₁, hf₁, hk₁, hvk₁⟩ := ihu n m a x hu' m₁ hA hwf hu hU
    have hwf₁ : NStoreWF a₁.store.lss.ls.ns := hk₁.2 ▸ hwf
    have hvv₁ : LvR (nameN a₁.store.lss.ls.ns) m₁ y v := by
      rw [hk₁.2]; exact LvR.of_view hvk₁ hvv
    cases hV : lvInternW n m₁ y with
    | none => rw [hV] at hW; simp [liTwoK] at hW
    | some r =>
    obtain ⟨hv', m₂⟩ := r
    rw [hV, liTwoK_imax _ _ _ _ rfl] at hW
    obtain ⟨a₂, hrun₂, hA₂, hlt₂, hf₂, hk₂, hvk₂⟩ := ihv n m₁ a₁ y hv' m₂ hA₁ hwf₁ hvv₁ hV
    obtain ⟨ok, hR, res, hlt, hf⟩ := liNode_ok (internLNode (.imax (decI hu') (decI hv')))
      (fun m => iminternW m hu' hv')
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.imax_A m a hA w m' hu' hv' hlt₁ hlt₂ hI
        exact ⟨ok, hR, res, hf.mono lvSch_sub.2.2.2.2.2.2.1 lvSch_sub.2.2.2.2.2.2.2.1⟩)
      m₂ a₂ h m' hA₂ hW
    have hrun := node_run ok
    rw [res] at hrun
    have hk := internLNode_keep _ _ _ _ hrun
    refine ⟨_, ?_, hR, hlt, hf₁.trans (hf₂.trans hf), hk₁.trans (hk₂.trans hk),
      hvk₁.trans (hvk₂.trans (viewsKept_of hA₂.1 hR.1 hk hf))⟩
    show (internLevel u >>= fun hu => internLevel v >>= fun hv => internLNode (.imax hu hv)).run a = _
    rw [StateT.run_bind, hrun₁]; simp only [except_ok_bind]
    rw [StateT.run_bind, hrun₂]; exact hrun

/-! ## Slices of names and of levels -/

/-- `LvsR` (`LevelEquivRel.lean`) is lane `levels`' `LvsAR` at the pool. -/
theorem LvsR.toAR {N : Word → Name → Prop} {m : Mem} {o k : Word} {ls : List Level}
    (h : LvsR N m o k ls) : LvsAR N m POOL o k ls := by
  induction h with
  | nil => exact .nil
  | cons hk hl _ ih => exact .cons hk hl ih

theorem NmsR.of_arr {N : Word → Name → Prop} {m m' : Mem} {A : ArrId} (he : m'.arr64 A = m.arr64 A)
    {o k : Word} {xs : List Name} (h : NmsR N m A o k xs) : NmsR N m' A o k xs := by
  induction h with
  | nil => exact .nil
  | cons h0 hx _ ih => exact .cons h0 (by rw [rdW, he]; exact hx) ih

theorem lp_hslice_succ {k : IdxKind} (a : Array Word) (off n : Nat) :
    (hslice? a off (n + 1) : Option (List (Idx k))) = (do
      let x ← hd? a off
      let xs ← hslice? a (off + 1) n
      pure (x :: xs)) := by
  simp only [hslice?, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range n))
  funext j
  simp only [Function.comp]
  congr 1
  omega

/-- **A record-pool name slice that reads back is an `NmsR` slice.** -/
theorem lp_nmsR_of_hslice (ns : NStore) (m : Mem) (A : ArrId) :
    ∀ (lps : List NIdx) (ks : List Name) (o k : Word),
      hslice? (m.arr64 A) o.toNat k.toNat = some lps → o.toNat + k.toNat < 2 ^ 64 →
      lps.mapM (denoteN ns) = some ks → NmsR (nameN ns) m A o k ks := by
  intro lps
  induction lps with
  | nil =>
    intro ks o k hs hb hd
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hd; subst hd
    have hk : k.toNat = 0 := by
      rcases hk : k.toNat with _ | j
      · rfl
      · rw [hk, lp_hslice_succ] at hs
        simp only [Option.bind_eq_bind] at hs
        cases e : (hd? (m.arr64 A) o.toNat : Option NIdx) with
        | none => simp [e] at hs
        | some x =>
          cases e' : (hslice? (m.arr64 A) (o.toNat + 1) j : Option (List NIdx)) with
          | none | some xs => simp [e, e'] at hs
    have : k = 0 := UInt64.toNat_inj.mp (by simpa using hk)
    subst this; exact .nil
  | cons x xs ih =>
    intro ks o k hs hb hd
    rcases hk : k.toNat with _ | j
    · rw [hk] at hs; simp [hslice?] at hs
    rw [hk, lp_hslice_succ] at hs
    simp only [Option.bind_eq_bind] at hs
    cases e : (hd? (m.arr64 A) o.toNat : Option NIdx) with
    | none => simp [e] at hs
    | some x' =>
    cases e' : (hslice? (m.arr64 A) (o.toNat + 1) j : Option (List NIdx)) with
    | none => simp [e, e'] at hs
    | some xs' =>
    simp only [e, e', Option.bind_some, Option.pure_def, Option.some.injEq, List.cons.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at hd
    cases d1 : denoteN ns x' with
    | none => simp [d1] at hd
    | some nm =>
    cases d2 : (xs'.mapM (denoteN ns)) with
    | none => simp [d1, d2] at hd
    | some nms =>
    simp only [d1, d2, Option.bind_some, Option.some.injEq] at hd
    subst hd
    simp only [hd?] at e
    cases ew : (m.arr64 A)[o.toNat]? with
    | none => simp [ew] at e
    | some w =>
    simp only [ew] at e
    by_cases hw : w.toNat < 2 ^ 32
    · simp [hw] at e
      subst e
      have hk0 : k ≠ 0 := fun h0 => by subst h0; simp at hk
      have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hk1 : (k - 1).toNat = j := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
      refine .cons hk0 ⟨by simpa [rdW, ew] using hw, by simpa [rdW, ew] using d1⟩
        (ih _ (o + 1) (k - 1) (by rw [ho1, hk1]; exact e') (by omega) d2)
    · simp [hw] at e

/-! ## `lv_sub_int` refines `internLevel (Level.subst ks vs l)` -/

theorem arenaD_reset {m : Mem} {a : AState} (hA : ArenaD m a) : ArenaD (m.set64 CTL 192 0) a :=
  ⟨ArenaR.frame (by decide) c192_not_arena (reset_frame m) hA.1,
    DerR.frameM [] [192] m _ (reset_frame m) (by simp) a hA.2⟩

theorem arenaD_heap {m m' : Mem} {a : AState} (hA : ArenaD m a) (he : HeapExt m m') : ArenaD m' a :=
  ⟨ArenaR.frame lh_not_arena c192_not_arena he.memFrame hA.1,
    DerR.frameM [LH] [192] m m' he.memFrame (by simp [LH]) a hA.2⟩

/-- **The model of `lv_sub_int` refines `internLevel (Level.subst ks vs l)`**, `l` the readback of
the handle `u`, the keys an `EREC` name slice, the values a `POOL` level slice (both related at
the reset memory, where the caller builds them). -/
theorem lvSubIntW_ok (n : Nat) (m m' : Mem) (a : AState) (u ko kc vo vc h : Word) (L : Level)
    (ks : List Name) (vs : List Level) (hA : ArenaD m a) (hwf : NStoreWF a.store.lss.ls.ns)
    (hu : u.toNat < 2 ^ 32) (hdu : denoteL a.store.ls (decI u) = some L)
    (hk : NmsR (nameN a.store.lss.ls.ns) (m.set64 CTL 192 0) SPN ko kc ks)
    (hv : LvsR (nameN a.store.lss.ls.ns) (m.set64 CTL 192 0) vo vc vs)
    (hW : lvSubIntW n m u ko kc vo vc = some (h, m')) :
    ∃ a', (internLevel (Level.subst ks vs L)).run a = .ok (decI h, a') ∧ ArenaD m' a' ∧
      h.toNat < 2 ^ 32 ∧ MemFrame (LH :: lvArrs) (192 :: lvCtl) m m' ∧ LKeep a a' := by
  cases n with
  | zero => simp [lvSubIntW] at hW
  | succ n =>
  simp only [lvSubIntW] at hW
  have hA₀ := arenaD_reset hA
  have hl : LvR (nameN a.store.lss.ls.ns) (m.set64 CTL 192 0) u L := by
    have := denoteL_lvR hA₀.1 (decI u) L hdu
    rwa [(word_decI _ u hu).mpr rfl] at this
  cases hS : substLW SPN POOL n (m.set64 CTL 192 0) u ko kc vo vc with
  | none => rw [hS] at hW; simp [subIntK] at hW
  | some r =>
  obtain ⟨x, m₁⟩ := r
  rw [hS, subIntK_some] at hW
  obtain ⟨he, hx⟩ := substLW_ok (nameN_rel _ hwf) (KA := SPN) (VA := POOL) (by decide) (by decide)
    ks vs n _ _ _ _ _ _ _ _ _ hl hk hv.toAR hS
  obtain ⟨a', hrun, hA', hlt, hf, hkp, -⟩ := lvInternW_ok _ n m₁ a x h m' (arenaD_heap hA₀ he) hwf hx hW
  refine ⟨a', hrun, hA', hlt, ?_, hkp⟩
  exact ((reset_frame m).mono (by simp) (by simp)).trans
    ((he.memFrame.mono (by simp) (by simp)).trans
      (hf.mono (fun b hb => List.mem_cons_of_mem _ hb) (fun x hx => List.mem_cons_of_mem _ hx)))

/-! ## `ek_copy`, `keys_push`: the keys onto the spine stack -/

theorem toNat_succ_lt {d : Word} (h : d.toNat + 1 < 2 ^ 64) : (d + 1).toNat = d.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

/-- **`ek_copy` copies a name slice**: the words land on the stack above `d`, below `d` nothing
changes, only the stack array is written. -/
theorem ekCopyW_ok {N : Word → Name → Prop} : ∀ (ks : List Name) (n : Nat) (m m' : Mem) (s d l : Word),
    NmsR N m EREC s l ks → d.toNat + l.toNat ≤ (m.arr64 SPN).size → (m.arr64 SPN).size < 2 ^ 63 →
    ekCopyW n m s d l = some m' →
    NmsR N m' SPN d l ks ∧ MemFrame [SPN] [] m m' ∧
      ∀ i : Word, i.toNat < d.toNat → rdW (m'.arr64 SPN) i = rdW (m.arr64 SPN) i := by
  intro ks
  induction ks with
  | nil =>
    intro n m m' s d l hk hb hsz hW
    cases hk
    cases n with
    | zero => simp [ekCopyW] at hW
    | succ n =>
      rw [ekCopyW_zero n m s d 0 rfl] at hW; cases hW
      exact ⟨.nil, MemFrame.refl _ _ _, fun _ _ => rfl⟩
  | cons x xs ih =>
    intro n m m' s d l hk hb hsz hW
    cases hk with
    | cons hl0 hx hxs =>
    cases n with
    | zero => simp [ekCopyW] at hW
    | succ n =>
    rw [ekCopyW_succ n m s d l hl0] at hW
    have hl1 : 1 ≤ l.toNat := by
      rcases Nat.eq_zero_or_pos l.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hl0
      · omega
    have hd1 : (d + 1).toNat = d.toNat + 1 := toNat_succ_lt (by omega)
    have hlm : (l - 1).toNat = l.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hsz₁ : ((m.set64 SPN d (rdW (m.arr64 EREC) s)).arr64 SPN).size = (m.arr64 SPN).size :=
      Mem.size_arr64_set64 _ _ _ _
    obtain ⟨hk', hf', hb'⟩ := ih n _ m' (s + 1) (d + 1) (l - 1)
      (hxs.of_arr (Mem.arr64_set64_ne _ _ _ _ _ (by decide))) (by rw [hsz₁, hd1, hlm]; omega)
      (by rw [hsz₁]; exact hsz) hW
    have hdl : d.toNat < (m.arr64 SPN).size := by omega
    have hd : rdW (m'.arr64 SPN) d = rdW (m.arr64 EREC) s := by
      rw [hb' d (by rw [hd1]; omega), rdW_set64]; simp [hdl]
    refine ⟨.cons hl0 (by rw [hd]; exact hx) hk', (MemFrame.set64 _ _ (by decide) _ _).trans hf', ?_⟩
    intro i hi
    rw [hb' i (by rw [hd1]; omega), rdW_set64]
    have : ¬ d = i := fun e => by subst e; omega
    simp [this]

/-! ## `caps_never_zero` refines `capsNeverZero`'s computation -/

theorem arenaD_frame_hi {m m' : Mem} {a : AState} {A : List ArrId} {C : List Word}
    (hA : ArenaD m a) (hf : MemFrame A C m m') (hA' : ∀ b ∈ A, 64 ≤ b ∧ b < 256) (hC : ∀ x ∈ C, 64 ≤ x.toNat) :
    ArenaD m' a :=
  ⟨ArenaR.frame_ext A C hA' hC m m' hf a hA.1,
    DerR.frameM A C m m' hf (fun b hb => by have := hA' b hb; simp only [ArrId] at this ⊢; omega) a hA.2⟩

/-- **The model of `caps_never_zero` is `(substPW ks vs pw).isNever`**, the keys an `EREC` name
slice, the values the readback of the list `us`, the datum `pw` related at `(swd, so, sc)`; it
writes the heap and the stack above its top, and puts the top back. -/
theorem capsNeverZeroW_ok (n : Nat) (m m' : Mem) (a : AState) (po pc us swd so sc x : Word)
    (ks : List Name) (vs : List Level) (pw : PropWhen) (hA : ArenaD m a)
    (hwf : NStoreWF a.store.lss.ls.ns) (hus : us.toNat < 2 ^ 32)
    (hsz : (m.arr64 SPN).size < 2 ^ 63)
    (hdl : denoteLs a.store.lss (decI us) = some vs)
    (hk : NmsR (nameN a.store.lss.ls.ns) m EREC po pc ks)
    (hp : PWR (nameN a.store.lss.ls.ns) m EREC swd so sc pw)
    (hW : capsNeverZeroW n m po pc us swd so sc = some (x, m')) :
    ArenaD m' a ∧ MemFrame [LH, SPN] [192, 136] m m' ∧ spTop m' = spTop m ∧
      (∀ i : Word, i < spTop m → spW m' i = spW m i) ∧
      (x ≠ 0) = ((Level.substPW ks vs pw).isNever = true) ∧ x.toNat < 2 ^ 32 := by
  cases n with
  | zero => simp [capsNeverZeroW] at hW
  | succ n =>
  simp only [capsNeverZeroW] at hW
  obtain ⟨ids, hv, hdl'⟩ := denoteLs_view a (decI us) vs hdl
  obtain ⟨e₁, t₁, s₁⟩ := lsNodeW_store hA.1 hus hv
  rw [e₁] at hW
  simp only [List.headD_cons, List.tail_cons, reduceCtorEq, ↓reduceIte] at hW
  cases n with
  | zero => simp [keysPushW, capsK1] at hW
  | succ n =>
  simp only [keysPushW] at hW
  have t1 : ¬ m.len64 SPN < spTop m := fun t1 => by simp [t1, capsK1] at hW
  have t2 : ¬ m.len64 SPN - spTop m < pc := fun t2 => by simp [t1, t2, capsK1] at hW
  simp only [t1, t2, ↓reduceIte] at hW
  have hlen : (m.len64 SPN).toNat = (m.arr64 SPN).size := L.Front.toNat_ofNat_size _ hsz
  have t1' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp t1)
  have t2' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp t2)
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp t1), hlen] at t2'
  rw [hlen] at t1'
  have hroom : (spTop m).toNat + pc.toNat ≤ (m.arr64 SPN).size := by omega
  rcases hc : ekCopyW n m po (spTop m) pc with _ | m₁ <;> simp only [hc, kpK, capsK1, reduceCtorEq] at hW
  obtain ⟨hk₁, hf₁, hb₁⟩ := ekCopyW_ok ks n m m₁ po (spTop m) pc hk hroom hsz hc
  generalize hm₂ : (m₁.set64 CTL 136 (spTop m + pc)).set64 CTL 192 0 = m₂ at hW
  have hf₂ : MemFrame [SPN] [136, 192] m m₂ := hm₂ ▸
    (hf₁.mono (by simp) (by simp)).trans (((MemFrame.setCtl _ _ _).mono (by simp) (by simp)).trans
      ((MemFrame.setCtl _ _ _).mono (by simp) (by simp)))
  have hA₂ : ArenaD m₂ a := arenaD_frame_hi hA hf₂ (by simp [SPN]) (by simp)
  have hspn₂ : m₂.arr64 SPN = m₁.arr64 SPN := by
    rw [← hm₂, Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have herec₂ : m₂.arr64 EREC = m.arr64 EREC := hf₂.1 EREC (by simp [SPN, EREC]) (by decide)
  have hpool₂ : m₂.arr64 POOL = m.arr64 POOL := hf₂.1 POOL (by simp [SPN, POOL]) (by decide)
  have hpool₂' : m₂.arr64 POOL1 = m.arr64 POOL1 := hf₂.1 POOL1 (by simp [SPN, POOL1]) (by decide)
  have hpool₂v := vpool_congr hpool₂ hpool₂'
  have hpool₂c := pcap_congr' hpool₂ hpool₂'
  have htop := m.top.toNat_lt
  have h41 := hA.1.lit.1.top41
  have hl := lvsR_of_slice hA₂.1 ids vs _ _ (by rw [hpool₂v]; exact s₁) (by omega) hdl'
  have hp₂ : PWR (nameN a.store.lss.ls.ns) m₂ EREC swd so sc pw := by
    rcases hp with ⟨h1, h2⟩ | ⟨h1, ps, h2, hps⟩
    · exact .inl ⟨h1, h2⟩
    · exact .inr ⟨h1, ps, h2, hps.of_arr herec₂⟩
  cases hS : substPWW SPN POOL EREC (n + 1) m₂ swd so sc (spTop m) pc (tfld m LVLS (tierW us) (idxW us) 0)
      (tfld m LVLS (tierW us) (idxW us) 1) with
  | none => rw [hS] at hW; simp [capsK2] at hW
  | some r =>
  obtain ⟨x₃, m₃⟩ := r
  rw [hS, capsK2_some] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨he, hz⟩ := substPWW_ok (nameN_rel _ hwf) (KA := SPN) (VA := POOL) (PA := EREC)
    (by decide) (by decide) (by decide) ks vs (n + 1) _ _ _ _ _ _ _ _ _ _ pw hp₂ (hk₁.of_arr hspn₂)
    hl.toAR hS
  have hf₃ : MemFrame [LH, SPN] [192, 136] m (m₃.set64 CTL 136 (spTop m)) :=
    (hf₂.mono (by simp) (by simp)).trans ((he.memFrame.mono (by simp) (by simp)).trans
      ((MemFrame.setCtl _ _ _).mono (by simp) (by simp)))
  have hspn₃ : (m₃.set64 CTL 136 (spTop m)).arr64 SPN = m₁.arr64 SPN := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), he.arr SPN (by decide) (by decide), hspn₂]
  refine ⟨arenaD_frame_hi hA hf₃ (by simp [LH, SPN]) (by simp), hf₃, ?_, ?_, ?_, ?_⟩
  · simp only [spTop]; rw [rdW_set64]
    by_cases hs : (136 : Word).toNat < (m₃.arr64 CTL).size
    · simp; intro h; simp at hs; omega
    · have hsz₃ : (m₃.arr64 CTL).size = (m.arr64 CTL).size := by
        have := hf₃.2.2.1 CTL; rw [Mem.size_arr64_set64] at this; exact this
      simp only [hs, and_false, ↓reduceIte, rdW]
      rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  · intro i hi
    simp only [spW, hspn₃]
    exact hb₁ i (UInt64.lt_iff_toNat_lt.mp hi)
  · rcases hz with ⟨rfl, h2⟩ | ⟨rfl, ps, h2, -⟩
    · simp [h2, PropWhen.isNever]
    · simp [h2, PropWhen.isNever]
  · rcases hz with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

end L.Arena
