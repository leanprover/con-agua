import ConAgua.Arena.LevelIntern
import ConAgua.Arena.Rom
import ConAgua.Arena.PromoteLRef
import ConAgua.Arena.MemoTree
import ConAgua.Census.Attr

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

set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Rom (StoreA StoreC frame_store)

/-! ## A stored name re-interns to itself -/

theorem NStore.find?_of_view {st : NStore} (hwf : NStoreWF st) {i : NIdx} {v : NNodeView}
    (hv : st.view i = some v) : st.find? v = some i := by
  obtain ⟨rk, w⟩ := hwf
  unfold NStore.view at hv
  unfold NStore.find?
  by_cases hp : i.isPersistent = true
  · rw [if_pos hp] at hv
    have : st.pers.find? v = some i := (w.consP v i).mpr ⟨by simp [NStore.view, hp, hv], hp⟩
    rw [this]
  · rw [if_neg hp] at hv
    by_cases hon : st.scratchOn = true
    · rw [if_pos hon] at hv
      have hvi : st.view i = some v := by simp [NStore.view, hp, hon, hv]
      have hs : st.scr.find? v = some i := (w.consS v i).mpr ⟨hvi, by simpa using hp⟩
      rw [w.fresh v i hs, if_pos hon, hs]
    · rw [if_neg hon] at hv; cases hv

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
    | str p s =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨q, hq, rfl⟩ := h
      have hp := ih p q hq
      simp only [internName, StateT.run_bind, hp]
      exact internNNode_view_run a hwf hv
    | num p k =>
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
      | (simp only [StateT.run_pure, pure_bind, StateT.bind, StateT.set, StateT.pure, StateT.run,
          bind, Except.bind, pure, Except.pure] at h
         injection h with h
         obtain ⟨-, rfl⟩ := Prod.mk.inj h
         exact ⟨fun j v hv => LStore.view_intern_mono _ w hv, LStore.intern_ns _ w⟩)
      | simp [fail, throwThe, MonadExceptOf.throw, StateT.run, bind, StateT.bind, StateT.lift,
          Except.bind] at h

/-! ## Level pointers keep their views across the store's interning -/

/-- Every level pointer that views keeps its view. -/
def ViewsKept (m m' : Mem) : Prop := ∀ q, lvNodeW m q ≠ [] → lvNodeW m' q = lvNodeW m q

theorem ViewsKept.refl (m : Mem) : ViewsKept m m := fun _ _ => rfl

theorem ViewsKept.trans {m₁ m₂ m₃ : Mem} (h₁ : ViewsKept m₁ m₂) (h₂ : ViewsKept m₂ m₃) :
    ViewsKept m₁ m₃ := fun q hq => by
  rw [h₂ q (by rw [h₁ q hq]; exact hq), h₁ q hq]

theorem viewsKept_of {m m' : Mem} {a a' : AState} (hR : ArenaR m a) (hR' : ArenaR m' a')
    (hk : LKeep a a') (hf : MemFrame StoreA StoreC m m') : ViewsKept m m' := by
  intro q hq
  by_cases hb : q >>> 32 = 0
  · have hh : q.toNat < 2 ^ 32 := by
      have := congrArg UInt64.toNat hb
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow] at this
      have := q.toNat_lt; omega
    obtain ⟨v, hv⟩ := lvNodeW_view hR hh hq
    rw [lvNodeW_store hR hh hv, lvNodeW_store hR' hh (hk.1 _ _ hv)]
  · have hLH : m'.arr64 LH = m.arr64 LH := hf.1 LH (by simp [StoreA, LH]) (by decide)
    have h192 : rdW (m'.arr64 CTL) 192 = rdW (m.arr64 CTL) 192 :=
      hf.2.1 192 (by
        simp only [StoreC, List.mem_map, List.mem_range, not_exists, not_and]
        intro x hx e; have := congrArg UInt64.toNat e; simp at this; omega)
    rw [lvNodeW_heap m' q hb, lvNodeW_heap m q hb, hLH, h192]

/-! ## The refinement -/

/-- One node interned by a store function: the twin's step, the frame, the handle bound. -/
theorem liNode_ok (op : AM LIdx) (W : Mem → Option (Word × Mem))
    (hop : ∀ m a w m', ArenaD m a → W m = some (w, m') →
      AM.ok op a ∧ ArenaD m' (AM.st op a) ∧ AM.res op a = decI w ∧ MemFrame StoreA StoreC m m')
    (m : Mem) (a : AState) (h : Word) (m' : Mem) (hA : ArenaD m a)
    (hW : liNodeK (W m) = some (h, m')) :
    AM.ok op a ∧ ArenaD m' (AM.st op a) ∧ AM.res op a = decI h ∧ h.toNat < 2 ^ 32 ∧
      MemFrame StoreA StoreC m m' := by
  cases hI : W m with
  | none => rw [hI] at hW; simp [liNodeK] at hW
  | some r =>
    obtain ⟨w, m₁⟩ := r
    rw [hI] at hW
    simp only [liNodeK] at hW
    split at hW
    · simp at hW
    rename_i hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    obtain ⟨ok, hR, res, hf⟩ := hop m a _ _ hA hI
    exact ⟨ok, hR, res, by simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt, hf⟩

/-- The twin facts of a node step, as a run. -/
theorem node_run {op : AM LIdx} {a : AState} (ok : AM.ok op a) : op.run a = .ok (AM.res op a, AM.st op a) :=
  AM.run_of_ok _ _ ok

/-- **What a successful `lv_intern` gives.** -/
def LIOk (L : Level) (m : Mem) (a : AState) (h : Word) (m' : Mem) : Prop :=
  ∃ a', (internLevel L).run a = .ok (decI h, a') ∧ ArenaD m' a' ∧ h.toNat < 2 ^ 32 ∧
    MemFrame StoreA StoreC m m' ∧ LKeep a a' ∧ ViewsKept m m'

set_option linter.constructorNameAsVariable false in
/-- **The model of `lv_intern` refines `internLevel`** of the level the pointer denotes. -/
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
        exact ⟨ok, hR, res, frame_store hf (by simp [zeroSch, ZREC, ZSLOT]) (by simp [zeroSch])⟩)
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
        exact ⟨ok, hR, res, frame_store hf (by simp [paramSch, PREC, PSLOT]) (by simp [paramSch])⟩)
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
        exact ⟨ok, hR, res, frame_store hf (by simp [succSch, SREC, SSLOT]) (by simp [succSch])⟩)
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
        exact ⟨ok, hR, res, frame_store hf (by simp [maxSch, MREC, MSLOT]) (by simp [maxSch])⟩)
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
        exact ⟨ok, hR, res, frame_store hf (by simp [imaxSch, IREC, ISLOT]) (by simp [imaxSch])⟩)
      m₂ a₂ h m' hA₂ hW
    have hrun := node_run ok
    rw [res] at hrun
    have hk := internLNode_keep _ _ _ _ hrun
    refine ⟨_, ?_, hR, hlt, hf₁.trans (hf₂.trans hf), hk₁.trans (hk₂.trans hk),
      hvk₁.trans (hvk₂.trans (viewsKept_of hA₂.1 hR.1 hk hf))⟩
    show (internLevel u >>= fun hu => internLevel v >>= fun hv => internLNode (.imax hu hv)).run a = _
    rw [StateT.run_bind, hrun₁]; simp only [except_ok_bind]
    rw [StateT.run_bind, hrun₂]; exact hrun

end L.Arena
