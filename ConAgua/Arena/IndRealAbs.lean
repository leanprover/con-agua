import ConAgua.Arena.IndRealSpine
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# `abstract1_fast` under the stage relation and the `abstract1` memo (lane `indproofs4`, helper `abs`)

`abstract1_fast(fuel, e, d, k)` is the adapter `L.Checker.abstract1FastA` (`Checker/Entry.lean`):
it ignores the fuel word and calls `abs_entry(e, d, k)`, lane `exprops4`'s walk, which refines
`abstract1Fast coreWalkFuel` under `ArenaA = ArenaD ∧ AbsR` (`absEntry_refines`). Every caller of
the stage passes `CWF` (= `coreWalkFuel`).

* **The memo.** `abs_entry` keeps its memo (`ABMEMO` = 49, epoch word `CTL[48]`) outside the
  arena's memos, so `StageR` says nothing about it. Both sides clear it at entry and exit (the
  twin's `abstract1Fast`, `ExprOps.lean:1721`), so the twin run from `a` is the run from `a` with
  any other `abs1C` (definitionally: the entry clear overwrites it), and the walk needs only *some*
  well-formed memo in the memory at hand: the memory-only predicate `AbsOK` (`IndStubs.lean`),
  which holds again after the call. Callers thread it as a hypothesis and a post (like `PosMR`);
  it survives every writer apart from array 49 and `CTL[48]` (`AbsOK.frame`), the stubs by the
  contract `stubM_absOK`. The core's `CoreMemos` contains it (`coreAbSch = abSch`), so a `StageT`
  stage has it (`IndRealAbsT.lean`).
* **The model** `abF := callF abProg "abstract1_fast"` (the recipe of `IndReal.lean`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The memo predicate -/

/-- A list of arrays apart from the walk memos' (49, 50, 51, 155; the core's 151‥153, 52‥54) and
the pins. -/
def memoFreeA (A : List ArrId) : Bool := A.all fun b => b != 49 && b != 50 && b != 51 && b != 155 &&
  b != PINS && b != 151 && b != 152 && b != 153 && b != 52 && b != 53 && b != 54

/-- A list of `CTL` words apart from the walk memos' epoch words (48, 50, 52, 158; the core's 152,
154, 156, 54, 56, 58). -/
def memoFreeC (C : List Word) : Bool := C.all fun x => x != 48 && x != 50 && x != 52 && x != 158 &&
  x != 152 && x != 154 && x != 156 && x != 54 && x != 56 && x != 58

theorem AbMemo.frame {A : List ArrId} {C : List Word} {m m' : Mem} (h : AbMemo m)
    (hf : MemFrame A C m m') (hA : (49 : ArrId) ∉ A) (hC : (48 : Word) ∉ C) : AbMemo m' :=
  let ⟨mp, hm⟩ := h; ⟨mp, memoRG_frame _ ⟨by decide, by decide⟩ lfKey decE A C hA hC m m' hf mp hm⟩

theorem I1Memo.frame {A : List ArrId} {C : List Word} {m m' : Mem} (h : I1Memo m)
    (hf : MemFrame A C m m') (hA : (51 : ArrId) ∉ A) (hC : (52 : Word) ∉ C) : I1Memo m' :=
  let ⟨mp, hm⟩ := h; ⟨mp, memoRG_frame _ ⟨by decide, by decide⟩ lfKey decE A C hA hC m m' hf mp hm⟩

theorem CrMemo.frame {A : List ArrId} {C : List Word} {m m' : Mem} (h : CrMemo m)
    (hf : MemFrame A C m m') (hA : (155 : ArrId) ∉ A) (hC : (158 : Word) ∉ C) : CrMemo m' :=
  let ⟨mp, hm⟩ := h
  ⟨mp, memoRV_frame _ ⟨by decide, by decide⟩ bmKey _ A C hA hC m m' hf (fun _ _ h => h) mp hm⟩

theorem IlMemo.frame {A : List ArrId} {C : List Word} {m m' : Mem} (h : IlMemo m)
    (hf : MemFrame A C m m') (hA : (50 : ArrId) ∉ A) (hC : (50 : Word) ∉ C) : IlMemo m' :=
  let ⟨mp, hm⟩ := h; ⟨mp, memoRG_frame _ ⟨by decide, by decide⟩ lfKey decE A C hA hC m m' hf mp hm⟩

/-- `memoFreeA`, unfolded. -/
theorem memoFreeA_iff {A : List ArrId} (hA : memoFreeA A = true) :
    (49 : ArrId) ∉ A ∧ (50 : ArrId) ∉ A ∧ (51 : ArrId) ∉ A ∧ (155 : ArrId) ∉ A ∧ PINS ∉ A ∧
      ((151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A) ∧
      ((52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A) := by
  have h : ∀ b ∈ A, b ≠ 49 ∧ b ≠ 50 ∧ b ≠ 51 ∧ b ≠ 155 ∧ b ≠ PINS ∧ b ≠ 151 ∧ b ≠ 152 ∧ b ≠ 153 ∧
      b ≠ 52 ∧ b ≠ 53 ∧ b ≠ 54 := fun b hb => by
    have := List.all_eq_true.mp hA b hb; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := this
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  refine ⟨fun hm => (h _ hm).1 rfl, fun hm => (h _ hm).2.1 rfl, fun hm => (h _ hm).2.2.1 rfl,
    fun hm => (h _ hm).2.2.2.1 rfl, fun hm => (h _ hm).2.2.2.2.1 rfl,
    ⟨fun hm => (h _ hm).2.2.2.2.2.1 rfl, fun hm => (h _ hm).2.2.2.2.2.2.1 rfl,
      fun hm => (h _ hm).2.2.2.2.2.2.2.1 rfl⟩,
    ⟨fun hm => (h _ hm).2.2.2.2.2.2.2.2.1 rfl, fun hm => (h _ hm).2.2.2.2.2.2.2.2.2.1 rfl,
      fun hm => (h _ hm).2.2.2.2.2.2.2.2.2.2 rfl⟩⟩

/-- `memoFreeC`, unfolded. -/
theorem memoFreeC_iff {C : List Word} (hC : memoFreeC C = true) :
    (48 : Word) ∉ C ∧ (50 : Word) ∉ C ∧ (52 : Word) ∉ C ∧ (158 : Word) ∉ C ∧
      ((152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C) ∧
      ((54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C) := by
  have h : ∀ x ∈ C, x ≠ 48 ∧ x ≠ 50 ∧ x ≠ 52 ∧ x ≠ 158 ∧ x ≠ 152 ∧ x ≠ 154 ∧ x ≠ 156 ∧ x ≠ 54 ∧
      x ≠ 56 ∧ x ≠ 58 := fun x hx => by
    have := List.all_eq_true.mp hC x hx; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact ⟨this.1.1.1.1.1.1.1.1.1, this.1.1.1.1.1.1.1.1.2, this.1.1.1.1.1.1.1.2, this.1.1.1.1.1.1.2,
      this.1.1.1.1.1.2, this.1.1.1.1.2, this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩
  refine ⟨fun hm => (h _ hm).1 rfl, fun hm => (h _ hm).2.1 rfl, fun hm => (h _ hm).2.2.1 rfl,
    fun hm => (h _ hm).2.2.2.1 rfl,
    ⟨fun hm => (h _ hm).2.2.2.2.1 rfl, fun hm => (h _ hm).2.2.2.2.2.1 rfl,
      fun hm => (h _ hm).2.2.2.2.2.2.1 rfl⟩,
    ⟨fun hm => (h _ hm).2.2.2.2.2.2.2.1 rfl, fun hm => (h _ hm).2.2.2.2.2.2.2.2.1 rfl,
      fun hm => (h _ hm).2.2.2.2.2.2.2.2.2 rfl⟩⟩

/-- **`WkOK` across a writer apart from the pins and the core's walk memos.** -/
theorem WkOK.frame {A : List ArrId} {C : List Word} {m m' : Mem} (h : WkOK m)
    (hf : MemFrame A C m m') (hP : PINS ∉ A)
    (hW : (151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A)
    (hL : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A)
    (hWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C)
    (hLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C) : WkOK m' :=
  ⟨h.1.frame hf hW hWC hL hLC, by rw [hf.2.2.1]; exact h.2.1, by rw [hf.2.2.1]; exact h.2.2.1,
    by rw [hf.2.2.1]; exact h.2.2.2.1, by simp only [pinW, hf.1 PINS hP (by decide)]; exact h.2.2.2.2⟩

/-- **`AbsOK` across a writer apart from the walk memos' arrays and epoch words.** -/
theorem AbsOK.frameD {A : List ArrId} {C : List Word} {m m' : Mem} (h : AbsOK m)
    (hf : MemFrame A C m m') (hA : memoFreeA A = true) (hC : memoFreeC C = true) : AbsOK m' :=
  let ⟨a1, a2, a3, a4, a5, a6, a7⟩ := memoFreeA_iff hA
  let ⟨c1, c2, c3, c4, c5, c6⟩ := memoFreeC_iff hC
  ⟨h.1.frame hf a1 c1, h.2.1.frame hf a3 c3, h.2.2.1.frame hf a4 c4, h.2.2.2.1.frame hf a2 c2,
    h.2.2.2.2.frame hf a5 a6 a7 c5 c6⟩

/-! ## Steps that keep it

`AFr m m'`: a step from `m` to `m'` keeps the memo well formed. Model frames are proved by
`afr_auto h [f₁, …]` from the callees' (the counterpart of `mfr_auto`, `IndPosSpec/NestCrest.lean`). -/

/-- The step from `m` to `m'` keeps `AbsOK`. -/
def AFr (m m' : Mem) : Prop := AbsOK m → AbsOK m'

theorem AFr.refl (m : Mem) : AFr m m := id

theorem AFr.trans {m₁ m₂ m₃ : Mem} (h₁ : AFr m₁ m₂) (h₂ : AFr m₂ m₃) : AFr m₁ m₃ := h₂ ∘ h₁

/-- A writer apart from the walk memos' arrays and epoch words. -/
theorem AFr.of_frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : memoFreeA A = true := by decide)
    (hC : memoFreeC C = true := by decide) : AFr m m' :=
  fun h => h.frameD hf hA hC

/-- A write of an array other than `CTL` and the walk memos'. -/
theorem AFr.set64 (m : Mem) (a : ArrId) (ha : a ≠ CTL) (h49 : memoFreeA [a] = true) (k v : Word) :
    AFr m (m.set64 a k v) :=
  fun h => h.frameD (MemFrame.set64 m a ha k v) h49 rfl

/-- A write of a `CTL` word other than the walk memos' epoch words. -/
theorem AFr.setCtl (m : Mem) (c : Word) (h48 : memoFreeC [c] = true) (v : Word) : AFr m (m.set64 CTL c v) :=
  fun h => h.frameD (MemFrame.setCtl m c v) rfl h48

/-- `afr_set`: `AFr m m'` for `m'` a chain of writes of `m` apart from the walk memos. -/
macro "afr_set" : tactic => `(tactic|
  repeat (first
    | with_reducible refine AFr.trans ?_ (AFr.set64 _ _ (by decide) (by decide) _ _)
    | with_reducible refine AFr.trans ?_ (AFr.setCtl _ _ (by decide) _)
    | with_reducible exact AFr.refl _))

syntax "afr_auto" ident "[" term,* "]" : tactic
macro_rules
  | `(tactic| afr_auto $h [$ts,*]) => `(tactic|
    repeat' (first
      | with_reducible exact AFr.refl _
      | (simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident; rw [← ($h).2]
         first | with_reducible exact AFr.refl _ | (afr_set; done))
      | (simp only [Option.some.injEq] at $h:ident; subst $h:ident; exact AFr.refl _)
      | (simp only [reduceCtorEq] at $h:ident; done)
      | (first $[| refine AFr.trans ($ts (by with_reducible assumption)) ?_]*)
      | split at $h:ident))

/-- Across a writer of the record pool (`IW`, its top `CTL[200]`). -/
theorem AbsOK.iw {m m' : Mem} (h : AbsOK m) (hf : MemFrame [IW] [200] m m') : AbsOK m' :=
  h.frameD hf rfl rfl

theorem allocW_iwFrame {m m' : Mem} {k q : Word} (h : allocW m k = some (q, m')) :
    MemFrame [IW] [200] m m' := by
  simp only [allocW] at h
  split at h; · simp at h
  split at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact allocMem_frame m k

theorem copyW_iwFrame : ∀ (n : Nat) (m m' : Mem) (d s l : Word), copyW n m d s l = some m' →
    MemFrame [IW] [200] m m'
  | 0, _, _, _, _, _, h => by simp [copyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [copyW_nil n m d s l hl] at h; cases h; exact MemFrame.refl _ _ _
    · rw [copyW_step n m d s l hl] at h
      exact (set64IW_frame _ _ _).trans (copyW_iwFrame n _ _ _ _ _ h)

theorem consW_iwFrame {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word}
    (h : consW n m x o l = some (r, m')) : MemFrame [IW] [200] m m' := by
  unfold consW at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ((allocW_iwFrame hal).trans (set64IW_frame _ _ _)).trans (copyW_iwFrame _ _ _ _ _ _ hc)

/-- Across `sl_cons`. -/
theorem AbsOK.consW {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} (hA : AbsOK m)
    (h : consW n m x o l = some (r, m')) : AbsOK m' := hA.iw (consW_iwFrame h)

theorem AFr.iw {m m' : Mem} (hf : MemFrame [IW] [200] m m') : AFr m m' := AFr.of_frame hf

theorem consW_afr {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word}
    (h : consW n m x o l = some (r, m')) : AFr m m' := AFr.iw (consW_iwFrame h)

theorem allocW_afr {m m' : Mem} {k q : Word} (h : allocW m k = some (q, m')) : AFr m m' :=
  AFr.iw (allocW_iwFrame h)

theorem set64IW_afr (m : Mem) (x v : Word) : AFr m (m.set64 IW x v) := AFr.iw (set64IW_frame m x v)

theorem set64ER_afr (m : Mem) (x v : Word) : AFr m (m.set64 EREC x v) :=
  AFr.of_frame (MemFrame.set64 m EREC (by decide) x v)

theorem mkAppW_afr {m m' : Mem} {f a r : Word} (h : mkAppW m f a = some (r, m')) : AFr m m' :=
  AFr.of_frame (mkAppW_frameA m m' f a r h)
theorem mkLamW_afr {m m' : Mem} {f a r : Word} (h : mkLamW m f a = some (r, m')) : AFr m m' :=
  AFr.of_frame (mkLamW_frameA m m' f a r h)
theorem mkForallW_afr {m m' : Mem} {f a r : Word} (h : mkForallW m f a = some (r, m')) : AFr m m' :=
  AFr.of_frame (mkForallW_frameA m m' f a r h)
theorem mkLetW_afr {m m' : Mem} {t v b r : Word} (h : mkLetW m t v b = some (r, m')) : AFr m m' :=
  AFr.of_frame (mkLetW_frameA m m' t v b r h)
theorem mkProjW_afr {m m' : Mem} {n i e r : Word} (h : mkProjW m n i e = some (r, m')) : AFr m m' :=
  AFr.of_frame (mkProjW_frameA m m' n i e r h)

theorem erAllocW_afr {m m' : Mem} {k q : Word} (h : erAllocW m k = some (q, m')) : AFr m m' := by
  simp only [erAllocW] at h
  split at h; · simp at h
  split at h; · simp at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact AFr.of_frame (MemFrame.setCtl m 129 _)

theorem wrER_afr (ws : List Word) (m : Mem) (q : Word) : AFr m (wrER m q ws) :=
  AFr.of_frame (wrER_frame ws m q)

theorem cvNewW_afr {m m' : Mem} {nm lo ll ty q : Word} (h : cvNewW m nm lo ll ty = some (q, m')) :
    AFr m m' := by
  simp only [cvNewW] at h
  split at h; · cases h
  rename_i q1 m1 h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (erAllocW_afr h1).trans (by rw [cvNewMem_eq]; exact wrER_afr _ _ _)

theorem sointernW_afr {m m' : Mem} {u r : Word} (h : sointernW m u = some (r, m')) : AFr m m' :=
  AFr.of_frame (sointernW_frame m u r m' h)

theorem fvinternW_afr {m m' : Mem} {u ty r : Word} (h : fvinternW m u ty = some (r, m')) : AFr m m' :=
  AFr.of_frame (fvinternW_frame m u ty r m' h)

theorem stripF_afr {tg : Word} {m m' : Mem} {args r : List Word} (h : stripF tg m args = some (r, m')) :
    AFr m m' := AFr.iw (stripF_frame h)

theorem i1F_afr {m m' : Mem} {args r : List Word} (h : i1F m args = some (r, m')) : AFr m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact AFr.of_frame (run_memFrame i1Prog_closed (List.mem_cons_self ..) (run_of_callW hc)).1

theorem copyW_afr {n : Nat} {m m' : Mem} {d s l : Word} (h : copyW n m d s l = some m') : AFr m m' :=
  AFr.iw (copyW_iwFrame _ _ _ _ _ _ h)

theorem appendW_afr {n : Nat} {m m' : Mem} {o1 l1 o2 l2 : Word} {r : List Word}
    (h : appendW n m o1 l1 o2 l2 = some (r, m')) : AFr m m' := by
  unfold appendW at h
  afr_auto h [allocW_afr, copyW_afr]

theorem binternW_afr {m m' : Mem} {u r : Word} (h : binternW m u = some (r, m')) : AFr m m' :=
  AFr.of_frame (binternW_frameA m m' u r h)
theorem ceinternW_afr {m m' : Mem} {f a r : Word} (h : ceinternW m f a = some (r, m')) : AFr m m' :=
  AFr.of_frame (ceinternW_frame m f a r m' h)
theorem ftdF_afr {m m' : Mem} {args r : List Word} (h : ftdF m args = some (r, m')) : AFr m m' :=
  AFr.of_frame (ftdF_frame h)
theorem ftdsF_afr {m m' : Mem} {args r : List Word} (h : ftdsF m args = some (r, m')) : AFr m m' :=
  AFr.of_frame (ftdsF_frame h)
theorem gaaF_afr {m m' : Mem} {args r : List Word} (h : gaaF m args = some (r, m')) : AFr m m' :=
  AFr.of_frame (gaaF_frame h)
theorem mknF_afr {m m' : Mem} {args r : List Word} (h : mknF m args = some (r, m')) : AFr m m' :=
  AFr.of_frame (mknF_frame h)
theorem snocW_afr {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} (h : snocW n m o l x = some (r, m')) :
    AFr m m' := by
  unfold snocW at h
  afr_auto h [allocW_afr, copyW_afr]

theorem erCopyW_afr : ∀ (n : Nat) (m m' : Mem) (d s l : Word), erCopyW n m d s l = some m' → AFr m m'
  | 0, _, _, _, _, _, h => by simp [erCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [erCopyW_nil n m d s l hl] at h; cases h; exact AFr.refl _
    · rw [erCopyW_step n m d s l hl] at h
      exact (set64IW_afr _ _ _).trans (erCopyW_afr n _ _ _ _ _ h)

theorem erToIwW_afr {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : erToIwW n m o l = some (r, m')) :
    AFr m m' := by
  unfold erToIwW at h
  afr_auto h [allocW_afr, erCopyW_afr _ _ _ _ _ _]

/-- **A function of `p` keeps the `abstract1` memo well formed**: every returning run from a
memory with `AbsOK` ends in one. A program fact the install layers take as a hypothesis for their
callees outside the `abstract1` cascade (like the write sets `closedA … hbFreeA …`); true of the
checker's program: such a function either leaves array 49 and `CTL[48]` alone or reaches them only
through the core and `abs_entry`, both of which keep the memo well formed. -/
def AbsKeep (p : Prog) (f : FnName) : Prop :=
  ∀ (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem), callW p n f vs m = some (r, m') →
    AFr m m'

/-! ## The model -/

/-- The adapter, the `abstract1` walk and its entry. -/
def abProg : Prog := [("abstract1_fast", L.Checker.abstract1FastA)] ++ absWalkProg ++
  [("abs_entry", absEntry)]

/-- The functions `abstract1_fast` reaches. -/
def abFns : List FnName := "abstract1_fast" :: absFns

theorem abProg_closed : closedA abProg absA absC abFns = true := by decide +kernel

theorem abProg_abs : AbsProg abProg := (ProgHas.right (l₁ := [_]) (ProgHas.refl _)).left

/-- The program bundle. -/
abbrev AbF (p : Prog) : Prop := ProgHas p abProg

/-- **The model of `abstract1_fast`** (program- and fuel-free). -/
noncomputable def abF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF abProg "abstract1_fast" m args

theorem abF_spec (p : Prog) (hp : AbF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "abstract1_fast" args
    ⦃fun r s' => LocEq s' s₀ ∧ abF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec abProg_closed (hp.agree abFns) (List.mem_cons_self ..) n s₀ args

/-- `abstract1_fast` writes only the `abstract1` memo, the `fvarRange` memo and the store. -/
theorem abF_frame {m m' : Mem} {args r : List Word} (h : abF m args = some (r, m')) :
    MemFrame absA absC m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame abProg_closed (List.mem_cons_self ..) (run_of_callW hc)).1

/-- The adapter forwards to `abs_entry`. -/
theorem abAdapter_spec (n : Nat) (s₀ : St) (f e d k : Word) :
    ⦃fun s => s = s₀⦄ invoke abProg (exec abProg (n + 1)) "abstract1_fast" [f, e, d, k]
    ⦃fun r s' => LocEq s' s₀ ∧ fwd1 (callW abProg n "abs_entry" [e, d, k] s₀.mem) =
      some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (show abProg.lookup "abstract1_fast" = some L.Checker.abstract1FastA from rfl)]
  simp only [callFn, L.Checker.abstract1FastA]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec abProg n "abs_entry"] <;>
    finish [fwd1_some]

/-- **`abstract1_fast` refines `abstract1Fast coreWalkFuel` under the stage relation and a
well-formed `abstract1` memo** (replaces `IndStubs.abstract1Fast_spec`); the memo is well formed
after. -/
theorem abF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (e d k : Word)
    (he : H e) :
    RelW abF [CWF, e, d, k] (fun m a => StageR dn vis fe m a ∧ AbsOK m)
      (abstract1Fast CWF.toNat (decI e) d.toNat k.toNat)
      (fun m m' a r x => KeepPost dn vis fe decW0E m m' a r x ∧ AbsOK m') := by
  intro m m' a r h ⟨hS, ⟨mp, hmp⟩, hI1, hCr, hIl, hWk⟩
  have hfr := abF_frame h
  obtain ⟨n, hc⟩ := callF_run h
  rcases n with _ | n
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (abAdapter_spec n _ CWF e d k) hc
  obtain ⟨⟨rI, mI⟩, hi, hm⟩ := of_K hm rfl
  simp only [fwd1, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, hmI⟩ := hm
  rw [hs'] at hmI
  subst hmI
  rcases n with _ | j
  · rw [callW_zero] at hi; cases hi
  have hA : ArenaA m { a with memos := { a.memos with abs1C := mp } } :=
    ⟨hS.1.arena.memo_irrel a.memos.instLC mp, hmp⟩
  obtain ⟨s'', hs'', -, hok, hA', hres, hlt⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (absEntry_refines abProg abProg_abs rfl j _ _ hA e d k he) hi
  rw [hs''] at hA'
  have hrun := AM.run_of_ok _ _ hok
  have hrun' : (abstract1Fast coreWalkFuel (decE e) d.toNat k.toNat).run a =
      .ok (AM.res (abstract1Fast coreWalkFuel (decE e) d.toNat k.toNat)
          { a with memos := { a.memos with abs1C := mp } },
        AM.st (abstract1Fast coreWalkFuel (decE e) d.toNat k.toNat)
          { a with memos := { a.memos with abs1C := mp } }) := hrun
  have hcp := (keepsW_abs1Fast coreWalkFuel (decE e) d.toNat k.toNat).cp_of_cpl.run hrun'
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hA'.1 hfr (lt64A_of_all rfl) (lt64_of_all rfl) hcp
  exact ⟨_, _, by rw [CWF_eq]; exact hrun', ⟨hS', hg, hlt, hres.symm⟩, ⟨_, hA'.2⟩,
    hI1.frame hfr (by decide) (by decide), hCr.frame hfr (by decide) (by decide),
    hIl.frame hfr (by decide) (by decide),
    hWk.frame hfr (by decide) (by decide) (by decide) (by decide) (by decide)⟩

end L.Ind
