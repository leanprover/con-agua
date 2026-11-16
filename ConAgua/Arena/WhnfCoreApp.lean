module

import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.DerRel
import ConAgua.Front.Preserve
import ConRon.Arena.WFProofs
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.WhnfCore
import all ConAgua.Arena.WhnfCore
import ConAgua.L.WordOff
import ConAgua.Arena.Abs1Refine
import ConAgua.Arena.Inst1Refine

@[expose] public section

/-!
# `beta_peel` (proved) and `whnf_app` (groundwork): the batched β spine

`WhnfCore.lean`'s `betaPeelL` and `whnfAppL`, each a `while` loop over the spine's argument array
(`get_app_spine`'s slices `(ao, an)`, `(ao + an, an)`), with an accumulator (`beta_peel`) or the
head's growing argument vector (`whnf_app`) pushed at the top of the spine stack (`SPN` = 144,
top `CTL[136]`).

**Proved here: `betaPeel_refines`** (with the hypothesis
`hp : WhnfCoreProg p`). The method follows `WhnfCoreSlot.lean`'s loop: the loop is a named block
(`betaPeelW`, spliced into `betaPeelL'`, `betaPeelL_eq : betaPeelL = betaPeelL' := rfl`, so
`WhnfCore.lean` is untouched), its model `peelLoop` is by L fuel (callees through `callW`), the
block spec `betaPeelW_spec` is by induction on the fuel, `betaPeel_spec` is the function's, and
`peelFull_ref` is the refinement by induction on the fuel. What `WhnfCoreSlot.lean`'s loop does
not need: the model's memory changes under stack writes, so each step shows `SpineR` of the
growing accumulator after the push (`SpineR.push`) and `CoreS` across the write
(`CoreS.frame_stk`), and across `mk_app_n_from` (`CoreS.of_app`: `ArenaD` from the callee, the
rest of what `CoreS` reads kept by `keeps_cpl_mkAppNFrom`). `inst_list` is used through
`hil`, so the theorem depends on that stub's `sorry`.

**Handle words of `mk_app`/`mk_app_n_from` results.** `mkAppNFrom_refines` dropped `HW (r.headD 0)`;
`callW_mkApp`/`callW_mkAppNFrom` re-derive it from the store (`consInternM_lt`: a hit's index is below
the tier's node count, a push's below `2^27`).

**Proved in `WhnfCoreAppLoop.lean`: `app_ref`**, `whnf_app`'s one refinement, both outcomes, over
its unified model (`whnfAppE`), by induction on the L fuel (`appLoop_ref`: the `peelFull_ref`
pattern, with the twin's state and the mode maps generalized: a fired `iota_rec_at` moves both);
over `WhnfCallees` (`instList` through `betaPeel_refines'`) and `CoreCallees` (`iota` for
`iota_rec_at`), its errors `iota_rec_at`'s (`AppG`). `whnfApp_refines'` is its ok half.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- A write to `SPN` at an index below its size, and (separately or together) to `CTL[136]`, is
such a frame. -/
theorem spnCtl_frame (m : Mem) (i v w : Word) :
    MemFrame [SPN] [136] m ((m.set64 SPN i v).set64 CTL 136 w) :=
  ((MemFrame.set64 m SPN (by decide) i v).mono (by simp) (by simp)).trans
    ((MemFrame.setCtl (m.set64 SPN i v) 136 w).mono (by simp) (by simp))

/-! ## `CoreS` across the arena's interning

An `internE (.app _ _)` run changes the store's expression tables (and so `ArenaD`, supplied by
the interning's own refinement) and nothing `CoreS` reads from the twin's state besides: the
caches, the pins, the level/name stores `lss`. -/

/-- What `CoreS` reads of the twin's state, besides `ArenaD`. -/
def cpl (a : AState) : Caches × Pins × LsStore := (a.caches, a.pins, a.store.lss)

theorem keeps_cpl_internNodeE (v : ENodeView) : Keeps cpl (internNodeE v) := by
  unfold Keeps; intro a r a' h
  simp only [internNodeE, StateT.run_bind, StateT.run_get, pure_bind] at h
  repeat' split at h
  all_goals simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
    ConRon.Arena.fail, throwThe, MonadExceptOf.throw] at h
  all_goals first
    | (cases h; rfl)
    | (cases h; simp only [cpl, EStore.lss_intern])
    | (simp [throwThe, Functor.map, Except.map] at h)

theorem keeps_cpl_internApp (f x : EIdx) : Keeps cpl (internE (.app f x)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

theorem keeps_cpl_mkAppNFrom (f : EIdx) (args : Array EIdx) (i : Nat) :
    Keeps cpl (mkAppNFrom f args i) := by
  induction h : args.size - i generalizing f i with
  | zero =>
    rw [mkAppNFrom]; split
    · omega
    · exact Keeps.pure _
  | succ k ih =>
    rw [mkAppNFrom]; split
    · refine Keeps.bind (keeps_cpl_internApp _ _) (fun g => ?_)
      exact ih g (i + 1) (by omega)
    · exact Keeps.pure _

/-- **`CoreS` across an interning step**, `StoreDen` of the new state given (`hden`: an interning
of a `sort`/`const` node, `StoreDenIntern.lean`): `ArenaD` comes from the step's own refinement,
the twin's state keeps what else `CoreS` reads (`cpl`), and the memory write is confined to arrays
and `CTL` words outside the core tier, the pins and the environment. -/
theorem CoreS.arena_frameD {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List TieredArray} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a') (hcpl : cpl a' = cpl a)
    (hf : MemFrame A C m m')
    (h128 : ∀ b ∈ A, b.arr < 96 ∨ 128 ≤ b.arr) (hpins : (PINS : TieredArray) ∉ A)
    (henv : ∀ b ∈ A, b.arr < 129 ∨ 149 ≤ b.arr)
    (hC128 : ∀ x ∈ C, x.toNat < 96 ∨ 128 ≤ x.toNat)
    (hCenv : ∀ x ∈ C, x.toNat < 128 ∨ 136 ≤ x.toNat) (hden : StoreDen dn m' a' fe)
    (hmA : (ILMEMO : TieredArray) ∉ A ∧ (ABMEMO : TieredArray) ∉ A := by decide) (hmC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C := by decide)
    (hmWA : (WSM : TieredArray) ∉ A ∧ (FLM : TieredArray) ∉ A ∧ (LSM : TieredArray) ∉ A := by decide)
    (hmWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C := by decide)
    (hmLA : (LPMEMO : TieredArray) ∉ A ∧ (LPLMEMO : TieredArray) ∉ A ∧ (LPLSMEMO : TieredArray) ∉ A := by decide)
    (hmLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C := by decide) (hmode : ModeOK m')
    (hiw : L.Ind.IWOK m') (hhb : ∃ mp, L.Ind.hbMR m' mp) :
    CoreS dn m' a' vis fe M eb := by
  sorry

/-- **`CoreS` across an interning step** that writes neither the `sort` nor the `const` tables
(`StoreDen` carries over by `StoreDen.of_arena`). -/
theorem CoreS.arena_frame {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List TieredArray} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a') (hcpl : cpl a' = cpl a)
    (hf : MemFrame A C m m')
    (h128 : ∀ b ∈ A, b.arr < 96 ∨ 128 ≤ b.arr) (hpins : (PINS : TieredArray) ∉ A)
    (henv : ∀ b ∈ A, b.arr < 129 ∨ 149 ≤ b.arr)
    (hC128 : ∀ x ∈ C, x.toNat < 96 ∨ 128 ≤ x.toNat)
    (hCenv : ∀ x ∈ C, x.toNat < 128 ∨ 136 ≤ x.toNat)
    (hmA : (ILMEMO : TieredArray) ∉ A ∧ (ABMEMO : TieredArray) ∉ A := by decide) (hmC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C := by decide)
    (hmWA : (WSM : TieredArray) ∉ A ∧ (FLM : TieredArray) ∉ A ∧ (LSM : TieredArray) ∉ A := by decide)
    (hmWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C := by decide)
    (hmLA : (LPMEMO : TieredArray) ∉ A ∧ (LPLMEMO : TieredArray) ∉ A ∧ (LPLSMEMO : TieredArray) ∉ A := by decide)
    (hmLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C := by decide)
    (hscA : (SOREC : TieredArray) ∉ A ∧ (CREC : TieredArray) ∉ A ∧ tier1 SOREC ∉ A ∧ tier1 CREC ∉ A := by decide)
    (hscC : (1 : Word) ∉ C ∧ (16 : Word) ∉ C ∧ (17 : Word) ∉ C ∧ (18 : Word) ∉ C ∧ (19 : Word) ∉ C :=
      by decide) (hC0 : (0 : Word) ∉ C := by decide)
    (hiwA : (EREC : TieredArray) ∉ A ∧ (tier1 EREC : TieredArray) ∉ A ∧ (L.Ind.HBM : TieredArray) ∉ A := by decide)
    (hiwC : (129 : Word) ∉ C ∧ (130 : Word) ∉ C ∧ (200 : Word) ∉ C ∧ (214 : Word) ∉ C := by decide) :
    CoreS dn m' a' vis fe M eb := by
  have hk := hcpl
  simp only [cpl, Prod.mk.injEq] at hk
  exact hS.arena_frameD hD hcpl hf h128 hpins henv hC128 hCenv
    (hS.den.of_arena hS.arena.base hD.base hk.1 hk.2.1 hk.2.2 hf hscA hscC) hmA hmC hmWA hmWC hmLA hmLC
    (hS.mode.frame hf hC0 hscC.1)
    (hS.iwF hf hiwA.1 hiwA.2.1 hiwC.1 hiwC.2.1 hiwC.2.2.1) (hS.memos.hbF hf hiwA.2.2 hiwC.2.2.2)

/-- `CoreS.arena_frame` for a writer of the `hb` memo, its relation after the write given. -/
theorem CoreS.arena_frameHb {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List TieredArray} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a') (hcpl : cpl a' = cpl a)
    (hf : MemFrame A C m m')
    (h128 : ∀ b ∈ A, b.arr < 96 ∨ 128 ≤ b.arr) (hpins : (PINS : TieredArray) ∉ A)
    (henv : ∀ b ∈ A, b.arr < 129 ∨ 149 ≤ b.arr)
    (hC128 : ∀ x ∈ C, x.toNat < 96 ∨ 128 ≤ x.toNat)
    (hCenv : ∀ x ∈ C, x.toNat < 128 ∨ 136 ≤ x.toNat)
    (hmA : (ILMEMO : TieredArray) ∉ A ∧ (ABMEMO : TieredArray) ∉ A := by decide) (hmC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C := by decide)
    (hmWA : (WSM : TieredArray) ∉ A ∧ (FLM : TieredArray) ∉ A ∧ (LSM : TieredArray) ∉ A := by decide)
    (hmWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C := by decide)
    (hmLA : (LPMEMO : TieredArray) ∉ A ∧ (LPLMEMO : TieredArray) ∉ A ∧ (LPLSMEMO : TieredArray) ∉ A := by decide)
    (hmLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C := by decide)
    (hscA : (SOREC : TieredArray) ∉ A ∧ (CREC : TieredArray) ∉ A ∧ tier1 SOREC ∉ A ∧ tier1 CREC ∉ A := by decide)
    (hscC : (1 : Word) ∉ C ∧ (16 : Word) ∉ C ∧ (17 : Word) ∉ C ∧ (18 : Word) ∉ C ∧ (19 : Word) ∉ C :=
      by decide) (hC0 : (0 : Word) ∉ C := by decide)
    (hiw : L.Ind.IWOK m') (hhb : ∃ mp, L.Ind.hbMR m' mp) :
    CoreS dn m' a' vis fe M eb := by
  have hk := hcpl
  simp only [cpl, Prod.mk.injEq] at hk
  exact hS.arena_frameD hD hcpl hf h128 hpins henv hC128 hCenv
    (hS.den.of_arena hS.arena.base hD.base hk.1 hk.2.1 hk.2.2 hf hscA hscC) hmA hmC hmWA hmWC hmLA hmLC
    (hS.mode.frame hf hC0 hscC.1) hiw hhb

/-! ## Handle words of the interning functions' results

`mk_app` and `mk_app_n_from` post `decE` of their result only; the loop and the specs below need
the result word itself below `2^32` (`HW`): a hit's index is below the tier's node count, a push's
below `2^27`. -/

theorem ainternW_hw (m : Mem) (a : AState) (hR : AppR m a) (f x : Word) (w : Word) (m' : Mem)
    (hI : ainternW m f x = some (w, m')) : w.toNat < 2 ^ 32 := by
  exact consInternM_lt appCS_wf hR hI

/-- **`mk_app`'s result is a handle word.** -/
theorem mkAppW_hw (m : Mem) (a : AState) (hA : ArenaD m a) (f x r : Word) (m' : Mem)
    (hI : mkAppW m f x = some (r, m')) : r.toNat < 2 ^ 32 := by
  unfold mkAppW at hI
  split at hI
  · cases hI
  rcases hI₁ : ainternW m f x with _ | ⟨r₁, m₁⟩ <;> simp only [hI₁, mkK, reduceCtorEq] at hI
  cases hP : derPutW ADER 4 m₁ (cnt2 m 4) r₁
      (packBFL (maxW (derBW m f) (derBW m x)) (maxW (derFW m f) (derFW m x))
        (exprLPW m f ||| exprLPW m x)) with
  | none => simp [hP] at hI
  | some m₂ =>
  simp only [hP, Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  exact ainternW_hw m a hA.base.app f x _ m₁ hI₁

/-- **`mk_app_n_from`'s result is a handle word.** -/
theorem mkAppNFromW_hw : ∀ (K : Nat) (m : Mem) (a : AState) (f o n i : Word),
    K = n.toNat - i.toNat → ArenaD m a → f.toNat < 2 ^ 32 →
    ∀ r m', mkAppNFromW K m f o n i = some (r, m') → r.toNat < 2 ^ 32 := by
  intro K
  induction K with
  | zero =>
    intro m a f o n i hK hD hf r m' hL
    rw [mkAppNFromW] at hL
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    exact hf
  | succ K ih =>
    intro m a f o n i hK hD hf r m' hL
    have hin : i.toNat < n.toNat := by omega
    have hiw : i < n := hin
    rw [mkAppNFromW] at hL
    simp only [hiw, ↓reduceIte] at hL
    rcases hmk : mkAppW m f (spW m (o + i)) with _ | ⟨f₁, m₁⟩ <;> simp only [hmk, reduceCtorEq] at hL
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add]; simp
      have := n.toNat_lt
      omega
    obtain ⟨-, hArenaD, -⟩ := mkApp_ok m a hD f (spW m (o + i)) f₁ m₁ hmk
    exact ih m₁ _ f₁ o n (i + 1) (by omega) hArenaD (mkAppW_hw m a hD f _ f₁ m₁ hmk) r m' hL

/-- **`mk_app` as a run**: the twin's interning, `ArenaD` after it, the result word is a handle and
only the `app` tables and their derived-range cache are written. -/
theorem callW_mkApp (p : Prog) (hp : SpineProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (hD : ArenaD s₀.mem a₀) (f x : Word) (r : List Word) (m' : Mem)
    (h : callW p n "mk_app" [f, x] s₀.mem = some (r, m')) :
    AM.ok (internE (.app (decE f) (decE x))) a₀ ∧
    ArenaD m' (AM.st (internE (.app (decE f) (decE x))) a₀) ∧
    AM.res (internE (.app (decE f) (decE x))) a₀ = decE (r.headD 0) ∧
    MemFrame [AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] [4, 5] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, hm⟩ := triple_of_callW (mkApp_spec p hp.derb hp.appf hp.appp hp.appi hp.mkapp n
    s₀ f x) h
  obtain ⟨-, hm⟩ := hm
  obtain ⟨h1, h2, h3⟩ := mkApp_ok s₀.mem a₀ hD f x _ _ hm
  exact ⟨h1, h2, h3, L.Arena.mkAppW_frame _ _ _ _ _ hm, mkAppW_hw _ a₀ hD f x _ _ hm⟩

/-- **`mk_app_n_from` as a run.** -/
theorem callW_mkAppNFrom (p : Prog) (hp : SpineProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (hD : ArenaD s₀.mem a₀) (f o k i : Word) (xs : Array EIdx) (hf : HW f)
    (hx : SpineR s₀.mem o k xs) (hik : i.toNat ≤ k.toNat) (r : List Word) (m' : Mem)
    (h : callW p n "mk_app_n_from" [f, o, k, i] s₀.mem = some (r, m')) :
    AM.ok (mkAppNFrom (decE f) xs i.toNat) a₀ ∧
    ArenaD m' (AM.st (mkAppNFrom (decE f) xs i.toNat) a₀) ∧
    AM.res (mkAppNFrom (decE f) xs i.toNat) a₀ = decE (r.headD 0) ∧
    MemFrame [AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] [4, 5] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hok, hD', hres, hfr⟩ := triple_of_callW (Q := fun r s' =>
      LocEq s' s₀ ∧ AM.ok (mkAppNFrom (decE f) xs i.toNat) a₀ ∧
        ArenaD s'.mem (AM.st (mkAppNFrom (decE f) xs i.toNat) a₀) ∧
        AM.res (mkAppNFrom (decE f) xs i.toNat) a₀ = decE (r.headD 0) ∧
        MemFrame [AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] [4, 5] s₀.mem s'.mem)
    (mkAppNFrom_refines p hp n s₀ a₀ hD f o k i xs hf hx hik) h
  obtain ⟨s'', hm⟩ := triple_of_callW (mkAppNFromL_spec p hp.derb hp.appf hp.appp hp.appi hp.mkapp
    hp.mknf n s₀ f o k i) h
  exact ⟨hok, hD', hres, hfr, mkAppNFromW_hw _ s₀.mem a₀ f o k i rfl hD hf _ _ hm.2.2⟩

/-- **The `app` interning writes neither the stack nor its top.** -/
theorem StackKept.of_app_frame {m m' : Mem} (hf : MemFrame [AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] [4, 5] m m') :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.arr SPN (by simp [tier1, AREC, ASLOT, ADER, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.ctl 136 (by simp)
  exact StackKept.of_frame hf

/-- **`CoreS` across an `app` interning step.** -/
theorem CoreS.of_app {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a')
    (hcpl : cpl a' = cpl a) (hf : MemFrame [AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] [4, 5] m m') :
    CoreS dn m' a' vis fe M eb :=
  hS.arena_frame hD hcpl hf
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by decide)
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)

/-- `SpineR` of a slice below a bound `T` across a change that keeps the stack below `T`. -/
theorem SpineR.keepT {m m' : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (T : Word) (hsz : (m'.arr64 SPN).size = (m.arr64 SPN).size)
    (hk : ∀ i : Word, i < T → spW m' i = spW m i) (htop : off.toNat + cnt.toNat ≤ T.toNat)
    (hspn : (m.arr64 SPN).size < 2 ^ 63) : SpineR m' off cnt xs := by
  have hb := h.bound
  have hlt : ∀ i : Nat, i < cnt.toNat → off + i.toUInt64 < T := by
    intro i hi
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat']
    have : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨h.size, hsz ▸ hb, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hk _ (hlt i hi)]; exact h.lt i hi
  · rw [hk _ (hlt i (h.size ▸ hi))]; exact h.get i hi

/-! ## Pushing one word onto the spine stack -/

theorem spW_set64_eq (m : Mem) (p v : Word) (hb : p.toNat < (m.arr64 SPN).size) :
    spW (m.set64 SPN p v) p = v := by
  unfold spW; rw [L.Arena.rdW_set64, ite_eq_left ⟨rfl, rfl, hb⟩]

theorem spW_set64_ne (m : Mem) (p j v : Word) (hj : p ≠ j) :
    spW (m.set64 SPN p v) j = spW m j := by
  unfold spW; rw [L.Arena.rdW_set64, ite_eq_right (fun h => hj h.2.1)]

/-- **A push onto the spine stack extends `SpineR`**: the write is at the old top of the slice
(`off + cnt`), so every old entry's position is untouched. -/
theorem SpineR.push {m : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (hcap : (m.arr64 SPN).size < 2 ^ 63) (hb : off.toNat + cnt.toNat < (m.arr64 SPN).size)
    (v : Word) (hv : v.toNat < 2 ^ 32) :
    SpineR (m.set64 SPN (off + cnt) v) off (cnt + 1) (xs.push (decE v)) := by
  have hsz := h.bound
  have hsize := h.size
  have h1 : (1 : Word).toNat = 1 := by decide
  have hoc : (off + cnt).toNat = off.toNat + cnt.toNat := by
    simp only [UInt64.toNat_add]; omega
  have hcnt1 : (cnt + 1).toNat = cnt.toNat + 1 := by
    simp only [UInt64.toNat_add, h1]; omega
  have hidx : ∀ i : Nat, i ≤ cnt.toNat → (off + (i.toUInt64 : Word)).toNat = off.toNat + i := by
    intro i hi
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  have heqv : off + (cnt.toNat.toUInt64 : Word) = off + cnt :=
    UInt64.toNat_inj.mp (by rw [hidx cnt.toNat (by omega), hoc])
  have hnev : ∀ i : Nat, i < cnt.toNat → off + (i.toUInt64 : Word) ≠ off + cnt := by
    intro i hi hco
    have := congrArg UInt64.toNat hco
    rw [hidx i (by omega), hoc] at this
    omega
  have hbound : off.toNat + (cnt + 1).toNat ≤ ((m.set64 SPN (off + cnt) v).arr64 SPN).size := by
    rw [L.Mem.size64_set64, hcnt1]; omega
  refine ⟨by rw [Array.size_push, h.size, hcnt1], hbound, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hcnt1] at hi
    by_cases he : i = cnt.toNat
    · subst he
      rw [heqv, spW_set64_eq _ _ _ (by rw [hoc]; omega)]
      omega
    · rw [spW_set64_ne _ _ _ _ (hnev i (by omega)).symm]
      exact h.lt i (by omega)
  · rw [Array.size_push, h.size] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
    · rw [Array.getElem_push, dite_eq_left (by rw [h.size]; exact hi')]
      rw [h.get i (by rw [h.size]; exact hi')]
      congr 1
      rw [spW_set64_ne _ _ _ _ (hnev i hi').symm]
    · rw [Array.getElem_push, dite_eq_right (by omega)]
      have hieq : i = cnt.toNat := by omega
      subst hieq
      rw [heqv, spW_set64_eq _ _ _ (by rw [hoc]; omega), decE_eq]

/-! ## `beta_peel` refines `betaPeel` -/

/-- A write to `CTL` leaves every `SpineR` alone. -/
theorem SpineR.setCtl {m : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (c w : Word) : SpineR (m.set64 CTL c w) off cnt xs := by
  have e : (m.set64 CTL c w).arr64 SPN = m.arr64 SPN := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨h.size, by rw [e]; exact h.bound, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [spW, e]; exact h.lt i hi
  · simp only [spW, e]; exact h.get i hi

/-- A write to `CTL` keeps `spW` and the stack's size. -/
theorem spW_setCtl (m : Mem) (c w j : Word) : spW (m.set64 CTL c w) j = spW m j := by
  simp only [spW, Mem.arr64_set64_ne _ _ _ _ _ (show (SPN : TieredArray) ≠ CTL by decide)]

/-- **`beta_peel` refines `betaPeel t s args i`**: the peeled arguments are the spine range
`args[s:i]`, substituted straight from the stack slice. -/
theorem betaPeel_refines' (p : Prog) (hp : WhnfCoreProg p) (hil : InstListOK p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb t s ao an i : Word)
    (args : Array EIdx) (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (ht : HW t) (hsi : s ≤ i) (hia : i ≤ an)
    (har : SpineR s₀.mem ao an args) (hlo : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpec p (n + 1) "beta_peel" [t, s, ao, an, i]
      (betaPeel (decE t) s.toNat args i.toNat) decStep s₀ a₀ dn vis fe MM eb ResW := by
  sorry

end L.Arena
