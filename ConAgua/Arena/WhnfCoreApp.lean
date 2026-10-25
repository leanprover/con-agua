import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.PinsNatOp
import ConAgua.Arena.StoreDenIntern

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

**Proved in `WhnfCoreAppLoop.lean`: `whnfApp_refines'`** (with `hp : WhnfCoreProg p`, over
`WhnfCallees` (`instList` through `betaPeel_refines'`) and `CoreCallees` (`iota` for
`iota_rec_at`); the tagged `whnfApp_refines` instantiates the stub bundles). The loop of `whnfAppL` is spliced from named blocks
(`whnfAppW` is `while i < an { ⟪whnfAppBodyW⟫ }`, the body is `a := ..; node := ..; ⟪whnfAppLamW⟫;
⟪whnfAppRestW⟫`, the rest contains the ι arm `⟪whnfAppIotaW⟫`; `whnfAppL_eq := rfl`; a spliced block
must be a single statement unless it is the last of its sequence, which is why the push is not a
block of its own). Each block has its own model (`lamW`, `iotaW`, `appRestW`, `bodyW`) with callees
through `callW`, and its own small spec, which `vcgen` + `finish` closes: the blow-up came from
putting the two-result call, the `CTL` write and the loop's induction hypothesis in one goal. The
loop spec `whnfAppW_spec` is then by fuel induction against `bodyW_spec`, `whnfApp_spec` is the
function's, and `appFull_ref` the refinement by induction on the fuel (the `peelFull_ref` pattern,
with the twin's state and the mode maps generalized: a fired `iota_rec_at` moves both).
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
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a') (hcpl : cpl a' = cpl a)
    (hf : MemFrame A C m m')
    (h128 : ∀ b ∈ A, b < 96 ∨ 128 ≤ b) (hpins : (128 : ArrId) ∉ A)
    (henv : ∀ b ∈ A, b < 132 ∨ 144 ≤ b)
    (hC128 : ∀ x ∈ C, x.toNat < 96 ∨ 128 ≤ x.toNat)
    (hCenv : ∀ x ∈ C, x.toNat < 128 ∨ 136 ≤ x.toNat) (hden : StoreDen dn m' a' fe)
    (hmA : (50 : ArrId) ∉ A ∧ (49 : ArrId) ∉ A := by decide) (hmC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C := by decide)
    (hmWA : (151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A := by decide)
    (hmWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C := by decide)
    (hmLA : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A := by decide)
    (hmLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C := by decide) (hmode : ModeOK m') :
    CoreS dn m' a' vis fe M eb := by
  simp only [cpl, Prod.mk.injEq] at hcpl
  obtain ⟨hc, hp, hl⟩ := hcpl
  refine ⟨hD, ?_, ?_, hS.env.frame (fun b hb => (henv b hb).elim (fun h => .inl h) (fun h => .inr h))
      (fun x hx => (hCenv x hx).elim (fun h => .inl h) (fun h => .inr h)) hf, ?_, ?_, ?_,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn, hS.memos.frame hf hmA hmC hmWA hmWC hmLA hmLC,
      hf.2.2.1 145 ▸ hS.bstk, hden, hmode⟩
  · rw [hc]
    exact CoreRM.frame (A := A) (C := C)
      (fun b hb => (h128 b hb).elim (fun h => .inl h) (fun h => .inr h))
      (fun x hx => (hC128 x hx).elim (fun h => .inl h) (fun h => .inr h)) hf hS.core
  · rw [hp]; exact hS.pins.congr (hf.1 PINS hpins (by decide))
  · intro h l e; rw [hc] at e; have := hS.readL h l e; simp only [EStore.ls] at this ⊢; rw [hl]; exact this
  · intro h l e; rw [hc] at e; have := hS.readLs h l e; rw [hl]; exact this
  · rw [hl]; exact hS.nwf

/-- **`CoreS` across an interning step** that writes neither the `sort` nor the `const` tables
(`StoreDen` carries over by `StoreDen.of_arena`). -/
theorem CoreS.arena_frame {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a') (hcpl : cpl a' = cpl a)
    (hf : MemFrame A C m m')
    (h128 : ∀ b ∈ A, b < 96 ∨ 128 ≤ b) (hpins : (128 : ArrId) ∉ A)
    (henv : ∀ b ∈ A, b < 132 ∨ 144 ≤ b)
    (hC128 : ∀ x ∈ C, x.toNat < 96 ∨ 128 ≤ x.toNat)
    (hCenv : ∀ x ∈ C, x.toNat < 128 ∨ 136 ≤ x.toNat)
    (hmA : (50 : ArrId) ∉ A ∧ (49 : ArrId) ∉ A := by decide) (hmC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C := by decide)
    (hmWA : (151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A := by decide)
    (hmWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C := by decide)
    (hmLA : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A := by decide)
    (hmLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C := by decide)
    (hscA : SOREC ∉ A ∧ CREC ∉ A ∧ SOREC + 256 ∉ A ∧ CREC + 256 ∉ A := by decide)
    (hscC : (1 : Word) ∉ C ∧ (16 : Word) ∉ C ∧ (17 : Word) ∉ C ∧ (18 : Word) ∉ C ∧ (19 : Word) ∉ C :=
      by decide) (hC0 : (0 : Word) ∉ C := by decide) :
    CoreS dn m' a' vis fe M eb := by
  have hk := hcpl
  simp only [cpl, Prod.mk.injEq] at hk
  exact hS.arena_frameD hD hcpl hf h128 hpins henv hC128 hCenv
    (hS.den.of_arena hS.arena.1 hD.1 hk.1 hk.2.1 hk.2.2 hf hscA hscC) hmA hmC hmWA hmWC hmLA hmLC
    (hS.mode.frame hf hC0 hscC.1)

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
  rcases hI₁ : ainternW m f x with _ | ⟨r₁, m₁⟩ <;> simp only [hI₁, mkK, mkK_some, reduceCtorEq] at hI
  cases hP : derPutW ADER 4 m₁ (cnt2 m 4) r₁
      (packBFL (maxW (derBW m f) (derBW m x)) (maxW (derFW m f) (derFW m x))
        (exprLPW m f ||| exprLPW m x)) with
  | none => simp [hP] at hI
  | some m₂ =>
  simp only [hP, Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  exact ainternW_hw m a hA.1.app f x _ m₁ hI₁

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
    MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, hm⟩ := triple_of_callW (mkApp_spec p hp.derb hp.appf hp.appp hp.appi hp.mkapp n
    s₀ f x) h
  obtain ⟨-, hm⟩ := hm
  obtain ⟨h1, h2, h3⟩ := mkApp_ok s₀.mem a₀ hD f x _ _ hm
  exact ⟨h1, h2, h3, mkAppW_frame _ _ _ _ _ hm, mkAppW_hw _ a₀ hD f x _ _ hm⟩

/-- **`mk_app_n_from` as a run.** -/
theorem callW_mkAppNFrom (p : Prog) (hp : SpineProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (hD : ArenaD s₀.mem a₀) (f o k i : Word) (xs : Array EIdx) (hf : HW f)
    (hx : SpineR s₀.mem o k xs) (hik : i.toNat ≤ k.toNat) (r : List Word) (m' : Mem)
    (h : callW p n "mk_app_n_from" [f, o, k, i] s₀.mem = some (r, m')) :
    AM.ok (mkAppNFrom (decE f) xs i.toNat) a₀ ∧
    ArenaD m' (AM.st (mkAppNFrom (decE f) xs i.toNat) a₀) ∧
    AM.res (mkAppNFrom (decE f) xs i.toNat) a₀ = decE (r.headD 0) ∧
    MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hok, hD', hres, hfr⟩ := triple_of_callW (Q := fun r s' =>
      LocEq s' s₀ ∧ AM.ok (mkAppNFrom (decE f) xs i.toNat) a₀ ∧
        ArenaD s'.mem (AM.st (mkAppNFrom (decE f) xs i.toNat) a₀) ∧
        AM.res (mkAppNFrom (decE f) xs i.toNat) a₀ = decE (r.headD 0) ∧
        MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] s₀.mem s'.mem)
    (mkAppNFrom_refines p hp n s₀ a₀ hD f o k i xs hf hx hik) h
  obtain ⟨s'', hm⟩ := triple_of_callW (mkAppNFromL_spec p hp.derb hp.appf hp.appp hp.appi hp.mkapp
    hp.mknf n s₀ f o k i) h
  exact ⟨hok, hD', hres, hfr, mkAppNFromW_hw _ s₀.mem a₀ f o k i rfl hD hf _ _ hm.2.2⟩

/-- **The `app` interning writes neither the stack nor its top.** -/
theorem StackKept.of_app_frame {m m' : Mem} (hf : MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] m m') :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (by simp [AREC, ASLOT, ADER, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  exact StackKept.of_frame hf

/-- **`CoreS` across an `app` interning step.** -/
theorem CoreS.of_app {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a')
    (hcpl : cpl a' = cpl a) (hf : MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] m m') :
    CoreS dn m' a' vis fe M eb :=
  hS.arena_frame hD hcpl hf
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp [AREC, ASLOT, ADER, PINS])
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

theorem decE_tag_lam (e : Word) (hh : e.toNat < 2 ^ 32) :
    ((decE e).tag == ETag.lam) = decide (e >>> 28 = 5) := by
  have := decE_tag_eq e hh 5 (by decide)
  by_cases h : e >>> 28 = 5
  · have h2 : (decE e).tag = UInt32.ofNat 5 := this.mpr h
    simp [h, ETag.lam, h2]
  · have h2 : ¬ (decE e).tag = UInt32.ofNat 5 := fun h' => h (this.mp h')
    simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq, ETag.lam]
    exact h2

/-! ## Pushing one word onto the spine stack -/

theorem spW_set64_eq (m : Mem) (p v : Word) (hb : p.toNat < (m.arr64 SPN).size) :
    spW (m.set64 SPN p v) p = v := by
  unfold spW; rw [rdW_set64L, if_pos ⟨rfl, rfl, hb⟩]

theorem spW_set64_ne (m : Mem) (p j v : Word) (hj : p ≠ j) :
    spW (m.set64 SPN p v) j = spW m j := by
  unfold spW; rw [rdW_set64L, if_neg (fun h => hj h.2.1)]

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
    rw [size_set64L, hcnt1]; omega
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
    · rw [Array.getElem_push, dif_pos (by rw [h.size]; exact hi')]
      rw [h.get i (by rw [h.size]; exact hi')]
      congr 1
      rw [spW_set64_ne _ _ _ _ (hnev i hi').symm]
    · rw [Array.getElem_push, dif_neg (by omega)]
      have hieq : i = cnt.toNat := by omega
      subst hieq
      rw [heqv, spW_set64_eq _ _ _ (by rw [hoc]; omega), decE_eq]

/-! ## `beta_peel`: the loop as a named block -/

/-- The loop of `betaPeelL` (WhnfCore.lean), named for its spec. -/
def betaPeelW : Stmt := lblk (t, a, ao, an, i, co, cn, tt, x, e2, e3) {
  while i < an {
    if t >> 28 != 5 {
      e2 := call inst_list(t, co, cn, 0);
      e3 := call mk_app_n_from(e2, ao, an, i);
      CTL.u64[136] := co;
      return (1, e3)
    };
    tt := ⟦t⟧.tier;
    x := ⟦t⟧.idx;
    if tt != 0 && CTL.u64[1] == 0 { abort };
    if LAM⟨tt⟩.count <= x { abort };
    t := LAM⟨tt, x⟩.b;
    if len(SPN.u64) <= co + cn { abort };
    SPN.u64[co + cn] := SPN.u64[ao + i];
    cn += 1;
    CTL.u64[136] := co + cn;
    i += 1
  }
}

/-- `betaPeelL`, with its loop spliced from `betaPeelW`.
con-ron: ConRon/Arena/Core.lean:2202-2221 ConRon.Arena.betaPeel -/
def betaPeelL' : FunDecl := lfn (t, a, ao, an, i) locals (co, cn, tt, x, e2, e3) {
  co := CTL.u64[136];
  if len(SPN.u64) <= co { abort };
  SPN.u64[co] := a;
  cn := 1;
  CTL.u64[136] := co + 1;
  ⟪betaPeelW⟫;
  e2 := call inst_list(t, co, cn, 0);
  CTL.u64[136] := co;
  return (1, e2)
}

theorem betaPeelL_eq : betaPeelL = betaPeelL' := rfl

/-- How a loop ends: by a `return` (`st`, `r`, the memory) or by its condition failing (the
locals the tail reads: `t`, `cn`, and the memory). -/
inductive LoopOut
  | ret (st r : Word) (m : Mem)
  | exit (t cn : Word) (m : Mem)

/-- **The model of the peel loop** at L fuel `k`. -/
def peelLoop (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word →
    Option LoopOut
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, t, ao, an, i, co, cn =>
    if i < an then
      if t >>> 28 ≠ 5 then
        match callW p k "inst_list" [t, co, cn, 0] m with
        | none => none
        | some (r₁, m₁) =>
          match callW p k "mk_app_n_from" [r₁.headD 0, ao, an, i] m₁ with
          | none => none
          | some (r₂, m₂) => some (.ret 1 (r₂.headD 0) (m₂.set64 CTL 136 co))
      else if tierW t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
      else if tcnt m LAM (tierW t) ≤ idxW t then none
      else if m.len64 SPN ≤ co + cn then none
      else peelLoop p k ((m.set64 SPN (co + cn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
          (co + cn + 1)) (tfld m LAM (tierW t) (idxW t) 1) ao an (i + 1) co (cn + 1)
    else some (.exit t cn m)

/-- The end of a loop run, as the model's: a `return`, or the exit with the tail's locals. -/
def LoopOut.ofSig (r : Sig) (s' : St) : LoopOut :=
  match r with
  | .ret v => .ret (v.headD 0) (v.tail.headD 0) s'.mem
  | _ => .exit (s'.loc 0) (s'.loc 6) s'.mem

theorem betaPeelW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n betaPeelW
    ⦃fun r s' => r ≠ .brk ∧ s'.loc 5 = s₀.loc 5 ∧
      peelLoop p n s₀.mem (s₀.loc 0) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6) =
        some (LoopOut.ofSig r s') ∧ (∀ v, r = .ret v → (136 : Word).toNat < (s'.mem.arr64 CTL).size);
      ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := betaPeelW) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM,
        evalE_tierE, evalE_idxE, st64, ih,
        callW_spec p n "inst_list", callW_spec p n "mk_app_n_from"] <;>
      finish [peelLoop, tierW, idxW, LoopOut.ofSig]

/-- **The model of `beta_peel`** at L fuel `n + 1`. -/
def betaPeelFnW (p : Prog) (n : Nat) (m : Mem) (t a ao an i : Word) : Option (Word × Word × Mem) :=
  if m.len64 SPN ≤ rdW (m.arr64 CTL) 136 then none
  else
    match peelLoop p (n + 1) ((m.set64 SPN (rdW (m.arr64 CTL) 136) a).set64 CTL 136
        (rdW (m.arr64 CTL) 136 + 1)) t ao an i (rdW (m.arr64 CTL) 136) 1 with
    | none => none
    | some (.ret st r m₂) => some (st, r, m₂)
    | some (.exit t' cn m₂) =>
      match callW p n "inst_list" [t', rdW (m.arr64 CTL) 136, cn, 0] m₂ with
      | none => none
      | some (r₁, m₃) => some (1, r₁.headD 0, m₃.set64 CTL 136 (rdW (m.arr64 CTL) 136))

theorem betaPeel_spec (p : Prog) (hp : p.lookup "beta_peel" = some betaPeelL) (n : Nat) (s₀ : St)
    (t a ao an i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "beta_peel" [t, a, ao, an, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      betaPeelFnW p n s₀.mem t a ao an i = some (r.headD 0, r.tail.headD 0, s'.mem) ∧
      (136 : Word).toNat < (s₀.mem.arr64 CTL).size ∧
      (136 : Word).toNat < (s'.mem.arr64 CTL).size; ⊤⦄ := by
  rw [invoke_eq _ hp, betaPeelL_eq]
  simp only [callFn, betaPeelL']
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      fun s => Triple.step_exec (betaPeelW_spec p (n + 1) s),
      callW_spec p n "inst_list"] <;>
    finish [betaPeelFnW, rdW, size_set64, LoopOut.ofSig]

/-! ## `beta_peel` refines `betaPeel` -/

/-- The tail of `beta_peel`: the substitution, the top put back. -/
def peelTail (p : Prog) (n : Nat) (m : Mem) (t co cn : Word) : Option (Word × Word × Mem) :=
  match callW p n "inst_list" [t, co, cn, 0] m with
  | none => none
  | some (r₁, m₃) => some (1, r₁.headD 0, m₃.set64 CTL 136 co)

/-- The loop with its tail: the `beta_peel` body after its prologue. -/
def peelFull (p : Prog) (n k : Nat) (m : Mem) (t ao an i co cn : Word) :
    Option (Word × Word × Mem) :=
  match peelLoop p k m t ao an i co cn with
  | none => none
  | some (.ret st r m') => some (st, r, m')
  | some (.exit t' cn' m') => peelTail p n m' t' co cn'

theorem betaPeelFnW_eq (p : Prog) (n : Nat) (m : Mem) (t a ao an i : Word) :
    betaPeelFnW p n m t a ao an i =
      if m.len64 SPN ≤ rdW (m.arr64 CTL) 136 then none
      else peelFull p n (n + 1) ((m.set64 SPN (rdW (m.arr64 CTL) 136) a).set64 CTL 136
        (rdW (m.arr64 CTL) 136 + 1)) t ao an i (rdW (m.arr64 CTL) 136) 1 := by
  unfold betaPeelFnW peelFull peelTail
  split
  · rfl
  · rfl

theorem peelFull_zero (p : Prog) (n : Nat) (m : Mem) (t ao an i co cn : Word) :
    peelFull p n 0 m t ao an i co cn = none := rfl

theorem peelFull_exit (p : Prog) (n k : Nat) (m : Mem) (t ao an i co cn : Word) (h : ¬ i < an) :
    peelFull p n (k + 1) m t ao an i co cn = peelTail p n m t co cn := by
  simp [peelFull, peelLoop, h]

theorem peelFull_ret (p : Prog) (n k : Nat) (m : Mem) (t ao an i co cn : Word) (h : i < an)
    (ht : t >>> 28 ≠ 5) :
    peelFull p n (k + 1) m t ao an i co cn =
      (match callW p k "inst_list" [t, co, cn, 0] m with
        | none => none
        | some (r₁, m₁) =>
          match callW p k "mk_app_n_from" [r₁.headD 0, ao, an, i] m₁ with
          | none => none
          | some (r₂, m₂) => some (1, r₂.headD 0, m₂.set64 CTL 136 co)) := by
  simp only [peelFull, peelLoop, h, ht, ↓reduceIte, ne_eq, not_false_eq_true]
  rcases h1 : callW p k "inst_list" [t, co, cn, 0] m with _ | ⟨r₁, m₁⟩
  · simp
  · simp only
    rcases h2 : callW p k "mk_app_n_from" [r₁.headD 0, ao, an, i] m₁ with _ | ⟨r₂, m₂⟩
    · simp
    · simp

theorem peelFull_step (p : Prog) (n k : Nat) (m : Mem) (t ao an i co cn : Word) (h : i < an)
    (ht : ¬ t >>> 28 ≠ 5) (h1 : ¬ (tierW t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (h2 : ¬ tcnt m LAM (tierW t) ≤ idxW t) (h3 : ¬ m.len64 SPN ≤ co + cn) :
    peelFull p n (k + 1) m t ao an i co cn =
      peelFull p n k ((m.set64 SPN (co + cn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
          (co + cn + 1)) (tfld m LAM (tierW t) (idxW t) 1) ao an (i + 1) co
          (cn + 1) := by
  simp only [peelFull, peelLoop, h, ht, h1, h2, h3, ↓reduceIte, ne_eq, not_false_eq_true,
    not_true_eq_false]

/-- A write to `CTL` leaves every `SpineR` alone. -/
theorem SpineR.setCtl {m : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (c w : Word) : SpineR (m.set64 CTL c w) off cnt xs := by
  have e : (m.set64 CTL c w).arr64 SPN = m.arr64 SPN := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨h.size, by rw [e]; exact h.bound, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [spW, e]; exact h.lt i hi
  · simp only [spW, e]; exact h.get i hi

/-- A write to `CTL` keeps `spW` and the stack's size. -/
theorem spW_setCtl (m : Mem) (c w j : Word) : spW (m.set64 CTL c w) j = spW m j := by
  simp only [spW, Mem.arr64_set64_ne _ _ _ _ _ (show SPN ≠ CTL by decide)]

/-- The top put back after a run that kept the stack below the loop's own start. -/
theorem peel_restore {m₀ m m₃ : Mem} {co cn : Word} (hco : co = spTop m₀)
    (hb : ∀ j : Word, j < co → spW m j = spW m₀ j) (hsz : (m.arr64 SPN).size = (m₀.arr64 SPN).size)
    (hbk : BKept m₀ m) (hpg : PoolGrew m₀ m)
    (hSt : StackKept m m₃) (htop : spTop m = co + cn) (hcn : co.toNat + cn.toNat < 2 ^ 64)
    (h136 : (136 : Word).toNat < (m₃.arr64 CTL).size) :
    StackKept m₀ (m₃.set64 CTL 136 co) := by
  have hr : rdW (m₀.arr64 CTL) 136 = co := by rw [hco]; rfl
  have := StackKept.restore (m := m₀) (m₁ := m₃) (fun j hj => by
      have hjc : j < co := hco ▸ hj
      have : j < spTop m := by
        rw [htop, UInt64.lt_iff_toNat_lt, addW _ _ hcn]
        have := UInt64.lt_iff_toNat_lt.mp hjc
        omega
      rw [hSt.below j this, hb j hjc]) (by rw [hSt.size, hsz]) (hbk.trans hSt.bstk)
      (hpg.trans hSt.pool) h136
  rwa [hr] at this

/-- The state `CoreAfter`-style conclusion of a `beta_peel` run from the loop's memory `m`. -/
def PeelPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb : Word) (m₀ : Mem) (a : AState) (T : AM WhnfStep) (st r : Word) (mF : Mem) : Prop :=
  ∃ x a', T.run a = .ok (x, a') ∧ x = decStep [st, r] ∧ ResW [st, r] ∧
    ∃ M', CoreS dn mF a' vis fe M' eb ∧ KeptAll MM M' eb ∧ StackKept m₀ mF

theorem peelFull_ref (p : Prog) (hp : SpineProg p) (hil : InstListOK p) (n : Nat) (ao an : Word) (args : Array EIdx)
    (co : Word) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb : Word) (a : AState) (m₀ : Mem) (har₀ : SpineR m₀ ao an args) (hco : co = spTop m₀)
    (hlo : ao.toNat + an.toNat ≤ co.toNat) :
    ∀ (k : Nat) (m : Mem) (t i cn : Word) (acc : Array EIdx),
      CoreS dn m a vis fe MM eb → HW t → SpineR m co cn acc → spTop m = co + cn →
      (∀ j : Word, j < co → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      BKept m₀ m → PoolGrew m₀ m → (136 : Word).toNat < (m.arr64 CTL).size →
      ∀ st r mF, peelFull p n k m t ao an i co cn = some (st, r, mF) →
      (136 : Word).toNat < (mF.arr64 CTL).size →
      PeelPost dn vis fe MM eb m₀ a (betaPeel (decE t) acc args i.toNat) st r mF := by
  intro k
  induction k with
  | zero => intro m t i cn acc _ _ _ _ _ _ _ _ _ st r mF hF; rw [peelFull_zero] at hF; cases hF
  | succ k ih =>
    intro m t i cn acc hS ht hacc htop hb hsz hbk hpg h136m st r mF hF h136
    have hspn := hS.spn
    have hco_le : co.toNat + cn.toNat ≤ (m.arr64 SPN).size := hacc.bound
    have hcn64 : co.toNat + cn.toNat < 2 ^ 64 := by omega
    have hadd : (co + cn).toNat = co.toNat + cn.toNat := addW _ _ hcn64
    have hspT : (spTop m).toNat = co.toNat + cn.toNat := by rw [htop, hadd]
    have har : SpineR m ao an args :=
      har₀.keepT co hsz hb hlo (hsz ▸ hspn)
    by_cases hlt : i < an
    · by_cases ht5 : t >>> 28 = 5
      · -- the λ step: the argument is pushed and the loop goes on with the body
        have hc1 : ¬ (tierW t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := fun h => by
          simp [peelFull, peelLoop, hlt, ht5, h] at hF
        have hc2 : ¬ tcnt m LAM (tierW t) ≤ idxW t := fun h => by
          simp [peelFull, peelLoop, hlt, ht5, hc1, h] at hF
        have hc3 : ¬ m.len64 SPN ≤ co + cn := fun h => by
          simp [peelFull, peelLoop, hlt, ht5, hc1, hc2, h] at hF
        rw [peelFull_step _ _ _ _ _ _ _ _ _ _ hlt (fun h => h ht5) hc1 hc2 hc3] at hF
        have hv : viewOK m t LAM := ⟨hc1, UInt64.not_le.mp hc2⟩
        obtain ⟨-, -, hbody1⟩ := view_lam m a hS.arena.1 t ht hv ht5
        have hvb := viewBind_lam m a hS.arena.1 t ht hv ht5
        have hlt' : i.toNat < args.size := by
          rw [har₀.size]; exact UInt64.lt_iff_toNat_lt.mp hlt
        have hit : (i.toNat).toUInt64 = i := by simp
        have hxi : args[i.toNat] = decE (spW m (ao + i)) := by
          have h := har.get i.toNat hlt'
          rwa [hit] at h
        have hvv : (spW m (ao + i)).toNat < 2 ^ 32 := by
          have h := har.lt i.toNat (by rw [← har.size]; exact hlt')
          rwa [hit] at h
        have hbd : co.toNat + cn.toNat < (m.arr64 SPN).size := by
          have h : ¬ UInt64.ofNat (m.arr64 SPN).size ≤ co + cn := hc3
          rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), hadd] at h
          omega
        have hS' := hS.frame_stk (spnCtl_frame m (co + cn) (spW m (ao + i)) (co + cn + 1))
          (by simp) (by simp)
        have hacc' := (hacc.push hspn hbd (spW m (ao + i)) hvv).setCtl 136 (co + cn + 1)
        have htop' : spTop ((m.set64 SPN (co + cn) (spW m (ao + i))).set64 CTL 136 (co + cn + 1)) =
            co + (cn + 1) := by
          unfold spTop
          rw [rdW_set64, if_pos ⟨rfl, rfl, by rw [size_set64]; exact h136m⟩, UInt64.add_assoc]
        have hb' : ∀ j : Word, j < co →
            spW ((m.set64 SPN (co + cn) (spW m (ao + i))).set64 CTL 136 (co + cn + 1)) j =
              spW m₀ j := by
          intro j hj
          rw [spW_setCtl, spW_set64_ne _ _ _ _ (fun h => by
            have := UInt64.lt_iff_toNat_lt.mp hj
            rw [← h, hadd] at this; omega)]
          exact hb j hj
        have hi1 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt64.toNat_add]; simp
          have := UInt64.lt_iff_toNat_lt.mp hlt
          have := an.toNat_lt
          omega
        obtain ⟨x, a', hrun', hx, hrw, M', hS'', hK, hSt⟩ := ih _ _ (i + 1) (cn + 1)
          (acc.push (decE (spW m (ao + i)))) hS' hbody1 hacc' htop' hb'
          (by simp only [size_set64]; exact hsz)
          (hbk.trans (BKept.of_frame (spnCtl_frame m (co + cn) (spW m (ao + i)) (co + cn + 1))
            (by decide) (by decide)))
          (hpg.trans (PoolGrew.of_frame (spnCtl_frame m (co + cn) (spW m (ao + i)) (co + cn + 1))
            (by decide) (by decide)))
          (by simp only [size_set64]; exact h136m)
          st r mF hF h136
        have hlam : ((decE t).tag == ETag.lam) = true := by
          rw [decE_tag_lam t ht]; simp [ht5]
        refine ⟨x, a', ?_, hx, hrw, M', hS'', hK, hSt⟩
        rw [← hrun', betaPeel]
        simp only [hlt', dite_true, hlam, ite_true, StateT.run_bind, viewBind_run', hvb,
          except_ok_bind, hxi, hi1]
      · rw [peelFull_ret _ _ _ _ _ _ _ _ _ _ hlt ht5] at hF
        cases h1 : callW p k "inst_list" [t, co, cn, 0] m with
        | none => rw [h1] at hF; simp at hF
        | some q =>
        obtain ⟨r₁, m₁⟩ := q
        rw [h1] at hF; dsimp only at hF
        cases h2 : callW p k "mk_app_n_from" [r₁.headD 0, ao, an, i] m₁ with
        | none => rw [h2] at hF; simp at hF
        | some q2 =>
        obtain ⟨r₂, m₂⟩ := q2
        rw [h2] at hF; dsimp only at hF
        obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hF)
        have hinst := hil k ⟨m, Locals.init []⟩ a dn vis fe MM eb t co cn 0
          acc hS ht hacc (by rw [hspT]; omega)
        obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hrw⟩ := CoreSpec.of_callW hinst h1
        have h0 : (0 : Word).toNat = 0 := rfl
        rw [h0] at hok hres hS'
        have hx : SpineR m₁ ao an args :=
          har₀.keepT co (hSt'.size.trans hsz)
            (fun j hj => (hSt'.below j (by
              rw [htop, UInt64.lt_iff_toNat_lt, hadd]
              have := UInt64.lt_iff_toNat_lt.mp hj; omega)).trans (hb j hj)) hlo (hsz ▸ hspn)
        obtain ⟨hok2, hD2, hres2, hfr2, hhw2⟩ := callW_mkAppNFrom p hp k ⟨m₁, Locals.init []⟩ _
          hS'.arena (r₁.headD 0) ao an i args hrw hx
          (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlt)) r₂ m₂ h2
        have hcpl := Keeps.run (keeps_cpl_mkAppNFrom (decE (r₁.headD 0)) args i.toNat)
          (AM.run_of_ok _ _ hok2)
        have hS2 := hS'.of_app hD2 hcpl hfr2
        have hSt2 : StackKept m m₂ := hSt'.trans (StackKept.of_app_frame hfr2)
        have hnlam : ((decE t).tag == ETag.lam) = false := by
          rw [decE_tag_lam t ht]; simp [ht5]
        have hlt' : i.toNat < args.size := by
          rw [har₀.size]; exact UInt64.lt_iff_toNat_lt.mp hlt
        have hrun : (betaPeel (decE t) acc args i.toNat).run a =
            .ok (WhnfStep.cont (decE (r₂.headD 0)), AM.st (mkAppNFrom (decE (r₁.headD 0)) args i.toNat)
              (AM.st (instantiateListFast coreWalkFuel (decE t) acc 0) a)) := by
          rw [betaPeel]
          simp only [hlt', dite_true, hnlam, Bool.false_eq_true, ite_false, StateT.run_bind,
            AM.run_of_ok _ _ hok, except_ok_bind]
          have hres' : AM.res (instantiateListFast coreWalkFuel (decE t) acc 0) a =
              decE (r₁.headD 0) := hres
          rw [hres', AM.run_of_ok _ _ hok2, hres2]
          rfl
        have h136' : (136 : Word).toNat < (m₂.arr64 CTL).size := by
          rwa [size_set64] at h136
        refine ⟨_, _, hrun, ?_, ⟨by simp [HW], hhw2⟩, M', ?_, hK', ?_⟩
        · simp [decStep]
        · exact hS2.frame_stk (MemFrame.setCtl m₂ 136 co) (by simp) (by simp)
        · exact peel_restore hco hb hsz hbk hpg hSt2 htop hcn64 h136'
    · rw [peelFull_exit _ _ _ _ _ _ _ _ _ _ hlt] at hF
      unfold peelTail at hF
      rcases h1 : callW p n "inst_list" [t, co, cn, 0] m with _ | ⟨r₁, m₃⟩ <;> simp only [h1, reduceCtorEq] at hF
      obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hF)
      have hinst := hil n ⟨m, Locals.init []⟩ a dn vis fe MM eb t co cn 0
        acc hS ht hacc (by rw [hspT]; omega)
      obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hrw⟩ := CoreSpec.of_callW hinst h1
      have h0 : (0 : Word).toNat = 0 := rfl
      rw [h0] at hok hres hS'
      have hnlt : ¬ i.toNat < args.size := by
        rw [har₀.size]; exact fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      have hrun : (betaPeel (decE t) acc args i.toNat).run a =
          .ok (WhnfStep.cont (decE (r₁.headD 0)), AM.st (instantiateListFast coreWalkFuel (decE t) acc 0) a) := by
        rw [betaPeel]
        simp only [hnlt, dite_false, StateT.run_bind, AM.run_of_ok _ _ hok, except_ok_bind, hres]
        rfl
      have h136' : (136 : Word).toNat < (m₃.arr64 CTL).size := by
        rwa [size_set64] at h136
      refine ⟨_, _, hrun, ?_, ⟨by simp [HW], hrw⟩, M', ?_, hK', ?_⟩
      · simp [decStep]
      · exact hS'.frame_stk (MemFrame.setCtl m₃ 136 co) (by simp) (by simp)
      · exact peel_restore hco hb hsz hbk hpg hSt' htop hcn64 h136'

/-- **`beta_peel` refines `betaPeel t #[a] args i`.** -/
theorem betaPeel_refines' (p : Prog) (hp : WhnfCoreProg p) (hil : InstListOK p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb t a ao an i : Word)
    (args : Array EIdx) (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (ht : HW t) (ha : HW a)
    (har : SpineR s₀.mem ao an args) (hlo : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpec p (n + 1) "beta_peel" [t, a, ao, an, i]
      (betaPeel (decE t) #[decE a] args i.toNat) decStep s₀ a₀ dn vis fe MM eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW, h136i, h136⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (betaPeel_spec p hp.peel n s₀ t a ao an i)
  subst hs0
  refine ⟨hloc, ?_⟩
  rw [betaPeelFnW_eq] at hW
  split at hW
  · cases hW
  rename_i hcap
  obtain ⟨co, hcodef⟩ : ∃ co, co = rdW (s.mem.arr64 CTL) 136 := ⟨_, rfl⟩
  rw [← hcodef] at hW hcap
  have hco : co = spTop s.mem := hcodef
  have hspn := hS.spn
  have hcoSz : co.toNat < (s.mem.arr64 SPN).size := by
    have h : ¬ UInt64.ofNat (s.mem.arr64 SPN).size ≤ co := hcap
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at h
    omega
  have h0 : (0 : Word).toNat = 0 := rfl
  have hacc0 : SpineR s.mem co 0 #[] :=
    ⟨by simp [h0], by rw [h0]; omega, fun i hi => by rw [h0] at hi; omega,
      fun i hi => by simp at hi⟩
  have hacc := (hacc0.push hspn (by rw [h0]; omega) a ha).setCtl 136 (co + 0 + 1)
  have hco0 : co + 0 = co := UInt64.add_zero co
  rw [hco0] at hacc
  have e1 : (0 : Word) + 1 = 1 := rfl
  rw [e1] at hacc
  have hS1 := hS.frame_stk (spnCtl_frame s.mem co a (co + 1)) (by simp) (by simp)
  have htop1 : spTop ((s.mem.set64 SPN co a).set64 CTL 136 (co + 1)) = co + 1 := by
    unfold spTop
    rw [rdW_set64, if_pos ⟨rfl, rfl, by rw [size_set64]; exact h136i⟩]
  have hb1 : ∀ j : Word, j < co →
      spW ((s.mem.set64 SPN co a).set64 CTL 136 (co + 1)) j = spW s.mem j := by
    intro j hj
    rw [spW_setCtl, spW_set64_ne _ _ _ _ (fun h => by
      have := UInt64.lt_iff_toNat_lt.mp hj
      rw [← h] at this; omega)]
  obtain ⟨x, a', hrun', hx, hrw, M', hS', hK, hSt⟩ := peelFull_ref p hp.spine hil n ao an args co dn vis
    fe MM eb a₀ s.mem har hco (by rw [hco]; exact hlo) (n + 1) _ t i 1 #[decE a] hS1 ht hacc htop1 hb1
    (by simp only [size_set64])
    (BKept.of_frame (spnCtl_frame s.mem co a (co + 1)) (by decide) (by decide))
    (PoolGrew.of_frame (spnCtl_frame s.mem co a (co + 1)) (by decide) (by decide))
    (by simp only [size_set64]; exact h136i) _ _ _ hW h136
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hok, ?_, ?_, ?_⟩
  · rw [hst]; exact ⟨M', hS', hK, hSt⟩
  · rw [hres, hx]; simp [decStep]
  · exact hrw

end L.Arena
