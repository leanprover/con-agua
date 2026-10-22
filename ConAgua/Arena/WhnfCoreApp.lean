import ConAgua.Arena.WhnfCoreStep

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
`(whnfCallees_stub p).instList`, so the theorem depends on that stub's `sorry`.

**Handle words of `mk_app`/`mk_app_n_from` results.** `mkAppNFrom_refines` dropped `HW (r.headD 0)`;
`callW_mkApp`/`callW_mkAppNFrom` re-derive it from the store (`internM_hw`: a hit's index is below
the tier's node count, a push's below `2^27`).

**`whnf_app`: not done.** `whnfAppW` (the loop, spliced into `whnfAppL'`, `whnfAppL_eq := rfl`)
and its model `appLoop` are here. The block spec by `vcgen` + `finish` does not close: the
two-result `(st, e3) := call beta_peel(..)` followed by a `CTL` write blows the goal up (the same
loop with a single-result call, or with the call replaced by a load, closes in about a second;
`simp_all` as in `coreApp2_spec` hits the heartbeat limit). The way on is to name the loop body's
pieces (`if v >> 28 == 5 {..}`, the `iota_rec_at` step) as blocks of their own and prove each
with the `simp_all` fallback.
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

/-- **`CoreS` across an interning step**: `ArenaD` comes from the step's own refinement, the
twin's state keeps what else `CoreS` reads (`cpl`), and the memory write is confined to arrays
and `CTL` words outside the core tier, the pins and the environment. -/
theorem CoreS.arena_frame {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a') (hcpl : cpl a' = cpl a)
    (hf : MemFrame A C m m')
    (h128 : ∀ b ∈ A, b < 96 ∨ 128 ≤ b) (hpins : (128 : ArrId) ∉ A)
    (henv : ∀ b ∈ A, b < 132 ∨ 144 ≤ b)
    (hC128 : ∀ x ∈ C, x.toNat < 96 ∨ 128 ≤ x.toNat)
    (hCenv : ∀ x ∈ C, x.toNat < 128 ∨ 136 ≤ x.toNat) :
    CoreS dn m' a' vis fe M eb := by
  simp only [cpl, Prod.mk.injEq] at hcpl
  obtain ⟨hc, hp, hl⟩ := hcpl
  refine ⟨hD, ?_, ?_, hS.env.frame (fun b hb => (henv b hb).elim (fun h => .inl h) (fun h => .inr h))
      (fun x hx => (hCenv x hx).elim (fun h => .inl h) (fun h => .inr h)) hf, ?_, ?_, ?_,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn⟩
  · rw [hc]
    exact CoreRM.frame (A := A) (C := C)
      (fun b hb => (h128 b hb).elim (fun h => .inl h) (fun h => .inr h))
      (fun x hx => (hC128 x hx).elim (fun h => .inl h) (fun h => .inr h)) hf hS.core
  · rw [hp]; exact hS.pins.congr (hf.1 PINS hpins (by decide))
  · intro h l e; rw [hc] at e; have := hS.readL h l e; simp only [EStore.ls] at this ⊢; rw [hl]; exact this
  · intro h l e; rw [hc] at e; have := hS.readLs h l e; rw [hl]; exact this
  · rw [hl]; exact hS.nwf

/-! ## Handle words of the interning functions' results

`mk_app` and `mk_app_n_from` post `decE` of their result only; the loop and the specs below need
the result word itself below `2^32` (`HW`): a hit's index is below the tier's node count, a push's
below `2^27`. -/

theorem hdW_lt (g t i : Word) (hg : g.toNat < 16) (ht : t.toNat ≤ 1) (hi : i.toNat < 2 ^ 27) :
    (hdW g t i).toNat < 2 ^ 32 := by
  simp only [hdW, UInt64.toNat_add, UInt64.toNat_mul]
  have h1 : (0x10000000 : Word).toNat = 268435456 := by simp
  have h2 : (0x8000000 : Word).toNat = 134217728 := by simp
  have e27 : (2:Nat) ^ 27 = 134217728 := by decide
  have e32 : (2:Nat) ^ 32 = 4294967296 := by decide
  have e64 : (2:Nat) ^ 64 = 18446744073709551616 := by decide
  rw [h1, h2, e64]
  rw [e27] at hi; rw [e32]
  rw [Nat.mod_eq_of_lt (by omega : g.toNat * 268435456 < 18446744073709551616),
    Nat.mod_eq_of_lt (by omega : t.toNat * 134217728 < 18446744073709551616)]
  rw [Nat.mod_eq_of_lt (by omega : g.toNat * 268435456 + t.toNat * 134217728 < 18446744073709551616)]
  rw [Nat.mod_eq_of_lt (by omega : g.toNat * 268435456 + t.toNat * 134217728 + i.toNat < 18446744073709551616)]
  omega

section
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] (S : Schema)
  (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)

/-- A hit's index is below the tier's node count. -/
theorem hit_idx_lt (m : Mem) (t : Word) (tb : Tbl α (Idx k) δ) (hT : TierR S R hs m t tb)
    (mt : Word → Bool) (x : Word) (rs : List Word) (hP : ProbeOKG S m t mt x rs)
    (hr : rs ≠ []) (hh : rs.headD 0 ≠ 0) : (rs.tail.headD 0).toNat < 2 ^ 27 := by
  obtain ⟨-, hs2, hs3, hj⟩ := (hP hr).1 hh
  obtain ⟨-, hcap, -, -, -, -, ⟨hsl, -⟩⟩ := hT
  have h1 := hsl _ hj
  rw [hs2] at h1
  have h3 : (rs.tail.headD 0 + 1).toNat ≠ 0 := fun h => hs3 (by rw [hs2]; exact UInt64.toNat_inj.mp (by simpa using h))
  rw [UInt64.toNat_add] at h1 h3
  simp only [UInt64.toNat_one] at h1 h3
  have := (rs.tail.headD 0).toNat_lt
  omega

/-- **An interned handle word is below `2^32`.** -/
theorem internM_hw (hS : S.WF) (m : Mem) (on : Bool) (tbP tbS : Tbl α (Idx k) δ)
    (hR : StoreR S R hs m on tbP tbS) (mt : Word → Word → Bool) (x0 x1 : Word)
    (rs₀ rs₁ : List Word) (hP0 : ProbeOKG S m 0 (mt 0) x0 rs₀) (hP1 : ProbeOKG S m 1 (mt 1) x1 rs₁)
    (pk : Word → Bool) (hpk : ∀ t, pk t = true → PushRoom S m t) (sk : Word) (vs : List Word)
    (w : Word) (m' : Mem) (hI : internM S m sk pk vs rs₀ rs₁ = some (w, m')) :
    w.toNat < 2 ^ 32 := by
  have hg : S.tag.toUInt64.toNat < 16 := by
    rw [UInt32.toNat_toUInt64]; exact hS.tag
  have h0 : (0 : Word).toNat ≤ 1 := by decide
  have h1 : (1 : Word).toNat ≤ 1 := by decide
  have e27 : (2:Nat) ^ 27 = 134217728 := by decide
  obtain ⟨-, -, hT0, hT1⟩ := hR
  simp only [internM] at hI
  split at hI
  · simp at hI
  rename_i hn0
  split at hI
  · rename_i hh
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hI)
    exact hdW_lt _ _ _ hg h0 (hit_idx_lt S R hs m 0 _ hT0 _ _ rs₀ hP0 (fun h => hn0 ⟨hh.1, h⟩) hh.2)
  rename_i hh
  split at hI
  · split at hI
    · simp at hI
    split at hI
    · rename_i hz hhit
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hI)
      exact hdW_lt _ _ _ hg h1 (hit_idx_lt S R hs m 1 _ hT1 _ _ rs₁ hP1 hz hhit)
    split at hI
    · rename_i hpk1
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hI)
      have := (hpk 1 hpk1).1
      exact hdW_lt _ _ _ hg h1 this
    · simp at hI
  · split at hI
    · rename_i hpk0
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hI)
      exact hdW_lt _ _ _ hg h0 (hpk 0 hpk0).1
    · simp at hI

end

theorem ainternW_hw (m : Mem) (a : AState) (hR : AppR m a) (f x : Word) (w : Word) (m' : Mem)
    (hI : ainternW m f x = some (w, m')) : w.toNat < 2 ^ 32 := by
  rw [ainternW_eq] at hI
  exact internM_hw appSch ARecRel ahash appSch_wf m _ _ _ hR (aMt m f x) _ _ _ _
    (probe_homeG appSch m 0 _ _ (aprobeW_arm m f x 0) _)
    (probe_homeG appSch m 1 _ _ (aprobeW_arm m f x 1) _) _ (apushOK_room m) _ _ w m' hI

/-- **`mk_app`'s result is a handle word.** -/
theorem mkAppW_hw (m : Mem) (a : AState) (hA : ArenaD m a) (f x r : Word) (m' : Mem)
    (hI : mkAppW m f x = some (r, m')) : r.toNat < 2 ^ 32 := by
  unfold mkAppW at hI
  split at hI
  · cases hI
  cases hI₁ : ainternW m f x with
  | none => simp [hI₁, mkK] at hI
  | some p =>
  obtain ⟨r₁, m₁⟩ := p
  simp only [hI₁, mkK_some] at hI
  cases hP : derPutW ADER 4 m₁ (cnt2 m 4) r₁ (maxW (derBW m f) (derBW m x)) with
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
    cases hmk : mkAppW m f (spW m (o + i)) with
    | none => simp [hmk] at hL
    | some p =>
      obtain ⟨f₁, m₁⟩ := p
      simp only [hmk] at hL
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
    MemFrame [AREC, ASLOT, ADER] [4, 5] s₀.mem m' ∧ HW (r.headD 0) := by
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
    MemFrame [AREC, ASLOT, ADER] [4, 5] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hok, hD', hres, hfr⟩ := triple_of_callW (Q := fun r s' =>
      LocEq s' s₀ ∧ AM.ok (mkAppNFrom (decE f) xs i.toNat) a₀ ∧
        ArenaD s'.mem (AM.st (mkAppNFrom (decE f) xs i.toNat) a₀) ∧
        AM.res (mkAppNFrom (decE f) xs i.toNat) a₀ = decE (r.headD 0) ∧
        MemFrame [AREC, ASLOT, ADER] [4, 5] s₀.mem s'.mem)
    (mkAppNFrom_refines p hp n s₀ a₀ hD f o k i xs hf hx hik) h
  obtain ⟨s'', hm⟩ := triple_of_callW (mkAppNFromL_spec p hp.derb hp.appf hp.appp hp.appi hp.mkapp
    hp.mknf n s₀ f o k i) h
  exact ⟨hok, hD', hres, hfr, mkAppNFromW_hw _ s₀.mem a₀ f o k i rfl hD hf _ _ hm.2.2⟩

/-- **The `app` interning writes neither the stack nor its top.** -/
theorem StackKept.of_app_frame {m m' : Mem} (hf : MemFrame [AREC, ASLOT, ADER] [4, 5] m m') :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (by simp [AREC, ASLOT, ADER, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  exact ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩

/-- **`CoreS` across an `app` interning step.** -/
theorem CoreS.of_app {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a')
    (hcpl : cpl a' = cpl a) (hf : MemFrame [AREC, ASLOT, ADER] [4, 5] m m') :
    CoreS dn m' a' vis fe M eb :=
  hS.arena_frame hD hcpl hf
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> decide)
    (by simp [AREC, ASLOT, ADER, PINS])
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> decide)
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
    tt := (t >> 27) & 1;
    x := t & 134217727;
    if tt != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[28 + tt] <= x { abort };
    t := LAREC.u64[x * 4 + tt * 2 + 1];
    if len(SPN.u64) <= co + cn { abort };
    SPN.u64[co + cn] := SPN.u64[ao + i];
    cn += 1;
    CTL.u64[136] := co + cn;
    i += 1
  }
}

/-- `betaPeelL`, with its loop spliced from `betaPeelW`. -/
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
      else if rdW (m.arr64 CTL) (28 + tierW t) ≤ idxW t then none
      else if m.len64 SPN ≤ co + cn then none
      else peelLoop p k ((m.set64 SPN (co + cn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
          (co + cn + 1)) (rdW (m.arr64 LAREC) (idxW t * 4 + tierW t * 2 + 1)) ao an (i + 1) co (cn + 1)
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
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih,
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
    (h2 : ¬ rdW (m.arr64 CTL) (28 + tierW t) ≤ idxW t) (h3 : ¬ m.len64 SPN ≤ co + cn) :
    peelFull p n (k + 1) m t ao an i co cn =
      peelFull p n k ((m.set64 SPN (co + cn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
          (co + cn + 1)) (rdW (m.arr64 LAREC) (idxW t * 4 + tierW t * 2 + 1)) ao an (i + 1) co
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
      rw [hSt.2.2 j this, hb j hjc]) (by rw [hSt.2.1, hsz]) h136
  rwa [hr] at this

/-- The state `CoreAfter`-style conclusion of a `beta_peel` run from the loop's memory `m`. -/
def PeelPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb : Word) (m₀ : Mem) (a : AState) (T : AM WhnfStep) (st r : Word) (mF : Mem) : Prop :=
  ∃ x a', T.run a = .ok (x, a') ∧ x = decStep [st, r] ∧ ResW [st, r] ∧
    ∃ M', CoreS dn mF a' vis fe M' eb ∧ KeptAll MM M' eb ∧ StackKept m₀ mF

theorem peelFull_ref (p : Prog) (hp : SpineProg p) (n : Nat) (ao an : Word) (args : Array EIdx)
    (co : Word) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb : Word) (a : AState) (m₀ : Mem) (har₀ : SpineR m₀ ao an args) (hco : co = spTop m₀)
    (hlo : ao.toNat + an.toNat ≤ co.toNat) :
    ∀ (k : Nat) (m : Mem) (t i cn : Word) (acc : Array EIdx),
      CoreS dn m a vis fe MM eb → HW t → SpineR m co cn acc → spTop m = co + cn →
      (∀ j : Word, j < co → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      (136 : Word).toNat < (m.arr64 CTL).size →
      ∀ st r mF, peelFull p n k m t ao an i co cn = some (st, r, mF) →
      (136 : Word).toNat < (mF.arr64 CTL).size →
      PeelPost dn vis fe MM eb m₀ a (betaPeel (decE t) acc args i.toNat) st r mF := by
  intro k
  induction k with
  | zero => intro m t i cn acc _ _ _ _ _ _ _ st r mF hF; rw [peelFull_zero] at hF; cases hF
  | succ k ih =>
    intro m t i cn acc hS ht hacc htop hb hsz h136m st r mF hF h136
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
        have hc2 : ¬ rdW (m.arr64 CTL) (28 + tierW t) ≤ idxW t := fun h => by
          simp [peelFull, peelLoop, hlt, ht5, hc1, h] at hF
        have hc3 : ¬ m.len64 SPN ≤ co + cn := fun h => by
          simp [peelFull, peelLoop, hlt, ht5, hc1, hc2, h] at hF
        rw [peelFull_step _ _ _ _ _ _ _ _ _ _ hlt (fun h => h ht5) hc1 hc2 hc3] at hF
        have hv : viewOK m t 28 := ⟨hc1, UInt64.not_le.mp hc2⟩
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
          (by simp only [size_set64]; exact hsz) (by simp only [size_set64]; exact h136m)
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
        simp only [Option.some.injEq, Prod.mk.injEq] at hF
        obtain ⟨rfl, rfl, rfl⟩ := hF
        have hinst := (whnfCallees_stub p).instList k ⟨m, Locals.init []⟩ a dn vis fe MM eb t co cn 0
          acc hS ht hacc (by rw [hspT]; omega)
        obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hrw⟩ := CoreSpec.of_callW hinst h1
        have h0 : (0 : Word).toNat = 0 := rfl
        rw [h0] at hok hres hS'
        have hx : SpineR m₁ ao an args :=
          har₀.keepT co (hSt'.2.1.trans hsz)
            (fun j hj => (hSt'.2.2 j (by
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
        · exact peel_restore hco hb hsz hSt2 htop hcn64 h136'
    · rw [peelFull_exit _ _ _ _ _ _ _ _ _ _ hlt] at hF
      unfold peelTail at hF
      cases h1 : callW p n "inst_list" [t, co, cn, 0] m with
      | none => rw [h1] at hF; simp at hF
      | some q =>
      obtain ⟨r₁, m₃⟩ := q
      rw [h1] at hF
      simp only [Option.some.injEq, Prod.mk.injEq] at hF
      obtain ⟨rfl, rfl, rfl⟩ := hF
      have hinst := (whnfCallees_stub p).instList n ⟨m, Locals.init []⟩ a dn vis fe MM eb t co cn 0
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
      · exact peel_restore hco hb hsz hSt' htop hcn64 h136'


/-- **`beta_peel` refines `betaPeel t #[a] args i`.** -/
@[refines ConRon.Arena.betaPeel]
theorem betaPeel_refines (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St) (a₀ : AState)
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
  obtain ⟨x, a', hrun', hx, hrw, M', hS', hK, hSt⟩ := peelFull_ref p hp.spine n ao an args co dn vis
    fe MM eb a₀ s.mem har hco (by rw [hco]; exact hlo) (n + 1) _ t i 1 #[decE a] hS1 ht hacc htop1 hb1
    (by simp only [size_set64]) (by simp only [size_set64]; exact h136i) _ _ _ hW h136
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hok, ?_, ?_, ?_⟩
  · rw [hst]; exact ⟨M', hS', hK, hSt⟩
  · rw [hres, hx]; simp [decStep]
  · exact hrw


/-! ## `whnf_app`: the loop as named blocks

The loop body is the λ arm (`whnfAppLamW`: `beta_peel` and the return) and the rest
(`whnfAppRestW`: the push, then the ι step `whnfAppIotaW`, then the next round); a block spliced
into the middle of a sequence must be one statement, so the push is not a block of its own. The loop (`whnfAppW`) splices them; `whnfAppL'` splices the loop. All are
`rfl`-equal to `whnfAppL` of `WhnfCore.lean`. -/

/-- The λ-head arm of the loop body. -/
def whnfAppLamW : Stmt := lblk (mode, vis, d, v, hd, vo, vn, same, ao, an, i, top, a, node, ap, st, e2, e3, t, x) {
  if v >> 28 == 5 {
    t := (v >> 27) & 1;
    x := v & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[28 + t] <= x { abort };
    (st, e3) := call beta_peel(LAREC.u64[x * 4 + t * 2 + 1], a, ao, an, i + 1);
    CTL.u64[136] := top;
    return (st, e3)
  }
}

/-- The ι step at a constant head. -/
def whnfAppIotaW : Stmt := lblk (mode, vis, d, v, hd, vo, vn, same, ao, an, i, top, a, node, ap, st, e2, e3, t, x) {
  if hd >> 28 == 3 {
    (st, e2) := call iota_rec_at(mode, vis, d, hd, vo, vn);
    if st != 0 {
      e3 := call mk_app_n_from(e2, ao, an, i + 1);
      CTL.u64[136] := top;
      return (1, e3)
    }
  }
}

/-- The rest of the loop body after the λ arm: the push, the ι step, the next round. -/
def whnfAppRestW : Stmt := lblk (mode, vis, d, v, hd, vo, vn, same, ao, an, i, top, a, node, ap, st, e2, e3, t, x) {
  if same != 0 { ap := node } else { ap := call mk_app(v, a) };
  same := u64(ap == node);
  if len(SPN.u64) <= vo + vn { abort };
  SPN.u64[vo + vn] := a;
  vn += 1;
  CTL.u64[136] := vo + vn;
  ⟪whnfAppIotaW⟫;
  v := ap;
  i += 1
}

/-- The loop body of `whnfAppL` (WhnfCore.lean), named for its spec. -/
def whnfAppBodyW : Stmt := lblk (mode, vis, d, v, hd, vo, vn, same, ao, an, i, top, a, node, ap, st, e2, e3, t, x) {
  a := SPN.u64[ao + i];
  node := SPN.u64[ao + an + i];
  ⟪whnfAppLamW⟫;
  ⟪whnfAppRestW⟫
}

/-- The loop of `whnfAppL` (WhnfCore.lean), named for its spec. -/
def whnfAppW : Stmt := lblk (mode, vis, d, v, hd, vo, vn, same, ao, an, i, top, a, node, ap, st, e2, e3, t, x) {
  while i < an {
    ⟪whnfAppBodyW⟫
  }
}

/-- `whnfAppL`, with its loop spliced from `whnfAppW`. -/
def whnfAppL' : FunDecl :=
    lfn (mode, vis, d, v, hd, vo, vn, same, ao, an, i) locals (top, a, node, ap, st, e2, e3, t, x) {
  top := CTL.u64[136];
  ⟪whnfAppW⟫;
  CTL.u64[136] := top;
  return (0, v)
}

theorem whnfAppL_eq : whnfAppL = whnfAppL' := rfl



/-! ## The models of the arms -/

/-- How an arm ends: by a `return` (`st`, `r`, the memory), or by falling through with the memory. -/
inductive StepOut
  | ret (st r : Word) (m : Mem)
  | cont (m : Mem)

/-- The model of the λ arm at callee fuel `k`. -/
def lamW (p : Prog) (k : Nat) (m : Mem) (v a ao an i top : Word) : Option StepOut :=
  if v >>> 28 = 5 then
    if tierW v ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (28 + tierW v) ≤ idxW v then none
    else
      match callW p k "beta_peel" [rdW (m.arr64 LAREC) (idxW v * 4 + tierW v * 2 + 1), a, ao, an,
          i + 1] m with
      | none => none
      | some (r, m₁) => some (.ret (r.headD 0) (r.tail.headD 0) (m₁.set64 CTL 136 top))
  else some (.cont m)

theorem whnfAppLamW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p (n + 1) whnfAppLamW
    ⦃fun r s' => match lamW p n s₀.mem (s₀.loc 3) (s₀.loc 12) (s₀.loc 8) (s₀.loc 9) (s₀.loc 10)
        (s₀.loc 11) with
      | none => False
      | some (.ret st rv m) => r = .ret [st, rv] ∧ s'.mem = m ∧
          (136 : Word).toNat < (s'.mem.arr64 CTL).size
      | some (.cont _) => r = .normal ∧ s'.mem = s₀.mem ∧
          s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = s₀.loc 7 ∧ s'.loc 8 = s₀.loc 8 ∧ s'.loc 9 = s₀.loc 9 ∧ s'.loc 10 = s₀.loc 10 ∧ s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧ s'.loc 14 = s₀.loc 14 ∧ s'.loc 15 = s₀.loc 15 ∧ s'.loc 16 = s₀.loc 16 ∧ s'.loc 17 = s₀.loc 17 ∧ s'.loc 18 = s₀.loc 18 ∧ s'.loc 19 = s₀.loc 19; ⊤⦄ := by
  rw [exec]; unfold whnfAppLamW L.Notation.blk
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "beta_peel"] <;>
    finish [lamW, tierW, idxW, St.setLoc_loc, St.setLoc_mem]

/-- The model of the ι arm at callee fuel `k`. -/
def iotaW (p : Prog) (k : Nat) (m : Mem) (mode vis d hd vo vn ao an i top : Word) :
    Option StepOut :=
  if hd >>> 28 = 3 then
    match callW p k "iota_rec_at" [mode, vis, d, hd, vo, vn] m with
    | none => none
    | some (r, m₃) =>
      if r.headD 0 ≠ 0 then
        match callW p k "mk_app_n_from" [r.tail.headD 0, ao, an, i + 1] m₃ with
        | none => none
        | some (r', m₄) => some (.ret 1 (r'.headD 0) (m₄.set64 CTL 136 top))
      else some (.cont m₃)
  else some (.cont m)

theorem whnfAppIotaW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p (n + 1) whnfAppIotaW
    ⦃fun r s' => match iotaW p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 4) (s₀.loc 5)
        (s₀.loc 6) (s₀.loc 8) (s₀.loc 9) (s₀.loc 10) (s₀.loc 11) with
      | none => False
      | some (.ret st rv m) => r = .ret [st, rv] ∧ s'.mem = m ∧
          (136 : Word).toNat < (s'.mem.arr64 CTL).size
      | some (.cont m) => r = .normal ∧ s'.mem = m ∧
          ∀ y, y ≠ 15 → y ≠ 16 → s'.loc y = s₀.loc y; ⊤⦄ := by
  rw [exec]; unfold whnfAppIotaW L.Notation.blk
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "iota_rec_at", callW_spec p n "mk_app_n_from"] <;>
    finish [iotaW, St.setLoc_loc, St.setLoc_mem]

/-- The next spine node of the walk: the saved node (`same`), else `mk_app(v, a)`. -/
def apW (p : Prog) (k : Nat) (m : Mem) (v same a node : Word) : Option (Word × Mem) :=
  if same ≠ 0 then some (node, m)
  else match callW p k "mk_app" [v, a] m with
    | none => none
    | some (r, m₁) => some (r.headD 0, m₁)

/-- How the rest of the loop body ends: by a `return`, or into the next round with the memory and
the next `v`, `vn`, `same`. -/
inductive RestOut
  | ret (st r : Word) (m : Mem)
  | cont (m : Mem) (v vn same : Word)

/-- The model of the rest of the loop body at callee fuel `k`: the push (its `CTL` write checked
in bounds, as `st64` does), then the ι arm. -/
def appRestW (p : Prog) (k : Nat) (m : Mem) (mode vis d v hd vo vn same ao an i top a node : Word) :
    Option RestOut :=
  match apW p k m v same a node with
  | none => none
  | some (ap, m₁) =>
    if m₁.len64 SPN ≤ vo + vn then none
    else if (136 : Word).toNat < (m₁.arr64 CTL).size then
      match iotaW p k ((m₁.set64 SPN (vo + vn) a).set64 CTL 136 (vo + vn + 1)) mode vis d hd vo
          (vn + 1) ao an i top with
      | none => none
      | some (.ret st r m') => some (.ret st r m')
      | some (.cont m') => some (.cont m' ap (vn + 1) (Cmp.evalW .eq ap node))
    else none

theorem whnfAppRestW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p (n + 1) whnfAppRestW
    ⦃fun r s' => match appRestW p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)
        (s₀.loc 5) (s₀.loc 6) (s₀.loc 7) (s₀.loc 8) (s₀.loc 9) (s₀.loc 10) (s₀.loc 11)
        (s₀.loc 12) (s₀.loc 13) with
      | none => False
      | some (.ret st rv m) => r = .ret [st, rv] ∧ s'.mem = m ∧
          (136 : Word).toNat < (s'.mem.arr64 CTL).size
      | some (.cont m v vn same) => r = .normal ∧ s'.mem = m ∧ s'.loc 3 = v ∧ s'.loc 6 = vn ∧
          s'.loc 7 = same ∧ s'.loc 10 = s₀.loc 10 + 1 ∧ s'.loc 0 = s₀.loc 0 ∧
          s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 4 = s₀.loc 4 ∧
          s'.loc 5 = s₀.loc 5 ∧ s'.loc 8 = s₀.loc 8 ∧ s'.loc 9 = s₀.loc 9 ∧
          s'.loc 11 = s₀.loc 11; ⊤⦄ := by
  rw [exec]; unfold whnfAppRestW L.Notation.blk
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "mk_app", fun s => Triple.step_exec (whnfAppIotaW_spec p n s)] <;>
    finish [appRestW, apW]

theorem getElem_toNat_rdW (a : Array Word) (x : Word) (h : x.toNat < a.size) :
    a[x.toNat]'h = rdW a x := by simp [rdW, h]

theorem BinOp.add_eval' (a b : Word) : BinOp.add.eval a b = a + b := rfl

/-- The model of the loop body at callee fuel `k`. -/
def bodyW (p : Prog) (k : Nat) (m : Mem) (mode vis d v hd vo vn same ao an i top : Word) :
    Option RestOut :=
  match lamW p k m v (rdW (m.arr64 SPN) (ao + i)) ao an i top with
  | none => none
  | some (.ret st r m') => some (.ret st r m')
  | some (.cont _) =>
    appRestW p k m mode vis d v hd vo vn same ao an i top (rdW (m.arr64 SPN) (ao + i))
      (rdW (m.arr64 SPN) (ao + an + i))

theorem whnfAppBodyW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p (n + 1) whnfAppBodyW
    ⦃fun r s' => match bodyW p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)
        (s₀.loc 5) (s₀.loc 6) (s₀.loc 7) (s₀.loc 8) (s₀.loc 9) (s₀.loc 10) (s₀.loc 11) with
      | none => False
      | some (.ret st rv m) => r = .ret [st, rv] ∧ s'.mem = m ∧
          (136 : Word).toNat < (s'.mem.arr64 CTL).size
      | some (.cont m v vn same) => r = .normal ∧ s'.mem = m ∧ s'.loc 3 = v ∧ s'.loc 6 = vn ∧
          s'.loc 7 = same ∧ s'.loc 10 = s₀.loc 10 + 1 ∧ s'.loc 0 = s₀.loc 0 ∧
          s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 4 = s₀.loc 4 ∧
          s'.loc 5 = s₀.loc 5 ∧ s'.loc 8 = s₀.loc 8 ∧ s'.loc 9 = s₀.loc 9 ∧
          s'.loc 11 = s₀.loc 11; ⊤⦄ := by
  rw [exec]; unfold whnfAppBodyW L.Notation.blk
  vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    fun s => Triple.step_exec (whnfAppLamW_spec p n s),
    fun s => Triple.step_exec (whnfAppRestW_spec p n s)] <;>
  simp_all [bodyW, St.setLoc_loc, St.setLoc_mem, getElem_toNat_rdW, BinOp.add_eval', SPN,
    -UInt64.toNat_add] <;>
  (split at * <;> first | grind | simp_all)

/-- How a loop ends: by a `return` (`st`, `r`, the memory) or by its condition failing (`v`, the
memory). -/
inductive AppOut
  | ret (st r : Word) (m : Mem)
  | exit (v : Word) (m : Mem)

/-- **The model of the `whnf_app` loop** at L fuel `k`. -/
def appLoop (p : Prog) (mode vis d hd vo ao an top : Word) : Nat → Mem → Word → Word → Word →
    Word → Option AppOut
  | 0, _, _, _, _, _ => none
  | k + 1, m, v, vn, same, i =>
    if i < an then
      match bodyW p k m mode vis d v hd vo vn same ao an i top with
      | none => none
      | some (.ret st r m') => some (.ret st r m')
      | some (.cont m' v' vn' same') =>
        appLoop p mode vis d hd vo ao an top k m' v' vn' same' (i + 1)
    else some (.exit v m)

/-- The end of the `whnf_app` loop run, as the model's. -/
def AppOut.ofSig (r : Sig) (s' : St) : AppOut :=
  match r with
  | .ret v => .ret (v.headD 0) (v.tail.headD 0) s'.mem
  | _ => .exit (s'.loc 3) s'.mem

theorem whnfAppW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n whnfAppW
    ⦃fun r s' => (r = .normal ∧ s'.loc 11 = s₀.loc 11 ∧
        appLoop p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 8) (s₀.loc 9)
          (s₀.loc 11) n s₀.mem (s₀.loc 3) (s₀.loc 6) (s₀.loc 7) (s₀.loc 10) =
          some (.exit (s'.loc 3) s'.mem)) ∨
      (∃ st rv, r = .ret [st, rv] ∧ (136 : Word).toNat < (s'.mem.arr64 CTL).size ∧
        appLoop p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 8) (s₀.loc 9)
          (s₀.loc 11) n s₀.mem (s₀.loc 3) (s₀.loc 6) (s₀.loc 7) (s₀.loc 10) =
          some (.ret st rv s'.mem)); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := whnfAppW) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih,
        fun s => Triple.step_exec (whnfAppBodyW_spec p n s)] <;>
      finish [appLoop, AppOut.ofSig]

theorem getElem_ctl136 (a : Array Word) (h : 136 < a.size) : a[136]'h = rdW a 136 := by
  simp [rdW, h]

/-- **The model of `whnf_app`** at L fuel `n + 1`. -/
def appFnW (p : Prog) (n : Nat) (m : Mem) (mode vis d v hd vo vn same ao an i : Word) :
    Option (Word × Word × Mem) :=
  match appLoop p mode vis d hd vo ao an (rdW (m.arr64 CTL) 136) (n + 1) m v vn same i with
  | none => none
  | some (.ret st r m') => some (st, r, m')
  | some (.exit v' m') => some (0, v', m'.set64 CTL 136 (rdW (m.arr64 CTL) 136))

theorem whnfApp_spec (p : Prog) (hp : p.lookup "whnf_app" = some whnfAppL) (n : Nat) (s₀ : St)
    (mode vis d v hd vo vn same ao an i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "whnf_app" [mode, vis, d, v, hd, vo, vn, same, ao, an, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      appFnW p n s₀.mem mode vis d v hd vo vn same ao an i =
        some (r.headD 0, r.tail.headD 0, s'.mem) ∧
      (136 : Word).toNat < (s₀.mem.arr64 CTL).size ∧
      (136 : Word).toNat < (s'.mem.arr64 CTL).size; ⊤⦄ := by
  rw [invoke_eq _ hp, whnfAppL_eq]
  simp only [callFn, whnfAppL']
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    fun s => Triple.step_exec (whnfAppW_spec p (n + 1) s)] <;>
  simp_all [appFnW, AppOut.ofSig, LocEq, St.setLoc_loc, St.setLoc_mem, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr, getElem_ctl136, CTL, size_set64] <;>
  first | assumption | grind

end L.Arena
