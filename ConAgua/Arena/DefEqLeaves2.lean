import ConAgua.Arena.DefEqLeaves

/-!
# Refinements of `DefEq.lean`'s small leaves, continued

`er_slice_eq` (a loop, as `limbs_eq`'s in `Store.lean`), `nat_pred`, `lit_eq`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## `er_slice_eq` -/

theorem erSliceEqLoop_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n erSliceEqLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [1] = [if eqW (s₀.mem.arr64 EREC) (s₀.loc 0) (s₀.loc 2) (s₀.loc 1) (s₀.loc 4)
        then 1 else 0]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := erSliceEqLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, ih] <;> finish

theorem erSliceEqLoop_step_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) erSliceEqLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [1] = [if eqW (s₀.mem.arr64 EREC) (s₀.loc 0) (s₀.loc 2) (s₀.loc 1) (s₀.loc 4)
        then 1 else 0]; ⊤⦄ :=
  Triple.step_exec (erSliceEqLoop_spec p (n + 1) s₀)

theorem erSliceEq_spec (p : Prog) (hp : p.lookup "er_slice_eq" = some erSliceEqL) (n : Nat)
    (s₀ : St) (o1 n1 o2 n2 : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "er_slice_eq" [o1, n1, o2, n2]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      r = [if n1 = n2 ∧ eqW (s₀.mem.arr64 EREC) o1 o2 n1 0 = true then 1 else 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erSliceEqL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, erSliceEqLoop_step_spec p n] <;> finish

theorem mapM_get {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {l : List β}, xs.mapM f = some l →
      l.length = xs.length ∧ ∀ k (hk : k < xs.length), f xs[k] = l[k]?
  | [], l, h => by simp at h; subst h; simp
  | x :: xs, l, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    obtain ⟨hl, hg⟩ := mapM_get hys
    refine ⟨by simp [hl], fun k hk => ?_⟩
    cases k with
    | zero => simpa using hy
    | succ k => simpa using hg k (by simpa using hk)

/-- A decoded handle slice: its length, and each element a word below `2^32`. -/
theorem hslice?_get {k : IdxKind} {a : Array Word} {o n : Nat} {l : List (Idx k)}
    (h : hslice? a o n = some l) :
    l.length = n ∧ ∀ j, j < n → ∃ w, a[o + j]? = some w ∧ w.toNat < 2 ^ 32 ∧ l[j]? = some (decI w) := by
  obtain ⟨hl, hg⟩ := mapM_get h
  simp only [List.length_range] at hl
  refine ⟨hl, fun j hj => ?_⟩
  have := hg j (by simpa using hj)
  simp only [List.getElem_range] at this
  cases e : a[o + j]? with
  | none => simp [hd?, e] at this; omega
  | some w =>
    simp only [hd?, e, Option.bind_eq_bind, Option.bind_some] at this
    by_cases hw : w.toNat < 2 ^ 32
    · simp only [hw, ↓reduceIte] at this; exact ⟨w, rfl, hw, this.symm⟩
    · simp only [hw, ↓reduceIte] at this; have := List.getElem?_eq_none_iff.mp this.symm; omega

/-- **`er_slice_eq` decides the equality of two decoded handle slices of the record pool** (the
twin's `cvc.levelParams = cvT.levelParams` in `structEtaCertWith`). -/
@[refines_part ConRon.Arena.structEtaCertWith "level-parameter lists equal"]
theorem erSliceEq_refines (p : Prog) (hp : p.lookup "er_slice_eq" = some erSliceEqL) (n : Nat)
    (s₀ : St) (o1 n1 o2 n2 : Word) {k : IdxKind} (l1 l2 : List (Idx k))
    (hsz : (s₀.mem.arr64 EREC).size < 2 ^ 63)
    (h1 : hslice? (erecP s₀.mem) o1.toNat n1.toNat = some l1)
    (h2 : hslice? (erecP s₀.mem) o2.toNat n2.toNat = some l2) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "er_slice_eq" [o1, n1, o2, n2]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ decBool r = decide (l1 = l2) ∧ ResH r; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hm, hloc, hr⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (erSliceEq_spec p hp n s₀ o1 n1 o2 n2)
  subst hs0
  refine ⟨hm, hloc, ?_, by rw [hr]; unfold ResH; split <;> first | exact hw0 | exact hw1⟩
  rw [hr, decBool]
  simp only [List.headD_cons]
  rw [ite_bne]
  obtain ⟨hl1, hg1⟩ := hslice?_get h1
  obtain ⟨hl2, hg2⟩ := hslice?_get h2
  have hext := erecP_ext s.mem
  have hb : ∀ {o c : Nat} {l : List (Idx k)}, hslice? (erecP s.mem) o c = some l → 0 < c →
      o + c < 2 ^ 64 := by
    intro o c l h hc
    obtain ⟨-, hg⟩ := hslice?_get h
    obtain ⟨w, hw, -, -⟩ := hg (c - 1) (by omega)
    have := hext _ _ hw
    have : o + (c - 1) < (s.mem.arr64 EREC).size := by
      rcases Nat.lt_or_ge (o + (c - 1)) (s.mem.arr64 EREC).size with h' | h'
      · exact h'
      · simp [Array.getElem?_eq_none h'] at this
    omega
  congr 1
  apply propext
  constructor
  · rintro ⟨rfl, he⟩
    rcases Nat.eq_zero_or_pos n1.toNat with hz | hz
    · apply List.ext_getElem?; intro j
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    have hb1 := hb h1 hz
    have hb2 := hb h2 hz
    rw [eqW_iff _ _ _ _ _ hb1 hb2] at he
    apply List.ext_getElem?; intro j
    by_cases hj : j < n1.toNat
    · obtain ⟨w1, hw1, -, he1⟩ := hg1 j hj
      obtain ⟨w2, hw2, -, he2⟩ := hg2 j hj
      have := he j (by simp) hj
      rw [hext _ _ hw1, hext _ _ hw2] at this
      simp only [Option.getD_some] at this
      rw [he1, he2, this]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · intro heq
    subst heq
    have hn : n1 = n2 := UInt64.toNat_inj.mp (hl1.symm.trans hl2)
    subst hn
    refine ⟨rfl, ?_⟩
    rcases Nat.eq_zero_or_pos n1.toNat with hz | hz
    · exact eqW_end _ _ _ _ _ (by simp [UInt64.lt_iff_toNat_lt, hz])
    rw [eqW_iff _ _ _ _ _ (hb h1 hz) (hb h2 hz)]
    intro j _ hj
    obtain ⟨w1, hw1, hl1', he1⟩ := hg1 j hj
    obtain ⟨w2, hw2, hl2', he2⟩ := hg2 j hj
    rw [he1] at he2
    have := decI_inj hl1' hl2' (Option.some.inj he2)
    rw [hext _ _ hw1, hext _ _ hw2, this]

/-! ## `CoreS` across the `Nat` literal arms (`nat_pred_lit`)

`NatArms.lean`'s arm refinements are generic in the relation `R` they keep: it must give the pool
(`PoolOK`), survive appending to the pool (`Grows`) and an `intern_lit` (`InternSpec`). `CoreS`
(with the stack kept from a fixed memory) is such a relation: the pool append and the `lit` tables
lie outside the core tier, the pins, the environment and the stack, and the interning keeps the
caches, the pins and the level store (`cpl`). -/

/-- What `CoreS` reads of the twin's state, besides `ArenaD` (a copy of `WhnfCoreApp.lean`'s `cpl`,
which does not build at this commit). -/
def cplL (a : AState) : Caches × Pins × LsStore := (a.caches, a.pins, a.store.lss)

theorem keeps_cplL_internNodeE (v : ENodeView) : Keeps cplL (internNodeE v) := by
  unfold Keeps; intro a r a' h
  simp only [internNodeE, StateT.run_bind, StateT.run_get, pure_bind] at h
  repeat' split at h
  all_goals simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
    ConRon.Arena.fail, throwThe, MonadExceptOf.throw] at h
  all_goals first
    | (cases h; rfl)
    | (cases h; simp only [cplL, EStore.lss_intern])
    | (simp [throwThe, Functor.map, Except.map] at h)

/-- **`CoreS` across an interning step** (`WhnfCoreApp.lean`'s `CoreS.arena_frame`, copied). -/
theorem CoreS.arenaFrame {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a') (hcpl : cplL a' = cplL a)
    (hf : MemFrame A C m m')
    (h128 : ∀ b ∈ A, b < 96 ∨ 128 ≤ b) (hpins : (128 : ArrId) ∉ A)
    (henv : ∀ b ∈ A, b < 132 ∨ 144 ≤ b)
    (hC128 : ∀ x ∈ C, x.toNat < 96 ∨ 128 ≤ x.toNat)
    (hCenv : ∀ x ∈ C, x.toNat < 128 ∨ 136 ≤ x.toNat) :
    CoreS dn m' a' vis fe M eb := by
  simp only [cplL, Prod.mk.injEq] at hcpl
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

/-- `CoreS`, with the stack as it was in `m₀`. -/
def CoreK (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word)
    (m₀ : Mem) (m : Mem) (a : AState) : Prop :=
  CoreS dn m a vis fe M eb ∧ StackKept m₀ m

theorem StackKept.of_frame {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    (hA : SPN ∉ A) (hC : (136 : Word) ∉ C) : StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN hA (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 hC
  exact ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩

theorem CoreK.grow {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {m₀ m m' : Mem} {a : AState} (h : CoreK dn vis fe M eb m₀ m a) (hg : Grows m m') :
    CoreK dn vis fe M eb m₀ m' a := by
  have hf := grows_frame m m' hg
  refine ⟨h.1.arenaFrame (ArenaD.grow m m' hg a h.1.arena) rfl hf (by simp [POOL, REC, SLOT, PINS, SPN]) (by simp [POOL, REC, SLOT, PINS, SPN])
    (by simp [POOL, REC, SLOT, PINS, SPN]) (by simp [POOL, REC, SLOT, PINS, SPN]) (by simp [POOL, REC, SLOT, PINS, SPN]),
    h.2.trans (StackKept.of_frame hf (by simp [POOL, REC, SLOT, PINS, SPN]) (by simp [POOL, REC, SLOT, PINS, SPN]))⟩

/-- **`intern_lit` keeps `CoreK`.** -/
theorem internLit_core (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match" = some litMatch)
    (hpf : p.lookup "lit_find" = some litFind) (hpp : p.lookup "lit_push" = some litPush)
    (hp : p.lookup "intern_lit" = some internLit) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb : Word) (m₀ : Mem) :
    InternSpec p (CoreK dn vis fe M eb m₀) := by
  intro a₀ n s₀ o l hK hq hn
  have ⟨_, _, hps, htop⟩ := hK.1.arena.1.lit.1
  have hspec := internLit_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply L.M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  obtain ⟨hok, hD, hres⟩ := internLit_D s.mem a₀ hK.1.arena o l _ hq hn _ hI
  have hI₂ := hI; rw [internW_eq] at hI₂
  have hfr := internM_frame _ litS_wf _ _ _ _ _ _ _ _ hI₂
  simp only [litSch] at hfr
  have hcpl : cplL (AM.st (internE (.lit (.natVal (pv (s.mem.arr64 POOL) o.toNat l.toNat)))) a₀) =
      cplL a₀ := by
    have := AM.run_of_ok _ _ hok
    exact (keeps_cplL_internNodeE _).run (by simpa only [internE] using this)
  refine ⟨hloc, hok, ⟨hK.1.arenaFrame hD hcpl hfr (by simp [POOL, REC, SLOT, PINS, SPN]) (by simp [POOL, REC, SLOT, PINS, SPN]) (by simp [POOL, REC, SLOT, PINS, SPN])
    (by simp [POOL, REC, SLOT, PINS, SPN]) (by simp [POOL, REC, SLOT, PINS, SPN]), hK.2.trans (StackKept.of_frame hfr (by simp [POOL, REC, SLOT, PINS, SPN])
    (by simp [POOL, REC, SLOT, PINS, SPN]))⟩, hres⟩

end L.Arena
