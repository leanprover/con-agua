import ConAgua.Arena.DefEqLeaves
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.WhnfCoreProj

/-!
# Refinements of `DefEq.lean`'s small leaves, continued

`er_slice_eq` (a loop, as `limbs_eq`'s in `Store.lean`), `nat_pred`, `lit_eq`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

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


theorem erSliceEq_spec (p : Prog) (hp : p.lookup "er_slice_eq" = some erSliceEqL) (n : Nat)
    (s₀ : St) (o1 n1 o2 n2 : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "er_slice_eq" [o1, n1, o2, n2]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      r = [if n1 = n2 ∧ eqW (s₀.mem.arr64 EREC) o1 o2 n1 0 = true then 1 else 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erSliceEqL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, fun s₀ => Triple.step_exec (erSliceEqLoop_spec p (n + 1) s₀)] <;> finish

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
    (henv : ∀ b ∈ A, b < 129 ∨ (144 ≤ b ∧ (b < 385 ∨ 388 ≤ b)))
    (hC128 : ∀ x ∈ C, x.toNat < 96 ∨ 128 ≤ x.toNat)
    (hCenv : ∀ x ∈ C, x.toNat < 128 ∨ 136 ≤ x.toNat)
    (hmA : (50 : ArrId) ∉ A ∧ (49 : ArrId) ∉ A := by decide) (hmC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C := by decide)
    (hmWA : (151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A := by decide)
    (hmWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C := by decide)
    (hmLA : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A := by decide)
    (hmLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C := by decide)
    (hscA : SOREC ∉ A ∧ CREC ∉ A ∧ SOREC + 256 ∉ A ∧ CREC + 256 ∉ A := by decide)
    (hscC : (1 : Word) ∉ C ∧ (16 : Word) ∉ C ∧ (17 : Word) ∉ C ∧ (18 : Word) ∉ C ∧ (19 : Word) ∉ C :=
      by decide) (hmode : ModeOK m') :
    CoreS dn m' a' vis fe M eb := by
  simp only [cplL, Prod.mk.injEq] at hcpl
  obtain ⟨hc, hp, hl⟩ := hcpl
  refine ⟨hD, ?_, ?_, hS.env.frame (fun b hb => (henv b hb).elim (fun h => .inl h) (fun h => .inr h.1))
      (fun x hx => (hCenv x hx).elim (fun h => .inl h) (fun h => .inr h)) hf
      (fun b hb => by have := henv b hb; simp only [ArrId] at this ⊢; omega), ?_, ?_, ?_,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn, hS.memos.frame hf hmA hmC hmWA hmWC hmLA hmLC,
      hf.2.2.1 145 ▸ hS.bstk,
      hS.den.of_arena hS.arena.1 hD.1 hc hp hl hf hscA hscC, hmode⟩
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

theorem CoreK.grow {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {m₀ m m' : Mem} {a : AState} (h : CoreK dn vis fe M eb m₀ m a) (hg : Grows m m') :
    CoreK dn vis fe M eb m₀ m' a := by
  have hf := grows_frame m m' hg
  refine ⟨h.1.arenaFrame (ArenaD.grow m m' hg a h.1.arena) rfl hf (by simp [POOL, POOL1]) (by simp [POOL, POOL1])
    (by simp [POOL, POOL1]) (by simp) (by simp)
    (hmode := h.1.mode.grows hg),
    h.2.trans (StackKept.of_grows hg)⟩

/-- An interned `lit` handle word is below `2^32`: `WhnfDeltaRefine3.lean`'s `internW_hw`, which
this file does not import (it would pull in the whnf walks); `natPredW_of` discharges it. -/
def LitInternHW : Prop :=
  ∀ (m : Mem) (a : AState) (o l w : Word) (m' : Mem), LitR m a → internW m o l = some (w, m') → HW w

/-- `InternSpec` with the handle word below `2^32`. -/
def InternSpecW (p : Prog) (R : Mem → AState → Prop) : Prop :=
  ∀ (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word), R s₀.mem a₀ →
    SliceOK s₀.mem o l → Norm (vpool s₀.mem) o.toNat l.toNat →
    (s₀.mem.flag = 0 → o.toNat < 2 ^ 40) →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ ∧
      R s'.mem (AM.st (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ =
        decE (r.headD 0) ∧ HW (r.headD 0); ⊤⦄

/-- **`intern_lit` keeps `CoreK`**, with a handle word result. -/
theorem internLit_core (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match" = some litMatch)
    (hpf : p.lookup "lit_find" = some litFind) (hpp : p.lookup "lit_push" = some litPush)
    (hp : p.lookup "intern_lit" = some internLit) (hlw : LitInternHW)
    (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb : Word) (m₀ : Mem) :
    InternSpecW p (CoreK dn vis fe M eb m₀) := by
  intro a₀ n s₀ o l hK hq hn hq0
  have ⟨_, _, hps, htop⟩ := hK.1.arena.1.lit.1
  have hspec := internLit_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply L.M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  obtain ⟨hok, hD, hres⟩ := internLit_D s.mem a₀ hK.1.arena o l _ hq hn hq0 _ hI
  have hI₂ := hI
  have hfr := consInternM_frame litCS_wf hI₂
  simp only [litCS, litCSk] at hfr
  have hcpl : cplL (AM.st (internE (.lit (.natVal (pv (vpool s.mem) o.toNat l.toNat)))) a₀) =
      cplL a₀ := by
    have := AM.run_of_ok _ _ hok
    exact (keeps_cplL_internNodeE _).run (by simpa only [internE] using this)
  refine ⟨hloc, hok, ⟨hK.1.arenaFrame hD hcpl hfr (by simp [ConsSch.wset, REC, SLOT]) (by simp [ConsSch.wset, REC, SLOT]) (by simp [ConsSch.wset, REC, SLOT])
    (by simp) (by simp)
    (hmode := hK.1.mode.frame hfr (by simp) (by simp)), hK.2.trans (StackKept.of_frame hfr)⟩, hres, hlw s.mem a₀ o l _ _ hK.1.arena.1.lit hI⟩

/-! ## `nat_pred` -/

/-- The lookups `nat_pred` needs beyond the leaves'. -/
structure NatPredProg (p : Prog) : Prop where
  leaf : DefEqLeafProg p
  np : p.lookup "nat_pred" = some natPredL
  npl : p.lookup "nat_pred_lit" = some natPredLit
  limb : p.lookup "nat_limb" = some natLimb
  sbb : p.lookup "sub_borrow" = some subBorrow
  trim : p.lookup "nat_trim" = some natTrim
  sub : p.lookup "nat_sub" = some natSub
  lhash : p.lookup "lit_hash" = some litHash
  leq : p.lookup "limbs_eq" = some limbsEq
  lmatch : p.lookup "lit_match" = some litMatch
  lfind : p.lookup "lit_find" = some litFind
  lpush : p.lookup "lit_push" = some litPush
  lintern : p.lookup "intern_lit" = some internLit

section predhw
variable (p : Prog) (R : Mem → AState → Prop)
  (hpool : ∀ m a, R m a → PoolOK m) (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
  (hI : InternSpecW p R)
  (hpl : p.lookup "nat_limb" = some natLimb) (hps : p.lookup "sub_borrow" = some subBorrow)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpn : p.lookup "nat_sub" = some natSub)

include hpool hgrow hI hpl hps hpt hpn in
/-- `natPredLit_refines` (`NatArms.lean`) with a handle word result. -/
theorem natPredLit_refines_hw (hg : p.lookup "nat_pred_lit" = some natPredLit) (n : Nat) (s₀ : St)
    (a₀ : AState) (hR : R s₀.mem a₀) (oa la : Word) (ha : SliceOK s₀.mem oa la)
    (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_pred_lit" [oa, la]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natPredArm (pv (vpool s₀.mem) oa.toNat la.toNat)) a₀ ∧
      R s'.mem (AM.st (natPredArm (pv (vpool s₀.mem) oa.toNat la.toNat)) a₀) ∧
      AM.res (natPredArm (pv (vpool s₀.mem) oa.toNat la.toNat)) a₀ =
        some (decE (r.headD 0)) ∧ HW (r.headD 0); ⊤⦄ := by
  have hok := hpool _ _ hR
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  rw [invoke_eq _ hg]
  simp only [callFn, natPredLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, natop_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        natSub_spec p hpl hps hpt hpn n, hI a₀ n] <;>
      finish (gen := 20) [natPredArm]

end predhw

/-- After `nat_pred_lit`: `(1, handle)`. -/
def npLitF (x : List Word × Mem) : Option (Word × Word × Mem) := some (1, x.1.headD 0, x.2)

/-- The model of `nat_pred`. -/
def natPredW (p : Prog) (n : Nat) (m : Mem) (e : Word) : Option (Word × Word × Mem) :=
  if e >>> 28 = 8 then
    if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m LIT (tierW e) ≤ idxW e then none
    else if tfld m LIT (tierW e) (idxW e) 0 ≠ 0 then some (0, 0, m)
    else if tfld m LIT (tierW e) (idxW e) 2 = 0 then some (0, 0, m)
    else (callW p n "nat_pred_lit" [tfld m LIT (tierW e) (idxW e) 1,
      tfld m LIT (tierW e) (idxW e) 2] m).bind npLitF
  else if e >>> 28 = 4 then
    if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m APP (tierW e) ≤ idxW e then none
    else if tfld m APP (tierW e) (idxW e) 0 >>> 28 ≠ 3 then some (0, 0, m)
    else if tierW (tfld m APP (tierW e) (idxW e) 0) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
      then none
    else if tcnt m CONST (tierW (tfld m APP (tierW e) (idxW e) 0)) ≤
      idxW (tfld m APP (tierW e) (idxW e) 0) then none
    else if tfld m CONST (tierW (tfld m APP (tierW e) (idxW e) 0)) (idxW (tfld m APP (tierW e) (idxW e) 0)) 0 = rdW (m.arr64 PINS) (1 + 3) ∧
      tfld m CONST (tierW (tfld m APP (tierW e) (idxW e) 0)) (idxW (tfld m APP (tierW e) (idxW e) 0)) 1 = rdW (m.arr64 PINS) 52
      then some (1, tfld m APP (tierW e) (idxW e) 1, m)
    else some (0, 0, m)
  else some (0, 0, m)

-- Two views (and a callee): the paths cost more than the default budget.
set_option maxHeartbeats 2000000 in
theorem natPred_spec (p : Prog) (hp : NatPredProg p) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_pred" [e]
    ⦃fun r s' => LocEq s' s₀ ∧
      natPredW p n s₀.mem e = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.np]
  simp only [callFn, natPredL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "nat_pred_lit", pinAt_rd p hp.leaf.pinat n, pinWord_rd p hp.leaf.pinword n] <;>
    finish [natPredW, npLitF, Option.bind_some, tierW, idxW]

theorem am_eq_run {α : Type} [Inhabited α] {T T' : AM α} {a : AState} (h : T.run a = T'.run a) :
    AM.ok T a = AM.ok T' a ∧ AM.st T a = AM.st T' a ∧ AM.res T a = AM.res T' a := by
  simp only [AM.ok, AM.st, AM.res, h, and_self]

/-- **`nat_pred` refines `natPred?`**, both result words handle words (`ResW`). -/
@[refines ConRon.Arena.natPred?]
theorem natPred_refines (p : Prog) (hp : NatPredProg p) (hlw : LitInternHW) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb e : Word) (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) :
    CoreSpec p (n + 1) "nat_pred" [e] (natPred? (decE e)) decOptR s₀ a₀ dn vis fe MM eb ResW := by
  refine triple_post (natPred_spec p hp n s₀ e) fun r s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  have hR := hS.arena.1
  have hP := hS.pins
  -- the arms that keep the state
  have hres : ∀ (x y : Word), some (x, y, s₀.mem) = some (r.headD 0, r.tail.headD 0, s'.mem) →
      HW x → HW y → (natPred? (decE e)).run a₀ = .ok (decOpt x y, a₀) →
      CoreRef (natPred? (decE e)) a₀ decOptR dn s₀.mem vis fe MM eb r s'.mem ResW := by
    intro x y hxy hx hy hv
    simp only [Option.some.injEq, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    rw [← h3]
    obtain ⟨hok, hst, hrs⟩ := AM.of_run_ok _ _ _ _ hv
    refine ⟨hok, ?_, by rw [hrs, decOptR, ← h1, ← h2], ?_⟩
    · rw [hst]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
    · unfold ResW; rw [← h1, ← h2]; exact ⟨hx, hy⟩
  unfold natPredW at hW
  by_cases h8 : e >>> 28 = 8
  · simp only [h8, ↓reduceIte] at hW
    by_cases hs : tierW e ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
    · simp [hs] at hW
    by_cases hc : tcnt s₀.mem LIT (tierW e) ≤ idxW e
    · simp [hs, hc] at hW
    simp only [hs, hc, ↓reduceIte] at hW
    have hvo : viewOK s₀.mem e LIT := ⟨hs, by simpa using hc⟩
    have htl : ((decE e).tag == ETag.lit) = true := by rw [tag_beq_lit e he]; simp [h8]
    obtain ⟨k, hk, hkr⟩ := node_of s₀.mem a₀ e litCS RecRel (·.lits) _ hR.lit.2 hvo.2
    have hview : ∀ l, k = ⟨l⟩ → a₀.store.view (decE e) = some (.lit l) := by
      intro l hl
      rw [view_tier s₀.mem a₀ hR e he hvo.1, get_lit _ e he h8, Tbl.node?, hk, hl]
      rfl
    obtain ⟨l⟩ := k
    cases l with
    | strVal str =>
      simp only [RecRel_strVal, StrRec] at hkr
      have h1 : tfld s₀.mem LIT (tierW e) (idxW e) 0 ≠ 0 := by rw [hkr.1]; decide
      simp only [h1, ne_eq, not_false_eq_true, ↓reduceIte] at hW
      refine hres 0 0 hW hw0 hw0 ?_
      simp only [natPred?, htl, ↓reduceIte, StateT.run_bind, view_run _ _ _ (hview _ rfl),
        except_ok_bind]
      rfl
    | natVal N =>
      simp only [RecRel_natVal, NatRec] at hkr
      obtain ⟨h0, hsl, hn, hpv, -⟩ := hkr
      simp only [h0, ne_eq, not_true_eq_false, ↓reduceIte] at hW
      by_cases hl0 : tfld s₀.mem LIT (tierW e) (idxW e) 2 = 0
      · simp only [hl0, ↓reduceIte] at hW
        have hN : N = 0 := by rw [← hpv, hl0]; rfl
        subst hN
        refine hres 0 0 hW hw0 hw0 ?_
        simp only [natPred?, htl, ↓reduceIte, StateT.run_bind, view_run _ _ _ (hview _ rfl),
          except_ok_bind]
        rfl
      simp only [hl0, ↓reduceIte] at hW
      have hNpos : N ≠ 0 := by
        rw [← hpv]; intro h
        exact hl0 (UInt64.toNat_inj.mp (by simpa using (pv_eq_zero_iff _ _ _ hn).mp h))
      rcases hc2 : callW p n "nat_pred_lit" [tfld s₀.mem LIT (tierW e) (idxW e) 1,
        tfld s₀.mem LIT (tierW e) (idxW e) 2] s₀.mem with _ | ⟨r₁, m₁⟩
      · simp [hc2] at hW
      rw [hc2, Option.bind_some, npLitF, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr0, hr1, hm⟩ := hW
      obtain ⟨t, ht, -, hok, hK, hres', hhw⟩ := triple_of_callW
        (natPredLit_refines_hw p (CoreK dn vis fe MM eb s₀.mem) (fun _ _ h => h.1.arena.1.lit.1)
          (fun m m' a h hg => h.grow hg)
          (internLit_core p hp.lhash hp.leq hp.lmatch hp.lfind hp.lpush hp.lintern hlw dn vis fe MM eb
            s₀.mem)
          hp.limb hp.sbb hp.trim hp.sub hp.npl n s₀ a₀ ⟨hS, StackKept.refl _⟩ _ _ hsl.1 hS.mode) hc2
      rw [hpv] at hok hK hres'
      have hrun : (natPred? (decE e)).run a₀ = (natPredArm N).run a₀ := by
        obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
        simp only [natPred?, htl, ↓reduceIte, StateT.run_bind, view_run _ _ _ (hview _ rfl),
          except_ok_bind, natPredArm, Nat.add_sub_cancel]
      obtain ⟨eok, est, eres⟩ := am_eq_run hrun
      simp only at hm
      rw [ht, hm] at hK
      refine ⟨eok ▸ hok, ?_, ?_, by unfold ResW; rw [← hr0, ← hr1]; exact ⟨hw1, hhw⟩⟩
      · rw [est]; exact ⟨MM, hK.1, KeptAll.refl _ _, hK.2⟩
      · rw [eres, hres', decOptR, ← hr0, ← hr1, decOpt_ne _ _ (by decide)]
  -- the `app` arm
  have htl : ((decE e).tag == ETag.lit) = false := by rw [tag_beq_lit e he]; simp [h8]
  simp only [h8, ↓reduceIte] at hW
  rcases (Classical.em (e >>> 28 = 4)).symm with h4 | h4
  · simp only [h4, ↓reduceIte] at hW
    refine hres 0 0 hW hw0 hw0 ?_
    simp only [natPred?, htl, tag_beq_app e he, h4, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  simp only [h4, ↓reduceIte] at hW
  by_cases hs : tierW e ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · simp [hs] at hW
  by_cases hc : tcnt s₀.mem APP (tierW e) ≤ idxW e
  · simp [hs, hc] at hW
  simp only [hs, hc, ↓reduceIte] at hW
  have hvo : viewOK s₀.mem e APP := ⟨hs, by simpa using hc⟩
  obtain ⟨-, hf, hx⟩ := view_app s₀.mem a₀ hR e he hvo h4
  have hpre : (natPred? (decE e)).run a₀ = (do
      let f := decE (tfld s₀.mem APP (tierW e) (idxW e) 0)
      if f.tag == ETag.const then
        match ← view f with
        | .const c us => do
          let el ← emptyLevels
          let ns ← pinNatSucc
          if c == ns && us == el then
            pure (some (decE (tfld s₀.mem APP (tierW e) (idxW e) 1)))
          else pure none
        | _ => pure none
      else pure none : AM (Option EIdx)).run a₀ := by
    simp only [natPred?, htl, tag_beq_app e he, h4, decide_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, viewApp_run', viewApp_ok s₀.mem a₀ hR e he hvo, except_ok_bind]
    rfl
  generalize tfld s₀.mem APP (tierW e) (idxW e) 0 = f at hf hW hpre
  generalize tfld s₀.mem APP (tierW e) (idxW e) 1 = x at hx hW hpre
  rcases (Classical.em (f >>> 28 = 3)).symm with f3 | f3
  · simp only [ne_eq, f3, not_false_eq_true, ↓reduceIte] at hW
    refine hres 0 0 hW hw0 hw0 ?_
    rw [hpre]
    simp only [tag_beq_const f hf, f3, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  by_cases fs : tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · simp [f3, fs] at hW
  by_cases fc : tcnt s₀.mem CONST (tierW f) ≤ idxW f
  · simp [f3, fs, fc] at hW
  simp only [f3, fs, fc, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  have fvo : viewOK s₀.mem f CONST := ⟨fs, by simpa using fc⟩
  obtain ⟨hv, hn, hu⟩ := L.Ind.view_const_f s₀.mem a₀ hR f hf fvo f3
  have hel := hP.lv_lt.1
  rw [pinW_rdW s₀.mem 52 52 rfl] at hel
  have hns := hP.names_lt 3 (by decide)
  rw [pinW_rdW s₀.mem (1 + 3) (1 + 3) rfl] at hns
  have hrun2 : (natPred? (decE e)).run a₀ = .ok (
      if tfld s₀.mem CONST (tierW f) (idxW f) 0 = rdW (s₀.mem.arr64 PINS) (1 + 3) ∧
        tfld s₀.mem CONST (tierW f) (idxW f) 1 = rdW (s₀.mem.arr64 PINS) 52
      then some (decE x) else none, a₀) := by
    rw [hpre]
    simp only [tag_beq_const f hf, f3, decide_true, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv,
      except_ok_bind, emptyLevels, pinEmptyLevels_run hP, pinNatSucc, PIN_NAT_SUCC,
      pinAt_run hP 3 (by decide), pinW_rdW s₀.mem 52 52 rfl, pinW_rdW s₀.mem (1 + 3) (1 + 3) rfl]
    rw [decI_beq _ _ hn hns, decI_beq _ _ hu hel]
    by_cases h1 : tfld s₀.mem CONST (tierW f) (idxW f) 0 = rdW (s₀.mem.arr64 PINS) (1 + 3) <;>
    by_cases h2 : tfld s₀.mem CONST (tierW f) (idxW f) 1 = rdW (s₀.mem.arr64 PINS) 52 <;>
    simp only [h1, h2, decide_true, decide_false, Bool.and_true, Bool.and_false, Bool.false_eq_true,
      and_true, and_false, ↓reduceIte] <;> rfl
  by_cases hc2 : tfld s₀.mem CONST (tierW f) (idxW f) 0 = rdW (s₀.mem.arr64 PINS) (1 + 3) ∧
      tfld s₀.mem CONST (tierW f) (idxW f) 1 = rdW (s₀.mem.arr64 PINS) 52
  · simp only [hc2, and_self, ↓reduceIte] at hW hrun2
    exact hres 1 x hW hw1 hx (by rw [hrun2, decOpt_ne _ _ (by decide)])
  · simp only [hc2, ↓reduceIte] at hW hrun2
    exact hres 0 0 hW hw0 hw0 (by rw [hrun2]; rfl)

/-! ## `lit_eq`: the literal comparison of `quickDefEq` -/

/-- The model of `lit_eq` (`none` where it aborts). -/
def litEqW (m : Mem) (a b : Word) : Option Word :=
  if tierW a ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m LIT (tierW a) ≤ idxW a then none
  else if tierW b ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m LIT (tierW b) ≤ idxW b then none
  else if tfld m LIT (tierW a) (idxW a) 0 ≠ tfld m LIT (tierW b) (idxW b) 0
    then some 0
  else if tfld m LIT (tierW a) (idxW a) 2 ≠
      tfld m LIT (tierW b) (idxW b) 2 then some 0
  else some (if eqW (tpool m) (tfld m LIT (tierW a) (idxW a) 1)
      (tfld m LIT (tierW b) (idxW b) 1)
      (tfld m LIT (tierW a) (idxW a) 2) 0 then 1 else 0)

/-- `limbs_eq` reads the total pool view; on slices below `2^41` it is the virtual pool. -/
theorem eqW_tpool (m : Mem) (a b l i : Word) (ha : a.toNat + l.toNat ≤ 2 ^ 41)
    (hb : b.toNat + l.toNat ≤ 2 ^ 41) : eqW (tpool m) a b l i = eqW (vpool m) a b l i := by
  have e : ∀ j, j < 2 ^ 41 → (tpool m)[j]?.getD 0 = (vpool m)[j]?.getD 0 := fun j hj => by
    rw [tpool_vpool m j hj]
  rw [Bool.eq_iff_iff, eqW_iff _ _ _ _ _ (by omega) (by omega), eqW_iff _ _ _ _ _ (by omega) (by omega)]
  constructor <;> intro h k hk1 hk2
  · rw [← e _ (by omega), ← e _ (by omega)]; exact h k hk1 hk2
  · rw [e _ (by omega), e _ (by omega)]; exact h k hk1 hk2

-- Two views: the paths cost more than the default budget.
set_option maxHeartbeats 2000000 in
theorem litEq_spec (p : Prog) (hle : p.lookup "lit_eq" = some litEqL)
    (hlq : p.lookup "limbs_eq" = some limbsEq) (n : Nat) (s₀ : St) (a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lit_eq" [a, b]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ litEqW s₀.mem a b = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hle]
  simp only [callFn, litEqL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE, limbsEq_spec p hlq n] <;>
    finish [litEqW, tierW, idxW]

/-- **A `lit` node's record**, past the view checks: a `natVal` is a normalised slice of its value,
a `strVal` a slice of its bytes; kind word `0`/`1`; the slice below the pool top. -/
theorem lit_rec (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : HW h)
    (hv : viewOK m h LIT) (hg : h >>> 28 = 8) (l : ConLeche.Literal)
    (hl : a.store.view (decE h) = some (.lit l)) :
    (tfld m LIT (tierW h) (idxW h) 1).toNat +
      (tfld m LIT (tierW h) (idxW h) 2).toNat ≤ m.top.toNat ∧
    (∀ N, l = .natVal N → tfld m LIT (tierW h) (idxW h) 0 = 0 ∧
      Norm (vpool m) (tfld m LIT (tierW h) (idxW h) 1).toNat
        (tfld m LIT (tierW h) (idxW h) 2).toNat ∧
      pv (vpool m) (tfld m LIT (tierW h) (idxW h) 1).toNat
        (tfld m LIT (tierW h) (idxW h) 2).toNat = N) ∧
    (∀ s, l = .strVal s → tfld m LIT (tierW h) (idxW h) 0 = 1 ∧
      sliceL (vpool m) (tfld m LIT (tierW h) (idxW h) 1).toNat
        (tfld m LIT (tierW h) (idxW h) 2).toNat = strWords s) := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h litCS RecRel (·.lits) _ hR.lit.2 hv.2
  have hview : a.store.view (decE h) = some (.lit k.l) := by
    rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk]; rfl
  rw [hl] at hview
  have hkl : l = k.l := by simpa using hview
  subst hkl
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · simp only [RecRel_natVal, NatRec] at hkr
    obtain ⟨h0, hsl, hn, hpv, -⟩ := hkr
    refine ⟨hsl.1.1, fun N' e => ?_, fun s e => by cases e⟩
    cases e; exact ⟨h0, hn, hpv⟩
  · simp only [RecRel_strVal, StrRec] at hkr
    obtain ⟨h1, hsl, hs, -⟩ := hkr
    refine ⟨hsl.1.1, fun N e => (by cases e), fun s' e => ?_⟩
    cases e; exact ⟨h1, hs⟩

/-- **`lit_eq` decides `l₁ == l₂`** on two `lit` handles (`quickDefEq`'s `.lit l₁, .lit l₂` arm). -/
@[refines_part ConRon.Arena.quickDefEq "literal comparison"]
theorem litEq_refines (p : Prog) (hle : p.lookup "lit_eq" = some litEqL)
    (hlq : p.lookup "limbs_eq" = some limbsEq) (n : Nat) (s₀ : St) (a₀ : AState)
    (hR : ArenaR s₀.mem a₀) (a b : Word) (ha : HW a) (hb : HW b) (ha8 : a >>> 28 = 8)
    (hb8 : b >>> 28 = 8) (l₁ l₂ : ConLeche.Literal)
    (hv₁ : a₀.store.view (decE a) = some (.lit l₁)) (hv₂ : a₀.store.view (decE b) = some (.lit l₂)) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lit_eq" [a, b]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ decBool r = (l₁ == l₂) ∧ ResH r; ⊤⦄ := by
  refine triple_post (litEq_spec p hle hlq n s₀ a b) fun r s' ⟨hm, hloc, hW⟩ => ⟨hm, hloc, ?_⟩
  unfold litEqW at hW
  by_cases as : tierW a ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · simp [as] at hW
  by_cases ac : tcnt s₀.mem LIT (tierW a) ≤ idxW a
  · simp [as, ac] at hW
  by_cases bs : tierW b ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · simp [ac, bs] at hW
  by_cases bc : tcnt s₀.mem LIT (tierW b) ≤ idxW b
  · simp [as, ac, bs, bc] at hW
  simp only [as, ac, bs, bc, ↓reduceIte] at hW
  obtain ⟨sl₁, hn₁, hs₁⟩ := lit_rec s₀.mem a₀ hR a ha ⟨as, by simpa using ac⟩ ha8 l₁ hv₁
  obtain ⟨sl₂, hn₂, hs₂⟩ := lit_rec s₀.mem a₀ hR b hb ⟨bs, by simpa using bc⟩ hb8 l₂ hv₂
  have ⟨_, _, hps, htop⟩ := hR.lit.1
  generalize tfld s₀.mem LIT (tierW a) (idxW a) 0 = k₁ at hW hn₁ hs₁
  generalize tfld s₀.mem LIT (tierW b) (idxW b) 0 = k₂ at hW hn₂ hs₂
  generalize tfld s₀.mem LIT (tierW a) (idxW a) 1 = o₁ at hW hn₁ hs₁ sl₁
  generalize tfld s₀.mem LIT (tierW b) (idxW b) 1 = o₂ at hW hn₂ hs₂ sl₂
  generalize tfld s₀.mem LIT (tierW a) (idxW a) 2 = c₁ at hW hn₁ hs₁ sl₁
  generalize tfld s₀.mem LIT (tierW b) (idxW b) 2 = c₂ at hW hn₂ hs₂ sl₂
  have h41 := hR.lit.1.top41
  have hb₁ : o₁.toNat + c₁.toNat < 2 ^ 64 := by omega
  have hb₂ : o₂.toNat + c₂.toNat < 2 ^ 64 := by omega
  have hres : ∀ c : Prop, [Decidable c] → some (if c then (1 : Word) else 0) = some (r.headD 0) →
      decide c = (l₁ == l₂) → decBool r = (l₁ == l₂) ∧ ResH r := by
    intro c _ h hc
    simp only [Option.some.injEq] at h
    exact ⟨by rw [decBool_of h, hc], resH_of hw1 hw0 h⟩
  have h0 : some (0 : Word) = some (r.headD 0) → (l₁ == l₂) = false →
      decBool r = (l₁ == l₂) ∧ ResH r := by
    intro h hc
    simp only [Option.some.injEq] at h
    refine ⟨by rw [hc, decBool, ← h]; rfl, by unfold ResH; rw [← h]; exact hw0⟩
  cases l₁ with
  | natVal N₁ =>
    obtain ⟨hk₁, hN₁, hp₁⟩ := hn₁ N₁ rfl
    cases l₂ with
    | natVal N₂ =>
      obtain ⟨hk₂, hN₂, hp₂⟩ := hn₂ N₂ rfl
      subst hk₁ hk₂
      simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hW
      by_cases hc : c₁ = c₂
      · subst hc
        simp only [not_true_eq_false, ↓reduceIte] at hW
        rw [eqW_tpool s₀.mem o₁ o₂ c₁ 0 (by omega) (by omega)] at hW
        refine hres _ hW ?_
        have : (ConLeche.Literal.natVal N₁ == .natVal N₂) = decide (N₁ = N₂) := by
          rw [Bool.eq_iff_iff]; simp
        rw [this]
        apply decide_eq_decide.mpr
        constructor
        · intro h; rw [← hp₁, ← hp₂]; exact pv_of_eqW _ _ _ _ hb₁ hb₂ h
        · intro h; rw [← hp₁, ← hp₂] at h; exact (slice_eq _ _ _ _ _ hN₁ hN₂ hb₁ hb₂ h).2.1
      · simp only [hc, not_false_eq_true, ↓reduceIte] at hW
        refine h0 hW ?_
        simp only [beq_eq_false_iff_ne, ne_eq, ConLeche.Literal.natVal.injEq]
        intro h; subst h; rw [← hp₁] at hp₂
        exact hc (UInt64.toNat_inj.mp (pv_len _ _ _ _ _ _ hN₁ hN₂ hp₂.symm))
    | strVal s₂ =>
      obtain ⟨hk₂, -⟩ := hs₂ s₂ rfl
      subst hk₁ hk₂
      simp only [show (0 : Word) ≠ 1 by decide, ne_eq, not_false_eq_true, ↓reduceIte] at hW
      exact h0 hW (by simp)
  | strVal s₁ =>
    obtain ⟨hk₁, hS₁⟩ := hs₁ s₁ rfl
    cases l₂ with
    | natVal N₂ =>
      obtain ⟨hk₂, -⟩ := hn₂ N₂ rfl
      subst hk₁ hk₂
      simp only [show (1 : Word) ≠ 0 by decide, ne_eq, not_false_eq_true, ↓reduceIte] at hW
      exact h0 hW (by simp)
    | strVal s₂ =>
      obtain ⟨hk₂, hS₂⟩ := hs₂ s₂ rfl
      subst hk₁ hk₂
      simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hW
      have hkey := slice_key (vpool s₀.mem) o₁ c₁ o₂ c₂ hb₁ hb₂
      rw [hS₁, hS₂] at hkey
      by_cases hc : c₁ = c₂
      · subst hc
        simp only [not_true_eq_false, ↓reduceIte] at hW
        rw [eqW_tpool s₀.mem o₁ o₂ c₁ 0 (by omega) (by omega)] at hW
        refine hres _ hW ?_
        have : (ConLeche.Literal.strVal s₁ == .strVal s₂) = decide (s₁ = s₂) := by
          rw [Bool.eq_iff_iff]; simp
        rw [this]
        apply decide_eq_decide.mpr
        simp only [beq_self_eq_true, Bool.true_and] at hkey
        rw [hkey]
        exact ⟨strWords_inj _ _, fun h => by rw [h]⟩
      · simp only [hc, not_false_eq_true, ↓reduceIte] at hW
        refine h0 hW ?_
        simp only [beq_eq_false_iff_ne, ne_eq, ConLeche.Literal.strVal.injEq]
        intro h; subst h
        have := hkey.mpr rfl
        simp only [Bool.and_eq_true, beq_iff_eq] at this
        exact hc this.1

end L.Arena
