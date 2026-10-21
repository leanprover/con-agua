import ConRon.Arena.Monad
import ConAgua.Arena.Refine
import ConAgua.Arena.Store

/-!
# The `lit` store refines the arena's `lit` tables; `natAddLit_refines` without hypotheses

`ConAgua/Arena/Store.lean` has the L code of the `lit` node store and its specs against
word-level models (`probeW`, `matchW`, `internW`). This file relates them to con-ron's arena:

* **`LitR m a`**, the state relation (`natAddLit_refines`'s `R`): the pool is well formed, the
  scratch flag `CTL[1]` is `a.store.scratchOn`, and each tier of the L store represents the
  arena's `lit` table of that tier (`TierRel`): the same nodes in the same order (so the same
  handles), each `natVal` node a normalised slice below the pool top with its hash, and an L
  cons table with the same key → handle map as the arena's `Std.HashMap`, whose layout is
  never looked at (`SlotsOK`: the linear-probing invariant, node `i` reachable from its home
  slot through occupied slots).
* **The arena side** (`internE_lit_run`): `internE (.lit l)` unfolded to the three probes and the
  append, as one equation.
* **The table lemmas**: a match of `lit_match` is equality of literals (`matchW_iff`, through the
  uniqueness of normalised slices, `pv_len`/`pv_limbs`); the probe either aborts, finds a
  matching node, or stops at a free slot after non-matching ones (`probe_cases`); a hit is the
  arena's cons hit at the same handle (`tier_hit`), a miss means the literal is absent
  (`tier_miss`), and `lit_push` at the free slot represents the arena's append (`tier_push`,
  `tier_other`).
* **`intern_correct`**: `internW` (the model of `intern_lit`) refines `internE (.lit (.natVal _))`.
* **`LitR.grow`**: appending to the pool preserves `LitR`.
* **`natAddLit_refines_store`**, `natAddLit_run_store`: milestone 3's `natAddLit_refines` with
  `R := LitR` and its three hypotheses discharged.

Not represented: the arena's derived column for `lit` nodes (`derOfLit`, through Lean's opaque
`mixHash`), the contents of `strVal` nodes (kind `1` only), and every other table of `AState`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The arena's `lit` cons key of a literal. -/
abbrev litKey (l : ConLeche.Literal) : LitNode := ⟨l⟩

/-- `a` with the scratch / persistent `lit` table replaced. -/
def withScrLits (a : AState) (t : Tbl LitNode EIdx UInt64) : AState :=
  { a with store := { a.store with scr := { a.store.scr with lits := t } } }
def withPersLits (a : AState) (t : Tbl LitNode EIdx UInt64) : AState :=
  { a with store := { a.store with pers := { a.store.pers with lits := t } } }

/-- `internE` at a literal, unfolded: the persistent probe, the scratch probe (when the scratch
tier is open), the capacity test and the append. -/
theorem internE_lit_run (l : ConLeche.Literal) (a : AState) :
    (internE (.lit l)).run a =
      match a.store.pers.lits.cons[litKey l]? with
      | some h => .ok (h, a)
      | none =>
        if a.store.scratchOn then
          match a.store.scr.lits.cons[litKey l]? with
          | some h => .ok (h, a)
          | none =>
            if a.store.scr.lits.size < Idx.idxCap then
              .ok (Idx.mk ETag.lit Idx.tierS (UInt32.ofNat a.store.scr.lits.size),
                withScrLits a (a.store.scr.lits.push (litKey l) (a.store.derOfView (.lit l))
                    (Idx.mk ETag.lit Idx.tierS (UInt32.ofNat a.store.scr.lits.size))))
            else .error (.native "arena: expression constructor array full")
        else
          if a.store.pers.lits.size < Idx.idxCap then
            .ok (Idx.mk ETag.lit Idx.tierP (UInt32.ofNat a.store.pers.lits.size),
              withPersLits a (a.store.pers.lits.push (litKey l) (a.store.derOfView (.lit l))
                  (Idx.mk ETag.lit Idx.tierP (UInt32.ofNat a.store.pers.lits.size))))
          else .error (.native "arena: expression constructor array full") := by
  simp only [internE, internNodeE, EStore.find?, EStore.persFindMaybe,
    EStore.eViewHasScratchChild, EStore.intern, ETables.find?, Tbl.find?, ETables.sizeOf,
    ETables.push]
  cases hp : a.store.pers.lits.cons[litKey l]? <;> cases hs : a.store.scratchOn <;>
    cases hc : a.store.scr.lits.cons[litKey l]? <;>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hp, hs, hc, Bool.false_eq_true,
      ↓reduceIte, litKey, ite_self] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrLits, withPersLits, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## Normalised slices are unique -/

theorem wt_mono {i j : Nat} (h : i ≤ j) : wt i ≤ wt j :=
  Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ h)

theorem pv_lt (p : Array Word) (o l : Nat) : pv p o l < wt l := by
  induction l with
  | zero => simp [pv, wt]
  | succ k ih =>
    have hx := (p[o + k]?.getD 0).toNat_lt
    have hw : wt (k + 1) = wt k * 2 ^ 64 := wt_succ k _ rfl
    simp only [pv, hw]
    have : (p[o + k]?.getD 0).toNat * wt k ≤ (2 ^ 64 - 1) * wt k :=
      Nat.mul_le_mul_right _ (by omega)
    have : (2 ^ 64 - 1) * wt k + wt k = wt k * 2 ^ 64 := by
      rw [Nat.mul_comm (wt k)]; have := wt_pos k; rw [Nat.sub_mul]; omega
    omega

theorem pv_ge (p : Array Word) (o l : Nat) (hl : 0 < l) (hn : Norm p o l) : wt (l - 1) ≤ pv p o l := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have h := hn hl
  simp only [Nat.add_sub_cancel] at h ⊢
  simp only [pv]
  have : 1 ≤ (p[o + k]?.getD 0).toNat := by
    rcases Nat.eq_zero_or_pos (p[o + k]?.getD 0).toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) h
    · exact h0
  have := Nat.mul_le_mul_right (wt k) this
  omega

/-- Two normalised slices with the same value have the same length. -/
theorem pv_len (p q : Array Word) (a b la lb : Nat) (ha : Norm p a la) (hb : Norm q b lb)
    (h : pv p a la = pv q b lb) : la = lb := by
  rcases Nat.lt_trichotomy la lb with hl | hl | hl
  · have := pv_ge q b lb (by omega) hb
    have := pv_lt p a la
    have := wt_mono (show la ≤ lb - 1 by omega)
    omega
  · exact hl
  · have := pv_ge p a la (by omega) ha
    have := pv_lt q b lb
    have := wt_mono (show lb ≤ la - 1 by omega)
    omega

/-- Two slices of the same length with the same value agree limb for limb. -/
theorem pv_limbs (p q : Array Word) (a b l : Nat) (h : pv p a l = pv q b l) :
    ∀ i < l, p[a + i]?.getD 0 = q[b + i]?.getD 0 := by
  induction l with
  | zero => intro i hi; omega
  | succ k ih =>
    simp only [pv] at h
    have hA := pv_lt p a k
    have hB := pv_lt q b k
    have hw := wt_pos k
    have hx : (p[a + k]?.getD 0).toNat = (q[b + k]?.getD 0).toNat := by
      have e1 : (pv p a k + (p[a + k]?.getD 0).toNat * wt k) / wt k = (p[a + k]?.getD 0).toNat := by
        rw [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hA]; simp
      have e2 : (pv q b k + (q[b + k]?.getD 0).toNat * wt k) / wt k = (q[b + k]?.getD 0).toNat := by
        rw [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hB]; simp
      rw [← e1, ← e2, h]
    have hk : pv p a k = pv q b k := by
      have := congrArg (· % wt k) h
      simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB] at this
      exact this
    intro i hi
    rcases Nat.lt_or_ge i k with hik | hik
    · exact ih hk i hik
    · have : i = k := by omega
      subst this; exact UInt64.toNat_inj.mp hx

theorem pv_congr (p q : Array Word) (a b l : Nat)
    (h : ∀ i < l, p[a + i]?.getD 0 = q[b + i]?.getD 0) : pv p a l = pv q b l := by
  induction l with
  | zero => rfl
  | succ k ih =>
    simp only [pv, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem hashN_congr (p q : Array Word) (a b l : Nat)
    (h : ∀ i < l, p[a + i]?.getD 0 = q[b + i]?.getD 0) : hashN p a l = hashN q b l := by
  induction l with
  | zero => rfl
  | succ k ih =>
    simp only [hashN, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem Agree.hashN (p q : Array Word) (t o k : Nat) (h : Agree p q t) (hk : o + k ≤ t) :
    L.Arena.hashN p o k = L.Arena.hashN q o k :=
  hashN_congr p q o o k (fun i hi => by rw [h (o + i) (by omega)])

theorem Agree.norm (p q : Array Word) (t o l : Nat) (h : Agree p q t) (hk : o + l ≤ t)
    (hn : Norm q o l) : Norm p o l := by
  intro hl; rw [h (o + (l - 1)) (by omega)]; exact hn hl

/-- `eqW` from position `i` in `Nat` terms, where no index wraps. -/
theorem eqW_iff (p : Array Word) (a b l i : Word) (ha : a.toNat + l.toNat < 2 ^ 64)
    (hb : b.toNat + l.toNat < 2 ^ 64) :
    eqW p a b l i = true ↔
      ∀ k, i.toNat ≤ k → k < l.toNat → p[a.toNat + k]?.getD 0 = p[b.toNat + k]?.getD 0 := by
  fun_induction eqW p a b l i with
  | case1 i hi he ih =>
    rw [ih]
    have hil : i.toNat < l.toNat := hi
    have h1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hai : (a + i).toNat = a.toNat + i.toNat := by rw [UInt64.toNat_add]; omega
    have hbi : (b + i).toNat = b.toNat + i.toNat := by rw [UInt64.toNat_add]; omega
    rw [hai, hbi] at he
    rw [h1]
    constructor
    · intro H k hk hkl
      rcases Nat.eq_or_lt_of_le hk with hk | hk
      · subst hk; exact he
      · exact H k (by omega) hkl
    · intro H k hk hkl; exact H k (by omega) hkl
  | case2 i hi he =>
    have hil : i.toNat < l.toNat := hi
    have hai : (a + i).toNat = a.toNat + i.toNat := by rw [UInt64.toNat_add]; omega
    have hbi : (b + i).toNat = b.toNat + i.toNat := by rw [UInt64.toNat_add]; omega
    rw [hai, hbi] at he
    simp only [Bool.false_eq_true, false_iff]
    intro H; exact he (H _ (Nat.le_refl _) hil)
  | case3 i hi =>
    have hil : ¬ i.toNat < l.toNat := hi
    simp only [true_iff]; intro k hk hkl; omega

/-! ## The relation between L memory and the arena's `lit` tables -/

/-- Field `f` of node `i` of tier `t`. -/
def fld (m : Mem) (t i f : Nat) : Word := (m.arr64 REC)[8 * i + 4 * t + f]?.getD 0
/-- Slot `j` of tier `t`. -/
def slt (m : Mem) (t j : Nat) : Word := (m.arr64 SLOT)[2 * j + t]?.getD 0
/-- The number of slots per tier. -/
def ns (m : Mem) : Nat := (m.arr64 SLOT).size / 2
/-- The home slot of node `i` of tier `t`. -/
def homeN (m : Mem) (t i : Nat) : Nat := (homeW (fld m t i 3) (nSlots m)).toNat

/-- Node `i` of tier `t` holds the literal `k`: a `natVal` as a normalised slice below the top,
with its hash; a `strVal` as kind `1` (its contents are not represented yet). -/
def RecRel (m : Mem) (t i : Nat) (k : LitNode) : Prop :=
  match k.l with
  | .natVal N => fld m t i 0 = 0 ∧ (fld m t i 1).toNat + (fld m t i 2).toNat ≤ m.top.toNat ∧
      Norm (m.arr64 POOL) (fld m t i 1).toNat (fld m t i 2).toNat ∧
      pv (m.arr64 POOL) (fld m t i 1).toNat (fld m t i 2).toNat = N ∧
      fld m t i 3 = hashN (m.arr64 POOL) (fld m t i 1).toNat (fld m t i 2).toNat
  | .strVal _ => fld m t i 0 = 1

/-- The slots of tier `t` index its `c` nodes, and node `i` is reachable from its home slot by
a run of occupied slots (the invariant of linear probing without deletion). -/
def SlotsOK (m : Mem) (t c : Nat) : Prop :=
  (∀ j < ns m, (slt m t j).toNat ≤ c) ∧
  ∀ i < c, ∃ d < ns m, slt m t ((homeN m t i + d) % ns m) = UInt64.ofNat (i + 1) ∧
    ∀ e < d, slt m t ((homeN m t i + e) % ns m) ≠ 0

/-- Tier `t` of the L store represents the arena table `tb`: same nodes, in the same order (so
the same handles), and a cons table with the same key → handle map. Nothing is said about the
layout of `tb.cons`, which depends on its insertion history. -/
def TierRel (m : Mem) (t : Nat) (tb : Tbl LitNode EIdx UInt64) : Prop :=
  (cnt m (UInt64.ofNat t)).toNat = tb.nodes.size ∧ tb.nodes.size ≤ Idx.idxCap ∧
  8 * tb.nodes.size ≤ (m.arr64 REC).size ∧
  (∀ (i : Nat) k, tb.nodes[i]? = some k → RecRel m t i k) ∧
  (∀ (i : Nat) k, tb.nodes[i]? = some k →
    tb.cons[k]? = some (Idx.mk ETag.lit (UInt32.ofNat t) (UInt32.ofNat i))) ∧
  (∀ k : LitNode, (∀ i : Nat, tb.nodes[i]? ≠ some k) → tb.cons[k]? = none) ∧
  SlotsOK m t tb.nodes.size

/-- **The state relation.** The pool is well formed, the scratch flag is the arena's, and both
tiers of the `lit` store represent the arena's `lit` tables. -/
def LitR (m : Mem) (a : AState) : Prop :=
  PoolOK m ∧ 4 ≤ (m.arr64 CTL).size ∧ (m.arr64 REC).size < 2 ^ 63 ∧
  (m.arr64 SLOT).size < 2 ^ 63 ∧ (rdW (m.arr64 CTL) 1 ≠ 0 ↔ a.store.scratchOn = true) ∧
  TierRel m 0 a.store.pers.lits ∧ TierRel m 1 a.store.scr.lits

/-! ### Reading the L store -/

theorem nSlots_toNat (m : Mem) (h : (m.arr64 SLOT).size < 2 ^ 63) : (nSlots m).toNat = ns m := by
  simp only [nSlots, ns, Mem.len64, UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
  simp [Nat.shiftRight_eq_div_pow]; omega

theorem homeW_lt (h n : Word) (hn : 0 < n.toNat) : (homeW h n).toNat < n.toNat := by
  simp only [homeW]
  have hx := ((h * golden) ^^^ ((h * golden) >>> 32)).toNat_lt
  have hn' := n.toNat_lt
  have : ((h * golden) ^^^ ((h * golden) >>> 32)).toNat * n.toNat / 2 ^ 64 < n.toNat :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right hx hn)
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact this

theorem rec_toNat (i t c : Nat) (hi : i < 2 ^ 27) (ht : t ≤ 1) (hc : c < 4) :
    (UInt64.ofNat i * 8 + UInt64.ofNat t * 4 + UInt64.ofNat c).toNat = 8 * i + 4 * t + c := by
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
    show (8 : Word).toNat = 8 from rfl, show (4 : Word).toNat = 4 from rfl]
  omega

theorem rdW_rec (m : Mem) (i t c : Nat) (hi : i < 2 ^ 27) (ht : t ≤ 1) (hc : c < 4) :
    rdW (m.arr64 REC) (UInt64.ofNat i * 8 + UInt64.ofNat t * 4 + UInt64.ofNat c) = fld m t i c := by
  simp only [rdW, fld, rec_toNat i t c hi ht hc]

theorem rdW_recW (m : Mem) (i t : Nat) (c : Word) (hi : i < 2 ^ 27) (ht : t ≤ 1) (hc : c.toNat < 4) :
    rdW (m.arr64 REC) (UInt64.ofNat i * 8 + UInt64.ofNat t * 4 + c) = fld m t i c.toNat := by
  have := rdW_rec m i t c.toNat hi ht hc
  simpa using this

theorem rdW_rec0 (m : Mem) (i t : Nat) (hi : i < 2 ^ 27) (ht : t ≤ 1) :
    rdW (m.arr64 REC) (UInt64.ofNat i * 8 + UInt64.ofNat t * 4) = fld m t i 0 := by
  have := rdW_rec m i t 0 hi ht (by decide)
  simpa using this

theorem rdW_slt (m : Mem) (j : Word) (t : Nat) (hj : j.toNat < 2 ^ 62) (ht : t ≤ 1) :
    rdW (m.arr64 SLOT) (j * 2 + UInt64.ofNat t) = slt m t j.toNat := by
  simp only [rdW, slt, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
    show (2 : Word).toNat = 2 from rfl]
  congr 2; omega

/-- **Matching is equality of literals.** On a node of a represented tier, `lit_match`'s model
holds exactly when the node is the `natVal` the query slice denotes. -/
theorem matchW_iff (m : Mem) (t : Nat) (ht : t ≤ 1) (tb : Tbl LitNode EIdx UInt64)
    (hT : TierRel m t tb) (hpool : PoolOK m) (i : Nat) (k : LitNode) (hk : tb.nodes[i]? = some k)
    (o l : Word) (hq : o.toNat + l.toNat ≤ m.top.toNat) (hn : Norm (m.arr64 POOL) o.toNat l.toNat) :
    matchW (m.arr64 REC) (m.arr64 POOL) (UInt64.ofNat t) (UInt64.ofNat i) o l
        (hashN (m.arr64 POOL) o.toNat l.toNat) = true ↔
      k = litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)) := by
  obtain ⟨-, hcap, -, hrec, -, -, -⟩ := hT
  have hi : i < 2 ^ 27 := by
    have := (Array.getElem?_eq_some_iff.mp hk).1
    simp only [Idx.idxCap] at hcap; omega
  obtain ⟨-, -, hps, htop⟩ := hpool
  have hr := hrec i k hk
  simp only [matchW, rdW_rec0 m i t hi ht, rdW_recW m i t 3 hi ht (by decide),
    rdW_recW m i t 2 hi ht (by decide), rdW_recW m i t 1 hi ht (by decide),
    show (3 : Word).toNat = 3 from rfl, show (2 : Word).toNat = 2 from rfl,
    show (1 : Word).toNat = 1 from rfl]
  obtain ⟨lit⟩ := k
  cases lit with
  | strVal s =>
    simp only [RecRel] at hr
    simp [hr, litKey]
  | natVal N =>
    simp only [RecRel] at hr
    obtain ⟨h0, hsl, hnorm, hpv, hh⟩ := hr
    have hl1 : (fld m t i 1).toNat + l.toNat < 2 ^ 64 ∨ fld m t i 2 ≠ l := by
      by_cases h2 : fld m t i 2 = l
      · left; rw [← h2]; omega
      · right; exact h2
    simp only [h0, hh, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq, litKey,
      LitNode.mk.injEq, ConLeche.Literal.natVal.injEq]
    constructor
    · rintro ⟨⟨-, h2⟩, he⟩
      subst h2
      rw [eqW_iff _ _ _ _ _ (by omega) (by omega)] at he
      rw [← hpv]
      exact pv_congr _ _ _ _ _ (fun k hk => he k (Nat.zero_le _) hk)
    · intro hN
      rw [← hpv] at hN
      have hlen := pv_len _ _ _ _ _ _ hnorm hn hN
      have h2 : fld m t i 2 = l := UInt64.toNat_inj.mp hlen
      rw [h2] at hN hnorm ⊢
      have hlimbs := pv_limbs _ _ _ _ _ hN
      refine ⟨⟨hashN_congr _ _ _ _ _ hlimbs, rfl⟩, ?_⟩
      rw [eqW_iff _ _ _ _ _ (by rw [← h2]; omega) (by omega)]
      intro k _ hk; exact hlimbs k hk

/-! ### The probe -/

/-- The first `d` slots of the run from `home` are occupied by nodes that do not match. -/
def NoMatch (m : Mem) (t : Nat) (o l h : Word) (home d : Nat) : Prop :=
  ∀ e < d, slt m t ((home + e) % ns m) ≠ 0 ∧
    matchW (m.arr64 REC) (m.arr64 POOL) (UInt64.ofNat t) (slt m t ((home + e) % ns m) - 1) o l h =
      false

theorem mod_succ_lt (a n : Nat) (h : a % n + 1 < n) : (a + 1) % n = a % n + 1 := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < n by omega), Nat.mod_eq_of_lt h]

theorem mod_succ_eq (a n : Nat) (h : a % n + 1 = n) : (a + 1) % n = 0 := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · rw [Nat.add_mod, Nat.mod_eq_of_lt hn, h, Nat.mod_self]
  · have : n = 1 := by omega
    subst this; simp [Nat.mod_one]

/-- What the probe model returns: nothing (the L code aborts), a matching node, or the first
free slot of the run, after a run of nodes that do not match. -/
theorem probe_cases (m : Mem) (t : Nat) (ht : t ≤ 1) (hS : (m.arr64 SLOT).size < 2 ^ 63)
    (o l h : Word) (home : Nat) :
    ∀ (k : Nat) (j d : Word), ns m - d.toNat = k → d.toNat ≤ ns m →
      (d.toNat < ns m → j.toNat = (home + d.toNat) % ns m) → NoMatch m t o l h home d.toNat →
      probeW (m.arr64 SLOT) (m.arr64 REC) (m.arr64 POOL) (UInt64.ofNat t) o l h (nSlots m) j d = [] ∨
      (∃ e < ns m, probeW (m.arr64 SLOT) (m.arr64 REC) (m.arr64 POOL) (UInt64.ofNat t) o l h
          (nSlots m) j d =
        [1, slt m t ((home + e) % ns m) - 1, UInt64.ofNat ((home + e) % ns m), UInt64.ofNat e] ∧
        slt m t ((home + e) % ns m) ≠ 0 ∧
        matchW (m.arr64 REC) (m.arr64 POOL) (UInt64.ofNat t) (slt m t ((home + e) % ns m) - 1) o l h
          = true) ∨
      (∃ e < ns m, probeW (m.arr64 SLOT) (m.arr64 REC) (m.arr64 POOL) (UInt64.ofNat t) o l h
          (nSlots m) j d = [0, 0, UInt64.ofNat ((home + e) % ns m), UInt64.ofNat e] ∧
        slt m t ((home + e) % ns m) = 0 ∧ NoMatch m t o l h home e) := by
  have hn := nSlots_toNat m (by omega)
  intro k
  induction k with
  | zero =>
    intro j d hk hd _ _
    left
    rw [probeW, ite_eq_right_of_eq_false _ _ (eq_false (by rw [UInt64.lt_iff_toNat_lt, hn]; omega))]
  | succ k ih =>
    intro j d hk hd hj hnm
    have hdn : d.toNat < ns m := by omega
    have hjn := hj hdn
    have hjlt : j.toNat < ns m := by rw [hjn]; exact Nat.mod_lt _ (by omega)
    have hjd : j = UInt64.ofNat ((home + d.toNat) % ns m) := by
      rw [← hjn, UInt64.ofNat_toNat]
    have hdd : d = UInt64.ofNat d.toNat := by rw [UInt64.ofNat_toNat]
    have hns : ns m ≤ 2 ^ 62 := by simp only [ns]; omega
    rw [probeW, ite_eq_left_of_eq_true _ _ (eq_true (by rw [UInt64.lt_iff_toNat_lt, hn]; exact hdn)),
      rdW_slt m j t (by omega) ht]
    by_cases h0 : slt m t j.toNat = 0
    · right; right
      refine ⟨d.toNat, hdn, ?_, by rw [← hjn]; exact h0, hnm⟩
      simp only [h0, ↓reduceIte, ← hjn, UInt64.ofNat_toNat]
    · simp only [h0, ↓reduceIte]
      by_cases hm : matchW (m.arr64 REC) (m.arr64 POOL) (UInt64.ofNat t) (slt m t j.toNat - 1) o l h
          = true
      · right; left
        refine ⟨d.toNat, hdn, ?_, by rw [← hjn]; exact h0, by rw [← hjn]; exact hm⟩
        simp only [h0, hm, ↓reduceIte, ← hjn, UInt64.ofNat_toNat]
      · simp only [hm, ↓reduceIte, Bool.false_eq_true]
        have hd1 : (d + 1).toNat = d.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; omega
        apply ih
        · rw [hd1]; omega
        · rw [hd1]; omega
        · intro hlt
          rw [hd1] at hlt ⊢
          have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
          by_cases hw : j + 1 < nSlots m
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hw), UInt64.mul_one, hj1, hjn]
            rw [UInt64.lt_iff_toNat_lt, hj1, hn] at hw
            rw [hjn] at hw
            rw [← Nat.add_assoc, mod_succ_lt _ _ hw]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hw), UInt64.mul_zero]
            rw [UInt64.lt_iff_toNat_lt, hj1, hn] at hw
            have : j.toNat + 1 = ns m := by omega
            rw [hjn] at this
            simp only [UInt64.toNat_zero]
            rw [← Nat.add_assoc, mod_succ_eq _ _ this]
        · rw [hd1]
          intro e he
          rcases Nat.lt_or_ge e d.toNat with hlt | hge
          · exact hnm e hlt
          · have : e = d.toNat := by omega
            subst this
            rw [← hjn]
            exact ⟨h0, by simpa using hm⟩

/-! ### Hit and miss -/

section tier
variable (m : Mem) (t : Nat) (ht : t ≤ 1) (tb : Tbl LitNode EIdx UInt64) (hT : TierRel m t tb)
  (hpool : PoolOK m) (hS : (m.arr64 SLOT).size < 2 ^ 63) (o l : Word)
  (hq : o.toNat + l.toNat ≤ m.top.toNat) (hn : Norm (m.arr64 POOL) o.toNat l.toNat)

include ht in
theorem fld3_of_match (i : Nat) (hi : i < 2 ^ 27) (h : Word)
    (hm : matchW (m.arr64 REC) (m.arr64 POOL) (UInt64.ofNat t) (UInt64.ofNat i) o l h = true) :
    fld m t i 3 = h := by
  simp only [matchW, rdW_recW m i t 3 hi ht (by decide), show (3 : Word).toNat = 3 from rfl,
    Bool.and_eq_true, beq_iff_eq] at hm
  exact hm.1.1.2

theorem node_lt (i : Nat) (k : LitNode) (hk : tb.nodes[i]? = some k) : i < tb.nodes.size :=
  (Array.getElem?_eq_some_iff.mp hk).1

include ht hT hpool hq hn in
/-- A probe hit is the arena's cons-table hit, at the same handle. -/
theorem tier_hit (e : Nat) (he : e < ns m)
    (hv : slt m t (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e) % ns m) ≠ 0)
    (hm : matchW (m.arr64 REC) (m.arr64 POOL) (UInt64.ofNat t)
      (slt m t (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e) % ns m) - 1)
      o l (hashN (m.arr64 POOL) o.toNat l.toNat) = true) :
    let v := slt m t (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e) % ns m)
    v - 1 = UInt64.ofNat (v.toNat - 1) ∧ v.toNat - 1 < 2 ^ 27 ∧
    tb.cons[litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))]? =
      some (Idx.mk ETag.lit (UInt32.ofNat t) (UInt32.ofNat (v.toNat - 1))) := by
  intro v
  obtain ⟨hc, hcap, -, hrec, hsome, -, hslots, -⟩ := id hT
  have hvle : v.toNat ≤ tb.nodes.size := hslots _ (Nat.mod_lt _ (show ns m > 0 by omega))
  have hv0 : 0 < v.toNat := by
    rcases Nat.eq_zero_or_pos v.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hv
    · exact h0
  have hv1 : v - 1 = UInt64.ofNat (v.toNat - 1) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega),
      UInt64.toNat_ofNat']
    have := v.toNat_lt; simp; omega
  simp only [Idx.idxCap] at hcap
  refine ⟨hv1, by omega, ?_⟩
  have hi : v.toNat - 1 < tb.nodes.size := by omega
  obtain ⟨k, hk⟩ : ∃ k, tb.nodes[v.toNat - 1]? = some k := ⟨_, Array.getElem?_eq_getElem hi⟩
  rw [hv1] at hm
  rw [matchW_iff m t ht tb hT hpool _ k hk o l hq hn] at hm
  subst hm
  exact hsome _ _ hk

include ht hT hpool hq hn in
/-- A probe miss: the literal is not in the tier. -/
theorem tier_miss (e : Nat) (he : e < ns m)
    (hv : slt m t (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e) % ns m) = 0)
    (hnm : NoMatch m t o l (hashN (m.arr64 POOL) o.toNat l.toNat)
      (homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat e) :
    ∀ i : Nat, tb.nodes[i]? ≠ some (litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))) := by
  intro i hk
  obtain ⟨-, hcap, -, -, -, -, -, hrun⟩ := id hT
  have hic := node_lt tb i _ hk
  simp only [Idx.idxCap] at hcap
  have hi : i < 2 ^ 27 := by omega
  have hm := (matchW_iff m t ht tb hT hpool i _ hk o l hq hn).mpr rfl
  have h3 := fld3_of_match m t ht o l i hi _ hm
  obtain ⟨d, hd, hslot, hbefore⟩ := hrun i hic
  have hhome : homeN m t i = (homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat := by
    simp only [homeN, h3]
  rw [hhome] at hslot hbefore
  have hne : UInt64.ofNat (i + 1) ≠ 0 := by
    intro h0
    have := congrArg UInt64.toNat h0
    rw [UInt64.toNat_ofNat'] at this; simp at this; omega
  rcases Nat.lt_trichotomy d e with hlt | heq | hgt
  · obtain ⟨-, hf⟩ := hnm d hlt
    rw [hslot] at hf
    have : UInt64.ofNat (i + 1) - 1 = UInt64.ofNat i := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat']; simp; omega), UInt64.toNat_ofNat',
        UInt64.toNat_ofNat']
      simp; omega
    rw [this, hm] at hf
    exact Bool.noConfusion hf
  · subst heq; rw [hslot] at hv; exact hne hv
  · exact hbefore e hgt hv

end tier

/-! ### The memory after `lit_push` -/

theorem getD_set! (a : Array Word) (k x : Nat) (v : Word) :
    (a.set! k v)[x]?.getD 0 = if k = x ∧ x < a.size then v else a[x]?.getD 0 := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h : k = x
  · subst h; by_cases h' : k < a.size <;> simp [h']
  · simp [h]

theorem size_set! (a : Array Word) (k : Nat) (v : Word) : (a.set! k v).size = a.size := by
  simp [Array.set!_eq_setIfInBounds]

theorem size_arr64_set64 (m : Mem) (a b : ArrId) (i v : Word) :
    ((m.set64 a i v).arr64 b).size = (m.arr64 b).size := by
  by_cases h : b = a
  · subst h; rw [Mem.arr64_set64_same, size_set!]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]

/-- The index of field `x` of node `C` of tier `t`, as `lit_push` computes it. -/
theorem recW_toNat (C : Word) (t : Nat) (x : Word) (hC : C.toNat < 2 ^ 27) (ht : t ≤ 1)
    (hx : x.toNat < 4) : (C * 8 + UInt64.ofNat t * 4 + x).toNat = 8 * C.toNat + 4 * t + x.toNat := by
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
    show (8 : Word).toNat = 8 from rfl, show (4 : Word).toNat = 4 from rfl]
  omega

theorem recW0_toNat (C : Word) (t : Nat) (hC : C.toNat < 2 ^ 27) (ht : t ≤ 1) :
    (C * 8 + UInt64.ofNat t * 4).toNat = 8 * C.toNat + 4 * t := by
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
    show (8 : Word).toNat = 8 from rfl, show (4 : Word).toNat = 4 from rfl]
  omega

section push
variable (m : Mem) (t : Nat) (ht : t ≤ 1) (o l h J C : Word) (hC : C.toNat < 2 ^ 27)
  (hJ : J.toNat < 2 ^ 62)

theorem pm_arr (a : ArrId) (ha1 : a ≠ REC) (ha2 : a ≠ SLOT) (ha3 : a ≠ CTL) :
    (pushMem m (UInt64.ofNat t) o l h J C).arr64 a = m.arr64 a := by
  simp only [pushMem, Mem.arr64_set64_ne _ _ _ _ _ ha1, Mem.arr64_set64_ne _ _ _ _ _ ha2,
    Mem.arr64_set64_ne _ _ _ _ _ ha3]

include ht hC in
theorem pm_rec :
    (pushMem m (UInt64.ofNat t) o l h J C).arr64 REC =
      ((((m.arr64 REC).set! (8 * C.toNat + 4 * t) 0).set! (8 * C.toNat + 4 * t + 1) o).set!
        (8 * C.toNat + 4 * t + 2) l).set! (8 * C.toNat + 4 * t + 3) h := by
  simp only [pushMem, Mem.arr64_set64_ne _ _ _ _ _ (show REC ≠ CTL by decide),
    Mem.arr64_set64_ne _ _ _ _ _ (show REC ≠ SLOT by decide), Mem.arr64_set64_same,
    recW0_toNat C t hC ht, recW_toNat C t 1 hC ht (by decide), recW_toNat C t 2 hC ht (by decide),
    recW_toNat C t 3 hC ht (by decide)]
  rfl

include ht hJ in
theorem pm_slot :
    (pushMem m (UInt64.ofNat t) o l h J C).arr64 SLOT =
      (m.arr64 SLOT).set! (2 * J.toNat + t) (C + 1) := by
  simp only [pushMem, Mem.arr64_set64_ne _ _ _ _ _ (show SLOT ≠ CTL by decide), Mem.arr64_set64_same,
    Mem.arr64_set64_ne _ _ _ _ _ (show SLOT ≠ REC by decide)]
  congr 1
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
    show (2 : Word).toNat = 2 from rfl]
  omega

include ht in
theorem pm_ctl :
    (pushMem m (UInt64.ofNat t) o l h J C).arr64 CTL = (m.arr64 CTL).set! (2 + t) (C + 1) := by
  have e : (2 + UInt64.ofNat t).toNat = 2 + t := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', show (2 : Word).toNat = 2 from rfl]; omega
  simp only [pushMem, Mem.arr64_set64_same, e, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ SLOT by decide),
    Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ REC by decide)]

include ht hC in
theorem pm_fld (t' i f : Nat) (ht' : t' ≤ 1) (hf : f < 4)
    (hsz : 8 * C.toNat + 8 ≤ (m.arr64 REC).size) :
    fld (pushMem m (UInt64.ofNat t) o l h J C) t' i f =
      if t' = t ∧ i = C.toNat then (if f = 0 then 0 else if f = 1 then o else if f = 2 then l else h)
      else fld m t' i f := by
  simp only [fld, pm_rec m t ht o l h J C hC, getD_set!, size_set!]
  by_cases hc : t' = t ∧ i = C.toNat
  · obtain ⟨rfl, rfl⟩ := hc
    simp only [and_self, ↓reduceIte]
    rcases (show f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 by omega) with rfl | rfl | rfl | rfl <;> simp <;> omega
  · simp only [hc, ↓reduceIte]
    have : ∀ g < 4, ¬ (8 * C.toNat + 4 * t + g = 8 * i + 4 * t' + f) := by
      intro g hg heq; apply hc; omega
    have h0 := this 0 (by decide); have h1 := this 1 (by decide); have h2 := this 2 (by decide)
    have h3 := this 3 (by decide)
    simp only [Nat.add_zero] at h0
    simp [h0, h1, h2, h3]

include ht hJ in
theorem pm_slt (t' j : Nat) (ht' : t' ≤ 1) (hj : 2 * J.toNat + t < (m.arr64 SLOT).size) :
    slt (pushMem m (UInt64.ofNat t) o l h J C) t' j =
      if t' = t ∧ j = J.toNat then C + 1 else slt m t' j := by
  simp only [slt, pm_slot m t ht o l h J C hJ, getD_set!]
  by_cases hc : t' = t ∧ j = J.toNat
  · obtain ⟨rfl, rfl⟩ := hc; simp [hj]
  · simp only [hc, ↓reduceIte]
    have : ¬ (2 * J.toNat + t = 2 * j + t') := by intro heq; apply hc; omega
    simp [this]

include ht in
theorem pm_cnt (t' : Nat) (ht' : t' ≤ 1) (hctl : 4 ≤ (m.arr64 CTL).size) :
    cnt (pushMem m (UInt64.ofNat t) o l h J C) (UInt64.ofNat t') =
      if t' = t then C + 1 else cnt m (UInt64.ofNat t') := by
  have e : (2 + UInt64.ofNat t').toNat = 2 + t' := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', show (2 : Word).toNat = 2 from rfl]; omega
  simp only [cnt, rdW, pm_ctl m t ht o l h J C, getD_set!, e]
  by_cases hc : t' = t
  · subst hc; simp; omega
  · have : ¬ (2 + t = 2 + t') := by omega
    simp [this, hc, Ne.symm hc]

include ht in
theorem pm_ctl_low (x : Nat) (hx : x < 2) :
    ((pushMem m (UInt64.ofNat t) o l h J C).arr64 CTL)[x]?.getD 0 = (m.arr64 CTL)[x]?.getD 0 := by
  simp only [pm_ctl m t ht o l h J C, getD_set!]
  have : ¬ (2 + t = x) := by omega
  simp [this]

include ht in
theorem pm_top : (pushMem m (UInt64.ofNat t) o l h J C).top = m.top := by
  simp only [Mem.top]
  have := pm_ctl_low m t ht o l h J C 0 (by decide)
  simpa using this

include ht in
theorem pm_flag : rdW ((pushMem m (UInt64.ofNat t) o l h J C).arr64 CTL) 1 = rdW (m.arr64 CTL) 1 := by
  simp only [rdW]; exact pm_ctl_low m t ht o l h J C 1 (by decide)

theorem pm_size (a : ArrId) :
    ((pushMem m (UInt64.ofNat t) o l h J C).arr64 a).size = (m.arr64 a).size := by
  simp only [pushMem, size_arr64_set64]

end push

/-! ### `lit_push` preserves the relation -/

theorem Tbl.push_nodes (tb : Tbl LitNode EIdx UInt64) (a : LitNode) (d : UInt64) (i : EIdx) :
    (tb.push a d i).nodes = tb.nodes.push a := by cases tb; rfl

theorem Tbl.push_cons (tb : Tbl LitNode EIdx UInt64) (a : LitNode) (d : UInt64) (i : EIdx) :
    (tb.push a d i).cons = tb.cons.insert a i := by cases tb; rfl

theorem RecRel_congr (m m' : Mem) (t i : Nat) (k : LitNode)
    (hf : ∀ f < 4, fld m' t i f = fld m t i f) (hp : m'.arr64 POOL = m.arr64 POOL)
    (htop : m'.top = m.top) (h : RecRel m t i k) : RecRel m' t i k := by
  obtain ⟨lit⟩ := k
  cases lit <;> simp only [RecRel] at h ⊢ <;>
    simp only [hf 0 (by decide), hf 1 (by decide), hf 2 (by decide), hf 3 (by decide), hp, htop] <;>
    exact h

theorem nSlots_congr (m m' : Mem) (h : (m'.arr64 SLOT).size = (m.arr64 SLOT).size) :
    nSlots m' = nSlots m := by simp only [nSlots, Mem.len64, h]

theorem pushOK_nat (m : Mem) (t : Word) (h : pushOK m t = true) (hR : (m.arr64 REC).size < 2 ^ 63) :
    (cnt m t).toNat < 2 ^ 27 ∧ 8 * (cnt m t).toNat + 8 ≤ (m.arr64 REC).size := by
  simp only [pushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, -⟩ := h
  rw [UInt64.lt_iff_toNat_lt] at h1 h2
  simp only [Mem.len64, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
    show (3 : Word).toNat = 3 from rfl, Nat.shiftRight_eq_div_pow] at h2
  refine ⟨by simpa using h1, ?_⟩
  rw [Nat.mod_eq_of_lt (by omega)] at h2
  simp only [show 3 % 64 = 3 from rfl, show 2 ^ 3 = 8 from rfl] at h2
  omega

section pushRel
variable (m : Mem) (t : Nat) (ht : t ≤ 1) (o l h J C : Word) (hC : C.toNat < 2 ^ 27)
  (hJ : J.toNat < 2 ^ 62) (hj : 2 * J.toNat + t < (m.arr64 SLOT).size)
  (hsz : 8 * C.toNat + 8 ≤ (m.arr64 REC).size) (hctl : 4 ≤ (m.arr64 CTL).size)

include ht hC hJ hj hsz hctl in
/-- Appending to tier `t` leaves the other tier represented. -/
theorem tier_other (t' : Nat) (ht' : t' ≤ 1) (hne : t' ≠ t) (tb : Tbl LitNode EIdx UInt64)
    (hT : TierRel m t' tb) : TierRel (pushMem m (UInt64.ofNat t) o l h J C) t' tb := by
  obtain ⟨hc, hcap, hrs, hrec, hsome, hnone, hsl, hrun⟩ := hT
  have hf : ∀ i, ∀ f < 4, fld (pushMem m (UInt64.ofNat t) o l h J C) t' i f = fld m t' i f := by
    intro i f hf
    rw [pm_fld m t ht o l h J C hC t' i f ht' hf hsz]; simp [hne]
  have hs : ∀ j, slt (pushMem m (UInt64.ofNat t) o l h J C) t' j = slt m t' j := by
    intro j; rw [pm_slt m t ht o l h J C hJ t' j ht' hj]; simp [hne]
  have hns : ns (pushMem m (UInt64.ofNat t) o l h J C) = ns m := by simp only [ns, pm_size]
  have hhome : ∀ i, homeN (pushMem m (UInt64.ofNat t) o l h J C) t' i = homeN m t' i := by
    intro i; simp only [homeN, hf i 3 (by decide), nSlots_congr _ _ (pm_size _ _ _ _ _ _ _ _)]
  refine ⟨?_, hcap, ?_, ?_, hsome, hnone, ?_, ?_⟩
  · rw [pm_cnt m t ht o l h J C t' ht' hctl]; simp [hne, hc]
  · rw [pm_size]; exact hrs
  · intro i k hk
    exact RecRel_congr _ _ _ _ _ (hf i) (pm_arr _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide))
      (pm_top m t ht o l h J C) (hrec i k hk)
  · intro j hjn; rw [hs]; rw [hns] at hjn; exact hsl j hjn
  · intro i hi
    obtain ⟨d, hd, h1, h2⟩ := hrun i hi
    refine ⟨d, by rw [hns]; exact hd, ?_, ?_⟩
    · rw [hns, hhome, hs]; exact h1
    · intro e he; rw [hns, hhome, hs]; exact h2 e he

include ht hC hJ hj hsz hctl in
/-- Appending the queried literal to tier `t`, at the free slot `J` that ends the run from its
home slot, represents the arena's append. -/
theorem tier_push (tb : Tbl LitNode EIdx UInt64) (hT : TierRel m t tb)
    (hcC : C = cnt m (UInt64.ofNat t))
    (hq : o.toNat + l.toNat ≤ m.top.toNat) (hn : Norm (m.arr64 POOL) o.toNat l.toNat)
    (hh : h = hashN (m.arr64 POOL) o.toNat l.toNat) (e : Nat) (he : e < ns m)
    (hJe : J.toNat = ((homeW h (nSlots m)).toNat + e) % ns m) (hv : slt m t J.toNat = 0)
    (hrun' : ∀ e' < e, slt m t (((homeW h (nSlots m)).toNat + e') % ns m) ≠ 0)
    (habs : ∀ i : Nat, tb.nodes[i]? ≠ some (litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))))
    (dd : UInt64) :
    TierRel (pushMem m (UInt64.ofNat t) o l h J C) t
      (tb.push (litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))) dd
        (Idx.mk ETag.lit (UInt32.ofNat t) (UInt32.ofNat tb.nodes.size))) := by
  obtain ⟨hc, hcap, hrs, hrec, hsome, hnone, hsl, hrun⟩ := hT
  rw [← hcC] at hc
  have hns : ns (pushMem m (UInt64.ofNat t) o l h J C) = ns m := by simp only [ns, pm_size]
  have hnS : nSlots (pushMem m (UInt64.ofNat t) o l h J C) = nSlots m := nSlots_congr _ _ (pm_size _ _ _ _ _ _ _ _)
  have hf : ∀ i, i ≠ C.toNat → ∀ f < 4, fld (pushMem m (UInt64.ofNat t) o l h J C) t i f = fld m t i f := by
    intro i hi f hf
    rw [pm_fld m t ht o l h J C hC t i f ht hf hsz]; simp [hi]
  have hfc : ∀ f < 4, fld (pushMem m (UInt64.ofNat t) o l h J C) t C.toNat f =
      (if f = 0 then 0 else if f = 1 then o else if f = 2 then l else h) := by
    intro f hf
    rw [pm_fld m t ht o l h J C hC t _ f ht hf hsz]; simp
  have hs : ∀ j, slt (pushMem m (UInt64.ofNat t) o l h J C) t j = if j = J.toNat then C + 1 else slt m t j := by
    intro j; rw [pm_slt m t ht o l h J C hJ t j ht hj]; simp
  have hhome : ∀ i, i ≠ C.toNat → homeN (pushMem m (UInt64.ofNat t) o l h J C) t i = homeN m t i := by
    intro i hi; simp only [homeN, hf i hi 3 (by decide), hnS]
  have hC1 : (C + 1).toNat = C.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have hne1 : C + 1 ≠ 0 := by
    intro h0; have := congrArg UInt64.toNat h0; rw [hC1] at this; simp at this
  simp only [TierRel, SlotsOK, Tbl.push_nodes, Tbl.push_cons, Array.size_push]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pm_cnt m t ht o l h J C t ht hctl]; simp [hC1, hc]
  · simp only [Idx.idxCap] at hcap ⊢; omega
  · rw [pm_size]; omega
  · intro i k hk
    rw [Array.getElem?_push] at hk
    split at hk
    · rename_i hi
      cases hk
      simp only [litKey, RecRel]
      rw [← hc] at hi; subst hi
      simp only [hfc 0 (by decide), hfc 1 (by decide), hfc 2 (by decide), hfc 3 (by decide),
        ↓reduceIte, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
        show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
        show (3 : Nat) ≠ 2 by decide, pm_arr m t o l h J C POOL (by decide) (by decide) (by decide),
        pm_top m t ht o l h J C]
      exact ⟨trivial, hq, hn, trivial, hh⟩
    · rename_i hi
      have hic := node_lt tb i k hk
      exact RecRel_congr _ _ _ _ _ (hf i (by omega))
        (pm_arr _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)) (pm_top m t ht o l h J C)
        (hrec i k hk)
  · intro i k hk
    rw [Array.getElem?_push] at hk
    rw [Std.HashMap.getElem?_insert]
    split at hk
    · rename_i hi; cases hk; simp [hi]
    · have hkk : k ≠ (litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))) := by intro heq; subst heq; exact habs i hk
      simp only [beq_iff_eq, Ne.symm hkk, ↓reduceIte]
      exact hsome i k hk
  · intro k hk
    rw [Std.HashMap.getElem?_insert]
    have hkk : (litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))) ≠ k := by
      intro heq; subst heq; apply hk tb.nodes.size; simp
    simp only [beq_iff_eq, hkk, ↓reduceIte]
    apply hnone; intro i hi; apply hk i; rw [Array.getElem?_push]
    have := node_lt tb i k hi
    simp [show i ≠ tb.nodes.size by omega, hi]
  · intro j hjn
    rw [hns] at hjn
    rw [hs]; split
    · omega
    · have := hsl j hjn; omega
  · intro i hi
    rcases Nat.lt_or_ge i tb.nodes.size with hlt | hge
    · obtain ⟨d, hd, h1, h2⟩ := hrun i hlt
      have hic : i ≠ C.toNat := by omega
      refine ⟨d, by rw [hns]; exact hd, ?_, ?_⟩
      · rw [hns, hhome i hic, hs]
        have : (homeN m t i + d) % ns m ≠ J.toNat := by
          intro heq; rw [heq, hv] at h1
          have := congrArg UInt64.toNat h1
          rw [UInt64.toNat_ofNat'] at this; simp at this
          simp only [Idx.idxCap] at hcap; omega
        simp only [this, ↓reduceIte]; exact h1
      · intro e' he'; rw [hns, hhome i hic, hs]
        split
        · exact hne1
        · exact h2 e' he'
    · have hic : i = C.toNat := by omega
      subst hic
      have hhc : homeN (pushMem m (UInt64.ofNat t) o l h J C) t C.toNat = (homeW h (nSlots m)).toNat := by
        simp only [homeN, hfc 3 (by decide), show (3 : Nat) ≠ 0 by decide,
          show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, ↓reduceIte, hnS]
      refine ⟨e, by rw [hns]; exact he, ?_, ?_⟩
      · rw [hns, hhc, hs, ← hJe]; simp only [↓reduceIte]
        apply UInt64.toNat_inj.mp; rw [hC1, UInt64.toNat_ofNat']; simp; omega
      · intro e' he'; rw [hns, hhc, hs]
        split
        · exact hne1
        · exact hrun' e' he'

end pushRel

/-! ### Frames -/

/-- A tier stays represented when its records, slots and count are unchanged, the pool agrees
below the old top, and the top only moves up. -/
theorem TierRel.transfer (m m' : Mem) (t : Nat) (tb : Tbl LitNode EIdx UInt64)
    (hrec : m'.arr64 REC = m.arr64 REC) (hslot : m'.arr64 SLOT = m.arr64 SLOT)
    (hcnt : cnt m' (UInt64.ofNat t) = cnt m (UInt64.ofNat t))
    (hagree : Agree (m'.arr64 POOL) (m.arr64 POOL) m.top.toNat) (htop : m.top.toNat ≤ m'.top.toNat)
    (hT : TierRel m t tb) : TierRel m' t tb := by
  obtain ⟨hc, hcap, hrs, hr, hsome, hnone, hsl, hrun⟩ := hT
  have hf : ∀ i f, fld m' t i f = fld m t i f := by intro i f; simp only [fld, hrec]
  have hs : ∀ j, slt m' t j = slt m t j := by intro j; simp only [slt, hslot]
  have hns : ns m' = ns m := by simp only [ns, hslot]
  have hhome : ∀ i, homeN m' t i = homeN m t i := by
    intro i; simp only [homeN, hf, nSlots_congr m m' (by rw [hslot])]
  refine ⟨by rw [hcnt]; exact hc, hcap, by rw [hrec]; exact hrs, ?_, hsome, hnone, ?_, ?_⟩
  · intro i k hk
    have h := hr i k hk
    obtain ⟨lit⟩ := k
    cases lit with
    | strVal => simp only [RecRel] at h ⊢; rw [hf]; exact h
    | natVal N =>
      simp only [RecRel] at h ⊢
      simp only [hf]
      obtain ⟨h0, hsl', hn, hpv, hh⟩ := h
      refine ⟨h0, by omega, Agree.norm _ _ _ _ _ hagree hsl' hn, ?_, ?_⟩
      · rw [Agree.pv _ _ _ _ _ hagree hsl']; exact hpv
      · rw [Agree.hashN _ _ _ _ _ hagree hsl']; exact hh
  · intro j hj; rw [hs]; rw [hns] at hj; exact hsl j hj
  · intro i hi
    obtain ⟨d, hd, h1, h2⟩ := hrun i hi
    exact ⟨d, by rw [hns]; exact hd, by rw [hns, hhome, hs]; exact h1,
      fun e he => by rw [hns, hhome, hs]; exact h2 e he⟩

theorem cnt_eq_of_ctl (m m' : Mem) (t : Nat) (ht : t ≤ 1)
    (h : ∀ x, 2 ≤ x → (m'.arr64 CTL)[x]?.getD 0 = (m.arr64 CTL)[x]?.getD 0) :
    cnt m' (UInt64.ofNat t) = cnt m (UInt64.ofNat t) := by
  have e : (2 + UInt64.ofNat t).toNat = 2 + t := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', show (2 : Word).toNat = 2 from rfl]; omega
  simp only [cnt, rdW, e]; exact h _ (by omega)

/-- **Appending to the pool preserves the relation** (`natAddLit_refines`'s `hgrow`). -/
theorem LitR.grow (m m' : Mem) (a : AState) (hR : LitR m a) (hg : Grows m m') : LitR m' a := by
  obtain ⟨⟨hc1, hc2, hps, htop⟩, hctl, hrs, hss, hflag, hT0, hT1⟩ := hR
  obtain ⟨hfr, hag, ht1, ht2, hps'⟩ := hg
  have hne : ∀ b, b ≠ POOL → m'.arr64 b = (m.set64 CTL 0 m'.top).arr64 b :=
    fun b hb => Frame.arr64 _ _ _ _ hfr hb
  have hrec : m'.arr64 REC = m.arr64 REC := by
    rw [hne REC (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hslot : m'.arr64 SLOT = m.arr64 SLOT := by
    rw [hne SLOT (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hctl' : m'.arr64 CTL = (m.arr64 CTL).set! 0 m'.top := by
    rw [hne CTL (by decide), Mem.arr64_set64_same]; rfl
  have hctlx : ∀ x, x ≠ 0 → (m'.arr64 CTL)[x]?.getD 0 = (m.arr64 CTL)[x]?.getD 0 := by
    intro x hx; rw [hctl', getD_set!]; simp [Ne.symm hx]
  have hws : m'.words.size = m.words.size := by
    rw [Frame.size _ _ _ hfr]; simp [Mem.words_size_set64]
  refine ⟨⟨by rw [hws]; exact hc1, by rw [hctl', size_set!]; exact hc2, by omega, ht2⟩,
    by rw [hctl', size_set!]; exact hctl, by rw [hrec]; exact hrs, by rw [hslot]; exact hss, ?_,
    ?_, ?_⟩
  · simp only [rdW, show (1 : Word).toNat = 1 from rfl] at hflag ⊢
    rw [hctlx 1 (by decide)]; exact hflag
  · exact TierRel.transfer m m' 0 _ hrec hslot
      (cnt_eq_of_ctl m m' 0 (by decide) fun x hx => hctlx x (by omega)) hag ht1 hT0
  · exact TierRel.transfer m m' 1 _ hrec hslot
      (cnt_eq_of_ctl m m' 1 (by decide) fun x hx => hctlx x (by omega)) hag ht1 hT1

/-! ### `intern_lit` refines `internE (.lit (.natVal _))` -/

theorem AM.of_run_ok {α : Type} [Inhabited α] (x : AM α) (a a' : AState) (v : α)
    (h : x.run a = .ok (v, a')) : AM.ok x a ∧ AM.st x a = a' ∧ AM.res x a = v := by
  simp [AM.ok, AM.st, AM.res, h]

theorem decE_lit (b i : Nat) (hb : b * 2 ^ 27 < 2 ^ 28) :
    decE (UInt64.ofNat (2 ^ 31 + b * 2 ^ 27) + UInt64.ofNat i) =
      Idx.mk ETag.lit (UInt32.ofNat b) (UInt32.ofNat i) := by
  simp only [decE, Idx.mk, ETag.lit]
  congr 1
  apply UInt32.toNat_inj.mp
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_ofNat', UInt32.toNat_add,
    UInt32.toNat_mul, UInt32.toNat_ofNat']
  have : b ≤ 1 := by omega
  simp only [show (8 : UInt32).toNat = 8 from rfl, show (268435456 : UInt32).toNat = 268435456 from rfl,
    show (134217728 : UInt32).toNat = 134217728 from rfl]
  omega

theorem litP_eq : litP = UInt64.ofNat (2 ^ 31 + 0 * 2 ^ 27) := rfl
theorem litS_eq : litS = UInt64.ofNat (2 ^ 31 + 1 * 2 ^ 27) := rfl
theorem tierP_eq : Idx.tierP = UInt32.ofNat 0 := rfl
theorem tierS_eq : Idx.tierS = UInt32.ofNat 1 := rfl

/-- The memory after `lit_push` relates to the arena's state after its append to tier `t`. -/
theorem LitR.push (m : Mem) (a a' : AState) (t : Nat) (ht : t ≤ 1) (o l h J : Word)
    (hR : LitR m a) (hflag : a'.store.scratchOn = a.store.scratchOn)
    (h0 : TierRel (pushMem m (UInt64.ofNat t) o l h J (cnt m (UInt64.ofNat t))) 0 a'.store.pers.lits)
    (h1 : TierRel (pushMem m (UInt64.ofNat t) o l h J (cnt m (UInt64.ofNat t))) 1 a'.store.scr.lits) :
    LitR (pushMem m (UInt64.ofNat t) o l h J (cnt m (UInt64.ofNat t))) a' := by
  obtain ⟨⟨hc1, hc2, hps, htop⟩, hctl, hrs, hss, hfl, -, -⟩ := hR
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, h0, h1⟩
  · simp only [pushMem, Mem.words_size_set64]; exact hc1
  · rw [pm_size]; exact hc2
  · rw [pm_size]; exact hps
  · rw [pm_size, pm_top m t ht]; exact htop
  · rw [pm_size]; exact hctl
  · rw [pm_size]; exact hrs
  · rw [pm_size]; exact hss
  · rw [pm_flag m t ht, hflag]; exact hfl

theorem start_pos (x n : Nat) (h : x < n) : x = (x + (0 : Word).toNat) % n := by
  rw [UInt64.toNat_zero, Nat.add_zero, Nat.mod_eq_of_lt h]

section intern
variable (m : Mem) (a : AState) (hR : LitR m a) (o l : Word) (hq : SliceOK m o l)
  (hn : Norm (m.arr64 POOL) o.toNat l.toNat)

include hR hq hn in
/-- **`intern_lit`'s model refines the arena's `internE` at a `natVal` literal.** If the model
(and so the L code) returns the handle `w` and the memory `m'`, the arena's `internE` of the
literal the slice denotes succeeds with the handle `w`, in a state related to `m'`. -/
theorem intern_correct (w : Word) (m' : Mem) (hI : internW m o l = some (w, m')) :
    AM.ok (internE (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)))) a ∧
    LitR m' (AM.st (internE (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)))) a) ∧
    AM.res (internE (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)))) a = decE w := by
  obtain ⟨hpool, hctl, hrs, hss, hflag, hT0, hT1⟩ := id hR
  simp only [SliceOK] at hq
  have hns : (nSlots m).toNat = ns m := nSlots_toNat m hss
  have hns62 : ns m ≤ 2 ^ 62 := by simp only [ns]; omega
  have hstart : ∀ t, t ≤ 1 →
      probeW (m.arr64 SLOT) (m.arr64 REC) (m.arr64 POOL) (UInt64.ofNat t) o l
        (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)
        (homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)) 0 = [] ∨
      (∃ e < ns m, probeW (m.arr64 SLOT) (m.arr64 REC) (m.arr64 POOL) (UInt64.ofNat t) o l
        (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)
        (homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)) 0 =
        [1, slt m t (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e) % ns m) - 1,
          UInt64.ofNat (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e) % ns m),
          UInt64.ofNat e] ∧
        slt m t (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e) % ns m) ≠ 0 ∧
        matchW (m.arr64 REC) (m.arr64 POOL) (UInt64.ofNat t)
          (slt m t (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e) % ns m) - 1)
          o l (hashN (m.arr64 POOL) o.toNat l.toNat) = true) ∨
      (∃ e < ns m, probeW (m.arr64 SLOT) (m.arr64 REC) (m.arr64 POOL) (UInt64.ofNat t) o l
        (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)
        (homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)) 0 =
        [0, 0, UInt64.ofNat (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e) % ns m),
          UInt64.ofNat e] ∧
        slt m t (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e) % ns m) = 0 ∧
        NoMatch m t o l (hashN (m.arr64 POOL) o.toNat l.toNat)
          (homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat e) := by
    intro t ht
    exact probe_cases m t ht hss o l _ _ (ns m) _ 0 (by simp) (by simp)
      (fun h0 => start_pos _ _ (by
        rw [← hns]; exact homeW_lt _ _ (by rw [hns]; simpa using h0)))
      (fun e he => absurd he (by simp))
  have hjb : ∀ e, e < ns m →
      (UInt64.ofNat (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e) % ns m)).toNat
        = ((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e) % ns m := by
    intro e he
    have := Nat.mod_lt ((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e)
      (show ns m > 0 by omega)
    rw [UInt64.toNat_ofNat']; omega
  have hjs : ∀ e, e < ns m → 2 * (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e)
      % ns m) + 1 < (m.arr64 SLOT).size := by
    intro e he
    have := Nat.mod_lt ((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e)
      (show ns m > 0 by omega)
    simp only [ns] at this ⊢; omega
  have hjlt : ∀ e, e < ns m →
      ((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e) % ns m < ns m :=
    fun e he => Nat.mod_lt _ (by omega)
  have hrun := internE_lit_run (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)) a
  simp only [internW] at hI
  rcases hstart 0 (by decide) with h0 | ⟨e, he, hr0, hv, hm0⟩ | ⟨e, he, hr0, hv, hnm⟩
  · -- the persistent probe aborted
    simp only [show UInt64.ofNat 0 = (0 : Word) from rfl] at h0
    simp [h0] at hI
  · -- persistent hit
    obtain ⟨hv1, hi, hcons⟩ := tier_hit m 0 (by decide) _ hT0 hpool o l hq hn e he hv hm0
    simp only [show UInt64.ofNat 0 = (0 : Word) from rfl] at hr0
    simp [hr0] at hI
    obtain ⟨rfl, rfl⟩ := hI
    rw [hcons] at hrun
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨hok, by rw [hst]; exact hR, ?_⟩
    rw [hres, hv1, litP_eq, decE_lit 0 _ (by decide)]; try rfl
  · -- persistent miss
    have habs0 := tier_miss m 0 (by decide) _ hT0 hpool o l hq hn e he hv hnm
    have hnone0 := hT0.2.2.2.2.2.1 _ habs0
    simp only [show UInt64.ofNat 0 = (0 : Word) from rfl] at hr0
    simp only [hr0, reduceCtorEq, ↓reduceIte, List.headD_cons, ne_eq, not_true_eq_false,
      List.tail_cons] at hI
    rw [hnone0] at hrun
    by_cases hsc : a.store.scratchOn = true
    · have hf : rdW (m.arr64 CTL) 1 ≠ 0 := hflag.mpr hsc
      simp only [hf, not_false_eq_true, ↓reduceIte] at hI
      simp only [hsc, ↓reduceIte] at hrun
      rcases hstart 1 (by decide) with h1 | ⟨e', he', hr1, hv', hm1⟩ | ⟨e', he', hr1, hv', hnm'⟩
      · simp only [show UInt64.ofNat 1 = (1 : Word) from rfl] at h1
        simp [h1] at hI
      · obtain ⟨hv1, hi, hcons⟩ := tier_hit m 1 (by decide) _ hT1 hpool o l hq hn e' he' hv' hm1
        simp only [show UInt64.ofNat 1 = (1 : Word) from rfl] at hr1
        simp [hr1] at hI
        obtain ⟨rfl, rfl⟩ := hI
        rw [hcons] at hrun
        obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
        refine ⟨hok, by rw [hst]; exact hR, ?_⟩
        rw [hres, hv1, litS_eq, decE_lit 1 _ (by decide)]; try rfl
      · have habs1 := tier_miss m 1 (by decide) _ hT1 hpool o l hq hn e' he' hv' hnm'
        have hnone1 := hT1.2.2.2.2.2.1 _ habs1
        simp only [show UInt64.ofNat 1 = (1 : Word) from rfl] at hr1
        simp only [hr1, reduceCtorEq, ↓reduceIte, List.headD_cons, ne_eq, not_true_eq_false,
          List.tail_cons] at hI
        rw [hnone1] at hrun
        by_cases hok1 : pushOK m 1 = true
        · simp only [hok1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hI
          obtain ⟨rfl, rfl⟩ := hI
          have ⟨hC, hsz⟩ := pushOK_nat m 1 hok1 hrs
          have hc := hT1.1
          simp only [show UInt64.ofNat 1 = (1 : Word) from rfl] at hc
          have hcap : a.store.scr.lits.size < Idx.idxCap := by
            simp only [Tbl.size, Idx.idxCap]; omega
          simp only [hcap, ↓reduceIte] at hrun
          obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
          have hcw : cnt m 1 = UInt64.ofNat a.store.scr.lits.nodes.size := by
            rw [← hc, UInt64.ofNat_toNat]
          refine ⟨hok, ?_, ?_⟩
          · rw [hst]
            have := LitR.push m a (withScrLits a (a.store.scr.lits.push
              (litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)))
              (a.store.derOfView (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))))
              (Idx.mk ETag.lit Idx.tierS (UInt32.ofNat a.store.scr.lits.size)))) 1 (by decide)
              o l (hashN (m.arr64 POOL) o.toNat l.toNat)
              (UInt64.ofNat (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e')
                % ns m)) hR rfl
              (tier_other m 1 (by decide) _ _ _ _ _ hC (by rw [hjb e' he']; have := hjlt e' he'; omega)
                (by rw [hjb e' he']; exact hjs e' he') hsz hctl 0 (by decide) (by decide) _ hT0)
              (tier_push m 1 (by decide) _ _ _ _ _ hC (by rw [hjb e' he']; have := hjlt e' he'; omega)
                (by rw [hjb e' he']; exact hjs e' he') hsz hctl _ hT1 rfl hq hn rfl e' he'
                (hjb e' he') (by rw [hjb e' he']; exact hv') (fun e'' he'' => (hnm' e'' he'').1)
                habs1 _)
            simpa [show UInt64.ofNat 1 = (1 : Word) from rfl, withScrLits, tierS_eq,
              Tbl.size] using this
          · rw [hres, hcw, litS_eq, decE_lit 1 _ (by decide), tierS_eq]; try rfl
        · simp [hok1] at hI
    · have hf : rdW (m.arr64 CTL) 1 = 0 := by
        by_cases h : rdW (m.arr64 CTL) 1 = 0
        · exact h
        · exact absurd (hflag.mp h) hsc
      simp only [hf, not_true_eq_false, ↓reduceIte] at hI
      have hsc' : a.store.scratchOn = false := by simpa using hsc
      simp only [hsc', Bool.false_eq_true, ↓reduceIte] at hrun
      by_cases hok0 : pushOK m 0 = true
      · simp only [hok0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hI
        obtain ⟨rfl, rfl⟩ := hI
        have ⟨hC, hsz⟩ := pushOK_nat m 0 hok0 hrs
        have hc := hT0.1
        simp only [show UInt64.ofNat 0 = (0 : Word) from rfl] at hc
        have hcap : a.store.pers.lits.size < Idx.idxCap := by
          simp only [Tbl.size, Idx.idxCap]; omega
        simp only [hcap, ↓reduceIte] at hrun
        obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
        have hcw : cnt m 0 = UInt64.ofNat a.store.pers.lits.nodes.size := by
          rw [← hc, UInt64.ofNat_toNat]
        refine ⟨hok, ?_, ?_⟩
        · rw [hst]
          have := LitR.push m a (withPersLits a (a.store.pers.lits.push
            (litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)))
            (a.store.derOfView (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))))
            (Idx.mk ETag.lit Idx.tierP (UInt32.ofNat a.store.pers.lits.size)))) 0 (by decide)
            o l (hashN (m.arr64 POOL) o.toNat l.toNat)
            (UInt64.ofNat (((homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlots m)).toNat + e)
              % ns m)) hR rfl
            (tier_push m 0 (by decide) _ _ _ _ _ hC (by rw [hjb e he]; have := hjlt e he; omega)
              (by rw [hjb e he]; have := hjs e he; omega) hsz hctl _ hT0 rfl hq hn rfl e he
              (hjb e he) (by rw [hjb e he]; exact hv) (fun e'' he'' => (hnm e'' he'').1)
              habs0 _)
            (tier_other m 0 (by decide) _ _ _ _ _ hC (by rw [hjb e he]; have := hjlt e he; omega)
              (by rw [hjb e he]; have := hjs e he; omega) hsz hctl 1 (by decide) (by decide) _ hT1)
          simpa [show UInt64.ofNat 0 = (0 : Word) from rfl, withPersLits, tierP_eq,
            Tbl.size] using this
        · rw [hres, hcw, litP_eq, decE_lit 0 _ (by decide), tierP_eq]; try rfl
      · simp [hok0] at hI

end intern

/-! ## `natAddLit_refines` without hypotheses -/

/-- `intern_lit` refines `internE (.lit (.natVal _))` under `LitR`: the spec
`natAddLit_refines` assumes as `hI`. -/
theorem internLit_refines (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match" = some litMatch)
    (hpf : p.lookup "lit_find" = some litFind) (hpp : p.lookup "lit_push" = some litPush)
    (hp : p.lookup "intern_lit" = some internLit)
    (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word) (hR : LitR s₀.mem a₀) (hq : SliceOK s₀.mem o l)
    (hn : Norm (s₀.mem.arr64 POOL) o.toNat l.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ ∧
      LitR s'.mem (AM.st (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ =
        decE (r.headD 0); ⊤⦄ := by
  have ⟨_, _, hps, htop⟩ := hR.1
  have hspec := internLit_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  exact ⟨hloc, intern_correct s.mem a₀ hR o l hq hn _ _ hI⟩

/-- The arena functions and the store functions, as one program. -/
def storeProg : Prog := natProg ++ [("nat_add_lit", natAddLit)] ++ litProg

/- `5 + 7` twice and `12` (`7 + 5`): one node, handle `0x80000000`; `5 + 5` is the second. -/
#guard
  let m : Mem := { words := #[#[5, 7, 0, 0, 0, 0, 0, 0, 0, 0], #[2, 0, 0, 0],
    Array.replicate 64 0, Array.replicate 32 0] }
  let go (m : Mem) (a b : Word) : Option (Word × Mem) :=
    match run storeProg 100 "nat_add_lit" [a, 1, b, 1] m with
    | .ok (r, m') => some (r.headD 0, m')
    | .error _ => none
  match go m 0 1 with
  | some (h₁, m) => match go m 0 1 with
    | some (h₂, m) => match go m 1 0 with
      | some (h₃, m) => match go m 0 0 with
        | some (h₄, _) => [h₁, h₂, h₃, h₄] == [0x80000000, 0x80000000, 0x80000000, 0x80000001]
        | none => false
      | none => false
    | none => false
  | none => false

/-- **`nat_add_lit` refines `natOpResult`'s `Nat.add` arm**, with the state relation `LitR`
and nothing assumed: `natAddLit_refines` instantiated at `storeProg`. -/
theorem natAddLit_refines_store (n : Nat) (s₀ : St) (a₀ : AState) (hR : LitR s₀.mem a₀)
    (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke storeProg (exec storeProg n) "nat_add_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀ ∧
      LitR s'.mem (AM.st (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀) ∧
      AM.res (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄ :=
  natAddLit_refines storeProg rfl rfl rfl rfl rfl LitR (fun _ _ h => h.1) LitR.grow
    (internLit_refines storeProg rfl rfl rfl rfl rfl rfl) n s₀ a₀ hR oa la ob lb ha hb

/-- From an L run of `nat_add_lit` to the arena run of the `Nat.add` arm, under `LitR`. -/
theorem natAddLit_run_store (fuel : Nat) (m : Mem) (a₀ : AState) (hR : LitR m a₀)
    (oa la ob lb : Word) (ha : SliceOK m oa la) (hb : SliceOK m ob lb) (r : List Word) (m' : Mem)
    (h : run storeProg fuel "nat_add_lit" [oa, la, ob, lb] m = .ok (r, m')) :
    ∃ a', (natAddArm (pv (m.arr64 POOL) oa.toNat la.toNat) (pv (m.arr64 POOL) ob.toNat lb.toNat)).run
      a₀ = .ok (some (decE (r.headD 0)), a') ∧ LitR m' a' :=
  natAddLit_run storeProg rfl rfl rfl rfl rfl LitR (fun _ _ h => h.1) LitR.grow
    (internLit_refines storeProg rfl rfl rfl rfl rfl rfl) fuel m a₀ hR oa la ob lb ha hb r m' h

end L.Arena
