import ConAgua.Arena.StoreRel

/-!
# The `lit` store refines the arena's `lit` tables; `natAddLit_refines` without hypotheses

`ConAgua/Arena/Store.lean` has the L code of the `lit` node store and its specs against
word-level models (`probeW`, `matchW`, `internW`). This file relates them to con-ron's arena:

* **`LitR m a`**, the state relation (`natAddLit_refines`'s `R`): the pool is well formed, the
  scratch flag `CTL[1]` is `a.store.scratchOn`, and each tier `t` of the L store represents the
  arena's `lit` table of that tier (`TierRel`): node `i` (a word) holds `tb.nodes[i]`
  (`RecRel`: a `natVal` is a normalised slice below the pool top, with its hash), the cons
  table maps each node's key to its handle `hdW 8 t i` and points only at nodes with its key, and
  the L slots satisfy the linear-probing invariant (`SlotsOK`). Everything is stated over the
  words the L code reads (`rdW (m.arr64 REC) (i * 8 + t * 4 + 3)`, `walkW`), so the L models and
  the relation share their terms and no index conversion is needed.
* **The memory after `lit_push`**: one equation per array (`pm_rec`, `pm_slot`, `pm_ctl`,
  `pm_pool`), from the generic `rdW_set64`.
* **The probe** (`probe_ok`): a named predicate `ProbeOK` on the result, no `∃`/`∨`.
* **The table lemmas**: a hit is the arena's cons hit (`tier_hit`), a miss means absence
  (`tier_miss`), the append represents `Tbl.push` (`tier_push`, `tier_other`).
* **The arena side**: one guarded run equation per path of `internE (.lit l)`.
* **`intern_correct`**: `internW` refines `internE (.lit (.natVal _))`, one `grind` per path.
* **`LitR.grow`**, `natAddLit_refines_store`, `natAddLit_run_store`.

Proofs are `grind [store_grind, …]` per clause, with the case splits of the data (which tier,
which node) and the instantiations of the relation's `∀` clauses made by hand where `grind`
would otherwise instantiate them on every term. The pool facts (normalised slices are unique)
are by hand.

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
    have e1 : (a + i).toNat = a.toNat + i.toNat := by grind
    have e2 : (b + i).toNat = b.toNat + i.toNat := by grind
    rw [e1, e2] at he
    constructor
    · intro H k hk hkl
      by_cases hk' : k = i.toNat
      · subst hk'; exact he
      · exact H k (by grind) hkl
    · grind
  | case2 i hi he =>
    have e1 : (a + i).toNat = a.toNat + i.toNat := by grind
    have e2 : (b + i).toNat = b.toNat + i.toNat := by grind
    rw [e1, e2] at he
    simp only [Bool.false_eq_true, false_iff]
    exact fun H => he (H _ (Nat.le_refl _) (by grind))
  | case3 i hi => grind


attribute [store_grind] cnt nSlots

/-! ## The probe run -/

/-- The home slot of a hash among the slots of `m`. -/
abbrev homeM (m : Mem) (h : Word) : Word := homeW h (nSlots m)

/-- The first `d` slots of the run from `x` hold nodes that do not match. -/
def NoMatch (m : Mem) (t o l h x : Word) (d : Nat) : Prop :=
  ∀ e < d, rdW (m.arr64 SLOT) ((walkW (nSlots m) x e) * 2 + t) ≠ 0 ∧
    matchW (m.arr64 REC) (m.arr64 POOL) t (rdW (m.arr64 SLOT) ((walkW (nSlots m) x e) * 2 + t) - 1) o l h = false

/-- What a result `rs` of the probe of tier `t` from slot `x` says: a hit (`rs[0] ≠ 0`) is a
matching node `rs[1]` in an occupied slot `rs[2]`; a miss is the free slot `rs[2]`, step `rs[3]` of
the run, after nodes that do not match. -/
def ProbeOK (m : Mem) (t o l h x : Word) (rs : List Word) : Prop :=
  rs ≠ [] →
    (rs.headD 0 ≠ 0 → matchW (m.arr64 REC) (m.arr64 POOL) t (rs.tail.headD 0) o l h = true ∧
      rdW (m.arr64 SLOT) ((rs.tail.tail.headD 0) * 2 + t) = rs.tail.headD 0 + 1 ∧
      rdW (m.arr64 SLOT) ((rs.tail.tail.headD 0) * 2 + t) ≠ 0 ∧ rs.tail.tail.headD 0 < nSlots m) ∧
    (rs.headD 0 = 0 → rs.tail.tail.headD 0 = walkW (nSlots m) x (rs.tail.tail.tail.headD 0).toNat ∧
      rdW (m.arr64 SLOT) ((rs.tail.tail.headD 0) * 2 + t) = 0 ∧
      NoMatch m t o l h x (rs.tail.tail.tail.headD 0).toNat)

theorem probe_ok (m : Mem) (t o l h x : Word) (hx : x < nSlots m) :
    ∀ (k : Nat) (d : Word), (nSlots m).toNat - d.toNat = k → NoMatch m t o l h x d.toNat →
      ProbeOK m t o l h x (probeW (m.arr64 SLOT) (m.arr64 REC) (m.arr64 POOL) t o l h (nSlots m)
        (walkW (nSlots m) x d.toNat) d) := by
  intro k
  induction k with
  | zero => intro d hk _; rw [probeW]; grind [ProbeOK]
  | succ k ih =>
    intro d hk hnm
    have := ih (d + 1)
    clear ih
    have hd : d < nSlots m := by grind
    have hd1 : (d + 1).toNat = d.toNat + 1 := by grind
    specialize this (by grind)
    rw [hd1, walkW_succ] at this
    rw [probeW]
    by_cases h0 : rdW (m.arr64 SLOT) ((walkW (nSlots m) x d.toNat) * 2 + t) = 0
    · simp only [hd, h0, ↓reduceIte]; grind [ProbeOK]
    by_cases hm : matchW (m.arr64 REC) (m.arr64 POOL) t (rdW (m.arr64 SLOT) ((walkW (nSlots m) x d.toNat) * 2 + t) - 1)
        o l h
    · simp only [hd, h0, hm, ↓reduceIte]; grind [store_grind, ProbeOK]
    · simp only [hd, h0, hm, ↓reduceIte, Bool.false_eq_true]
      exact this (by grind [NoMatch])

/-- The probe `lit_find` makes, from the home slot. -/
theorem probe_home (m : Mem) (t o l h : Word) :
    ProbeOK m t o l h (homeM m h) (probeW (m.arr64 SLOT) (m.arr64 REC) (m.arr64 POOL) t o l h
      (nSlots m) (homeM m h) 0) := by
  by_cases hn : nSlots m = 0
  · rw [probeW]; simp [hn, ProbeOK]
  · exact probe_ok m t o l h _ (homeW_lt _ _ (by grind)) _ 0 rfl (by simp [NoMatch])

/-! ## Normalised slices, in words -/

/-- Two normalised slices with the same value: the same length, `limbs_eq` holds, the same hash. -/
theorem slice_eq (p : Array Word) (a la b lb : Word) (ha : Norm p a.toNat la.toNat)
    (hb : Norm p b.toNat lb.toNat) (hab : a.toNat + la.toNat < 2 ^ 64)
    (hbb : b.toNat + lb.toNat < 2 ^ 64) (h : pv p a.toNat la.toNat = pv p b.toNat lb.toNat) :
    la = lb ∧ eqW p a b la 0 = true ∧ hashN p a.toNat la.toNat = hashN p b.toNat lb.toNat := by
  have hl := UInt64.toNat_inj.mp (pv_len p p _ _ _ _ ha hb h)
  subst hl
  have hlimbs := pv_limbs p p _ _ _ h
  exact ⟨rfl, (eqW_iff p a b la 0 hab hbb).mpr (fun k _ hk => hlimbs k hk),
    hashN_congr p p _ _ _ hlimbs⟩

/-- Equal limbs, equal values. -/
theorem pv_of_eqW (p : Array Word) (a b l : Word) (hab : a.toNat + l.toNat < 2 ^ 64)
    (hbb : b.toNat + l.toNat < 2 ^ 64) (h : eqW p a b l 0 = true) :
    pv p a.toNat l.toNat = pv p b.toNat l.toNat :=
  pv_congr p p _ _ _ (fun k hk => (eqW_iff p a b l 0 hab hbb).mp h k (Nat.zero_le _) hk)

/-! ## The relation between L memory and the arena's `lit` tables -/

/-- Node `i` of tier `t` holds the `natVal` `N`: kind `0`, a normalised slice below the top with
value `N`, and its hash. -/
def NatRec (m : Mem) (t i : Word) (N : Nat) : Prop :=
  rdW (m.arr64 REC) (i * 8 + t * 4) = 0 ∧
  (rdW (m.arr64 REC) (i * 8 + t * 4 + 1)).toNat + (rdW (m.arr64 REC) (i * 8 + t * 4 + 2)).toNat ≤
    m.top.toNat ∧
  Norm (m.arr64 POOL) (rdW (m.arr64 REC) (i * 8 + t * 4 + 1)).toNat
    (rdW (m.arr64 REC) (i * 8 + t * 4 + 2)).toNat ∧
  pv (m.arr64 POOL) (rdW (m.arr64 REC) (i * 8 + t * 4 + 1)).toNat
    (rdW (m.arr64 REC) (i * 8 + t * 4 + 2)).toNat = N ∧
  rdW (m.arr64 REC) (i * 8 + t * 4 + 3) = hashN (m.arr64 POOL)
    (rdW (m.arr64 REC) (i * 8 + t * 4 + 1)).toNat (rdW (m.arr64 REC) (i * 8 + t * 4 + 2)).toNat

/-- Node `i` of tier `t` holds the literal `k`; a `strVal` is kind `1`, its contents are not
represented yet. -/
def RecRel (m : Mem) (t i : Word) : LitNode → Prop
  | ⟨.natVal N⟩ => NatRec m t i N
  | ⟨.strVal _⟩ => rdW (m.arr64 REC) (i * 8 + t * 4) = 1

@[store_grind =] theorem RecRel_natVal (m : Mem) (t i : Word) (N : Nat) :
    RecRel m t i ⟨.natVal N⟩ = NatRec m t i N := rfl
@[store_grind =] theorem RecRel_strVal (m : Mem) (t i : Word) (s : String) :
    RecRel m t i ⟨.strVal s⟩ = (rdW (m.arr64 REC) (i * 8 + t * 4) = 1) := rfl

/-- The slots of tier `t` index its `c` nodes, and node `i` lies on the run from its home slot,
after occupied slots (the invariant of linear probing without deletion). -/
def SlotsOK (m : Mem) (t : Word) (c : Nat) : Prop :=
  (∀ j : Word, j < nSlots m → (rdW (m.arr64 SLOT) (j * 2 + t)).toNat ≤ c) ∧
  ∀ i : Word, i.toNat < c → ∃ d : Nat,
    rdW (m.arr64 SLOT) (walkW (nSlots m) (homeM m (rdW (m.arr64 REC) (i * 8 + t * 4 + 3))) d * 2 + t)
      = i + 1 ∧
    ∀ e < d, rdW (m.arr64 SLOT)
      (walkW (nSlots m) (homeM m (rdW (m.arr64 REC) (i * 8 + t * 4 + 3))) e * 2 + t) ≠ 0

/-- Tier `t` of the L store represents the arena table `tb`: the same nodes in the same order (so
the same handles), and a cons table with the same key → handle map (each node's key maps to its
handle, each entry points to a node with its key). The layout of `tb.cons` is never mentioned. -/
def TierRel (m : Mem) (t : Word) (tb : Tbl LitNode EIdx UInt64) : Prop :=
  (cnt m t).toNat = tb.nodes.size ∧ tb.nodes.size ≤ 134217728 ∧
  8 * tb.nodes.size ≤ (m.arr64 REC).size ∧
  (∀ (i : Word) k, tb.nodes[i.toNat]? = some k → RecRel m t i k) ∧
  (∀ (i : Word) k, tb.nodes[i.toNat]? = some k → tb.cons[k]? = some (decE (hdW 8 t i))) ∧
  (∀ k x, tb.cons[k]? = some x → tb.nodes[(hix x).toNat]? = some k) ∧
  SlotsOK m t tb.nodes.size

/-- **The state relation.** The pool is well formed, the scratch flag is the arena's, and both
tiers of the `lit` store represent the arena's `lit` tables. -/
def LitR (m : Mem) (a : AState) : Prop :=
  PoolOK m ∧ 4 ≤ (m.arr64 CTL).size ∧ (m.arr64 REC).size < 2 ^ 63 ∧
  (m.arr64 SLOT).size < 2 ^ 63 ∧ (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn ∧
  TierRel m 0 a.store.pers.lits ∧ TierRel m 1 a.store.scr.lits

/-! ## The memory after `lit_push` -/

section push
variable (m : Mem) (t o l h J c : Word)

@[store_grind =] theorem pm_pool : (pushMem m t o l h J c).arr64 POOL = m.arr64 POOL := by
  grind [pushMem, Mem.arr64_set64_ne]

@[store_grind =] theorem pm_size (a : ArrId) :
    ((pushMem m t o l h J c).arr64 a).size = (m.arr64 a).size := by
  grind [pushMem, size_set64]

@[store_grind =] theorem pm_words :
    (pushMem m t o l h J c).words.size = m.words.size := by
  grind [pushMem, Mem.words_size_set64]

@[store_grind =] theorem pm_ctl (x : Word) :
    rdW ((pushMem m t o l h J c).arr64 CTL) x =
      if x = 2 + t ∧ (2 + t).toNat < (m.arr64 CTL).size then c + 1 else rdW (m.arr64 CTL) x := by
  grind [pushMem, rdW_set64, size_set64]

@[store_grind =] theorem pm_slot (x : Word) :
    rdW ((pushMem m t o l h J c).arr64 SLOT) x =
      if x = J * 2 + t ∧ (J * 2 + t).toNat < (m.arr64 SLOT).size then c + 1
      else rdW (m.arr64 SLOT) x := by
  grind [pushMem, rdW_set64, size_set64]

@[store_grind =] theorem pm_rec (x : Word) (hc : (c * 8 + t * 4 + 3).toNat < (m.arr64 REC).size)
    (hw : (c * 8 + t * 4).toNat + 3 < 2 ^ 64) :
    rdW ((pushMem m t o l h J c).arr64 REC) x =
      if x = c * 8 + t * 4 then 0 else if x = c * 8 + t * 4 + 1 then o
      else if x = c * 8 + t * 4 + 2 then l else if x = c * 8 + t * 4 + 3 then h
      else rdW (m.arr64 REC) x := by
  grind [pushMem, rdW_set64, size_set64]

end push

/-- A node's relation depends only on its four words, the pool and the top. -/
theorem RecRel_frame (m m' : Mem) (t i : Word) (k : LitNode)
    (h0 : rdW (m'.arr64 REC) (i * 8 + t * 4) = rdW (m.arr64 REC) (i * 8 + t * 4))
    (h1 : rdW (m'.arr64 REC) (i * 8 + t * 4 + 1) = rdW (m.arr64 REC) (i * 8 + t * 4 + 1))
    (h2 : rdW (m'.arr64 REC) (i * 8 + t * 4 + 2) = rdW (m.arr64 REC) (i * 8 + t * 4 + 2))
    (h3 : rdW (m'.arr64 REC) (i * 8 + t * 4 + 3) = rdW (m.arr64 REC) (i * 8 + t * 4 + 3))
    (hp : m'.arr64 POOL = m.arr64 POOL) (htop : m'.top = m.top) :
    RecRel m' t i k = RecRel m t i k := by
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k <;> simp only [RecRel, NatRec, h0, h1, h2, h3, hp, htop]

/-! ## Hit and miss -/

section tier
variable (m : Mem) (t : Word) (ht : t ≤ 1) (tb : Tbl LitNode EIdx UInt64) (hT : TierRel m t tb)
  (hpool : PoolOK m) (o l : Word) (hq : SliceOK m o l) (hn : Norm (m.arr64 POOL) o.toNat l.toNat)

include hT hpool hq hn in
/-- **Matching is equality of literals**, on a node of a represented tier. -/
theorem matchW_iff (i : Word) (k : LitNode) (hk : tb.nodes[i.toNat]? = some k) :
    matchW (m.arr64 REC) (m.arr64 POOL) t i o l (hashN (m.arr64 POOL) o.toNat l.toNat) = true ↔
      k = litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)) := by
  have hr := hT.2.2.2.1 i k hk
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · have := slice_eq (m.arr64 POOL) (rdW (m.arr64 REC) (i * 8 + t * 4 + 1))
      (rdW (m.arr64 REC) (i * 8 + t * 4 + 2)) o l
    have := pv_of_eqW (m.arr64 POOL) (rdW (m.arr64 REC) (i * 8 + t * 4 + 1)) o l
    grind [matchW, NatRec, RecRel_natVal, PoolOK, SliceOK]
  · grind [matchW, RecRel_strVal]

include hT hpool hq hn in
/-- A probe hit is the arena's cons hit, at the same handle. -/
theorem tier_hit (x : Word) (rs : List Word)
    (hP : ProbeOK m t o l (hashN (m.arr64 POOL) o.toNat l.toNat) x rs) (hr : rs ≠ [])
    (hf : rs.headD 0 ≠ 0) :
    tb.cons[litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))]? =
      some (decE (hdW 8 t (rs.tail.headD 0))) := by
  have := matchW_iff m t tb hT hpool o l hq hn (rs.tail.headD 0)
  obtain ⟨-, -, -, -, hsome, -, ⟨hsl, -⟩⟩ := hT
  have := hsl (rs.tail.tail.headD 0)
  have := hsome (rs.tail.headD 0)
  clear hsl hsome
  grind [ProbeOK]

include hT hpool hq hn in
/-- A probe miss from the home slot: the literal is not in the tier. -/
theorem tier_miss (rs : List Word)
    (hP : ProbeOK m t o l (hashN (m.arr64 POOL) o.toNat l.toNat)
      (homeM m (hashN (m.arr64 POOL) o.toNat l.toNat)) rs) (hr : rs ≠ []) (hf : rs.headD 0 = 0) :
    tb.cons[litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))]? = none := by
  cases hc : tb.cons[litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))]? with
  | none => rfl
  | some x =>
    exfalso
    have := matchW_iff m t tb hT hpool o l hq hn (hix x)
    grind [ProbeOK, TierRel, SlotsOK, NoMatch, matchW]

include ht hT hpool hq hn in
/-- `lit_push` at the free slot the probe from the home slot stopped at represents the arena's
append of the queried literal. -/
theorem tier_push (rs : List Word)
    (hP : ProbeOK m t o l (hashN (m.arr64 POOL) o.toNat l.toNat)
      (homeM m (hashN (m.arr64 POOL) o.toNat l.toNat)) rs) (hr : rs ≠ []) (hf : rs.headD 0 = 0)
    (hok : pushOK m t = true) (hctl : 4 ≤ (m.arr64 CTL).size) (dd : UInt64) :
    TierRel (pushMem m t o l (hashN (m.arr64 POOL) o.toNat l.toNat) (rs.tail.tail.headD 0) (cnt m t)) t
      (tb.push (litKey (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))) dd (decE (hdW 8 t (cnt m t)))) := by
  have hmiss := tier_miss m t tb hT hpool o l hq hn rs hP hr hf
  obtain ⟨hc, hcap, hrs, hrec, hsome, hback, hsl, hrun⟩ := hT
  simp only [TierRel, SlotsOK, Tbl.push_nodes, Tbl.push_cons, Array.size_push]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · clear hrec hsome hback hsl hrun; grind [store_grind, pushOK]
  · clear hrec hsome hback hsl hrun; grind [store_grind, pushOK]
  · clear hrec hsome hback hsl hrun; grind [store_grind, pushOK]
  · intro i k hk
    rw [Array.getElem?_push] at hk
    split at hk
    · cases hk
      have : i = cnt m t := UInt64.toNat_inj.mp (by omega)
      subst this
      have hb : (cnt m t * 8 + t * 4 + 3).toNat < (m.arr64 REC).size ∧
          (cnt m t * 8 + t * 4).toNat + 3 < 2 ^ 64 := by
        clear hrec hsome hback hsl hrun; grind [store_grind, pushOK]
      simp only [litKey, RecRel_natVal, NatRec, pm_rec _ _ _ _ _ _ _ _ hb.1 hb.2, pm_pool]
      clear hrec hsome hback hsl hrun
      grind [store_grind, pushOK, PoolOK, SliceOK]
    · have := hrec i k hk
      rw [RecRel_frame _ _ t i k]
      · exact this
      all_goals clear hrec hsome hback hsl hrun; grind [store_grind, pushOK, PoolOK, SliceOK]
  · intro i k hk
    clear hrec hback hsl hrun
    grind [store_grind, pushOK]
  · intro k x hk
    clear hrec hsome hsl hrun
    grind [store_grind, pushOK]
  · intro j hj
    clear hrec hsome hback hrun
    grind [store_grind, pushOK, ProbeOK]
  · intro i hi
    clear hsome hback hsl
    by_cases hic : i = cnt m t
    · subst hic
      refine ⟨(rs.tail.tail.tail.headD 0).toNat, ?_, ?_⟩
      · grind [store_grind, pushOK, ProbeOK]
      · grind [store_grind, pushOK, ProbeOK, NoMatch]
    · obtain ⟨d, hd1, hd2⟩ := hrun i (by grind)
      have := hrec i
      refine ⟨d, ?_, ?_⟩
      · grind [store_grind, pushOK, ProbeOK]
      · grind [store_grind, pushOK, ProbeOK]

end tier

/-- Appending to tier `t` leaves the other tier represented. -/
theorem tier_other (m : Mem) (t t' o l h J : Word) (ht : t ≤ 1) (ht' : t' ≤ 1) (hne : t' ≠ t)
    (tb : Tbl LitNode EIdx UInt64) (hT : TierRel m t' tb) (hok : pushOK m t = true) :
    TierRel (pushMem m t o l h J (cnt m t)) t' tb := by
  obtain ⟨hc, hcap, hrs, hrec, hsome, hback, hsl, hrun⟩ := hT
  refine ⟨?_, hcap, ?_, ?_, hsome, hback, ?_, ?_⟩
  · clear hrec hsome hback hsl hrun; grind [store_grind, pushOK]
  · clear hrec hsome hback hsl hrun; grind [store_grind, pushOK]
  · intro i k hk
    have := hrec i k hk
    rw [RecRel_frame _ _ t' i k]
    · exact this
    all_goals clear hrec hsome hback hsl hrun; grind [store_grind, pushOK]
  · intro j hj
    clear hrec hsome hback hrun
    grind [store_grind, pushOK]
  · intro i hi
    obtain ⟨d, hd1, hd2⟩ := hrun i (by grind)
    have := hrec i
    clear hsome hback hsl hrun
    refine ⟨d, ?_, ?_⟩
    · grind [store_grind, pushOK]
    · grind [store_grind, pushOK]

/-! ## The arena side, one equation per path -/

section arena
variable (l : ConLeche.Literal) (a : AState) (x : EIdx)

theorem internE_lit_hitP (h0 : a.store.pers.lits.cons[litKey l]? = some x) :
    (internE (.lit l)).run a = .ok (x, a) := by
  rw [internE_lit_run]; simp [h0]

theorem internE_lit_hitS (h0 : a.store.pers.lits.cons[litKey l]? = none)
    (hs : a.store.scratchOn = true) (h1 : a.store.scr.lits.cons[litKey l]? = some x) :
    (internE (.lit l)).run a = .ok (x, a) := by
  rw [internE_lit_run]; simp [h0, hs, h1]

theorem internE_lit_pushS (h0 : a.store.pers.lits.cons[litKey l]? = none)
    (hs : a.store.scratchOn = true) (h1 : a.store.scr.lits.cons[litKey l]? = none)
    (hc : a.store.scr.lits.nodes.size < 134217728) :
    (internE (.lit l)).run a = .ok (decE (hdW 8 1 (UInt64.ofNat a.store.scr.lits.nodes.size)),
      withScrLits a (a.store.scr.lits.push (litKey l) (a.store.derOfView (.lit l))
        (decE (hdW 8 1 (UInt64.ofNat a.store.scr.lits.nodes.size))))) := by
  rw [internE_lit_run, show Idx.tierS = UInt32.ofNat 1 from rfl, mk_eq]
  simp [h0, hs, h1, Tbl.size, Idx.idxCap, hc, ETag.lit]

theorem internE_lit_pushP (h0 : a.store.pers.lits.cons[litKey l]? = none)
    (hs : a.store.scratchOn = false) (hc : a.store.pers.lits.nodes.size < 134217728) :
    (internE (.lit l)).run a = .ok (decE (hdW 8 0 (UInt64.ofNat a.store.pers.lits.nodes.size)),
      withPersLits a (a.store.pers.lits.push (litKey l) (a.store.derOfView (.lit l))
        (decE (hdW 8 0 (UInt64.ofNat a.store.pers.lits.nodes.size))))) := by
  rw [internE_lit_run, show Idx.tierP = UInt32.ofNat 0 from rfl, mk_eq]
  simp [h0, hs, Tbl.size, Idx.idxCap, hc, ETag.lit]

end arena

section with_
variable (a : AState) (t : Tbl LitNode EIdx UInt64)
@[store_grind =] theorem withScrLits_scr : (withScrLits a t).store.scr.lits = t := rfl
@[store_grind =] theorem withScrLits_pers : (withScrLits a t).store.pers.lits = a.store.pers.lits := rfl
@[store_grind =] theorem withScrLits_on : (withScrLits a t).store.scratchOn = a.store.scratchOn := rfl
@[store_grind =] theorem withPersLits_pers : (withPersLits a t).store.pers.lits = t := rfl
@[store_grind =] theorem withPersLits_scr : (withPersLits a t).store.scr.lits = a.store.scr.lits := rfl
@[store_grind =] theorem withPersLits_on :
    (withPersLits a t).store.scratchOn = a.store.scratchOn := rfl
end with_

/-- The memory after `lit_push` relates to the arena's state after its append. -/
theorem LitR_push (m : Mem) (a a' : AState) (t o l h J : Word) (ht : t ≤ 1) (hR : LitR m a)
    (hflag : a'.store.scratchOn = a.store.scratchOn)
    (h0 : TierRel (pushMem m t o l h J (cnt m t)) 0 a'.store.pers.lits)
    (h1 : TierRel (pushMem m t o l h J (cnt m t)) 1 a'.store.scr.lits) :
    LitR (pushMem m t o l h J (cnt m t)) a' := by
  obtain ⟨hpool, hctl, hrs, hss, hfl, -, -⟩ := hR
  refine ⟨?_, ?_, ?_, ?_, ?_, h0, h1⟩ <;> grind [store_grind, PoolOK]

/-! ## `intern_lit` refines `internE (.lit (.natVal _))` -/

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
  have hP0 := probe_home m 0 o l (hashN (m.arr64 POOL) o.toNat l.toNat)
  have hP1 := probe_home m 1 o l (hashN (m.arr64 POOL) o.toNat l.toNat)
  have hit0 := tier_hit m 0 _ hT0 hpool o l hq hn _ _ hP0
  have hit1 := tier_hit m 1 _ hT1 hpool o l hq hn _ _ hP1
  have miss0 := tier_miss m 0 _ hT0 hpool o l hq hn _ hP0
  have miss1 := tier_miss m 1 _ hT1 hpool o l hq hn _ hP1
  simp only [internW] at hI
  split at hI
  · simp at hI
  split at hI
  · -- persistent hit
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (internE_lit_hitP _ a _ (hit0 ‹_› ‹_›))
    grind [litP, hdW]
  have hm0 := miss0 ‹_› (by grind)
  split at hI
  · split at hI
    · simp at hI
    split at hI
    · -- scratch hit
      obtain ⟨hok, hst, hres⟩ :=
        AM.of_run_ok _ _ _ _ (internE_lit_hitS _ a _ hm0 (by grind) (hit1 ‹_› ‹_›))
      grind [litS, hdW]
    split at hI
    · -- scratch append
      have hsz : a.store.scr.lits.nodes.size < 134217728 := by grind [pushOK, TierRel]
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
        (internE_lit_pushS _ a hm0 (by grind) (miss1 ‹_› (by grind)) hsz)
      have e : UInt64.ofNat a.store.scr.lits.nodes.size = cnt m 1 := by grind [TierRel]
      rw [e] at hst hres
      have hp1 := tier_push m 1 (by decide) _ hT1 hpool o l hq hn _ hP1 ‹_› (by grind) ‹_› hctl
        (a.store.derOfView (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))))
      simp only [Option.some.injEq, Prod.mk.injEq] at hI
      obtain ⟨rfl, rfl⟩ := hI
      rw [hst, hres]
      refine ⟨hok, LitR_push m a _ 1 o l _ _ (by decide) hR rfl ?_ hp1, by grind [litS, hdW]⟩
      exact tier_other m 1 0 o l _ _ (by decide) (by decide) (by decide) _ hT0 ‹_›
    · simp at hI
  split at hI
  · -- persistent append
    have hsz : a.store.pers.lits.nodes.size < 134217728 := by grind [pushOK, TierRel]
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
      (internE_lit_pushP _ a hm0 (by grind) hsz)
    have e : UInt64.ofNat a.store.pers.lits.nodes.size = cnt m 0 := by grind [TierRel]
    rw [e] at hst hres
    have hp0 := tier_push m 0 (by decide) _ hT0 hpool o l hq hn _ hP0 ‹_› (by grind) ‹_› hctl
      (a.store.derOfView (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))))
    simp only [Option.some.injEq, Prod.mk.injEq] at hI
    obtain ⟨rfl, rfl⟩ := hI
    rw [hst, hres]
    refine ⟨hok, LitR_push m a _ 0 o l _ _ (by decide) hR rfl hp0 ?_, by grind [litP, hdW]⟩
    exact tier_other m 0 1 o l _ _ (by decide) (by decide) (by decide) _ hT1 ‹_›
  · simp at hI

end intern
/-! ## Appending to the pool preserves the relation -/

section grow
variable (m m' : Mem) (hg : Grows m m')

include hg in
theorem grow_arr (b : ArrId) (hb : b ≠ POOL) (hc : b ≠ CTL) : m'.arr64 b = m.arr64 b := by
  rw [Frame.arr64 _ _ _ _ hg.1 hb, Mem.arr64_set64_ne _ _ _ _ _ hc]

include hg in
theorem grow_ctl (x : Word) (hx : x ≠ 0) : rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x := by
  rw [Frame.arr64 _ _ _ _ hg.1 (by decide), rdW_set64]; simp [Ne.symm hx]

include hg in
theorem RecRel_grow (t i : Word) (k : LitNode) (h : RecRel m t i k) : RecRel m' t i k := by
  have hr := grow_arr m m' hg REC (by decide) (by decide)
  obtain ⟨hfr, hag, ht1, ht2, hps'⟩ := hg
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · simp only [RecRel, NatRec, hr] at h ⊢
    obtain ⟨h0, hsl, hnm, hpv, hh⟩ := h
    exact ⟨h0, by omega, Agree.norm _ _ _ _ _ hag hsl hnm, by rw [Agree.pv _ _ _ _ _ hag hsl, hpv],
      by rw [Agree.hashN _ _ _ _ _ hag hsl, hh]⟩
  · simpa only [RecRel, hr] using h

include hg in
theorem TierRel_grow (t : Word) (ht : t ≤ 1) (tb : Tbl LitNode EIdx UInt64) (hT : TierRel m t tb) :
    TierRel m' t tb := by
  have hr := grow_arr m m' hg REC (by decide) (by decide)
  have hs := grow_arr m m' hg SLOT (by decide) (by decide)
  have hc := grow_ctl m m' hg (2 + t) (by grind)
  obtain ⟨hc', hcap, hrs, hrec, hsome, hback, hsl, hrun⟩ := hT
  refine ⟨by grind [cnt], hcap, by grind, fun i k hk => RecRel_grow m m' hg t i k (hrec i k hk),
    hsome, hback, ?_, ?_⟩
  · intro j hj; grind [nSlots, len64_eq]
  · intro i hi; obtain ⟨d, h1, h2⟩ := hrun i hi; exact ⟨d, by grind [nSlots, len64_eq],
      by grind [nSlots, len64_eq]⟩

include hg in
/-- **Appending to the pool preserves the relation** (`natAddLit_refines`'s `hgrow`). -/
theorem LitR.grow (a : AState) (hR : LitR m a) : LitR m' a := by
  obtain ⟨hpool, hctl, hrs, hss, hfl, hT0, hT1⟩ := hR
  have hr := grow_arr m m' hg REC (by decide) (by decide)
  have hs := grow_arr m m' hg SLOT (by decide) (by decide)
  have hf := grow_ctl m m' hg 1 (by decide)
  have := Frame.size _ _ _ hg.1
  have := Frame.arr64 POOL CTL _ _ hg.1 (by decide)
  refine ⟨?_, ?_, by grind, by grind, by grind, TierRel_grow m m' hg 0 (by decide) _ hT0,
    TierRel_grow m m' hg 1 (by decide) _ hT1⟩
  · obtain ⟨-, -, -, h1, h2⟩ := hg
    grind [PoolOK, store_grind]
  · grind [store_grind]

end grow

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
  natAddLit_refines storeProg rfl rfl rfl rfl rfl LitR (fun _ _ h => h.1) (fun m m' a hR hg => LitR.grow m m' hg a hR)
    (internLit_refines storeProg rfl rfl rfl rfl rfl rfl) n s₀ a₀ hR oa la ob lb ha hb

/-- From an L run of `nat_add_lit` to the arena run of the `Nat.add` arm, under `LitR`. -/
theorem natAddLit_run_store (fuel : Nat) (m : Mem) (a₀ : AState) (hR : LitR m a₀)
    (oa la ob lb : Word) (ha : SliceOK m oa la) (hb : SliceOK m ob lb) (r : List Word) (m' : Mem)
    (h : run storeProg fuel "nat_add_lit" [oa, la, ob, lb] m = .ok (r, m')) :
    ∃ a', (natAddArm (pv (m.arr64 POOL) oa.toNat la.toNat) (pv (m.arr64 POOL) ob.toNat lb.toNat)).run
      a₀ = .ok (some (decE (r.headD 0)), a') ∧ LitR m' a' :=
  natAddLit_run storeProg rfl rfl rfl rfl rfl LitR (fun _ _ h => h.1) (fun m m' a hR hg => LitR.grow m m' hg a hR)
    (internLit_refines storeProg rfl rfl rfl rfl rfl rfl) fuel m a₀ hR oa la ob lb ha hb r m' h

end L.Arena
