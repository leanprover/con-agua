import ConAgua.Arena.Promote
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# `pool_alloc0` and `pool_copy0`: the promotion's tier-0 slices (lane tierpool)

A persistent node's slice lies in tier 0 (`RSlice`). Inside the scratch tier (the top in tier 1)
the promotion copies a tier-1 slice to tier 0 above the saved tier-0 top `PT0[0]`, which moves
past it; no slice in use lies there (`SliceOK`: a tier-0 slice in use ends below `PT0[0]` while
the top is in tier 1), so every table's relation stays (`ArenaD.grow0`).

* `poolAlloc0_spec`, `poolCopy0_spec`: the L runs, by the models `alloc0Mem`, `cp0W`.
* `Grow0 m m'`: `m'` is `m` with words of tier 0 at and above `ptop0` written and `ptop0` raised,
  the top in tier 1; `ArenaD.grow0` keeps the arena across it.
* `copy0_facts`: `pool_copy0`'s memory is a `Grow0` whose new slice holds the old one's words.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The models -/

/-- Where `pool_alloc0` allocates: the top outside the scratch tier, else the saved tier-0 top. -/
def alloc0Q (m : Mem) : Word := if m.top >>> 40 = 0 then m.top else m.ptop0

/-- `pool_alloc0(l)`'s memory: the tier-0 top raised by `l`. -/
def alloc0Mem (m : Mem) (l : Word) : Mem :=
  if m.top >>> 40 = 0 then m.set64 CTL 0 (alloc0Q m + l) else m.set64 PT0 0 (alloc0Q m + l)

/-- The model of `pool_copy0`'s loop: `POOL⦃o + j⦄` to `POOL⟨0⟩[q + j]`, `j` up to `l`. -/
def cp0W (m : Mem) (q o l j : Word) : Mem :=
  if j < l then cp0W (m.set64 (tierA 0 0) (q + j) (prd m (o + j))) q o l (j + 1) else m
termination_by l.toNat - j.toNat
decreasing_by
  have : j.toNat < l.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹j < l›
  have := l.toNat_lt
  have : (j + 1).toNat = j.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

theorem cp0W_end (m : Mem) (q o l j : Word) (hj : ¬ j < l) : cp0W m q o l j = m := by
  rw [cp0W]; simp only [hj, ↓reduceIte]

theorem cp0W_step (m m' : Mem) (q o l j j' : Word) (hj : j < l) (hj' : j' = j + 1)
    (hm' : m' = m.set64 (tierA 0 0) (q + j) (prd m (o + j))) :
    cp0W m q o l j = cp0W m' q o l j' := by
  subst hj' hm'
  rw [cp0W]; simp only [hj, ↓reduceIte]

grind_pattern [arena_grind] cp0W_end => cp0W m q o l j
grind_pattern [arena_grind] cp0W_step => cp0W m q o l j, cp0W m' q o l j'

/-! ## The specs -/

section specs
variable (p : Prog)

theorem copy0Loop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n copy0Loop
    ⦃fun r s' => r = .normal ∧ s'.loc 2 = s₀.loc 2 ∧
      s'.mem = cp0W s₀.mem (s₀.loc 2) (s₀.loc 0) (s₀.loc 1) (s₀.loc 3); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := copy0Loop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, st64, ih] <;> finish [prd]

theorem copy0Loop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) copy0Loop
    ⦃fun r s' => r = .normal ∧ s'.loc 2 = s₀.loc 2 ∧
      s'.mem = cp0W s₀.mem (s₀.loc 2) (s₀.loc 0) (s₀.loc 1) (s₀.loc 3); ⊤⦄ :=
  Triple.step_exec (copy0Loop_spec p (n + 1) s₀)

/-- `pool_alloc0`'s checks: the slice fits in tier 0 above the allocation point. -/
def Alloc0OK (m : Mem) (l : Word) : Prop :=
  alloc0Q m ≤ m.len64 (tierA 0 0) ∧ l ≤ m.len64 (tierA 0 0) - alloc0Q m ∧
    (m.top >>> 40 ≠ 0 → 0 < (m.arr64 PT0).size)

instance (m : Mem) (l : Word) : Decidable (Alloc0OK m l) := by unfold Alloc0OK; infer_instance

theorem poolAlloc0_spec (hp : p.lookup "pool_alloc0" = some poolAlloc0) (n : Nat) (s₀ : St)
    (l : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "pool_alloc0" [l]
    ⦃fun r s' => LocEq s' s₀ ∧ Alloc0OK s₀.mem l ∧ r = [alloc0Q s₀.mem] ∧
      s'.mem = alloc0Mem s₀.mem l; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, poolAlloc0]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [Alloc0OK, alloc0Q, alloc0Mem, Mem.ptop0, Mem.top]

theorem poolCopy0_spec (hp : p.lookup "pool_copy0" = some poolCopy0)
    (ha : p.lookup "pool_alloc0" = some poolAlloc0) (n : Nat) (s₀ : St) (o l : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "pool_copy0" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ Alloc0OK s₀.mem l ∧ r = [alloc0Q s₀.mem] ∧
      s'.mem = cp0W (alloc0Mem s₀.mem l) (alloc0Q s₀.mem) o l 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, poolCopy0]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, poolAlloc0_spec p ha n,
      copy0Loop_step_spec p n] <;>
    finish

/-- `poolCopy0_spec` at every fuel (fuel `0` aborts). -/
theorem poolCopy0_spec' (hp : p.lookup "pool_copy0" = some poolCopy0)
    (ha : p.lookup "pool_alloc0" = some poolAlloc0) (n : Nat) (s₀ : St) (o l : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "pool_copy0" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ Alloc0OK s₀.mem l ∧ r = [alloc0Q s₀.mem] ∧
      s'.mem = cp0W (alloc0Mem s₀.mem l) (alloc0Q s₀.mem) o l 0; ⊤⦄ := by
  cases n with
  | zero =>
    rw [invoke_eq _ hp]
    simp only [callFn, poolCopy0]
    vcgen [exec] <;> grind
  | succ n => exact poolCopy0_spec p hp ha n s₀ o l

end specs

/-! ## Writing tier 0 above the saved tier-0 top -/

/-- **`m'` is `m` with tier-0 words at and above `ptop0` written and `ptop0` raised**, the top in
tier 1: no slice in use moves (`grow0_slice`). -/
structure Grow0 (m m' : Mem) : Prop where
  frame : MemFrame [POOL, PT0] [] m m'
  low : ∀ k, k < m.ptop0.toNat → (m'.arr64 POOL)[k]? = (m.arr64 POOL)[k]?
  le : m.ptop0.toNat ≤ m'.ptop0.toNat
  cap : m'.ptop0.toNat ≤ (m'.arr64 POOL).size
  tier1 : 2 ^ 40 ≤ m.top.toNat

theorem Grow0.top {m m' : Mem} (h : Grow0 m m') : m'.top = m.top := by
  have := h.frame.2.1 0 (by simp)
  simp only [rdW] at this
  simpa [Mem.top] using this

/-- A word of a slice in use reads the same after a `Grow0`. -/
theorem Grow0.prd_eq {m m' : Mem} (h : Grow0 m m') (hp : PoolOK m) (j : Nat) (hj : j < m.top.toNat)
    (hj0 : j < 2 ^ 40 → j < m.ptop0.toNat) :
    L.Arena.prd m' (UInt64.ofNat j) = L.Arena.prd m (UInt64.ofNat j) := by
  have h41 := hp.top41
  rw [prd_nat m' j (by omega), prd_nat m j (by omega)]
  by_cases hj4 : j < 2 ^ 40
  · simp only [hj4, ↓reduceIte]
    rw [h.low (j % 2 ^ 40) (by have := hj0 hj4; omega)]
  · simp only [hj4, ↓reduceIte]
    rw [h.frame.1 POOL1 (by decide) (by decide)]

/-- **A slice in use is unchanged by a `Grow0`**, pointwise in both pool views. -/
theorem Grow0.slice {m m' : Mem} (h : Grow0 m m') (hp : PoolOK m) {o l : Word} (hs : SliceOK m o l) :
    (∀ k < l.toNat, (vpool m')[o.toNat + k]?.getD 0 = (vpool m)[o.toNat + k]?.getD 0) ∧
    (∀ k < l.toNat, (tpool m')[o.toNat + k]?.getD 0 = (tpool m)[o.toNat + k]?.getD 0) := by
  have h41 := hp.top41
  have ht1 := h.tier1
  obtain ⟨h1, h2⟩ := hs
  have hw : ∀ k < l.toNat,
      L.Arena.prd m' (UInt64.ofNat (o.toNat + k)) = L.Arena.prd m (UInt64.ofNat (o.toNat + k)) :=
    fun k hk => h.prd_eq hp _ (by omega) (fun h0 => by omega)
  have hx : ∀ k < l.toNat, (UInt64.ofNat (o.toNat + k)).toNat = o.toNat + k := fun k hk =>
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have e := hx k hk
    rw [← e, vpool_getD _ _ (by omega), vpool_getD _ _ (by omega)]; exact hw k hk
  · have e := hx k hk
    rw [← e, tpool_getD, tpool_getD]; exact hw k hk

theorem Grow0.rslice {m m' : Mem} (h : Grow0 m m') {t o l : Word} (hs : RSlice m t o l) :
    RSlice m' t o l := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  have := h.le; have := h.tier1
  refine ⟨⟨by rw [h.top]; exact h1, ?_⟩, h3⟩
  rw [h.top]; omega

theorem Grow0.poolOK {m m' : Mem} (h : Grow0 m m') (hp : PoolOK m) : PoolOK m' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hp
  have hf := h.frame
  have hpc : pcap m' = pcap m := pcap_congr (hf.2.2.1 _) (hf.2.2.1 _)
  refine ⟨by rw [hf.2.2.2]; exact a1, by rw [hf.2.2.1]; exact a2, by rw [hpc]; exact a3,
    by rw [hpc, h.top]; exact a4, .inr h.cap, ?_⟩
  rw [h.top, hf.2.2.1]; exact a6

theorem Grow0.tfld {m m' : Mem} (h : Grow0 m m') (R : TRec) (hR : R.arr < 256 ∧ R.arr ≠ POOL ∧ R.arr ≠ PT0 ∧ R.arr ≠ CTL)
    (t i j : Word) : L.Arena.tfld m' R t i j = L.Arena.tfld m R t i j := by
  simp only [L.Arena.tfld]
  rw [h.frame.1 _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨tierA_ne_small _ _ hR.1 (by decide) (Ne.symm hR.2.1) t,
      tierA_ne_small _ _ hR.1 (by decide) (Ne.symm hR.2.2.1) t⟩)
    (tierA_ne_small _ _ hR.1 (by decide) (Ne.symm hR.2.2.2) t)]

section rels
variable {m m' : Mem} (h : Grow0 m m') (hp : PoolOK m)
include h hp

theorem Grow0.recRel (t i : Word) (k : LitNode) (hk : RecRel m t i k) : RecRel m' t i k := by
  have htf := h.tfld LIT (by decide) t i
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · simp only [RecRel, NatRec, htf] at hk ⊢
    obtain ⟨h0, hsl, hnm, hpv, hh⟩ := hk
    obtain ⟨hv, hq⟩ := h.slice hp hsl.1
    refine ⟨h0, h.rslice hsl, fun hl => by rw [hv _ (by omega)]; exact hnm hl,
      by rw [← hpv]; exact pv_congr _ _ _ _ _ hv, by rw [hh]; exact (hashN_congr _ _ _ _ _ hq).symm⟩
  · simp only [RecRel, StrRec, htf] at hk ⊢
    obtain ⟨h0, hsl, hw, hh⟩ := hk
    obtain ⟨hv, hq⟩ := h.slice hp hsl.1
    exact ⟨h0, h.rslice hsl, by rw [← hw]; exact (sliceL_eq_iff _ _ _ _ _).mpr hv,
      by rw [hh]; exact (hashN_congr _ _ _ _ _ hq).symm⟩

theorem Grow0.nsRecRel (t i : Word) (k : StrNode) (hk : NsRecRel m t i k) : NsRecRel m' t i k := by
  have htf := h.tfld NSTR (by decide) t i
  simp only [NsRecRel, htf] at hk ⊢
  obtain ⟨h0, hsl, hw, hh⟩ := hk
  obtain ⟨hv, hq⟩ := h.slice hp hsl.1
  exact ⟨h0, h.rslice hsl, by rw [← hw]; exact (sliceL_eq_iff _ _ _ _ _).mpr hv,
    by rw [hh, hashN_congr _ _ _ _ _ hq]⟩

theorem Grow0.lsRecRel (t i : Word) (k : ListNode) (hk : LsRecRel m t i k) : LsRecRel m' t i k := by
  have htf := h.tfld LVLS (by decide) t i
  simp only [LsRecRel, htf] at hk ⊢
  obtain ⟨hsl, hw, hh⟩ := hk
  obtain ⟨hv, hq⟩ := h.slice hp hsl.1
  exact ⟨h.rslice hsl, by rw [← hw]; exact (sliceL_eq_iff _ _ _ _ _).mpr hv,
    by rw [hh]; exact (hashN_congr _ _ _ _ _ hq).symm⟩

end rels

/-- **A `Grow0` keeps the arena**: the pool tables by their records' slices (in use, so
unchanged), every other table and the derived ranges by the frame. -/
theorem ArenaD.grow0 {m m' : Mem} {a : AState} (h : Grow0 m m') (hD : ArenaD m a) : ArenaD m' a := by
  obtain ⟨hR, hDer⟩ := hD
  have hf := h.frame
  have hp := hR.lit.1
  have hra : ∀ {b : ArrId}, b < 256 → POOL ≠ b → PT0 ≠ b → CTL ≠ b → ∀ t,
      m'.arr64 (tierA b t) = m.arr64 (tierA b t) := fun hb h1 h2 h3 t =>
    hf.1 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨tierA_ne_small _ _ hb (by decide) h1 t, tierA_ne_small _ _ hb (by decide) h2 t⟩)
      (tierA_ne_small _ _ hb (by decide) h3 t)
  have hc : ∀ x, rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x := fun x => hf.2.1 x (by simp)
  refine ⟨?_, DerR.frameM _ _ m m' hf (by decide) a hDer⟩
  arena_build hR, hf with
    first
    | exact ⟨h.poolOK hp, ConsR.mono hR.lit.2 (hra (by decide) (by decide) (by decide) (by decide))
        (hra (by decide) (by decide) (by decide) (by decide)) (hf.2.2.1 CTL) (fun x _ => hc x)
        (fun t i k => h.recRel hp t i k)
        (fun t i => by simp only [litCS, litCSk, litH, hra (b := REC) (by decide) (by decide) (by decide) (by decide)])⟩
    | exact ConsR.mono hR.ls (hra (by decide) (by decide) (by decide) (by decide))
        (hra (by decide) (by decide) (by decide) (by decide)) (hf.2.2.1 CTL) (fun x _ => hc x)
        (fun t i k => h.lsRecRel hp t i k)
        (fun t i => by simp only [lsCS, lshash, hra (b := LSREC) (by decide) (by decide) (by decide) (by decide)])
    | exact ConsR.mono hR.nstr (hra (by decide) (by decide) (by decide) (by decide))
        (hra (by decide) (by decide) (by decide) (by decide)) (hf.2.2.1 CTL) (fun x _ => hc x)
        (fun t i k => h.nsRecRel hp t i k)
        (fun t i => by simp only [nstrCS, nshash, hra (b := NSREC) (by decide) (by decide) (by decide) (by decide)])

/-! ## `pool_copy0`'s memory -/

theorem tierA_00 : tierA 0 0 = POOL := rfl

/-- A tier-1 word is not moved by a tier-0 store. -/
theorem prd_set64_pool (m : Mem) (i v : Word) (x : Nat) (hx : 2 ^ 40 ≤ x) (hx' : x < 2 ^ 41) :
    L.Arena.prd (m.set64 POOL i v) (UInt64.ofNat x) = L.Arena.prd m (UInt64.ofNat x) := by
  rw [prd_nat _ x hx', prd_nat _ x hx']
  have : ¬ x < 2 ^ 40 := by omega
  simp only [this, ↓reduceIte]
  rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]

theorem cp0W_facts (q o l : Word) (ho : 2 ^ 40 ≤ o.toNat) (hol : o.toNat + l.toNat < 2 ^ 41) :
    ∀ (d : Nat) (m : Mem) (j : Word), l.toNat - j.toNat = d → j ≤ l →
      q.toNat + l.toNat ≤ (m.arr64 POOL).size → (m.arr64 POOL).size < 2 ^ 40 →
      MemFrame [POOL] [] m (cp0W m q o l j) ∧
      ∀ k, ((cp0W m q o l j).arr64 POOL)[k]? =
        if q.toNat + j.toNat ≤ k ∧ k < q.toNat + l.toNat then
          some (L.Arena.prd m (UInt64.ofNat (o.toNat + (k - q.toNat))))
        else (m.arr64 POOL)[k]? := by
  intro d
  induction d with
  | zero =>
    intro m j hd hj _ _
    have hjn : ¬ j < l := by rw [UInt64.lt_iff_toNat_lt]; omega
    rw [cp0W_end _ _ _ _ _ hjn]
    refine ⟨MemFrame.refl _ _ _, fun k => ?_⟩
    have : ¬ (q.toNat + j.toNat ≤ k ∧ k < q.toNat + l.toNat) := by
      have := UInt64.le_iff_toNat_le.mp hj; omega
    simp [this]
  | succ d ih =>
    intro m j hd hj hq hs
    have hjn : j < l := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hjn' := UInt64.lt_iff_toNat_lt.mp hjn
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hqj : (q + j).toNat = q.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
    have hoj : (o + j).toNat = o.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
    rw [cp0W]; simp only [hjn, ↓reduceIte, tierA_00]
    obtain ⟨m₁, hm₁⟩ : ∃ m₁, m₁ = m.set64 POOL (q + j) (L.Arena.prd m (o + j)) := ⟨_, rfl⟩
    rw [← hm₁]
    have hsz : (m₁.arr64 POOL).size = (m.arr64 POOL).size := by rw [hm₁]; exact size_set64 _ _ _ _ _
    obtain ⟨hf, hx⟩ := ih m₁ (j + 1) (by omega) (UInt64.le_iff_toNat_le.mpr (by omega))
      (by omega) (by omega)
    refine ⟨((hm₁ ▸ MemFrame.set64 m POOL (by decide) _ _).trans hf).mono (by simp) (by simp), fun k => ?_⟩
    rw [hx, hj1]
    have hp1 : ∀ x, 2 ^ 40 ≤ x → x < 2 ^ 41 →
        L.Arena.prd m₁ (UInt64.ofNat x) = L.Arena.prd m (UInt64.ofNat x) :=
      fun x h1 h2 => by rw [hm₁]; exact prd_set64_pool m _ _ x h1 h2
    have hm1k : (m₁.arr64 POOL)[k]? = if q.toNat + j.toNat = k then some (L.Arena.prd m (o + j))
        else (m.arr64 POOL)[k]? := by
      rw [hm₁, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hqj]
      by_cases h : q.toNat + j.toNat = k
      · subst h; simp [show q.toNat + j.toNat < (m.arr64 POOL).size by omega]
      · simp [h]
    by_cases h1 : q.toNat + (j.toNat + 1) ≤ k ∧ k < q.toNat + l.toNat
    · simp only [h1, and_self, ↓reduceIte, show q.toNat + j.toNat ≤ k ∧ k < q.toNat + l.toNat from
        ⟨by omega, h1.2⟩]
      rw [hp1 _ (by omega) (by omega)]
    · simp only [h1, ↓reduceIte]
      rw [hm1k]
      by_cases h2 : q.toNat + j.toNat = k
      · subst h2
        simp only [↓reduceIte, show q.toNat + j.toNat ≤ q.toNat + j.toNat ∧
          q.toNat + j.toNat < q.toNat + l.toNat from ⟨Nat.le_refl _, by omega⟩]
        congr 2
        apply UInt64.toNat_inj.mp
        rw [hoj, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
        omega
      · have : ¬ (q.toNat + j.toNat ≤ k ∧ k < q.toNat + l.toNat) := by omega
        simp only [h2, ↓reduceIte, this]

theorem len64_toNat' (m : Mem) (A : ArrId) (hs : (m.arr64 A).size < 2 ^ 63) :
    (m.len64 A).toNat = (m.arr64 A).size := by
  simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)

theorem tier0_iff' (x : Word) : x >>> 40 = 0 ↔ x.toNat < 2 ^ 40 := by
  constructor
  · intro h; have := congrArg UInt64.toNat h; rw [tag_tier_toNat] at this; simp at this; omega
  · intro h; exact UInt64.toNat_inj.mp (by rw [tag_tier_toNat]; simp; omega)

/-- **`pool_copy0` inside the scratch tier**: the copy lies at the saved tier-0 top, which moves
past it (a `Grow0`); it is a slice in use holding the source's words. -/
theorem copy0_facts (m : Mem) (o l : Word) (hp : PoolOK m) (ht : m.top >>> 40 ≠ 0)
    (hs : SliceOK m o l) (ho : 2 ^ 40 ≤ o.toNat) (hA : Alloc0OK m l) :
    alloc0Q m = m.ptop0 ∧ Grow0 m (cp0W (alloc0Mem m l) m.ptop0 o l 0) ∧
    SliceOK (cp0W (alloc0Mem m l) m.ptop0 o l 0) m.ptop0 l ∧ m.ptop0.toNat < 2 ^ 40 ∧
    (∀ k < l.toNat, (vpool (cp0W (alloc0Mem m l) m.ptop0 o l 0))[m.ptop0.toNat + k]?.getD 0 =
      (vpool m)[o.toNat + k]?.getD 0) ∧
    (∀ k < l.toNat, (tpool (cp0W (alloc0Mem m l) m.ptop0 o l 0))[m.ptop0.toNat + k]?.getD 0 =
      (tpool m)[o.toNat + k]?.getD 0) ∧
    (cp0W (alloc0Mem m l) m.ptop0 o l 0).flag = m.flag ∧
    (cp0W (alloc0Mem m l) m.ptop0 o l 0).top = m.top := by
  have hq : alloc0Q m = m.ptop0 := by simp [alloc0Q, ht]
  have h41 := hp.top41
  have ht1 : 2 ^ 40 ≤ m.top.toNat := Nat.le_of_not_lt (fun hc => ht ((tier0_iff' _).mpr hc))
  have hsm := hp.small
  obtain ⟨hA1, hA2, hA3⟩ := hA
  have hpt := hA3 ht
  rw [hq, tierA_00] at hA1 hA2
  have hlen := len64_toNat' m (tierA 0 0) (by rw [tierA_00]; have := hsm.1; omega)
  rw [tierA_00] at hlen
  have hq1 := UInt64.le_iff_toNat_le.mp hA1
  rw [hlen] at hq1
  have hl1 := UInt64.le_iff_toNat_le.mp hA2
  rw [UInt64.toNat_sub_of_le _ _ hA1, hlen] at hl1
  have hsz0 := hsm.1
  -- the allocation
  have e0 : alloc0Mem m l = m.set64 PT0 0 (m.ptop0 + l) := by simp [alloc0Mem, ht, hq]
  rw [e0]
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, m₀ = m.set64 PT0 0 (m.ptop0 + l) := ⟨_, rfl⟩
  rw [← hm₀]
  have hf0 : MemFrame [PT0] [] m m₀ := hm₀ ▸ MemFrame.set64 m PT0 (by decide) _ _
  have hp0 : m₀.arr64 POOL = m.arr64 POOL := hf0.1 POOL (by decide) (by decide)
  have hp1 : m₀.arr64 POOL1 = m.arr64 POOL1 := hf0.1 POOL1 (by decide) (by decide)
  have hpt0 : m₀.ptop0 = m.ptop0 + l := by rw [hm₀]; exact Mem.ptop0_set64 _ _ hpt
  have hql : (m.ptop0 + l).toNat = m.ptop0.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hol : o.toNat + l.toNat < 2 ^ 41 := by have := hs.1; omega
  obtain ⟨hf1, hx⟩ := cp0W_facts m.ptop0 o l ho hol _ m₀ 0 rfl (UInt64.le_iff_toNat_le.mpr (by simp))
    (by rw [hp0]; omega) (by rw [hp0]; omega)
  obtain ⟨m₁, hm₁⟩ : ∃ m₁, m₁ = cp0W m₀ m.ptop0 o l 0 := ⟨_, rfl⟩
  rw [← hm₁] at hf1 hx ⊢
  have hf : MemFrame [POOL, PT0] [] m m₁ :=
    (hf0.mono (by simp) (by simp)).trans (hf1.mono (by simp) (by simp))
  have htop : m₁.top = m.top := by
    have := hf.2.1 0 (by simp); simp only [rdW] at this; simpa [Mem.top] using this
  have hpt1 : m₁.ptop0 = m.ptop0 + l := by
    rw [← hpt0]; simp only [Mem.ptop0]; rw [hf1.1 PT0 (by decide) (by decide)]
  have hsz1 : (m₁.arr64 POOL).size = (m.arr64 POOL).size := hf.2.2.1 POOL
  have hg : Grow0 m m₁ := by
    refine ⟨hf, fun k hk => ?_, by rw [hpt1, hql]; omega, by rw [hpt1, hql, hsz1]; omega, ht1⟩
    rw [hx k, ← hp0]
    have : ¬ (m.ptop0.toNat + (0 : Word).toNat ≤ k ∧ k < m.ptop0.toNat + l.toNat) := by simp; omega
    simp only [this, ↓reduceIte]
  have hval : ∀ k < l.toNat, L.Arena.prd m₁ (UInt64.ofNat (m.ptop0.toNat + k)) =
      L.Arena.prd m (UInt64.ofNat (o.toNat + k)) := fun k hk => by
    rw [prd_nat _ _ (by omega)]
    have h4 : m.ptop0.toNat + k < 2 ^ 40 := by omega
    simp only [h4, ↓reduceIte, Nat.mod_eq_of_lt h4]
    rw [hx]
    have : m.ptop0.toNat + (0 : Word).toNat ≤ m.ptop0.toNat + k ∧
        m.ptop0.toNat + k < m.ptop0.toNat + l.toNat := by simp; omega
    simp only [this, and_self, ↓reduceIte, Option.getD_some, Nat.add_sub_cancel_left]
    rw [prd_nat _ _ (by omega), prd_nat _ _ (by omega)]
    have : ¬ o.toNat + k < 2 ^ 40 := by omega
    simp only [this, ↓reduceIte, hp1]
  have hxk : ∀ x, x < 2 ^ 41 → (UInt64.ofNat x).toNat = x := fun x hx =>
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  refine ⟨hq, hg, ⟨by rw [htop]; omega, .inr (.inr (by rw [hpt1, hql]; exact Nat.le_refl _))⟩, by omega,
    fun k hk => ?_, fun k hk => ?_, ?_, htop⟩
  · rw [← hxk (m.ptop0.toNat + k) (by omega), ← hxk (o.toNat + k) (by omega),
      vpool_getD _ _ (by rw [hxk _ (by omega)]; omega), vpool_getD _ _ (by rw [hxk _ (by omega)]; omega)]
    exact hval k hk
  · rw [← hxk (m.ptop0.toNat + k) (by omega), ← hxk (o.toNat + k) (by omega), tpool_getD, tpool_getD]
    exact hval k hk
  · have := hf.2.1 1 (by simp); simp only [rdW] at this; simpa [Mem.flag] using this

/-! ## Slices in use kept -/

/-- **Every slice in use stays in use and holds the same words; the top and the pool above it in
its tier are kept**: what the promotion keeps of the pool across its copies (`Grow0`) and its other
writes. -/
def SlKeep (m m' : Mem) : Prop :=
  m'.top = m.top ∧
  (∀ x : Nat, m.top.toNat ≤ x → x < 2 ^ 41 → (x < 2 ^ 40 ↔ m.top.toNat < 2 ^ 40) →
    (vpool m')[x]? = (vpool m)[x]?) ∧
  ∀ o l : Word, SliceOK m o l → SliceOK m' o l ∧
    ∀ k < l.toNat, (vpool m')[o.toNat + k]?.getD 0 = (vpool m)[o.toNat + k]?.getD 0

theorem SlKeep.refl (m : Mem) : SlKeep m m := ⟨rfl, fun _ _ _ _ => rfl, fun _ _ h => ⟨h, fun _ _ => rfl⟩⟩

theorem SlKeep.trans {m₁ m₂ m₃ : Mem} (h₁ : SlKeep m₁ m₂) (h₂ : SlKeep m₂ m₃) : SlKeep m₁ m₃ :=
  ⟨h₂.1.trans h₁.1, fun x h1 h2 h3 => by
      have e := h₁.1
      rw [h₂.2.1 x (by rw [e]; exact h1) h2 (by rw [e]; exact h3), h₁.2.1 x h1 h2 h3],
    fun o l h => ⟨(h₂.2.2 o l (h₁.2.2 o l h).1).1, fun k hk =>
      ((h₂.2.2 o l (h₁.2.2 o l h).1).2 k hk).trans ((h₁.2.2 o l h).2 k hk)⟩⟩

/-- A frame away from the pool's arrays, the saved tier-0 top and the top keeps the slices. -/
theorem SlKeep.of_frame {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    (hA : POOL ∉ A ∧ POOL1 ∉ A ∧ PT0 ∉ A) (hC : (0 : Word) ∉ C) : SlKeep m m' := by
  have h0 := hf.1 POOL hA.1 (by decide)
  have h1 := hf.1 POOL1 hA.2.1 (by decide)
  have ht : m'.top = m.top := by
    have := hf.2.1 0 hC; simp only [rdW] at this; simpa [Mem.top] using this
  have hp : m'.ptop0 = m.ptop0 := ptop0_congr (hf.1 PT0 hA.2.2 (by decide))
  refine ⟨ht, fun x _ _ _ => by rw [vpool_congr h0 h1], fun o l h => ?_⟩
  exact ⟨(SliceOK_congr o l ht hp).mpr h, fun k _ => by rw [vpool_congr h0 h1]⟩

theorem Grow0.slKeep {m m' : Mem} (h : Grow0 m m') (hp : PoolOK m) : SlKeep m m' := by
  refine ⟨h.top, fun x h1 h2 h3 => ?_, fun _ _ hs =>
    ⟨(h.rslice (t := 1) ⟨hs, fun e => absurd e (by decide)⟩).1, (h.slice hp hs).1⟩⟩
  have ht1 := h.tier1
  have hx : (UInt64.ofNat x).toNat = x := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  rw [← hx, vpool_get? _ _ (by omega), vpool_get? _ _ (by omega), prd_nat _ _ h2, prd_nat _ _ h2]
  have : ¬ x < 2 ^ 40 := by omega
  simp only [this, ↓reduceIte]
  rw [h.frame.1 POOL1 (by decide) (by decide)]

/-! ## The top's tier kept -/

/-- **A top in tier 0 stays in tier 0**: what the promotion keeps of the mode (with the flag kept
by its frames). -/
def TierKeep (m m' : Mem) : Prop := m.top.toNat < 2 ^ 40 → m'.top.toNat < 2 ^ 40

theorem TierKeep.refl (m : Mem) : TierKeep m m := id

theorem TierKeep.trans {m₁ m₂ m₃ : Mem} (h₁ : TierKeep m₁ m₂) (h₂ : TierKeep m₂ m₃) : TierKeep m₁ m₃ :=
  fun h => h₂ (h₁ h)

theorem TierKeep.of_frame {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    (h0 : (0 : Word) ∉ C) : TierKeep m m' := fun h => by
  have := hf.2.1 0 h0; simp only [rdW] at this
  have ht : m'.top = m.top := by simpa [Mem.top] using this
  rw [ht]; exact h

theorem TierKeep.of_grows {m m' : Mem} (hg : Grows m m') : TierKeep m m' := fun h => by
  have := hg.tier; omega

/-- The mode across a run that keeps the flag and the top's tier. -/
theorem ModeOK.of_keep {m m' : Mem} (h : ModeOK m) (hfl : m'.flag = m.flag) (ht : TierKeep m m') :
    ModeOK m' := by
  rcases h with h | h
  · exact .inl (by rw [hfl]; exact h)
  · exact .inr (ht h)

end L.Arena
