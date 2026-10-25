import ConAgua.Arena.PromoteProg
import ConAgua.Arena.PromoteFlag

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
set_option linter.unusedSimpArgs false

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
  alloc0Q m ≤ m.len64 (tierA 0 0) ∧ l ≤ m.len64 (tierA 0 0) - alloc0Q m

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
    by rw [hpc, h.top]; exact a4, h.cap, ?_⟩
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

end L.Arena
