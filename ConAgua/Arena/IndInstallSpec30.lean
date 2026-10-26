import ConAgua.Arena.IndInstallSpec29
import ConAgua.Arena.CoreErec
import ConAgua.Arena.RecGenSpec4
import ConAgua.Arena.RecCheckSpec4

/-!
# Refinements of `IndInstall`, part 30 (lane `indproofs3`, helper `tail`): the walk memos from the
program text; the `BlockPass` record's slices

* **The walk memos across callees with no memo lemma.** `check_block_tables` needs the `hb` memo
  well formed (`HbMemo`) after `check_block_idx_sorts`, `cons_block_ctors`, the flush,
  `block_nested_bit`, `check_block_rec` and `cons_block_recs_tf`, whose relational lemmas say
  nothing about the memo arrays. Their write sets are facts about the program text: `closedA p
  hbFreeA hbFreeC fs` (`Frame.lean`, lane `whnf3`'s mechanism) says every function of the
  call-closed set `fs` stores only outside the `hb` memo's array and stamp word; then a call of any
  of them keeps `HbMemo` (`HbMemo.ofClosed`). Likewise `PosMR` (all five walk memos, which
  `check_block_positivity` needs) across `check_block_inds`, `check_block_ctors`, `block_nest_ctx`
  (`PosMR.ofClosed`, at `posFreeA`/`posFreeC`). For the checker's program each is a
  `decide +kernel` over the call closure (a program hypothesis, like the lookups).
* `BPassB`: the record's eight slices lie below the pool's top (as `ShapeSrc` for the shape's
  members); `bpPSl`/`bpHSl` read a slice of a decoded record as L does.
-/

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Write sets from the program text -/

/-- Every word array below 320 (both tiers) but the `has_loose_bvar_b` memo's. -/
def hbFreeA : List ArrId := (List.range 388).filter (· ≠ HBM)
/-- Every `CTL` word below 256 but the `hb` memo's stamp word. -/
def hbFreeC : List Word := ((List.range 256).filter (· ≠ 214)).map Nat.toUInt64

theorem hbFree_mfr {m m' : Mem} (h : MemFrame hbFreeA hbFreeC m m') :
    MFr [MAM, NOM, DPM, RFM, RAM, TAM, MCM]
      [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 215, 216, 217, 218, 219] m m' := by
  refine ⟨hbFreeA, hbFreeC, h, fun b hb => ?_, fun x hx => ?_⟩
  · simp only [hbFreeA, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb
    obtain ⟨c, hc⟩ : ∃ c : Nat, c = b := ⟨b, rfl⟩
    have h1 : c < 388 := hc ▸ hb.1
    have h2 : c ≠ 207 := hc ▸ hb.2
    subst hc
    by_cases a1 : c < 201; · exact .inl a1
    by_cases a2 : 208 < c; · exact .inr (.inl a2)
    right; right
    rcases (show c = 201 ∨ c = 202 ∨ c = 203 ∨ c = 204 ∨ c = 205 ∨ c = 206 ∨ c = 208 by omega) with
      h | h | h | h | h | h | h <;> subst h <;> decide
  · simp only [hbFreeC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
    obtain ⟨c, ⟨hc, hne⟩, rfl⟩ := hx
    have hc' : (Nat.toUInt64 c).toNat = c := by simp; omega
    rw [hc']
    by_cases h1 : c < 202; · exact .inl h1
    by_cases h2 : 219 < c; · exact .inr (.inl h2)
    right; right
    rcases (show c = 202 ∨ c = 203 ∨ c = 204 ∨ c = 205 ∨ c = 206 ∨ c = 207 ∨ c = 208 ∨ c = 209 ∨
      c = 210 ∨ c = 211 ∨ c = 212 ∨ c = 213 ∨ c = 215 ∨ c = 216 ∨ c = 217 ∨ c = 218 ∨ c = 219 by omega) with
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- **A call of a function of a set closed outside the `hb` memo keeps it well formed.** -/
theorem HbMemo.ofClosed {p : Prog} {fs : List FnName} (hcl : closedA p hbFreeA hbFreeC fs = true)
    {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word} {m' : Mem}
    (h : callW p n f vs m = some (r, m')) (hM : HbMemo m) : HbMemo m' := by
  obtain ⟨mp, hmp⟩ := hM
  exact ⟨mp, hbMR_mfr (hbFree_mfr (run_memFrame hcl hf (run_of_callW h)).1) (by decide) (by decide) hmp⟩

/-- Every word array below 320 (both tiers) but the five walk memos'. -/
def posFreeA : List ArrId := (List.range 388).filter (fun b => b ∉ [NOM, DPM, RAM, HBM, RFM])
/-- Every `CTL` word below 256 but the five memos' stamp words (and the banked memo's two). -/
def posFreeC : List Word :=
  ((List.range 256).filter (fun c => c ∉ [204, 206, 208, 210, 214, 218, 219])).map Nat.toUInt64

theorem posFree_mfr {m m' : Mem} (h : MemFrame posFreeA posFreeC m m') :
    MFr [MAM, TAM, MCM] [202, 203, 205, 207, 209, 211, 212, 213, 215, 216, 217] m m' := by
  refine ⟨posFreeA, posFreeC, h, fun b hb => ?_, fun x hx => ?_⟩
  · simp only [posFreeA, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb
    obtain ⟨c, hc⟩ : ∃ c : Nat, c = b := ⟨b, rfl⟩
    have h1 : c < 388 := hc ▸ hb.1
    have h2 : c ∉ [202, 203, 205, 207, 204] := hc ▸ hb.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
    subst hc
    by_cases a1 : c < 201; · exact .inl a1
    by_cases a2 : 208 < c; · exact .inr (.inl a2)
    right; right
    rcases (show c = 201 ∨ c = 206 ∨ c = 208 by omega) with h | h | h <;> subst h <;> decide
  · simp only [posFreeC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    obtain ⟨c, ⟨hc, hne⟩, rfl⟩ := hx
    have hc' : (Nat.toUInt64 c).toNat = c := by simp; omega
    rw [hc']
    by_cases h1 : c < 202; · exact .inl h1
    by_cases h2 : 219 < c; · exact .inr (.inl h2)
    right; right
    rcases (show c = 202 ∨ c = 203 ∨ c = 205 ∨ c = 207 ∨ c = 209 ∨ c = 211 ∨ c = 212 ∨ c = 213 ∨
      c = 215 ∨ c = 216 ∨ c = 217 by omega) with
      h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- **A call of a function of a set closed outside the five walk memos keeps them well formed.** -/
theorem PosMR.ofClosed {p : Prog} {fs : List FnName} (hcl : closedA p posFreeA posFreeC fs = true)
    {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word} {m' : Mem}
    (h : callW p n f vs m = some (r, m')) (hM : PosMR m) : PosMR m' :=
  hM.mfr (posFree_mfr (run_memFrame hcl hf (run_of_callW h)).1) (by simp [PosAv, MAM, NOM, DPM, RAM, HBM, RFM, TAM, MCM])

/-- **`flush_caches()` as a `Sim`**, keeping the stage relation and the `hb` memo. -/
theorem tailSimFlush {p : Prog} (hF : FlushProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} (hS : StageR dn vis fe m a) (hM : HbMemo m) :
    Sim (callW p n "flush_caches" [] m) flushCaches a
      (fun _ _ m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ HbMemo m') := by
  intro r m' e
  obtain ⟨s', rfl, -, hok, hmem⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (flushCaches_spec p hF n _) e
  obtain ⟨hS', hg⟩ := flush_stage hS hok
  refine ⟨(), _, flushCaches_run a, ?_⟩
  rw [hmem]
  exact ⟨hS', hg, hM.fr (MFr.of_frame (flushMem_frame m) (by simp) (by
    intro x hx; left; have := flushCtl_lt x hx; omega))⟩

/-! ## The record's slices -/

/-- **The `BlockPass` record and its eight slices lie below the pool's top.** -/
def BPassB (m : Mem) (q : Nat) : Prop :=
  q + 19 ≤ iwTop m ∧ ∀ i ∈ [1, 4, 6, 8, 10, 12, 15, 17], ∀ o l, iwN m (q + i) = some o →
    iwN m (q + i + 1) = some l → o + l ≤ iwTop m

theorem BPassB.grow {m m' : Mem} (hg : IWGrow m m') {q : Nat} (h : BPassB m q) : BPassB m' q := by
  refine ⟨Nat.le_trans h.1 hg.1, fun i hi o l h1 h2 => ?_⟩
  have hi' : i + 1 < 19 := by simp at hi; omega
  have e1 : iwN m' (q + i) = iwN m (q + i) := by
    simp only [iwN, nat?, iwA]; rw [hg.2.2.1 _ (by have := h.1; omega)]
  have e2 : iwN m' (q + i + 1) = iwN m (q + i + 1) := by
    simp only [iwN, nat?, iwA]; rw [hg.2.2.1 _ (by have := h.1; omega)]
  rw [e1] at h1; rw [e2] at h2
  exact Nat.le_trans (h.2 i hi o l h1 h2) hg.1

/-- A word of the pool below the top, read where L reads it. -/
theorem bpWord {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) {w : Word} (hw : w.toNat = i) :
    rdW (m.arr64 IW) w = UInt64.ofNat v ∧ v < 2 ^ 64 := by
  obtain ⟨h1, h2, -⟩ := partsIwRd h hw; exact ⟨h1, h2⟩

/-- **A pointer slice of a decoded record**, at the words L reads, below the tops. -/
theorem bpPSl {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q)) {m : Mem}
    {i : Nat} {xs : List α} (h : decAt (truncM m) (decPL (truncM m) (f (truncM m))) i = some xs)
    (hB : ∀ o l, iwN m i = some o → iwN m (i + 1) = some l → o + l ≤ iwTop m)
    {w w1 : Word} (hw : w.toNat = i) (hw1 : w1.toNat = i + 1) :
    PSlR f xs (rdW (m.arr64 IW) w) (rdW (m.arr64 IW) w1) m := by
  obtain ⟨o, l, ho, hl, hd, -⟩ := partsAt hf h
  obtain ⟨hwo, -⟩ := bpWord ho hw
  obtain ⟨hwl, -⟩ := bpWord hl hw1
  rw [ofNat_toNat_word] at hwo hwl
  rw [hwo, hwl]
  exact ⟨hd, hB _ _ (iwN_truncM_get ho).2 (iwN_truncM_get hl).2⟩

/-- **A handle slice of a decoded record**, at the words L reads, below the top. -/
theorem bpHSl {k : IdxKind} {m : Mem} {i : Nat} {xs : List (Idx k)}
    (h : decAt (truncM m) (decHL (truncM m)) i = some xs)
    (hB : ∀ o l, iwN m i = some o → iwN m (i + 1) = some l → o + l ≤ iwTop m)
    {w w1 : Word} (hw : w.toNat = i) (hw1 : w1.toNat = i + 1) :
    decHL m (rdW (m.arr64 IW) w).toNat (rdW (m.arr64 IW) w1).toNat = some xs ∧
      (rdW (m.arr64 IW) w).toNat + (rdW (m.arr64 IW) w1).toNat ≤ iwTop m := by
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some h
  obtain ⟨hwo, hob⟩ := bpWord ho hw
  obtain ⟨hwl, hlb⟩ := bpWord hl hw1
  rw [hwo, hwl, UInt64.toNat_ofNat_of_lt' hob, UInt64.toNat_ofNat_of_lt' hlb]
  have hb := hB _ _ (iwN_truncM_get ho).2 (iwN_truncM_get hl).2
  exact ⟨by rw [← decHL_truncM hb]; exact hd, hb⟩

end L.Ind
