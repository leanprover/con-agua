module

public import ConAgua.Arena.LoopT
import ConAgua.Arena.IndSumSpec.StructUsedHb
import ConAgua.Arena.IndTwin
public import ConAgua.Arena.IndInstallSpec.Frame
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndPosSpec.Mfr
public import ConAgua.Arena.RecCheckSpec.RcLook
public import ConAgua.Arena.IndInstallSpec.LeafKeep
public import ConAgua.Arena.IndInstallSpec.PosFreeMfr
public import ConAgua.Arena.IndInstallSpec.GpbWSimF

@[expose] public section

/-!
# The inductive arm's memos across its calls (lane `indstaget`)

What `cid_ref` needs to hand back `IndMemos` and `CoreMemos` (`IndArmSpec`'s post) beyond the
posts of its callees: write-set frames (program facts `closedA …`, decided for the checker's
program) for the memos a call does not write. Measured on the checker's program, each memo array /
epoch word of `IndMemos` and `CoreMemos` is written only by its own `…_put` / `…_clear`; the
recursor stage's memos (`RcMR`) are written in `check_block_tail` only by `check_block_rec` and
(`hb`) `check_block_tables`; `mentions_any`'s (`maMR`) only by `block_raw_rec`; `mentions_const`'s
(`mcMR`) by nothing under `check_ind_decl`.
-/


open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `RcMR` across a writer of the `hb` memo alone -/

/-- Every word array of the checker (`checkerWordArrays`) but the recursor check's memos other than `hb`'s. -/
def rcHbFreeA : List TieredArray := checkerWordArrays.filter (fun b => b ∉ ([NOM, DPM, RAM, RFM, TAM] : List TieredArray))
/-- Every `CTL` word below 256 but those memos' control words. -/
def rcHbFreeC : List Word :=
  ((List.range 256).filter (fun c => c ∉ [204, 206, 208, 210, 212, 213, 218, 219])).map Nat.toUInt64

theorem rcHbFree_mfr {m m' : Mem} (h : MemFrame rcHbFreeA rcHbFreeC m m') :
    MFr [MAM, MCM, HBM] [202, 203, 205, 207, 209, 211, 214, 215, 216, 217] m m' := by
  refine ⟨rcHbFreeA, rcHbFreeC, h, fun b hb => ?_, fun x hx => ?_⟩
  · have key : ∀ b ∈ rcHbFreeA,
        b.arr < 201 ∨ 208 < b.arr ∨ b ∈ ([MAM, MCM, HBM] : List TieredArray) := by
      decide +kernel
    exact key b hb
  · simp only [rcHbFreeC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨c, ⟨hc, h2⟩, rfl⟩ := hx
    have : (Nat.toUInt64 c).toNat = c := by simp; omega
    rw [this]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    by_cases h1 : c < 202
    · exact .inl h1
    by_cases h2' : 219 < c
    · exact .inr (.inl h2')
    right; right
    have : c = 202 ∨ c = 203 ∨ c = 205 ∨ c = 207 ∨ c = 209 ∨ c = 211 ∨ c = 214 ∨ c = 215 ∨
        c = 216 ∨ c = 217 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **`RcMR` across a callee that writes, of its memos, only `hb`'s**, that memo given after it. -/
theorem RcMR.ofClosedHb {p : Prog} {fs : List FnName} (hcl : closedA p rcHbFreeA rcHbFreeC fs = true)
    {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word} {m' : Mem}
    (h : callW p n f vs m = some (r, m')) (hM : RcMR m) (hb : HbMemo m') : RcMR m' := by
  have hfr := rcHbFree_mfr (run_memFrame hcl hf (run_of_callW h)).1
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb'⟩, ⟨c, hc⟩, -, ⟨M, G, g, hR⟩⟩, ⟨t, ht⟩⟩ := hM
  exact ⟨⟨⟨a, noMR_mfr hfr (by decide) (by decide) ha⟩, ⟨b, dpMR_mfr hfr (by decide) (by decide) hb'⟩,
    ⟨c, rpMR_mfr hfr (by decide) (by decide) hc⟩, hb, ⟨M, G, g, hR.mfr hfr (by decide) (by decide)⟩⟩,
    ⟨t, taMR_mfr hfr (by decide) (by decide) ht⟩⟩

/-! ## `maMR`, `mcMR` across writers outside them -/

/-- Every word array of the checker (`checkerWordArrays`) but `mentions_any`'s memo. -/
def maFreeA : List TieredArray := checkerWordArrays.filter (· ≠ MAM)
/-- Every `CTL` word below 256 but its control words. -/
def maFreeC : List Word := ((List.range 256).filter (fun c => c ≠ 202 ∧ c ≠ 203)).map Nat.toUInt64

/-- Every word array of the checker (`checkerWordArrays`) but `mentions_const`'s memo. -/
def mcFreeA : List TieredArray := checkerWordArrays.filter (· ≠ MCM)
/-- Every `CTL` word below 256 but its control words. -/
def mcFreeC : List Word := ((List.range 256).filter (fun c => c ≠ 216 ∧ c ≠ 217)).map Nat.toUInt64

theorem maMR.ofClosed {p : Prog} {fs : List FnName} (hcl : closedA p maFreeA maFreeC fs = true)
    {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word} {m' : Mem}
    (h : callW p n f vs m = some (r, m')) (hM : ∃ mp, maMR m mp) : ∃ mp, maMR m' mp := by
  obtain ⟨mp, hm⟩ := hM
  exact ⟨mp, memoRG_frame maSch maSch_wf bmKey _ maFreeA maFreeC (by decide +kernel)
    (by decide +kernel) m m' (run_memFrame hcl hf (run_of_callW h)).1 mp hm⟩

theorem mcMR.ofClosed {p : Prog} {fs : List FnName} (hcl : closedA p mcFreeA mcFreeC fs = true)
    {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word} {m' : Mem}
    (h : callW p n f vs m = some (r, m')) (hM : ∃ mp, mcMR m mp) : ∃ mp, mcMR m' mp := by
  obtain ⟨mp, hm⟩ := hM
  exact ⟨mp, memoRG_frame mcSch mcSch_wf bmKey _ mcFreeA mcFreeC (by decide +kernel)
    (by decide +kernel) m m' (run_memFrame hcl hf (run_of_callW h)).1 mp hm⟩

/-! ## The whole arm's memos across `check_ind_decl`'s frame callees -/

/-- **`IndMemos` and `CoreMemos` across a callee of `check_ind_decl`'s frame** (`cidFreeA`,
`cidFreeC`: outside every walk memo, the stage memos and the pins). -/
theorem armMemos_call {p : Prog} {fs : List FnName} (hcl : closedA p cidFreeA cidFreeC fs = true)
    {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word} {m' : Mem}
    (h : callW p n f vs m = some (r, m')) (hI : IndMemos m) (hC : CoreMemos m) :
    IndMemos m' ∧ CoreMemos m' := by
  have hfr := (run_memFrame hcl hf (run_of_callW h)).1
  have hA : ∀ b ∈ cidFreeA, b ≠ ILFM ∧ b ≠ Stubs.CRM ∧ (b.arr < 201 ∨ 208 < b.arr) := fun b hb => by
    simp only [cidFreeA, List.mem_filter, decide_eq_true_eq] at hb
    obtain ⟨-, h1, -, -, h51, h155, -⟩ := hb
    exact ⟨h51, h155, h1⟩
  have hC' : ∀ x ∈ cidFreeC, x.toNat ≠ 52 ∧ x.toNat ≠ 158 ∧ (x.toNat < 202 ∨ 219 < x.toNat) :=
    fun x hx => by
      simp only [cidFreeC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
      obtain ⟨c, ⟨hc, h1⟩, rfl⟩ := hx
      have : (Nat.toUInt64 c).toNat = c := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
      rw [this]; omega
  exact ⟨hI.frame hfr hA hC', CoreMemos.frame hfr (by decide +kernel) (by decide +kernel) hC
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩


/-! ## The arms with leaves: `struct_used_later`, `mentions_any_const`

The arms reaching the core (or the positivity check's constructor walk) reach `struct_used_later`,
whose `hb` walk writes the `hb` memo; the tail reaches `mentions_any_const` (through
`gen_rec_check`), which writes its own memo. Their write-set facts leave those two out as leaves
(`closedAL`); the memos survive a leaf call by its own lemma. -/

/-- A triple at a property of the memory gives it across a returning call. -/
theorem callW_of_triple {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {Q R : Mem → Prop}
    (ht : ⦃fun s => Q s.mem⦄ invoke p (exec p n) f vs ⦃fun _ s => R s.mem; ⊤⦄)
    {m m' : Mem} {r : List Word} (h : callW p n f vs m = some (r, m')) (hq : Q m) : R m' := by
  have h := run_of_callW h
  simp only [run] at h
  cases hr : (invoke p (exec p n) f vs).run { mem := m, loc := Locals.init [] } with
  | error e => simp [hr, Except.map] at h
  | ok q =>
    obtain ⟨q, s'⟩ := q
    simp only [hr, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact M.of_run (P := fun s => Q s.mem) (Q := fun _ s => R s.mem) hq hr ht

/-- `struct_used_later`'s frame, at any arguments: a core frame. -/
theorem usLeaf_coreFr {p : Prog} (hus : UsF p) {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callW p n "struct_used_later" vs m = some (r, m')) : CoreFr m m' :=
  callW_of_triple (Q := CoreFr m) (R := CoreFr m) (coreFr_us hus n m vs) h (coreFr_wframe.refl m)

/-- **`struct_used_later` keeps the `hb` memo well formed**, at any arguments. -/
theorem usLeaf_hb {p : Prog} (hus : UsF p) :
    ∀ n vs m r m', callW p n "struct_used_later" vs m = some (r, m') → HbMemo m → HbMemo m' :=
  fun n vs m _ _ h => callW_of_triple (Q := fun s => HbMemo m → HbMemo s) (R := fun s => HbMemo m → HbMemo s)
    (coreHb_us hus n m vs) h id

/-- **`struct_used_later` keeps the positivity check's memos.** -/
theorem usLeaf_pos {p : Prog} (hus : UsF p) :
    ∀ n vs m r m', callW p n "struct_used_later" vs m = some (r, m') → PosMR m → PosMR m' :=
  fun n vs m r m' h hP => hP.setHb (usLeaf_coreFr hus h).mfr (usLeaf_hb hus n vs m r m' h hP.hb)

/-- **`struct_used_later` keeps the recursor check's memos.** -/
theorem usLeaf_rc {p : Prog} (hus : UsF p) :
    ∀ n vs m r m', callW p n "struct_used_later" vs m = some (r, m') → RcMR m → RcMR m' :=
  fun n vs m r m' h hR =>
    let ⟨t, ht⟩ := hR.ta
    ⟨usLeaf_pos hus n vs m r m' h hR.pos, t, taMR_mfr (usLeaf_coreFr hus h).mfr (by decide) (by decide) ht⟩

/-- The `hb` memo's two queries, as leaves (the projection guard calls them directly): a core
frame (`coreFr_hl`). -/
theorem hlLeaf_coreFr {p : Prog} (hl : ProgHas p hbLeafP) {g : FnName} (hg : g ∈ hbLeafFns) {n : Nat}
    {vs : List Word} {m m' : Mem} {r : List Word} (h : callW p n g vs m = some (r, m')) : CoreFr m m' :=
  callW_of_triple (Q := CoreFr m) (R := CoreFr m) (coreFr_hl hl hg n m vs) h (coreFr_wframe.refl m)

theorem hlLeaf_hb {p : Prog} (hl : ProgHas p hbLeafP) {g : FnName}
    (hg : g = "has_loose_b_var_b_fast" ∨ g = "has_loose_bvar_in") :
    ∀ n vs m r m', callW p n g vs m = some (r, m') → HbMemo m → HbMemo m' :=
  fun _ _ _ _ _ h hM => ((hlLeaf_run hl hg h).2 hM).2

theorem hlLeaf_pos {p : Prog} (hl : ProgHas p hbLeafP) {g : FnName}
    (hg : g = "has_loose_b_var_b_fast" ∨ g = "has_loose_bvar_in") :
    ∀ n vs m r m', callW p n g vs m = some (r, m') → PosMR m → PosMR m' :=
  fun n vs m r m' h hP => hP.setHb (hlLeaf_coreFr hl (by rcases hg with rfl | rfl <;> decide) h).mfr
    (hlLeaf_hb hl hg n vs m r m' h hP.hb)

theorem hlLeaf_rc {p : Prog} (hl : ProgHas p hbLeafP) {g : FnName}
    (hg : g = "has_loose_b_var_b_fast" ∨ g = "has_loose_bvar_in") :
    ∀ n vs m r m', callW p n g vs m = some (r, m') → RcMR m → RcMR m' :=
  fun n vs m r m' h hR =>
    let ⟨t, ht⟩ := hR.ta
    ⟨hlLeaf_pos hl hg n vs m r m' h hR.pos, t,
      taMR_mfr (hlLeaf_coreFr hl (by rcases hg with rfl | rfl <;> decide) h).mfr (by decide) (by decide) ht⟩

/-- The leaves of the arms that reach the core: `struct_used_later` and the `hb` memo's two
queries. -/
def usLeaves : List FnName := ["struct_used_later", "has_loose_bvar_in", "has_loose_b_var_b_fast"]

/-- The leaf of the `mentions_any` arm. -/
def maLeaves : List FnName := ["mentions_any_const"]

theorem HbMemo.ofClosedL {p : Prog} {fs : List FnName} (hl : ProgHas p hbLeafP) (hcl : closedAL p hbFreeA hbFreeC fs usLeaves = true)
    (hus : UsF p) {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word}
    {m' : Mem} (h : callW p n f vs m = some (r, m')) (hM : HbMemo m) : HbMemo m' :=
  callW_keepL hcl (P := HbMemo) (fun _ _ hf ⟨mp, hmp⟩ => ⟨mp, hbMR_mfr (hbFree_mfr hf) (by decide) (by decide) hmp⟩)
    (fun g hg => by
      simp only [usLeaves, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact usLeaf_hb hus
      · exact hlLeaf_hb hl (.inr rfl)
      · exact hlLeaf_hb hl (.inl rfl)) hf h hM

theorem PosMR.ofClosedL {p : Prog} {fs : List FnName} (hl : ProgHas p hbLeafP) (hcl : closedAL p posFreeA posFreeC fs usLeaves = true)
    (hus : UsF p) {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word}
    {m' : Mem} (h : callW p n f vs m = some (r, m')) (hM : PosMR m) : PosMR m' :=
  callW_keepL hcl (P := PosMR)
    (fun _ _ hf hP => hP.mfr (posFree_mfr hf) (by simp [PosAv, MAM, NOM, DPM, RAM, HBM, RFM, TAM, MCM]))
    (fun g hg => by
      simp only [usLeaves, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact usLeaf_pos hus
      · exact hlLeaf_pos hl (.inr rfl)
      · exact hlLeaf_pos hl (.inl rfl)) hf h hM

theorem RcMR.ofClosedL {p : Prog} {fs : List FnName} (hl : ProgHas p hbLeafP) (hcl : closedAL p rcFreeA rcFreeC fs usLeaves = true)
    (hus : UsF p) {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word}
    {m' : Mem} (h : callW p n f vs m = some (r, m')) (hM : RcMR m) : RcMR m' :=
  callW_keepL hcl (P := RcMR) (fun _ _ hf hR => by
      have hfr := rcFree_mfr hf
      obtain ⟨t, ht⟩ := hR.ta
      exact ⟨hR.pos.mfr hfr (by simp [PosAv, NOM, DPM, RAM, HBM, RFM, MAM, MCM]), t,
        taMR_mfr hfr (by decide) (by decide) ht⟩)
    (fun g hg => by
      simp only [usLeaves, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact usLeaf_rc hus
      · exact hlLeaf_rc hl (.inr rfl)
      · exact hlLeaf_rc hl (.inl rfl)) hf h hM

theorem maMR.ofClosedL {p : Prog} {fs : List FnName} (hcl : closedAL p maFreeA maFreeC fs maLeaves = true)
    (hma : MaProg p) {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word}
    {m' : Mem} (h : callW p n f vs m = some (r, m')) (hM : ∃ mp, maMR m mp) : ∃ mp, maMR m' mp :=
  callW_keepL hcl (P := fun m => ∃ mp, maMR m mp)
    (fun _ _ hf ⟨mp, hm⟩ => ⟨mp, memoRG_frame maSch maSch_wf bmKey _ maFreeA maFreeC (by decide +kernel)
      (by decide +kernel) _ _ hf mp hm⟩)
    (fun g hg => by simp only [maLeaves, List.mem_singleton] at hg; subst hg; exact maLeaf_keep hma) hf h hM

end L.Ind
