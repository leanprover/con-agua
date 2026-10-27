import ConAgua.Arena.LoopT
import ConAgua.Arena.IndInstallSpec.TabsProg

/-!
# The inductive arm's memos across its calls (lane `indstaget`)

What `cidW_okC` needs to hand back `IndMemos` and `CoreMemos` (`IndArmSpec`'s post) beyond the
posts of its callees: write-set frames (program facts `closedA …`, decided for the checker's
program) for the memos a call does not write. Measured on the checker's program, each memo array /
epoch word of `IndMemos` and `CoreMemos` is written only by its own `…_put` / `…_clear`; the
recursor stage's memos (`RcMR`) are written in `check_block_tail` only by `check_block_rec` and
(`hb`) `check_block_tables`; `mentions_any`'s (`maMR`) only by `block_raw_rec`; `mentions_const`'s
(`mcMR`) by nothing under `check_ind_decl`.
-/


namespace L.Ind

open L.Arena

/-! ## `RcMR` across a writer of the `hb` memo alone -/

/-- Every word array below 320 (both tiers) but the recursor check's memos other than `hb`'s. -/
def rcHbFreeA : List ArrId := (List.range 388).filter (fun b => b ∉ [NOM, DPM, RAM, RFM, TAM])
/-- Every `CTL` word below 256 but those memos' control words. -/
def rcHbFreeC : List Word :=
  ((List.range 256).filter (fun c => c ∉ [204, 206, 208, 210, 212, 213, 218, 219])).map Nat.toUInt64

theorem rcHbFree_mfr {m m' : Mem} (h : MemFrame rcHbFreeA rcHbFreeC m m') :
    MFr [MAM, MCM, HBM] [202, 203, 205, 207, 209, 211, 214, 215, 216, 217] m m' := by
  refine ⟨rcHbFreeA, rcHbFreeC, h, fun b hb => ?_, fun x hx => ?_⟩
  · simp only [rcHbFreeA, List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_cons,
      List.not_mem_nil, or_false] at hb
    simp only [NOM, DPM, RAM, HBM, RFM, TAM, MAM, MCM, ArrId] at hb ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
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

/-- Every word array below 320 (both tiers) but `mentions_any`'s memo. -/
def maFreeA : List ArrId := (List.range 388).filter (· ≠ MAM)
/-- Every `CTL` word below 256 but its control words. -/
def maFreeC : List Word := ((List.range 256).filter (fun c => c ≠ 202 ∧ c ≠ 203)).map Nat.toUInt64

/-- Every word array below 320 (both tiers) but `mentions_const`'s memo. -/
def mcFreeA : List ArrId := (List.range 388).filter (· ≠ MCM)
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
  have hA : ∀ b ∈ cidFreeA, b ≠ 51 ∧ b ≠ 155 ∧ (b < 201 ∨ 208 < b) := fun b hb => by
    simp only [cidFreeA, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb
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

end L.Ind
