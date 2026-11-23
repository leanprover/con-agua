module

public import ConAgua.Arena.IndDeclConstsFrame
public import ConAgua.Arena.IndInstallSpec.LeafKeep
import ConAgua.Arena.IlpRdReal

@[expose] public section

/-!
# The ι reading rule, part 3: the stage's memos across `block_reads_at` (lane ronsync8)

`block_reads_at`'s call closure writes the walk memos (`instantiate_lift_fast`, `inst_lp_core`,
kept by its refinement: `AbsOK`) and `mentions_any`'s memo (`mentions_any_const`, through
`block_constants`), so it is outside `check_ind_decl`'s frame (`cidFreeA`). What `cid_ref` needs
besides `AbsOK` after it, the stage's memos and the `constsResolveF` memo (`BrMem`), it keeps by a
write set with those three walks as leaves (`briA`, `briC`, `briLeaves`; decided for the checker's
program in `Checker/IotaArmClosed.lean`).
-/

namespace L.Ind

open L.Arena

/-- The arrays the closure may write: all but the stage's memos (`201‥208`) and `CRM`. -/
def briA : List TieredArray :=
  checkerWordArrays.filter fun b => decide ((b.arr < 201 ∨ 208 < b.arr) ∧ b ≠ Stubs.CRM)

/-- The `CTL` words it may write: all below 1024 but the stage memos' (`202‥219`) and `158`. -/
def briC : List Word :=
  ((List.range 1024).filter fun c => decide ((c < 202 ∨ 219 < c) ∧ c ≠ 158)).map Nat.toUInt64

/-- The leaves: the walks that write a memo of their own. -/
def briLeaves : List FnName := ["mentions_any_const", "inst_lp_core", "instantiate_lift_fast"]

/-- What the closure keeps beside `AbsOK`. -/
structure BrMem (m : Mem) : Prop where
  stage : StageMemos m
  cr : L.Stubs.CrOK m

theorem briA_spec {b : TieredArray} (h : b ∈ briA) : (b.arr < 201 ∨ 208 < b.arr) ∧ b ≠ Stubs.CRM := by
  simpa [briA] using (List.mem_filter.mp h).2

theorem briC_spec {x : Word} (h : x ∈ briC) : (x.toNat < 202 ∨ 219 < x.toNat) ∧ x.toNat ≠ 158 := by
  simp only [briC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨c, ⟨hc, h1⟩, rfl⟩ := h
  have : (Nat.toUInt64 c).toNat = c := by simp; omega
  rw [this]; exact h1

theorem BrMem.frameBri {m m' : Mem} (h : BrMem m) (hf : MemFrame briA briC m m') : BrMem m' :=
  ⟨h.stage.frame hf (fun _ hb => (briA_spec hb).1) (fun _ hx => (briC_spec hx).1),
    CrOK.frame h.cr hf (fun hb => (briA_spec hb).2 rfl)
      (fun hx => (briC_spec hx).2 (by decide))⟩

theorem brMem_ma {p : Prog} (hM : MaProg p) {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "mentions_any_const" vs m = some (r, m')) (h : BrMem m) : BrMem m' := by
  have hf := maLeaf_frame hM hc
  obtain ⟨⟨hpos, hma, ⟨mpc, hmc⟩, ⟨mpt, hta⟩⟩, hcr⟩ := h
  exact ⟨⟨hpos.mfr (ma_mfr hf) (by decide), maLeaf_keep hM _ _ _ _ _ hc hma,
      ⟨mpc, memoRG_frame mcSch mcSch_wf _ _ _ _ (by decide) (by decide) m m' hf mpc hmc⟩,
      ⟨mpt, memoRG_frame taSch taSch_wf _ _ _ _ (by decide) (by decide) m m' hf mpt hta⟩⟩,
    CrOK.frame hcr hf (by decide) (by decide)⟩

theorem brMem_ilp {p : Prog} (hI : IlpfF p) {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "inst_lp_core" vs m = some (r, m')) (h : BrMem m) : BrMem m' := by
  have hf := instLPCore_frame (hp := hI) hc
  exact ⟨h.stage.frame hf ilpfA_stage ilpfC_stage, CrOK.frame h.cr hf (by decide) (by decide)⟩

theorem brMem_i1 {p : Prog} (hI : I1lF p) {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "instantiate_lift_fast" vs m = some (r, m')) (h : BrMem m) : BrMem m' := by
  have hf := i1lF_call hI hc
  have hA : ∀ b ∈ i1lA, b.arr < 201 ∨ 208 < b.arr := fun b hb => by
    have := i1lA_mem b hb
    simp only [dcMemArrOk, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not] at this
    omega
  have hC : ∀ x ∈ i1lC, x.toNat < 202 ∨ 219 < x.toNat := fun x hx => by
    have := i1lC_mem x hx
    simp only [dcMemCtlOk, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not] at this
    omega
  have hcrm : (Stubs.CRM : TieredArray) ∉ i1lA := fun hb => by
    have := i1lA_mem _ hb; revert this; decide
  have h158 : (158 : Word) ∉ i1lC := fun hx => by
    have := i1lC_mem _ hx; revert this; decide
  exact ⟨h.stage.frame hf hA hC, CrOK.frame h.cr hf hcrm h158⟩

/-- **A call of a function of the closure keeps `BrMem`.** -/
theorem bri_keep {p : Prog} {fs : List FnName} (hcl : closedAL p briA briC fs briLeaves = true)
    (hM : MaProg p) (hI : IlpfF p) (hi : I1lF p) {f : FnName} (hf : f ∈ fs) {n : Nat}
    {vs : List Word} {m m' : Mem} {r : List Word} (h : callW p n f vs m = some (r, m'))
    (h0 : BrMem m) : BrMem m' :=
  callW_keepL hcl (P := BrMem) (fun _ _ hfr hx => hx.frameBri hfr)
    (fun g hg n vs m₁ r m₂ hc hx => by
      simp only [briLeaves, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact brMem_ma hM hc hx
      · exact brMem_ilp hI hc hx
      · exact brMem_i1 hi hc hx) hf h h0

end L.Ind
