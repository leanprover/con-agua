module

public import ConAgua.Arena.DefEqStuckWith
public import ConAgua.Arena.IndRecRead
import ConAgua.Arena.EtaRescueRef
import ConAgua.Arena.DefEqLeaves2
import ConAgua.Arena.RefWalk
import ConRon.Bridge.Grind

@[expose] public section

/-!
# `struct_eta_cert_go` refines `structEtaCertWith`'s keys (lane `defeq`, helper `defeq-top`)

The twin's `match ← viewLsLen us' …; if … then …` past the family's projection table (`setGoT`):
the table's constructor and parameter count, the level list's length, the level parameters. The
`viewLsLen` read has no effect (`setGoT_run`), so L's pure calls (`er_slice_eq`, `ls_node`) run first.
The decoded records: `decCI_ctorLp`, `decCI_indCaps` (`IndRecRead.lean`), `tblFound_words`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin -/

/-- **`structEtaCertWith` once both heads, the family's table and the spines are known**,
copied. -/
def setGoT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
    (cvc : IConstantVal) (T : NIdx) (us' : LsIdx) (cvT : IConstantVal) (caps : IIndCaps)
    (tbl : IProjTable) (aargs targs : List EIdx) : AM Bool := do
  match ← viewLsLen us' with
  | none => failDanglingLs
  | some uslen =>
  if caps.eta = true ∧ tbl.ctor = c ∧
      targs.length = tbl.numParams ∧
      uslen = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams then
    setTailT r fe depth b us T us' tbl.numParams tbl.numFields aargs targs
  else pure false

/-- `setGoT`'s test and tail, at the level list's length. -/
def setGoK (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
    (cvc : IConstantVal) (T : NIdx) (us' : LsIdx) (cvT : IConstantVal) (caps : IIndCaps)
    (tbl : IProjTable) (aargs targs : List EIdx) (uslen : Nat) : AM Bool :=
  if caps.eta = true ∧ tbl.ctor = c ∧
      targs.length = tbl.numParams ∧
      uslen = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams then
    setTailT r fe depth b us T us' tbl.numParams tbl.numFields aargs targs
  else pure false

/-- **`setGoT` past the level list's length**, where it has one. -/
theorem setGoT_run (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
    (cvc : IConstantVal) (T : NIdx) (us' : LsIdx) (cvT : IConstantVal) (caps : IIndCaps)
    (tbl : IProjTable) (aargs targs : List EIdx) {a : AState} (uslen : Nat)
    (hv : a.store.lss.viewLen us' = some uslen) :
    (setGoT r fe depth b c us cvc T us' cvT caps tbl aargs targs).run a =
      (setGoK r fe depth b c us cvc T us' cvT caps tbl aargs targs uslen).run a := by
  simp only [setGoT, StateT.run_bind, viewLsLen_run, hv]
  rfl

section sgKarms
variable (m0 : Mem) (c q tq tn lpe uslen : Word)

/-- The tests of `struct_eta_cert_go`, all passed. -/
def sgOK : Prop :=
  erRd m0 (q + 5) ≠ 0 ∧ erRd m0 (tq + 5) = c ∧ tn = erRd m0 (tq + 4) ∧ uslen = erRd m0 (q + 3) ∧
    lpe ≠ 0

end sgKarms

section secgTests
variable (p : Prog) (n : Nat) (m0 : Mem) (mode vis d b us c T q tq us2 ao an to tn lpe : Word)
  (r : List Word) (m : Mem)

/-- `struct_eta_cert_go`'s tests, all passed: the tail. -/
theorem secgE_yes (h : sgOK m0 c q tq tn lpe (r.tail.headD 0)) :
    secgE.k_ls_node p n mode vis d b us c T us2 ao an to tn (erRd m0 (q + 5))
      (erRd m0 (tq + 5)) (erRd m0 (tq + 4)) (erRd m0 (tq + 6))
      (erRd m0 (q + 3)) lpe (.ok (r, m)) =
    secgE.k_struct_eta_cert_tail p (sectE p n m mode vis d b us T us2 ao an to tn
      (erRd m0 (tq + 4)) (erRd m0 (tq + 6))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [secgE.k_ls_node, h1, h2, h3, h4, h5, ne_eq, not_true_eq_false, ↓reduceIte]

/-- `struct_eta_cert_go`'s tests, one failed: `false`. -/
theorem secgE_no (h : ¬ sgOK m0 c q tq tn lpe (r.tail.headD 0)) :
    secgE.k_ls_node p n mode vis d b us c T us2 ao an to tn (erRd m0 (q + 5))
      (erRd m0 (tq + 5)) (erRd m0 (tq + 4)) (erRd m0 (tq + 6))
      (erRd m0 (q + 3)) lpe (.ok (r, m)) = .ok ([0], m) := by
  unfold secgE.k_ls_node
  by_cases h1 : erRd m0 (q + 5) = 0
  · simp only [h1, ↓reduceIte]
  by_cases h2 : erRd m0 (tq + 5) ≠ c
  · simp only [h1, h2, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h3 : tn ≠ erRd m0 (tq + 4)
  · simp only [h1, h2, h3, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h4 : r.tail.headD 0 ≠ erRd m0 (q + 3)
  · simp only [h1, h2, h3, h4, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h5 : lpe = 0
  · simp only [h1, h2, h3, h4, h5, ↓reduceIte]
  exact absurd ⟨h1, by simpa using h2, by simpa using h3, by simpa using h4, h5⟩ h

end secgTests

/-- **`struct_eta_cert_go` refines `setGoT`, both outcomes** (the projections' slice left on the
stack): the errors are `struct_eta_cert_tail`'s. -/
@[refines_part ConRon.Arena.structEtaCertWith "the keys, then the tail (setGoT)"]
theorem secg_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d b us c pc T q tq us2 ao an to tn : Word) (aargs targs : Array EIdx)
    (cvc : IConstantVal) (np nf : Nat) (cvT : IConstantVal) (caps : IIndCaps) (tbl : IProjTable)
    (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hus : HW us)
    (hcw : HW c) (hT : HW T) (hus2 : HW us2)
    (hvus : ∃ x c', a₀.store.view x = some (.const c' (decI us)))
    (hvus2 : ∃ x c', a₀.store.view x = some (.const c' (decI us2)))
    {fam : NIdx} (hcvc : decCI (erecP s₀.mem) pc.toNat = some (.ctorInfo cvc np nf fam))
    (hcvT : decCI (erecP s₀.mem) q.toNat = some (.indInfo cvT caps))
    (htbl : tblFound s₀.mem tq = some tbl)
    (ha : SpineR s₀.mem ao an aargs) (ht : SpineR s₀.mem to tn targs)
    (hat : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat)
    (htt : to.toNat + tn.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (SetG p n) (secgE p (n + 1) s₀.mem mode vis d b us c pc T q tq us2 ao an to tn)
      (setGoT (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE b) (decI c) (decI us) cvc (decI T)
        (decI us2) cvT caps tbl aargs.toList targs.toList) a₀
      (GrowPost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hIR := decCI_indCaps (erRdOK _) hcvT
  have hCL := decCI_ctorLp (erRdOK _) hcvc
  obtain ⟨-, hTp, hTcw, hTc, hTf⟩ := tblFound_words htbl
  simp only [secgE]
  cases n with
  | zero =>
    exact RefE.onlySim (Q := fun _ _ => False) (fun _ => rfl)
      (fun _ _ h => by rw [callW_zero] at h; cases h) fun _ _ h => h.elim
  | succ n' =>
  -- `er_slice_eq`: memory unchanged
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (erSliceEq_refines p hq.ers n' ⟨s₀.mem, Locals.init []⟩ _ _ _ _ cvc.levelParams cvT.levelParams
      hS.erec hCL hIR.lp) h) fun r₁ m₁ ⟨t₁, ht₁, hm₁, _, hr₁, _⟩ => ?_
  obtain rfl : m₁ = s₀.mem := by rw [← ht₁]; exact hm₁
  dsimp only [secgE.k_er_slice_eq]
  -- `ls_node`: memory unchanged, the length
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (lsNode_spec p hq.leaf.core.lsn (n' + 1) ⟨s₀.mem, Locals.init []⟩ us2) h)
    fun r₄ m₄ ⟨t₄, ht₄, ht₄s, hne, hr₄⟩ => ?_
  obtain rfl : m₄ = s₀.mem := by rw [← ht₄, ht₄s]
  rw [hr₄] at hne
  have hvl := defeq_lsNodeW_viewLen hS.arena.base hus2 hne
  rw [← hr₄] at hvl
  refine RefE.of_run_eq (setGoT_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hvl) ?_
  unfold setGoK
  -- the tests
  have hlenT : targs.toList.length = tn.toNat := by simpa using ht.size
  have hlpT : cvT.levelParams.length = (erRd s₀.mem (q + 3)).toNat :=
    hslice?_lenR hIR.lp
  have hiff : (caps.eta = true ∧ tbl.ctor = decI c ∧
      targs.toList.length = tbl.numParams ∧
      (r₄.tail.headD 0).toNat = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams) ↔
      sgOK s₀.mem c q tq tn (r₁.headD 0) (r₄.tail.headD 0) := by
    unfold sgOK
    rw [hIR.eta, hTc, hlenT, hTp, hlpT]
    have e2 : decI (erRd s₀.mem (tq + 5)) = (decI c : NIdx) ↔
        erRd s₀.mem (tq + 5) = c :=
      ⟨fun h => decI_inj hTcw hcw h, fun h => by rw [h]⟩
    have e7 : cvc.levelParams = cvT.levelParams ↔ r₁.headD 0 ≠ 0 := by
      have h1 : decBool r₁ = decide (cvc.levelParams = cvT.levelParams) := hr₁
      unfold decBool at h1
      by_cases he : cvc.levelParams = cvT.levelParams
      · simp only [he, decide_true, bne_iff_ne, ne_eq] at h1; exact ⟨fun _ => h1, fun _ => he⟩
      · simp only [he, decide_false, bne_eq_false_iff_eq] at h1
        exact ⟨fun h => absurd h he, fun h => absurd h1 h⟩
    rw [e2, e7]
    simp only [bne_iff_ne, ne_eq, UInt64.toNat_inj]
  simp only [L.Ind.erRd_foldN]
  by_cases hok : sgOK s₀.mem c q tq tn (r₁.headD 0) (r₄.tail.headD 0)
  · rw [secgE_yes (h := hok), ite_eq_left (hiff.mpr hok)]
    rw [hTp, hTf]
    exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ n')) rfl
      (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
      (sect_ref p hi hc n' (hk.mono (by omega)) F ⟨s₀.mem, Locals.init []⟩ _ dn vis fe M eb mode d b us
        T us2 ao an to tn _ _ aargs targs (by omega) (by omega) ⟨hS, hs.mode4, hs.eb_mode⟩ hb hus hT
        hus2
        (by obtain ⟨x, c', hx⟩ := hvus
            exact (hc.den _ _ _ _ _ _ _ hS).constLs _ _ _ hx)
        (by obtain ⟨x, c', hx⟩ := hvus2
            exact (hc.den _ _ _ _ _ _ _ hS).constLs _ _ _ hx)
        ha ht hat htt)
  · rw [secgE_no (h := hok), ite_eq_right (fun h => hok (hiff.mp h))]
    exact RefE.ret rfl (GrowPost.of_core (CorePost.ret hS rfl hw0))

end L.Arena
