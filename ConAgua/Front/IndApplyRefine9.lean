module

public import ConAgua.Front.IndApplyRefine8
import ConAgua.Front.IndApplyRefine6
public import ConAgua.Verdict.FrontRecsE
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Checker.NoVerdictTree
import ConAgua.Front.IndApplyRefine
import all ConAgua.Front.IndApply

@[expose] public section

/-!
# The apply step of an `inductive` line against the twin, IX: `validate_ind_d` refines `validateIndD`

`validate_ref`, one refinement for both outcomes of `validate_ind_d`'s unified model (with
`vi_tail`'s, unfolded) on the records of an inductive line (`IndFR`): an ok value establishes the
clean facts `VFacts` of the twin's validation (`IndValidTwin.lean`), so `validateIndD` succeeds
with the ordered constructors, which the model left as record pointers at `oo`; an error of class
`≠ 0` is `validateIndD`'s record verdict at the check that failed (`FrontOrderE.lean`,
`FrontRecsE.lean`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true


namespace L.Front.Ind

theorem psum_fpos {b : ByteArray} {m : Mem} {to : Word} {tys : List IndTypeRec}
    (hF : ∀ k (hk : k < tys.length), TyF b m (to.toNat + 11 * k) tys[k])
    {LS : List (List NIdx)} (hLS : LS.map List.length = tys.map fun t : IndTypeRec => t.ctors.length) :
    ∀ i, i ≤ tys.length → psum m to i = fpos LS i := by
  have hl : LS.length = tys.length := by
    have := congrArg List.length hLS; simpa using this
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [psum_succ, fpos_succ LS i (by omega), ih (by omega)]
    congr 1
    obtain ⟨-, h4, -⟩ := hF i (by omega)
    have := congrArg (fun l => l[i]?) hLS
    simp only [List.getElem?_map, List.getElem?_eq_getElem (show i < LS.length by omega),
      List.getElem?_eq_getElem (show i < tys.length by omega), Option.map_some, Option.some.injEq] at this
    rw [this]; exact h4

theorem ordList_get (m : Mem) (oo co : Nat) (cts : List IndCtorRec) (l p : Nat)
    (hp : p < (ordList m oo co cts l).length) :
    (ordList m oo co cts l)[p] = cts.getD (((wd m IFL (oo + p)).toNat - co) / 10) default := by
  simp [ordList]

/-- A write set of the level heap only is an `IExt`. -/
theorem iext_of_heap {m m' : Mem} (h : MemFrame [LH] [192] m m') : IExt m m' := by
  have hI : m'.arr64 IFL = m.arr64 IFL := h.arr IFL (by decide) (by decide)
  refine ⟨h.mono (by simp) (by simp), by simp [topN, wd, hI], fun i _ _ => by simp [wd, hI]⟩


/-! ## The unified models -/

l_model viTail_specE (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_tail ↦ viTailE]
  specs [storeFuel_spec p hL n, viOrder_specE p hL n, kExp_spec p hL n, recs_specE p hL n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE]
  unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model validate_specE (p : Prog) (hL : IndApplyLookups p)
  fns [hL.validate_ind_d ↦ validateE]
  specs [viUnsafe_specE p hL.vi_unsafe n, viNparams_specE p hL n, map_spec p hL n, listed_spec p hL n,
    nodup_spec p hL n, viTail_specE p hL n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE]
  unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-! ## `validate_ind_d` -/

/-- `ifl_nodup` returning `0`: two equal words. -/
theorem nodupW_zero : ∀ (n : Nat) (m : Mem) (o l j : Word), nodupW n m o l j = some 0 →
    o.toNat + l.toNat < 2 ^ 64 →
    ∃ i i', j.toNat ≤ i ∧ i < i' ∧ i' < l.toNat ∧ wd m IFL (o.toNat + i) = wd m IFL (o.toNat + i') := by
  intro n
  induction n with
  | zero => intro m o l j h; simp [nodupW] at h
  | succ n ih =>
    intro m o l j h hb
    simp only [nodupW] at h
    split at h
    · cases h
    rename_i hlj
    have hjl := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlj)
    have hj1 := wsucc j l (UInt64.not_le.mp hlj)
    have hoj : (o + j).toNat = o.toNat + j.toNat := widx2 _ _ (by omega)
    rcases hc : containsW n m o l (rdW (m.arr64 IFL) (o + j)) (j + 1) with _ | c <;> simp only [hc, nodupK, reduceCtorEq] at h
    obtain ⟨c1, -⟩ := containsW_facts n m o l _ _ c hc hb
    rw [hj1] at c1
    split at h
    · rename_i hc0
      obtain ⟨k, k1, k2, k3⟩ := c1 hc0
      refine ⟨j.toNat, k, Nat.le_refl _, by omega, k2, ?_⟩
      rw [k3, wd_eq, hoj]
    · obtain ⟨i, i', h1, h2, h3, h4⟩ := ih m o l (j + 1) h hb
      rw [hj1] at h1
      exact ⟨i, i', by omega, h2, h3, h4⟩

/-- Two equal words make a duplicate in the decoded slice. -/
theorem islice_not_nodup {m : Mem} {o l : Nat} {i i' : Nat} (h2 : i < i') (h3 : i' < l)
    (h4 : wd m IFL (o + i) = wd m IFL (o + i')) : ¬ (islice (k := .name) m o l).Nodup := by
  rw [List.nodup_iff_eq_of_getElem_eq]
  intro hn
  have := hn i i' (by rw [islice_length]; omega) (by rw [islice_length]; omega)
    (by rw [islice_get, islice_get, h4])
  omega

/-- The twin facts `validate_ind_d`'s error half takes (the messages' name reads). -/
def XV (st : StateD) (a : AState) : Prop := NamesRead st a ∧ NamesReadR st a ∧ ViewReadR a

theorem R_DUPLICATE_cls : (Err.abort R_DUPLICATE_CONSTRUCTOR_NAME).cls = 1 := by decide
theorem R_BLOCK_cls : (Err.abort R_THE_INDUCTIVE_BLOCK).cls = 1 := by decide

/-- **`validate_ind_d`'s ok half**: `validateIndD` succeeds with the ordered constructors, which
the model left as record pointers at `oo` (the first result word), and `nPd` (the second). -/
structure ValidatePost (st : StateD) (a : AState) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (co : Word) (m : Mem) (v : List Word × Mem) : Prop where
  twin : ∃ ordered : List IndCtorRec,
    (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = .ok (.inr (ordered, (v.1.tail.headD 0).toNat), a) ∧
      ordered.length = cts.length ∧
      ∀ p (hp : p < ordered.length), ∃ k, ∃ _ : k < cts.length,
        wd v.2 IFL ((v.1.headD 0).toNat + p) = co + 10 * UInt64.ofNat k ∧ ordered[p] = cts[k]
  ext : IExt m v.2
  top : TopOK v.2
  off : 1 ≤ (v.1.headD 0).toNat
  room : (v.1.headD 0).toNat + cts.length ≤ topN v.2 IFL + 1
  np : (v.1.tail.headD 0).toNat < 10 ^ 18

/-- **`validate_ind_d`, both outcomes**: on the records of an inductive line (`IndFR`), the
model's ok value is `validateIndD`'s success (`ValidatePost`), its error (of class `≠ 0`, at the
twin facts `XV`) `validateIndD`'s record verdict. -/
@[refines ConRon.Arena.Frontend.validateIndD]
theorem validate_ref {b : ByteArray} {m : Mem} {a : AState} {st : StateD} (hR : ArenaR m a)
    (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a) (hT : TopOK m)
    {to tn co cn ro rn : Word} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} (hF : IndFR b m to tn co cn ro rn tys cts rcs) (hIFR : topN m IFR < 2 ^ 62)
    (p : Prog) (n : Nat) :
    RefC (XV st a) (validateE p n m to tn co cn ro rn) (ValidatePost st a tys cts rcs co m)
      (L.Front.VerdictClaimL (ConRon.Arena.Frontend.validateIndD st tys cts rcs) a) := by
  sorry

end L.Front.Ind
