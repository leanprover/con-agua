module

public import ConAgua.Arena.WhnfIota
public import ConAgua.Arena.DeclCanonSpec
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.IndRecRead
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.DeclArmsCanon
import all ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# `eta_rescue_table`: the structure-η rescue's standing condition (`etaRescueTable?`)

The table's constructor tested, the constructor's and the family's level parameters compared as `EREC` slices (`er_sl_eq`), the
`And.intro` pin read last.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- `er_sl_eq`'s spec at its own lookup (`StubIndRefine.erSlEq_spec'`'s, for callers that cannot
import that file). -/
theorem erSlEq_spec (p : Prog) (hp : p.lookup "er_sl_eq" = some L.Ind.erSlEq) (n : Nat) :
    ∀ (s₀ : St) (o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "er_sl_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if L.Ind.erSlEqB (erRd s₀.mem) o1 l1 o2 l2 then 1 else 0; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o1 l1 o2 l2; rw [invoke_eq _ hp]; simp only [callFn, L.Ind.erSlEq]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o1 l1 o2 l2
    rw [invoke_eq _ hp]
    simp only [callFn, L.Ind.erSlEq]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, ih] <;>
      finish (gen := 20) [rdW_eq, erRd]

/-- **`eta_rescue_table`'s model**: `er_sl_eq` and `pin_at` lifted. -/
l_model ertW_spec (p : Prog) (hf : p.lookup "eta_rescue_table" = some etaRescueTableL)
  fns [hf ↦ ertW] specs [callW_spec p n "er_sl_eq", callW_spec p n "pin_at"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- A `ctorInfo` record's constant value decodes at `q + 1`. -/
theorem decCI_ctor_cv {R : Nat → Option Word} {q : Nat} {cv : IConstantVal} {nP nF : Nat}
    {fam : NIdx} (h : decCI R q = some (.ctorInfo cv nP nF fam)) : decCV R (q + 1) = some cv := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, -, h⟩ := h
  rcases k with _ | _ | _ | _ | _ | _ | k <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq, and_false, exists_false] at h
  obtain ⟨cv', hcv, _, -, _, -, _, -, he⟩ := h
  cases he; exact hcv

/-- **The words of a found table** (`find_table`'s answer `tq ≠ 0`, the record at `tq - 1`): the
parameter count, the constructor and the field count, read through the handle. -/
theorem tblFound_words {m : Mem} {tq : Word} {tb : IProjTable} (h : tblFound m tq = some tb) :
    tq ≠ 0 ∧ tb.numParams = (erRd m (tq + (ProjTbl.numParams - 1))).toNat ∧
      HW (erRd m (tq + (ProjTbl.ctor - 1))) ∧ tb.ctor = decI (erRd m (tq + (ProjTbl.ctor - 1))) ∧
      tb.numFields = (erRd m (tq + (ProjTbl.numFields - 1))).toNat := by
  have h0 : tq ≠ 0 := by rintro rfl; simp [tblFound] at h
  simp only [tblFound, h0, ↓reduceIte] at h
  exact ⟨h0, decTbl_rd1 (erRdOK m) h0 h⟩

/-- **`eta_rescue_table` refines `etaRescueTable?`** (memory and twin state kept): the answer is
`find_table`'s `tq` or `0`, decoded as the twin's `Option IProjTable`. -/
@[refines ConRon.Arena.etaRescueTable?]
theorem ert_ok {p : Prog} (hes : p.lookup "er_sl_eq" = some L.Ind.erSlEq)
    (hpa : p.lookup "pin_at" = some pinAtL) {n : Nat} {m m' : Mem} {a : AState} (hP : PinsR m a.pins)
    {tq ctor cq q : Word} (hctor : HW ctor) {cvj : IConstantVal} {nP nF : Nat} {cvT : IConstantVal}
    {caps : IIndCaps} {fam : NIdx} (hcj : decCI (erecP m) cq.toNat = some (.ctorInfo cvj nP nF fam))
    (hci : decCI (erecP m) q.toNat = some (.indInfo cvT caps))
    (htq : tq ≠ 0 → ∃ tb, decTbl (erecP m) (tq.toNat - 1) = some tb) {w : Word}
    (h : ertW p n m tq ctor cq q = some (w, m')) :
    m' = m ∧ (etaRescueTable? (tblFound m tq) (decI ctor) cvj cvT caps).run a =
      .ok (tblFound m w, a) ∧ (w ≠ 0 → ∃ tb, tblFound m w = some tb) := by
  rcases n with _ | n
  · simp [ertW] at h
  by_cases g0 : tq = 0
  · rw [ertW.arm1 _ _ _ _ _ _ _ g0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst g0
    exact ⟨rfl, rfl, fun h => absurd rfl h⟩
  obtain ⟨tb, htb⟩ := htq g0
  have hT : tblFound m tq = some tb := by simp [tblFound, g0, htb]
  obtain ⟨-, -, hcw, hcd, -⟩ := tblFound_words hT
  have hrec := decCI_indCaps (erRdOK m) hci
  obtain ⟨hlj, -⟩ := decCV_rd (erRdOK m) (L.Arena.decCI_ctor_cv hcj)
  have hlT := hrec.lp
  have heta := hrec.eta
  have hz : tblFound m 0 = none := by simp [tblFound]
  rw [hT]
  by_cases g1 : erRd m (q + (CI.indCaps + Caps.eta)) = 0
  · rw [ertW.arm2 _ _ _ _ _ _ _ g0 g1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_, fun h => absurd rfl h⟩
    have : caps.eta = false := by rw [heta, g1]; rfl
    simp [etaRescueTable?, this, hz]; rfl
  by_cases g2 : erRd m (tq + (ProjTbl.ctor - 1)) ≠ ctor
  · rw [ertW.arm3 _ _ _ _ _ _ _ g0 g1 g2] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_, fun h => absurd rfl h⟩
    have : (tb.ctor == decI ctor) = false := by
      rw [hcd]; simpa using fun e => g2 ((decI_inj_iff hcw hctor).mp e)
    simp [etaRescueTable?, this, hz]; rfl
  have g2' : erRd m (tq + (ProjTbl.ctor - 1)) = ctor := by simpa using g2
  rw [ertW.arm4 _ _ _ _ _ _ _ g0 g1 g2'] at h
  have hE : caps.eta = true := by rw [heta]; simpa using g1
  have hC : (tb.ctor == decI ctor) = true := by rw [hcd, g2']; simp
  simp only [L.Ind.erRd_foldN] at h
  rcases c1 : callW p n "er_sl_eq" [erRd m (cq + 2), erRd m (cq + 3), erRd m (q + 2),
      erRd m (q + 3)] m with _ | ⟨r1, m1⟩
  · rw [c1, ertW.k_er_sl_eq.none] at h; cases h
  rw [c1] at h
  obtain ⟨s1, hs1, -, hm1, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Arena.erSlEq_spec p hes n ⟨m, Locals.init []⟩ _ _ _ _) c1
  have hm1' : m = m1 := (hs1 ▸ hm1).symm
  subst hm1'
  rw [L.Ind.erSlEqB_ok (erRdOK m) hlj hlT] at hr1
  by_cases g3 : cvj.levelParams = cvT.levelParams
  · rw [ertW.k_er_sl_eq.arm2 _ _ _ _ _ _ (by rw [hr1]; simp [g3])] at h
    rcases c2 : callW p n "pin_at" [48] m with _ | ⟨r2, m2⟩
    · rw [c2, ertW.k_pin_at.none] at h; cases h
    obtain ⟨s2, hs2, hm2, -, hr2, hpin⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (pinAt_refines p hpa n ⟨m, Locals.init []⟩ a hP 48) c2
    have hm2' : m2 = m := hs2 ▸ hm2
    have hpin' : pinAndIntro.run a = .ok (decI (r2.headD 0), a) := hpin
    have hiff : ((decI ctor : NIdx) != decI (r2.headD 0)) = (ctor != r2.headD 0) := by
      unfold bne; congr 1
      exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact decI_inj_iff hctor hr2)
    rw [c2] at h
    simp only [etaRescueTable?]
    rw [ite_eq_left (by simp [hE, hC, g3]), StateT.run_bind, hpin']
    by_cases e : ctor = r2.headD 0
    · rw [ertW.k_pin_at.arm1 _ _ _ _ _ e] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hb : ((decI ctor : NIdx) != decI (r2.headD 0)) = false := by rw [hiff]; simp [e]
      refine ⟨hm2', ?_, fun h => absurd rfl h⟩
      change StateT.run (if ((decI ctor : NIdx) != decI (r2.headD 0)) = true then
        (pure (some tb) : AM _) else pure none) a = _
      rw [hb, hz]; rfl
    · rw [ertW.k_pin_at.arm2 _ _ _ _ _ e] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hb : ((decI ctor : NIdx) != decI (r2.headD 0)) = true := by rw [hiff]; exact bne_iff_ne.mpr e
      refine ⟨hm2', ?_, fun _ => ⟨tb, hT⟩⟩
      change StateT.run (if ((decI ctor : NIdx) != decI (r2.headD 0)) = true then
        (pure (some tb) : AM _) else pure none) a = _
      rw [hb, hT]; rfl
  · rw [ertW.k_er_sl_eq.arm1 _ _ _ _ _ _ (by rw [hr1]; simp [g3])] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_, fun h => absurd rfl h⟩
    simp [etaRescueTable?, hE, hC, g3, hz]; rfl

end L.Arena
