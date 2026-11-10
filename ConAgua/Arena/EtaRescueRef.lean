module

public import ConAgua.Arena.WhnfIota
public import ConAgua.Arena.DeclCanonSpec
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DefEqStuckGo
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
# `eta_rescue_ok`: the structure-η rescue's standing condition (`etaRescueOk`)

The constructor's and the family's level parameters compared as `EREC` slices (`er_sl_eq`), the
`And.intro` pin read last.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- `er_sl_eq`'s spec at its own lookup (`StubIndRefine.erSlEq_spec'`'s, for callers that cannot
import that file). -/
theorem erSlEq_specR (p : Prog) (hp : p.lookup "er_sl_eq" = some L.Ind.erSlEq) (n : Nat) :
    ∀ (s₀ : St) (o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "er_sl_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if L.Ind.erSlEqB (erRdT s₀.mem) o1 l1 o2 l2 then 1 else 0; ⊤⦄ := by
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
      finish (gen := 20) [rdW_eq]

/-- **`eta_rescue_ok`'s model**: `er_sl_eq` and `pin_at` lifted. -/
l_model eroW_spec (p : Prog) (hf : p.lookup "eta_rescue_ok" = some etaRescueOkL)
  fns [hf ↦ eroW] specs [callW_spec p n "er_sl_eq", callW_spec p n "pin_at"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- A `ctorInfo` record's constant value decodes at `q + 1`. -/
theorem decCI_ctor_cv' {R : Nat → Option Word} {q : Nat} {cv : IConstantVal} {nP nF : Nat}
    (h : decCI R q = some (.ctorInfo cv nP nF)) : decCV R (q + 1) = some cv := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, -, h⟩ := h
  rcases k with _ | _ | _ | _ | _ | _ | k <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq, and_false, exists_false] at h
  obtain ⟨cv', hcv, _, -, _, -, he⟩ := h
  cases he; exact hcv

/-- **`eta_rescue_ok` refines `etaRescueOk`** (memory and twin state kept). -/
theorem ero_ok {p : Prog} (hes : p.lookup "er_sl_eq" = some L.Ind.erSlEq)
    (hpa : p.lookup "pin_at" = some pinAtL) {n : Nat} {m m' : Mem} {a : AState} (hP : PinsR m a.pins)
    {ctor cq q : Word} (hctor : HW ctor) {cvj : IConstantVal} {nP nF : Nat} {cvT : IConstantVal}
    {caps : IIndCaps} (hcj : decCI (erecP m) cq.toNat = some (.ctorInfo cvj nP nF))
    (hci : decCI (erecP m) q.toNat = some (.indInfo cvT caps)) {w : Word}
    (h : eroW p n m ctor cq q = some (w, m')) :
    m' = m ∧ (etaRescueOk (decI ctor) cvj cvT caps).run a = .ok (w != 0, a) ∧ HW w := by
  rcases n with _ | n
  · simp [eroW] at h
  have hrec := decCI_indCaps (erRdOK m) hci
  obtain ⟨hlj, -⟩ := decCV_rd (erRdOK m) (decCI_ctor_cv' hcj)
  have hlT := hrec.lp
  have heta := hrec.eta
  have hec := hrec.etaCtor
  have hechw := hrec.etaCtor_hw
  have h0 : HW 0 := by unfold HW; decide
  have h1 : HW 1 := by unfold HW; decide
  by_cases g1 : erRdT m (q + 5) = 0
  · rw [eroW.arm1 _ _ _ _ _ _ g1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_, h0⟩
    have : caps.eta = false := by rw [heta, g1]; rfl
    simp [etaRescueOk, this]; rfl
  by_cases g2 : erRdT m (q + 6) ≠ ctor
  · rw [eroW.arm2 _ _ _ _ _ _ g1 g2] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_, h0⟩
    have : (caps.etaCtor == decI ctor) = false := by
      rw [hec]; simpa using fun e => g2 ((decI_inj_iff hechw hctor).mp e)
    simp [etaRescueOk, this]; rfl
  have g2' : erRdT m (q + 6) = ctor := by simpa using g2
  rw [eroW.arm3 _ _ _ _ _ _ g1 g2'] at h
  have hE : caps.eta = true := by rw [heta]; simpa using g1
  have hC : (caps.etaCtor == decI ctor) = true := by rw [hec, g2']; simp
  rcases c1 : callW p n "er_sl_eq" [erRdT m (cq + 2), erRdT m (cq + 3), erRdT m (q + 2),
      erRdT m (q + 3)] m with _ | ⟨r1, m1⟩
  · rw [c1, eroW.k_er_sl_eq.none] at h; cases h
  rw [c1] at h
  obtain ⟨s1, hs1, -, hm1, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erSlEq_specR p hes n ⟨m, Locals.init []⟩ _ _ _ _) c1
  have hm1' : m = m1 := (hs1 ▸ hm1).symm
  subst hm1'
  rw [L.Ind.erSlEqB_ok (erRdOK m) hlj hlT] at hr1
  by_cases g3 : cvj.levelParams = cvT.levelParams
  · rw [eroW.k_er_sl_eq.arm2 _ _ _ _ _ (by rw [hr1]; simp [g3])] at h
    rcases c2 : callW p n "pin_at" [48] m with _ | ⟨r2, m2⟩
    · rw [c2, eroW.k_pin_at.none] at h; cases h
    rw [c2, eroW.k_pin_at.arm1] at h
    obtain ⟨s2, hs2, hm2, -, hr2, hpin⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (pinAt_refines p hpa n ⟨m, Locals.init []⟩ a hP 48) c2
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hm2' : m2 = m := hs2 ▸ hm2
    refine ⟨hm2', ?_, by split <;> assumption⟩
    have hpin' : pinAndIntro.run a = .ok (decI (r2.headD 0), a) := hpin
    have hiff : ((decI ctor : NIdx) != decI (r2.headD 0)) = (ctor != r2.headD 0) := by
      unfold bne; congr 1
      exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact decI_inj_iff hctor hr2)
    simp only [etaRescueOk]
    rw [ite_eq_left (by simp [hE, hC, g3]), StateT.run_bind, hpin']
    show Except.ok ((decI ctor : NIdx) != decI (r2.headD 0), a) = _
    rw [hiff]
    generalize r2.headD 0 = x
    by_cases e : ctor = x <;> simp [e]
  · rw [eroW.k_er_sl_eq.arm1 _ _ _ _ _ (by rw [hr1]; simp [g3])] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_, h0⟩
    simp [etaRescueOk, hE, hC, g3]; rfl

end L.Arena
