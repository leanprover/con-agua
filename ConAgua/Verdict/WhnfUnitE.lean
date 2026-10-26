import ConAgua.Verdict.WhnfStuckE
import ConAgua.Arena.DefEqStuckUnit

/-!
# `struct_unit_cert`, `struct_unit_head`, `struct_unit_tail`: error claims (lane `verdicts-b`, helper `k2`)

Their verdicts are the `infer_io`, `whnf` and `defeq` slots'. `struct_unit_head` has a hand error
model (`suhH`) with the store of the spine's top checked in bounds (the generated `suhE` drops it).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace L.Arena

/-- Error model of `struct_unit_head`, the top's store checked. -/
def suhH (p : Prog) (n : Nat) (m : Mem) (mode vis d b wta : Word) : Except Err (List Word × Mem) :=
  match callE p n "get_app_fn" [wta] m with
  | .error e => .error e
  | .ok (r, m₁) =>
    if r.headD 0 >>> 28 ≠ 3 then .ok ([0], m₁)
    else if tierW (r.headD 0) ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0 then .error (.abort 0)
    else if ¬ idxW (r.headD 0) < tcnt m₁ CONST (tierW (r.headD 0)) then .error (.abort 0)
    else
    match callE p n "env_find" [tfld m₁ CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0, vis] m₁ with
    | .error e => .error e
    | .ok (r₂, m₂) =>
      if r₂.headD 0 = 0 then .ok ([0], m₂)
      else if rdW (m₂.arr64 EREC) (r₂.tail.headD 0) ≠ 3 then .ok ([0], m₂)
      else match callE p n "get_app_args" [wta] m₂ with
      | .error e => .error e
      | .ok (r₃, m₃) =>
        if ¬ (136 : Word).toNat < (m₃.arr64 CTL).size then .error (.abort 0)
        else match callE p n "ls_node" [tfld m₁ CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 1]
            (m₃.set64 CTL 136 (rdW (m₂.arr64 CTL) 136)) with
        | .error e => .error e
        | .ok (r₄, m₄) =>
          match callE p n "reserved_contains_w" [tfld m₁ CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0]
              m₄ with
          | .error e => .error e
          | .ok (r₅, m₅) =>
            if rdW (m₂.arr64 EREC) (r₂.tail.headD 0 + 9) = 0 then .ok ([0], m₅)
            else if r₅.headD 0 ≠ 0 then .ok ([0], m₅)
            else if r₃.tail.headD 0 ≠ rdW (m₂.arr64 EREC) (r₂.tail.headD 0 + 10) then .ok ([0], m₅)
            else if r₄.tail.headD 0 ≠ rdW (m₂.arr64 EREC) (r₂.tail.headD 0 + 3) then .ok ([0], m₅)
            else match callE p n "struct_unit_tail" [mode, vis, d, b, wta] m₅ with
              | .error e => .error e
              | .ok (r₆, m₆) => .ok ([r₆.headD 0], m₆)

set_option experimental.vcgen true in
set_option maxRecDepth 8000 in
theorem suhH_spec (p : Prog) (hp : p.lookup "struct_unit_head" = some structUnitHeadL) (n : Nat)
    (s₀ : St) (mode vis d b wta : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_unit_head" [mode, vis, d, b, wta]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 → suhH p n s₀.mem mode vis d b wta = .error ε⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structUnitHeadL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_specE, evalE_tld, tld,
    evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64,
    callE_spec p n "get_app_fn", callE_spec p n "env_find", callE_spec p n "get_app_args",
    callE_spec p n "ls_node", callE_spec p n "reserved_contains_w", callE_spec p n "struct_unit_tail"] <;>
  simp_all [suhH, Cmp.eval, Cmp.evalW, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr, tierW, idxW,
    CTL, EREC, CONST]

theorem whnfUnitE_nv : ∀ f ∈ ["get_app_fn", "env_find", "get_app_args", "ls_node", "reserved_contains_w"],
    f ∈ L.Checker.nvFns := by
  decide +kernel

section suErr
variable (r : CoreFnsA) (depth : Nat) (b wta : EIdx)

theorem suTail_err_io (a : AState) (ce : CheckError) (h : (r.inferIO depth b).run a = .error ce) :
    (suTailT r depth b wta).run a = .error ce := by
  simp only [suTailT, StateT.run_bind, h]; rfl

theorem suTail_err_whnf (a a₁ : AState) (tb : EIdx) (h1 : (r.inferIO depth b).run a = .ok (tb, a₁))
    (ce : CheckError) (h : (r.whnf depth tb).run a₁ = .error ce) :
    (suTailT r depth b wta).run a = .error ce := by
  simp only [suTailT, StateT.run_bind, h1, except_ok_bind, h]; rfl

theorem suTail_err_defeq (a a₁ a₂ : AState) (tb wtb : EIdx) (h1 : (r.inferIO depth b).run a = .ok (tb, a₁))
    (h2 : (r.whnf depth tb).run a₁ = .ok (wtb, a₂)) (hf : isForallE wtb = false) (ce : CheckError)
    (h : (r.defeq depth wta wtb).run a₂ = .error ce) :
    (suTailT r depth b wta).run a = .error ce := by
  simp only [suTailT, StateT.run_bind, h1, except_ok_bind, h2, hf, Bool.false_eq_true, ↓reduceIte, h]

end suErr

section su
variable (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (hnv : closedNV p L.Checker.nvFns = true)

include hq hnv in
/-- **`struct_unit_tail`'s verdicts** are the `infer_io`, `whnf` and `defeq` slots'. -/
theorem suTail_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d b wta : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hwta : HW wta) :
    CoreSpecE p (n + 1) "struct_unit_tail" [mode, vis, d, b, wta]
      (suTailT (coreKnot (decMode mode) fe id F) d.toNat (decE b) (decE wta)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (sutE_spec p hq.suTail (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d b wta) hc0 (Err.code_ne_of_cls hk0)
  simp only [sutE] at hW
  cases c1 : callE p n "infer_io" [mode, vis, d, b] s₀.mem with
  | error e1 =>
    rw [c1, sutE.k_infer_io.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => suTail_err_io (wta := _) (ce := ce) (h := h'))
      (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).inferIO F s₀ a₀ dn vis fe M eb mode d b hF hn hs hb) c1)
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [c1] at hW
  simp only [sutE.k_infer_io] at hW
  obtain ⟨hok1, ⟨M₁, hS₁, -, -⟩, hres1, hr1⟩ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).inferIO F
    s₀ a₀ dn vis fe M eb mode d b hF hn hs hb) (callW_of_callE c1)
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  cases c2 : callE p n "whnf" [mode, vis, d, r₁.headD 0] m₁ with
  | error e2 =>
    rw [c2, sutE.k_whnf.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => suTail_err_whnf (wta := _) (h1 := hrun1) (ce := ce) (h := h'))
      (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d
        (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hr1) c2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [c2] at hW
  simp only [sutE.k_whnf] at hW
  obtain ⟨hok2, ⟨M₂, hS₂, -, -⟩, hres2, hh2⟩ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).whnf F
    ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hr1)
    (callW_of_callE c2)
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  by_cases h6 : r₂.headD 0 >>> 28 = 6
  · rw [if_pos h6] at hW; cases hW
  rw [if_neg h6] at hW
  have hfa : isForallE (decH r₂) = false := by
    simp only [isForallE, decH, tag_beq_w _ hh2 6 (by decide) ETag.forallE rfl 6 rfl]; simpa using h6
  have hW' := err_of_k (by intro q e; simp [sutE.k_defeq]) (fun _ => rfl) hW
  exact ErrClaim.of_run_err (fun ce h' => suTail_err_defeq (h1 := hrun1) (h2 := hrun2) (hf := hfa) (ce := ce)
      (h := h'))
    (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).defeq F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d wta
      (r₂.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ hwta hh2) hW')

end su

end L.Arena
