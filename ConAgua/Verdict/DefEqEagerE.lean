import ConAgua.Verdict.DefEqSlotE
import ConAgua.Arena.InferLeaves

/-!
# The eager slot `defeq_e` and `defeq_arg`: error claims (lane `verdicts-b`, helper `k3`)

`defeq_e(mode, …)` is `defeq(mode | 2, …)`: its failure is the `defeq` slot's at the eager mode
word. From an eager mode the twin's `defeqE` is its `defeq` slot (`knot_defeqE_eager`); from a
plain mode it is the eager tower's `defeq` slot on the entered caches, and a failure there is the
eager slot's failure (`knot_defeqE_plainE`). `defeq_arg` passes on `defeq_e`'s or `defeq`'s
failure; `is_eager_reduce` is outside the verdict closure.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **A failure of the eager tower's `defeq` slot from a plain mode** is the eager slot's. -/
theorem knot_defeqE_plainE (mode : ConLeche.CheckMode) (fe : IFEnv) (F d : Nat) (x y : EIdx)
    (a : AState) (h : mode.eager = false) (ce : CheckError)
    (hr : ((coreKnot mode.toEager fe id (F + 1)).defeq d x y).run
      { a with caches := enterC a.caches } = .error ce) :
    ((coreKnot mode fe id (F + 1)).defeqE d x y).run a = .error ce := by
  simp only [coreKnot, id] at hr ⊢
  simp only [enterEager, h, Bool.false_eq_true, ite_false]
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind] at hr ⊢
  cases hc : (a.caches.eagerMemos.defeqC)[(x, y)]? with
  | some w =>
    simp only [enterC, hc, StateT.run_pure] at hr
    cases hr
  | none =>
    simp only [enterC, hc, StateT.run_bind] at hr
    cases hb : (defeqBody mode.toEager (coreKnot mode.toEager fe id F) fe d x y).run
        { a with caches := enterC a.caches } with
    | error e =>
      simp only [enterC] at hb; simp only [hb] at hr
      cases hr
      simp only [StateT.run_bind, hb]
      rfl
    | ok q =>
      simp only [enterC] at hb
      simp only [hb, except_ok_bind, defeqSet, StateT.run_bind, StateT.run_get, StateT.run_set,
        StateT.run_pure, pure_bind] at hr
      cases hr

/-- **`defeq_e`'s error claim** (the error half of `DefeqESlot`). -/
def DefeqESlotE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d x y : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
    HW x → HW y →
    CoreSpecE p n "defeq_e" [mode, vis, d, x, y]
      ((coreKnot (decMode mode) fe id F).defeqE d.toNat (decE x) (decE y)) s₀ a₀

l_model defeqESlot_specE (p : Prog) (hf : p.lookup "defeq_e" = some defeqESlotL)
  fns [hf ↦ defeqESlotE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`defeq_e`'s error claim one level up**, from the `defeq` slot's (the error half of
`defeqE_refines`). -/
theorem defeqE_refinesE (p : Prog) (hp : KnotProg p) (n : Nat) (hd : DefeqSlotE p n) :
    DefeqESlotE p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode d x y hF hn2 hs hx hy
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (defeqESlot_specE p hp.defeqE (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d x y) hc0 (Err.code_ne_of_cls hkc)
  simp only [defeqESlotE] at hW
  have hcall := tailE (defeqESlotE.k_defeq.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  cases he : (decMode mode).eager with
  | true =>
    rw [mode_eager mode hs.mode4 he] at hcall
    rw [knot_defeqE_eager _ fe F' d.toNat _ _ he]
    exact CoreSpecE.of_callE (hd (F' + 1) s₀ a₀ dn vis fe MM eb mode d x y (by omega) (by omega) hs
      hx hy) hcall
  | false =>
    obtain ⟨hdm, heb0, hm4, heb1⟩ := mode_plain mode hs.mode4 he
    have heb : eb = 0 := hs.eb_mode.trans heb0
    subst heb
    have hpre : SlotPre s₀ { a₀ with caches := enterC a₀.caches } dn vis fe MM 1 (mode ||| 2) :=
      ⟨hs.rel.enter, hm4, heb1⟩
    have hE := CoreSpecE.of_callE
      (hd (F' + 1) s₀ _ dn vis fe MM 1 (mode ||| 2) d x y (by omega) (by omega) hpre hx hy) hcall
    rw [hdm] at hE
    intro hk
    obtain ⟨ce, hce, hc⟩ := hE hk
    exact ⟨ce, knot_defeqE_plainE _ fe F' d.toNat _ _ a₀ he ce hce, hc⟩

/-! ## `defeq_arg` -/

l_model defeqArg_specE (p : Prog) (hf : p.lookup "defeq_arg" = some defeqArgL)
  fns [hf ↦ defeqArgE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`defeq_arg`'s error claim** (the error half of `defeqArg_refines`), from the `defeq` and
`defeq_e` slots' error claims. -/
theorem defeqArg_refinesE (p : Prog) (hp : InferLeafProg p) (hnv : closedNV p L.Checker.nvFns = true)
    (n : Nat) (he : IsEagerReduceH p) (hdE : DefeqSlotE p n) (hdeE : DefeqESlotE p n) (F : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a ta ty : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hta : HW ta) (hty : HW ty) :
    CoreSpecE p (n + 1) "defeq_arg" [mode, vis, d, a, ta, ty]
      (defeqArg (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE ta) (decE ty)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (defeqArg_specE p hp.defeqArg (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a ta ty) hc0 (Err.code_ne_of_cls hkc)
  simp only [defeqArgE] at hW
  cases hc : callE p n "is_eager_reduce" [a] s₀.mem with
  | error e =>
    rw [hc, defeqArgE.k_is_eager_reduce.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc] at hW
  simp only [defeqArgE.k_is_eager_reduce] at hW
  have h₁ := CoreSpec.of_callW (he n s₀ a₀ dn vis fe M eb a hs.rel ha) (callW_of_callE hc)
  have hrun₁ := AM.run_of_ok _ _ h₁.1
  rw [h₁.2.2.1] at hrun₁
  have hT := defeqArg_run (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE ta) (decE ty)
    a₀ _ _ hrun₁
  obtain ⟨M', hS', -, -⟩ := h₁.2.1
  by_cases h0 : r₁.headD 0 ≠ 0
  · rw [if_pos h0] at hW
    have hb : decBool r₁ = true := by simp only [decBool, bne_iff_ne]; exact h0
    rw [hb] at hT
    have h2 := tailE (defeqArgE.k_defeq_e.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
    exact ErrClaim.congr_run hT (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      (hdeE F _ _ dn vis fe M' eb mode d ta ty hF hn ⟨hS', hs.mode4, hs.eb_mode⟩ hta hty) h2)
  · rw [if_neg h0] at hW
    have hb : decBool r₁ = false := by simp only [decBool, bne_eq_false_iff_eq]; simpa using h0
    rw [hb] at hT
    have h2 := tailE (defeqArgE.k_defeq_e.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
    exact ErrClaim.congr_run hT (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      (hdE F _ _ dn vis fe M' eb mode d ta ty hF hn ⟨hS', hs.mode4, hs.eb_mode⟩ hta hty) h2)

end L.Arena
