import ConAgua.Arena.IndInstallSpec19

/-!
# Refinements of `IndInstall`, part 20 (lane `indproofs2`, helper `install`): `checkAbsCtorSorts`,
`checkAbsCtorSortsAll`, the relation

Per constructor: the level parameters' check (`all_level_params_defined`'s stub), `NestCtx.hiAt`
(`nest_ctx_hi_at`, helper `pos`'s), the fields opened above the holes (`open_pis_at_fvars_f`'s
stub) and their sorts (`check_struct_field_sorts_i`'s pending contract).
-/

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- One constructor's fields' universes, as the twin computes them after its level check. -/
def absOneAM (fe : IFEnv) (ctx : NestCtx) (b : Bool) (nF : Nat) (tyN : EIdx) : AM Unit := do
  let xq ← unwrapOr (← openPisAtFvarsF nF tyN (ctx.hiAt 0))
    (.internal "direct rec: abstracted constructor fields")
  let _ ← checkStructFieldSortsI V fe b false ctx.sort (ctx.hiAt 0) xq.1 [] nF
  pure ()

/-- A context word decoded below the tops. -/
theorem installCtxWord9 {m : Mem} {ctx : Word} {c : NestCtx}
    (hc : DecB (fun m => decCtx m ctx.toNat) m c) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    H (rdW (m.arr64 IW) (ctx + 9)) ∧ decI (rdW (m.arr64 IW) (ctx + 9)) = c.sort := by
  have hcT : decCtx (truncM m) ctx.toNat = some c := hc
  obtain ⟨-, -, -, -, -, h9, -⟩ := decCtx_some hcT
  obtain ⟨-, h9'⟩ := rec2IwH_trunc h9
  obtain ⟨v, hv, hv32, hve⟩ := iwH_rdW_at (w := ctx) (k := 9) h9' hsz
  rw [show (UInt64.ofNat 9 : Word) = 9 from rfl] at hv
  rw [hv]; exact ⟨hv32, hve⟩

/-- **`check_abs_ctor_sorts_one`'s model refines one constructor's fields' universes.** -/
theorem iaoW_sim {p : Prog} (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {m : Mem} {a : AState} {ctx isP nF tyN hi : Word} {c : NestCtx} {b : Bool}
    (hS : StageR dn vis fe m a) (hc : DecB (fun m => decCtx m ctx.toNat) m c) (hty : H tyN)
    (hhi : hi.toNat = c.hiAt 0) (hb : (isP != 0) = b) :
    Sim (iaoW p n m vis ctx isP nF tyN hi) (absOneAM fe c b nF.toNat (decI tyN)) a
      (fun _ _ m' a' => StageR dn vis fe m' a' ∧ IWGrow m m') := by
  obtain ⟨hs32, hse⟩ := installCtxWord9 hc hS.2.2.2.1
  unfold iaoW absOneAM
  refine Sim.bindK (K := iaoK1 p n vis isP nF hi (rdW (m.arr64 IW) (ctx + 9)))
    (body := fun r1 m1 => if r1.headD 0 = 0 then none else iaoK2 (callW p n "check_struct_field_sorts_i"
      [vis, isP, 0, rdW (m.arr64 IW) (ctx + 9), hi, r1.tail.headD 0, r1.tail.tail.headD 0, 0, 0, nF] m1))
    (by simp [iaoK1])
    (fun r m₁ => by
      by_cases h : r.headD 0 = 0
      · rw [iaoK1_none p n m₁ _ _ _ _ _ r h, if_pos h]
      · rw [iaoK1_some p n m₁ _ _ _ _ _ r h, if_neg h])
    (by
      have h := installSimKeep (p := p) (n := n) (openPisAtFvarsF_spec dn vis fe nF tyN hi hty) hS
      rw [hhi] at h; exact h) ?_
  rintro r1 x1 m1 a1 ⟨hS1, hg1, hd1⟩
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    simp only [h0, if_true]; exact Sim.of_none
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  simp only [h1', show (1 : Word) ≠ 0 by decide, if_false]
  show Sim _ (checkStructFieldSortsI V fe b false c.sort (c.hiAt 0) fvs [] nF.toNat >>= fun _ => pure ()) a1 _
  refine Sim.bindK (K := iaoK2) (body := fun _ m2 => some ([0], m2)) rfl (fun _ _ => rfl)
    (by
      have h := installSimStub (p := p) (n := n) (checkStructFieldSortsI_pending dn vis fe isP 0
        (rdW (m.arr64 IW) (ctx + 9)) hi _ _ 0 0 nF hs32 fvs []) ⟨hS1, hfd, hfb, by simp [decHL, hslice?], by simp⟩
      rw [hse, hhi, hb, show ((0 : Word) != 0) = false from rfl] at h
      exact h) ?_
  rintro r2 - m2 a2 ⟨hS2, hg2, -⟩
  exact Sim.ret ⟨hS2, hg1.trans hg2⟩

end L.Ind
