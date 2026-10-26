import ConAgua.Verdict.PhaseBE
import ConAgua.Verdict.DeclValE

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

l_model checkPending_specE (p : Prog) (hf : p.lookup "check_pending" = some checkPendingL)
  fns [hf ↦ checkPendingE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] errors


section pend
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog) (fe : IFEnv) (pend : Array PendingCheck)

local notation "V" => ConLeche.CheckMode.verified

/-- The record's two words read by `rdW` (the error model's loads). -/
theorem pend_rdW (m : Mem) (pend : Array PendingCheck) (hP : PendR m pend) (j : Word)
    (hj : j.toNat < pend.size) (hj62 : j.toNat < 2 ^ 62) :
    decVG (erecP m) (rdW (m.arr64 PEND) (3 * j)).toNat = some (pdAt pend j).vg ∧
    (rdW (m.arr64 PEND) (3 * j + 2)).toNat = (pdAt pend j).vis := by
  have hr := hP.recs j.toNat hj
  have e0 : (3 * j).toNat = 3 * j.toNat := by rw [UInt64.toNat_mul]; simp; omega
  have e2 : (3 * j + 2).toNat = 3 * j.toNat + 2 := by rw [UInt64.toNat_add, e0]; simp; omega
  have hpd : pdAt pend j = pend[j.toNat] := by simp [pdAt, hj]
  simp only [decPend, nat?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at hr
  obtain ⟨g, ⟨w0, hw0, rfl⟩, vg, hvg, x, ⟨w1, hw1, rfl⟩, y, ⟨w2, hw2, rfl⟩, he⟩ := hr
  rw [hpd, ← Option.some.inj he]
  refine ⟨?_, ?_⟩
  · rw [rdW_of_get? e0.symm hw0]; exact hvg
  · rw [rdW_of_get? e2.symm hw2]

/-- **`check_pending`'s error claim** (`CPErrT`): `scratch_enter` and `scratch_drop` claim nothing;
`check_value_group`'s claim (`cvgE_okT`) at the record's view, `StageT` from the loop's relation. -/
theorem checkPending_errT (hm : mode = .verified) (hP : PhaseBProg p) (hcE : CoreStubsE p)
    (hivE : IvgE p) (hnvR : NVAt p "iw_reset") (hnvP : NVAt p "pin_word")
    (hnvL : NVAt p "lvl_eq_c") (hnvE : NVAt p "scratch_enter") (hnvD : NVAt p "scratch_drop") :
    CPErrT mode pins dn ds p fe pend := by
  subst hm
  intro n hn s₀ a₀ j vis hj hT hR hM hc hj62 hCr
  refine CoreSpecE.of_runs fun e hc0 => ?_
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hb := hP.bracket
  have h1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [drop_cons_pdAt pend j hj h1] at hT
  have hW := triple_of_callE_err (checkPending_specE p hP.cp n ⟨s₀.mem, Locals.init []⟩ j vis) hc0
    (Err.code_ne_of_cls hk0)
  have hvB := hR.vis
  have hwf : StoreWF a₀.store := hT.stateOK.wf
  have hoff := hT.off
  have hTw := hT.twinOK dn hM hc
  have hfl := hM.flag
  have hthm := hT.enterThm
  cases n with
  | zero => rw [checkPendingE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  simp only [checkPendingE] at hW
  by_cases g1 : 4611686018427387904 ≤ j
  · rw [ite_eq_left g1] at hW; cases hW; exact absurd rfl hk0
  rw [ite_eq_right g1] at hW
  unfold checkPending
  cases h1 : callE p n "scratch_enter" [] s₀.mem with
  | error e1 =>
    rw [h1, checkPendingE.k_scratch_enter.none] at hW; cases hW
    exact ErrClaim.of_cls0 (hnvE _ _ _ _ h1)
  | ok q =>
  obtain ⟨r, m₁⟩ := q
  rw [h1, checkPendingE.k_scratch_enter.arm1] at hW
  obtain ⟨s1, hs1, -, hok1, hR1, hT1, hfl1, hCr1⟩ := triple_of_callE
    (enter_loopB dn ds p hb hP.crk (pins := pins) n ⟨s₀.mem, Locals.init []⟩ a₀ vis fe
      (fe.restrictTo (pdAt pend j).vis) pend hwf hoff hR hTw hfl hCr) h1
  subst hs1
  refine ErrClaim.bind_right (AM.run_of_ok _ _ hok1) ?_
  obtain ⟨hg, hv⟩ := pend_rdW s1.mem pend hR1.pend j hj hj62
  generalize rdW (s1.mem.arr64 PEND) (3 * j + 2) = v at hW hv
  generalize rdW (s1.mem.arr64 PEND) (3 * j) = g at hW hg
  have hR' := hR1.restrict v
  rw [hv] at hR'
  have hS : StageT dn v (fe.restrictTo (pdAt pend j).vis) s1.mem (AM.st enterScratch a₀) :=
    ⟨⟨hR'.check, hR'.iw⟩, hT1, hfl1⟩
  have hv' : ∃ x, x = v := ⟨_, rfl⟩
  cases h2 : callE p n "check_value_group" [v, g] s1.mem with
  | error e2 =>
    rw [h2, checkPendingE.k_check_value_group.none] at hW; cases hW
    refine ErrClaim.bind_left ?_
    exact cvgE_okT hP.knot hP.cvg hP.knot.knot.lvc hP.apd hP.crk hcE hivE hnvR hnvP hnvL (by omega) hS
      hg hCr1 hthm h2
  | ok q =>
  obtain ⟨r2, m2⟩ := q
  rw [h2, checkPendingE.k_check_value_group.arm1] at hW
  cases h3 : callE p n "scratch_drop" [] m2 with
  | error e3 =>
    rw [h3, checkPendingE.k_scratch_drop.none] at hW; cases hW
    exact ErrClaim.of_cls0 (hnvD _ _ _ _ h3)
  | ok q =>
  obtain ⟨r3, m3⟩ := q
  rw [h3, checkPendingE.k_scratch_drop.arm1] at hW
  cases hW

end pend

end L.Arena
