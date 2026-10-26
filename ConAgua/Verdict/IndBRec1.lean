import ConAgua.Arena.IndT.CheckIndDecl
import ConAgua.Verdict.IndE

/-!
# Error refinements of the recursor generation's leaves (lane `verdicts-b`, helper `ib`)

`class_key_of`, ... : a failing call of class `1`/`2` claims that the twin fails with that class.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model classKeyOfE_spec (p : Prog) (hf : p.lookup "class_key_of" = some classKeyOfL)
  fns [hf ↦ classKeyOfE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] heartbeats 400000 errors

section kof
variable {p : Prog} (L : KofProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
include L

/-- **`class_key_of`'s error refinement** (the hypotheses of `classKeyOf_refines`): a failing call of
class `1`/`2` (the one reject site, the major's parameters mentioning more than the recursor's;
the callees `class_key_canon`, `class_key_of_closed` are outside the verdict closure) claims the
twin's `classKeyOf` fails. -/
theorem classKeyOf_claim (hnv : closedNV p _root_.L.Checker.nvFns = true) (k : Nat) (s₀ : St)
    (a₀ : AState) (nP po pl key : Word) (pfvs : List EIdx) (ck : ClassKey)
    (hS : StageR dn vis fe s₀.mem a₀) (hpf : decHL s₀.mem po.toNat pl.toNat = some pfvs)
    (hpb : po.toNat + pl.toNat ≤ iwTop s₀.mem) (hk : DecB (fun m => decCK m key.toNat) s₀.mem ck)
    (hP : PosMR s₀.mem) :
    CoreSpecE p (k + 2) "class_key_of" [nP, po, pl, key] (ConRon.Arena.classKeyOf nP.toNat pfvs ck)
      s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (classKeyOfE_spec p L.kof (k + 2) ⟨s₀.mem, Locals.init []⟩ nP po pl key)
    hc (Err.code_ne_of_cls hk0)
  rw [classKeyOfE.arm1] at hW
  cases h1 : callE p (k + 1) "class_key_canon" [po, pl, key] s₀.mem with
  | error e1 =>
    rw [h1, classKeyOfE.k_class_key_canon.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  obtain ⟨s1, hs1, -, hm1⟩ := triple_of_callW (kc_spec L k ⟨s₀.mem, Locals.init []⟩ po pl key)
    (callW_of_callE h1)
  subst hs1
  obtain ⟨x1, a1, hrun1, hd1, hb1, hds1, hS1, hg1, hP1⟩ :=
    kcW_ok dn fe vis k s₀.mem _ a₀ po pl key r1 pfvs ck hm1 hS hpf hpb hk hP
  have htop1 : iwTop s1.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨nk, hnk, rfl⟩ := decCK_decB_nk hd1
  obtain ⟨-, -, -, -, hds, -, -⟩ := pos2_nk_fields hnk htop1
  rw [h1, classKeyOfE.k_class_key_canon.eq_2] at hW
  refine ErrClaim.bind_right hrun1 ?_
  cases h2 : callE p (k + 1) "class_key_of_closed"
      [nP, rdW (s1.mem.arr64 IW) (r1.headD 0 + 2), rdW (s1.mem.arr64 IW) (r1.headD 0 + 3)] s1.mem with
  | error e2 =>
    rw [h2, classKeyOfE.k_class_key_of_closed.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hm2⟩ := triple_of_callW (ckc2_spec L (k + 1) ⟨s1.mem, Locals.init []⟩ nP _ _)
    (callW_of_callE h2)
  subst hs2
  obtain ⟨b, a2, hrun2, hS2, hg2, hb2, -⟩ := ckc2W_ok dn fe vis (k + 1) s1.mem _ a1 nP _ _ nk.ds r2 hm2 hS1 hds
    (by omega) hds1
  by_cases h0 : r2.headD 0 = 0
  · rw [h2, classKeyOfE.k_class_key_of_closed.abort1 p _ r2 _ h0] at hW
    cases hW
    have hbf : b = false := by
      rw [← hb2, h0]; rfl
    subst hbf
    refine ErrClaim.bind_right hrun2 ?_
    exact ErrClaim.fail _ _ rfl
  · rw [h2, classKeyOfE.k_class_key_of_closed.arm1 p _ r2 _ h0] at hW
    cases hW
end kof

end L.Ind
