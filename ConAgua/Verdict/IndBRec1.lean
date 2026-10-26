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


l_model classMinorSlotE_spec (p : Prog) (hf : p.lookup "class_minor_slot" = some classMinorSlotL)
  fns [hf ↦ classMinorSlotE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`class_minor_slot`'s error refinement** (the hypotheses of `classMinorSlot_refines`): the
scan `class_minor_slot_go` is outside the verdict closure; the one reject site (not exactly one
minor premise) means the twin's hit list is not a singleton. -/
theorem classMinorSlot_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hgo : p.lookup "class_minor_slot_go" = some classMinorSlotGo)
    (hp : p.lookup "class_minor_slot" = some classMinorSlotL) (n : Nat) (s₀ : St) (a₀ : AState)
    (rd c cc : Word) (R : ClassRead) (hR : decCR s₀.mem rd.toNat = some R) (hcc : cc.toNat < 2 ^ 32)
    (hsz : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) :
    CoreSpecE p (n + 1) "class_minor_slot" [rd, c, cc]
      (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (classMinorSlotE_spec p hp (n + 1) ⟨s₀.mem, Locals.init []⟩ rd c cc)
    hc (Err.code_ne_of_cls hk0)
  simp only [classMinorSlotE] at hW
  cases h1 : callE p n "class_minor_slot_go"
      [rdW (s₀.mem.arr64 IW) rd, rdW (s₀.mem.arr64 IW) (rd + 1), 0, c, cc, 0, 0, 0, 0] s₀.mem with
  | error e1 =>
    rw [h1, classMinorSlotE.k_class_minor_slot_go.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q =>
  obtain ⟨r, m1⟩ := q
  by_cases hx : r.headD 0 ≠ 1
  · rw [h1, classMinorSlotE.k_class_minor_slot_go.abort1 p r m1 hx] at hW
    cases hW
    obtain ⟨s', -, -, -, x, y, z, w, hg, rfl⟩ := triple_of_callW
      (classMinorSlotGo_spec p hgo n ⟨s₀.mem, Locals.init []⟩ _ _ 0 c cc 0 0 0 0) (callW_of_callE h1)
    simp only [List.headD_cons] at hx
    have hR' := hR
    simp only [decCR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hR'
    obtain ⟨slots, hsl, rcs, -, hRe⟩ := hR'
    have hRs : R.slots = slots := by rw [← hRe]
    obtain ⟨o, l, ho, hl, hdec⟩ := decAt_some hsl
    have hrd64 : rd.toNat < 2 ^ 64 := rd.toNat_lt
    have ho' := iwN_rdW ho hrd64
    rw [UInt64.ofNat_toNat] at ho'
    have hl' := iwN_off (k := 1) hl (by have := iwN_lt hl; omega)
    rw [show UInt64.ofNat 1 = 1 from rfl, UInt64.ofNat_toNat] at hl'
    have hl1 : rdW (s₀.mem.arr64 IW) (rd + 1) = UInt64.ofNat l := hl'.2
    simp only at hg
    rw [ho'.1, hl1] at hg
    have hol : o + l < 2 ^ 64 := by
      rcases decPL_le hdec with h0 | h0
      · have : o < 2 ^ 64 := ho'.2
        omega
      · omega
    have hlz : l < 2 ^ 64 := (iwN_rdW hl (by have := iwN_lt hl; omega)).2
    have hos : o < 2 ^ 64 := ho'.2
    have hg2 := classMinorSlotGoW_ok n s₀.mem (UInt64.ofNat o) (UInt64.ofNat l) 0 c cc 0 0 0 0 x y z w
      slots hg
      (by simpa [UInt64.toNat_ofNat_of_lt' hos, UInt64.toNat_ofNat_of_lt' hlz] using hdec) hcc hsz
      (by simp [UInt64.toNat_ofNat_of_lt' hos, UInt64.toNat_ofNat_of_lt' hlz]; omega)
      (by simp [UInt64.toNat_ofNat_of_lt' hlz]; omega) (by simp [UInt64.toNat_ofNat_of_lt' hlz]; omega)
    obtain ⟨g1, -, -⟩ := hg2
    simp only [UInt64.toNat_zero, Nat.zero_add] at g1
    rw [← hRs] at g1
    have hlen : (hitsFrom c.toNat (decI cc) 0 R.slots).length ≠ 1 := by
      intro h1'
      apply hx
      have : x.toNat = (1 : Word).toNat := by rw [g1, h1']; rfl
      exact UInt64.toNat_inj.mp this
    have hits := hitsFrom_eq c.toNat (decI cc) 0 R.slots
    simp only [Nat.zero_add] at hits
    show ErrClaim (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) a₀ _
    simp only [ConRon.Arena.classMinorSlot]
    erw [hits]
    match hh : hitsFrom c.toNat (decI cc) 0 R.slots, hlen with
    | [], _ => exact ErrClaim.fail _ _ (by decide)
    | _ :: _ :: _, _ => exact ErrClaim.fail _ _ (by decide)
  · rw [h1, classMinorSlotE.k_class_minor_slot_go.arm1 p r m1 (by simpa using hx)] at hW
    cases hW

end L.Ind
