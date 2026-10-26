import ConAgua.Verdict.PosE2M

/-!
# The positivity walk's error claims: `nest_cont_new`, `nest_frame` and their leaves
`nest_grow_group`, `nest_group_ctors` (lane `verdicts-b`, helper `ia2`, fork `kn2a`)

The error halves of `newOKC_step` (`PosNew.lean`), `frameOKC_step` (`PosFrame.lean`),
`ggW_ok` and `gcW_ok`, on the generated error models (`PosE2M.lean`).
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dGrp dKey kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `nest_group_ctors` -/

/-- **`nest_group_ctors`' error claim** (`gcW_ok`'s hypotheses): a container that is none, or
whose parameter count disagrees, rejects as the twin's `nestGroupCtors` does. -/
theorem ngcE_claim {p : Prog} (L : NbLook p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis nPc : Word) (k : Nat) :
    ∀ (m : Mem) (a : AState) (off l oo ol : Word) (cs : List NIdx) (out : List (IConstantVal × Nat)),
    StageR dn vis fe m a →
    decHL m off.toNat l.toNat = some cs → (∀ j < l.toNat, off.toNat + j < iwTop m) →
    ol.toNat = out.length → oo.toNat + out.length ≤ iwTop m → CsAt m oo.toNat out (· < iwTop m) →
    ∀ e, ngcE p k m vis nPc off l oo ol = .error e →
      ErrClaim (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out) a e := by
  induction k with
  | zero =>
    intro m a off l oo ol cs out _ _ _ _ _ _ e he
    rw [ngcE.eq_1] at he; cases he; exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
    intro m a off l oo ol cs out hS hcs' hcb hol hob hout e he
    by_cases hl0 : l = 0
    · rw [ngcE.arm1 p k m vis nPc off l oo ol hl0] at he; cases he
    rw [ngcE.arm2 p k m vis nPc off l oo ol hl0] at he
    have hl : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hcs2 := hcs'
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hcs2
    obtain ⟨c, hc, cs', hcs'', rfl⟩ := hcs2
    obtain ⟨hcH, hcd⟩ := rd_iwH0E (m := m) (o := off) (k := IdxKind.name) (by simpa [iwH, iwA] using hc)
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      word_add_toNat (show off.toNat + 1 < 2 ^ 64 by have := hcb 0 (by omega); omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    cases h1 : callE p k "nest_container" [vis, rdW (m.arr64 IW) off] m with
    | error e1 =>
      rw [h1, ngcE.k_nest_container.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
    | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    obtain ⟨s1, hs1, -, hnt⟩ := triple_of_callW (nt_spec' p L.nt k ⟨m, Locals.init []⟩ vis _)
      (callW_of_callE h1)
    simp only at hnt
    rw [hs1] at hnt
    cases k with
    | zero => simp [ntWf] at hnt
    | succ k =>
    simp only [ntWf] at hnt
    obtain ⟨x, a1, hrun1, hS1, hg1, hnc⟩ := ntW_ok dn fe vis _ hcH k m m1 a r1 hnt hS
    rw [hcd] at hrun1
    rw [h1] at he
    simp only [ConRon.Arena.nestGroupCtors.eq_2]
    refine ErrClaim.bind_right hrun1 ?_
    cases x with
    | none =>
      have h0 : r1.headD 0 = 0 := hnc
      rw [ngcE.k_nest_container.abort1 p _ vis nPc off l oo ol r1 m1 h0] at he; cases he
      exact ErrClaim.fail _ _ (by decide)
    | some pc =>
    obtain ⟨nPc2, ctors⟩ := pc
    obtain ⟨h0, h1', h3, h2b, hcs3⟩ := hnc
    have hne0 : r1.headD 0 ≠ 0 := by rw [h0]; decide
    by_cases hbad : r1.tail.headD 0 ≠ nPc ∧ r1.tail.tail.tail.headD 0 ≠ 0
    · rw [ngcE.k_nest_container.abort2 p _ vis nPc off l oo ol r1 m1 hne0 hbad] at he; cases he
      have hneq : nPc2 ≠ nPc.toNat := fun e => hbad.1 (UInt64.toNat_inj.mp (by rw [h1', e]))
      have hlen : ctors.length ≠ 0 := by
        intro e; apply hbad.2; apply UInt64.toNat_inj.mp; rw [h3, e]; rfl
      have hc : (!(nPc2 == nPc.toNat || ctors.length == 0)) = true := by
        simp [hneq, hlen]
      show ErrClaim (if (!(nPc2 == nPc.toNat || ctors.length == 0)) = true then _ else _) a1 _
      rw [if_pos hc]
      exact ErrClaim.fail _ _ (by decide)
    rw [ngcE.k_nest_container.arm1 p _ vis nPc off l oo ol r1 m1 hne0 hbad] at he
    have hchk : (nPc2 == nPc.toNat || ctors.length == 0) = true := by
      by_cases hp1 : r1.tail.headD 0 = nPc
      · rw [← h1', hp1]; simp
      · have : r1.tail.tail.tail.headD 0 = 0 := by
          by_cases hh : r1.tail.tail.tail.headD 0 = 0
          · exact hh
          · exact absurd ⟨hp1, hh⟩ hbad
        have : ctors.length = 0 := by rw [← h3, this]; rfl
        simp [this]
    show ErrClaim (if (!(nPc2 == nPc.toNat || ctors.length == 0)) = true then _ else _) a1 _
    rw [hchk]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases h2 : callE p (k + 1) "sl_append" [oo, ol, r1.tail.tail.headD 0, r1.tail.tail.tail.headD 0] m1 with
    | error e2 =>
      rw [h2, ngcE.k_sl_append.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
    | ok q2 =>
    obtain ⟨r2, m2⟩ := q2
    obtain ⟨s2, hs2, -, hap⟩ := triple_of_callW (slAppend_specW p L.nt.ha L.nit.hc2 L.hap (k + 1)
      ⟨m1, Locals.init []⟩ _ _ _ _) (callW_of_callE h2)
    simp only at hap
    rw [hs2] at hap
    rw [h2, ngcE.k_sl_append.arm1] at he
    obtain ⟨hS2, hg2, hr20, hr21, ht2, hw1, hw2⟩ := appendW_stage hap hS1 (by have := hg1.1; omega)
      (by rw [h3]; exact h2b)
    rw [h3] at hr21 ht2 hw2
    have hcsA : CsAt m2 (r2.headD 0).toNat (out ++ ctors) (· < iwTop m2) := by
      intro i hi
      rw [hr20]
      by_cases hio : i < out.length
      · obtain ⟨w, hw, hc'⟩ := hout i hio
        refine ⟨w, ?_, ?_⟩
        · rw [hw1 i (by omega), hg1.2.2.1 _ (by omega)]; exact hw
        · rw [List.getElem_append_left hio]; exact (hc'.grow hg1).grow hg2
      · simp only [List.length_append] at hi
        obtain ⟨w, hw, hc'⟩ := hcs3 (i - out.length) (by omega)
        refine ⟨w, ?_, ?_⟩
        · have := hw2 (i - out.length) (by omega)
          rw [show iwTop m1 + ol.toNat + (i - out.length) = iwTop m1 + i by omega] at this
          rw [this]; exact hw
        · rw [List.getElem_append_right (by omega)]; exact hc'.grow hg2
    cases h3' : ngcE p (k + 1) m2 vis nPc (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0) with
    | ok q3 => obtain ⟨r3, m3⟩ := q3; rw [h3', ngcE.k_nest_group_ctors.arm1] at he; cases he
    | error e3 =>
    rw [h3', ngcE.k_nest_group_ctors.none] at he; cases he
    exact ih m2 a1 (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0) cs' (out ++ ctors) hS2
        (by rw [hoff1, hl1, decHL_agree (RdS.of_grow (hg1.trans hg2)) (fun j hj => by
              have := hcb (j + 1) (by omega); omega)]
            simpa [decHL] using hcs'')
        (fun j hj => by rw [hoff1, hl1] at *; have := hcb (j + 1) (by omega); have := hg1.1; have := hg2.1; omega)
        (by rw [hr21]; simp [hol]) (by rw [hr20]; simp; omega) hcsA _ h3'

end L.Ind
