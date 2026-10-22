import ConAgua.Arena.DeclDivMod3

/-!
# The `Nat.div` family's pin gate, bottom up: the certificate builders, part 4 (lane `decls3`, `decls3-divmod`)

The seven certificate builders and the dispatch `div_mod_cert_stmts_at`, `div_mod_cert_stmts`.
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section nat
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

def certLorRhsW (p : Prog) (n : Nat) (m : Mem) (cx c : Word) : Option (List Word × Mem) :=
  bW (callW p n "cert_halves" [cx, c] m) fun r1 m1 =>
  bW (callW p n "nat_ap2" [rdW (m1.arr64 IW) (cx + 13), rdW (m1.arr64 IW) (cx + 9), r1.headD 0] m1) fun r2 m2 =>
  bW (callW p n "nat_ap2" [rdW (m2.arr64 IW) (cx + 10), rdW (m2.arr64 IW) (cx + 1), rdW (m2.arr64 IW) (cx + 9)] m2) fun r3 m3 =>
  bW (callW p n "nat_ap2" [rdW (m3.arr64 IW) (cx + 10), rdW (m3.arr64 IW) (cx + 2), rdW (m3.arr64 IW) (cx + 9)] m3) fun r4 m4 =>
  bW (callW p n "nat_ap2" [rdW (m4.arr64 IW) (cx + 12), r3.headD 0, r4.headD 0] m4) fun r5 m5 =>
  bW (callW p n "nat_ap2" [rdW (m5.arr64 IW) (cx + 13), r3.headD 0, r4.headD 0] m5) fun r6 m6 =>
  bW (callW p n "nat_ap2" [rdW (m6.arr64 IW) (cx + 14), r5.headD 0, r6.headD 0] m6) fun r7 m7 =>
  bW (callW p n "nat_ap2" [rdW (m7.arr64 IW) (cx + 12), r2.headD 0, r7.headD 0] m7) fun r8 m8 =>
  some ([r8.headD 0], m8)

set_option maxHeartbeats 1600000 in
theorem certLorRhs_specW (p : Prog) (hp : p.lookup "cert_lor_rhs" = some certLorRhsL) (n : Nat) (s₀ : St)
    (cx c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_lor_rhs" [cx, c]
    ⦃fun r s' => LocEq s' s₀ ∧ certLorRhsW p n s₀.mem cx c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certLorRhsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_halves", callW_spec p n "nat_ap2"] <;>
    finish (gen := 30) (instances := 10000) [certLorRhsW, bW, rdW_eq]

theorem certLorRhs_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_lor_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certLorRhs cc (decI c)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mm => certLorRhsW p k mm cx c) (certLorRhs_specW p hD.lCertLorRhs k · cx c) hcall
  unfold certLorRhsW at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (certHalves_ref hD cx c cc).bind_ ⟨hS, hC, hc⟩ hw
  rw [(hC.grow hG1).f13] at hw
  rw [(hC.grow hG1).f9] at hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.mulN.word.toUInt64 cc.two.word.toUInt64 (r1.headD 0)).bind_ ⟨hS1, (word_lt32 _), (word_lt32 _), hl1⟩ hw
  have hG2 : IWGrow m m2 := hG1.trans hg2
  rw [(hC.grow hG2).f10] at hw
  rw [(hC.grow hG2).f1] at hw
  rw [(hC.grow hG2).f9] at hw
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.modN.word.toUInt64 cc.x.word.toUInt64 cc.two.word.toUInt64).bind_ ⟨hS2, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG3 : IWGrow m m3 := hG2.trans hg3
  rw [(hC.grow hG3).f10] at hw
  rw [(hC.grow hG3).f2] at hw
  rw [(hC.grow hG3).f9] at hw
  obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.modN.word.toUInt64 cc.y.word.toUInt64 cc.two.word.toUInt64).bind_ ⟨hS3, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG4 : IWGrow m m4 := hG3.trans hg4
  rw [(hC.grow hG4).f12] at hw
  obtain ⟨r5, m5, x5, a5, hrun5, ⟨hS5, hg5, hl5, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.addN.word.toUInt64 (r3.headD 0) (r4.headD 0)).bind_ ⟨hS4, (word_lt32 _), hl3, hl4⟩ hw
  have hG5 : IWGrow m m5 := hG4.trans hg5
  rw [(hC.grow hG5).f13] at hw
  obtain ⟨r6, m6, x6, a6, hrun6, ⟨hS6, hg6, hl6, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.mulN.word.toUInt64 (r3.headD 0) (r4.headD 0)).bind_ ⟨hS5, (word_lt32 _), hl3, hl4⟩ hw
  have hG6 : IWGrow m m6 := hG5.trans hg6
  rw [(hC.grow hG6).f14] at hw
  obtain ⟨r7, m7, x7, a7, hrun7, ⟨hS7, hg7, hl7, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.subN.word.toUInt64 (r5.headD 0) (r6.headD 0)).bind_ ⟨hS6, (word_lt32 _), hl5, hl6⟩ hw
  have hG7 : IWGrow m m7 := hG6.trans hg7
  rw [(hC.grow hG7).f12] at hw
  obtain ⟨r8, m8, x8, a8, hrun8, ⟨hS8, hg8, hl8, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.addN.word.toUInt64 (r2.headD 0) (r7.headD 0)).bind_ ⟨hS7, (word_lt32 _), hl2, hl7⟩ hw
  have hG8 : IWGrow m m8 := hG7.trans hg8
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨_, a8, ?_, hS8, hG8, hl8, rfl⟩
  simp only [decE_eq_decI, decI_word] at hrun1 hrun2 hrun3 hrun4 hrun5 hrun6 hrun7 hrun8
  simp only [certLorRhs, StateT.run_bind, exc_ok_bind', decE_eq_decI, decI_word, hrun1, hrun2, hrun3, hrun4, hrun5, hrun6, hrun7, hrun8]
  try rfl

def certXorRhsW (p : Prog) (n : Nat) (m : Mem) (cx c : Word) : Option (List Word × Mem) :=
  bW (callW p n "cert_halves" [cx, c] m) fun r1 m1 =>
  bW (callW p n "nat_ap2" [rdW (m1.arr64 IW) (cx + 13), rdW (m1.arr64 IW) (cx + 9), r1.headD 0] m1) fun r2 m2 =>
  bW (callW p n "nat_ap2" [rdW (m2.arr64 IW) (cx + 10), rdW (m2.arr64 IW) (cx + 1), rdW (m2.arr64 IW) (cx + 9)] m2) fun r3 m3 =>
  bW (callW p n "nat_ap2" [rdW (m3.arr64 IW) (cx + 10), rdW (m3.arr64 IW) (cx + 2), rdW (m3.arr64 IW) (cx + 9)] m3) fun r4 m4 =>
  bW (callW p n "nat_ap2" [rdW (m4.arr64 IW) (cx + 12), r3.headD 0, r4.headD 0] m4) fun r5 m5 =>
  bW (callW p n "nat_ap2" [rdW (m5.arr64 IW) (cx + 10), r5.headD 0, rdW (m5.arr64 IW) (cx + 9)] m5) fun r6 m6 =>
  bW (callW p n "nat_ap2" [rdW (m6.arr64 IW) (cx + 12), r2.headD 0, r6.headD 0] m6) fun r7 m7 =>
  some ([r7.headD 0], m7)

set_option maxHeartbeats 1600000 in
theorem certXorRhs_specW (p : Prog) (hp : p.lookup "cert_xor_rhs" = some certXorRhsL) (n : Nat) (s₀ : St)
    (cx c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_xor_rhs" [cx, c]
    ⦃fun r s' => LocEq s' s₀ ∧ certXorRhsW p n s₀.mem cx c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certXorRhsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_halves", callW_spec p n "nat_ap2"] <;>
    finish (gen := 30) (instances := 10000) [certXorRhsW, bW, rdW_eq]

theorem certXorRhs_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_xor_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certXorRhs cc (decI c)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mm => certXorRhsW p k mm cx c) (certXorRhs_specW p hD.lCertXorRhs k · cx c) hcall
  unfold certXorRhsW at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (certHalves_ref hD cx c cc).bind_ ⟨hS, hC, hc⟩ hw
  rw [(hC.grow hG1).f13] at hw
  rw [(hC.grow hG1).f9] at hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.mulN.word.toUInt64 cc.two.word.toUInt64 (r1.headD 0)).bind_ ⟨hS1, (word_lt32 _), (word_lt32 _), hl1⟩ hw
  have hG2 : IWGrow m m2 := hG1.trans hg2
  rw [(hC.grow hG2).f10] at hw
  rw [(hC.grow hG2).f1] at hw
  rw [(hC.grow hG2).f9] at hw
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.modN.word.toUInt64 cc.x.word.toUInt64 cc.two.word.toUInt64).bind_ ⟨hS2, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG3 : IWGrow m m3 := hG2.trans hg3
  rw [(hC.grow hG3).f10] at hw
  rw [(hC.grow hG3).f2] at hw
  rw [(hC.grow hG3).f9] at hw
  obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.modN.word.toUInt64 cc.y.word.toUInt64 cc.two.word.toUInt64).bind_ ⟨hS3, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG4 : IWGrow m m4 := hG3.trans hg4
  rw [(hC.grow hG4).f12] at hw
  obtain ⟨r5, m5, x5, a5, hrun5, ⟨hS5, hg5, hl5, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.addN.word.toUInt64 (r3.headD 0) (r4.headD 0)).bind_ ⟨hS4, (word_lt32 _), hl3, hl4⟩ hw
  have hG5 : IWGrow m m5 := hG4.trans hg5
  rw [(hC.grow hG5).f10] at hw
  rw [(hC.grow hG5).f9] at hw
  obtain ⟨r6, m6, x6, a6, hrun6, ⟨hS6, hg6, hl6, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.modN.word.toUInt64 (r5.headD 0) cc.two.word.toUInt64).bind_ ⟨hS5, (word_lt32 _), hl5, (word_lt32 _)⟩ hw
  have hG6 : IWGrow m m6 := hG5.trans hg6
  rw [(hC.grow hG6).f12] at hw
  obtain ⟨r7, m7, x7, a7, hrun7, ⟨hS7, hg7, hl7, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.addN.word.toUInt64 (r2.headD 0) (r6.headD 0)).bind_ ⟨hS6, (word_lt32 _), hl2, hl6⟩ hw
  have hG7 : IWGrow m m7 := hG6.trans hg7
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨_, a7, ?_, hS7, hG7, hl7, rfl⟩
  simp only [decE_eq_decI, decI_word] at hrun1 hrun2 hrun3 hrun4 hrun5 hrun6 hrun7
  simp only [certXorRhs, StateT.run_bind, exc_ok_bind', decE_eq_decI, decI_word, hrun1, hrun2, hrun3, hrun4, hrun5, hrun6, hrun7]
  try rfl


def certGcdW (p : Prog) (n : Nat) (m : Mem) (cx c : Word) : Option (List Word × Mem) :=
  bW (callW p n "cert_guard" [cx, rdW (m.arr64 IW) (cx + 3), rdW (m.arr64 IW) (cx + 1), rdW (m.arr64 IW) (cx + 6)] m) fun r1 m1 =>
  bW (callW p n "cert_guard" [cx, rdW (m1.arr64 IW) (cx + 3), rdW (m1.arr64 IW) (cx + 1), rdW (m1.arr64 IW) (cx + 7)] m1) fun r2 m2 =>
  bW (callW p n "nat_ap2" [rdW (m2.arr64 IW) (cx + 10), rdW (m2.arr64 IW) (cx + 2), rdW (m2.arr64 IW) (cx + 1)] m2) fun r3 m3 =>
  bW (callW p n "nat_ap2" [c, r3.headD 0, rdW (m3.arr64 IW) (cx + 1)] m3) fun r4 m4 =>
  bW (callW p n "cert_two_eqs" [cx, c, r1.headD 0, r2.headD 0, r4.headD 0, rdW (m4.arr64 IW) (cx + 2)] m4) fun r5 m5 =>
  some ([r5.headD 0, r5.tail.headD 0], m5)

set_option maxHeartbeats 1600000 in
theorem certGcd_specW (p : Prog) (hp : p.lookup "cert_gcd" = some certGcdL) (n : Nat) (s₀ : St)
    (cx c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_gcd" [cx, c]
    ⦃fun r s' => LocEq s' s₀ ∧ certGcdW p n s₀.mem cx c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certGcdL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_guard", callW_spec p n "cert_two_eqs", callW_spec p n "nat_ap2"] <;>
    finish (gen := 30) (instances := 10000) [certGcdW, bW, rdW_eq]

theorem certGcd_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_gcd" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certGcd cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mm => certGcdW p k mm cx c) (certGcd_specW p hD.lCertGcd k · cx c) hcall
  unfold certGcdW at hw
  rw [hC.f3] at hw
  rw [hC.f1] at hw
  rw [hC.f6] at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.x.word.toUInt64 cc.bT.word.toUInt64 cc).bind_ ⟨hS, hC, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  rw [(hC.grow hG1).f3] at hw
  rw [(hC.grow hG1).f1] at hw
  rw [(hC.grow hG1).f7] at hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.x.word.toUInt64 cc.bF.word.toUInt64 cc).bind_ ⟨hS1, (hC.grow hG1), (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG2 : IWGrow m m2 := hG1.trans hg2
  rw [(hC.grow hG2).f10] at hw
  rw [(hC.grow hG2).f2] at hw
  rw [(hC.grow hG2).f1] at hw
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.modN.word.toUInt64 cc.y.word.toUInt64 cc.x.word.toUInt64).bind_ ⟨hS2, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG3 : IWGrow m m3 := hG2.trans hg3
  rw [(hC.grow hG3).f1] at hw
  obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg c (r3.headD 0) cc.x.word.toUInt64).bind_ ⟨hS3, hc, hl3, (word_lt32 _)⟩ hw
  have hG4 : IWGrow m m4 := hG3.trans hg4
  rw [(hC.grow hG4).f2] at hw
  obtain ⟨r5, m5, x5, a5, hrun5, ⟨hS5, hg5, hl5⟩, hw⟩ :=
    (certTwoEqs_ref hD cx c (r1.headD 0) (r2.headD 0) (r4.headD 0) cc.y.word.toUInt64 cc).bind_ ⟨hS4, (hC.grow hG4), hc, hl1, hl2, hl4, (word_lt32 _)⟩ hw
  have hG5 : IWGrow m m5 := hG4.trans hg5
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨x5, a5, ?_, hS5, hG5, decStmtL_pair hl5⟩
  simp only [decE_eq_decI, decI_word] at hrun1 hrun2 hrun3 hrun4 hrun5
  simp only [certGcd, StateT.run_bind, exc_ok_bind', decE_eq_decI, decI_word, hrun1, hrun2, hrun3, hrun4, hrun5]
  try rfl

def certShiftLeftW (p : Prog) (n : Nat) (m : Mem) (cx c : Word) : Option (List Word × Mem) :=
  bW (callW p n "cert_guard" [cx, rdW (m.arr64 IW) (cx + 3), rdW (m.arr64 IW) (cx + 2), rdW (m.arr64 IW) (cx + 6)] m) fun r1 m1 =>
  bW (callW p n "cert_guard" [cx, rdW (m1.arr64 IW) (cx + 3), rdW (m1.arr64 IW) (cx + 2), rdW (m1.arr64 IW) (cx + 7)] m1) fun r2 m2 =>
  bW (callW p n "nat_ap2" [rdW (m2.arr64 IW) (cx + 13), rdW (m2.arr64 IW) (cx + 9), rdW (m2.arr64 IW) (cx + 1)] m2) fun r3 m3 =>
  bW (callW p n "nat_ap2" [rdW (m3.arr64 IW) (cx + 14), rdW (m3.arr64 IW) (cx + 2), rdW (m3.arr64 IW) (cx + 3)] m3) fun r4 m4 =>
  bW (callW p n "nat_ap2" [c, r3.headD 0, r4.headD 0] m4) fun r5 m5 =>
  bW (callW p n "cert_two_eqs" [cx, c, r1.headD 0, r2.headD 0, r5.headD 0, rdW (m5.arr64 IW) (cx + 1)] m5) fun r6 m6 =>
  some ([r6.headD 0, r6.tail.headD 0], m6)

set_option maxHeartbeats 1600000 in
theorem certShiftLeft_specW (p : Prog) (hp : p.lookup "cert_shift_left" = some certShiftLeftL) (n : Nat) (s₀ : St)
    (cx c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_shift_left" [cx, c]
    ⦃fun r s' => LocEq s' s₀ ∧ certShiftLeftW p n s₀.mem cx c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certShiftLeftL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_guard", callW_spec p n "cert_two_eqs", callW_spec p n "nat_ap2"] <;>
    finish (gen := 30) (instances := 10000) [certShiftLeftW, bW, rdW_eq]

theorem certShiftLeft_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_shift_left" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certShiftLeft cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mm => certShiftLeftW p k mm cx c) (certShiftLeft_specW p hD.lCertShiftLeft k · cx c) hcall
  unfold certShiftLeftW at hw
  rw [hC.f3] at hw
  rw [hC.f2] at hw
  rw [hC.f6] at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.y.word.toUInt64 cc.bT.word.toUInt64 cc).bind_ ⟨hS, hC, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  rw [(hC.grow hG1).f3] at hw
  rw [(hC.grow hG1).f2] at hw
  rw [(hC.grow hG1).f7] at hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.y.word.toUInt64 cc.bF.word.toUInt64 cc).bind_ ⟨hS1, (hC.grow hG1), (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG2 : IWGrow m m2 := hG1.trans hg2
  rw [(hC.grow hG2).f13] at hw
  rw [(hC.grow hG2).f9] at hw
  rw [(hC.grow hG2).f1] at hw
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.mulN.word.toUInt64 cc.two.word.toUInt64 cc.x.word.toUInt64).bind_ ⟨hS2, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG3 : IWGrow m m3 := hG2.trans hg3
  rw [(hC.grow hG3).f14] at hw
  rw [(hC.grow hG3).f2] at hw
  rw [(hC.grow hG3).f3] at hw
  obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.subN.word.toUInt64 cc.y.word.toUInt64 cc.one.word.toUInt64).bind_ ⟨hS3, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG4 : IWGrow m m4 := hG3.trans hg4
  obtain ⟨r5, m5, x5, a5, hrun5, ⟨hS5, hg5, hl5, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg c (r3.headD 0) (r4.headD 0)).bind_ ⟨hS4, hc, hl3, hl4⟩ hw
  have hG5 : IWGrow m m5 := hG4.trans hg5
  rw [(hC.grow hG5).f1] at hw
  obtain ⟨r6, m6, x6, a6, hrun6, ⟨hS6, hg6, hl6⟩, hw⟩ :=
    (certTwoEqs_ref hD cx c (r1.headD 0) (r2.headD 0) (r5.headD 0) cc.x.word.toUInt64 cc).bind_ ⟨hS5, (hC.grow hG5), hc, hl1, hl2, hl5, (word_lt32 _)⟩ hw
  have hG6 : IWGrow m m6 := hG5.trans hg6
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨x6, a6, ?_, hS6, hG6, decStmtL_pair hl6⟩
  simp only [decE_eq_decI, decI_word] at hrun1 hrun2 hrun3 hrun4 hrun5 hrun6
  simp only [certShiftLeft, StateT.run_bind, exc_ok_bind', decE_eq_decI, decI_word, hrun1, hrun2, hrun3, hrun4, hrun5, hrun6]
  try rfl

def certShiftRightW (p : Prog) (n : Nat) (m : Mem) (cx c : Word) : Option (List Word × Mem) :=
  bW (callW p n "cert_guard" [cx, rdW (m.arr64 IW) (cx + 3), rdW (m.arr64 IW) (cx + 2), rdW (m.arr64 IW) (cx + 6)] m) fun r1 m1 =>
  bW (callW p n "cert_guard" [cx, rdW (m1.arr64 IW) (cx + 3), rdW (m1.arr64 IW) (cx + 2), rdW (m1.arr64 IW) (cx + 7)] m1) fun r2 m2 =>
  bW (callW p n "nat_ap2" [rdW (m2.arr64 IW) (cx + 14), rdW (m2.arr64 IW) (cx + 2), rdW (m2.arr64 IW) (cx + 3)] m2) fun r3 m3 =>
  bW (callW p n "nat_ap2" [c, rdW (m3.arr64 IW) (cx + 1), r3.headD 0] m3) fun r4 m4 =>
  bW (callW p n "nat_ap2" [rdW (m4.arr64 IW) (cx + 11), r4.headD 0, rdW (m4.arr64 IW) (cx + 9)] m4) fun r5 m5 =>
  bW (callW p n "cert_two_eqs" [cx, c, r1.headD 0, r2.headD 0, r5.headD 0, rdW (m5.arr64 IW) (cx + 1)] m5) fun r6 m6 =>
  some ([r6.headD 0, r6.tail.headD 0], m6)

set_option maxHeartbeats 1600000 in
theorem certShiftRight_specW (p : Prog) (hp : p.lookup "cert_shift_right" = some certShiftRightL) (n : Nat) (s₀ : St)
    (cx c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_shift_right" [cx, c]
    ⦃fun r s' => LocEq s' s₀ ∧ certShiftRightW p n s₀.mem cx c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certShiftRightL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_guard", callW_spec p n "cert_two_eqs", callW_spec p n "nat_ap2"] <;>
    finish (gen := 30) (instances := 10000) [certShiftRightW, bW, rdW_eq]

theorem certShiftRight_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_shift_right" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certShiftRight cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mm => certShiftRightW p k mm cx c) (certShiftRight_specW p hD.lCertShiftRight k · cx c) hcall
  unfold certShiftRightW at hw
  rw [hC.f3] at hw
  rw [hC.f2] at hw
  rw [hC.f6] at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.y.word.toUInt64 cc.bT.word.toUInt64 cc).bind_ ⟨hS, hC, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  rw [(hC.grow hG1).f3] at hw
  rw [(hC.grow hG1).f2] at hw
  rw [(hC.grow hG1).f7] at hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.y.word.toUInt64 cc.bF.word.toUInt64 cc).bind_ ⟨hS1, (hC.grow hG1), (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG2 : IWGrow m m2 := hG1.trans hg2
  rw [(hC.grow hG2).f14] at hw
  rw [(hC.grow hG2).f2] at hw
  rw [(hC.grow hG2).f3] at hw
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.subN.word.toUInt64 cc.y.word.toUInt64 cc.one.word.toUInt64).bind_ ⟨hS2, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG3 : IWGrow m m3 := hG2.trans hg3
  rw [(hC.grow hG3).f1] at hw
  obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg c cc.x.word.toUInt64 (r3.headD 0)).bind_ ⟨hS3, hc, (word_lt32 _), hl3⟩ hw
  have hG4 : IWGrow m m4 := hG3.trans hg4
  rw [(hC.grow hG4).f11] at hw
  rw [(hC.grow hG4).f9] at hw
  obtain ⟨r5, m5, x5, a5, hrun5, ⟨hS5, hg5, hl5, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.divN.word.toUInt64 (r4.headD 0) cc.two.word.toUInt64).bind_ ⟨hS4, (word_lt32 _), hl4, (word_lt32 _)⟩ hw
  have hG5 : IWGrow m m5 := hG4.trans hg5
  rw [(hC.grow hG5).f1] at hw
  obtain ⟨r6, m6, x6, a6, hrun6, ⟨hS6, hg6, hl6⟩, hw⟩ :=
    (certTwoEqs_ref hD cx c (r1.headD 0) (r2.headD 0) (r5.headD 0) cc.x.word.toUInt64 cc).bind_ ⟨hS5, (hC.grow hG5), hc, hl1, hl2, hl5, (word_lt32 _)⟩ hw
  have hG6 : IWGrow m m6 := hG5.trans hg6
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨x6, a6, ?_, hS6, hG6, decStmtL_pair hl6⟩
  simp only [decE_eq_decI, decI_word] at hrun1 hrun2 hrun3 hrun4 hrun5 hrun6
  simp only [certShiftRight, StateT.run_bind, exc_ok_bind', decE_eq_decI, decI_word, hrun1, hrun2, hrun3, hrun4, hrun5, hrun6]
  try rfl

def certLandW (p : Prog) (n : Nat) (m : Mem) (cx c : Word) : Option (List Word × Mem) :=
  bW (callW p n "cert_guard" [cx, rdW (m.arr64 IW) (cx + 3), rdW (m.arr64 IW) (cx + 1), rdW (m.arr64 IW) (cx + 6)] m) fun r1 m1 =>
  bW (callW p n "cert_guard" [cx, rdW (m1.arr64 IW) (cx + 3), rdW (m1.arr64 IW) (cx + 1), rdW (m1.arr64 IW) (cx + 7)] m1) fun r2 m2 =>
  bW (callW p n "cert_halves" [cx, c] m2) fun r3 m3 =>
  bW (callW p n "nat_ap2" [rdW (m3.arr64 IW) (cx + 13), rdW (m3.arr64 IW) (cx + 9), r3.headD 0] m3) fun r4 m4 =>
  bW (callW p n "nat_ap2" [rdW (m4.arr64 IW) (cx + 10), rdW (m4.arr64 IW) (cx + 1), rdW (m4.arr64 IW) (cx + 9)] m4) fun r5 m5 =>
  bW (callW p n "nat_ap2" [rdW (m5.arr64 IW) (cx + 10), rdW (m5.arr64 IW) (cx + 2), rdW (m5.arr64 IW) (cx + 9)] m5) fun r6 m6 =>
  bW (callW p n "nat_ap2" [rdW (m6.arr64 IW) (cx + 13), r5.headD 0, r6.headD 0] m6) fun r7 m7 =>
  bW (callW p n "nat_ap2" [rdW (m7.arr64 IW) (cx + 12), r4.headD 0, r7.headD 0] m7) fun r8 m8 =>
  bW (callW p n "cert_two_eqs" [cx, c, r1.headD 0, r2.headD 0, r8.headD 0, rdW (m8.arr64 IW) (cx + 8)] m8) fun r9 m9 =>
  some ([r9.headD 0, r9.tail.headD 0], m9)

set_option maxHeartbeats 1600000 in
theorem certLand_specW (p : Prog) (hp : p.lookup "cert_land" = some certLandL) (n : Nat) (s₀ : St)
    (cx c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_land" [cx, c]
    ⦃fun r s' => LocEq s' s₀ ∧ certLandW p n s₀.mem cx c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certLandL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_guard", callW_spec p n "cert_halves", callW_spec p n "cert_two_eqs", callW_spec p n "nat_ap2"] <;>
    finish (gen := 30) (instances := 10000) [certLandW, bW, rdW_eq]

theorem certLand_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_land" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certLand cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mm => certLandW p k mm cx c) (certLand_specW p hD.lCertLand k · cx c) hcall
  unfold certLandW at hw
  rw [hC.f3] at hw
  rw [hC.f1] at hw
  rw [hC.f6] at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.x.word.toUInt64 cc.bT.word.toUInt64 cc).bind_ ⟨hS, hC, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  rw [(hC.grow hG1).f3] at hw
  rw [(hC.grow hG1).f1] at hw
  rw [(hC.grow hG1).f7] at hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.x.word.toUInt64 cc.bF.word.toUInt64 cc).bind_ ⟨hS1, (hC.grow hG1), (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG2 : IWGrow m m2 := hG1.trans hg2
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
    (certHalves_ref hD cx c cc).bind_ ⟨hS2, (hC.grow hG2), hc⟩ hw
  have hG3 : IWGrow m m3 := hG2.trans hg3
  rw [(hC.grow hG3).f13] at hw
  rw [(hC.grow hG3).f9] at hw
  obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.mulN.word.toUInt64 cc.two.word.toUInt64 (r3.headD 0)).bind_ ⟨hS3, (word_lt32 _), (word_lt32 _), hl3⟩ hw
  have hG4 : IWGrow m m4 := hG3.trans hg4
  rw [(hC.grow hG4).f10] at hw
  rw [(hC.grow hG4).f1] at hw
  rw [(hC.grow hG4).f9] at hw
  obtain ⟨r5, m5, x5, a5, hrun5, ⟨hS5, hg5, hl5, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.modN.word.toUInt64 cc.x.word.toUInt64 cc.two.word.toUInt64).bind_ ⟨hS4, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG5 : IWGrow m m5 := hG4.trans hg5
  rw [(hC.grow hG5).f10] at hw
  rw [(hC.grow hG5).f2] at hw
  rw [(hC.grow hG5).f9] at hw
  obtain ⟨r6, m6, x6, a6, hrun6, ⟨hS6, hg6, hl6, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.modN.word.toUInt64 cc.y.word.toUInt64 cc.two.word.toUInt64).bind_ ⟨hS5, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG6 : IWGrow m m6 := hG5.trans hg6
  rw [(hC.grow hG6).f13] at hw
  obtain ⟨r7, m7, x7, a7, hrun7, ⟨hS7, hg7, hl7, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.mulN.word.toUInt64 (r5.headD 0) (r6.headD 0)).bind_ ⟨hS6, (word_lt32 _), hl5, hl6⟩ hw
  have hG7 : IWGrow m m7 := hG6.trans hg7
  rw [(hC.grow hG7).f12] at hw
  obtain ⟨r8, m8, x8, a8, hrun8, ⟨hS8, hg8, hl8, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.addN.word.toUInt64 (r4.headD 0) (r7.headD 0)).bind_ ⟨hS7, (word_lt32 _), hl4, hl7⟩ hw
  have hG8 : IWGrow m m8 := hG7.trans hg8
  rw [(hC.grow hG8).f8] at hw
  obtain ⟨r9, m9, x9, a9, hrun9, ⟨hS9, hg9, hl9⟩, hw⟩ :=
    (certTwoEqs_ref hD cx c (r1.headD 0) (r2.headD 0) (r8.headD 0) cc.z.word.toUInt64 cc).bind_ ⟨hS8, (hC.grow hG8), hc, hl1, hl2, hl8, (word_lt32 _)⟩ hw
  have hG9 : IWGrow m m9 := hG8.trans hg9
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨x9, a9, ?_, hS9, hG9, decStmtL_pair hl9⟩
  simp only [decE_eq_decI, decI_word] at hrun1 hrun2 hrun3 hrun4 hrun5 hrun6 hrun7 hrun8 hrun9
  simp only [certLand, StateT.run_bind, exc_ok_bind', decE_eq_decI, decI_word, hrun1, hrun2, hrun3, hrun4, hrun5, hrun6, hrun7, hrun8, hrun9]
  try rfl

def certLorW (p : Prog) (n : Nat) (m : Mem) (cx c : Word) : Option (List Word × Mem) :=
  bW (callW p n "cert_guard" [cx, rdW (m.arr64 IW) (cx + 3), rdW (m.arr64 IW) (cx + 1), rdW (m.arr64 IW) (cx + 6)] m) fun r1 m1 =>
  bW (callW p n "cert_guard" [cx, rdW (m1.arr64 IW) (cx + 3), rdW (m1.arr64 IW) (cx + 1), rdW (m1.arr64 IW) (cx + 7)] m1) fun r2 m2 =>
  bW (callW p n "cert_lor_rhs" [cx, c] m2) fun r3 m3 =>
  bW (callW p n "cert_two_eqs" [cx, c, r1.headD 0, r2.headD 0, r3.headD 0, rdW (m3.arr64 IW) (cx + 2)] m3) fun r4 m4 =>
  some ([r4.headD 0, r4.tail.headD 0], m4)

set_option maxHeartbeats 1600000 in
theorem certLor_specW (p : Prog) (hp : p.lookup "cert_lor" = some certLorL) (n : Nat) (s₀ : St)
    (cx c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_lor" [cx, c]
    ⦃fun r s' => LocEq s' s₀ ∧ certLorW p n s₀.mem cx c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certLorL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_guard", callW_spec p n "cert_lor_rhs", callW_spec p n "cert_two_eqs"] <;>
    finish (gen := 30) (instances := 10000) [certLorW, bW, rdW_eq]

theorem certLor_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_lor" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certLor cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mm => certLorW p k mm cx c) (certLor_specW p hD.lCertLor k · cx c) hcall
  unfold certLorW at hw
  rw [hC.f3] at hw
  rw [hC.f1] at hw
  rw [hC.f6] at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.x.word.toUInt64 cc.bT.word.toUInt64 cc).bind_ ⟨hS, hC, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  rw [(hC.grow hG1).f3] at hw
  rw [(hC.grow hG1).f1] at hw
  rw [(hC.grow hG1).f7] at hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.x.word.toUInt64 cc.bF.word.toUInt64 cc).bind_ ⟨hS1, (hC.grow hG1), (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG2 : IWGrow m m2 := hG1.trans hg2
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
    (certLorRhs_ref hD cx c cc).bind_ ⟨hS2, (hC.grow hG2), hc⟩ hw
  have hG3 : IWGrow m m3 := hG2.trans hg3
  rw [(hC.grow hG3).f2] at hw
  obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4⟩, hw⟩ :=
    (certTwoEqs_ref hD cx c (r1.headD 0) (r2.headD 0) (r3.headD 0) cc.y.word.toUInt64 cc).bind_ ⟨hS3, (hC.grow hG3), hc, hl1, hl2, hl3, (word_lt32 _)⟩ hw
  have hG4 : IWGrow m m4 := hG3.trans hg4
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨x4, a4, ?_, hS4, hG4, decStmtL_pair hl4⟩
  simp only [decE_eq_decI, decI_word] at hrun1 hrun2 hrun3 hrun4
  simp only [certLor, StateT.run_bind, exc_ok_bind', decE_eq_decI, decI_word, hrun1, hrun2, hrun3, hrun4]
  try rfl

def certXorW (p : Prog) (n : Nat) (m : Mem) (cx c : Word) : Option (List Word × Mem) :=
  bW (callW p n "cert_guard" [cx, rdW (m.arr64 IW) (cx + 3), rdW (m.arr64 IW) (cx + 1), rdW (m.arr64 IW) (cx + 6)] m) fun r1 m1 =>
  bW (callW p n "cert_guard" [cx, rdW (m1.arr64 IW) (cx + 3), rdW (m1.arr64 IW) (cx + 1), rdW (m1.arr64 IW) (cx + 7)] m1) fun r2 m2 =>
  bW (callW p n "cert_xor_rhs" [cx, c] m2) fun r3 m3 =>
  bW (callW p n "cert_two_eqs" [cx, c, r1.headD 0, r2.headD 0, r3.headD 0, rdW (m3.arr64 IW) (cx + 2)] m3) fun r4 m4 =>
  some ([r4.headD 0, r4.tail.headD 0], m4)

set_option maxHeartbeats 1600000 in
theorem certXor_specW (p : Prog) (hp : p.lookup "cert_xor" = some certXorL) (n : Nat) (s₀ : St)
    (cx c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_xor" [cx, c]
    ⦃fun r s' => LocEq s' s₀ ∧ certXorW p n s₀.mem cx c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certXorL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_guard", callW_spec p n "cert_two_eqs", callW_spec p n "cert_xor_rhs"] <;>
    finish (gen := 30) (instances := 10000) [certXorW, bW, rdW_eq]

theorem certXor_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_xor" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certXor cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mm => certXorW p k mm cx c) (certXor_specW p hD.lCertXor k · cx c) hcall
  unfold certXorW at hw
  rw [hC.f3] at hw
  rw [hC.f1] at hw
  rw [hC.f6] at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.x.word.toUInt64 cc.bT.word.toUInt64 cc).bind_ ⟨hS, hC, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  rw [(hC.grow hG1).f3] at hw
  rw [(hC.grow hG1).f1] at hw
  rw [(hC.grow hG1).f7] at hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.x.word.toUInt64 cc.bF.word.toUInt64 cc).bind_ ⟨hS1, (hC.grow hG1), (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG2 : IWGrow m m2 := hG1.trans hg2
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
    (certXorRhs_ref hD cx c cc).bind_ ⟨hS2, (hC.grow hG2), hc⟩ hw
  have hG3 : IWGrow m m3 := hG2.trans hg3
  rw [(hC.grow hG3).f2] at hw
  obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4⟩, hw⟩ :=
    (certTwoEqs_ref hD cx c (r1.headD 0) (r2.headD 0) (r3.headD 0) cc.y.word.toUInt64 cc).bind_ ⟨hS3, (hC.grow hG3), hc, hl1, hl2, hl3, (word_lt32 _)⟩ hw
  have hG4 : IWGrow m m4 := hG3.trans hg4
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨x4, a4, ?_, hS4, hG4, decStmtL_pair hl4⟩
  simp only [decE_eq_decI, decI_word] at hrun1 hrun2 hrun3 hrun4
  simp only [certXor, StateT.run_bind, exc_ok_bind', decE_eq_decI, decI_word, hrun1, hrun2, hrun3, hrun4]
  try rfl


/-! ## `cert_rec_rhs` -/

def certRecRhsW (p : Prog) (n : Nat) (m : Mem) (cx c : Word) : Option (List Word × Mem) :=
  bW (callW p n "nat_ap2" [rdW (m.arr64 IW) (cx + 14), rdW (m.arr64 IW) (cx + 1),
    rdW (m.arr64 IW) (cx + 2)] m) fun r1 m1 =>
  bW (callW p n "nat_ap2" [c, r1.headD 0, rdW (m1.arr64 IW) (cx + 2)] m1) fun r2 m2 =>
  if c = rdW (m2.arr64 IW) (cx + 11) then
    bW (callW p n "pin_at" [3] m2) fun r3 m3 =>
    bW (callW p n "nat_ap1" [r3.headD 0, r2.headD 0] m3) fun r4 m4 => some ([r4.headD 0], m4)
  else some ([r2.headD 0], m2)

set_option maxHeartbeats 1600000 in
theorem certRecRhs_specW (p : Prog) (hp : p.lookup "cert_rec_rhs" = some certRecRhsL) (n : Nat)
    (s₀ : St) (cx c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_rec_rhs" [cx, c]
    ⦃fun r s' => LocEq s' s₀ ∧ certRecRhsW p n s₀.mem cx c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certRecRhsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_ap2", callW_spec p n "pin_at", callW_spec p n "nat_ap1"] <;>
    finish (gen := 30) (instances := 10000) [certRecRhsW, bW, rdW_eq]

theorem certRecRhs_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_rec_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certRecRhs cc (decI c)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mq => certRecRhsW p k mq cx c)
    (certRecRhs_specW p hD.lCertRecRhs k · cx c) hcall
  unfold certRecRhsW at hw
  rw [hC.f14, hC.f1, hC.f2] at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.subN.word.toUInt64 cc.x.word.toUInt64 cc.y.word.toUInt64).bind_
      ⟨hS, word_lt32 _, word_lt32 _, word_lt32 _⟩ hw
  rw [(hC.grow hG1).f2] at hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg c (r1.headD 0) cc.y.word.toUInt64).bind_
      ⟨hS1, hc, hl1, word_lt32 _⟩ hw
  have hG2 : IWGrow m m2 := hG1.trans hg2
  rw [(hC.grow hG2).f11] at hw
  simp only [decE_eq_decI, decI_word] at hrun1 hrun2
  have hb := decI_beq_word (κ := IdxKind.name) hc (word_lt32 cc.divN)
  simp only [decI_word] at hb
  by_cases hd : c = cc.divN.word.toUInt64
  · rw [if_pos hd] at hw
    obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
      (pinSlot_ref p hD.lPinAt 3 pinNatSucc rfl).bind_ hS2 hw
    obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hw⟩ :=
      (natAp1_ref hD.toNatEqProg (r3.headD 0) (r2.headD 0)).bind_ ⟨hS3, hl3, hl2⟩ hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨_, a4, ?_, hS4, hG2.trans (hg3.trans hg4), hl4, rfl⟩
    simp only [decE_eq_decI, decI_word] at hrun4
    have hb' : (decI c == cc.divN) = true := by rw [hb]; exact decide_eq_true hd
    simp only [certRecRhs, StateT.run_bind, exc_ok_bind', hrun1, hrun2, hb', if_true, hrun3, hrun4]
    try rfl
  · rw [if_neg hd] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨_, a2, ?_, hS2, hG2, hl2, rfl⟩
    have hb' : (decI c == cc.divN) = false := by rw [hb]; exact decide_eq_false hd
    simp only [certRecRhs, StateT.run_bind, exc_ok_bind', hrun1, hrun2, hb', Bool.false_eq_true,
      if_false]
    try rfl

/-! ## `cert_div_mod_eqs` -/

def certDivModEqsW (p : Prog) (n : Nat) (m : Mem) (cx c h1 h2 h3 h4 recRhs baseRhs : Word) :
    Option (List Word × Mem) :=
  bW (callW p n "cert_eq" [cx, c, recRhs] m) fun r1 m1 =>
  bW (callW p n "cert_eq" [cx, c, baseRhs] m1) fun r2 m2 =>
  bW (callW p n "rec2" [h1, h2] m2) fun r3 m3 =>
  bW (callW p n "rec3" [r3.headD 0, 2, r1.headD 0] m3) fun r4 m4 =>
  bW (callW p n "stmt1" [h3, r2.headD 0] m4) fun r5 m5 =>
  bW (callW p n "stmt1" [h4, r2.headD 0] m5) fun r6 m6 =>
  bW (callW p n "rec3" [r4.headD 0, r5.headD 0, r6.headD 0] m6) fun r7 m7 =>
  some ([r7.headD 0, 3], m7)

set_option maxHeartbeats 1600000 in
theorem certDivModEqs_specW (p : Prog) (hp : p.lookup "cert_div_mod_eqs" = some certDivModEqsL)
    (n : Nat) (s₀ : St) (cx c h1 h2 h3 h4 recRhs baseRhs : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_div_mod_eqs" [cx, c, h1, h2, h3, h4, recRhs, baseRhs]
    ⦃fun r s' => LocEq s' s₀ ∧ certDivModEqsW p n s₀.mem cx c h1 h2 h3 h4 recRhs baseRhs = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certDivModEqsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_eq", callW_spec p n "rec2", callW_spec p n "rec3",
      callW_spec p n "stmt1"] <;>
    finish (gen := 30) (instances := 10000) [certDivModEqsW, bW]

theorem certDivModEqs_ref (hD : DmProg2 p) (cx c h1 h2 h3 h4 recRhs baseRhs : Word) (cc : CertCtxA) :
    CallRef p "cert_div_mod_eqs" [cx, c, h1, h2, h3, h4, recRhs, baseRhs]
      (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c ∧ H h1 ∧ H h2 ∧ H h3 ∧ H h4 ∧
        H recRhs ∧ H baseRhs)
      (certDivModEqs cc (decI c) (decE h1) (decE h2) (decE h3) (decE h4) (decE recRhs) (decE baseRhs))
      (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc, hh1, hh2, hh3, hh4, hrr, hbr⟩ hcall => ?_
  have hw := callW_model (M := fun mq => certDivModEqsW p k mq cx c h1 h2 h3 h4 recRhs baseRhs)
    (certDivModEqs_specW p hD.lCertDivModEqs k · cx c h1 h2 h3 h4 recRhs baseRhs) hcall
  unfold certDivModEqsW at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1, rfl⟩, hw⟩ :=
    (certEq_ref hD cx c recRhs cc).bind_ ⟨hS, hC, hc, hrr⟩ hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (certEq_ref hD cx c baseRhs cc).bind_ ⟨hS1, hC.grow hg1, hc, hbr⟩ hw
  obtain ⟨r3, m3, hrec3, hw⟩ := (rec2_fref p hD.lIwAlloc hD.lRec2 h1 h2).bind_ hS2.2 hw
  have hS3 := hrec3.2.1.stage hS2
  obtain ⟨r4, m4, hrec4, hw⟩ :=
    (rec3_fref p hD.lIwAlloc hD.lRec3 (r3.headD 0) 2 (r1.headD 0)).bind_ hS3.2 hw
  have hS4 := hrec4.2.1.stage hS3
  obtain ⟨r5, m5, x5, a5, hrun5, ⟨hS5, hg5, hs5⟩, hw⟩ :=
    (stmt1_ref hD h3 (r2.headD 0)).bind_ ⟨hS4, hh3, hl2⟩ hw
  obtain ⟨rfl, rfl⟩ := pure_run_eq hrun5
  obtain ⟨r6, m6, x6, a6, hrun6, ⟨hS6, hg6, hs6⟩, hw⟩ :=
    (stmt1_ref hD h4 (r2.headD 0)).bind_ ⟨hS5, hh4, hl2⟩ hw
  obtain ⟨rfl, rfl⟩ := pure_run_eq hrun6
  obtain ⟨r7, m7, hrec7, hw⟩ :=
    (rec3_fref p hD.lIwAlloc hD.lRec3 (r4.headD 0) (r5.headD 0) (r6.headD 0)).bind_ hS6.2 hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hq3 : (r3.headD 0).toNat = iwTop m2 := by rw [hrec3.1]; rfl
  have hbound : (r3.headD 0).toNat + (2 : Word).toNat ≤ iwTop m3 := by
    have h2w : (2 : Word).toNat = 2 := rfl
    have hl : [h1, h2].length = 2 := rfl
    have := hrec3.2.2.2.1; rw [hl] at this; rw [h2w, hq3]; omega
  have hdec : decHL m3 (r3.headD 0).toNat (2 : Word).toNat = some [decE h1, decE h2] :=
    rec2_dec hrec3 hh1 hh2
  have st1 := stmtAt_of_rec3 hrec4 hS3.2 hbound hdec hl1
  refine ⟨[([decE h1, decE h2], decE (r1.headD 0)), ([decE h3], decE (r2.headD 0)),
    ([decE h4], decE (r2.headD 0))], _, ?_, hrec7.2.1.stage hS6,
    (hg1.trans hg2).trans (hrec3.2.1.1.trans (hrec4.2.1.1.trans (hg5.trans (hg6.trans hrec7.2.1.1)))),
    stmtL_of_rec3 hrec7 (st1.grow (hg5.trans hg6)) (hs5.grow hg6) hs6⟩
  simp only [decE_eq_decI] at hrun1 hrun2
  simp only [certDivModEqs, StateT.run_bind, exc_ok_bind', decE_eq_decI, hrun1, hrun2]
  try rfl


def certDivModGuardsW (p : Prog) (n : Nat) (m : Mem) (cx c recRhs baseRhs : Word) : Option (List Word × Mem) :=
  bW (callW p n "cert_guard" [cx, rdW (m.arr64 IW) (cx + 2), rdW (m.arr64 IW) (cx + 1), rdW (m.arr64 IW) (cx + 6)] m) fun r1 m1 =>
  bW (callW p n "cert_guard" [cx, rdW (m1.arr64 IW) (cx + 3), rdW (m1.arr64 IW) (cx + 2), rdW (m1.arr64 IW) (cx + 6)] m1) fun r2 m2 =>
  bW (callW p n "cert_guard" [cx, rdW (m2.arr64 IW) (cx + 2), rdW (m2.arr64 IW) (cx + 1), rdW (m2.arr64 IW) (cx + 7)] m2) fun r3 m3 =>
  bW (callW p n "cert_guard" [cx, rdW (m3.arr64 IW) (cx + 3), rdW (m3.arr64 IW) (cx + 2), rdW (m3.arr64 IW) (cx + 7)] m3) fun r4 m4 =>
  bW (callW p n "cert_div_mod_eqs" [cx, c, r1.headD 0, r2.headD 0, r3.headD 0, r4.headD 0, recRhs, baseRhs] m4) fun r5 m5 =>
  some ([r5.headD 0, r5.tail.headD 0], m5)

set_option maxHeartbeats 1600000 in
theorem certDivModGuards_specW (p : Prog) (hp : p.lookup "cert_div_mod_guards" = some certDivModGuardsL) (n : Nat) (s₀ : St)
    (cx c recRhs baseRhs : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_div_mod_guards" [cx, c, recRhs, baseRhs]
    ⦃fun r s' => LocEq s' s₀ ∧ certDivModGuardsW p n s₀.mem cx c recRhs baseRhs = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certDivModGuardsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_div_mod_eqs", callW_spec p n "cert_guard"] <;>
    finish (gen := 30) (instances := 10000) [certDivModGuardsW, bW, rdW_eq]

theorem certDivModGuards_ref (hD : DmProg2 p) (cx c recRhs baseRhs : Word) (cc : CertCtxA) :
    CallRef p "cert_div_mod_guards" [cx, c, recRhs, baseRhs] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c ∧ H recRhs ∧ H baseRhs)
      (certDivModGuards cc (decI c) (decE recRhs) (decE baseRhs)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc, hrecRhs, hbaseRhs⟩ hcall => ?_
  have hw := callW_model (M := fun mm => certDivModGuardsW p k mm cx c recRhs baseRhs) (certDivModGuards_specW p hD.lCertDivModGuards k · cx c recRhs baseRhs) hcall
  unfold certDivModGuardsW at hw
  rw [hC.f2] at hw
  rw [hC.f1] at hw
  rw [hC.f6] at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.y.word.toUInt64 cc.x.word.toUInt64 cc.bT.word.toUInt64 cc).bind_ ⟨hS, hC, (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  rw [(hC.grow hG1).f3] at hw
  rw [(hC.grow hG1).f2] at hw
  rw [(hC.grow hG1).f6] at hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.y.word.toUInt64 cc.bT.word.toUInt64 cc).bind_ ⟨hS1, (hC.grow hG1), (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG2 : IWGrow m m2 := hG1.trans hg2
  rw [(hC.grow hG2).f2] at hw
  rw [(hC.grow hG2).f1] at hw
  rw [(hC.grow hG2).f7] at hw
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.y.word.toUInt64 cc.x.word.toUInt64 cc.bF.word.toUInt64 cc).bind_ ⟨hS2, (hC.grow hG2), (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG3 : IWGrow m m3 := hG2.trans hg3
  rw [(hC.grow hG3).f3] at hw
  rw [(hC.grow hG3).f2] at hw
  rw [(hC.grow hG3).f7] at hw
  obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hw⟩ :=
    (certGuard_ref hD cx cc.one.word.toUInt64 cc.y.word.toUInt64 cc.bF.word.toUInt64 cc).bind_ ⟨hS3, (hC.grow hG3), (word_lt32 _), (word_lt32 _), (word_lt32 _)⟩ hw
  have hG4 : IWGrow m m4 := hG3.trans hg4
  obtain ⟨r5, m5, x5, a5, hrun5, ⟨hS5, hg5, hl5⟩, hw⟩ :=
    (certDivModEqs_ref hD cx c (r1.headD 0) (r2.headD 0) (r3.headD 0) (r4.headD 0) recRhs baseRhs cc).bind_ ⟨hS4, (hC.grow hG4), hc, hl1, hl2, hl3, hl4, hrecRhs, hbaseRhs⟩ hw
  have hG5 : IWGrow m m5 := hG4.trans hg5
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨x5, a5, ?_, hS5, hG5, decStmtL_pair hl5⟩
  simp only [decE_eq_decI, decI_word] at hrun1 hrun2 hrun3 hrun4 hrun5
  simp only [certDivModGuards, StateT.run_bind, exc_ok_bind', decE_eq_decI, decI_word, hrun1, hrun2, hrun3, hrun4, hrun5]
  try rfl



/-! ## `cert_div_mod` -/

def certDivModW (p : Prog) (n : Nat) (m : Mem) (cx c : Word) : Option (List Word × Mem) :=
  bW (callW p n "cert_rec_rhs" [cx, c] m) fun r1 m1 =>
  bW (callW p n "cert_div_mod_guards" [cx, c, r1.headD 0,
    if c = rdW (m1.arr64 IW) (cx + 11) then rdW (m1.arr64 IW) (cx + 8) else rdW (m1.arr64 IW) (cx + 1)] m1)
    fun r2 m2 => some ([r2.headD 0, r2.tail.headD 0], m2)

set_option maxHeartbeats 1600000 in
theorem certDivMod_specW (p : Prog) (hp : p.lookup "cert_div_mod" = some certDivModL) (n : Nat)
    (s₀ : St) (cx c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_div_mod" [cx, c]
    ⦃fun r s' => LocEq s' s₀ ∧ certDivModW p n s₀.mem cx c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certDivModL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_rec_rhs", callW_spec p n "cert_div_mod_guards"] <;>
    finish (gen := 30) (instances := 10000) [certDivModW, bW, rdW_eq]

theorem certDivMod_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_div_mod" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certDivMod cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mq => certDivModW p k mq cx c)
    (certDivMod_specW p hD.lCertDivMod k · cx c) hcall
  unfold certDivModW at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (certRecRhs_ref hD cx c cc).bind_ ⟨hS, hC, hc⟩ hw
  have hC1 := hC.grow hG1
  rw [hC1.f11, hC1.f8, hC1.f1] at hw
  have hb := decI_beq_word (κ := IdxKind.name) hc (word_lt32 cc.divN)
  simp only [decI_word] at hb
  by_cases hd : c = cc.divN.word.toUInt64
  · rw [if_pos hd] at hw
    obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2⟩, hw⟩ :=
      (certDivModGuards_ref hD cx c (r1.headD 0) cc.z.word.toUInt64 cc).bind_
        ⟨hS1, hC1, hc, hl1, word_lt32 _⟩ hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨x2, a2, ?_, hS2, hG1.trans hg2, decStmtL_pair hl2⟩
    have hb' : (decI c == cc.divN) = true := by rw [hb]; exact decide_eq_true hd
    simp only [decE_eq_decI, decI_word] at hrun2
    simp only [certDivMod, StateT.run_bind, exc_ok_bind', hrun1, hb', if_true, hrun2]
    try rfl
  · rw [if_neg hd] at hw
    obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2⟩, hw⟩ :=
      (certDivModGuards_ref hD cx c (r1.headD 0) cc.x.word.toUInt64 cc).bind_
        ⟨hS1, hC1, hc, hl1, word_lt32 _⟩ hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨x2, a2, ?_, hS2, hG1.trans hg2, decStmtL_pair hl2⟩
    have hb' : (decI c == cc.divN) = false := by rw [hb]; exact decide_eq_false hd
    simp only [decE_eq_decI, decI_word] at hrun2
    simp only [certDivMod, StateT.run_bind, exc_ok_bind', hrun1, hb', Bool.false_eq_true, if_false,
      hrun2]
    try rfl

/-! ## `div_mod_cert_stmts_at` -/
def divModCertStmtsAtW (p : Prog) (n : Nat) (m : Mem) (cx c : Word) : Option (List Word × Mem) :=
  if c = rdW (m.arr64 IW) (cx + 15) then
    bW (callW p n "cert_gcd" [cx, c] m) fun r m' => some ([r.headD 0, r.tail.headD 0], m')
  else if c = rdW (m.arr64 IW) (cx + 16) then
    bW (callW p n "cert_shift_left" [cx, c] m) fun r m' => some ([r.headD 0, r.tail.headD 0], m')
  else if c = rdW (m.arr64 IW) (cx + 17) then
    bW (callW p n "cert_shift_right" [cx, c] m) fun r m' => some ([r.headD 0, r.tail.headD 0], m')
  else if c = rdW (m.arr64 IW) (cx + 18) then
    bW (callW p n "cert_land" [cx, c] m) fun r m' => some ([r.headD 0, r.tail.headD 0], m')
  else if c = rdW (m.arr64 IW) (cx + 19) then
    bW (callW p n "cert_lor" [cx, c] m) fun r m' => some ([r.headD 0, r.tail.headD 0], m')
  else if c = rdW (m.arr64 IW) (cx + 20) then
    bW (callW p n "cert_xor" [cx, c] m) fun r m' => some ([r.headD 0, r.tail.headD 0], m')
  else bW (callW p n "cert_div_mod" [cx, c] m) fun r m' => some ([r.headD 0, r.tail.headD 0], m')

set_option maxHeartbeats 1600000 in
theorem divModCertStmtsAt_specW (p : Prog) (hp : p.lookup "div_mod_cert_stmts_at" = some divModCertStmtsAtL)
    (n : Nat) (s₀ : St) (cx c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "div_mod_cert_stmts_at" [cx, c]
    ⦃fun r s' => LocEq s' s₀ ∧ divModCertStmtsAtW p n s₀.mem cx c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divModCertStmtsAtL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_gcd", callW_spec p n "cert_shift_left", callW_spec p n "cert_shift_right", callW_spec p n "cert_land", callW_spec p n "cert_lor", callW_spec p n "cert_xor", callW_spec p n "cert_div_mod"] <;>
    finish (gen := 30) (instances := 10000) [divModCertStmtsAtW, bW, rdW_eq]

theorem divModCertStmtsAt_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "div_mod_cert_stmts_at" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (divModCertStmtsAt cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mq => divModCertStmtsAtW p k mq cx c)
    (divModCertStmtsAt_specW p hD.lDivModCertStmtsAt k · cx c) hcall
  unfold divModCertStmtsAtW at hw
  rw [hC.f15, hC.f16, hC.f17, hC.f18, hC.f19, hC.f20] at hw
  have b15 := decI_beq_word (κ := IdxKind.name) hc (word_lt32 cc.gcdN)
  simp only [decI_word] at b15
  have b16 := decI_beq_word (κ := IdxKind.name) hc (word_lt32 cc.slN)
  simp only [decI_word] at b16
  have b17 := decI_beq_word (κ := IdxKind.name) hc (word_lt32 cc.srN)
  simp only [decI_word] at b17
  have b18 := decI_beq_word (κ := IdxKind.name) hc (word_lt32 cc.landN)
  simp only [decI_word] at b18
  have b19 := decI_beq_word (κ := IdxKind.name) hc (word_lt32 cc.lorN)
  simp only [decI_word] at b19
  have b20 := decI_beq_word (κ := IdxKind.name) hc (word_lt32 cc.xorN)
  simp only [decI_word] at b20
  by_cases h15 : c = cc.gcdN.word.toUInt64
  · rw [if_pos h15] at hw
    obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1⟩, hw⟩ :=
      (certGcd_ref hD cx c cc).bind_ ⟨hS, hC, hc⟩ hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨x1, a1, ?_, hS1, hg1, decStmtL_pair hl1⟩
    have hb' : (decI c == cc.gcdN) = true := by rw [b15]; exact decide_eq_true h15
    simp only [divModCertStmtsAt, StateT.run_bind, hb', if_true]
    exact hrun1
  rw [if_neg h15] at hw
  have hb15' : (decI c == cc.gcdN) = false := by rw [b15]; exact decide_eq_false h15
  by_cases h16 : c = cc.slN.word.toUInt64
  · rw [if_pos h16] at hw
    obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1⟩, hw⟩ :=
      (certShiftLeft_ref hD cx c cc).bind_ ⟨hS, hC, hc⟩ hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨x1, a1, ?_, hS1, hg1, decStmtL_pair hl1⟩
    have hb' : (decI c == cc.slN) = true := by rw [b16]; exact decide_eq_true h16
    simp only [divModCertStmtsAt, StateT.run_bind, hb15', hb', Bool.false_eq_true, if_false, if_true]
    exact hrun1
  rw [if_neg h16] at hw
  have hb16' : (decI c == cc.slN) = false := by rw [b16]; exact decide_eq_false h16
  by_cases h17 : c = cc.srN.word.toUInt64
  · rw [if_pos h17] at hw
    obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1⟩, hw⟩ :=
      (certShiftRight_ref hD cx c cc).bind_ ⟨hS, hC, hc⟩ hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨x1, a1, ?_, hS1, hg1, decStmtL_pair hl1⟩
    have hb' : (decI c == cc.srN) = true := by rw [b17]; exact decide_eq_true h17
    simp only [divModCertStmtsAt, StateT.run_bind, hb15', hb16', hb', Bool.false_eq_true, if_false, if_true]
    exact hrun1
  rw [if_neg h17] at hw
  have hb17' : (decI c == cc.srN) = false := by rw [b17]; exact decide_eq_false h17
  by_cases h18 : c = cc.landN.word.toUInt64
  · rw [if_pos h18] at hw
    obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1⟩, hw⟩ :=
      (certLand_ref hD cx c cc).bind_ ⟨hS, hC, hc⟩ hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨x1, a1, ?_, hS1, hg1, decStmtL_pair hl1⟩
    have hb' : (decI c == cc.landN) = true := by rw [b18]; exact decide_eq_true h18
    simp only [divModCertStmtsAt, StateT.run_bind, hb15', hb16', hb17', hb', Bool.false_eq_true, if_false, if_true]
    exact hrun1
  rw [if_neg h18] at hw
  have hb18' : (decI c == cc.landN) = false := by rw [b18]; exact decide_eq_false h18
  by_cases h19 : c = cc.lorN.word.toUInt64
  · rw [if_pos h19] at hw
    obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1⟩, hw⟩ :=
      (certLor_ref hD cx c cc).bind_ ⟨hS, hC, hc⟩ hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨x1, a1, ?_, hS1, hg1, decStmtL_pair hl1⟩
    have hb' : (decI c == cc.lorN) = true := by rw [b19]; exact decide_eq_true h19
    simp only [divModCertStmtsAt, StateT.run_bind, hb15', hb16', hb17', hb18', hb', Bool.false_eq_true, if_false, if_true]
    exact hrun1
  rw [if_neg h19] at hw
  have hb19' : (decI c == cc.lorN) = false := by rw [b19]; exact decide_eq_false h19
  by_cases h20 : c = cc.xorN.word.toUInt64
  · rw [if_pos h20] at hw
    obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1⟩, hw⟩ :=
      (certXor_ref hD cx c cc).bind_ ⟨hS, hC, hc⟩ hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨x1, a1, ?_, hS1, hg1, decStmtL_pair hl1⟩
    have hb' : (decI c == cc.xorN) = true := by rw [b20]; exact decide_eq_true h20
    simp only [divModCertStmtsAt, StateT.run_bind, hb15', hb16', hb17', hb18', hb19', hb', Bool.false_eq_true, if_false, if_true]
    exact hrun1
  rw [if_neg h20] at hw
  have hb20' : (decI c == cc.xorN) = false := by rw [b20]; exact decide_eq_false h20
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1⟩, hw⟩ :=
    (certDivMod_ref hD cx c cc).bind_ ⟨hS, hC, hc⟩ hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨x1, a1, ?_, hS1, hg1, decStmtL_pair hl1⟩
  simp only [divModCertStmtsAt, StateT.run_bind, hb15', hb16', hb17', hb18', hb19', hb20', Bool.false_eq_true, if_false]
  exact hrun1

/-! ## `div_mod_cert_stmts` -/

def divModCertStmtsW (p : Prog) (n : Nat) (m : Mem) (c : Word) : Option (List Word × Mem) :=
  bW (callW p n "cert_ctx" [] m) fun r1 m1 =>
  bW (callW p n "div_mod_cert_stmts_at" [r1.headD 0, c] m1) fun r2 m2 =>
  some ([r2.headD 0, r2.tail.headD 0], m2)

theorem divModCertStmts_specW (p : Prog) (hp : p.lookup "div_mod_cert_stmts" = some divModCertStmtsL)
    (n : Nat) (s₀ : St) (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "div_mod_cert_stmts" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ divModCertStmtsW p n s₀.mem c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divModCertStmtsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_ctx", callW_spec p n "div_mod_cert_stmts_at"] <;>
    finish (gen := 20) (instances := 10000) [divModCertStmtsW, bW]

theorem divModCertStmts_ref (hD : DmProg2 p) (c : Word) :
    CallRef p "div_mod_cert_stmts" [c] (fun m s => StageR dn vis fe m s ∧ H c)
      (divModCertStmts (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mq => divModCertStmtsW p k mq c)
    (divModCertStmts_specW p hD.lDivModCertStmts k · c) hcall
  unfold divModCertStmtsW at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hctx⟩, hw⟩ := (certCtx_ref hD).bind_ hS hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2⟩, hw⟩ :=
    (divModCertStmtsAt_ref hD (r1.headD 0) c x1).bind_ ⟨hS1, hctx, hc⟩ hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨x2, a2, ?_, hS2, hg1.trans hg2, decStmtL_pair hl2⟩
  simp only [divModCertStmts, StateT.run_bind, hrun1, exc_ok_bind']
  exact hrun2

@[refines ConRon.Arena.certLorRhs]
theorem certLorRhs_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_lor_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certLorRhs cc (decI c)) (KeepPost dn vis fe decW0E) :=
  (certLorRhs_ref hD cx c cc).refAM

@[refines ConRon.Arena.certXorRhs]
theorem certXorRhs_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_xor_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certXorRhs cc (decI c)) (KeepPost dn vis fe decW0E) :=
  (certXorRhs_ref hD cx c cc).refAM

@[refines ConRon.Arena.certGcd]
theorem certGcd_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_gcd" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certGcd cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certGcd_ref hD cx c cc).refAM

@[refines ConRon.Arena.certShiftLeft]
theorem certShiftLeft_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_shift_left" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certShiftLeft cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certShiftLeft_ref hD cx c cc).refAM

@[refines ConRon.Arena.certShiftRight]
theorem certShiftRight_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_shift_right" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certShiftRight cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certShiftRight_ref hD cx c cc).refAM

@[refines ConRon.Arena.certLand]
theorem certLand_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_land" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certLand cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certLand_ref hD cx c cc).refAM

@[refines ConRon.Arena.certLor]
theorem certLor_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_lor" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certLor cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certLor_ref hD cx c cc).refAM

@[refines ConRon.Arena.certXor]
theorem certXor_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_xor" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certXor cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certXor_ref hD cx c cc).refAM

@[refines ConRon.Arena.certRecRhs]
theorem certRecRhs_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_rec_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certRecRhs cc (decI c)) (KeepPost dn vis fe decW0E) :=
  (certRecRhs_ref hD cx c cc).refAM

@[refines ConRon.Arena.certDivModEqs]
theorem certDivModEqs_refines (hD : DmProg2 p) (cx c h1 h2 h3 h4 recRhs baseRhs : Word) (cc : CertCtxA) :
    RefAM p "cert_div_mod_eqs" [cx, c, h1, h2, h3, h4, recRhs, baseRhs]
      (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c ∧ H h1 ∧ H h2 ∧ H h3 ∧ H h4 ∧
        H recRhs ∧ H baseRhs)
      (certDivModEqs cc (decI c) (decE h1) (decE h2) (decE h3) (decE h4) (decE recRhs) (decE baseRhs))
      (KeepPost dn vis fe decStmtL) :=
  (certDivModEqs_ref hD cx c h1 h2 h3 h4 recRhs baseRhs cc).refAM

@[refines ConRon.Arena.certDivModGuards]
theorem certDivModGuards_refines (hD : DmProg2 p) (cx c recRhs baseRhs : Word) (cc : CertCtxA) :
    RefAM p "cert_div_mod_guards" [cx, c, recRhs, baseRhs] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c ∧ H recRhs ∧ H baseRhs)
      (certDivModGuards cc (decI c) (decE recRhs) (decE baseRhs)) (KeepPost dn vis fe decStmtL) :=
  (certDivModGuards_ref hD cx c recRhs baseRhs cc).refAM

@[refines ConRon.Arena.certDivMod]
theorem certDivMod_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_div_mod" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (certDivMod cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certDivMod_ref hD cx c cc).refAM

@[refines ConRon.Arena.divModCertStmtsAt]
theorem divModCertStmtsAt_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "div_mod_cert_stmts_at" [cx, c] (fun m s => StageR dn vis fe m s ∧ CtxR m cx cc ∧ H c)
      (divModCertStmtsAt cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (divModCertStmtsAt_ref hD cx c cc).refAM

@[refines ConRon.Arena.divModCertStmts]
theorem divModCertStmts_refines (hD : DmProg2 p) (c : Word) :
    RefAM p "div_mod_cert_stmts" [c] (fun m s => StageR dn vis fe m s ∧ H c)
      (divModCertStmts (decI c)) (KeepPost dn vis fe decStmtL) :=
  (divModCertStmts_ref hD c).refAM

end nat

end L.Ind
