import ConAgua.Arena.DeclDivMod3

/-!
# The `Nat.div` family's pin gate, bottom up: the certificate builders, part 4 (lane `decls3`, `decls3-divmod`)

The seven certificate builders and the dispatch `div_mod_cert_stmts_at`, `div_mod_cert_stmts`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section nat
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-- The model's `if c = w` against the twin's `if decI c == N`, `w` the word of `N`. -/
theorem Sim.iteW {β α : Type} {N : NIdx} {c w : Word} {e1 e2 : Option (β × Mem)} {o1 o2 : AM α}
    {a : AState} {R : β → α → Mem → AState → Prop} (hw : w = N.word.toUInt64) (hc : H c)
    (h1 : c = w → Sim e1 o1 a R) (h2 : c ≠ w → Sim e2 o2 a R) :
    Sim (if c = w then e1 else e2) (if decI c == N then o1 else o2) a R := by
  subst hw
  have hb := decI_beq_word (κ := IdxKind.name) hc (dmWord_lt32 N)
  rw [decI_word] at hb
  by_cases hd : c = N.word.toUInt64
  · rw [ite_eq_left hd, hb, decide_eq_true hd, ite_eq_left rfl]; exact h1 hd
  · rw [ite_eq_right hd, hb, decide_eq_false hd]; exact h2 hd

/-- A last callee returning a statement list `(o, l)`. -/
theorem CallRef.simPair {f : FnName} {args : List Word} {pre : Mem → AState → Prop}
    {op : AM (List (List EIdx × EIdx))} (h : CallRef p f args pre op (KeepPost dn vis fe decStmtL)) {n : Nat}
    {m m0 : Mem} {a : AState} (hp : pre m a) (hG : IWGrow m0 m) :
    Sim (ntBW (callW p n f args m) fun r m' => some ([r.headD 0, r.tail.headD 0], m')) op a
      (fun r x m' a' => KeepPost dn vis fe decStmtL m0 m' a' r x) :=
  Sim.ntRet (h.simG hp hG) fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, decStmtL_pair h3⟩

/-- **`cert_lor_rhs` is its model `certLorRhsW`** (generated). -/
l_model certLorRhs_specW (p : Prog) (hp : p.lookup "cert_lor_rhs" = some certLorRhsL)
  fns [hp ↦ certLorRhsW list]
  specs [callW_spec p n "cert_halves", callW_spec p n "nat_ap2"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certLorRhs_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_lor_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certLorRhs cc (decI c)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_sim (M := fun k mm => certLorRhsW p (k + 1) mm cx c)
    (fun k s₀ => certLorRhs_specW p hD.lCertLorRhs (k + 1) s₀ cx c) fun k m s ⟨hS, hC, hc⟩ => ?_
  rw [certLorRhsW.arm1]; unfold certLorRhs
  have hN := hD.toNatEqProg
  refine Sim.ntB ((certHalves_ref hD cx c cc).simG ⟨hS, hC, hc⟩ (.refl m)) fun r1 _ m1 a1 ⟨hS1, hG1, hl1⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS1 hG1 (.of (hC.grow hG1).f13) (.of (hC.grow hG1).f9) hl1)
    fun r2 _ m2 a2 ⟨hS2, hG2, hl2⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS2 hG2 (.of (hC.grow hG2).f10) (.of (hC.grow hG2).f1) (.of (hC.grow hG2).f9))
    fun r3 _ m3 a3 ⟨hS3, hG3, hl3⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS3 hG3 (.of (hC.grow hG3).f10) (.of (hC.grow hG3).f2) (.of (hC.grow hG3).f9))
    fun r4 _ m4 a4 ⟨hS4, hG4, hl4⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS4 hG4 (.of (hC.grow hG4).f12) hl3 hl4) fun r5 _ m5 a5 ⟨hS5, hG5, hl5⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS5 hG5 (.of (hC.grow hG5).f13) hl3 hl4) fun r6 _ m6 a6 ⟨hS6, hG6, hl6⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS6 hG6 (.of (hC.grow hG6).f14) hl5 hl6) fun r7 _ m7 a7 ⟨hS7, hG7, hl7⟩ => ?_
  exact Sim.ntRet (natAp2_dw hN hS7 hG7 (.of (hC.grow hG7).f12) hl2 hl7)
    fun _ _ _ _ _ h => h

/-- **`cert_xor_rhs` is its model `certXorRhsW`** (generated). -/
l_model certXorRhs_specW (p : Prog) (hp : p.lookup "cert_xor_rhs" = some certXorRhsL)
  fns [hp ↦ certXorRhsW list]
  specs [callW_spec p n "cert_halves", callW_spec p n "nat_ap2"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certXorRhs_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_xor_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certXorRhs cc (decI c)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_sim (M := fun k mm => certXorRhsW p (k + 1) mm cx c)
    (fun k s₀ => certXorRhs_specW p hD.lCertXorRhs (k + 1) s₀ cx c) fun k m s ⟨hS, hC, hc⟩ => ?_
  rw [certXorRhsW.arm1]; unfold certXorRhs
  have hN := hD.toNatEqProg
  refine Sim.ntB ((certHalves_ref hD cx c cc).simG ⟨hS, hC, hc⟩ (.refl m)) fun r1 _ m1 a1 ⟨hS1, hG1, hl1⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS1 hG1 (.of (hC.grow hG1).f13) (.of (hC.grow hG1).f9) hl1)
    fun r2 _ m2 a2 ⟨hS2, hG2, hl2⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS2 hG2 (.of (hC.grow hG2).f10) (.of (hC.grow hG2).f1) (.of (hC.grow hG2).f9))
    fun r3 _ m3 a3 ⟨hS3, hG3, hl3⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS3 hG3 (.of (hC.grow hG3).f10) (.of (hC.grow hG3).f2) (.of (hC.grow hG3).f9))
    fun r4 _ m4 a4 ⟨hS4, hG4, hl4⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS4 hG4 (.of (hC.grow hG4).f12) hl3 hl4) fun r5 _ m5 a5 ⟨hS5, hG5, hl5⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS5 hG5 (.of (hC.grow hG5).f10) hl5 (.of (hC.grow hG5).f9))
    fun r6 _ m6 a6 ⟨hS6, hG6, hl6⟩ => ?_
  exact Sim.ntRet (natAp2_dw hN hS6 hG6 (.of (hC.grow hG6).f12) hl2 hl6)
    fun _ _ _ _ _ h => h


/-- **`cert_gcd` is its model `certGcdW`** (generated). -/
l_model certGcd_specW (p : Prog) (hp : p.lookup "cert_gcd" = some certGcdL)
  fns [hp ↦ certGcdW list]
  specs [callW_spec p n "cert_guard", callW_spec p n "cert_two_eqs", callW_spec p n "nat_ap2"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certGcd_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_gcd" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certGcd cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mm => certGcdW p (k + 1) mm cx c)
    (fun k s₀ => certGcd_specW p hD.lCertGcd (k + 1) s₀ cx c) fun k m s ⟨hS, hC, hc⟩ => ?_
  rw [certGcdW.arm1]; unfold certGcd
  have hN := hD.toNatEqProg
  refine Sim.ntB (certGuard_dw hD hS hC (.refl m) (.of hC.f3) (.of hC.f1) (.of hC.f6))
    fun r1 _ m1 a1 ⟨hS1, hG1, hl1⟩ => ?_
  refine Sim.ntB (certGuard_dw hD hS1 hC hG1 (.of (hC.grow hG1).f3) (.of (hC.grow hG1).f1) (.of (hC.grow hG1).f7))
    fun r2 _ m2 a2 ⟨hS2, hG2, hl2⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS2 hG2 (.of (hC.grow hG2).f10) (.of (hC.grow hG2).f2) (.of (hC.grow hG2).f1))
    fun r3 _ m3 a3 ⟨hS3, hG3, hl3⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS3 hG3 ⟨hc, rfl⟩ hl3 (.of (hC.grow hG3).f1)) fun r4 _ m4 a4 ⟨hS4, hG4, hl4⟩ => ?_
  exact Sim.ntRet (certTwoEqs_dw hD hS4 hC hG4 hc hl1 hl2 hl4 (.of (hC.grow hG4).f2))
    fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, decStmtL_pair h3⟩

/-- **`cert_shift_left` is its model `certShiftLeftW`** (generated). -/
l_model certShiftLeft_specW (p : Prog) (hp : p.lookup "cert_shift_left" = some certShiftLeftL)
  fns [hp ↦ certShiftLeftW list]
  specs [callW_spec p n "cert_guard", callW_spec p n "cert_two_eqs", callW_spec p n "nat_ap2"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certShiftLeft_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_shift_left" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certShiftLeft cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mm => certShiftLeftW p (k + 1) mm cx c)
    (fun k s₀ => certShiftLeft_specW p hD.lCertShiftLeft (k + 1) s₀ cx c) fun k m s ⟨hS, hC, hc⟩ => ?_
  rw [certShiftLeftW.arm1]; unfold certShiftLeft
  have hN := hD.toNatEqProg
  refine Sim.ntB (certGuard_dw hD hS hC (.refl m) (.of hC.f3) (.of hC.f2) (.of hC.f6))
    fun r1 _ m1 a1 ⟨hS1, hG1, hl1⟩ => ?_
  refine Sim.ntB (certGuard_dw hD hS1 hC hG1 (.of (hC.grow hG1).f3) (.of (hC.grow hG1).f2) (.of (hC.grow hG1).f7))
    fun r2 _ m2 a2 ⟨hS2, hG2, hl2⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS2 hG2 (.of (hC.grow hG2).f13) (.of (hC.grow hG2).f9) (.of (hC.grow hG2).f1))
    fun r3 _ m3 a3 ⟨hS3, hG3, hl3⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS3 hG3 (.of (hC.grow hG3).f14) (.of (hC.grow hG3).f2) (.of (hC.grow hG3).f3))
    fun r4 _ m4 a4 ⟨hS4, hG4, hl4⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS4 hG4 ⟨hc, rfl⟩ hl3 hl4) fun r5 _ m5 a5 ⟨hS5, hG5, hl5⟩ => ?_
  exact Sim.ntRet (certTwoEqs_dw hD hS5 hC hG5 hc hl1 hl2 hl5 (.of (hC.grow hG5).f1))
    fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, decStmtL_pair h3⟩

/-- **`cert_shift_right` is its model `certShiftRightW`** (generated). -/
l_model certShiftRight_specW (p : Prog) (hp : p.lookup "cert_shift_right" = some certShiftRightL)
  fns [hp ↦ certShiftRightW list]
  specs [callW_spec p n "cert_guard", callW_spec p n "cert_two_eqs", callW_spec p n "nat_ap2"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certShiftRight_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_shift_right" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certShiftRight cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mm => certShiftRightW p (k + 1) mm cx c)
    (fun k s₀ => certShiftRight_specW p hD.lCertShiftRight (k + 1) s₀ cx c) fun k m s ⟨hS, hC, hc⟩ => ?_
  rw [certShiftRightW.arm1]; unfold certShiftRight
  have hN := hD.toNatEqProg
  refine Sim.ntB (certGuard_dw hD hS hC (.refl m) (.of hC.f3) (.of hC.f2) (.of hC.f6))
    fun r1 _ m1 a1 ⟨hS1, hG1, hl1⟩ => ?_
  refine Sim.ntB (certGuard_dw hD hS1 hC hG1 (.of (hC.grow hG1).f3) (.of (hC.grow hG1).f2) (.of (hC.grow hG1).f7))
    fun r2 _ m2 a2 ⟨hS2, hG2, hl2⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS2 hG2 (.of (hC.grow hG2).f14) (.of (hC.grow hG2).f2) (.of (hC.grow hG2).f3))
    fun r3 _ m3 a3 ⟨hS3, hG3, hl3⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS3 hG3 ⟨hc, rfl⟩ (.of (hC.grow hG3).f1) hl3) fun r4 _ m4 a4 ⟨hS4, hG4, hl4⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS4 hG4 (.of (hC.grow hG4).f11) hl4 (.of (hC.grow hG4).f9))
    fun r5 _ m5 a5 ⟨hS5, hG5, hl5⟩ => ?_
  exact Sim.ntRet (certTwoEqs_dw hD hS5 hC hG5 hc hl1 hl2 hl5 (.of (hC.grow hG5).f1))
    fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, decStmtL_pair h3⟩

/-- **`cert_land` is its model `certLandW`** (generated). -/
l_model certLand_specW (p : Prog) (hp : p.lookup "cert_land" = some certLandL)
  fns [hp ↦ certLandW list]
  specs [callW_spec p n "cert_guard", callW_spec p n "cert_halves", callW_spec p n "cert_two_eqs", callW_spec p n "nat_ap2"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certLand_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_land" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certLand cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mm => certLandW p (k + 1) mm cx c)
    (fun k s₀ => certLand_specW p hD.lCertLand (k + 1) s₀ cx c) fun k m s ⟨hS, hC, hc⟩ => ?_
  rw [certLandW.arm1]; unfold certLand
  have hN := hD.toNatEqProg
  refine Sim.ntB (certGuard_dw hD hS hC (.refl m) (.of hC.f3) (.of hC.f1) (.of hC.f6))
    fun r1 _ m1 a1 ⟨hS1, hG1, hl1⟩ => ?_
  refine Sim.ntB (certGuard_dw hD hS1 hC hG1 (.of (hC.grow hG1).f3) (.of (hC.grow hG1).f1) (.of (hC.grow hG1).f7))
    fun r2 _ m2 a2 ⟨hS2, hG2, hl2⟩ => ?_
  refine Sim.ntB ((certHalves_ref hD cx c cc).simG ⟨hS2, hC.grow hG2, hc⟩ hG2) fun r3 _ m3 a3 ⟨hS3, hG3, hl3⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS3 hG3 (.of (hC.grow hG3).f13) (.of (hC.grow hG3).f9) hl3)
    fun r4 _ m4 a4 ⟨hS4, hG4, hl4⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS4 hG4 (.of (hC.grow hG4).f10) (.of (hC.grow hG4).f1) (.of (hC.grow hG4).f9))
    fun r5 _ m5 a5 ⟨hS5, hG5, hl5⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS5 hG5 (.of (hC.grow hG5).f10) (.of (hC.grow hG5).f2) (.of (hC.grow hG5).f9))
    fun r6 _ m6 a6 ⟨hS6, hG6, hl6⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS6 hG6 (.of (hC.grow hG6).f13) hl5 hl6) fun r7 _ m7 a7 ⟨hS7, hG7, hl7⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS7 hG7 (.of (hC.grow hG7).f12) hl4 hl7) fun r8 _ m8 a8 ⟨hS8, hG8, hl8⟩ => ?_
  exact Sim.ntRet (certTwoEqs_dw hD hS8 hC hG8 hc hl1 hl2 hl8 (.of (hC.grow hG8).f8))
    fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, decStmtL_pair h3⟩

/-- **`cert_lor` is its model `certLorW`** (generated). -/
l_model certLor_specW (p : Prog) (hp : p.lookup "cert_lor" = some certLorL)
  fns [hp ↦ certLorW list]
  specs [callW_spec p n "cert_guard", callW_spec p n "cert_lor_rhs", callW_spec p n "cert_two_eqs"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certLor_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_lor" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certLor cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mm => certLorW p (k + 1) mm cx c)
    (fun k s₀ => certLor_specW p hD.lCertLor (k + 1) s₀ cx c) fun k m s ⟨hS, hC, hc⟩ => ?_
  rw [certLorW.arm1]; unfold certLor
  have hN := hD.toNatEqProg
  refine Sim.ntB (certGuard_dw hD hS hC (.refl m) (.of hC.f3) (.of hC.f1) (.of hC.f6))
    fun r1 _ m1 a1 ⟨hS1, hG1, hl1⟩ => ?_
  refine Sim.ntB (certGuard_dw hD hS1 hC hG1 (.of (hC.grow hG1).f3) (.of (hC.grow hG1).f1) (.of (hC.grow hG1).f7))
    fun r2 _ m2 a2 ⟨hS2, hG2, hl2⟩ => ?_
  refine Sim.ntB ((certLorRhs_ref hD cx c cc).simG ⟨hS2, hC.grow hG2, hc⟩ hG2) fun r3 _ m3 a3 ⟨hS3, hG3, hl3⟩ => ?_
  exact Sim.ntRet (certTwoEqs_dw hD hS3 hC hG3 hc hl1 hl2 hl3 (.of (hC.grow hG3).f2))
    fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, decStmtL_pair h3⟩

/-- **`cert_xor` is its model `certXorW`** (generated). -/
l_model certXor_specW (p : Prog) (hp : p.lookup "cert_xor" = some certXorL)
  fns [hp ↦ certXorW list]
  specs [callW_spec p n "cert_guard", callW_spec p n "cert_two_eqs", callW_spec p n "cert_xor_rhs"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certXor_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_xor" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certXor cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mm => certXorW p (k + 1) mm cx c)
    (fun k s₀ => certXor_specW p hD.lCertXor (k + 1) s₀ cx c) fun k m s ⟨hS, hC, hc⟩ => ?_
  rw [certXorW.arm1]; unfold certXor
  have hN := hD.toNatEqProg
  refine Sim.ntB (certGuard_dw hD hS hC (.refl m) (.of hC.f3) (.of hC.f1) (.of hC.f6))
    fun r1 _ m1 a1 ⟨hS1, hG1, hl1⟩ => ?_
  refine Sim.ntB (certGuard_dw hD hS1 hC hG1 (.of (hC.grow hG1).f3) (.of (hC.grow hG1).f1) (.of (hC.grow hG1).f7))
    fun r2 _ m2 a2 ⟨hS2, hG2, hl2⟩ => ?_
  refine Sim.ntB ((certXorRhs_ref hD cx c cc).simG ⟨hS2, hC.grow hG2, hc⟩ hG2) fun r3 _ m3 a3 ⟨hS3, hG3, hl3⟩ => ?_
  exact Sim.ntRet (certTwoEqs_dw hD hS3 hC hG3 hc hl1 hl2 hl3 (.of (hC.grow hG3).f2))
    fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, decStmtL_pair h3⟩


/-! ## `cert_rec_rhs` -/

/-- **`cert_rec_rhs` is its model `certRecRhsW`** (generated). -/
l_model certRecRhs_specW (p : Prog) (hp : p.lookup "cert_rec_rhs" = some certRecRhsL)
  fns [hp ↦ certRecRhsW list]
  specs [callW_spec p n "nat_ap2", callW_spec p n "pin_at", callW_spec p n "nat_ap1"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certRecRhs_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_rec_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certRecRhs cc (decI c)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_sim (M := fun k mq => certRecRhsW p (k + 1) mq cx c)
    (fun k s₀ => certRecRhs_specW p hD.lCertRecRhs (k + 1) s₀ cx c) fun k m s ⟨hS, hC, hc⟩ => ?_
  rw [certRecRhsW.arm1]; unfold certRecRhs
  have hN := hD.toNatEqProg
  refine Sim.ntB (natAp2_dw hN hS (.refl m) (.of hC.f14) (.of hC.f1) (.of hC.f2))
    fun r1 _ m1 a1 ⟨hS1, hG1, hl1⟩ => ?_
  refine Sim.ntB (natAp2_dw hN hS1 hG1 ⟨hc, rfl⟩ hl1 (.of (hC.grow hG1).f2))
    fun r2 _ m2 a2 ⟨hS2, hG2, hl2, rfl⟩ => ?_
  refine Sim.iteW (hC.grow hG2).f11 hc (fun _ => ?_) fun _ => Sim.ret ⟨hS2, hG2, hl2, rfl⟩
  refine Sim.ntB ((pinSlot_ref p hD.lPinAt 3 pinNatSucc rfl).simG hS2 hG2)
    fun r3 _ m3 a3 ⟨hS3, hG3, hl3, rfl⟩ => ?_
  exact Sim.ntRet ((natAp1_ref hN (r3.headD 0) (r2.headD 0)).simG ⟨hS3, hl3, hl2⟩ hG3) fun _ _ _ _ _ h => h

/-! ## `cert_div_mod_eqs` -/

/-- **`cert_div_mod_eqs` is its model `certDivModEqsW`** (generated). -/
l_model certDivModEqs_specW (p : Prog) (hp : p.lookup "cert_div_mod_eqs" = some certDivModEqsL)
  fns [hp ↦ certDivModEqsW list]
  specs [callW_spec p n "cert_eq", callW_spec p n "rec2", callW_spec p n "rec3", callW_spec p n "stmt1"]
  grind [arena_grind] finish [ntBW] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certDivModEqs_ref (hD : DmProg2 p) (cx c h1 h2 h3 h4 recRhs baseRhs : Word) (cc : CertCtxA) :
    CallRef p "cert_div_mod_eqs" [cx, c, h1, h2, h3, h4, recRhs, baseRhs]
      (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H h1 ∧ H h2 ∧ H h3 ∧ H h4 ∧
        H recRhs ∧ H baseRhs)
      (certDivModEqs cc (decI c) (decE h1) (decE h2) (decE h3) (decE h4) (decE recRhs) (decE baseRhs))
      (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mq => certDivModEqsW p (k + 1) mq cx c h1 h2 h3 h4 recRhs baseRhs)
    (fun k s₀ => certDivModEqs_specW p hD.lCertDivModEqs (k + 1) s₀ cx c h1 h2 h3 h4 recRhs baseRhs)
    fun k m s ⟨hS, hC, hc, hh1, hh2, hh3, hh4, hrr, hbr⟩ => ?_
  rw [certDivModEqsW.arm1]; unfold certDivModEqs
  refine Sim.ntB ((certEq_ref hD cx c recRhs cc).simG ⟨hS, hC, hc, hrr⟩ (.refl m))
    fun r1 _ m1 a1 ⟨hS1, hg1, hl1, rfl⟩ => ?_
  refine Sim.ntB ((certEq_ref hD cx c baseRhs cc).simG ⟨hS1, hC.grow hg1, hc, hbr⟩ hg1)
    fun r2 _ m2 a2 ⟨hS2, hg2, hl2, rfl⟩ => ?_
  refine (rec2_fref p hD.lIwAlloc hD.lRec2 h1 h2).simB hS2.2 fun r3 m3 hrec3 => ?_
  have hS3 := hrec3.2.1.stage hS2
  refine (rec3_fref p hD.lIwAlloc hD.lRec3 (r3.headD 0) 2 (r1.headD 0)).simB hS3.2 fun r4 m4 hrec4 => ?_
  have hS4 := hrec4.2.1.stage hS3
  refine (stmt1_ref hD h3 (r2.headD 0)).simP ⟨hS4, hh3, hl2⟩ fun r5 m5 ⟨hS5, hg5, hs5⟩ => ?_
  refine (stmt1_ref hD h4 (r2.headD 0)).simP ⟨hS5, hh4, hl2⟩ fun r6 m6 ⟨hS6, hg6, hs6⟩ => ?_
  refine (rec3_fref p hD.lIwAlloc hD.lRec3 (r4.headD 0) (r5.headD 0) (r6.headD 0)).simB hS6.2 fun r7 m7 hrec7 => ?_
  have hq3 : (r3.headD 0).toNat = iwTop m2 := by rw [hrec3.1]; rfl
  have hbound : (r3.headD 0).toNat + (2 : Word).toNat ≤ iwTop m3 := by
    have h2w : (2 : Word).toNat = 2 := rfl
    have hl : [h1, h2].length = 2 := rfl
    have := hrec3.2.2.2.1; rw [hl] at this; rw [h2w, hq3]; omega
  have st1 := stmtAt_of_rec3 hrec4 hS3.2 hbound (rec2_dec hrec3 hh1 hh2) hl1
  exact Sim.ret ⟨hrec7.2.1.stage hS6, hg2.trans (hrec3.2.1.1.trans (hrec4.2.1.1.trans (hg5.trans (hg6.trans
    hrec7.2.1.1)))), stmtL_of_rec3 hrec7 (st1.grow (hg5.trans hg6)) (hs5.grow hg6) hs6⟩


/-- **`cert_div_mod_guards` is its model `certDivModGuardsW`** (generated). -/
l_model certDivModGuards_specW (p : Prog) (hp : p.lookup "cert_div_mod_guards" = some certDivModGuardsL)
  fns [hp ↦ certDivModGuardsW list]
  specs [callW_spec p n "cert_div_mod_eqs", callW_spec p n "cert_guard"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certDivModGuards_ref (hD : DmProg2 p) (cx c recRhs baseRhs : Word) (cc : CertCtxA) :
    CallRef p "cert_div_mod_guards" [cx, c, recRhs, baseRhs] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H recRhs ∧ H baseRhs)
      (certDivModGuards cc (decI c) (decE recRhs) (decE baseRhs)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mm => certDivModGuardsW p (k + 1) mm cx c recRhs baseRhs)
    (fun k s₀ => certDivModGuards_specW p hD.lCertDivModGuards (k + 1) s₀ cx c recRhs baseRhs)
    fun k m s ⟨hS, hC, hc, hrecRhs, hbaseRhs⟩ => ?_
  rw [certDivModGuardsW.arm1]; unfold certDivModGuards
  refine Sim.ntB (certGuard_dw hD hS hC (.refl m) (.of hC.f2) (.of hC.f1) (.of hC.f6))
    fun r1 _ m1 a1 ⟨hS1, hG1, hl1, rfl⟩ => ?_
  refine Sim.ntB (certGuard_dw hD hS1 hC hG1 (.of (hC.grow hG1).f3) (.of (hC.grow hG1).f2) (.of (hC.grow hG1).f6))
    fun r2 _ m2 a2 ⟨hS2, hG2, hl2, rfl⟩ => ?_
  refine Sim.ntB (certGuard_dw hD hS2 hC hG2 (.of (hC.grow hG2).f2) (.of (hC.grow hG2).f1) (.of (hC.grow hG2).f7))
    fun r3 _ m3 a3 ⟨hS3, hG3, hl3, rfl⟩ => ?_
  refine Sim.ntB (certGuard_dw hD hS3 hC hG3 (.of (hC.grow hG3).f3) (.of (hC.grow hG3).f2) (.of (hC.grow hG3).f7))
    fun r4 _ m4 a4 ⟨hS4, hG4, hl4, rfl⟩ => ?_
  exact (certDivModEqs_ref hD cx c _ _ _ _ recRhs baseRhs cc).simPair
    ⟨hS4, hC.grow hG4, hc, hl1, hl2, hl3, hl4, hrecRhs, hbaseRhs⟩ hG4



/-! ## `cert_div_mod` -/

/-- **`cert_div_mod` is its model `certDivModW`** (generated). -/
l_model certDivMod_specW (p : Prog) (hp : p.lookup "cert_div_mod" = some certDivModL)
  fns [hp ↦ certDivModW list]
  specs [callW_spec p n "cert_rec_rhs", callW_spec p n "cert_div_mod_guards"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem certDivMod_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_div_mod" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certDivMod cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mq => certDivModW p (k + 1) mq cx c)
    (fun k s₀ => certDivMod_specW p hD.lCertDivMod (k + 1) s₀ cx c) fun k m s ⟨hS, hC, hc⟩ => ?_
  rw [certDivModW.arm1]; unfold certDivMod
  refine Sim.ntB ((certRecRhs_ref hD cx c cc).simG ⟨hS, hC, hc⟩ (.refl m))
    fun r1 _ m1 a1 ⟨hS1, hG1, hl1, rfl⟩ => ?_
  have hC1 := hC.grow hG1
  have hb := decI_beq_word (κ := IdxKind.name) hc (dmWord_lt32 cc.divN)
  rw [decI_word] at hb
  rw [hC1.f11, hC1.f8, hC1.f1, hb]
  by_cases hd : c = cc.divN.word.toUInt64
  · rw [ite_eq_left hd, decide_eq_true hd, ite_eq_left rfl]
    exact ((certDivModGuards_ref hD cx c _ _ cc).simPair ⟨hS1, hC1, hc, hl1, dmWord_lt32 _⟩ hG1).congr
      (by simp only [decE_eq_decI, decI_word])
  · rw [ite_eq_right hd, decide_eq_false hd]
    exact ((certDivModGuards_ref hD cx c _ _ cc).simPair ⟨hS1, hC1, hc, hl1, dmWord_lt32 _⟩ hG1).congr
      (by simp only [decE_eq_decI, decI_word, Bool.false_eq_true, ite_false])

/-! ## `div_mod_cert_stmts_at` -/
/-- **`div_mod_cert_stmts_at` is its model `divModCertStmtsAtW`** (generated). -/
l_model divModCertStmtsAt_specW (p : Prog) (hp : p.lookup "div_mod_cert_stmts_at" = some divModCertStmtsAtL)
  fns [hp ↦ divModCertStmtsAtW list]
  specs [callW_spec p n "cert_gcd", callW_spec p n "cert_shift_left", callW_spec p n "cert_shift_right", callW_spec p n "cert_land", callW_spec p n "cert_lor", callW_spec p n "cert_xor", callW_spec p n "cert_div_mod"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem divModCertStmtsAt_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "div_mod_cert_stmts_at" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (divModCertStmtsAt cc (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mq => divModCertStmtsAtW p (k + 1) mq cx c)
    (fun k s₀ => divModCertStmtsAt_specW p hD.lDivModCertStmtsAt (k + 1) s₀ cx c) fun k m s ⟨hS, hC, hc⟩ => ?_
  rw [divModCertStmtsAtW.eq_2]; unfold divModCertStmtsAt
  refine Sim.iteW hC.f15 hc (fun _ => (certGcd_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)) fun _ => ?_
  refine Sim.iteW hC.f16 hc (fun _ => (certShiftLeft_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)) fun _ => ?_
  refine Sim.iteW hC.f17 hc (fun _ => (certShiftRight_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)) fun _ => ?_
  refine Sim.iteW hC.f18 hc (fun _ => (certLand_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)) fun _ => ?_
  refine Sim.iteW hC.f19 hc (fun _ => (certLor_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)) fun _ => ?_
  refine Sim.iteW hC.f20 hc (fun _ => (certXor_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)) fun _ => ?_
  exact (certDivMod_ref hD cx c cc).simPair ⟨hS, hC, hc⟩ (.refl m)

/-! ## `div_mod_cert_stmts` -/

/-- **`div_mod_cert_stmts` is its model `divModCertStmtsW`** (generated). -/
l_model divModCertStmts_specW (p : Prog) (hp : p.lookup "div_mod_cert_stmts" = some divModCertStmtsL)
  fns [hp ↦ divModCertStmtsW list]
  specs [callW_spec p n "cert_ctx", callW_spec p n "div_mod_cert_stmts_at"]
  grind [arena_grind] finish [ntBW] gen 20 heartbeats 1600000 bind ntBW instances 10000

theorem divModCertStmts_ref (hD : DmProg2 p) (c : Word) :
    CallRef p "div_mod_cert_stmts" [c] (fun m s => StageR dn vis fe m s ∧ H c)
      (divModCertStmts (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mq => divModCertStmtsW p (k + 1) mq c)
    (fun k s₀ => divModCertStmts_specW p hD.lDivModCertStmts (k + 1) s₀ c) fun k m s ⟨hS, hc⟩ => ?_
  rw [divModCertStmtsW.arm1]; unfold divModCertStmts
  refine Sim.ntB ((certCtx_ref hD).sim hS) fun r1 x1 m1 a1 ⟨hS1, hg1, hctx⟩ => ?_
  exact (divModCertStmtsAt_ref hD (r1.headD 0) c x1).simPair ⟨hS1, hctx, hc⟩ hg1

@[refines ConRon.Arena.certLorRhs]
theorem certLorRhs_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_lor_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certLorRhs cc (decI c)) (KeepPost dn vis fe decW0E) :=
  (certLorRhs_ref hD cx c cc).refAM

@[refines ConRon.Arena.certXorRhs]
theorem certXorRhs_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_xor_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certXorRhs cc (decI c)) (KeepPost dn vis fe decW0E) :=
  (certXorRhs_ref hD cx c cc).refAM

@[refines ConRon.Arena.certGcd]
theorem certGcd_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_gcd" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certGcd cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certGcd_ref hD cx c cc).refAM

@[refines ConRon.Arena.certShiftLeft]
theorem certShiftLeft_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_shift_left" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certShiftLeft cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certShiftLeft_ref hD cx c cc).refAM

@[refines ConRon.Arena.certShiftRight]
theorem certShiftRight_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_shift_right" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certShiftRight cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certShiftRight_ref hD cx c cc).refAM

@[refines ConRon.Arena.certLand]
theorem certLand_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_land" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certLand cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certLand_ref hD cx c cc).refAM

@[refines ConRon.Arena.certLor]
theorem certLor_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_lor" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certLor cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certLor_ref hD cx c cc).refAM

@[refines ConRon.Arena.certXor]
theorem certXor_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_xor" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certXor cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certXor_ref hD cx c cc).refAM

@[refines ConRon.Arena.certRecRhs]
theorem certRecRhs_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_rec_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certRecRhs cc (decI c)) (KeepPost dn vis fe decW0E) :=
  (certRecRhs_ref hD cx c cc).refAM

@[refines ConRon.Arena.certDivModEqs]
theorem certDivModEqs_refines (hD : DmProg2 p) (cx c h1 h2 h3 h4 recRhs baseRhs : Word) (cc : CertCtxA) :
    RefAM p "cert_div_mod_eqs" [cx, c, h1, h2, h3, h4, recRhs, baseRhs]
      (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H h1 ∧ H h2 ∧ H h3 ∧ H h4 ∧
        H recRhs ∧ H baseRhs)
      (certDivModEqs cc (decI c) (decE h1) (decE h2) (decE h3) (decE h4) (decE recRhs) (decE baseRhs))
      (KeepPost dn vis fe decStmtL) :=
  (certDivModEqs_ref hD cx c h1 h2 h3 h4 recRhs baseRhs cc).refAM

@[refines ConRon.Arena.certDivModGuards]
theorem certDivModGuards_refines (hD : DmProg2 p) (cx c recRhs baseRhs : Word) (cc : CertCtxA) :
    RefAM p "cert_div_mod_guards" [cx, c, recRhs, baseRhs] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H recRhs ∧ H baseRhs)
      (certDivModGuards cc (decI c) (decE recRhs) (decE baseRhs)) (KeepPost dn vis fe decStmtL) :=
  (certDivModGuards_ref hD cx c recRhs baseRhs cc).refAM

@[refines ConRon.Arena.certDivMod]
theorem certDivMod_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_div_mod" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certDivMod cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certDivMod_ref hD cx c cc).refAM

@[refines ConRon.Arena.divModCertStmtsAt]
theorem divModCertStmtsAt_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "div_mod_cert_stmts_at" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (divModCertStmtsAt cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (divModCertStmtsAt_ref hD cx c cc).refAM

@[refines ConRon.Arena.divModCertStmts]
theorem divModCertStmts_refines (hD : DmProg2 p) (c : Word) :
    RefAM p "div_mod_cert_stmts" [c] (fun m s => StageR dn vis fe m s ∧ H c)
      (divModCertStmts (decI c)) (KeepPost dn vis fe decStmtL) :=
  (divModCertStmts_ref hD c).refAM

end nat

end L.Ind
