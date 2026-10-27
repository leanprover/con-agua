import ConAgua.Arena.DeclDivMod2

/-!
# The `Nat.div` family's pin gate, bottom up: statement builders, part 3 (lane `decls3`, `decls3-divmod`)

Statement records and lists (`StmtAt`, `StmtL`), `stmt1`, `cert_guard`, `cert_eq`, `cert_halves`, `cert_two_eqs`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section nat
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-! ### Statements -/

/-- A three-word record at `p`. -/
def Rec3At (m : Mem) (p a b c : Word) : Prop :=
  p.toNat + 3 ≤ iwTop m ∧ (iwA m)[p.toNat]? = some a ∧ (iwA m)[p.toNat + 1]? = some b ∧
    (iwA m)[p.toNat + 2]? = some c

theorem Rec3At.grow {m m' : Mem} {p a b c : Word} (h : Rec3At m p a b c) (hg : IWGrow m m') :
    Rec3At m' p a b c := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨Nat.le_trans h1 hg.1, ?_, ?_, ?_⟩ <;> simp only [iwA] at * <;>
    first | (rw [hg.2.2.1 _ (by omega)]; assumption)

theorem rec3At_of_post {m m1 : Mem} {r : List Word} {a b c : Word} (h : RecPost m m1 r [a, b, c])
    (_hI : IWOK m) : Rec3At m1 (r.headD 0) a b c := by
  obtain ⟨hq, hK, hroom, htop, hget⟩ := h
  have hq' : (r.headD 0).toNat = iwTop m := by rw [hq]; rfl
  refine ⟨by rw [hq']; simp at htop; omega, ?_, ?_, ?_⟩
  · have := hget 0 (by simp); simp only [iwA, hq']; simpa using this
  · have := hget 1 (by simp); simp only [iwA, hq']; simpa using this
  · have := hget 2 (by simp); simp only [iwA, hq']; simpa using this

/-- **A statement record** `[hyps.off, hyps.len, eq]` at `p`. -/
def StmtAt (m : Mem) (p : Word) (st : List EIdx × EIdx) : Prop :=
  ∃ ho hl e : Word, Rec3At m p ho hl e ∧ ho.toNat + hl.toNat ≤ iwTop m ∧
    decHL m ho.toNat hl.toNat = some st.1 ∧ H e ∧ st.2 = decE e

theorem StmtAt.grow {m m' : Mem} {p : Word} {st : List EIdx × EIdx} (h : StmtAt m p st)
    (hg : IWGrow m m') : StmtAt m' p st := by
  obtain ⟨ho, hl, e, hr, hb, hd, he, hs⟩ := h
  exact ⟨ho, hl, e, hr.grow hg, Nat.le_trans hb hg.1, by rw [decHL_grow hg hb]; exact hd, he, hs⟩

/-- **A statement list**: the slice `(o, l)` of pointers to statement records. -/
def StmtL (m : Mem) (o l : Nat) (ss : List (List EIdx × EIdx)) : Prop :=
  o + l ≤ iwTop m ∧ l = ss.length ∧ ∀ (j : Nat) (hj : j < ss.length), ∃ p : Word,
    (iwA m)[o + j]? = some p ∧ StmtAt m p ss[j]

theorem StmtL.grow {m m' : Mem} {o l : Nat} {ss : List (List EIdx × EIdx)} (h : StmtL m o l ss)
    (hg : IWGrow m m') : StmtL m' o l ss := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.le_trans h1 hg.1, h2, fun j hj => ?_⟩
  obtain ⟨p, hp, hs⟩ := h3 j hj
  refine ⟨p, ?_, hs.grow hg⟩
  simp only [iwA] at hp ⊢; rw [hg.2.2.1 _ (by omega)]; exact hp

def decStmtL (m : Mem) (r : List Word) (ss : List (List EIdx × EIdx)) : Prop :=
  StmtL m (r.getD 0 0).toNat (r.getD 1 0).toNat ss

def decStmt (m : Mem) (r : List Word) (st : List EIdx × EIdx) : Prop := StmtAt m (r.headD 0) st

/-- **`cert_guard` is its model `certGuardW`** (generated). -/
l_model certGuard_specW (p : Prog) (hp : p.lookup "cert_guard" = some certGuardL)
  fns [hp ↦ certGuardW list]
  specs [callW_spec p n "eq_at1", callW_spec p n "nat_ap2"]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW, rdW_eq]

theorem certGuard_ref (hD : DmProg2 p) (cx a b rv : Word) (cc : CertCtxA) :
    CallRef p "cert_guard" [cx, a, b, rv] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H a ∧ H b ∧ H rv)
      (certGuard cc (decE a) (decE b) (decE rv)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_sim (M := fun k mm => certGuardW p (k + 1) mm cx a b rv)
    (fun k s₀ => certGuard_specW p hD.lCertGuard (k + 1) s₀ cx a b rv) fun k m s ⟨hS, hC, ha, hb, hrv⟩ => ?_
  rw [certGuardW.arm1]; unfold certGuard
  refine Sim.ntB (natAp2_dw hD.toNatEqProg hS (.refl m) (.of hC.f4) ⟨ha, rfl⟩ ⟨hb, rfl⟩)
    fun r1 _ m1 a1 ⟨hS1, hG1, hl1, rfl⟩ => ?_
  exact Sim.ntRet (((eqAt1_ref hD _ _ rv).simG hS1 hG1).congr
    (by simp only [(hC.grow hG1).f5, decE_eq_decI, decI_word])) fun _ _ _ _ _ h => h

/-- **`cert_eq` is its model `certEqW`** (generated). -/
l_model certEq_specW (p : Prog) (hp : p.lookup "cert_eq" = some certEqL)
  fns [hp ↦ certEqW list]
  specs [callW_spec p n "eq_at1", callW_spec p n "nat_ap2"]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW, rdW_eq]

theorem certEq_ref (hD : DmProg2 p) (cx c rhs : Word) (cc : CertCtxA) :
    CallRef p "cert_eq" [cx, c, rhs] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H rhs)
      (certEq cc (decI c) (decE rhs)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_sim (M := fun k mm => certEqW p (k + 1) mm cx c rhs)
    (fun k s₀ => certEq_specW p hD.lCertEq (k + 1) s₀ cx c rhs) fun k m s ⟨hS, hC, hc, hrhs⟩ => ?_
  rw [certEqW.arm1]; unfold certEq
  refine Sim.ntB (natAp2_dw hD.toNatEqProg hS (.refl m) ⟨hc, rfl⟩ (.of hC.f1) (.of hC.f2))
    fun r1 _ m1 a1 ⟨hS1, hG1, hl1, rfl⟩ => ?_
  exact Sim.ntRet (((eqAt1_ref hD _ _ rhs).simG hS1 hG1).congr
    (by simp only [(hC.grow hG1).f0, decE_eq_decI, decI_word])) fun _ _ _ _ _ h => h

/-- **`cert_halves` is its model `certHalvesW`** (generated). -/
l_model certHalves_specW (p : Prog) (hp : p.lookup "cert_halves" = some certHalvesL)
  fns [hp ↦ certHalvesW list]
  specs [callW_spec p n "nat_ap2"]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW, rdW_eq]

theorem certHalves_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_halves" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certHalves cc (decI c)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_sim (M := fun k mm => certHalvesW p (k + 1) mm cx c)
    (fun k s₀ => certHalves_specW p hD.lCertHalves (k + 1) s₀ cx c) fun k m s ⟨hS, hC, hc⟩ => ?_
  rw [certHalvesW.arm1]; unfold certHalves
  have hN := hD.toNatEqProg
  refine Sim.ntB (natAp2_dw hN hS (.refl m) (.of hC.f11) (.of hC.f1) (.of hC.f9))
    fun r1 _ m1 a1 ⟨hS1, hG1, hl1⟩ => ?_
  have hC1 := hC.grow hG1
  refine Sim.ntB (natAp2_dw hN hS1 hG1 (.of hC1.f11) (.of hC1.f2) (.of hC1.f9))
    fun r2 _ m2 a2 ⟨hS2, hG2, hl2⟩ => ?_
  exact Sim.ntRet (natAp2_dw hN hS2 hG2 ⟨hc, rfl⟩ hl1 hl2) fun _ _ _ _ _ h => h



/-! ### Records of statements -/

theorem pure_run_eq {α : Type} {x y : α} {a a' : AState} (h : (pure x : AM α).run a = .ok (y, a')) :
    y = x ∧ a' = a := by
  simp only [StateT.run_pure] at h
  have := Except.ok.inj h
  exact ⟨(Prod.mk.inj this).1.symm, (Prod.mk.inj this).2.symm⟩

theorem rec2_dec {κ : IdxKind} {m m1 : Mem} {r : List Word} {a b : Word} (hR : RecPost m m1 r [a, b])
    (ha : H a) (hb : H b) :
    decHL m1 (r.headD 0).toNat 2 = some [(decI a : Idx κ), decI b] := by
  obtain ⟨hq, -, -, -, hget⟩ := hR
  have hq' : (r.headD 0).toNat = iwTop m := by rw [hq]; rfl
  rw [hq']
  have := decHL_words (k := κ) m1 [a, b] (iwTop m)
    (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption)
    (fun j hj => by simpa [iwA] using hget j hj)
  simpa using this

/-- A statement record from `rec3(o, l, e)`, given the hypothesis slice. -/
theorem stmtAt_of_rec3 {m m1 : Mem} {r : List Word} {o l e : Word} {hyps : List EIdx}
    (hR : RecPost m m1 r [o, l, e]) (hI : IWOK m) (hb : o.toNat + l.toNat ≤ iwTop m)
    (hd : decHL m o.toNat l.toNat = some hyps) (he : H e) :
    StmtAt m1 (r.headD 0) (hyps, decE e) := by
  have hg := hR.2.1.1
  exact ⟨o, l, e, rec3At_of_post hR hI, Nat.le_trans hb hg.1, by rw [decHL_grow hg hb]; exact hd, he, rfl⟩

theorem stmtL_of_rec2 {m m1 : Mem} {r : List Word} {s1 s2 : Word} {st1 st2 : List EIdx × EIdx}
    (hR : RecPost m m1 r [s1, s2]) (h1 : StmtAt m s1 st1) (h2 : StmtAt m s2 st2) :
    decStmtL m1 [r.headD 0, 2] [st1, st2] := by
  obtain ⟨hq, hK, hroom, htop, hget⟩ := hR
  have hq' : (r.headD 0).toNat = iwTop m := by rw [hq]; rfl
  have hg := hK.1
  simp only [decStmtL, StmtL, List.getD_cons_zero, List.getD_cons_succ, hq']
  have hl : [s1, s2].length = 2 := rfl
  have h2w : (2 : Word).toNat = 2 := rfl
  refine ⟨by rw [hl] at htop; omega, rfl, fun j hj => ?_⟩
  match j, hj with
  | 0, _ =>
    refine ⟨s1, ?_, h1.grow hg⟩
    have := hget 0 (by simp); simp only [iwA]; simpa using this
  | 1, _ =>
    refine ⟨s2, ?_, h2.grow hg⟩
    have := hget 1 (by simp); simp only [iwA]; simpa using this

theorem stmtL_of_rec3 {m m1 : Mem} {r : List Word} {s1 s2 s3 : Word} {st1 st2 st3 : List EIdx × EIdx}
    (hR : RecPost m m1 r [s1, s2, s3]) (h1 : StmtAt m s1 st1) (h2 : StmtAt m s2 st2)
    (h3 : StmtAt m s3 st3) : decStmtL m1 [r.headD 0, 3] [st1, st2, st3] := by
  obtain ⟨hq, hK, hroom, htop, hget⟩ := hR
  have hq' : (r.headD 0).toNat = iwTop m := by rw [hq]; rfl
  have hg := hK.1
  simp only [decStmtL, StmtL, List.getD_cons_zero, List.getD_cons_succ, hq']
  have hl : [s1, s2, s3].length = 3 := rfl
  have h3w : (3 : Word).toNat = 3 := rfl
  refine ⟨by rw [hl] at htop; omega, rfl, fun j hj => ?_⟩
  match j, hj with
  | 0, _ =>
    refine ⟨s1, ?_, h1.grow hg⟩
    have := hget 0 (by simp); simp only [iwA]; simpa using this
  | 1, _ =>
    refine ⟨s2, ?_, h2.grow hg⟩
    have := hget 1 (by simp); simp only [iwA]; simpa using this
  | 2, _ =>
    refine ⟨s3, ?_, h3.grow hg⟩
    have := hget 2 (by simp); simp only [iwA]; simpa using this

theorem decStmtL_pair {m : Mem} {r : List Word} {ss : List (List EIdx × EIdx)} (h : decStmtL m r ss) :
    decStmtL m [r.headD 0, r.tail.headD 0] ss := by
  unfold decStmtL at *
  rw [ntGetD0, ntGetD1] at h
  exact h

/-! ## `stmt1` -/

/-- **`stmt1` is its model `stmt1W`** (generated). -/
l_model stmt1_specW (p : Prog) (hp : p.lookup "stmt1" = some stmt1)
  fns [hp ↦ stmt1W list]
  specs [callW_spec p n "sl_new1", callW_spec p n "rec3"]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW]

theorem stmt1_ref (hD : DmProg2 p) (h e : Word) :
    CallRef p "stmt1" [h, e] (fun m s => StageR dn vis fe m s ∧ H h ∧ H e)
      (pure ([decE h], decE e) : AM (List EIdx × EIdx)) (KeepPost dn vis fe decStmt) := by
  refine CallRef.of_sim (M := fun k mq => stmt1W p (k + 1) mq h e) (fun k s₀ => stmt1_specW p hD.lStmt1 (k + 1) s₀ h e)
    fun k m s ⟨hS, hh, he⟩ => ?_
  refine (slNew1_fref p hD.lIwAlloc hD.lSlNew1 h).simB hS.2 fun r1 m1 ⟨hrec1, hr1⟩ => ?_
  have hS1 := hrec1.2.1.stage hS
  refine (rec3_fref p hD.lIwAlloc hD.lRec3 (r1.headD 0) (r1.tail.headD 0) e).simB hS1.2 fun r2 m2 hrec2 =>
    Sim.ret ⟨hrec2.2.1.stage hS1, hrec1.2.1.1.trans hrec2.2.1.1, ?_⟩
  have hq : (r1.headD 0).toNat = iwTop m := by rw [hrec1.1]; rfl
  have hl1 : (r1.tail.headD 0).toNat = 1 := by rw [hr1]; rfl
  have hbound : (r1.headD 0).toNat + (r1.tail.headD 0).toNat ≤ iwTop m1 := by
    have := hrec1.2.2.2.1; simp at this; omega
  exact stmtAt_of_rec3 hrec2 hS1.2 hbound (slNew1_dec hrec1 hh hr1) he

/-! ## `cert_two_eqs` -/

/-- **`cert_two_eqs` is its model `certTwoEqsW`** (generated). -/
l_model certTwoEqs_specW (p : Prog) (hp : p.lookup "cert_two_eqs" = some certTwoEqsL)
  fns [hp ↦ certTwoEqsW list]
  specs [callW_spec p n "cert_eq", callW_spec p n "stmt1", callW_spec p n "rec2"]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW]

theorem certTwoEqs_ref (hD : DmProg2 p) (cx c h1 h2 r1 r2 : Word) (cc : CertCtxA) :
    CallRef p "cert_two_eqs" [cx, c, h1, h2, r1, r2]
      (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H h1 ∧ H h2 ∧ H r1 ∧ H r2)
      (certTwoEqs cc (decI c) (decE h1) (decE h2) (decE r1) (decE r2))
      (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mq => certTwoEqsW p (k + 1) mq cx c h1 h2 r1 r2)
    (fun k s₀ => certTwoEqs_specW p hD.lCertTwoEqs (k + 1) s₀ cx c h1 h2 r1 r2)
    fun k m s ⟨hS, hC, hc, hh1, hh2, hr1, hr2⟩ => ?_
  rw [certTwoEqsW.arm1]; unfold certTwoEqs
  refine Sim.ntB ((certEq_ref hD cx c r1 cc).simG ⟨hS, hC, hc, hr1⟩ (.refl m))
    fun ra _ ma aa ⟨hSa, hga, hla, rfl⟩ => ?_
  refine Sim.ntB ((certEq_ref hD cx c r2 cc).simG ⟨hSa, hC.grow hga, hc, hr2⟩ hga)
    fun rb _ mb ab ⟨hSb, hgb, hlb, rfl⟩ => ?_
  refine (stmt1_ref hD h1 (ra.headD 0)).simP ⟨hSb, hh1, hla⟩ fun rs1 ms1 ⟨hSs1, hgs1, hs1⟩ => ?_
  refine (stmt1_ref hD h2 (rb.headD 0)).simP ⟨hSs1, hh2, hlb⟩ fun rs2 ms2 ⟨hSs2, hgs2, hs2⟩ => ?_
  exact (rec2_fref p hD.lIwAlloc hD.lRec2 (rs1.headD 0) (rs2.headD 0)).simB hSs2.2 fun rq mq hrec =>
    Sim.ret ⟨hrec.2.1.stage hSs2, hgb.trans (hgs1.trans (hgs2.trans hrec.2.1.1)),
      stmtL_of_rec2 hrec (hs1.grow hgs2) hs2⟩



/-- `cert_guard` at decoded arguments, the context grown from `m0`. -/
theorem certGuard_dw (hD : DmProg2 p) {n : Nat} {m m0 : Mem} {s : AState} {cx a b rv : Word}
    {cc : CertCtxA} {a' b' rv' : EIdx} (hS : StageR dn vis fe m s) (hC : CertCtxR m0 cx cc)
    (hG : IWGrow m0 m) (ha : DW a a') (hb : DW b b') (hr : DW rv rv') :
    Sim (callW p n "cert_guard" [cx, a, b, rv] m) (certGuard cc a' b' rv') s (KG dn vis fe m0 decW0E) := by
  obtain ⟨ha, rfl⟩ := ha; obtain ⟨hb, rfl⟩ := hb; obtain ⟨hr, rfl⟩ := hr
  exact (certGuard_ref hD cx a b rv cc).simG ⟨hS, hC.grow hG, ha, hb, hr⟩ hG

/-- `cert_two_eqs` at decoded arguments, the context grown from `m0`. -/
theorem certTwoEqs_dw (hD : DmProg2 p) {n : Nat} {m m0 : Mem} {s : AState} {cx c h1 h2 r1 r2 : Word}
    {cc : CertCtxA} {h1' h2' r1' r2' : EIdx} (hS : StageR dn vis fe m s) (hC : CertCtxR m0 cx cc)
    (hG : IWGrow m0 m) (hc : H c) (d1 : DW h1 h1') (d2 : DW h2 h2') (d3 : DW r1 r1') (d4 : DW r2 r2') :
    Sim (callW p n "cert_two_eqs" [cx, c, h1, h2, r1, r2] m) (certTwoEqs cc (decI c) h1' h2' r1' r2') s
      (KG dn vis fe m0 decStmtL) := by
  obtain ⟨d1, rfl⟩ := d1; obtain ⟨d2, rfl⟩ := d2; obtain ⟨d3, rfl⟩ := d3; obtain ⟨d4, rfl⟩ := d4
  exact (certTwoEqs_ref hD cx c h1 h2 r1 r2 cc).simG ⟨hS, hC.grow hG, hc, d1, d2, d3, d4⟩ hG

@[refines ConRon.Arena.certGuard]
theorem certGuard_refines (hD : DmProg2 p) (cx a b rv : Word) (cc : CertCtxA) :
    RefAM p "cert_guard" [cx, a, b, rv] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H a ∧ H b ∧ H rv)
      (certGuard cc (decE a) (decE b) (decE rv)) (KeepPost dn vis fe decW0E) :=
  (certGuard_ref hD cx a b rv cc).refAM

@[refines ConRon.Arena.certEq]
theorem certEq_refines (hD : DmProg2 p) (cx c rhs : Word) (cc : CertCtxA) :
    RefAM p "cert_eq" [cx, c, rhs] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H rhs)
      (certEq cc (decI c) (decE rhs)) (KeepPost dn vis fe decW0E) :=
  (certEq_ref hD cx c rhs cc).refAM

@[refines ConRon.Arena.certHalves]
theorem certHalves_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_halves" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certHalves cc (decI c)) (KeepPost dn vis fe decW0E) :=
  (certHalves_ref hD cx c cc).refAM

@[refines ConRon.Arena.certTwoEqs]
theorem certTwoEqs_refines (hD : DmProg2 p) (cx c h1 h2 r1 r2 : Word) (cc : CertCtxA) :
    RefAM p "cert_two_eqs" [cx, c, h1, h2, r1, r2]
      (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H h1 ∧ H h2 ∧ H r1 ∧ H r2)
      (certTwoEqs cc (decI c) (decE h1) (decE h2) (decE r1) (decE r2))
      (KeepPost dn vis fe decStmtL) :=
  (certTwoEqs_ref hD cx c h1 h2 r1 r2 cc).refAM

end nat

end L.Ind
