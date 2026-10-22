import ConAgua.Arena.DeclDivMod2

/-!
# The `Nat.div` family's pin gate, bottom up: statement builders, part 3 (lane `decls3`, `decls3-divmod`)

Statement records and lists (`StmtAt`, `StmtL`), `stmt1`, `cert_guard`, `cert_eq`, `cert_halves`, `cert_two_eqs`.
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
    (hI : IWOK m) : Rec3At m1 (r.headD 0) a b c := by
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

def certGuardW (p : Prog) (n : Nat) (m : Mem) (cx a b rv : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "nat_ap2" [rdW (m.arr64 IW) (cx + 4), a, b] m) fun r1 m1 =>
  ntBW (callW p n "eq_at1" [rdW (m1.arr64 IW) (cx + 5), r1.headD 0, rv] m1) fun r2 m2 =>
  some ([r2.headD 0], m2)

set_option maxHeartbeats 1600000 in
theorem certGuard_specW (p : Prog) (hp : p.lookup "cert_guard" = some certGuardL) (n : Nat) (s₀ : St)
    (cx a b rv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_guard" [cx, a, b, rv]
    ⦃fun r s' => LocEq s' s₀ ∧ certGuardW p n s₀.mem cx a b rv = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certGuardL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "eq_at1", callW_spec p n "nat_ap2"] <;>
    finish (gen := 30) (instances := 10000) [certGuardW, ntBW, rdW_eq]

theorem certGuard_ref (hD : DmProg2 p) (cx a b rv : Word) (cc : CertCtxA) :
    CallRef p "cert_guard" [cx, a, b, rv] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H a ∧ H b ∧ H rv)
      (certGuard cc (decE a) (decE b) (decE rv)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, ha, hb, hrv⟩ hcall => ?_
  have hw := callW_model (M := fun mm => certGuardW p k mm cx a b rv) (certGuard_specW p hD.lCertGuard k · cx a b rv) hcall
  unfold certGuardW at hw
  rw [hC.f4] at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.bleN.word.toUInt64 a b).bind_ ⟨hS, (dmWord_lt32 _), ha, hb⟩ hw
  rw [(hC.grow hG1).f5] at hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (eqAt1_ref hD cc.boolTy.word.toUInt64 (r1.headD 0) rv).bind_ hS1 hw
  have hG2 : IWGrow m m2 := hG1.trans hg2
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨_, a2, ?_, hS2, hG2, hl2, rfl⟩
  simp only [decE_eq_decI, decI_word] at hrun1 hrun2
  simp only [certGuard, StateT.run_bind, exc_ok_bind', decE_eq_decI, decI_word, hrun1, hrun2]
  try rfl

def certEqW (p : Prog) (n : Nat) (m : Mem) (cx c rhs : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "nat_ap2" [c, rdW (m.arr64 IW) (cx + 1), rdW (m.arr64 IW) (cx + 2)] m) fun r1 m1 =>
  ntBW (callW p n "eq_at1" [rdW (m1.arr64 IW) (cx + 0), r1.headD 0, rhs] m1) fun r2 m2 =>
  some ([r2.headD 0], m2)

set_option maxHeartbeats 1600000 in
theorem certEq_specW (p : Prog) (hp : p.lookup "cert_eq" = some certEqL) (n : Nat) (s₀ : St)
    (cx c rhs : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_eq" [cx, c, rhs]
    ⦃fun r s' => LocEq s' s₀ ∧ certEqW p n s₀.mem cx c rhs = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certEqL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "eq_at1", callW_spec p n "nat_ap2"] <;>
    finish (gen := 30) (instances := 10000) [certEqW, ntBW, rdW_eq]

theorem certEq_ref (hD : DmProg2 p) (cx c rhs : Word) (cc : CertCtxA) :
    CallRef p "cert_eq" [cx, c, rhs] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H rhs)
      (certEq cc (decI c) (decE rhs)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc, hrhs⟩ hcall => ?_
  have hw := callW_model (M := fun mm => certEqW p k mm cx c rhs) (certEq_specW p hD.lCertEq k · cx c rhs) hcall
  unfold certEqW at hw
  rw [hC.f1] at hw
  rw [hC.f2] at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg c cc.x.word.toUInt64 cc.y.word.toUInt64).bind_ ⟨hS, hc, (dmWord_lt32 _), (dmWord_lt32 _)⟩ hw
  rw [(hC.grow hG1).f0] at hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (eqAt1_ref hD cc.natTy.word.toUInt64 (r1.headD 0) rhs).bind_ hS1 hw
  have hG2 : IWGrow m m2 := hG1.trans hg2
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨_, a2, ?_, hS2, hG2, hl2, rfl⟩
  simp only [decE_eq_decI, decI_word] at hrun1 hrun2
  simp only [certEq, StateT.run_bind, exc_ok_bind', decE_eq_decI, decI_word, hrun1, hrun2]
  try rfl

def certHalvesW (p : Prog) (n : Nat) (m : Mem) (cx c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "nat_ap2" [rdW (m.arr64 IW) (cx + 11), rdW (m.arr64 IW) (cx + 1), rdW (m.arr64 IW) (cx + 9)] m) fun r1 m1 =>
  ntBW (callW p n "nat_ap2" [rdW (m1.arr64 IW) (cx + 11), rdW (m1.arr64 IW) (cx + 2), rdW (m1.arr64 IW) (cx + 9)] m1) fun r2 m2 =>
  ntBW (callW p n "nat_ap2" [c, r1.headD 0, r2.headD 0] m2) fun r3 m3 =>
  some ([r3.headD 0], m3)

set_option maxHeartbeats 1600000 in
theorem certHalves_specW (p : Prog) (hp : p.lookup "cert_halves" = some certHalvesL) (n : Nat) (s₀ : St)
    (cx c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_halves" [cx, c]
    ⦃fun r s' => LocEq s' s₀ ∧ certHalvesW p n s₀.mem cx c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certHalvesL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_ap2"] <;>
    finish (gen := 30) (instances := 10000) [certHalvesW, ntBW, rdW_eq]

theorem certHalves_ref (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    CallRef p "cert_halves" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certHalves cc (decI c)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mm => certHalvesW p k mm cx c) (certHalves_specW p hD.lCertHalves k · cx c) hcall
  unfold certHalvesW at hw
  rw [hC.f11] at hw
  rw [hC.f1] at hw
  rw [hC.f9] at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hG1, hl1, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.divN.word.toUInt64 cc.x.word.toUInt64 cc.two.word.toUInt64).bind_ ⟨hS, (dmWord_lt32 _), (dmWord_lt32 _), (dmWord_lt32 _)⟩ hw
  rw [(hC.grow hG1).f11] at hw
  rw [(hC.grow hG1).f2] at hw
  rw [(hC.grow hG1).f9] at hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg cc.divN.word.toUInt64 cc.y.word.toUInt64 cc.two.word.toUInt64).bind_ ⟨hS1, (dmWord_lt32 _), (dmWord_lt32 _), (dmWord_lt32 _)⟩ hw
  have hG2 : IWGrow m m2 := hG1.trans hg2
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
    (natAp2_ref hD.toNatEqProg c (r1.headD 0) (r2.headD 0)).bind_ ⟨hS2, hc, hl1, hl2⟩ hw
  have hG3 : IWGrow m m3 := hG2.trans hg3
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨_, a3, ?_, hS3, hG3, hl3, rfl⟩
  simp only [decE_eq_decI, decI_word] at hrun1 hrun2 hrun3
  simp only [certHalves, StateT.run_bind, exc_ok_bind', decE_eq_decI, decI_word, hrun1, hrun2, hrun3]
  try rfl



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
  simp only [decStmtL, StmtL, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, hq']
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
  simp only [decStmtL, StmtL, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, hq']
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

def stmt1W (p : Prog) (n : Nat) (m : Mem) (h e : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "sl_new1" [h] m) fun r1 m1 =>
  ntBW (callW p n "rec3" [r1.headD 0, r1.tail.headD 0, e] m1) fun r2 m2 => some ([r2.headD 0], m2)

theorem stmt1_specW (p : Prog) (hp : p.lookup "stmt1" = some stmt1) (n : Nat) (s₀ : St)
    (h e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "stmt1" [h, e]
    ⦃fun r s' => LocEq s' s₀ ∧ stmt1W p n s₀.mem h e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, stmt1]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "sl_new1", callW_spec p n "rec3"] <;>
    finish (gen := 20) (instances := 10000) [stmt1W, ntBW]

theorem stmt1_ref (hD : DmProg2 p) (h e : Word) :
    CallRef p "stmt1" [h, e] (fun m s => StageR dn vis fe m s ∧ H h ∧ H e)
      (pure ([decE h], decE e) : AM (List EIdx × EIdx)) (KeepPost dn vis fe decStmt) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hh, he⟩ hcall => ?_
  have hw := callW_model (M := fun mq => stmt1W p k mq h e) (stmt1_specW p hD.lStmt1 k · h e) hcall
  unfold stmt1W at hw
  obtain ⟨r1, m1, ⟨hrec1, hr1⟩, hw⟩ := (slNew1_fref p hD.lIwAlloc hD.lSlNew1 h).bind_ hS.2 hw
  have hS1 := hrec1.2.1.stage hS
  have hg1 := hrec1.2.1.1
  obtain ⟨r2, m2, hrec2, hw⟩ :=
    (rec3_fref p hD.lIwAlloc hD.lRec3 (r1.headD 0) (r1.tail.headD 0) e).bind_ hS1.2 hw
  have hS2 := hrec2.2.1.stage hS1
  have hg2 := hrec2.2.1.1
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨([decE h], decE e), s, rfl, hS2, hg1.trans hg2, ?_⟩
  have hq : (r1.headD 0).toNat = iwTop m := by rw [hrec1.1]; rfl
  have hl1 : (r1.tail.headD 0).toNat = 1 := by rw [hr1]; rfl
  have hbound : (r1.headD 0).toNat + (r1.tail.headD 0).toNat ≤ iwTop m1 := by
    have := hrec1.2.2.2.1; simp at this; omega
  exact stmtAt_of_rec3 hrec2 hS1.2 hbound (slNew1_dec hrec1 hh hr1) he

/-! ## `cert_two_eqs` -/

def certTwoEqsW (p : Prog) (n : Nat) (m : Mem) (cx c h1 h2 r1 r2 : Word) :
    Option (List Word × Mem) :=
  ntBW (callW p n "cert_eq" [cx, c, r1] m) fun ra ma =>
  ntBW (callW p n "cert_eq" [cx, c, r2] ma) fun rb mb =>
  ntBW (callW p n "stmt1" [h1, ra.headD 0] mb) fun rs1 ms1 =>
  ntBW (callW p n "stmt1" [h2, rb.headD 0] ms1) fun rs2 ms2 =>
  ntBW (callW p n "rec2" [rs1.headD 0, rs2.headD 0] ms2) fun rq mq => some ([rq.headD 0, 2], mq)

theorem certTwoEqs_specW (p : Prog) (hp : p.lookup "cert_two_eqs" = some certTwoEqsL) (n : Nat)
    (s₀ : St) (cx c h1 h2 r1 r2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "cert_two_eqs" [cx, c, h1, h2, r1, r2]
    ⦃fun r s' => LocEq s' s₀ ∧ certTwoEqsW p n s₀.mem cx c h1 h2 r1 r2 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certTwoEqsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "cert_eq", callW_spec p n "stmt1", callW_spec p n "rec2"] <;>
    finish (gen := 20) (instances := 10000) [certTwoEqsW, ntBW]

theorem certTwoEqs_ref (hD : DmProg2 p) (cx c h1 h2 r1 r2 : Word) (cc : CertCtxA) :
    CallRef p "cert_two_eqs" [cx, c, h1, h2, r1, r2]
      (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H h1 ∧ H h2 ∧ H r1 ∧ H r2)
      (certTwoEqs cc (decI c) (decE h1) (decE h2) (decE r1) (decE r2))
      (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hC, hc, hh1, hh2, hr1, hr2⟩ hcall => ?_
  have hw := callW_model (M := fun mq => certTwoEqsW p k mq cx c h1 h2 r1 r2)
    (certTwoEqs_specW p hD.lCertTwoEqs k · cx c h1 h2 r1 r2) hcall
  unfold certTwoEqsW at hw
  obtain ⟨ra, ma, xa, aa, hruna, ⟨hSa, hga, hla, rfl⟩, hw⟩ :=
    (certEq_ref hD cx c r1 cc).bind_ ⟨hS, hC, hc, hr1⟩ hw
  obtain ⟨rb, mb, xb, ab, hrunb, ⟨hSb, hgb, hlb, rfl⟩, hw⟩ :=
    (certEq_ref hD cx c r2 cc).bind_ ⟨hSa, hC.grow hga, hc, hr2⟩ hw
  have hGb : IWGrow m mb := hga.trans hgb
  obtain ⟨rs1, ms1, xs1, as1, hruns1, ⟨hSs1, hgs1, hs1⟩, hw⟩ :=
    (stmt1_ref hD h1 (ra.headD 0)).bind_ ⟨hSb, hh1, hla⟩ hw
  obtain ⟨rfl, rfl⟩ := pure_run_eq hruns1
  obtain ⟨rs2, ms2, xs2, as2, hruns2, ⟨hSs2, hgs2, hs2⟩, hw⟩ :=
    (stmt1_ref hD h2 (rb.headD 0)).bind_ ⟨hSs1, hh2, hlb⟩ hw
  obtain ⟨rfl, rfl⟩ := pure_run_eq hruns2
  obtain ⟨rq, mq, hrec, hw⟩ :=
    (rec2_fref p hD.lIwAlloc hD.lRec2 (rs1.headD 0) (rs2.headD 0)).bind_ hSs2.2 hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨[([decE h1], decE (ra.headD 0)), ([decE h2], decE (rb.headD 0))], _, ?_,
    hrec.2.1.stage hSs2, hGb.trans (hgs1.trans (hgs2.trans hrec.2.1.1)),
    stmtL_of_rec2 hrec (hs1.grow hgs2) hs2⟩
  simp only [decE_eq_decI] at hruna hrunb
  simp only [certTwoEqs, StateT.run_bind, exc_ok_bind', decE_eq_decI, hruna, hrunb]
  try rfl



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
