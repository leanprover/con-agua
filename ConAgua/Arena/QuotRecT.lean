module

public import ConAgua.Arena.QuotRecW
public import ConAgua.Arena.IndPosSpec.EnvFindWHit
public import ConAgua.Arena.IndTwin
public import ConAgua.Arena.StageC
public import ConRon.Bridge.Checker.Basis
import ConAgua.Arena.RefWalk
import all ConAgua.Arena.BasisL

@[expose] public section

/-!
# The quotient records' refinements (lane `ronsync2`, stage 3)

Against the models of `QuotRecW.lean`: `quot_preds_ok(vis, k)` refines `quotPredsOk fe k` (the three
pins read, each looked up in the view, the slot's conjunction).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

theorem exb {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl
theorem exm {ε α β : Type} (x : α) (f : α → β) : (f <$> (Except.ok x : Except ε α)) = Except.ok (f x) := rfl

/-- A `pin_at` call through its model. -/
theorem callW_pinAtW {p : Prog} (hp : p.lookup "pin_at" = some pinAtL) {n : Nat} {m m' : Mem}
    {i : Word} {r : List Word} (h : callW p n "pin_at" [i] m = some (r, m')) :
    pinAtW m i = some (r, m') := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (pinAt_specW p hp n _ i) h
  exact hW

/-- **`env_find`'s hit flag is the view's `find?`**. -/
theorem findRes_isSome {vis : Word} {fe : IFEnv} {m : Mem} {w : Word} (hE : EnvR m vis fe)
    (hw : w.toNat < 2 ^ 32) : (fe.find? (decI w)).isSome = ((findRes m vis w).headD 0 != 0) := by
  by_cases h0 : (findRes m vis w).headD 0 = 0
  · rw [findRes_miss hE hw h0, h0]; rfl
  · obtain ⟨e, ci, hci⟩ := findRes_hit hE hw h0
    rw [e, hci]; simpa [List.headD] using h0

/-- One pin's lookup: the pin read (the memory unchanged), `env_find` at it. -/
theorem pinFind_ok {p : Prog} (hB : BasisProg p) (hpa : p.lookup "pin_at" = some pinAtL)
    {vis : Word} {fe : IFEnv} {m m1 m2 : Mem} {a : AState} {i : Word} {n : Nat}
    {r1 r2 : List Word} (hS : StageR vis fe m a)
    (h1 : callW p n "pin_at" [i] m = some (r1, m1))
    (h2 : callW p n "env_find" [r1.headD 0, vis] m1 = some (r2, m2)) :
    m = m1 ∧ m = m2 ∧ ∃ w : Word, w.toNat < 2 ^ 32 ∧ r1.headD 0 = w ∧
      (if i = 51 then (pinAt 51).run a = .ok (decI w, a)
        else (pinAt i.toNat).run a = .ok (decI w, a)) ∧
      (fe.find? (decI w)).isSome = (r2.headD 0 != 0) := by
  have hW := callW_pinAtW hpa h1
  by_cases h51 : i = 51
  · subst h51
    obtain ⟨rfl, rfl, hl, hrun⟩ := pinAtW_ok51 hW hS.check.pins
    obtain ⟨rfl, rfl⟩ := envFind_callB hB hl hS.check.env h2
    exact ⟨rfl, rfl, _, hl, rfl, by simpa using hrun, findRes_isSome hS.check.env hl⟩
  · obtain ⟨rfl, rfl, hl, hrun⟩ := pinAtW_ok hW hS.check.pins h51
    obtain ⟨rfl, rfl⟩ := envFind_callB hB hl hS.check.env h2
    exact ⟨rfl, rfl, _, hl, rfl, by simpa [h51] using hrun, findRes_isSome hS.check.env hl⟩

/-- **`quot_preds_ok(vis, k.slot)` refines `quotPredsOk fe k`** (the memory and the twin state
unchanged). -/
theorem quotPredsOkW_ok {p : Prog} (hB : BasisProg p) (hpa : p.lookup "pin_at" = some pinAtL)
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {n : Nat} {r : List Word}
    (k : ConLeche.QuotKind) (hS : StageR vis fe m a)
    (h : quotPredsOkW p n m vis (UInt64.ofNat k.slot) = some (r, m')) :
    m' = m ∧ (ConRon.Arena.quotPredsOk fe k).run a = .ok ((r.headD 0 != 0), a) := by
  cases n with
  | zero => simp [quotPredsOkW] at h
  | succ n =>
  simp only [quotPredsOkW] at h
  cases h1 : callW p n "pin_at" [0] m with
  | none => rw [h1] at h; simp [quotPredsOkW.k_pin_at] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at h; simp only [quotPredsOkW.k_pin_at] at h
  cases h2 : callW p n "env_find" [r1.headD 0, vis] m1 with
  | none => rw [h2] at h; simp [quotPredsOkW.k_env_find] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2] at h; simp only [quotPredsOkW.k_env_find] at h
  obtain ⟨rfl, rfl, w1, -, -, hp1, hf1⟩ := pinFind_ok hB hpa hS h1 h2
  cases h3 : callW p n "pin_at" [47] m with
  | none => rw [h3] at h; simp [quotPredsOkW.k_pin_at_2] at h
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3] at h; simp only [quotPredsOkW.k_pin_at_2] at h
  cases h4 : callW p n "env_find" [r3.headD 0, vis] m3 with
  | none => rw [h4] at h; simp [quotPredsOkW.k_env_find_2] at h
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [h4] at h; simp only [quotPredsOkW.k_env_find_2] at h
  obtain ⟨rfl, rfl, w3, -, -, hp3, hf3⟩ := pinFind_ok hB hpa hS h3 h4
  cases h5 : callW p n "pin_at" [51] m with
  | none => rw [h5] at h; simp [quotPredsOkW.k_pin_at_3] at h
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  rw [h5] at h; simp only [quotPredsOkW.k_pin_at_3] at h
  cases h6 : callW p n "env_find" [r5.headD 0, vis] m5 with
  | none => rw [h6] at h; simp [quotPredsOkW.k_env_find_3] at h
  | some x6 =>
  obtain ⟨r6, m6⟩ := x6
  rw [h6] at h
  obtain ⟨rfl, rfl, w5, -, -, hp5, hf5⟩ := pinFind_ok hB hpa hS h5 h6
  simp only [show (0 : Word) ≠ 51 by decide, show (47 : Word) ≠ 51 by decide, ite_true,
    ite_false] at hp1 hp3 hp5
  have e0 : (pinEq).run a = .ok (decI w1, a) := hp1
  have e47 : (pinQuot).run a = .ok (decI w3, a) := hp3
  have e51 : (pinQuotMk).run a = .ok (decI w5, a) := hp5
  simp only [ConRon.Arena.quotPredsOk, StateT.run_bind, e0, exb, e47, e51, StateT.run_pure]
  cases k <;> simp [ConLeche.QuotKind.slot, quotPredsOkW.k_env_find_3,
      hf1, hf3, hf5] at h ⊢ <;>
    first
    | (obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
    | (split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; refine ⟨rfl, ?_⟩; show Except.ok _ = Except.ok _; simp_all))
    | skip

/-! ## `check_quot_record(vis, k, q)` -/

/-- **The two callees of `check_quot_record` that read the quotient block and rename** (their
refinements under `StageT`: `quot_pin_hit`, `quot_at`). -/
structure QuotSims (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop where
  qph : ∀ (n : Nat) (vis : Word) (fe : IFEnv) (m : Mem) (a : AState) (q : Word) (cv : IConstantVal)
    (c : ConLeche.ConstantVal) (k : ConLeche.QuotKind), StageT dn vis fe m a →
    ConRon.Bridge.StateOK a → ConRon.Bridge.ReadOK a → decCV (erecP m) q.toNat = some cv →
    ConRon.Arena.Frontend.denoteCV a.store cv = some c →
    Sim (callW p n "quot_pin_hit" [UInt64.ofNat k.slot, q] m) (ConRon.Arena.quotPinHit k cv) a
      (fun r b m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0 ≠ 0 ↔ b = true))
  qat : ∀ (n : Nat) (vis : Word) (fe : IFEnv) (m : Mem) (a : AState) (q : Word) (cv : IConstantVal)
    (c : ConLeche.ConstantVal) (k : ConLeche.QuotKind), StageT dn vis fe m a →
    ConRon.Bridge.StateOK a → ConRon.Bridge.ReadOK a → decCV (erecP m) q.toNat = some cv →
    ConRon.Arena.Frontend.denoteCV a.store cv = some c →
    Sim (callW p n "quot_at" [UInt64.ofNat k.slot, q] m) (ConRon.Arena.quotAt k cv) a
      (fun r ci m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧
        decCI (erecP m') (r.headD 0).toNat = some ci)

/-- A weaker post. -/
theorem RefE.weakenP {α β : Type} {G : Prop} {x : Except Err α} {T : AM β} {a : AState}
    {R R' : α → β → AState → Prop} (h : RefE G x T a R) (hR : ∀ v y a', R v y a' → R' v y a') :
    RefE G x T a R' := by
  cases x with
  | error e => exact h
  | ok v => obtain ⟨y, a', h1, h2⟩ := h; exact ⟨y, a', h1, hR _ _ _ h2⟩

/-- The lookups `check_quot_record` takes. -/
structure QuotRecProg (p : Prog) : Prop where
  cqr : p.lookup "check_quot_record" = some checkQuotRecordL
  qpo : p.lookup "quot_preds_ok" = some quotPredsOk
  pa : p.lookup "pin_at" = some pinAtL
  basis : BasisProg p

/-- `quot_preds_ok` as a call. -/
theorem callW_quotPredsOk {p : Prog} (hP : QuotRecProg p) {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {n : Nat} {r : List Word} (k : ConLeche.QuotKind) (hS : StageR vis fe m a)
    (h : callW p n "quot_preds_ok" [vis, UInt64.ofNat k.slot] m = some (r, m')) :
    m' = m ∧ (ConRon.Arena.quotPredsOk fe k).run a = .ok ((r.headD 0 != 0), a) := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (quotPredsOk_specW p hP.qpo n _ vis _) h
  exact quotPredsOkW_ok hP.basis hP.pa k hS hW

/-- `install_basis_decl`'s run keeps the core's memos: its callees `env_find`, `env_push` are
leaves. -/
theorem ibdE_memos {p : Prog} (hcl : LeafClosed p) {n : Nat} {m m' : Mem} {vis c r : Word}
    (h : installBasisDeclE p n m vis c = .ok (r, m')) (hM : CoreMemos m) : CoreMemos m' := by
  have hlf : ∀ {f : FnName}, f ∈ leafFns → ∀ {k : Nat} {args : List Word} {x y : Mem}
      {rx : List Word}, callW p k f args x = some (rx, y) → CoreMemos x → CoreMemos y :=
    fun {_} hf {_ _ _ _ _} hc hM => hM.frame (callW_leafFrame hcl hf hc) leafA_memo leafC_memo leafA_walk
      leafC_walk leafA_lp leafC_lp leafA_hb leafC_hb
  cases n with
  | zero => rw [installBasisDeclE.eq_1] at h; cases h
  | succ n =>
  rw [installBasisDeclE.arm1] at h
  generalize hw : rdW _ _ = w at h
  rcases h1 : callW p n "env_find" [w, vis] m with _ | ⟨r1, m1⟩
  · rw [h1, liftE_none, installBasisDeclE.k_env_find.none] at h; cases h
  rw [h1, liftE_some] at h
  by_cases hb : r1.headD 0 = 0
  · rw [installBasisDeclE.k_env_find.arm1 p _ _ _ _ _ hb] at h
    rcases h2 : callW p n "env_push" [vis, c] m1 with _ | ⟨r2, m2⟩
    · rw [h2, liftE_none, installBasisDeclE.k_env_push.none] at h; cases h
    rw [h2, liftE_some, installBasisDeclE.k_env_push.arm1] at h
    cases h
    exact hlf (by decide) h2 (hlf (by decide) h1 hM)
  · rw [installBasisDeclE.k_env_find.abort1 p _ _ _ _ _ hb] at h; cases h

/-- What `check_quot_record` gives besides the twin's environment: `install_basis_decl`'s post and
the core's memos. -/
structure CqrPost (m : Mem) (r : Word) (m' : Mem) (fe' : IFEnv) (a' : AState) : Prop where
  stage : StageR r fe' m' a'
  grow : IWGrow m m'
  memos : CoreMemos m'

/-- **`check_quot_record(vis, k.slot, q)` refines `checkQuotRecord fe k cv`, both outcomes**, under
`StageT`: the pin match (`quot_pin_hit`), the slot's predecessors (`quot_preds_ok`), the install
of the pin at the record's names (`quot_at`, `install_basis_decl`). -/
theorem cqr_ref {p : Prog} (hP : QuotRecProg p) (hcl : LeafClosed p) {dn : NIdx → Option ConLeche.Name}
    (hQ : QuotSims p dn) {vis : Word} {fe : IFEnv} {a : AState} (n : Nat) {m : Mem} {q : Word}
    {cv : IConstantVal} {c : ConLeche.ConstantVal} (k : ConLeche.QuotKind) (hS : StageT dn vis fe m a)
    (hok : ConRon.Bridge.StateOK a) (hr : ConRon.Bridge.ReadOK a)
    (hq : decCV (erecP m) q.toNat = some cv)
    (hden : ConRon.Arena.Frontend.denoteCV a.store cv = some c) :
    RefE True (checkQuotRecordE p n m vis (UInt64.ofNat k.slot) q) (ConRon.Arena.checkQuotRecord fe k cv) a
      (fun v fe' a' => CqrPost m v.1 v.2 fe' a') := by
  cases n with
  | zero => exact RefE.of_cls0 (by simp)
  | succ n =>
  simp only [checkQuotRecordE]
  refine RefE.onlySim (fun _ => checkQuotRecordE.k_quot_pin_hit.none ..) (fun r m1 h => hQ.qph n vis fe m a q cv c k hS hok hr hq hden r m1 h)
    fun r1 m1 ⟨b, a1, hrun1, hS1, hg1, hb1⟩ => ?_
  simp only [ConRon.Arena.checkQuotRecord]
  obtain ⟨hst1, -⟩ := ConRon.Bridge.quotPinHit_run hok hr hden hrun1
  refine RefE.bind_right hrun1 ?_
  by_cases h0 : r1.headD 0 = 0
  · have hb : b = false := by cases b <;> simp_all
    subst hb
    have hk4 : (UInt64.ofNat k.slot = 4) ↔ k = .sound := by cases k <;> decide
    by_cases h4 : k = .sound
    · rw [checkQuotRecordE.k_quot_pin_hit.abort1 p _ _ _ _ _ _ h0 (hk4.mpr h4)]
      subst h4
      exact fun _ => ErrClaim.bind_left (ErrClaim.fail_abort _ _ (by decide))
    · rw [checkQuotRecordE.k_quot_pin_hit.abort2 p _ _ _ _ _ _ h0 (fun e => h4 (hk4.mp e))]
      exact fun _ => ErrClaim.bind_left (by cases k <;> first | exact absurd rfl h4 | exact ErrClaim.fail_abort _ _ (by decide))
  have hb : b = true := by simp_all
  subst hb
  rw [checkQuotRecordE.k_quot_pin_hit.arm1 p _ _ _ _ _ _ h0]
  simp only [ite_true]
  refine RefE.onlySim (fun _ => checkQuotRecordE.k_quot_preds_ok.none ..)
    (Q := fun r2 m2 => m1 = m2 ∧ (ConRon.Arena.quotPredsOk fe k).run a1 = .ok ((r2.headD 0 != 0), a1))
    (fun r m2 h => let ⟨e, h'⟩ := callW_quotPredsOk hP k hS1.stage h; ⟨e.symm, h'⟩) fun r2 m2 ⟨hm2, hrun2⟩ => ?_
  subst hm2
  refine RefE.bind_right hrun2 ?_
  by_cases h2 : r2.headD 0 = 0
  · rw [checkQuotRecordE.k_quot_preds_ok.abort1 p _ _ _ _ _ _ h2]
    simp only [h2, bne_self_eq_false]
    exact fun _ => ErrClaim.bind_left (ErrClaim.fail_abort _ _ (by decide))
  rw [checkQuotRecordE.k_quot_preds_ok.arm1 p _ _ _ _ _ _ h2]
  simp only [bne_iff_ne, ne_eq, h2, not_false_eq_true, ite_true]
  have hq1 : decCV (erecP m1) q.toNat = some cv := ArrExt.decCV hg1.ext hq
  refine RefE.onlySim (fun _ => checkQuotRecordE.k_quot_at.none ..)
    (fun r m3 h => hQ.qat n vis fe m1 a1 q cv c k hS1 hst1.ok hst1.read hq1
      (ConRon.Bridge.denoteCV_ext hden hst1.ext) r m3 h) fun r3 m3 ⟨ci, a3, hrun3, hS3, hg3, hci⟩ => ?_
  rw [checkQuotRecordE.k_quot_at.arm1]
  refine RefE.bind_right hrun3 ?_
  rcases e : installBasisDeclE p n m3 vis (r3.headD 0) with e | v
  · have := ibd_ref (dn := dn) hP.basis n hS3.stage hci; rw [e] at this; exact this
  have := ibd_ref (dn := dn) hP.basis n hS3.stage hci; rw [e] at this
  obtain ⟨y, a', h1, h2⟩ := this
  exact ⟨y, a', h1, h2.stage, hg1.trans (hg3.trans h2.grow), ibdE_memos hcl e hS3.twin.memos⟩

end L.Ind
