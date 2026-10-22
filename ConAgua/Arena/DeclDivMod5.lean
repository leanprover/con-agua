import ConAgua.Arena.DeclDivMod4
import ConAgua.Arena.IndMaster
import ConAgua.Arena.IndCopy

/-!
# The `Nat.div` family's pin gate, bottom up: applying a certificate (lane `decls3`, `decls3-divmod`)

Part 5: `div_mod_cert_applied`, `subst_const0_list`, `consts_resolve_all`.

The substitution functions `subst_const0`, `subst_const_all` belong to helper `decls3-nat`
(`DeclNatSub.lean`, not in this branch yet): this file takes their refinements as the explicit
hypotheses `SubstC0`, `SubstCAll` (`CallRef`s at the stage relation, universally quantified over
the handles), to be discharged by `substConst0_refines` and its `substConstAll` sibling.
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

section subst
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- **`subst_const0` refines `substConst0`** at the walk fuel `4000000000` (helper `decls3-nat`'s). -/
def SubstC0 : Prop := ∀ nm r h : Word, H nm → H r → H h →
  CallRef p "subst_const0" [nm, r, 4000000000, h] (StageR dn vis fe)
    (substConst0 (decI nm) (decE r) coreWalkFuel (decE h)) (KeepPost dn vis fe decW0E)

/-- **`subst_const_all` refines `substConstAll`** at the walk fuel `4000000000`. -/
def SubstCAll : Prop := ∀ nm r h : Word, H nm → H r → H h →
  CallRef p "subst_const_all" [nm, r, 4000000000, h] (StageR dn vis fe)
    (substConstAll (decI nm) (decE r) coreWalkFuel (decE h)) (KeepPost dn vis fe decW0E)

end subst

structure DmProg5 (p : Prog) : Prop extends DmProg2 p where
  lSlCons : p.lookup "sl_cons" = some slCons
  lIwCopy : p.lookup "iw_copy" = some iwCopy
  lSubstConst0 : p.lookup "subst_const0" = some substConst0L
  lSubstConstAll : p.lookup "subst_const_all" = some substConstAllL
  lSubstConst0List : p.lookup "subst_const0_list" = some substConst0ListL
  lConstsResolveAll : p.lookup "consts_resolve_all" = some constsResolveAllL
  lDivModCertGuard : p.lookup "div_mod_cert_guard" = some divModCertGuardL

section applied
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

theorem word_eq_of_toNat {w : Word} {k : Nat} (hk : k < 2 ^ 64) (h : w.toNat = k) :
    w = UInt64.ofNat k := UInt64.toNat_inj.mp (by rw [h, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)])

/-! ## `div_mod_cert_applied` -/

def appliedW (p : Prog) (n : Nat) (m : Mem) (pr ho hl : Word) : Option (List Word × Mem) :=
  bW (callW p n "nat_var" [0] m) fun r1 m1 =>
  bW (callW p n "nat_var" [1] m1) fun r2 m2 =>
  bW (callW p n "mk_app" [pr, r1.headD 0] m2) fun r3 m3 =>
  bW (callW p n "mk_app" [r3.headD 0, r2.headD 0] m3) fun r4 m4 =>
  if hl = 1 then
    bW (callW p n "intern_fvar" [2, rdW (m4.arr64 IW) ho] m4) fun r5 m5 =>
    bW (callW p n "mk_app" [r4.headD 0, r5.headD 0] m5) fun r6 m6 => some ([r6.headD 0], m6)
  else if hl = 2 then
    bW (callW p n "intern_fvar" [2, rdW (m4.arr64 IW) ho] m4) fun r5 m5 =>
    bW (callW p n "mk_app" [r4.headD 0, r5.headD 0] m5) fun r6 m6 =>
    bW (callW p n "intern_fvar" [3, rdW (m6.arr64 IW) (ho + 1)] m6) fun r7 m7 =>
    bW (callW p n "mk_app" [r6.headD 0, r7.headD 0] m7) fun r8 m8 => some ([r8.headD 0], m8)
  else some ([r4.headD 0], m4)

set_option maxHeartbeats 1600000 in
theorem applied_specW (p : Prog) (hp : p.lookup "div_mod_cert_applied" = some divModCertAppliedL)
    (n : Nat) (s₀ : St) (pr ho hl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "div_mod_cert_applied" [pr, ho, hl]
    ⦃fun r s' => LocEq s' s₀ ∧ appliedW p n s₀.mem pr ho hl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divModCertAppliedL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_var", callW_spec p n "mk_app", callW_spec p n "intern_fvar"] <;>
    finish (gen := 30) (instances := 10000) [appliedW, bW, rdW_eq]

theorem iw_rd_grow {m m' : Mem} (hg : IWGrow m m') {i : Word} (hi : i.toNat < iwTop m) :
    rdW (m'.arr64 IW) i = rdW (m.arr64 IW) i := by
  simp only [rdW]; rw [hg.2.2.1 i.toNat hi]

theorem word_add_one {w : Word} (h : w.toNat + 1 < 2 ^ 64) : (w + 1).toNat = w.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

set_option maxHeartbeats 1600000 in
theorem applied_ref (hD : DmProg5 p) (pr ho hl : Word) (hyps : List EIdx) :
    CallRef p "div_mod_cert_applied" [pr, ho, hl]
      (fun m s => StageR dn vis fe m s ∧ H pr ∧ decHL m ho.toNat hl.toNat = some hyps ∧
        ho.toNat + hl.toNat ≤ iwTop m)
      (divModCertApplied (decE pr) hyps) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hpr, hd, hb⟩ hcall => ?_
  have hw := callW_model (M := fun mq => appliedW p k mq pr ho hl)
    (applied_specW p hD.lDivModCertApplied k · pr ho hl) hcall
  unfold appliedW at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1, rfl⟩, hw⟩ :=
    (natVar_ref hD.toDmProg2 (0 : Word)).bind_ hS hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
    (natVar_ref hD.toDmProg2 (1 : Word)).bind_ hS1 hw
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
    (mkApp_ref hD.toMasterProg pr (r1.headD 0)).bind_ hS2 hw
  obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hw⟩ :=
    (mkApp_ref hD.toMasterProg (r3.headD 0) (r2.headD 0)).bind_ hS3 hw
  have hG4 : IWGrow m m4 := hg1.trans (hg2.trans (hg3.trans hg4))
  simp only [decE_eq_decI] at hrun3 hrun4
  have hlen := decHL_length m hd
  have h0w : (0 : Word).toNat = 0 := rfl
  have h1w : (1 : Word).toNat = 1 := rfl
  have h2w : (2 : Word).toNat = 2 := rfl
  have h3w : (3 : Word).toNat = 3 := rfl
  rw [h0w] at hrun1
  rw [h1w] at hrun2
  rcases hyps with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · have hn1 : hl ≠ 1 := fun e => by rw [e] at hlen; simp at hlen
    have hn2 : hl ≠ 2 := fun e => by rw [e] at hlen; simp at hlen
    rw [if_neg hn1, if_neg hn2] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨_, a4, ?_, hS4, hG4, hl4, rfl⟩
    simp only [divModCertApplied, StateT.run_bind, exc_ok_bind', decE_eq_decI, hrun1, hrun2, hrun3,
      hrun4]
    rfl
  · have e1 : hl = 1 := UInt64.toNat_inj.mp (by simp at hlen ⊢; omega)
    subst e1
    obtain ⟨-, hwlt, ha, -⟩ := decHL_cons_iw hS.2.2.2.1 hd
    have hlt : ho.toNat < iwTop m := by simp only [h1w, h2w] at hb; omega
    rw [if_pos rfl, iw_rd_grow hG4 hlt] at hw
    obtain ⟨r5, m5, x5, a5, hrun5, ⟨hS5, hg5, hl5, rfl⟩, hw⟩ :=
      (internFVar_ref hD.toMasterProg 2 (rdW (m.arr64 IW) ho) hwlt).bind_ hS4 hw
    obtain ⟨r6, m6, x6, a6, hrun6, ⟨hS6, hg6, hl6, rfl⟩, hw⟩ :=
      (mkApp_ref hD.toMasterProg (r4.headD 0) (r5.headD 0)).bind_ hS5 hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨_, a6, ?_, hS6, hG4.trans (hg5.trans hg6), hl6, rfl⟩
    rw [h2w] at hrun5
    try simp only [decE_eq_decI] at hrun5 hrun6
    simp only [divModCertApplied, StateT.run_bind, exc_ok_bind', decE_eq_decI, hrun1, hrun2, hrun3,
      hrun4, ha]
    simp only [hrun5, exc_ok_bind']
    exact hrun6
  · have e2 : hl = 2 := UInt64.toNat_inj.mp (by simp at hlen ⊢; omega)
    subst e2
    have hn1 : (2 : Word) ≠ 1 := by decide
    obtain ⟨-, hwlt, ha, hrest⟩ := decHL_cons_iw hS.2.2.2.1 hd
    obtain ⟨-, hwlt2, hb2, -⟩ := decHL_cons_iw hS.2.2.2.1 hrest
    have hlt : ho.toNat < iwTop m := by simp only [h1w, h2w] at hb; omega
    have hlt2 : (ho + 1).toNat < iwTop m := by
      have h1 := hS.2.1; have h2 := hS.2.2.2.1; simp only [h1w, h2w] at hb; have e := word_add_one (w := ho) (by omega); omega
    rw [if_neg hn1, if_pos rfl, iw_rd_grow hG4 hlt] at hw
    obtain ⟨r5, m5, x5, a5, hrun5, ⟨hS5, hg5, hl5, rfl⟩, hw⟩ :=
      (internFVar_ref hD.toMasterProg 2 (rdW (m.arr64 IW) ho) hwlt).bind_ hS4 hw
    obtain ⟨r6, m6, x6, a6, hrun6, ⟨hS6, hg6, hl6, rfl⟩, hw⟩ :=
      (mkApp_ref hD.toMasterProg (r4.headD 0) (r5.headD 0)).bind_ hS5 hw
    have hG6 : IWGrow m m6 := hG4.trans (hg5.trans hg6)
    rw [iw_rd_grow hG6 hlt2] at hw
    obtain ⟨r7, m7, x7, a7, hrun7, ⟨hS7, hg7, hl7, rfl⟩, hw⟩ :=
      (internFVar_ref hD.toMasterProg 3 (rdW (m.arr64 IW) (ho + 1)) hwlt2).bind_ hS6 hw
    obtain ⟨r8, m8, x8, a8, hrun8, ⟨hS8, hg8, hl8, rfl⟩, hw⟩ :=
      (mkApp_ref hD.toMasterProg (r6.headD 0) (r7.headD 0)).bind_ hS7 hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨_, a8, ?_, hS8, hG6.trans (hg7.trans hg8), hl8, rfl⟩
    rw [h2w] at hrun5
    rw [h3w] at hrun7
    try simp only [decE_eq_decI] at hrun5 hrun6 hrun7 hrun8
    simp only [divModCertApplied, StateT.run_bind, exc_ok_bind', decE_eq_decI, hrun1, hrun2, hrun3,
      hrun4, ha, hb2]
    simp only [hrun5, exc_ok_bind', hrun6, hrun7]
    exact hrun8
  · have hn1 : hl ≠ 1 := fun e => by rw [e] at hlen; simp at hlen
    have hn2 : hl ≠ 2 := fun e => by rw [e] at hlen; simp at hlen
    rw [if_neg hn1, if_neg hn2] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨_, a4, ?_, hS4, hG4, hl4, rfl⟩
    simp only [divModCertApplied, StateT.run_bind, exc_ok_bind', decE_eq_decI, hrun1, hrun2, hrun3,
      hrun4]
    rfl

@[refines ConRon.Arena.divModCertApplied]
theorem divModCertApplied_refines (hD : DmProg5 p) (pr ho hl : Word) (hyps : List EIdx) :
    RefAM p "div_mod_cert_applied" [pr, ho, hl]
      (fun m s => StageR dn vis fe m s ∧ H pr ∧ decHL m ho.toNat hl.toNat = some hyps ∧
        ho.toNat + hl.toNat ≤ iwTop m)
      (divModCertApplied (decE pr) hyps) (KeepPost dn vis fe decW0E) :=
  (applied_ref hD pr ho hl hyps).refAM

/-! ## `subst_const0_list` -/

def sc0ListW (p : Prog) (n : Nat) (m : Mem) (nm r o l : Word) : Option (List Word × Mem) :=
  if l = 0 then some ([0, 0], m) else
  bW (callW p n "subst_const0" [nm, r, 4000000000, rdW (m.arr64 IW) o] m) fun r1 m1 =>
  bW (callW p n "subst_const0_list" [nm, r, o + 1, l - 1] m1) fun r2 m2 =>
  bW (callW p n "sl_cons" [r1.headD 0, r2.headD 0, r2.tail.headD 0] m2) fun r3 m3 =>
  some ([r3.headD 0, r3.tail.headD 0], m3)

set_option maxHeartbeats 1600000 in
theorem sc0List_specW (p : Prog) (hp : p.lookup "subst_const0_list" = some substConst0ListL)
    (n : Nat) (s₀ : St) (nm r o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "subst_const0_list" [nm, r, o, l]
    ⦃fun res s' => LocEq s' s₀ ∧ sc0ListW p n s₀.mem nm r o l = some (res, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, substConst0ListL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "subst_const0", callW_spec p n "subst_const0_list",
      callW_spec p n "sl_cons"] <;>
    finish (gen := 30) (instances := 10000) [sc0ListW, bW, rdW_eq]

theorem sc0List_ref (hD : DmProg5 p) (hs0 : SubstC0 p dn vis fe) (nm r : Word) (hn : H nm) (hr : H r) :
    ∀ (hyps : List EIdx) (o l : Word) (k : Nat) (m : Mem) (a : AState) (res : List Word) (m' : Mem),
      StageR dn vis fe m a → decHL m o.toNat l.toNat = some hyps → o.toNat + l.toNat ≤ iwTop m →
      callW p k "subst_const0_list" [nm, r, o, l] m = some (res, m') →
      ∃ x a', (substConst0List (decI nm) (decE r) hyps).run a = .ok (x, a') ∧
        KeepPost dn vis fe (decRL (fun m => decHL m) 0) m m' a' res x := by
  intro hyps
  induction hyps with
  | nil =>
    intro o l k m a res m' hS hd hb hc
    have hl0 : l = 0 := by
      have := decHL_length m hd
      exact UInt64.toNat_inj.mp (by simp at this ⊢; omega)
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mm => sc0ListW p k mm nm r o l)
      (sc0List_specW p hD.lSubstConst0List k · nm r o l) hc
    simp only [sc0ListW, hl0, if_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨[], a, rfl, hS, IWGrow.refl _, ?_⟩
    simp only [decRL, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
    exact ⟨by simp [decHL, hslice?], by simp⟩
  | cons h hs ih =>
    intro o l k m a res m' hS hd hb hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    obtain ⟨hl0, hwlt, hh, hrest⟩ := decHL_cons_iw hS.2.2.2.1 hd
    subst hh
    have hw := callW_model (M := fun mm => sc0ListW p k mm nm r o l)
      (sc0List_specW p hD.lSubstConst0List k · nm r o l) hc
    unfold sc0ListW at hw
    rw [if_neg hl0] at hw
    cases h1 : callW p k "subst_const0" [nm, r, 4000000000, rdW (m.arr64 IW) o] m with
    | none => rw [h1] at hw; simp at hw
    | some q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, bW_some] at hw
    obtain ⟨x1, a1, hrun1, hS1, hg1, hl1, hx1⟩ := hs0 nm r _ hn hr hwlt k m a r1 m1 hS h1
    cases h2 : callW p k "subst_const0_list" [nm, r, o + 1, l - 1] m1 with
    | none => rw [h2] at hw; simp at hw
    | some q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2, bW_some] at hw
    have hlpos : 0 < l.toNat := Nat.pos_of_ne_zero (fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e)))
    have hsz := hS.2.2.2.1
    have hI1 := hS.2.1
    have ho1 : (o + 1).toNat = o.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hl1' : (l - 1).toNat = l.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hrest1 : decHL m1 (o + 1).toNat (l - 1).toNat = some hs := by
      rw [ho1, hl1']
      rw [ho1, hl1'] at hrest
      rw [decHL_grow hg1 (by omega)]; exact hrest
    obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := ih (o + 1) (l - 1) k m1 a1 r2 m2 hS1 hrest1
      (by rw [ho1, hl1']; have := hg1.1; omega) h2
    cases h3 : callW p k "sl_cons" [r1.headD 0, r2.headD 0, r2.tail.headD 0] m2 with
    | none => rw [h3] at hw; simp at hw
    | some q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨s', hs', -, hcons⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (slCons_specW p hD.lIwAlloc hD.lIwCopy hD.lSlCons k _ (r1.headD 0) (r2.headD 0) (r2.tail.headD 0)) h3
    have hcons' : consW k m2 (r1.headD 0) (r2.headD 0) (r2.tail.headD 0) = some (r3, m3) := by
      rw [← hs']; exact hcons
    simp only [decRL, Nat.zero_add, getD0, getD1] at hd2
    obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage hcons' hS2 hd2.2 hl1 hd2.1
    refine ⟨x1 :: x2, a2, ?_, hS3, hg1.trans (hg2.trans hg3), ?_⟩
    · simp only [substConst0List, StateT.run_bind, hrun1, exc_ok_bind', hrun2, StateT.run_pure]
      have hrun1' : (substConst0 (decI nm) (decE r) coreWalkFuel (decI (rdW (m.arr64 IW) o))).run a =
          .ok (x1, a1) := hrun1
      simp only [hrun1', exc_ok_bind', hrun2, StateT.run_pure]
      rfl
    · simp only [decRL, Nat.zero_add, getD0, getD1, List.headD_cons, List.tail_cons]
      rw [← hx1]
      exact ⟨hd3, by omega⟩

@[refines ConRon.Arena.substConst0List]
theorem substConst0List_refines (hD : DmProg5 p) (hs0 : SubstC0 p dn vis fe) (nm r o l : Word)
    (hn : H nm) (hr : H r) (hyps : List EIdx) :
    RefAM p "subst_const0_list" [nm, r, o, l]
      (fun m s => StageR dn vis fe m s ∧ decHL m o.toNat l.toNat = some hyps ∧
        o.toNat + l.toNat ≤ iwTop m)
      (substConst0List (decI nm) (decE r) hyps)
      (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) :=
  CallRef.refAM (fun k m a res m' ⟨hS, hd, hb⟩ hc =>
    sc0List_ref hD hs0 nm r hn hr hyps o l k m a res m' hS hd hb hc)

/-! ## `consts_resolve_all` -/

def craW (p : Prog) (n : Nat) (m : Mem) (vs o l : Word) : Option (List Word × Mem) :=
  if l = 0 then some ([1], m) else
  bW (stubM "consts_resolve_ffast" m [vs, rdW (m.arr64 IW) o]) fun r1 m1 =>
  if r1.headD 0 = 0 then some ([0], m1) else
  bW (callW p n "consts_resolve_all" [vs, o + 1, l - 1] m1) fun r2 m2 => some ([r2.headD 0], m2)

set_option maxHeartbeats 1600000 in
theorem cra_specW (p : Prog) (hp : p.lookup "consts_resolve_all" = some constsResolveAllL)
    (n : Nat) (s₀ : St) (vs o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "consts_resolve_all" [vs, o, l]
    ⦃fun res s' => LocEq s' s₀ ∧ craW p n s₀.mem vs o l = some (res, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, constsResolveAllL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      stubM_spec p "consts_resolve_ffast" n, callW_spec p n "consts_resolve_all"] <;>
    finish (gen := 30) (instances := 10000) [craW, bW, rdW_eq]

theorem cra_ref (hD : DmProg5 p) (vs : Word) (hvs : vs = vis) :
    ∀ (hyps : List EIdx) (o l : Word) (k : Nat) (m : Mem) (a : AState) (res : List Word) (m' : Mem),
      StageR dn vis fe m a → decHL m o.toNat l.toNat = some hyps → o.toNat + l.toNat ≤ iwTop m →
      callW p k "consts_resolve_all" [vs, o, l] m = some (res, m') →
      ∃ x a', (constsResolveAll fe hyps).run a = .ok (x, a') ∧
        KeepPost dn vis fe decW0B m m' a' res x := by
  subst hvs
  intro hyps
  induction hyps with
  | nil =>
    intro o l k m a res m' hS hd hb hc
    have hl0 : l = 0 := by
      have := decHL_length m hd
      exact UInt64.toNat_inj.mp (by simp at this ⊢; omega)
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mm => craW p k mm vs o l)
      (cra_specW p hD.lConstsResolveAll k · vs o l) hc
    simp only [craW, hl0, if_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨true, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
  | cons h hs ih =>
    intro o l k m a res m' hS hd hb hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    obtain ⟨hl0, hwlt, hh, hrest⟩ := decHL_cons_iw hS.2.2.2.1 hd
    subst hh
    have hw := callW_model (M := fun mm => craW p k mm vs o l)
      (cra_specW p hD.lConstsResolveAll k · vs o l) hc
    unfold craW at hw
    rw [if_neg hl0] at hw
    cases h1 : stubM "consts_resolve_ffast" m [vs, rdW (m.arr64 IW) o] with
    | none => rw [h1] at hw; simp at hw
    | some q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, bW_some] at hw
    obtain ⟨x1, a1, hrun1, hS1, hg1, hd1⟩ :=
      constsResolveFFast_spec dn vs fe _ hwlt m m1 a r1 h1 hS
    by_cases hz : r1.headD 0 = 0
    · rw [if_pos hz] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx1 : x1 = false := by
        have := hd1.1; rw [hz] at this; simpa using this.symm
      refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
      simp only [constsResolveAll, StateT.run_bind, hrun1, exc_ok_bind', hx1, Bool.false_eq_true,
        if_false, StateT.run_pure]
      rfl
    · rw [if_neg hz] at hw
      have hx1 : x1 = true := by
        have := hd1.1
        have e : (r1.headD 0 != 0) = true := by simpa using hz
        rw [e] at this; exact this.symm
      cases h2 : callW p k "consts_resolve_all" [vs, o + 1, l - 1] m1 with
      | none => rw [h2] at hw; simp at hw
      | some q2 =>
      obtain ⟨r2, m2⟩ := q2
      rw [h2, bW_some] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hsz := hS.2.2.2.1
      have hI1 := hS.2.1
      have hlpos : 0 < l.toNat := Nat.pos_of_ne_zero (fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e)))
      have ho1 : (o + 1).toNat = o.toNat + 1 := by
        have hb := decHL_bnd m o l hd hsz
        rw [UInt64.toNat_add]; simp; omega
      have hl1' : (l - 1).toNat = l.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
      have hrest1 : decHL m1 (o + 1).toNat (l - 1).toNat = some hs := by
        rw [ho1, hl1']
        rw [ho1, hl1'] at hrest
        rw [decHL_grow hg1 (by omega)]; exact hrest
      obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := ih (o + 1) (l - 1) k m1 a1 r2 m2 hS1 hrest1
        (by rw [ho1, hl1']; have := hg1.1; omega) h2
      refine ⟨x2, a2, ?_, hS2, hg1.trans hg2, hd2⟩
      simp only [constsResolveAll, StateT.run_bind, hrun1, exc_ok_bind', hx1, if_true]
      exact hrun2

@[refines ConRon.Arena.constsResolveAll]
theorem constsResolveAll_refines (hD : DmProg5 p) (o l : Word) (hyps : List EIdx) :
    RefAM p "consts_resolve_all" [vis, o, l]
      (fun m s => StageR dn vis fe m s ∧ decHL m o.toNat l.toNat = some hyps ∧
        o.toNat + l.toNat ≤ iwTop m)
      (constsResolveAll fe hyps) (KeepPost dn vis fe decW0B) :=
  CallRef.refAM (fun k m a res m' ⟨hS, hd, hb⟩ hc =>
    cra_ref hD vis rfl hyps o l k m a res m' hS hd hb hc)

/-! ## `div_mod_cert_guard` -/

def cgW (p : Prog) (n : Nat) (m : Mem) (vs c annVal ho hl eqE proof : Word) :
    Option (List Word × Mem) :=
  bW (callW p n "subst_const_all" [c, annVal, 4000000000, proof] m) fun r1 m1 =>
  bW (stubM "loose_bvars_bounded_fast" m1 [4000000000, 0, r1.headD 0]) fun r2 m2 =>
  if r2.headD 0 = 0 then some ([0], m2) else
  bW (stubM "has_fvar_fast" m2 [4000000000, r1.headD 0]) fun r3 m3 =>
  if r3.headD 0 ≠ 0 then some ([0], m3) else
  bW (stubM "all_level_params_defined" m3 [0, 0, r1.headD 0]) fun r4 m4 =>
  if r4.headD 0 = 0 then some ([0], m4) else
  bW (stubM "consts_resolve_ffast" m4 [vs, r1.headD 0]) fun r5 m5 =>
  if r5.headD 0 = 0 then some ([0], m5) else
  bW (callW p n "subst_const0_list" [c, annVal, ho, hl] m5) fun r6 m6 =>
  bW (callW p n "consts_resolve_all" [vs, r6.headD 0, r6.tail.headD 0] m6) fun r7 m7 =>
  if r7.headD 0 = 0 then some ([0], m7) else
  bW (callW p n "subst_const0" [c, annVal, 4000000000, eqE] m7) fun r8 m8 =>
  bW (stubM "consts_resolve_ffast" m8 [vs, r8.headD 0]) fun r9 m9 => some ([r9.headD 0], m9)

set_option maxHeartbeats 3200000 in
theorem cg_specW (p : Prog) (hp : p.lookup "div_mod_cert_guard" = some divModCertGuardL)
    (n : Nat) (s₀ : St) (vs c annVal ho hl eqE proof : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "div_mod_cert_guard" [vs, c, annVal, ho, hl, eqE, proof]
    ⦃fun res s' => LocEq s' s₀ ∧ cgW p n s₀.mem vs c annVal ho hl eqE proof = some (res, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divModCertGuardL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      stubM_spec p "loose_bvars_bounded_fast" n, stubM_spec p "has_fvar_fast" n,
      stubM_spec p "all_level_params_defined" n, stubM_spec p "consts_resolve_ffast" n,
      callW_spec p n "subst_const_all", callW_spec p n "subst_const0_list",
      callW_spec p n "consts_resolve_all", callW_spec p n "subst_const0"] <;>
    finish (gen := 30) (instances := 10000) [cgW, bW]

theorem decW0B_false {m : Mem} {r : List Word} {b : Bool} (h : decW0B m r b) (hz : r.headD 0 = 0) :
    b = false := by
  have := h.1; rw [hz] at this; simpa using this.symm

theorem decW0B_true {m : Mem} {r : List Word} {b : Bool} (h : decW0B m r b) (hz : ¬ r.headD 0 = 0) :
    b = true := by
  have := h.1
  have e : (r.headD 0 != 0) = true := by simpa using hz
  rw [e] at this; exact this.symm

theorem decW0B_of_false (m : Mem) : decW0B m [0] false := by simp [decW0B]

theorem fuelW_eq : (4000000000 : Word).toNat = coreWalkFuel := rfl

set_option maxHeartbeats 3200000 in
theorem cg_ref (hD : DmProg5 p) (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe)
    (c annVal ho hl eqE proof : Word) (hyps : List EIdx) :
    CallRef p "div_mod_cert_guard" [vis, c, annVal, ho, hl, eqE, proof]
      (fun m s => StageR dn vis fe m s ∧ H c ∧ H annVal ∧ H eqE ∧ H proof ∧
        decHL m ho.toNat hl.toNat = some hyps ∧ ho.toNat + hl.toNat ≤ iwTop m)
      (divModCertGuard fe (decI c) (decE annVal) hyps (decE eqE) (decE proof))
      (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hc, hann, heq, hpr, hd, hb⟩ hcall => ?_
  have hw := callW_model (M := fun mq => cgW p k mq vis c annVal ho hl eqE proof)
    (cg_specW p hD.lDivModCertGuard k · vis c annVal ho hl eqE proof) hcall
  unfold cgW at hw
  have h0w : (0 : Word).toNat = 0 := rfl
  -- subst_const_all
  cases h1 : callW p k "subst_const_all" [c, annVal, 4000000000, proof] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨x1, a1, hrun1, hS1, hg1, hl1, hx1⟩ := hsA c annVal proof hc hann hpr k m s r1 m1 hS h1
  -- loose bvars
  cases h2 : stubM "loose_bvars_bounded_fast" m1 [4000000000, 0, r1.headD 0] with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ :=
    looseBVarsBoundedFast_spec dn vis fe 4000000000 0 (r1.headD 0) hl1 m1 m2 a1 r2 h2 hS1
  rw [fuelW_eq, h0w, hx1] at hrun2
  by_cases z2 : r2.headD 0 = 0
  · rw [if_pos z2] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx2 := decW0B_false hd2 z2
    refine ⟨false, a2, ?_, hS2, hg1.trans hg2, decW0B_of_false _⟩
    simp only [divModCertGuard, StateT.run_bind, Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self, if_true, if_false, hrun1, exc_ok_bind', hrun2, hx2]
    rfl
  rw [if_neg z2] at hw
  have hx2 := decW0B_true hd2 z2
  -- has fvar
  cases h3 : stubM "has_fvar_fast" m2 [4000000000, r1.headD 0] with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := hasFvarFast_spec dn vis fe 4000000000 (r1.headD 0) hl1 m2 m3 a2 r3 h3 hS2
  rw [fuelW_eq, hx1] at hrun3
  by_cases z3 : r3.headD 0 ≠ 0
  · rw [if_pos z3] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx3 := decW0B_true hd3 z3
    refine ⟨false, a3, ?_, hS3, hg1.trans (hg2.trans hg3), decW0B_of_false _⟩
    simp only [divModCertGuard, StateT.run_bind, Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self, if_true, if_false, hrun1, exc_ok_bind', hrun2, hx2, hrun3, hx3]
    rfl
  rw [if_neg z3] at hw
  have z3' : r3.headD 0 = 0 := by simpa using z3
  have hx3 := decW0B_false hd3 z3'
  -- all level params
  cases h4 : stubM "all_level_params_defined" m3 [0, 0, r1.headD 0] with
  | none => rw [h4] at hw; simp at hw
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, bW_some] at hw
  obtain ⟨x4, a4, hrun4, hS4, hg4, hd4⟩ := allLevelParamsDefined_spec dn vis fe 0 0 (r1.headD 0) hl1 []
    m3 m4 a3 r4 h4 ⟨hS3, by rw [h0w]; simp [decHL, hslice?]⟩
  rw [hx1] at hrun4
  by_cases z4 : r4.headD 0 = 0
  · rw [if_pos z4] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx4 := decW0B_false hd4 z4
    refine ⟨false, a4, ?_, hS4, hg1.trans (hg2.trans (hg3.trans hg4)), decW0B_of_false _⟩
    simp only [divModCertGuard, StateT.run_bind, Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self, if_true, if_false, hrun1, exc_ok_bind', hrun2, hx2, hrun3, hx3, hrun4,
      hx4]
    rfl
  rw [if_neg z4] at hw
  have hx4 := decW0B_true hd4 z4
  -- consts resolve of the proof
  cases h5 : stubM "consts_resolve_ffast" m4 [vis, r1.headD 0] with
  | none => rw [h5] at hw; simp at hw
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, bW_some] at hw
  obtain ⟨x5, a5, hrun5, hS5, hg5, hd5⟩ := constsResolveFFast_spec dn vis fe (r1.headD 0) hl1 m4 m5 a4 r5 h5 hS4
  rw [hx1] at hrun5
  have hG5 : IWGrow m m5 := hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5)))
  by_cases z5 : r5.headD 0 = 0
  · rw [if_pos z5] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx5 := decW0B_false hd5 z5
    refine ⟨false, a5, ?_, hS5, hG5, decW0B_of_false _⟩
    simp only [divModCertGuard, StateT.run_bind, Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self, if_true, if_false, hrun1, exc_ok_bind', hrun2, hx2, hrun3, hx3, hrun4,
      hx4, hrun5, hx5]
    rfl
  rw [if_neg z5] at hw
  have hx5 := decW0B_true hd5 z5
  -- the hypotheses, substituted
  cases h6 : callW p k "subst_const0_list" [c, annVal, ho, hl] m5 with
  | none => rw [h6] at hw; simp at hw
  | some q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [h6, bW_some] at hw
  have hd5' : decHL m5 ho.toNat hl.toNat = some hyps := by
    rw [decHL_grow hG5 hb]; exact hd
  have hb5 : ho.toNat + hl.toNat ≤ iwTop m5 := Nat.le_trans hb hG5.1
  obtain ⟨x6, a6, hrun6, hS6, hg6, hd6⟩ := sc0List_ref hD hs0 c annVal hc hann hyps ho hl k m5 a5 r6 m6 hS5 hd5' hb5 h6
  simp only [decRL, Nat.zero_add, getD0, getD1] at hd6
  -- consts resolve of the hypotheses
  cases h7 : callW p k "consts_resolve_all" [vis, r6.headD 0, r6.tail.headD 0] m6 with
  | none => rw [h7] at hw; simp at hw
  | some q7 =>
  obtain ⟨r7, m7⟩ := q7
  rw [h7, bW_some] at hw
  obtain ⟨x7, a7, hrun7, hS7, hg7, hd7⟩ := cra_ref hD vis rfl x6 (r6.headD 0) (r6.tail.headD 0) k m6 a6 r7 m7 hS6
    hd6.1 hd6.2 h7
  have hG7 : IWGrow m m7 := hG5.trans (hg6.trans hg7)
  by_cases z7 : r7.headD 0 = 0
  · rw [if_pos z7] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx7 := decW0B_false hd7 z7
    refine ⟨false, a7, ?_, hS7, hG7, decW0B_of_false _⟩
    simp only [divModCertGuard, StateT.run_bind, Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self, if_true, if_false, hrun1, exc_ok_bind', hrun2, hx2, hrun3, hx3, hrun4,
      hx4, hrun5, hx5, hrun6, hrun7, hx7]
    rfl
  rw [if_neg z7] at hw
  have hx7 := decW0B_true hd7 z7
  -- the equation, substituted
  cases h8 : callW p k "subst_const0" [c, annVal, 4000000000, eqE] m7 with
  | none => rw [h8] at hw; simp at hw
  | some q8 =>
  obtain ⟨r8, m8⟩ := q8
  rw [h8, bW_some] at hw
  obtain ⟨x8, a8, hrun8, hS8, hg8, hl8, hx8⟩ := hs0 c annVal eqE hc hann heq k m7 a7 r8 m8 hS7 h8
  cases h9 : stubM "consts_resolve_ffast" m8 [vis, r8.headD 0] with
  | none => rw [h9] at hw; simp at hw
  | some q9 =>
  obtain ⟨r9, m9⟩ := q9
  rw [h9, bW_some] at hw
  obtain ⟨x9, a9, hrun9, hS9, hg9, hd9⟩ := constsResolveFFast_spec dn vis fe (r8.headD 0) hl8 m8 m9 a8 r9 h9 hS8
  rw [hx8] at hrun9
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨x9, a9, ?_, hS9, hG7.trans (hg8.trans hg9), hd9⟩
  simp only [divModCertGuard, StateT.run_bind, Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self, if_true, if_false, hrun1, exc_ok_bind', hrun2, hx2, hrun3, hx3, hrun4,
    hx4, hrun5, hx5, hrun6, hrun7, hx7, hrun8, hrun9]

@[refines ConRon.Arena.divModCertGuard]
theorem divModCertGuard_refines (hD : DmProg5 p) (hs0 : SubstC0 p dn vis fe)
    (hsA : SubstCAll p dn vis fe) (c annVal ho hl eqE proof : Word) (hyps : List EIdx) :
    RefAM p "div_mod_cert_guard" [vis, c, annVal, ho, hl, eqE, proof]
      (fun m s => StageR dn vis fe m s ∧ H c ∧ H annVal ∧ H eqE ∧ H proof ∧
        decHL m ho.toNat hl.toNat = some hyps ∧ ho.toNat + hl.toNat ≤ iwTop m)
      (divModCertGuard fe (decI c) (decE annVal) hyps (decE eqE) (decE proof))
      (KeepPost dn vis fe decW0B) :=
  (cg_ref hD hs0 hsA c annVal ho hl eqE proof hyps).refAM

end applied

end L.Ind
