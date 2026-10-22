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
  lConstsResolveFFast : p.lookup "consts_resolve_ffast" = some (stub 2)
  lDivModCertGuard : p.lookup "div_mod_cert_guard" = some divModCertGuardL
  lLooseBvars : p.lookup "loose_bvars_bounded_fast" = some (stub 3)
  lHasFvar : p.lookup "has_fvar_fast" = some (stub 2)
  lAllLevelParams : p.lookup "all_level_params_defined" = some (stub 3)

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

end applied

end L.Ind
