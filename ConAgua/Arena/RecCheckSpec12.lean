import ConAgua.Arena.RecCheckSpec11
import ConAgua.Arena.IndInstallSpec6


noncomputable section

/-!
# `RecCheck`: `targetClassMatch` (lane `indproofs3`, helper `rec`)

Levels by `lvls_eq_c` (the cached `lvlsEq?`; a master callee without a stage-level model, entered
through the stub contract `lvlsEqStub_spec` below, as `lvl_eq_c` is through `lvlEqStub_spec`), then
`block_shape_member_names`, `block_shape_lps` (L: called instead of the inlined copy of member 0's
level parameters, which it is), `param_levels`, `target_holes` and `target_params_def_eq`
(`RecCheckSpec11`). L: the depth `pfl + ftl` aborts on a wrap before `target_holes` (a capacity
abort; the twin's `Nat` sum cannot wrap). Write sets of the callees (`MFr`), so the walk memos
(`RcMR`) are carried.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The `lvls_eq_c` contract -/

/-- `lvls_eq_c(us, vs)`: `lvlsEq?` on two level-list handles, through the verdict cache as the twin
(lane `whnf`'s `lvls_eq_c`, `CoreLevels.lean`). **Stub contract** (`sorry`, like `IndStubs`'
`lvlEqStub_spec` for `lvl_eq_c`): lane `whnf`'s refinement holds under `CoreS`, whose twin-side
invariants (`TwinOK`, `DeclLvlStage.lean`) the stage relation does not carry; to be replaced by a
`lvlsEqC_stage` bridge once the stage relation carries `TwinOK` (lane `indproofs3`'s `StageT`). -/
theorem lvlsEqStub_spec (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (u v : Word)
    (hu : H u) (hv : H v) :
    RelAM "lvls_eq_c" [u, v] (StageR dn vis fe) (lvlsEq? (decI u) (decI v))
      (KeepPost dn vis fe decLvlEq) := sorry

/-! ## Write sets -/

theorem pinternW_mfr {m m' : Mem} {u r : Word} (h : pinternW m u = some (r, m')) : MFr [] [] m m' := by
  have h₂ := h; rw [pinternW_eq] at h₂
  exact MFr.of_low ⟨_, _, internM_frame _ paramSch_wf _ _ _ _ _ _ _ _ h₂, by simp [paramSch, PREC, PSLOT],
    by simp [paramSch]⟩

theorem plgW_mfr : ∀ (k : Nat) {m m' : Mem} {o l : Word} {r : List Word}, plgW k m o l = some (r, m') →
    MFr [] [] m m'
  | 0, _, _, _, _, _, h => by simp [plgW] at h
  | k + 1, m, m', o, l, r, h => by
    by_cases hl : l = 0
    · rw [plgW_nil (hl := hl)] at h
      cases ha : allocW m 0 with
      | none => rw [ha] at h; cases h
      | some x =>
        obtain ⟨q, m1⟩ := x
        rw [ha, plK0_some] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
        exact allocW_mfr ha
    rw [plgW_cons (hl := hl)] at h
    cases hp : pinternW m (rdW (m.arr64 IW) o) with
    | none => rw [hp] at h; simp [plK1] at h
    | some x =>
    obtain ⟨u, m1⟩ := x
    rw [hp] at h
    by_cases hb : 4294967296 ≤ u
    · rw [plK1_big (h := hb)] at h; cases h
    rw [plK1_ok (h := hb)] at h
    cases hg : plgW k m1 (o + 1) (l - 1) with
    | none => rw [hg] at h; simp [plK2] at h
    | some y =>
    obtain ⟨r2, m2⟩ := y
    rw [hg, plK2_some] at h
    cases hc : consW k m2 u (r2.headD 0) (r2.tail.headD 0) with
    | none => rw [hc] at h; simp [plK3] at h
    | some z =>
    obtain ⟨r3, m3⟩ := z
    rw [hc, plK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact ((pinternW_mfr hp).trans (plgW_mfr k hg)).trans (consW_mfr hc)

theorem plW_mfr {k : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : plW k m o l = some (r, m')) :
    MFr [] [] m m' := by
  cases k with
  | zero => simp [plW] at h
  | succ k =>
  rw [plW_succ] at h
  cases hg : plgW k m o l with
  | none => rw [hg] at h; cases h
  | some x =>
  obtain ⟨r1, m1⟩ := x
  rw [hg, plK4_some] at h
  cases hs : ilF m1 [r1.headD 0, r1.tail.headD 0] with
  | none => rw [hs] at h; cases h
  | some y =>
  obtain ⟨r2, m2⟩ := y
  rw [hs, plK5_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (plgW_mfr k hg).trans (MFr.of_frame (ilF_frame hs) (by simp [POOL, LSREC, LSSLOT, LSHP]) (by simp))

theorem thW_mfr : ∀ (n : Nat) {m m' : Mem} {tyo tyl base : Word} {r : List Word},
    thW n m tyo tyl base = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [thW] at h
  | n + 1, m, m', tyo, tyl, base, r, h => by
    by_cases hl : tyl = 0
    · rw [thW_nil (h := hl)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      exact MFr.refl _ _ _
    rw [thW_cons (h := hl)] at h
    cases hf : fvinternW m base (rdW (m.arr64 IW) tyo) with
    | none => rw [hf] at h; simp [thK1] at h
    | some x =>
    obtain ⟨v, m1⟩ := x
    rw [hf] at h
    by_cases hb : 4294967296 ≤ v
    · rw [thK1_big (h := hb)] at h; cases h
    rw [thK1_ok (h := hb)] at h
    cases hg : thW n m1 (tyo + 1) (tyl - 1) (base + 1) with
    | none => rw [hg] at h; simp [thK2] at h
    | some y =>
    obtain ⟨r2, m2⟩ := y
    rw [hg, thK2_some] at h
    cases hc : consW n m2 v (r2.headD 0) (r2.tail.headD 0) with
    | none => rw [hc] at h; simp [thK3] at h
    | some z =>
    obtain ⟨r3, m3⟩ := z
    rw [hc, thK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact ((fvinternW_mfr hf).trans (thW_mfr n hg)).trans (consW_mfr hc)

theorem lpsW_mfr {n : Nat} {m m' : Mem} {q : Word} {r : List Word} (h : lpsW n m q = some (r, m')) :
    MFr [] [] m m' := by
  cases n with
  | zero => simp [lpsW] at h
  | succ n =>
    simp only [lpsW] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact MFr.refl _ _ _
    · exact erToIwW_mfr h

/-! ## `target_class_match`: the word model -/

def tcmK6 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

def tcmK5 (cR : CallM) (n : Nat) (vis pfo pfl dso dsl edso edsl d : Word) (rn rb : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rh, m) => tcmK6 (pdeW cR n m vis d (rn.headD 0) (rn.tail.headD 0) (rb.headD 0) (rh.headD 0)
      (rh.tail.headD 0) pfo pfl dso dsl edso edsl)

def tcmK4 (cR : CallM) (n : Nat) (vis fto ftl pfo pfl dso dsl edso edsl : Word) (rn : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m) =>
    if pfl + ftl < pfl then none
    else tcmK5 cR n vis pfo pfl dso dsl edso edsl (pfl + ftl) rn rb (thW n m fto ftl pfl)

def tcmK3 (cR : CallM) (n : Nat) (vis fto ftl pfo pfl dso dsl edso edsl : Word) (rn : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rl, m) => tcmK4 cR n vis fto ftl pfo pfl dso dsl edso edsl rn (plW n m (rl.headD 0) (rl.tail.headD 0))

def tcmK2 (cR : CallM) (n : Nat) (vis p fto ftl pfo pfl dso dsl edso edsl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rn, m) => tcmK3 cR n vis fto ftl pfo pfl dso dsl edso edsl rn (lpsW n m p)

def tcmK1 (cR : CallM) (n : Nat) (vis p fto ftl pfo pfl dso dsl edso edsl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 2 then some ([0], m)
    else tcmK2 cR n vis p fto ftl pfo pfl dso dsl edso edsl (memberNamesW n m p)

/-- **The model of `target_class_match`** (body fuel `n`). -/
def tcmW (cR : CallM) (n : Nat) (m : Mem) (vis p fto ftl pfo pfl us dso dsl lvls edso edsl : Word) :
    Option (List Word × Mem) :=
  tcmK1 cR n vis p fto ftl pfo pfl dso dsl edso edsl (cR n "lvls_eq_c" [us, lvls] m)

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis p fto ftl pfo pfl dso dsl edso edsl d : Word) (r rn rb rh rl : List Word)
theorem tcmK6_some : tcmK6 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem tcmK5_some : tcmK5 cR n vis pfo pfl dso dsl edso edsl d rn rb (some (rh, m)) =
    tcmK6 (pdeW cR n m vis d (rn.headD 0) (rn.tail.headD 0) (rb.headD 0) (rh.headD 0) (rh.tail.headD 0) pfo pfl
      dso dsl edso edsl) := rfl
theorem tcmK4_wrap (h : pfl + ftl < pfl) : tcmK4 cR n vis fto ftl pfo pfl dso dsl edso edsl rn (some (rb, m)) =
    none := by simp only [tcmK4]; rw [if_pos h]
theorem tcmK4_ok (h : ¬ pfl + ftl < pfl) : tcmK4 cR n vis fto ftl pfo pfl dso dsl edso edsl rn (some (rb, m)) =
    tcmK5 cR n vis pfo pfl dso dsl edso edsl (pfl + ftl) rn rb (thW n m fto ftl pfl) := by
  simp only [tcmK4]; rw [if_neg h]
theorem tcmK3_some : tcmK3 cR n vis fto ftl pfo pfl dso dsl edso edsl rn (some (rl, m)) =
    tcmK4 cR n vis fto ftl pfo pfl dso dsl edso edsl rn (plW n m (rl.headD 0) (rl.tail.headD 0)) := rfl
theorem tcmK2_some : tcmK2 cR n vis p fto ftl pfo pfl dso dsl edso edsl (some (rn, m)) =
    tcmK3 cR n vis fto ftl pfo pfl dso dsl edso edsl rn (lpsW n m p) := rfl
theorem tcmK1_no (h : r.headD 0 ≠ 2) : tcmK1 cR n vis p fto ftl pfo pfl dso dsl edso edsl (some (r, m)) =
    some ([0], m) := by simp only [tcmK1]; rw [if_pos h]
theorem tcmK1_yes (h : ¬ r.headD 0 ≠ 2) : tcmK1 cR n vis p fto ftl pfo pfl dso dsl edso edsl (some (r, m)) =
    tcmK2 cR n vis p fto ftl pfo pfl dso dsl edso edsl (memberNamesW n m p) := by
  simp only [tcmK1]; rw [if_neg h]
end arms
attribute [ind_grind] tcmK6_some tcmK5_some tcmK4_wrap tcmK4_ok tcmK3_some tcmK2_some tcmK1_no tcmK1_yes

/-- The lookups of `target_class_match`. -/
structure TcmLook (p : Prog) : Prop where
  tp : TpLook p
  ha : p.lookup "iw_alloc" = some iwAlloc
  mnc : p.lookup "member_names_copy" = some memberNamesCopy
  mn : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  erc : p.lookup "er_copy" = some erCopy
  eri : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  ic : p.lookup "iw_copy" = some iwCopy
  sc : p.lookup "sl_cons" = some slCons
  sg : p.lookup "sl_get" = some slGet
  pf : p.lookup "param_find" = some paramFind
  pp : p.lookup "param_push" = some paramPush
  ip : p.lookup "intern_param" = some internParam
  plg : p.lookup "param_levels_go" = some paramLevelsGoL
  pl : p.lookup "param_levels" = some paramLevelsL
  il : IlF p
  ff : p.lookup "fvar_find" = some fvarFind
  fp : p.lookup "fvar_push" = some fvarPush
  iff : p.lookup "intern_fvar" = some internFVar
  th : p.lookup "target_holes" = some targetHoles
  tcm : p.lookup "target_class_match" = some targetClassMatch

theorem targetClassMatch_spec (p : Prog) (L : TcmLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St)
    (vis q fto ftl pfo pfl us dso dsl lvls edso edsl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_class_match"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, lvls, edso, edsl]
    ⦃fun r s' => LocEq s' s₀ ∧
      tcmW cR n s₀.mem vis q fto ftl pfo pfl us dso dsl lvls edso edsl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.tcm]
  simp only [callFn, targetClassMatch]
  sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      hcR n "lvls_eq_c", blockShapeMemberNames_spec p L.ha L.mnc L.mn n,
      blockShapeLps_spec p L.ha L.erc L.eri L.lps n,
      plW_spec p L.ha L.ic L.sc L.sg L.pf L.pp L.ip L.plg L.pl L.il n,
      targetHoles_spec p L.ff L.fp L.iff L.ic L.ha L.sc L.th n, tpd_spec p L.tp cR hcR n] <;>
    finish (gen := 40) (instances := 20000) [tcmW, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8,
      loc_init9, loc_init10, loc_init11]

/-! ## The relational side -/

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem word_add_nowrap {a b : Word} (h : ¬ a + b < a) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
  have := a.toNat_lt; have := b.toNat_lt
  rw [UInt64.toNat_add]
  by_cases hw : a.toNat + b.toNat < 2 ^ 64
  · exact Nat.mod_eq_of_lt hw
  · exfalso; apply h; rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem tcmW_ok (n : Nat) {m m' : Mem} {a : AState} {q fto ftl pfo pfl us dso dsl lvls edso edsl : Word}
    {r : List Word} {bs : BlockShape} {formerTys pfvs ds eds : List EIdx}
    (h : tcmW stubCall n m vis q fto ftl pfo pfl us dso dsl lvls edso edsl = some (r, m'))
    (hS : StageR dn vis fe m a) (hbs : BSOK m q.toNat bs) (hus : H us) (hlv : H lvls)
    (hft : decHL m fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop m)
    (hpf : HSl0 m pfo pfl pfvs) (hds : HSl0 m dso dsl ds) (heds : HSl0 m edso edsl eds) (hP : RcMR m) :
    ∃ c a', (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds).run a =
      .ok (c, a') ∧ (r.headD 0 != 0) = c ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  unfold tcmW at h
  cases h1 : stubCall n "lvls_eq_c" [us, lvls] m with
  | none => rw [h1] at h; simp [tcmK1] at h
  | some x =>
  obtain ⟨r1, m1⟩ := x
  rw [h1] at h
  replace h1 : stubM "lvls_eq_c" m [us, lvls] = some (r1, m1) := h1
  obtain ⟨o1, a1, run1, hS1, hg1, hd1⟩ := lvlsEqStub_spec dn vis fe us lvls hus hlv m m1 a r1 h1 hS
  have hP1 := hP.stub (by decide) h1
  by_cases hne : r1.headD 0 ≠ 2
  · rw [tcmK1_no (h := hne)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨false, a1, ?_, rfl, hS1, hg1, hP1⟩
    simp only [ConRon.Arena.targetClassMatch, StateT.run_bind, run1, except_ok_bind]
    simp only [decLvlEq] at hd1
    rcases o1 with _ | _ | _
    · rfl
    · rfl
    · exact absurd hd1 hne
  rw [tcmK1_yes (h := hne)] at h
  have ho1 : o1 = some true := by
    simp only [decLvlEq] at hd1
    rcases o1 with _ | _ | _
    · exfalso; apply hne; simp only at hd1; rw [hd1]; decide
    · exfalso; apply hne; simp only at hd1; rw [hd1]; decide
    · rfl
  subst ho1
  have hsz := hS1.2.2.2.1
  have hbs1 := hbs.grow hg1
  cases h2 : memberNamesW n m1 q with
  | none => rw [h2] at h; simp [tcmK2] at h
  | some x =>
  obtain ⟨rn, m2⟩ := x
  rw [h2, tcmK2_some] at h
  obtain ⟨hS2, hg2, -, hdn, htn⟩ := memberNamesW_stage h2 hS1 hbs1
  have hf2 := (memberNamesW_dec h2 hsz hS1.2.2.2.2.2 hbs1.dec (by have := hbs1.ptop; have := hS1.lt64 (Nat.le_refl _); omega)
    hbs1.2.1 hbs1.2.2).2.2.2.1
  have hP2 := hP1.fr (MFr.of_iw hf2)
  cases h3 : lpsW n m2 q with
  | none => rw [h3] at h; simp [tcmK3] at h
  | some x =>
  obtain ⟨rl, m3⟩ := x
  rw [h3, tcmK3_some] at h
  obtain ⟨hS3, hg3, hdl, hbl⟩ := lpsW_ok' h3 hS2 ((hbs1.1.grow (decBS_mono _) hg2))
  have hP3 := hP2.fr (lpsW_mfr h3)
  cases h4 : plW n m3 (rl.headD 0) (rl.tail.headD 0) with
  | none => rw [h4] at h; simp [tcmK4] at h
  | some x =>
  obtain ⟨rb, m4⟩ := x
  rw [h4] at h
  obtain ⟨blv, a4, run4, hS4, hg4, hH4, hdb⟩ := plW_ok dn vis fe n m3 m4 a1 _ _ bs.lps rb h4 hS3 hdl
    (hS3.lt64 hbl) hbl
  have hP4 := hP3.fr (plW_mfr h4)
  by_cases hw : pfl + ftl < pfl
  · rw [tcmK4_wrap (h := hw)] at h; cases h
  rw [tcmK4_ok (h := hw)] at h
  have hd : (pfl + ftl).toNat = pfl.toNat + ftl.toNat := word_add_nowrap hw
  have hg14 := (hg2.trans hg3).trans hg4
  have hg04 := hg1.trans hg14
  cases h5 : thW n m4 fto ftl pfl with
  | none => rw [h5] at h; simp [tcmK5] at h
  | some x =>
  obtain ⟨rh, m5⟩ := x
  rw [h5, tcmK5_some] at h
  obtain ⟨holes, a5, run5, hS5, hg5, hdh, hbh⟩ := thW_ok dn vis fe n m4 m5 a4 fto ftl pfl rh formerTys h5 hS4
    (by rw [decHL_grow hg04 hftb]; exact hft) (hS.lt64 hftb) (by have := hg04.1; omega)
    (by rw [← hd]; exact (pfl + ftl).toNat_lt)
  have hP5 := hP4.fr (thW_mfr n h5)
  have hg05 := hg04.trans hg5
  cases h6 : pdeW stubCall n m5 vis (pfl + ftl) (rn.headD 0) (rn.tail.headD 0) (rb.headD 0) (rh.headD 0)
      (rh.tail.headD 0) pfo pfl dso dsl edso edsl with
  | none => rw [h6] at h; simp [tcmK6] at h
  | some x =>
  obtain ⟨r6, m6⟩ := x
  rw [h6, tcmK6_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hg25 := (hg3.trans hg4).trans hg5
  obtain ⟨c, a6, run6, hc, hS6, hg6, hP6⟩ := pdeW_ok dn fe vis n h6 hS5 hH4
    (by rw [decHL_grow hg25 (by omega)]; exact hdn) (by have := hg25.1; omega) hdh hbh
    (hpf.grow hg05) (hds.grow hg05) (heds.grow hg05) hP5
  refine ⟨c, a6, ?_, by simpa using hc, hS6, hg05.trans hg6, hP6⟩
  have hlen : pfvs.length = pfl.toNat := hpf.len
  have hlenf : formerTys.length = ftl.toNat := decHL_length _ hft
  rw [hd, ← hlen, ← hlenf, hdb] at run6
  rw [← hlen] at run5
  simp only [ConRon.Arena.targetClassMatch, StateT.run_bind, run1, except_ok_bind, run4, run5]
  exact run6

end rel

/-- **`target_class_match` refines `targetClassMatch`** (through `lvls_eq_c`'s stub contract and the
stubs under `target_params_def_eq`): the shape record as `BSOK` (decoded below the tops, its member
slice and records below the top), the former types decoded below the top, the other three slices decoded (below the top
unless empty), the walk memos well
formed; the verdict as `r[0] ≠ 0`. Under `StageR`; the census link is `targetClassMatch_refinesC`
(`IndT/RecCheckTcm`). -/
theorem targetClassMatch_refines (p : Prog) (L : TcmLook p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl pfo pfl us dso dsl lvls edso edsl : Word)
    (bs : BlockShape) (formerTys pfvs ds eds : List EIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hbs : BSOK s₀.mem q.toNat bs) (hus : H us) (hlv : H lvls)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (hds : HSl0 s₀.mem dso dsl ds) (heds : HSl0 s₀.mem edso edsl eds)
    (hP : RcMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_class_match"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, lvls, edso, edsl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds) a₀ ∧
      (r.headD 0 != 0) = AM.res (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  refine triple_post (targetClassMatch_spec p L stubCall (stubCall_spec p) n s₀ vis q fto ftl pfo pfl us dso dsl lvls edso edsl) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨c, a', run, hc, hS', hg, hP'⟩ := tcmW_ok dn fe vis n hm hS hbs hus hlv hft hftb hpf hds heds hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres]; exact hc, by rw [hst]; exact hS', hg, hP'⟩

end L.Ind
