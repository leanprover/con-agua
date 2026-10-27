import ConAgua.Arena.IndSumSpec.ColW
import ConAgua.Arena.RecCheckSpec.TaGoWMfr
import ConAgua.Arena.RecCheckSpec.TcmK6

/-!
# TcmLook

`pinternW_mfr`, `plgW_mfr`, `plW_mfr`, `thW_mfr`, `lpsW_mfr`, `tcmK5` and the lemmas only they use.
-/

noncomputable section

/-!
# `RecCheck`: `targetClassMatch` (lane `indproofs3`, helper `rec`)

Levels by `lvls_eq_c` (the cached `lvlsEq?`; a master callee without a stage-level model, entered
through the stub contract `lvlsEqStub_spec` below, as `lvl_eq_c` is through `lvlEqStub_spec`), then
`block_shape_member_names`, `block_shape_lps` (L: called instead of the inlined copy of member 0's
level parameters, which it is), `param_levels`, `target_holes` and `target_params_def_eq`
(`RecCheckSpec/PdsC`). L: the depth `pfl + ftl` aborts on a wrap before `target_holes` (a capacity
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

/-! ## Write sets -/

theorem pinternW_mfr {m m' : Mem} {u r : Word} (h : pinternW m u = some (r, m')) : MFr [] [] m m' := by
  have h₂ := h
  exact MFr.of_low ⟨_, _, consInternM_frame paramCS_wf h₂, by simp [ConsSch.wset, paramCS, PREC, PSLOT],
    by simp [paramCS]⟩

theorem plgW_mfr : ∀ (k : Nat) {m m' : Mem} {o l : Word} {r : List Word}, plgW k m o l = some (r, m') →
    MFr [] [] m m'
  | 0, _, _, _, _, _, h => by simp [plgW] at h
  | k + 1, m, m', o, l, r, h => by
    by_cases hl : l = 0
    · rw [plgW_nil (hl := hl)] at h
      rcases ha : allocW m 0 with _ | ⟨q, m1⟩ <;> simp only [ha, plK0, reduceCtorEq] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      exact allocW_mfr ha
    rw [plgW_cons (hl := hl)] at h
    rcases hp : pinternW m (rdW (m.arr64 IW) o) with _ | ⟨u, m1⟩ <;> rw [hp] at h <;>
      try (simp only [plK1, reduceCtorEq] at h; done)
    by_cases hb : 4294967296 ≤ u
    · rw [plK1_big (h := hb)] at h; cases h
    rw [plK1_ok (h := hb)] at h
    rcases hg : plgW k m1 (o + 1) (l - 1) with _ | ⟨r2, m2⟩ <;> simp only [hg, plK2, reduceCtorEq] at h
    rcases hc : consW k m2 u (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> simp only [hc, plK3, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact ((pinternW_mfr hp).trans (plgW_mfr k hg)).trans (consW_mfr hc)

theorem plW_mfr {k : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : plW k m o l = some (r, m')) :
    MFr [] [] m m' := by
  obtain _ | k := k
  · simp [plW] at h
  rw [plW_succ] at h
  rcases hg : plgW k m o l with _ | ⟨r1, m1⟩ <;> simp only [hg, plW.plK4, reduceCtorEq] at h
  rcases hs : ilF m1 [r1.headD 0, r1.tail.headD 0] with _ | ⟨r2, m2⟩ <;> simp only [hs, plW.plK5, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (plgW_mfr k hg).trans (MFr.of_frame (ilF_frame hs) (by simp [POOL, POOL1, LSREC, LSSLOT, LSHP]) (by simp))

theorem thW_mfr : ∀ (n : Nat) {m m' : Mem} {tyo tyl base : Word} {r : List Word},
    thW n m tyo tyl base = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [thW] at h
  | n + 1, m, m', tyo, tyl, base, r, h => by
    by_cases hl : tyl = 0
    · rw [thW_nil (h := hl)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      exact MFr.refl _ _ _
    rw [thW_cons (h := hl)] at h
    rcases hf : fvinternW m base (rdW (m.arr64 IW) tyo) with _ | ⟨v, m1⟩ <;> rw [hf] at h <;>
      try (simp only [thK1, reduceCtorEq] at h; done)
    by_cases hb : 4294967296 ≤ v
    · rw [thK1_big (h := hb)] at h; cases h
    rw [thK1_ok (h := hb)] at h
    rcases hg : thW n m1 (tyo + 1) (tyl - 1) (base + 1) with _ | ⟨r2, m2⟩ <;> simp only [hg, thK2, reduceCtorEq] at h
    rcases hc : consW n m2 v (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> simp only [hc, thK3, reduceCtorEq] at h
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
theorem tcmK4_wrap (h : pfl + ftl < pfl) : tcmK4 cR n vis fto ftl pfo pfl dso dsl edso edsl rn (some (rb, m)) =
    none := by simp only [tcmK4]; rw [ite_eq_left h]
end arms
attribute [ind_grind] tcmK4_wrap

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

end rel

end L.Ind

end
end
