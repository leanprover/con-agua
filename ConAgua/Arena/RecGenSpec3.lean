import ConAgua.Arena.RecClassSpecH
import ConAgua.Arena.DeclHeader

/-!
# `RecGen`: `classConstOk` (lane `indproofs2`, helper `rec`)

`class_const_ok` calls `install_header` (lane `decls2`'s `installHeader`, the same guards in the
same order) and then infers the type. `ccoGuards` is `ihW_ok` (`DeclHeader.lean`) with the
conclusion stated for `classConstOk`'s guards (they differ from `installHeader`'s in the error
messages only).
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem ccoGuards (mode : ConLeche.CheckMode) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : L.Arena.ihW n m vis q = some (r, m')) (hS : StageR dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64) :
    ∃ a', (ConRon.Arena.classConstOk mode fe cv).run a = (do
        let stype ← inferTypeCore mode fe checkFuel 0 cv.type
        let _u ← ensureSortCore mode fe checkFuel 0 stype).run a' ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  have hq0 : decCV (erA m) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt (IWGrow.refl m)) hq
  obtain ⟨wx, hwx, hwxl, hname⟩ := decCV_name hq0
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hq0
  have ex : rdW (m.arr64 EREC) q = wx := rdW_of_get? rfl hwx
  have et : rdW (m.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hwt
  cases n with
  | zero => simp [L.Arena.ihW] at h
  | succ n =>
  rw [L.Arena.ihW_step, ex, et] at h
  -- `env_find(x, vis)`
  cases h1 : envFindW m wx vis with
  | none => rw [h1] at h; simp [L.Arena.ihK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, L.Arena.ihK1_some] at h
  by_cases hb1 : r1.headD 0 ≠ 0
  · rw [if_pos hb1] at h; simp at h
  rw [if_neg hb1] at h
  obtain ⟨rfl, hfind⟩ := envFindW_miss h1 hS.1.env hwxl (by simpa using hb1)
  -- `reserved_contains(x)`
  cases h2 : resContW n m1 wx with
  | none => rw [h2] at h; simp [L.Arena.ihK2] at h
  | some c =>
  rw [h2, L.Arena.ihK2_some] at h
  by_cases hb2 : c ≠ 0
  · rw [if_pos hb2] at h; simp at h
  rw [if_neg hb2] at h
  have hc0 : c = 0 := by simpa using hb2
  subst hc0
  obtain ⟨rl, hrunR, hrl⟩ := resContW_miss hwxl h2 hS.1.pins
  -- `is_proj_fn_shape(x)`
  cases h3 : stubM "is_proj_fn_shape" m1 [wx] with
  | none => rw [h3] at h; simp [L.Arena.ihK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, L.Arena.ihK3_some] at h
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3, -⟩ :=
    isProjFnShape_spec dn vis fe wx hwxl m1 m3 a r3 h3 hS
  by_cases hb3 : r3.headD 0 ≠ 0
  · rw [if_pos hb3] at h; simp at h
  rw [if_neg hb3] at h
  -- `cv_lps(q)`
  have hq3 : decCV (erA m3) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt hg3) hq
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hq3
  have e1 : rdW (m3.arr64 EREC) (q + 1) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw1
  have e2 : rdW (m3.arr64 EREC) (q + 2) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw2
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m3.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (hslice?_bound _ _ _ _ hsl h0)
  cases n with
  | zero => simp [L.Arena.cvLpsW, L.Arena.ihK4] at h
  | succ n =>
  rw [L.Arena.cvLpsW_step, e1, e2] at h
  cases h4 : erToIwW n m3 w1 w2 with
  | none => rw [h4] at h; simp [L.Arena.ihK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, L.Arena.ihK4_some] at h
  obtain ⟨-, hr4t, hdec4, hS4, hg4, htop4⟩ := L.Arena.erToIwW_stage h4 hS3 hsrc
  rw [hr4t] at h
  have hdecL : decHL m4 (r4.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [hdec4]; exact hsl
  -- `sl_nodup(o, l)`
  cases h5 : nodupW (n + 1) m4 (r4.headD 0) w2 with
  | none => rw [h5] at h; simp [L.Arena.ihK5] at h
  | some d =>
  rw [h5, L.Arena.ihK5_some] at h
  by_cases hb5 : d = 0
  · rw [if_pos hb5] at h; simp at h
  rw [if_neg hb5] at h
  have htopb : iwTop m4 < 2 ^ 64 := by simp only [iwTop]; exact UInt64.toNat_lt _
  obtain ⟨ws, hws, hlps, hwsl⟩ := slR_of_decHL m4 _ _ _ hdecL (by omega)
  simp only [UInt64.ofNat_toNat] at hws
  have hd := nodupW_ok _ _ _ _ _ _ hws h5
  have hnd : nameNodup cv.levelParams = true := by
    rw [hlps, nameNodup_map ws hwsl]
    by_cases hn : ws.Nodup
    · simp [hn]
    · simp [hn] at hd; exact absurd hd hb5
  -- the four walks, as in `ivgW_ok`
  cases h6 : stubM "loose_bvars_bounded_fast" m4 [4000000000, 0, wt] with
  | none => rw [h6] at h; simp [L.Arena.ihK6] at h
  | some rm6 =>
  obtain ⟨r6, m6⟩ := rm6
  rw [h6, L.Arena.ihK6_some] at h
  obtain ⟨x6, a6, hrun6, hS6, hg6, hx6, -⟩ :=
    looseBVarsBoundedFast_spec dn vis fe 4000000000 0 wt hwtl m4 m6 a3 r6 h6 hS4
  by_cases hb6 : r6.headD 0 = 0
  · rw [if_pos hb6] at h; simp at h
  rw [if_neg hb6] at h
  cases h7 : stubM "has_fvar_fast" m6 [4000000000, wt] with
  | none => rw [h7] at h; simp [L.Arena.ihK7] at h
  | some rm7 =>
  obtain ⟨r7, m7⟩ := rm7
  rw [h7, L.Arena.ihK7_some] at h
  obtain ⟨x7, a7, hrun7, hS7, hg7, hx7, -⟩ :=
    hasFvarFast_spec dn vis fe 4000000000 wt hwtl m6 m7 a6 r7 h7 hS6
  by_cases hb7 : r7.headD 0 ≠ 0
  · rw [if_pos hb7] at h; simp at h
  rw [if_neg hb7, hr4t] at h
  cases h8 : stubM "all_level_params_defined" m7 [r4.headD 0, w2, wt] with
  | none => rw [h8] at h; simp [L.Arena.ihK8] at h
  | some rm8 =>
  obtain ⟨r8, m8⟩ := rm8
  rw [h8, L.Arena.ihK8_some] at h
  have hdec7 : decHL m7 (r4.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [decHL_grow (hg6.trans hg7) (by omega), hdecL]
  obtain ⟨x8, a8, hrun8, hS8, hg8, hx8, -⟩ :=
    allLevelParamsDefined_spec dn vis fe (r4.headD 0) w2 wt hwtl cv.levelParams m7 m8 a7 r8 h8
      ⟨hS7, hdec7⟩
  by_cases hb8 : r8.headD 0 = 0
  · rw [if_pos hb8] at h; simp at h
  rw [if_neg hb8] at h
  cases h9 : stubM "consts_resolve_ffast" m8 [vis, wt] with
  | none => rw [h9] at h; simp [L.Arena.ihK9] at h
  | some rm9 =>
  obtain ⟨r9, m9⟩ := rm9
  rw [h9, L.Arena.ihK9_some] at h
  obtain ⟨x9, a9, hrun9, hS9, hg9, hx9, -⟩ :=
    constsResolveFFast_spec dn vis fe wt hwtl m8 m9 a8 r9 h9 hS8
  by_cases hb9 : r9.headD 0 = 0
  · rw [if_pos hb9] at h; simp at h
  rw [if_neg hb9] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have ex3 : x3 = false := by rw [← hx3]; simpa using hb3
  have ex6 : x6 = true := by rw [← hx6]; simpa using hb6
  have ex7 : x7 = false := by rw [← hx7]; simpa using hb7
  have ex8 : x8 = true := by rw [← hx8]; simpa using hb8
  have ex9 : x9 = true := by rw [← hx9]; simpa using hb9
  rw [L.Arena.fuelW] at hrun6 hrun7
  rw [show ((0 : Word).toNat) = 0 from rfl] at hrun6
  rw [← hname] at hfind hrun3 hrl
  rw [← hty] at hrun6 hrun7 hrun8 hrun9
  refine ⟨a9, ?_, hS9, hg3.trans (hg4.trans (hg6.trans (hg7.trans (hg8.trans hg9))))⟩
  simp only [ConRon.Arena.classConstOk, StateT.run_bind, hfind, Option.isSome_none,
    Bool.false_eq_true, if_false, hrunR, exc_ok_bind', hrl, hrun3, ex3, hnd, hrun6, ex6, hrun7,
    ex7, hrun8, ex8, hrun9, ex9, if_true, StateT.run_pure]


end L.Ind

namespace L.Ind

open L.Arena

/-! ## `class_const_ok` -/

def ccoK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m3) => some ([0], m3)

def ccoK2 (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => ccoK3 (stubM "ensure_sort_core" m2 [vis, 0, r2.headD 0])

def ccoK1 (vis q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => ccoK2 vis (stubM "infer_type_core" m1 [vis, 0, rdW (m1.arr64 EREC) (q + 3)])

/-- **The model of `class_const_ok`**: `install_header`, then the inference. -/
def ccoW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, q => ccoK1 vis q (L.Arena.ihW n m vis q)

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (vis q : Word) (r1 r2 r3 : List Word)
theorem ccoW_eq : ccoW (n + 1) m vis q = ccoK1 vis q (L.Arena.ihW n m vis q) := rfl
theorem ccoK1_some : ccoK1 vis q (some (r1, m1)) =
    ccoK2 vis (stubM "infer_type_core" m1 [vis, 0, rdW (m1.arr64 EREC) (q + 3)]) := rfl
theorem ccoK2_some : ccoK2 vis (some (r2, m2)) = ccoK3 (stubM "ensure_sort_core" m2 [vis, 0, r2.headD 0]) := rfl
theorem ccoK3_some : ccoK3 (some (r3, m3)) = some ([0], m3) := rfl
end arms

grind_pattern [ind_grind] ccoW_eq => ccoW (n + 1) m vis q
grind_pattern [ind_grind] ccoK1_some => ccoK1 vis q (some (r1, m1))
grind_pattern [ind_grind] ccoK2_some => ccoK2 vis (some (r2, m2))
grind_pattern [ind_grind] ccoK3_some => ccoK3 (some (r3, m3))

/-- `class_const_ok_header`'s spec: `install_header`'s (`ih_specW`), the same body. -/
theorem classConstOkHeader_spec (p : Prog) (h : IhProg p)
    (hh : p.lookup "class_const_ok_header" = some classConstOkHeader) (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_const_ok_header" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ L.Arena.ihW n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hh]
  simp only [callFn, classConstOkHeader]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_specW p h.ix h.rowGet h.find n, resCont_spec p h.resF h.resC n,
        L.Arena.cvLps_specW p h.alloc h.copy h.eti h.lps n, slNodup_spec p h.cont h.nodup n,
        stubM_spec p "is_proj_fn_shape" n,
        stubM_spec p "loose_bvars_bounded_fast" n, stubM_spec p "has_fvar_fast" n,
        stubM_spec p "all_level_params_defined" n, stubM_spec p "consts_resolve_ffast" n] <;>
      finish (gen := 20)

theorem classConstOk_spec (p : Prog) (h : IhProg p)
    (hh : p.lookup "class_const_ok_header" = some classConstOkHeader)
    (hc : p.lookup "class_const_ok" = some classConstOkL)
    (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_const_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ ccoW n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hc]
  simp only [callFn, classConstOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classConstOkHeader_spec p h hh n,
        stubM_spec p "infer_type_core" n, stubM_spec p "ensure_sort_core" n] <;>
      finish (gen := 20) [rdW_eq]

theorem ccoW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (q : Word) (cv : IConstantVal) (hS : StageR dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64) :
    RSim (ccoW n m vis q) (ConRon.Arena.classConstOk .verified fe cv) a (KP dn vis fe m decUnit) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [ccoW_eq]
  rintro b hb
  cases h1 : L.Arena.ihW n m vis q with
  | none => rw [h1] at hb; cases hb
  | some rm =>
  obtain ⟨r1, m1⟩ := rm
  rw [h1] at hb
  obtain ⟨a1, hrun, hS1, hg1⟩ := ccoGuards .verified h1 hS hq hqb
  have hq1 : decCV (erA m1) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt hg1) hq
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hq1
  have et : rdW (m1.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hwt
  have hr : RSim (ccoK1 vis q (some (r1, m1)))
      (do let stype ← inferTypeCore .verified fe checkFuel 0 cv.type
          let _u ← ensureSortCore .verified fe checkFuel 0 stype) a1 (KP dn vis fe m decUnit) := by
    rw [ccoK1_some, et, hty]
    have hi := (inferTypeCore_spec dn vis fe 0 wt hwtl).sim hS1
    rw [show (0 : Word).toNat = 0 from rfl] at hi
    refine RSim.bind (K := ccoK2 vis) rfl hi ?_
    rintro ⟨r2, m2⟩ st a2 - ⟨hS2, hg2, hb2, rfl⟩
    dsimp only at hS2 hg2 hb2
    rw [ccoK2_some]
    have he := (ensureSortCore_spec dn vis fe 0 (r2.headD 0) hb2).sim hS2
    rw [show (0 : Word).toNat = 0 from rfl] at he
    refine RSim.bind (K := ccoK3) rfl he ?_
    rintro ⟨r3, m3⟩ u a3 - ⟨hS3, hg3, -⟩
    rw [ccoK3_some]
    exact RSim.pure_some ⟨hS3, (hg1.trans hg2).trans hg3, trivial⟩
  obtain ⟨x, a', hr', hQ⟩ := hr b hb
  exact ⟨x, a', by rw [hrun]; exact hr', hQ⟩

/-- **`class_const_ok` refines `classConstOk`** (the guards are `install_header`'s, through its
stubs; then the stubs `infer_type_core`, `ensure_sort_core`). -/
@[refines ConRon.Arena.classConstOk]
theorem classConstOk_refines (p : Prog) (h : IhProg p)
    (hh : p.lookup "class_const_ok_header" = some classConstOkHeader)
    (hc : p.lookup "class_const_ok" = some classConstOkL) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q : Word) (cv : IConstantVal)
    (hS : StageR dn vis fe s₀.mem a₀) (hq : decCV (erecP s₀.mem) q.toNat = some cv)
    (hqb : q.toNat + 3 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_const_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classConstOk .verified fe cv) a₀ ∧
      KP dn vis fe s₀.mem decUnit (r, s'.mem) (AM.st (ConRon.Arena.classConstOk .verified fe cv) a₀)
        (AM.res (ConRon.Arena.classConstOk .verified fe cv) a₀); ⊤⦄ :=
  triple_post (classConstOk_spec p h hh hc n s₀ vis q) fun _ _ ⟨hl, hw⟩ =>
    ⟨hl, (ccoW_sim dn vis fe n _ a₀ q cv hS hq hqb).am hw⟩

end L.Ind
