module

public import ConAgua.Arena.IndSumSpec.TsrW
import ConAgua.Arena.RecGenSpec.CruleProg
public import ConAgua.Arena.RecGenSpec.DecRR
import ConAgua.Arena.IndInstallSpec.IcbiW
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.RecClassSpec.CloseLams
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.L.WordOff
import all ConAgua.Arena.IndParts
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.RecCheck

@[expose] public section

/-!
# ConsBlockRecsTF: `ConRon.Arena.consBlockRecsTF`

The refinement theorems `consBlockRecsTF_refines` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_struct_proj_table_scoped` -/

/-- After the rest. -/
def sctK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
/-- After `loose_bvars_bounded_fast`: the verdict. -/
def sctK4 (rest : Mem → Option (List Word × Mem)) (r1 r2 r3 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m) => if r1 = 0 ∧ r2 = 1 ∧ r3 = 1 ∧ r4.headD 0 = 1 then sctK5 (rest m) else some ([0], m)
/-- After `consts_resolve_ffast`. -/
def sctK3 (rest : Mem → Option (List Word × Mem)) (nP b r1 r2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m) => sctK4 rest r1 r2 (r3.headD 0)
      (lbbF m [CWF, nP + 1, b])
/- ronsync2 stage 2: commented out (statement at the old twin/L)
/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- After `all_level_params_defined`. -/
def sctK2 (rest : Mem → Option (List Word × Mem)) (vis nP b r1 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m) => sctK3 rest nP b r1 (r2.headD 0) (crfF m [vis, b])
-/
/-- After `has_fvar_fast`. -/
def sctK1 (c : CallM) (n : Nat) (rest : Mem → Option (List Word × Mem)) (vis nP lo ll b : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => sctK2 rest vis nP b (r1.headD 0) (c n "all_level_params_defined" [lo, ll, b] m)
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `check_struct_proj_table_scoped(vis, nP, lo, ll, bO, bL)`** at exec fuel `n`,
reading `all_level_params_defined` through `c` (`stubCall`: the stub contract; `realCall p`: the
program's own call, `IndRealSctC.lean`). -/
def sctW (c : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, nP, lo, ll, bO, bL =>
    if bL = 0 then some ([1], m)
    else sctK1 c n (fun m' => sctW c n m' vis nP lo ll (bO + 1) (bL - 1)) vis nP lo ll (rdW (m.arr64 IW) bO)
      (hffF m [CWF, rdW (m.arr64 IW) bO])
-/

section arms
variable (c : CallM) (rest : Mem → Option (List Word × Mem)) (n : Nat) (m : Mem)
  (vis nP lo ll bO bL b r1 r2 r3 : Word) (r : List Word)
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem sctW_nil (h : bL = 0) : sctW c (n + 1) m vis nP lo ll bO bL = some ([1], m) := by simp [sctW, h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem sctW_cons (h : bL ≠ 0) : sctW c (n + 1) m vis nP lo ll bO bL =
    sctK1 c n (fun m' => sctW c n m' vis nP lo ll (bO + 1) (bL - 1)) vis nP lo ll (rdW (m.arr64 IW) bO)
      (hffF m [CWF, rdW (m.arr64 IW) bO]) := by simp [sctW, h]
-/
theorem sctK5_some : sctK5 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem sctK4_yes (h : r1 = 0 ∧ r2 = 1 ∧ r3 = 1 ∧ r.headD 0 = 1) :
    sctK4 rest r1 r2 r3 (some (r, m)) = sctK5 (rest m) := by simp only [sctK4]; rw [ite_eq_left h]
theorem sctK4_no (h : ¬ (r1 = 0 ∧ r2 = 1 ∧ r3 = 1 ∧ r.headD 0 = 1)) :
    sctK4 rest r1 r2 r3 (some (r, m)) = some ([0], m) := by simp only [sctK4]; rw [ite_eq_right h]
theorem sctK3_some : sctK3 rest nP b r1 r2 (some (r, m)) =
    sctK4 rest r1 r2 (r.headD 0) (lbbF m [CWF, nP + 1, b]) := rfl
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem sctK2_some : sctK2 rest vis nP b r1 (some (r, m)) =
    sctK3 rest nP b r1 (r.headD 0) (crfF m [vis, b]) := rfl
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem sctK1_some : sctK1 c n rest vis nP lo ll b (some (r, m)) =
    sctK2 rest vis nP b (r.headD 0) (c n "all_level_params_defined" [lo, ll, b] m) := rfl
-/
end arms
-- ronsync2 stage 2: attribute [ind_grind] sctW_nil sctW_cons sctK5_some sctK4_yes sctK4_no sctK3_some sctK2_some sctK1_some

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem sctW_spec (p : Prog) (hb : BvbProg p) (hf : HfF p) (hcr : CrfF p)
    (hp : p.lookup "check_struct_proj_table_scoped" = some checkStructProjTableScopedL)
    (c : CallM) (hc : CallSpec p c) (n : Nat) : ∀ (s₀ : St) (vis nP lo ll bO bL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_struct_proj_table_scoped" [vis, nP, lo, ll, bO, bL]
    ⦃fun r s' => LocEq s' s₀ ∧ sctW c n s₀.mem vis nP lo ll bO bL = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis nP lo ll bO bL; rw [invoke_eq _ hp]; simp only [callFn, checkStructProjTableScopedL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis nP lo ll bO bL
    rw [invoke_eq _ hp]
    simp only [callFn, checkStructProjTableScopedL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        hffF_spec p hf n, hc n "all_level_params_defined",
        crfF_spec p hcr n, lbbF_spec p hb n, ih] <;>
      finish (gen := 30) (instances := 5000) [rdW_eq]
-/

/-- The twin's per-body scoping test (`checkStructProjTable`'s `allM` body, verbatim). -/
def scopeT (fe : IFEnv) (lps : List NIdx) (nP : Nat) (b : EIdx) : AM Bool := do
  pure (!(← hasFvarFast coreWalkFuel b) &&
    (← allLevelParamsDefined lps b) &&
    (← constsResolveFFast fe b) &&
    (← looseBVarsBoundedFast coreWalkFuel (nP + 1) b))

theorem sumB01 {r : Word} {b : Bool} (h : (r != 0) = b) (hl : r.toNat ≤ 1) :
    (r = 1 ↔ b = true) ∧ (r = 0 ↔ b = false) := by
  subst h
  have : r = 0 ∨ r = 1 := by
    rcases (show r.toNat = 0 ∨ r.toNat = 1 by omega) with h | h
    · exact .inl (UInt64.toNat_inj.mp (by simpa using h))
    · exact .inr (UInt64.toNat_inj.mp (by simpa using h))
  rcases this with rfl | rfl <;> decide

theorem tblMem_eq (m : Mem) (q T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 : Word) :
    tblMem m q T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 =
      wrER m q [6, 0, T, lo2, ll2, nP, C, nF, rs, bo2, bl2, go2, gl2] := by
  simp only [tblMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl, show q + 6 + 1 = q + 7 by ac_rfl,
    show q + 7 + 1 = q + 8 by ac_rfl, show q + 8 + 1 = q + 9 by ac_rfl,
    show q + 9 + 1 = q + 10 by ac_rfl, show q + 10 + 1 = q + 11 by ac_rfl,
    show q + 11 + 1 = q + 12 by ac_rfl]

/-! ## `check_struct_proj_table`: the relation to the twin -/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The table record's decoding**, from its thirteen words and the three copied slices. -/
theorem sumDecTbl {a : Array Word} {q : Nat}
    {T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 : Word} {lps : List NIdx} {bodies : List EIdx}
    {guards : List LIdx}
    (hw : ∀ i < 13, a[q + i]? = [6, 0, T, lo2, ll2, nP, C, nF, rs, bo2, bl2, go2, gl2][i]?)
    (hT : H T) (hC : H C) (hrs : H rs)
    (hl : hslice? (aread a) lo2.toNat ll2.toNat = some lps) (hb : hslice? (aread a) bo2.toNat bl2.toNat = some bodies)
    (hg : hslice? (aread a) go2.toNat gl2.toNat = some guards) :
    decTbl (aread a) q = some ⟨decI T, lps, nP.toNat, decI C, nF.toNat, decI rs, bodies.toArray, guards⟩ := by
  have h2 := hw 2 (by decide); have h3 := hw 3 (by decide)
  have h4 := hw 4 (by decide); have h5 := hw 5 (by decide); have h6 := hw 6 (by decide)
  have h7 := hw 7 (by decide); have h8 := hw 8 (by decide); have h9 := hw 9 (by decide)
  have h10 := hw 10 (by decide); have h11 := hw 11 (by decide); have h12 := hw 12 (by decide)
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have e3 : q + 3 + 1 = q + 4 := rfl
  have e9 : q + 9 + 1 = q + 10 := rfl
  have e11 : q + 11 + 1 = q + 12 := rfl
  simp only [decTbl, hlist?, nat?, hd?, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    e3, e9, e11, Option.map_some, Option.bind_eq_bind, Option.bind_some, hT, hC, hrs, ite_true,
    hl, hb, hg]
  rfl
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem envPushW_afr {m m' : Mem} {vis q : Word} {r : List Word} (h : envPushW m vis q = some (r, m')) :
    AFr m m' := by
  simp only [envPushW] at h
  split at h; · cases h
  split at h; · cases h
  split at h
  rotate_left
  · cases h
  rename_i hc
  obtain ⟨ht, -⟩ := hc
  have hrow : rowArr (rdW (m.arr64 EREC) (q + 1)) ∈ [132, 133, 134, ECON, 140, 141, 142] := by
    rcases rowArr_names (rdW (m.arr64 EREC) (q + 1)) with h | h | h | h | h | h <;> rw [h] <;> decide
  have hne : (rowArr (rdW (m.arr64 EREC) (q + 1)) : TieredArray) ≠ ↑CTL :=
    TieredArray.t0_ne (rowArr_ne _ (by decide))
  have h49 : memoFreeA [rowArr (rdW (m.arr64 EREC) (q + 1))] = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hf1 : AFr m (rowSet m (rdW (m.arr64 EREC) (q + 1)) (vis + 1) q) := by
    unfold rowSet
    exact (AFr.set64 m _ hne h49 _ _).trans (AFr.set64 _ _ hne h49 _ _)
  simp only [envPushK] at h
  split at h; · cases h
  split at h
  rotate_left
  · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact hf1.trans ((AFr.set64 _ ECON (by decide) (by decide) _ _).trans (AFr.setCtl _ 128 (by decide) _))
-/

end L.Ind

end

end

section

noncomputable section

/-!
# `RecCheck`: `targetMajorNfs` (lane `indproofs3`, helper `rec`)

The walk's recorded constructor normal forms of a class. L (D18): the loop became the twin's list
recursion (the tail first, so the class-match calls fire from the last entry to the first), each
kept entry `sl_cons`ed onto the kept tail (a copy, so the result is a pointer slice decoded below
the tops). Callees: `ctors_have_name` (helper `recb`'s `chnW`), `target_class_match`
(`RecCheckSpec/TcmLook`), `sl_cons`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The head of a pointer slice decoded below the tops. -/
theorem PSlR.uncons {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o l : Word} {m : Mem}
    (h : PSlR f xs o l m) (hl : l ≠ 0) (_hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∃ x ys, xs = x :: ys ∧ DecB (fun m' => f m' (rdW (m.arr64 IW) o).toNat) m x ∧
      PSlR f ys (o + 1) (l - 1) m := by
  obtain ⟨hd, hb⟩ := h
  have hb64 : o.toNat + l.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hb (Nat.lt_of_le_of_lt (by
    simp only [iwTop]; exact Nat.le_refl _) (rdW (m.arr64 CTL) 200).toNat_lt)
  obtain ⟨eo, el, hl0⟩ := slice_step hl hb64
  obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
  have hd' : decPL (truncM m) (f (truncM m)) o.toNat (l' + 1) = some xs := by rw [← hl']; exact hd
  obtain ⟨pp, x, ys, rfl, hp, hx, hys⟩ := decPL_cons hd'
  obtain ⟨-, hpm⟩ := rec2IwN_trunc hp
  have hr := (iwN_rdW hpm (by omega)).1
  rw [UInt64.ofNat_toNat] at hr
  refine ⟨x, ys, rfl, ?_, ?_, ?_⟩
  · show f (truncM m) (rdW (m.arr64 IW) o).toNat = some x
    rw [hr, UInt64.toNat_ofNat_of_lt' (iwN_rdW hpm (by omega)).2]; exact hx
  · show decPL (truncM m) (f (truncM m)) (o + 1).toNat (l - 1).toNat = some ys
    rw [eo, el, hl']; exact hys
  · rw [eo, el]; omega

end L.Ind

end
end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Rule records at another address -/

section shift
variable {a b : Array Word}

/-- A rule record copied word for word (its fire slices decoding in the larger array). -/
theorem decRule_copy {q q' : Nat} {rl : IRecRule} (h : decRule (aread a) q = some rl) (hext : ArrExt (aread a) (aread b))
    (hw : ∀ i, i < 11 → b[q' + i]? = a[q + i]?) : decRule (aread b) q' = some rl := by
  sorry

end shift

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `rules_to_erec` -/

/-- The memory after one record's eleven copies (each copy reads the memory of its time). -/
def cpMem (m : Mem) (b old : Word) : Mem :=
  let m1 := m.set64 EREC b (rdW (m.arr64 EREC) old)
  let m2 := m1.set64 EREC (b + 1) (rdW (m1.arr64 EREC) (old + 1))
  let m3 := m2.set64 EREC (b + 2) (rdW (m2.arr64 EREC) (old + 2))
  let m4 := m3.set64 EREC (b + 3) (rdW (m3.arr64 EREC) (old + 3))
  let m5 := m4.set64 EREC (b + 4) (rdW (m4.arr64 EREC) (old + 4))
  let m6 := m5.set64 EREC (b + 5) (rdW (m5.arr64 EREC) (old + 5))
  let m7 := m6.set64 EREC (b + 6) (rdW (m6.arr64 EREC) (old + 6))
  let m8 := m7.set64 EREC (b + 7) (rdW (m7.arr64 EREC) (old + 7))
  let m9 := m8.set64 EREC (b + 8) (rdW (m8.arr64 EREC) (old + 8))
  let m10 := m9.set64 EREC (b + 9) (rdW (m9.arr64 EREC) (old + 9))
  m10.set64 EREC (b + 10) (rdW (m10.arr64 EREC) (old + 10))

/-- **The model of `rule_copy`.** -/
def rcpW (m : Mem) (b old : Word) : Option (List Word × Mem) := some ([0], cpMem m b old)

def rteK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([0], m)

/-- **The model of `rules_to_erec_go`** (exec fuel). -/
def rteGoW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, b, ro, rl =>
    if rl = 0 then some ([0], m)
    else rteK1 (rteGoW n (cpMem m b (rdW (m.arr64 IW) ro)) (b + 11) (ro + 1) (rl - 1))

section arms
variable (n : Nat) (m : Mem) (b ro rl : Word) (r : List Word)
theorem rcW_eq (old : Word) : rcpW m b old = some ([0], cpMem m b old) := rfl
theorem rteGoW_nil (h : rl = 0) : rteGoW (n + 1) m b ro rl = some ([0], m) := by simp [rteGoW, h]
theorem rteGoW_cons (h : ¬ rl = 0) : rteGoW (n + 1) m b ro rl =
    rteK1 (rteGoW n (cpMem m b (rdW (m.arr64 IW) ro)) (b + 11) (ro + 1) (rl - 1)) := by simp [rteGoW, h]
theorem rteK1_some : rteK1 (some (r, m)) = some ([0], m) := rfl
end arms
attribute [ind_grind] rcW_eq rteGoW_nil rteGoW_cons rteK1_some

/-- The lookups of `cons_block_recs_tf`. -/
structure CbrLook (p : Prog) : Prop where
  tsr : TsrLook p
  rp : RecProg p
  rc : p.lookup "rule_copy" = some ruleCopy
  rteg : p.lookup "rules_to_erec_go" = some rulesToErecGo
  rir : p.lookup "rec_info_rec" = some recInfoRec
  rte : p.lookup "rules_to_erec" = some rulesToErec
  mi : p.lookup "block_shape_major_idx_at" = some blockShapeMajorIdxAt
  rpa : p.lookup "block_shape_rule_prefix_at" = some blockShapeRulePrefixAt

theorem rc_spec (p : Prog) (L : CbrLook p) (n : Nat) (s₀ : St) (b old : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rule_copy" [b, old]
    ⦃fun r s' => LocEq s' s₀ ∧ rcpW s₀.mem b old = some (r, s'.mem); ⊤⦄ := by
  sorry

theorem rteGo_spec (p : Prog) (L : CbrLook p) (n : Nat) :
    ∀ (s₀ : St) (b ro rl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rules_to_erec_go" [b, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ rteGoW n s₀.mem b ro rl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ b ro rl
    rw [invoke_eq _ L.rteg]; simp only [callFn, rulesToErecGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ b ro rl
    rw [invoke_eq _ L.rteg]
    simp only [callFn, rulesToErecGo]
    sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, rc_spec p L n, ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

l_model rte_spec (p : Prog) (hL : CbrLook p)
  fns [hL.rte ↦ rteW]
  specs [erecAlloc_specW p hL.tsr.ea n, rteGo_spec p hL n]
  grind [arena_grind]

/-! ## `rules_to_erec`: the copied run decodes as the rules -/

/-- The eleven words of the record at `old`. -/
def recWords (E : Array Word) (old : Word) : List Word :=
  [rdW E old, rdW E (old + 1), rdW E (old + 2), rdW E (old + 3), rdW E (old + 4), rdW E (old + 5),
    rdW E (old + 6), rdW E (old + 7), rdW E (old + 8), rdW E (old + 9), rdW E (old + 10)]

/-- The words of the records the pointers `IW[ro ‥ ro + k)` point to, in order. -/
def ruleWords (m : Mem) (ro : Word) : Nat → List Word
  | 0 => []
  | k + 1 => recWords (m.arr64 EREC) (rdW (m.arr64 IW) ro) ++ ruleWords m (ro + 1) k

theorem ruleWords_length (m : Mem) : ∀ (ro : Word) (k : Nat), (ruleWords m ro k).length = 11 * k
  | _, 0 => rfl
  | ro, k + 1 => by simp [ruleWords, recWords, ruleWords_length m (ro + 1) k]; omega

theorem cpMem_eq {m : Mem} {b old : Word} (hlt : old.toNat + 11 ≤ b.toNat) (hb : b.toNat + 11 < 2 ^ 64) :
    cpMem m b old = wrER m b (recWords (m.arr64 EREC) old) := by
  simp only [cpMem, wrER, recWords]
  rw [show b + 1 + 1 = b + 2 by ac_rfl, show b + 2 + 1 = b + 3 by ac_rfl,
    show b + 3 + 1 = b + 4 by ac_rfl, show b + 4 + 1 = b + 5 by ac_rfl,
    show b + 5 + 1 = b + 6 by ac_rfl, show b + 6 + 1 = b + 7 by ac_rfl, show b + 7 + 1 = b + 8 by ac_rfl,
    show b + 8 + 1 = b + 9 by ac_rfl, show b + 9 + 1 = b + 10 by ac_rfl]
  simp (disch := off_omega) only [rdW_set64_ne_er]

theorem rdW_agree {a a' : Array Word} {B : Nat} (hE : ∀ i < B, a'[i]? = a[i]?) {y : Word} (hy : y.toNat < B) :
    rdW a' y = rdW a y := by
  unfold rdW; rw [hE _ hy]

/-- `EREC` below `B` and `IW` agreeing: the record words read the same. -/
theorem ruleWords_congr {m m' : Mem} (hI : m'.arr64 IW = m.arr64 IW) {B : Nat}
    (hE : ∀ i < B, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) :
    ∀ (ro : Word) (k : Nat), (∀ j < k, (rdW (m.arr64 IW) (ro + UInt64.ofNat j)).toNat + 11 ≤ B) →
      ruleWords m' ro k = ruleWords m ro k
  | _, 0, _ => rfl
  | ro, k + 1, h => by
    simp only [ruleWords, hI]
    have h0 := h 0 (by omega)
    simp only [show (UInt64.ofNat 0 : Word) = 0 from rfl, UInt64.add_zero] at h0
    have hr : ∀ i : Nat, i ≤ 10 → rdW (m'.arr64 EREC) (rdW (m.arr64 IW) ro + UInt64.ofNat i) =
        rdW (m.arr64 EREC) (rdW (m.arr64 IW) ro + UInt64.ofNat i) := fun i hi =>
      rdW_agree hE (by rw [UInt64.toNat_add]; simp; omega)
    congr 1
    · simp only [recWords]
      have := hr 0 (by omega); have := hr 1 (by omega); have := hr 2 (by omega); have := hr 3 (by omega)
      have := hr 4 (by omega); have := hr 5 (by omega); have := hr 6 (by omega); have := hr 7 (by omega)
      have := hr 8 (by omega); have := hr 9 (by omega); have := hr 10 (by omega)
      simp_all
    · exact ruleWords_congr hI hE (ro + 1) k (fun j hj => by
        have e : ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := by
          rw [UInt64.ofNat_add]; ac_rfl
        rw [e]; exact h (j + 1) (by omega))

theorem ruleWords_get (m : Mem) : ∀ (ro : Word) (k j i : Nat), j < k → i < 11 →
    (ruleWords m ro k)[11 * j + i]? = some (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + UInt64.ofNat i))
  | _, 0, _, _, hj, _ => absurd hj (by omega)
  | ro, k + 1, 0, i, _, hi => by
    simp only [ruleWords, Nat.mul_zero, Nat.zero_add, show (UInt64.ofNat 0 : Word) = 0 from rfl, UInt64.add_zero]
    rw [List.getElem?_append_left (by simp [recWords]; omega)]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [recWords] <;> rfl
  | ro, k + 1, j + 1, i, hj, hi => by
    simp only [ruleWords]
    rw [List.getElem?_append_right (by simp [recWords]; omega)]
    have e : 11 * (j + 1) + i - (recWords (m.arr64 EREC) (rdW (m.arr64 IW) ro)).length = 11 * j + i := by
      simp [recWords]; omega
    rw [e, ruleWords_get m (ro + 1) k j i (by omega) hi]
    have e2 : ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := by rw [UInt64.ofNat_add]; ac_rfl
    rw [e2]

theorem rteGoW_mem (n : Nat) : ∀ (m m' : Mem) (b ro rl : Word) (r : List Word),
    rteGoW n m b ro rl = some (r, m') →
    (∀ j < rl.toNat, (rdW (m.arr64 IW) (ro + UInt64.ofNat j)).toNat + 11 ≤ b.toNat) →
    b.toNat + 11 * rl.toNat ≤ (m.arr64 EREC).size → (m.arr64 EREC).size < 2 ^ 64 →
    m' = wrER m b (ruleWords m ro rl.toNat) := by
  induction n with
  | zero => intro m m' b ro rl r h; simp [rteGoW] at h
  | succ n ih =>
  intro m m' b ro rl r h hold hsz hEs
  by_cases h0 : rl = 0
  · rw [rteGoW_nil (h := h0)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    subst h0; rfl
  rw [rteGoW_cons (h := h0)] at h
  have hl0 : rl.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
  have h00 := hold 0 (by omega)
  simp only [show (UInt64.ofNat 0 : Word) = 0 from rfl, UInt64.add_zero] at h00
  have hb11 : b.toNat + 11 < 2 ^ 64 := by omega
  rw [cpMem_eq h00 hb11] at h
  rcases h1 : rteGoW n (wrER m b (recWords (m.arr64 EREC) (rdW (m.arr64 IW) ro))) (b + 11) (ro + 1) (rl - 1) with _ | ⟨r1, m1⟩ <;> simp only [h1, rteK1, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  generalize hW : wrER m b (recWords (m.arr64 EREC) (rdW (m.arr64 IW) ro)) = W at h1
  have hfr := wrER_frame (recWords (m.arr64 EREC) (rdW (m.arr64 IW) ro)) m b
  rw [hW] at hfr
  have hI : W.arr64 IW = m.arr64 IW := hfr.1 IW (by decide) (by decide)
  have hEsz : (W.arr64 EREC).size = (m.arr64 EREC).size := hfr.size EREC
  have hlow : ∀ i < b.toNat, (W.arr64 EREC)[i]? = (m.arr64 EREC)[i]? := fun i hi => by
    rw [← hW, wrER_get _ m b i (by simp [recWords]; omega) hEs]
    rw [ite_eq_right (by omega)]
  have hb1 : (b + 11).toNat = b.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
  have hl1 : (rl - 1).toNat = rl.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  have hshift : ∀ j < (rl - 1).toNat, (rdW (W.arr64 IW) (ro + 1 + UInt64.ofNat j)).toNat + 11 ≤ (b + 11).toNat := by
    intro j hj
    have e2 : ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := by rw [UInt64.ofNat_add]; ac_rfl
    rw [hI, e2, hb1]; have := hold (j + 1) (by omega); omega
  have := ih W m1 (b + 11) (ro + 1) (rl - 1) r1 h1 hshift (by rw [hb1, hEsz, hl1]; omega) (by rw [hEsz]; exact hEs)
  rw [this, hl1]
  have hcong : ruleWords W (ro + 1) (rl.toNat - 1) = ruleWords m (ro + 1) (rl.toNat - 1) :=
    ruleWords_congr hI hlow (ro + 1) _ (fun j hj => by
      have e2 : ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := by rw [UInt64.ofNat_add]; ac_rfl
      rw [e2]; exact hold (j + 1) (by omega))
  rw [hcong, ← hW]
  obtain ⟨k, hk⟩ : ∃ k, rl.toNat = k + 1 := ⟨rl.toNat - 1, by omega⟩
  rw [hk, show k + 1 - 1 = k from rfl]
  simp only [ruleWords]
  rw [wrER_append]
  rfl

theorem mapM_range_some {α : Type} : ∀ (xs : List α) (f : Nat → Option α),
    (∀ j (hj : j < xs.length), f j = some xs[j]) → (List.range xs.length).mapM f = some xs
  | [], f, _ => rfl
  | x :: xs, f, h => by
    simp only [List.length_cons, List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
    have h0 : f 0 = some x := h 0 (by simp)
    have ih := mapM_range_some xs (f ∘ Nat.succ) (fun j hj => h (j + 1) (by simp; omega))
    simp only [h0, Option.bind_eq_bind, Option.bind_some]
    rw [ih]; rfl

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `rec_info_rec` -/

/-- The memory after `rec_info_rec`'s nine writes (each copy reads the memory of its time). -/
def riMem (m1 : Mem) (q cv mi rp3 reo rel : Word) : Mem :=
  let m2 := m1.set64 EREC q 5
  let m3 := m2.set64 EREC (q + 1) (rdW (m2.arr64 EREC) cv)
  let m4 := m3.set64 EREC (q + 2) (rdW (m3.arr64 EREC) (cv + 1))
  let m5 := m4.set64 EREC (q + 3) (rdW (m4.arr64 EREC) (cv + 2))
  let m6 := m5.set64 EREC (q + 4) (rdW (m5.arr64 EREC) (cv + 3))
  ((((m6.set64 EREC (q + 5) mi).set64 EREC (q + 6) rp3).set64 EREC (q + 7) reo).set64 EREC (q + 8) rel)

/-- **The model of `rec_info_rec`.** -/
def riW (m : Mem) (cv mi rp3 reo rel : Word) : Option (List Word × Mem) :=
  match erAllocW m 9 with
  | none => none
  | some (q, m1) => some ([q], riMem m1 q cv mi rp3 reo rel)

theorem ri_spec (p : Prog) (L : CbrLook p) (n : Nat) (s₀ : St) (cv mi rp3 reo rel : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec_info_rec" [cv, mi, rp3, reo, rel]
    ⦃fun r s' => LocEq s' s₀ ∧ riW s₀.mem cv mi rp3 reo rel = some (r, s'.mem); ⊤⦄ := by
  sorry

theorem riMem_eq {m1 : Mem} {q cq mi rp3 reo rel : Word} (hlt : cq.toNat + 4 ≤ q.toNat) (hq : q.toNat + 9 < 2 ^ 64) :
    riMem m1 q cq mi rp3 reo rel = wrER m1 q [5, rdW (m1.arr64 EREC) cq, rdW (m1.arr64 EREC) (cq + 1),
      rdW (m1.arr64 EREC) (cq + 2), rdW (m1.arr64 EREC) (cq + 3), mi, rp3, reo, rel] := by
  simp only [riMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl, show q + 6 + 1 = q + 7 by ac_rfl, show q + 7 + 1 = q + 8 by ac_rfl]
  simp (disch := off_omega) only [rdW_set64_ne_er]

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`class_fe_r_rec` under the stage relation**: a fresh rule-less `.recInfo` record of the constant
at `cq`. -/
theorem riRec_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq mi rp3 reo rel q : Word} {cv : IConstantVal} {rules : List IRecRule}
    (h : riW m cq mi rp3 reo rel = some ([q], m'))
    (hS : StageR vis fe m a) (hcv : decCV (erecP m) cq.toNat = some cv)
    (hru : decRules (erecP m) reo.toNat rel.toNat = some rules) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ MFr [] [] m m' ∧
      decCI (erecP m') q.toNat = some (.recInfo cv mi.toNat rp3.toNat rules) := by
  cases h1 : erAllocW m 9 with
  | none => simp [riW, h1] at h
  | some x =>
  obtain ⟨q1, m1⟩ := x
  simp only [riW, h1, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl⟩ := h
  have h3 : erecP m (cq.toNat + 3) ≠ none := by
    have := decCV_type hcv; intro e; simp [hd?, e] at this
  have hcq : cq.toNat + 4 ≤ erTop m := by
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h3; have := erecP_lt hv; omega
  have hE1 : m1.arr64 EREC = m.arr64 EREC := by
    simp only [erAllocW] at h1; split at h1; · cases h1
    split at h1; · cases h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨-, rfl⟩ := h1
    simp only [erAllocMem]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  obtain ⟨-, hEtop, -, hEsz, -⟩ := hS.iw
  have hq1 : q1.toNat = erTop m := by
    simp only [erAllocW] at h1; split at h1; · cases h1
    split at h1; · cases h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, -⟩ := h1; rfl
  obtain ⟨hS', hg, -, htop', hget⟩ := erRec_stage h1 hS [5, rdW (m.arr64 EREC) cq,
    rdW (m.arr64 EREC) (cq + 1), rdW (m.arr64 EREC) (cq + 2), rdW (m.arr64 EREC) (cq + 3), mi, rp3, reo, rel]
    (by simp)
  have hroom : q1.toNat + 9 < 2 ^ 64 := by
    obtain ⟨-, h2, -, h4, -⟩ := hS'.iw; simp only [List.length_cons, List.length_nil] at htop'; omega
  rw [riMem_eq (by omega) hroom, hE1]
  refine ⟨hS', hg, by rw [← hE1]; exact erRec_mfr h1 _, ?_⟩
  generalize hM : wrER m1 q1 _ = M at hS' hg htop' hget
  have hP : ∀ j, j < 9 → erecP M (q1.toNat + j) = ((M.arr64 EREC))[q1.toNat + j]? :=
    fun j hj => erecP_getE (by simp at htop'; omega)
  have c1 : (cq + 1).toNat = cq.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have c2 : (cq + 2).toNat = cq.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have c3 : (cq + 3).toNat = cq.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have hw : ∀ i, i < 4 → erecP M (q1.toNat + 1 + i) = erecP M (cq.toNat + i) := by
    intro i hi
    rw [show q1.toNat + 1 + i = q1.toNat + (i + 1) by omega, hP (i + 1) (by omega),
      hget (i + 1) (by simp; omega), erecP_getE (by omega), hg.erGet _ (by omega)]
    have hlt : cq.toNat + i < (m.arr64 EREC).size := by simp only [erTop] at hEtop hcq; omega
    rcases i with _ | _ | _ | _ | i
    all_goals first
      | omega
      | (simp only [Nat.add_zero, Nat.zero_add] at hlt ⊢
         simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, rdW, c1, c2, c3,
          Array.getElem?_eq_getElem hlt, Option.getD_some])
  have hcv' : decCV (erecP M) (q1.toNat + 1) = some cv := by
    rw [decCV_shift (by simpa using hw 0 (by decide)) (by simpa using hw 1 (by decide))
      (by simpa [Nat.add_assoc] using hw 2 (by decide)) (by simpa [Nat.add_assoc] using hw 3 (by decide))]
    exact ArrExt.decCV (IWGrow.erecPExtR hg) hcv
  have nk : ∀ j (hj : j < 9), nat? (erecP M) (q1.toNat + j) =
      some (([5, rdW (m.arr64 EREC) cq, rdW (m.arr64 EREC) (cq + 1), rdW (m.arr64 EREC) (cq + 2),
        rdW (m.arr64 EREC) (cq + 3), mi, rp3, reo, rel] : List Word)[j]'(by simpa using hj)).toNat := by
    intro j hj
    simp only [nat?, hP j hj, hget j (by simpa using hj)]
    rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
  have n0 := nk 0 (by decide)
  have n5 := nk 5 (by decide)
  have n6 := nk 6 (by decide)
  have n7 := nk 7 (by decide)
  have n8 := nk 8 (by decide)
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at n0 n5 n6 n7 n8
  have hru' : decRules (erecP M) reo.toNat rel.toNat = some rules := (IWGrow.erecPExtR hg).decRules hru
  simp only [decCI, Option.bind_eq_bind, n0, Option.bind_some, hcv', n5, n6, n7, n8, Option.pure_def]
  simp [hru']
-/

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- **`rules_to_erec` under the stage relation**: a fresh consecutive run of the rule records at the
old record top, decoding as the rules. -/
theorem rteW_ok (n : Nat) {m m' : Mem} {a : AState} {ro rl : Word} {r : List Word} {rules : List IRecRule}
    (h : rteW n m ro rl = some (r, m')) (hS : StageR vis fe m a)
    (hd : decPL m (rlDec m) ro.toNat rl.toNat = some rules) (_hb : ro.toNat + rl.toNat ≤ iwTop m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ r.tail.headD 0 = rl ∧
      decRules (erecP m') (r.headD 0).toNat rl.toNat = some rules ∧ MFr [] [] m m' := by
  sorry

end rel

/-! ## `cons_block_recs_push` -/

def cbpK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, m) => some ([rv.headD 0], m)

def cbpK2 (p : Prog) (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rq, m) => cbpK3 (callW p n "env_push" [vis, rq.headD 0] m)

def cbpK1 (p : Prog) (n : Nat) (vis cv mI rP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (re, m) => cbpK2 p n vis (riW m cv mI rP (re.headD 0) (re.tail.headD 0))

/-- **The model of `cons_block_recs_push`** (exec fuel). -/
def cbpW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, cv, mI, rP, ro, rl => cbpK1 p n vis cv mI rP (rteW n m ro rl)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis cv mI rP ro rl : Word) (rv rq re : List Word)
theorem cbpW_succ : cbpW p (n + 1) m vis cv mI rP ro rl = cbpK1 p n vis cv mI rP (rteW n m ro rl) := rfl
theorem cbpK1_some : cbpK1 p n vis cv mI rP (some (re, m)) =
    cbpK2 p n vis (riW m cv mI rP (re.headD 0) (re.tail.headD 0)) := rfl
theorem cbpK2_some : cbpK2 p n vis (some (rq, m)) = cbpK3 (callW p n "env_push" [vis, rq.headD 0] m) := rfl
theorem cbpK3_some : cbpK3 (some (rv, m)) = some ([rv.headD 0], m) := rfl
end arms
attribute [ind_grind] cbpW_succ cbpK1_some cbpK2_some cbpK3_some

theorem cbp_spec (p : Prog) (L : CbrLook p) (n : Nat) (s₀ : St) (vis cv mI rP ro rl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_block_recs_push" [vis, cv, mI, rP, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ cbpW p n s₀.mem vis cv mI rP ro rl = some (r, s'.mem); ⊤⦄ := by
  sorry

/-! ## The `abstract1` memo across `cons_block_recs_push` -/

theorem rteGoW_afr : ∀ (n : Nat) (m m' : Mem) (b ro rl : Word) (r : List Word),
    rteGoW n m b ro rl = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [rteGoW] at h
  | n + 1, m, m', b, ro, rl, r, h => by
    by_cases h0 : rl = 0
    · rw [rteGoW_nil (h := h0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [rteGoW_cons (h := h0)] at h
    rcases h2 : rteGoW n (cpMem m b (rdW (m.arr64 IW) ro)) (b + 11) (ro + 1) (rl - 1) with _ | ⟨r2, m2⟩ <;> simp only [h2, rteK1, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact (show AFr m (cpMem m b (rdW (m.arr64 IW) ro)) by simp only [cpMem]; afr_set).trans
      (rteGoW_afr n _ _ _ _ _ _ h2)

theorem rteW_afr {n : Nat} {m m' : Mem} {ro rl : Word} {r : List Word}
    (h : rteW n m ro rl = some (r, m')) : AFr m m' := by
  obtain _ | n := n
  · simp [rteW] at h
  by_cases hb : 4294967296 ≤ rl
  · rw [rteW.abort1 (hc1 := hb)] at h; cases h
  rw [rteW.arm1 (hc1 := hb)] at h
  rcases h1 : erAllocW m (rl * 11) with _ | ⟨b, m1⟩ <;> simp only [h1, rteW.k_erec_alloc, reduceCtorEq] at h
  rcases h2 : rteGoW n m1 b ro rl with _ | ⟨r2, m2⟩ <;> simp only [h2, rteW.k_rules_to_erec_go, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (erAllocW_afr h1).trans (rteGoW_afr n _ _ _ _ _ _ h2)

theorem riW_afr {m m' : Mem} {cv mi rp3 reo rel : Word} {r : List Word}
    (h : riW m cv mi rp3 reo rel = some (r, m')) : AFr m m' := by
  simp only [riW] at h
  split at h; · cases h
  rename_i q m1 h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (erAllocW_afr h1).trans (by simp only [riMem]; afr_set)

section rel2
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`cons_block_recs_push` under the stage relation**: the rules' run, the `.recInfo` record, pushed. -/
theorem cbpW_ok (p : Prog) (L : CbrLook p) (n : Nat) {m m' : Mem} {a : AState} {cv mI rP ro rl : Word}
    {r : List Word} {cvv : IConstantVal} {rules : List IRecRule}
    (h : cbpW p n m vis cv mI rP ro rl = some (r, m')) (hS : StageR vis fe m a)
    (hcv : decCV (erecP m) cv.toNat = some cvv)
    (hd : decPL m (rlDec m) ro.toNat rl.toNat = some rules) (hb : ro.toNat + rl.toNat ≤ iwTop m) :
    StageR (r.headD 0) (fe.push (.recInfo cvv mI.toNat rP.toNat rules)) m' a ∧ IWGrow m m' ∧
      AFr m m' := by
  obtain _ | n := n
  · simp [cbpW] at h
  rw [cbpW_succ] at h
  rcases h1 : rteW n m ro rl with _ | ⟨re, m1⟩ <;> simp only [h1, cbpK1, reduceCtorEq] at h
  obtain ⟨hS1, hg1, hre, hru, -⟩ := rteW_ok dn fe vis n h1 hS hd hb
  rw [hre] at h
  rcases h2 : riW m1 cv mI rP (re.headD 0) rl with _ | ⟨rq, m2⟩ <;> simp only [h2, cbpK2, reduceCtorEq] at h
  have hrq : rq = [rq.headD 0] := by
    simp only [riW] at h2; split at h2
    · cases h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at h2; rw [← h2.1]; rfl
  rw [hrq] at h2
  obtain ⟨hS2, hg2, -, hci⟩ := riRec_stage h2 hS1 ((IWGrow.erecPExtR hg1).decCV hcv) hru
  obtain ⟨wn, hwn, hwnl, -⟩ := decCI_name hci
  have hwn' : (rdW (m2.arr64 EREC) (rq.headD 0 + 1)).toNat < 2 ^ 32 := by
    have hq1 : (rq.headD 0 + 1).toNat = (rq.headD 0).toNat + 1 := by
      have := erecP_lt hwn; obtain ⟨-, h2', -, h4, -⟩ := hS2.iw
      rw [UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl]; exact Nat.mod_eq_of_lt (by omega)
    rw [rdW_of_get? hq1.symm (erecP_get hwn)]; exact hwnl
  rcases h3 : callW p n "env_push" [vis, rq.headD 0] m2 with _ | ⟨rv, m3⟩ <;> simp only [h3, cbpK3, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (envPush_specW p L.rp n ⟨m2, Locals.init []⟩ vis (rq.headD 0) hwn') h3
  subst hs4
  obtain ⟨hS3, hg3⟩ := envPushW_ok hW4 hS2 hci
  exact ⟨by simpa using hS3, (hg1.trans hg2).trans hg3,
    (rteW_afr h1).trans ((riW_afr h2).trans (envPushW_afr hW4))⟩
-/

end rel2

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem decRR_mono (p : Nat) : OMono (fun m => decRR m p) := by
  unfold decRR
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.decHL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply decTM_mono
    | apply OMono.bind
    | intro _)

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The major index and rule prefix of recursor `r` -/

def bmjW (m : Mem) (q r : Word) : Word :=
  if rdW (m.arr64 IW) (q + 3) ≤ r then 0
  else rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (q + 2) + r) + 2)

def brpW (m : Mem) (q r : Word) : Word :=
  if rdW (m.arr64 IW) (q + 3) ≤ r then 0
  else rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (q + 2) + r) + 1)

theorem mj_spec (p : Prog) (hp : p.lookup "block_shape_major_idx_at" = some blockShapeMajorIdxAt) (n : Nat)
    (s₀ : St) (q r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_major_idx_at" [q, r]
    ⦃fun res s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ res.headD 0 = bmjW s₀.mem q r; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeMajorIdxAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [bmjW, rdW_eq]

theorem rp_spec (p : Prog) (hp : p.lookup "block_shape_rule_prefix_at" = some blockShapeRulePrefixAt) (n : Nat)
    (s₀ : St) (q r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_rule_prefix_at" [q, r]
    ⦃fun res s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ res.headD 0 = brpW s₀.mem q r; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeRulePrefixAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [brpW, rdW_eq]

/-- The models at a shape record decoded below the tops. -/
theorem bmjW_rpW_eq {m : Mem} {q r : Word} {bs : BlockShape} (hq : DecB (fun m => decBS m q.toNat) m bs)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (bmjW m q r).toNat = bs.majorIdxAt r.toNat ∧ (brpW m q r).toNat = bs.rulePrefixAt r.toNat := by
  have h' : decBS (truncM m) q.toNat = some bs := hq
  obtain ⟨-, hrecs, -⟩ := decBS_some h'
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hrecs
  obtain ⟨-, hom⟩ := rec2IwN_trunc ho
  obtain ⟨hlt3, hlm⟩ := rec2IwN_trunc hl
  obtain ⟨e2, t2⟩ := rec2RdN (w := q) (k := 2) hom hsz
  obtain ⟨e3, t3⟩ := rec2RdN (w := q) (k := 3) (by simpa using hlm) hsz
  simp only [show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl] at e2 e3
  have hlen := decPL_length (truncM m) hd
  unfold bmjW brpW BlockShape.majorIdxAt BlockShape.rulePrefixAt
  rw [e3, e2]
  by_cases hle : UInt64.ofNat l ≤ r
  · rw [ite_eq_left hle, ite_eq_left hle]
    have : bs.recs[r.toNat]? = none := by
      rw [List.getElem?_eq_none_iff, hlen]; have := UInt64.le_iff_toNat_le.mp hle; rw [t3] at this; exact this
    rw [this]; exact ⟨rfl, rfl⟩
  rw [ite_eq_right hle, ite_eq_right hle]
  have hrl : r.toNat < l := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle); rwa [t3] at this
  obtain ⟨v, rc, hv, hrc, hget⟩ := decPL_get l o bs.recs hd r.toNat hrl
  rw [hget]
  obtain ⟨hvt, hvm⟩ := rec2IwN_trunc hv
  have hor : (UInt64.ofNat o + r).toNat = o + r.toNat := by
    rw [UInt64.toNat_add, t2]; exact Nat.mod_eq_of_lt (by
      have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at hvt; omega)
  have hrd := iwN_rdW hvm (by have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at hvt; omega)
  have e : UInt64.ofNat (o + r.toNat) = UInt64.ofNat o + r := by
    apply UInt64.toNat_inj.mp; rw [hor]; simp; have := (rdW (m.arr64 CTL) 200).toNat_lt
    simp only [iwTop] at hvt; omega
  rw [e] at hrd
  rw [hrd.1]
  obtain ⟨-, hrP, hmI, -, -⟩ := decRS_some hrc
  obtain ⟨-, hrPm⟩ := rec2IwN_trunc hrP
  obtain ⟨-, hmIm⟩ := rec2IwN_trunc hmI
  have hvv : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hrd.2
  obtain ⟨e1', t1'⟩ := rec2RdN (w := UInt64.ofNat v) (k := 1) (by rw [hvv]; exact hrPm) hsz
  obtain ⟨e2', t2'⟩ := rec2RdN (w := UInt64.ofNat v) (k := 2) (by rw [hvv]; exact hmIm) hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl] at e1' e2'
  exact ⟨by rw [e2', t2'], by rw [e1', t1']⟩

/-! ## `cons_block_recs_tf` -/

def cbrK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

def cbrK2 (k : Mem → Word → Option (List Word × Mem)) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, m) => k m (rv.headD 0)

def cbrK1 (p : Prog) (n : Nat) (vis cv mI rP : Word) (k : Mem → Word → Option (List Word × Mem)) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m) => cbrK2 k (cbpW p n m vis cv mI rP (rr.headD 0) (rr.tail.headD 0))

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `cons_block_recs_tf`** (exec fuel). -/
def cbrW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis2, pp, mm, lo, ll, vis =>
    if ll = 0 then some ([vis], m)
    else cbrK1 p n vis (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo)) (bmjW m pp mm) (brpW m pp mm)
      (fun m' v => cbrK3 (cbrW p n m' vis2 pp (mm + 1) (lo + 1) (ll - 1) v))
      (tsrW n m vis2 (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo)) (brpW m pp mm)
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo + 1)) (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo + 3)))
-/

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis2 pp mm lo ll vis cv mI rP v : Word) (r rr rv : List Word)
  (k : Mem → Word → Option (List Word × Mem))
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem cbrW_nil (h : ll = 0) : cbrW p (n + 1) m vis2 pp mm lo ll vis = some ([vis], m) := by simp [cbrW, h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem cbrW_cons (h : ¬ ll = 0) : cbrW p (n + 1) m vis2 pp mm lo ll vis =
    cbrK1 p n vis (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo)) (bmjW m pp mm) (brpW m pp mm)
      (fun m' v => cbrK3 (cbrW p n m' vis2 pp (mm + 1) (lo + 1) (ll - 1) v))
      (tsrW n m vis2 (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo)) (brpW m pp mm)
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo + 1)) (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo + 3))) := by simp [cbrW, h]
-/
theorem cbrK1_some : cbrK1 p n vis cv mI rP k (some (rr, m)) =
    cbrK2 k (cbpW p n m vis cv mI rP (rr.headD 0) (rr.tail.headD 0)) := rfl
theorem cbrK2_some : cbrK2 k (some (rv, m)) = k m (rv.headD 0) := rfl
theorem cbrK3_some : cbrK3 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
-- ronsync2 stage 2: attribute [ind_grind] cbrW_nil cbrW_cons cbrK1_some cbrK2_some cbrK3_some


section rel
variable (dn : NIdx → Option ConLeche.Name)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem cbrW_ok (p : Prog) (L : CbrLook p) (n : Nat) : ∀ {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {vis2 pp mm lo ll : Word} {r : List Word} {bs : BlockShape} {xs : List (IConstantVal × TargetMajor × List EIdx)},
    cbrW p n m vis2 pp mm lo ll vis = some (r, m') → StageR vis fe m a →
    DecB (fun m => decBS m pp.toNat) m bs → PSlR decRR xs lo ll m → mm.toNat + ll.toNat < 2 ^ 64 →
    AbsOK m →
    ∃ fe' a', (ConRon.Arena.consBlockRecsTF vis2.toNat bs mm.toNat xs fe).run a = .ok (fe', a') ∧
      StageR (r.headD 0) fe' m' a' ∧ IWGrow m m' ∧ AbsOK m' := by
  induction n with
  | zero => intro m m' a vis fe vis2 pp mm lo ll r bs xs h; simp [cbrW] at h
  | succ n ih =>
  intro m m' a vis fe vis2 pp mm lo ll r bs xs h hS hbs hxs hml hA
  by_cases hl : ll = 0
  · rw [cbrW_nil (h := hl)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hl
    have : xs = [] := by
      have := decPL_length _ (hxs.1.get (OMono.decPL decRR_mono _ _)); simpa using this
    subst this
    exact ⟨fe, a, rfl, hS, IWGrow.refl _, hA⟩
  rw [cbrW_cons (h := hl)] at h
  have hsz := hS.iw.iwSize
  obtain ⟨x, ys, rfl, hx, hys⟩ := hxs.uncons hl hsz
  obtain ⟨cvv, TM, rhss⟩ := x
  generalize hT : rdW (m.arr64 IW) lo = trip at h hx
  -- the record's fields
  have hx' : decRR (truncM m) trip.toNat = some (cvv, TM, rhss) := hx
  simp only [decRR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hx'
  obtain ⟨cvp, hcvp, cv', hcv', mp, hmp, TM', hTM', rh', hrh', he⟩ := hx'
  simp only [Prod.mk.injEq] at he; obtain ⟨e1', e2', e3'⟩ := he
  rw [e1'] at hcv'; rw [e2'] at hTM'; rw [e3'] at hrh'
  obtain ⟨-, hcvpm⟩ := rec2IwN_trunc (i := trip.toNat + 0) (by simpa using hcvp)
  obtain ⟨e0, t0⟩ := rec2RdN (w := trip) (k := 0) hcvpm hsz
  obtain ⟨-, hmpm⟩ := rec2IwN_trunc hmp
  obtain ⟨e1, t1⟩ := rec2RdN (w := trip) (k := 1) hmpm hsz
  obtain ⟨o, l, ho, hl', hd⟩ := decAt_some hrh'
  obtain ⟨-, hom⟩ := rec2IwN_trunc ho
  obtain ⟨-, hlm⟩ := rec2IwN_trunc hl'
  obtain ⟨e2, t2⟩ := rec2RdN (w := trip) (k := 2) hom hsz
  obtain ⟨e3, t3⟩ := rec2RdN (w := trip) (k := 3) (by simpa [Nat.add_assoc] using hlm) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl,
    show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl, UInt64.add_zero] at e0 e1 e2 e3
  rw [e0, e1, e2, e3] at h
  have hM : DecB (fun m => decTM m (UInt64.ofNat mp : Word).toNat) m TM := by
    show decTM (truncM m) _ = some TM; rw [t1]; exact hTM'
  have hrh : DecB (fun m => decHL m (UInt64.ofNat o : Word).toNat (UInt64.ofNat l : Word).toNat) m rhss := by
    show decHL (truncM m) _ _ = some rhss; rw [t2, t3]; exact hd
  have hcvE : decCV (erecP m) (UInt64.ofNat cvp : Word).toNat = some cvv := by rw [t0]; exact decCVp_truncM hcv'
  obtain ⟨hmj, hrp⟩ := bmjW_rpW_eq (r := mm) hbs hsz
  -- the stored rules, at the constructors' view
  rcases h1 : tsrW n m vis2 (UInt64.ofNat cvp) (brpW m pp mm) (UInt64.ofNat mp) (UInt64.ofNat o) (UInt64.ofNat l) with _ | ⟨rr, m1⟩ <;> simp only [h1, cbrK1, reduceCtorEq] at h
  obtain ⟨rules, a1, run1, hd1, hb1, hS1, hg1, hA1⟩ := tsrW_ok dn (fe.restrictTo vis2.toNat) vis2 n h1
    (hS.restrict vis2) hM hrh hA (cvv := cvv)
  have hS1' : StageR vis fe m1 a1 := hS1.unrestrict hS.check.env.vis
  rw [hrp] at run1
  rcases h2 : cbpW p n m1 vis (UInt64.ofNat cvp) (bmjW m pp mm) (brpW m pp mm) (rr.headD 0) (rr.tail.headD 0) with _ | ⟨rv, m2⟩ <;> simp only [h2, cbrK2, reduceCtorEq] at h
  obtain ⟨hS2, hg2, hf2⟩ := cbpW_ok dn fe vis p L n h2 hS1' ((IWGrow.erecPExtR hg1).decCV hcvE) hd1 hb1
  rw [hmj, hrp] at hS2
  rcases h3 : cbrW p n m2 vis2 pp (mm + 1) (lo + 1) (ll - 1) (rv.headD 0) with _ | ⟨r3, m3⟩ <;> simp only [h3, cbrK3, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hg12 := hg1.trans hg2
  have hl0 : ll.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
  have hmm1 : (mm + 1).toNat = mm.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hll1 : (ll - 1).toNat = ll.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  obtain ⟨fe', a3, run3, hS3, hg3, hA3⟩ := ih h3 hS2 (hbs.grow (decBS_mono _) hg12)
    (hys.grow (fun q => decRR_mono q) hg12) (by rw [hmm1, hll1]; omega) (hf2 hA1)
  refine ⟨fe', a3, ?_, by simpa using hS3, hg12.trans hg3, hA3⟩
  rw [hmm1] at run3
  simp only [ConRon.Arena.consBlockRecsTF, StateT.run_bind, run1, except_ok_bind]
  exact run3
-/

end rel


end L.Ind

end

end
