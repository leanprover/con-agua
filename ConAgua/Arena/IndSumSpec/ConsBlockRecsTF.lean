module

public import ConAgua.Arena.IndSumSpec.TsrW
public import ConAgua.Arena.RecGenSpec.DecRR
import ConAgua.Arena.IndInstallSpec.IcbiW
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.IndInstallSpec.InstallIwB
import ConAgua.Arena.IndInstallSpec.DomsW
import all ConAgua.Arena.IndParts
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.RecCheck

@[expose] public section

/-!
# ConsBlockRecsTF: `ConRon.Arena.consBlockRecsTF`

The models and stage lemmas of `block_rec_infos_tf`'s record writers: `rule_copy`, `rules_to_erec(_go)`
(the copied run decodes as the rules), `rec_info_rec` (a 10-word `.recInfo` record at `erec_put`);
`rec_k_expected` (`rkW_ok`), and `block_rec_infos_tf` itself (`briW_ok`, `blockRecInfosTF_refines`:
the records at a slice of `EREC` pointers, `decPL m (decCI (erecP m))`).
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
/-- After `all_level_params_defined`. -/
def sctK2 (rest : Mem → Option (List Word × Mem)) (vis nP b r1 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m) => sctK3 rest nP b r1 (r2.headD 0) (crfF m [vis, b])
/-- After `has_fvar_fast`. -/
def sctK1 (c : CallM) (n : Nat) (rest : Mem → Option (List Word × Mem)) (vis nP lo ll b : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => sctK2 rest vis nP b (r1.headD 0) (c n "all_level_params_defined" [lo, ll, b] m)

/-- **The model of `check_struct_proj_table_scoped(vis, nP, lo, ll, bO, bL)`** at exec fuel `n`,
reading `all_level_params_defined` through `c` (`stubCall`: the stub contract; `realCall p`: the
program's own call, `IndRealSctC.lean`). -/
def sctW (c : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, nP, lo, ll, bO, bL =>
    if bL = 0 then some ([1], m)
    else sctK1 c n (fun m' => sctW c n m' vis nP lo ll (bO + 1) (bL - 1)) vis nP lo ll (rdW (m.arr64 IW) bO)
      (hffF m [CWF, rdW (m.arr64 IW) bO])

section arms
variable (c : CallM) (rest : Mem → Option (List Word × Mem)) (n : Nat) (m : Mem)
  (vis nP lo ll bO bL b r1 r2 r3 : Word) (r : List Word)
theorem sctW_nil (h : bL = 0) : sctW c (n + 1) m vis nP lo ll bO bL = some ([1], m) := by simp [sctW, h]
theorem sctW_cons (h : bL ≠ 0) : sctW c (n + 1) m vis nP lo ll bO bL =
    sctK1 c n (fun m' => sctW c n m' vis nP lo ll (bO + 1) (bL - 1)) vis nP lo ll (rdW (m.arr64 IW) bO)
      (hffF m [CWF, rdW (m.arr64 IW) bO]) := by simp [sctW, h]
theorem sctK5_some : sctK5 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem sctK4_yes (h : r1 = 0 ∧ r2 = 1 ∧ r3 = 1 ∧ r.headD 0 = 1) :
    sctK4 rest r1 r2 r3 (some (r, m)) = sctK5 (rest m) := by simp only [sctK4]; rw [ite_eq_left h]
theorem sctK4_no (h : ¬ (r1 = 0 ∧ r2 = 1 ∧ r3 = 1 ∧ r.headD 0 = 1)) :
    sctK4 rest r1 r2 r3 (some (r, m)) = some ([0], m) := by simp only [sctK4]; rw [ite_eq_right h]
theorem sctK3_some : sctK3 rest nP b r1 r2 (some (r, m)) =
    sctK4 rest r1 r2 (r.headD 0) (lbbF m [CWF, nP + 1, b]) := rfl
theorem sctK2_some : sctK2 rest vis nP b r1 (some (r, m)) =
    sctK3 rest nP b r1 (r.headD 0) (crfF m [vis, b]) := rfl
theorem sctK1_some : sctK1 c n rest vis nP lo ll b (some (r, m)) =
    sctK2 rest vis nP b (r.headD 0) (c n "all_level_params_defined" [lo, ll, b] m) := rfl
end arms
attribute [ind_grind] sctW_nil sctW_cons sctK5_some sctK4_yes sctK4_no sctK3_some sctK2_some sctK1_some

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

/-- A rule record copied word for word: each word it reads at `q` present at `q'`, its fire's
slices in a larger pool. -/
theorem decRule_copy {R R' : Nat → Option Word} {q q' : Nat} {rl : IRecRule} (h : decRule R q = some rl)
    (hext : ArrExt R R') (hw : ∀ i, i < 11 → ∀ v, R (q + i) = some v → R' (q' + i) = some v) :
    decRule R' q' = some rl := by
  have nat' : ∀ i, i < 11 → ∀ x, nat? R (q + i) = some x → nat? R' (q' + i) = some x := by
    intro i hi x hx
    simp only [L.Arena.nat?, Option.map_eq_some_iff] at hx ⊢
    obtain ⟨v, hv, rfl⟩ := hx; exact ⟨v, hw i hi v hv, rfl⟩
  have hd' : ∀ {k : IdxKind} i, i < 11 → ∀ x : Idx k, hd? R (q + i) = some x → hd? R' (q' + i) = some x := by
    intro k i hi x hx
    simp only [L.Arena.hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
    obtain ⟨v, hv, hx⟩ := hx; exact ⟨v, hw i hi v hv, hx⟩
  have hl' : ∀ {k : IdxKind} i, i + 1 < 11 → ∀ xs : List (Idx k), hlist? R (q + i) = some xs →
      hlist? R' (q' + i) = some xs := by
    intro k i hi xs hx
    simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
    obtain ⟨o, ho, c, hc, hs⟩ := hx
    refine ⟨o, nat' i (by omega) o ho, c, ?_, hext.hslice? hs⟩
    have := nat' (i + 1) hi c (by simpa [Nat.add_assoc] using hc)
    simpa [Nat.add_assoc] using this
  unfold L.Arena.decRule at h ⊢
  cases h3 : L.Arena.nat? R (q + 3) with
  | none => simp [h3] at h
  | some t =>
    rw [nat' 3 (by decide) t h3]; rw [h3] at h
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some] at h ⊢
    have tail : ∀ (f : IRecRuleFire), (do
        let ctor ← L.Arena.hd? R q
        let nfields ← L.Arena.nat? R (q + 1)
        let rhs ← L.Arena.hd? R (q + 8)
        pure ({ ctor, nfields, fire := f, rhs } : IRecRule)) = some rl →
        (do
        let ctor ← L.Arena.hd? R' q'
        let nfields ← L.Arena.nat? R' (q' + 1)
        let rhs ← L.Arena.hd? R' (q' + 8)
        pure ({ ctor, nfields, fire := f, rhs } : IRecRule)) = some rl := by
      intro f hf
      simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hf ⊢
      obtain ⟨c, hc, nf, hnf, r, hr, e'⟩ := hf
      exact ⟨c, by simpa using hd' 0 (by decide) c (by simpa using hc), nf, nat' 1 (by decide) nf hnf,
        r, hd' 8 (by decide) r hr, e'⟩
    match t, h with
    | 0, h => simp only at h ⊢; exact tail _ h
    | 1, h =>
      cases hy : L.Arena.hlist? (k := .level) R (q + 4) with
      | none => simp [hy] at h
      | some y =>
        cases hz : L.Arena.hlist? (k := .expr) R (q + 6) with
        | none => simp [hy, hz] at h
        | some z =>
          rw [hy, hz] at h; rw [hl' 4 (by decide) y hy, hl' 6 (by decide) z hz]
          simp only [Option.bind_some] at h ⊢
          exact tail _ h
    | 2, h =>
      cases hy : L.Arena.hlist? (k := .level) R (q + 4) with
      | none => simp [hy] at h
      | some y =>
        rw [hy] at h; rw [hl' 4 (by decide) y hy]
        simp only [Option.bind_some] at h ⊢
        exact tail _ h
    | t + 3, h => simp at h

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

/-- The memory after one record's eleven `erec_put` copies (each copy reads the memory of its time). -/
def cpMem (m : Mem) (b old : Word) : Mem :=
  let m1 := erecPutMem m b (erRd m old)
  let m2 := erecPutMem m1 (b + 1) (erRd m1 (old + 1))
  let m3 := erecPutMem m2 (b + 2) (erRd m2 (old + 2))
  let m4 := erecPutMem m3 (b + 3) (erRd m3 (old + 3))
  let m5 := erecPutMem m4 (b + 4) (erRd m4 (old + 4))
  let m6 := erecPutMem m5 (b + 5) (erRd m5 (old + 5))
  let m7 := erecPutMem m6 (b + 6) (erRd m6 (old + 6))
  let m8 := erecPutMem m7 (b + 7) (erRd m7 (old + 7))
  let m9 := erecPutMem m8 (b + 8) (erRd m8 (old + 8))
  let m10 := erecPutMem m9 (b + 9) (erRd m9 (old + 9))
  erecPutMem m10 (b + 10) (erRd m10 (old + 10))

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

/-- The lookups of `block_rec_infos_tf`. -/
structure CbrLook (p : Prog) : Prop where
  tsr : TsrLook p
  rp : RecProg p
  rc : p.lookup "rule_copy" = some ruleCopy
  rteg : p.lookup "rules_to_erec_go" = some rulesToErecGo
  rir : p.lookup "rec_info_rec" = some recInfoRec
  rte : p.lookup "rules_to_erec" = some rulesToErec
  mi : p.lookup "block_shape_major_idx_at" = some blockShapeMajorIdxAt
  rpa : p.lookup "block_shape_rule_prefix_at" = some blockShapeRulePrefixAt
  rke : p.lookup "rec_k_expected" = some recKExpected
  bri : p.lookup "block_rec_infos_tf" = some blockRecInfosTF

theorem rc_spec (p : Prog) (L : CbrLook p) (hpu : p.lookup "erec_put" = some erecPut) (n : Nat)
    (s₀ : St) (b old : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rule_copy" [b, old]
    ⦃fun r s' => LocEq s' s₀ ∧ rcpW s₀.mem b old = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.rc]
  simp only [callFn, ruleCopy]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erecPut_specW p hpu n] <;>
      finish [rcpW, cpMem, erRd]

theorem rteGo_spec (p : Prog) (L : CbrLook p) (hpu : p.lookup "erec_put" = some erecPut) (n : Nat) :
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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, rc_spec p L hpu n, ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

l_model rte_spec (p : Prog) (hL : CbrLook p) (hpu : p.lookup "erec_put" = some erecPut)
  fns [hL.rte ↦ rteW]
  specs [erecAlloc_specW p hL.tsr.ea n, rteGo_spec p hL hpu n]
  grind [arena_grind]

/-! ## `rules_to_erec`: the copied run decodes as the rules -/

theorem ofNat_shift (q : Word) (a j : Nat) : q + UInt64.ofNat a + UInt64.ofNat j = q + UInt64.ofNat (a + j) := by
  rw [UInt64.ofNat_add]; ac_rfl

theorem ErApart.shift {q x : Word} {a k : Nat} (h : ErApart q (a + k) x) : ErApart (q + UInt64.ofNat a) k x :=
  fun j hj => by rw [ofNat_shift]; exact h (a + j) (by omega)

/-- `EREC⦃x⦄` across a run of `erec_put`s elsewhere. -/
theorem erRd_wrER_ne : ∀ (ws : List Word) (m : Mem) (q x : Word), ErApart q ws.length x →
    erRd (wrER m q ws) x = erRd m x
  | [], _, _, _, _ => rfl
  | w :: ws, m, q, x, h => by
    simp only [wrER]
    rw [erRd_wrER_ne ws _ (q + 1) x (fun j hj => by
      have := h (j + 1) (by simp; omega)
      rwa [show q + UInt64.ofNat (j + 1) = q + 1 + UInt64.ofNat j by rw [UInt64.ofNat_add]; ac_rfl] at this)]
    exact erRd_erecPutMem_ne (by simpa using h 0 (by simp))

/-- The eleven words of the record at `old`. -/
def recWords (m : Mem) (old : Word) : List Word :=
  [erRd m old, erRd m (old + 1), erRd m (old + 2), erRd m (old + 3), erRd m (old + 4), erRd m (old + 5),
    erRd m (old + 6), erRd m (old + 7), erRd m (old + 8), erRd m (old + 9), erRd m (old + 10)]

theorem recWords_length (m : Mem) (old : Word) : (recWords m old).length = 11 := rfl

theorem recWords_get (m : Mem) (old : Word) (i : Nat) (hi : i < 11) :
    (recWords m old)[i]? = some (erRd m (old + UInt64.ofNat i)) := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [recWords] <;> rfl

theorem recWords_congr {m m' : Mem} {old : Word}
    (h : ∀ i < 11, erRd m' (old + UInt64.ofNat i) = erRd m (old + UInt64.ofNat i)) :
    recWords m' old = recWords m old := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 11
  · rw [recWords_get _ _ _ hi, recWords_get _ _ _ hi, h i hi]
  · rw [List.getElem?_eq_none (by simp [recWords_length]; omega),
      List.getElem?_eq_none (by simp [recWords_length]; omega)]

/-- The words of the records the pointers `IW[ro ‥ ro + k)` point to, in order. -/
def ruleWords (m : Mem) (ro : Word) : Nat → List Word
  | 0 => []
  | k + 1 => recWords m (rdW (m.arr64 IW) ro) ++ ruleWords m (ro + 1) k

theorem ruleWords_length (m : Mem) : ∀ (ro : Word) (k : Nat), (ruleWords m ro k).length = 11 * k
  | _, 0 => rfl
  | ro, k + 1 => by simp [ruleWords, recWords_length, ruleWords_length m (ro + 1) k]; omega

theorem ruleWords_get (m : Mem) : ∀ (ro : Word) (k j i : Nat), j < k → i < 11 →
    (ruleWords m ro k)[11 * j + i]? = some (erRd m (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + UInt64.ofNat i))
  | _, 0, _, _, hj, _ => absurd hj (by omega)
  | ro, k + 1, 0, i, _, hi => by
    simp only [ruleWords, Nat.mul_zero, Nat.zero_add, show (UInt64.ofNat 0 : Word) = 0 from rfl, UInt64.add_zero]
    rw [List.getElem?_append_left (by simp [recWords_length]; omega), recWords_get _ _ _ hi]
  | ro, k + 1, j + 1, i, hj, hi => by
    simp only [ruleWords]
    rw [List.getElem?_append_right (by simp [recWords_length]; omega)]
    have e : 11 * (j + 1) + i - (recWords m (rdW (m.arr64 IW) ro)).length = 11 * j + i := by
      simp [recWords_length]; omega
    rw [e, ruleWords_get m (ro + 1) k j i (by omega) hi]
    have e2 : ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := by rw [UInt64.ofNat_add]; ac_rfl
    rw [e2]

/-- `IW` the same and the source records' words read the same: the record words agree. -/
theorem ruleWords_congr {m m' : Mem} (hI : m'.arr64 IW = m.arr64 IW) :
    ∀ (ro : Word) (k : Nat), (∀ j < k, ∀ i < 11, erRd m' (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + UInt64.ofNat i) =
      erRd m (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + UInt64.ofNat i)) →
      ruleWords m' ro k = ruleWords m ro k
  | _, 0, _ => rfl
  | ro, k + 1, h => by
    simp only [ruleWords, hI]
    congr 1
    · exact recWords_congr (fun i hi => by simpa using h 0 (by omega) i hi)
    · exact ruleWords_congr hI (ro + 1) k (fun j hj i hi => by
        have e : ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := by
          rw [UInt64.ofNat_add]; ac_rfl
        rw [e]; exact h (j + 1) (by omega) i hi)

theorem cpMem_frame (m : Mem) (b old : Word) : MemFrame [EREC, tier1 EREC] [] m (cpMem m b old) := by
  simp only [cpMem]
  repeat' refine MemFrame.trans ?_ (erecPutMem_frame _ _ _)
  exact MemFrame.refl _ _ _

theorem cpMem_eq {m : Mem} {b old : Word} (hfr : ∀ i < 11, ErApart b 11 (old + UInt64.ofNat i)) :
    cpMem m b old = wrER m b (recWords m old) := by
  have hA : ∀ i j : Word, i.toNat < 11 → j.toNat < 11 →
      erTier (old + i) ≠ erTier (b + j) ∨ erOff (old + i) ≠ erOff (b + j) := by
    intro i j hi hj
    have := hfr i.toNat hi j.toNat hj
    simpa using this
  have h00 : erTier old ≠ erTier b ∨ erOff old ≠ erOff b := by simpa using hA 0 0 (by decide) (by decide)
  have h0 : ∀ j : Word, j.toNat < 11 → erTier old ≠ erTier (b + j) ∨ erOff old ≠ erOff (b + j) :=
    fun j hj => by simpa using hA 0 j (by decide) hj
  have hB : ∀ i : Word, i.toNat < 11 → erTier (old + i) ≠ erTier b ∨ erOff (old + i) ≠ erOff b :=
    fun i hi => by simpa using hA i 0 hi (by decide)
  simp only [cpMem, wrER, recWords]
  rw [show b + 1 + 1 = b + 2 by ac_rfl, show b + 2 + 1 = b + 3 by ac_rfl,
    show b + 3 + 1 = b + 4 by ac_rfl, show b + 4 + 1 = b + 5 by ac_rfl,
    show b + 5 + 1 = b + 6 by ac_rfl, show b + 6 + 1 = b + 7 by ac_rfl,
    show b + 7 + 1 = b + 8 by ac_rfl, show b + 8 + 1 = b + 9 by ac_rfl,
    show b + 9 + 1 = b + 10 by ac_rfl]
  simp (disch := first
    | exact h00
    | (apply h0; decide)
    | (apply hB; decide)
    | (apply hA <;> decide)) only [erRd_erecPutMem_ne]

theorem rteGoW_mem : ∀ (n : Nat) (m m' : Mem) (b ro rl : Word) (r : List Word),
    rteGoW n m b ro rl = some (r, m') →
    (∀ j < rl.toNat, ∀ i < 11, ErApart b (11 * rl.toNat) (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + UInt64.ofNat i)) →
    m' = wrER m b (ruleWords m ro rl.toNat)
  | 0, _, _, _, _, _, _, h, _ => by simp [rteGoW] at h
  | n + 1, m, m', b, ro, rl, r, h, hfr => by
    by_cases h0 : rl = 0
    · rw [rteGoW_nil (h := h0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      subst h0; rw [← h.2]; simp [ruleWords, wrER]
    rw [rteGoW_cons (h := h0)] at h
    have hl0 : rl.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
    have hl1 : (rl - 1).toNat = rl.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
    rcases h2 : rteGoW n (cpMem m b (rdW (m.arr64 IW) ro)) (b + 11) (ro + 1) (rl - 1) with _ | ⟨r2, m2⟩ <;>
      simp only [h2, rteK1, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    have hsrc : ∀ j, ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := fun j => by
      rw [UInt64.ofNat_add]; ac_rfl
    have hfr0 : ∀ i < 11, ErApart b 11 (rdW (m.arr64 IW) ro + UInt64.ofNat i) := fun i hi => by
      have := hfr 0 (by omega) i hi
      simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at this
      exact this.mono (by omega)
    rw [cpMem_eq hfr0] at h2
    have hI : (wrER m b (recWords m (rdW (m.arr64 IW) ro))).arr64 IW = m.arr64 IW :=
      (wrER_frame _ m b).arr IW (by decide) (by decide)
    have h11 : b + 11 = b + UInt64.ofNat 11 := rfl
    have ih := rteGoW_mem n _ m2 (b + 11) (ro + 1) (rl - 1) r2 h2 (fun j hj i hi => by
      rw [hI, hsrc, h11]
      exact ErApart.shift (by rw [hl1] at hj; exact (hfr (j + 1) (by omega) i hi).mono (by omega)))
    rw [ih, hl1, ruleWords_congr hI (ro + 1) (rl.toNat - 1) (fun j hj i hi => by
      rw [hsrc]
      exact erRd_wrER_ne _ _ _ _ ((hfr (j + 1) (by omega) i hi).mono (by simp [recWords_length]; omega)))]
    conv => rhs; rw [show rl.toNat = (rl.toNat - 1) + 1 by omega]
    simp only [ruleWords]
    rw [wrER_append, recWords_length]
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

/-- **`rules_to_erec` under the stage relation**: a fresh run of copies of the rule records (every
source record's eleven words in the record pool), decoding as the rules. -/
theorem rteW_ok {vis : Word} {fe : IFEnv} (n : Nat) {m m' : Mem} {a : AState} {ro rl : Word}
    {r : List Word} {rules : List IRecRule}
    (h : rteW n m ro rl = some (r, m')) (hS : StageR vis fe m a)
    (hd : decPL m (rlDec m) ro.toNat rl.toNat = some rules)
    (hall : ∀ j < rl.toNat, ∀ v, iwN m (ro.toNat + j) = some v → ∀ i < 11, ∃ w, erecP m (v + i) = some w) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ r.tail.headD 0 = rl ∧
      decRules (erecP m') (r.headD 0).toNat rl.toNat = some rules := by
  obtain _ | n := n
  · simp [rteW] at h
  by_cases hbig : 4294967296 ≤ rl
  · rw [rteW.abort1 (hc1 := hbig)] at h; cases h
  rw [rteW.arm1 (hc1 := hbig)] at h
  have hrl : rl.toNat < 2 ^ 32 := by rw [UInt64.le_iff_toNat_le] at hbig; simp at hbig; omega
  rcases ha : erAllocW m (rl * 11) with _ | ⟨b, m1⟩ <;> simp only [ha, rteW.k_erec_alloc, reduceCtorEq] at h
  rcases h1 : rteGoW n m1 b ro rl with _ | ⟨r1, m2⟩ <;> simp only [h1, rteW.k_rules_to_erec_go, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hk : (rl * 11).toNat = 11 * rl.toNat := by
    rw [UInt64.toNat_mul]; simp; omega
  obtain ⟨-, hf1, -⟩ := erAllocW_spec ha hS.iw
  have hI1 : m1.arr64 IW = m.arr64 IW := hf1.arr IW (by simp) (by decide)
  have hr1 : ∀ x, erRd m1 x = erRd m x := fun x => by
    unfold erRd; rw [hf1.arr _ (by simp) (by rw [tierA_EREC]; split <;> decide)]
  have hsz := hS.iw.iwSize
  -- the source records: their pointers, their words in the old pool
  have hsrc : ∀ j < rl.toNat, ∃ v, iwN m (ro.toNat + j) = some v ∧
      rdW (m.arr64 IW) (ro + UInt64.ofNat j) = UInt64.ofNat v ∧ (UInt64.ofNat v : Word).toNat = v := by
    intro j hj
    obtain ⟨v, -, hv, -, -⟩ := decPL_get rl.toNat ro.toNat rules hd j hj
    obtain ⟨e, hlt⟩ := iwN_rdW_at (w := ro) (k := j) hv hsz
    exact ⟨v, hv, e, UInt64.toNat_ofNat_of_lt' hlt⟩
  have hword : ∀ j < rl.toNat, ∀ i < 11, ∃ v w, iwN m (ro.toNat + j) = some v ∧
      erecP m (v + i) = some w ∧
      erRd m (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + UInt64.ofNat i) = w ∧
      (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + UInt64.ofNat i).toNat = v + i := by
    intro j hj i hi
    obtain ⟨v, hv, e, hvv⟩ := hsrc j hj
    obtain ⟨w, hw⟩ := hall j hj v hv i hi
    rw [← hvv] at hw
    obtain ⟨r1, e1⟩ := erRd_add hw (by omega)
    exact ⟨v, w, hv, by rw [← hvv]; exact hw, by rw [e]; exact r1, by rw [e, e1, hvv]⟩
  have hfr : ∀ j < rl.toNat, ∀ i < 11,
      ErApart b (11 * rl.toNat) (rdW (m1.arr64 IW) (ro + UInt64.ofNat j) + UInt64.ofNat i) := by
    intro j hj i hi k hk'
    obtain ⟨v, w, -, hw, -, ht⟩ := hword j hj i hi
    rw [hI1]
    exact erFresh ha hS.iw (x := rdW (m.arr64 IW) (ro + UInt64.ofNat j) + UInt64.ofNat i)
      (by rw [ht]; exact hw) (by rw [hk]; exact hk')
  have hm2 := rteGoW_mem n m1 m2 b ro rl r1 h1 hfr
  subst hm2
  have hrw : ruleWords m1 ro rl.toNat = ruleWords m ro rl.toNat :=
    ruleWords_congr hI1 ro rl.toNat (fun _ _ _ _ => hr1 _)
  rw [hrw]
  obtain ⟨hS1, hg1, -, -, -, -, hget1⟩ := erRec_stage ha hS (ruleWords m ro rl.toNat)
    (by rw [ruleWords_length, hk])
  refine ⟨hS1, hg1, rfl, ?_⟩
  simp only [List.headD_cons]
  generalize hM : wrER m1 b (ruleWords m ro rl.toNat) = M at hS1 hg1 hget1 ⊢
  have hlen := decPL_length (m := m) hd
  unfold decRules
  rw [← hlen]
  apply mapM_range_some
  intro j hj
  rw [hlen] at hj
  obtain ⟨v, rlj, hvj, hfj, hgj⟩ := decPL_get rl.toNat ro.toNat rules hd j hj
  have hrj : rules[j] = rlj := by
    rw [List.getElem?_eq_getElem (by omega)] at hgj; exact Option.some.inj hgj
  rw [hrj]
  refine decRule_copy hfj (IWGrow.ext hg1) (fun i hi w hw => ?_)
  obtain ⟨v', w', hv', hw', hrd, -⟩ := hword j hj i hi
  rw [hvj] at hv'; cases hv'
  rw [hw] at hw'; cases hw'
  rw [show b.toNat + 11 * j + i = b.toNat + (11 * j + i) by omega,
    hget1 (11 * j + i) (by rw [ruleWords_length]; omega), ruleWords_get m ro rl.toNat j i hj hi, hrd]

/-! ## `rec_info_rec` -/

/-- The memory after `rec_info_rec`'s ten `erec_put`s (each copy reads the memory of its time). -/
def riMem (m1 : Mem) (q cv mi rp isK reo rel : Word) : Mem :=
  let m2 := erecPutMem m1 q 5
  let m3 := erecPutMem m2 (q + 1) (erRd m2 cv)
  let m4 := erecPutMem m3 (q + 2) (erRd m3 (cv + 1))
  let m5 := erecPutMem m4 (q + 3) (erRd m4 (cv + 2))
  let m6 := erecPutMem m5 (q + 4) (erRd m5 (cv + 3))
  erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem m6 (q + 5) mi) (q + 6) rp) (q + 7) reo)
    (q + 8) rel) (q + 9) isK

/-- **The model of `rec_info_rec(cv, mI, rP, isK, reo, rel)`.** -/
def riW (m : Mem) (cv mi rp isK reo rel : Word) : Option (Word × Mem) :=
  match erAllocW m 10 with
  | none => none
  | some (q, m1) =>
    if 4294967296 ≤ erRd (riMem m1 q cv mi rp isK reo rel) (q + 1) then none
    else some (q, riMem m1 q cv mi rp isK reo rel)

theorem ri_spec (p : Prog) (L : CbrLook p) (hpu : p.lookup "erec_put" = some erecPut) (n : Nat) (s₀ : St)
    (cv mi rp isK reo rel : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec_info_rec" [cv, mi, rp, isK, reo, rel]
    ⦃fun r s' => LocEq s' s₀ ∧ riW s₀.mem cv mi rp isK reo rel = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.rir]
  simp only [callFn, recInfoRec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        erecAlloc_specW p L.tsr.ea n, erecPut_specW p hpu n] <;>
      finish (gen := 30) (instances := 5000) [riW, riMem, erRd]

theorem riMem_eq {m1 : Mem} {q cq mi rp isK reo rel : Word}
    (hfr : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], ∀ j < 10,
      erTier x ≠ erTier (q + UInt64.ofNat j) ∨ erOff x ≠ erOff (q + UInt64.ofNat j)) :
    riMem m1 q cq mi rp isK reo rel = wrER m1 q [5, erRd m1 cq, erRd m1 (cq + 1), erRd m1 (cq + 2),
      erRd m1 (cq + 3), mi, rp, reo, rel, isK] := by
  have f0 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier q ∨ erOff x ≠ erOff q :=
    fun x hx => by simpa using hfr x hx 0 (by decide)
  have f1 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier (q + 1) ∨ erOff x ≠ erOff (q + 1) :=
    fun x hx => hfr x hx 1 (by decide)
  have f2 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier (q + 2) ∨ erOff x ≠ erOff (q + 2) :=
    fun x hx => hfr x hx 2 (by decide)
  have f3 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier (q + 3) ∨ erOff x ≠ erOff (q + 3) :=
    fun x hx => hfr x hx 3 (by decide)
  simp only [riMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl, show q + 6 + 1 = q + 7 by ac_rfl,
    show q + 7 + 1 = q + 8 by ac_rfl, show q + 8 + 1 = q + 9 by ac_rfl]
  simp (disch := first
    | exact f0 _ (by simp) | exact f1 _ (by simp) | exact f2 _ (by simp) | exact f3 _ (by simp))
    only [erRd_erecPutMem_ne]

/-- **`rec_info_rec` under the stage relation**: a fresh `.recInfo` record of the constant at `cq`,
its K flag `isK != 0` and its rules the run `(reo, rel)`. -/
theorem riRec_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq mi rp isK reo rel q : Word} {cv : IConstantVal} {rules : List IRecRule}
    (h : riW m cq mi rp isK reo rel = some (q, m'))
    (hS : StageR vis fe m a) (hcv : decCV (erecP m) cq.toNat = some cv)
    (hru : decRules (erecP m) reo.toNat rel.toNat = some rules) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') q.toNat = some (.recInfo cv mi.toNat rp.toNat (isK != 0) rules) := by
  rcases h1 : erAllocW m 10 with _ | ⟨q1, m1⟩
  · simp [riW, h1] at h
  have e : riW m cq mi rp isK reo rel = if 4294967296 ≤ erRd (riMem m1 q1 cq mi rp isK reo rel) (q1 + 1)
      then none else some (q1, riMem m1 q1 cq mi rp isK reo rel) := by simp [riW, h1]
  rw [e] at h
  split at h
  · cases h
  obtain ⟨rfl, rfl⟩ : q1 = q ∧ riMem m1 q1 cq mi rp isK reo rel = m' := by simpa using h
  have hcv0 := hcv
  simp only [decCV, hlist?, bind, Option.bind_eq_some_iff, pure] at hcv0
  obtain ⟨nm, hnm, lps, ⟨lo, hlo, ll, hll, -⟩, t, ht, -⟩ := hcv0
  obtain ⟨w0, hw0, -, -⟩ := hd?_some hnm
  obtain ⟨w1, hw1, -⟩ : ∃ w, erecP m (cq.toNat + 1) = some w ∧ w.toNat = lo := by
    simp only [nat?, Option.map_eq_some_iff] at hlo; exact hlo
  obtain ⟨w2, hw2, -⟩ : ∃ w, erecP m (cq.toNat + 2) = some w ∧ w.toNat = ll := by
    simp only [nat?, Option.map_eq_some_iff, Nat.add_assoc] at hll; exact hll
  obtain ⟨w3, hw3, -, -⟩ := hd?_some ht
  have hW : ∀ i < 4, ∃ w, erecP m (cq.toNat + i) = some w := by
    intro i hi
    rcases i with _ | _ | _ | _ | i
    · exact ⟨w0, by simpa using hw0⟩
    · exact ⟨w1, hw1⟩
    · exact ⟨w2, hw2⟩
    · exact ⟨w3, hw3⟩
    · omega
  have r0 : erRd m cq = w0 := (erRd_of_erecP (by simpa using hw0)).1
  obtain ⟨r1, e1⟩ := erRd_add (j := 1) (cq := cq) (m := m) hw1 (by decide)
  obtain ⟨r2, e2⟩ := erRd_add (j := 2) (cq := cq) (m := m) hw2 (by decide)
  obtain ⟨r3, e3⟩ := erRd_add (j := 3) (cq := cq) (m := m) hw3 (by decide)
  simp only [show (UInt64.ofNat 1 : Word) = 1 from rfl, show (UInt64.ofNat 2 : Word) = 2 from rfl,
    show (UInt64.ofNat 3 : Word) = 3 from rfl] at r1 r2 r3 e1 e2 e3
  have hfr : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], ∀ j < 10,
      erTier x ≠ erTier (q1 + UInt64.ofNat j) ∨ erOff x ≠ erOff (q1 + UInt64.ofNat j) := by
    intro x hx j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact erFresh h1 hS.iw (by simpa using hw0) hj
    · exact erFresh h1 hS.iw (by rw [e1]; exact hw1) hj
    · exact erFresh h1 hS.iw (by rw [e2]; exact hw2) hj
    · exact erFresh h1 hS.iw (by rw [e3]; exact hw3) hj
  obtain ⟨-, hf1, -⟩ := erAllocW_spec h1 hS.iw
  have hr1 : ∀ x, erRd m1 x = erRd m x := fun x => by
    unfold erRd; rw [hf1.arr _ (by simp) (by rw [tierA_EREC]; split <;> decide)]
  rw [riMem_eq hfr, hr1, hr1, hr1, hr1, r0, r1, r2, r3]
  obtain ⟨hS', hg, -, -, -, -, hget⟩ :=
    erRec_stage h1 hS [5, w0, w1, w2, w3, mi, rp, reo, rel, isK] (by simp)
  refine ⟨hS', hg, ?_⟩
  generalize wrER m1 q1 _ = M at hS' hg hget
  have hw : ∀ i, i < 4 → erecP M (q1.toNat + 1 + i) = erecP M (cq.toNat + i) := by
    intro i hi
    obtain ⟨w, hw⟩ := hW i hi
    rw [IWGrow.ext hg _ _ hw, Nat.add_assoc, hget (1 + i) (by simp; omega)]
    rcases i with _ | _ | _ | _ | i
    · simp at hw ⊢; rw [hw0] at hw; exact Option.some.inj hw
    · simp at hw ⊢; rw [hw1] at hw; exact Option.some.inj hw
    · simp at hw ⊢; rw [hw2] at hw; exact Option.some.inj hw
    · simp at hw ⊢; rw [hw3] at hw; exact Option.some.inj hw
    · omega
  have hcv' : decCV (erecP M) (q1.toNat + 1) = some cv := by
    rw [decCV_shift (by simpa using hw 0 (by decide)) (by simpa using hw 1 (by decide))
      (by simpa [Nat.add_assoc] using hw 2 (by decide)) (by simpa [Nat.add_assoc] using hw 3 (by decide))]
    exact ArrExt.decCV (IWGrow.ext hg) hcv
  have n0 : nat? (erecP M) q1.toNat = some 5 := by
    have := hget 0 (by simp); simp only [Nat.add_zero] at this; simp [nat?, this]
  have n5 : nat? (erecP M) (q1.toNat + 5) = some mi.toNat := by simp [nat?, hget 5 (by simp)]
  have n6 : nat? (erecP M) (q1.toNat + 6) = some rp.toNat := by simp [nat?, hget 6 (by simp)]
  have n7 : nat? (erecP M) (q1.toNat + 7) = some reo.toNat := by simp [nat?, hget 7 (by simp)]
  have n8 : nat? (erecP M) (q1.toNat + 8) = some rel.toNat := by simp [nat?, hget 8 (by simp)]
  have b9 : bool? (erecP M) (q1.toNat + 9) = some (isK != 0) := by simp [bool?, hget 9 (by simp)]
  have hru' : decRules (erecP M) reo.toNat rel.toNat = some rules := (IWGrow.ext hg).decRules hru
  simp only [decCI, Option.bind_eq_bind, n0, Option.bind_some, hcv', n5, n6, n7, n8, b9, hru',
    Option.pure_def]

/-! ## The `abstract1` memo -/

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
    exact (AFr.of_frame (cpMem_frame m b (rdW (m.arr64 IW) ro))).trans (rteGoW_afr n _ _ _ _ _ _ h2)

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

theorem riMem_frame (m : Mem) (q cv mi rp isK reo rel : Word) :
    MemFrame [EREC, tier1 EREC] [] m (riMem m q cv mi rp isK reo rel) := by
  simp only [riMem]
  repeat' refine MemFrame.trans ?_ (erecPutMem_frame _ _ _)
  exact MemFrame.refl _ _ _

theorem riW_afr {m m' : Mem} {cv mi rp isK reo rel q : Word}
    (h : riW m cv mi rp isK reo rel = some (q, m')) : AFr m m' := by
  simp only [riW] at h
  split at h; · cases h
  rename_i q1 m1 h1
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (erAllocW_afr h1).trans (AFr.of_frame (riMem_frame _ _ _ _ _ _ _ _))

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

/-! ## `rec_k_expected` -/

l_model rk_spec (p : Prog) (hL : CbrLook p)
  fns [hL.rke ↦ rkW ro]
  specs []
  grind [arena_grind]

/-- **`rec_k_expected` is `recKExpected`** at a shape and a target major decoded below the tops. -/
theorem rkW_ok {m : Mem} {p M : Word} {bs : BlockShape} {TM : TargetMajor}
    (hbs : DecB (fun m => decBS m p.toNat) m bs) (hM : DecB (fun m => decTM m M.toNat) m TM)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∃ w, rkW m p M = some w ∧ (w != 0) = ConRon.Arena.recKExpected bs TM := by
  have hM0 : decTM (truncM m) M.toNat = some TM := hM
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hM0
  obtain ⟨i0, -, l0, -, ds0, -, nP, -, nI, -, cs, hcs, k8, hk8, nfs0, -, pf0, -, hTM⟩ := hM0
  have eCs : TM.ctors = cs := by rw [← hTM]
  have eMem : TM.member = decON k8 := by rw [← hTM]
  obtain ⟨co, cl, hco, hcl, hcsd⟩ := decAt_some hcs
  obtain ⟨-, hcom⟩ := rec2IwN_trunc hco
  obtain ⟨-, hclm⟩ := rec2IwN_trunc hcl
  obtain ⟨-, hk8m⟩ := rec2IwN_trunc hk8
  obtain ⟨e6, t6⟩ := rec2RdN (w := M) (k := 6) hcom hsz
  obtain ⟨e7, t7⟩ := rec2RdN (w := M) (k := 7) (by simpa [Nat.add_assoc] using hclm) hsz
  obtain ⟨e8, t8⟩ := rec2RdN (w := M) (k := 8) hk8m hsz
  simp only [show UInt64.ofNat 6 = (6 : Word) from rfl, show UInt64.ofNat 7 = (7 : Word) from rfl,
    show UInt64.ofNat 8 = (8 : Word) from rfl] at e6 e7 e8
  have hbs0 : decBS (truncM m) p.toNat = some bs := hbs
  obtain ⟨hmem, -, -, -, -, -, hprop⟩ := decBS_some hbs0
  obtain ⟨mo, ml, -, hml, hmd⟩ := decAt_some hmem
  obtain ⟨-, hmlm⟩ := rec2IwN_trunc hml
  obtain ⟨e1, t1⟩ := rec2RdN (w := p) (k := 1) hmlm hsz
  have ek : bs.k = ml := by
    have := decPL_length _ hmd; simp only [BlockShape.k]; exact this
  have eP := installIwB (k := 8) hprop hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 8 = (8 : Word) from rfl] at e1 eP
  unfold rkW ConRon.Arena.recKExpected
  rw [e8, e7, eMem, eCs]
  by_cases hk0 : k8 = 0
  · subst hk0
    exact ⟨0, by simp, by simp [decON]⟩
  have hk8' : UInt64.ofNat k8 ≠ (0 : Word) := fun e => hk0 (by rw [← t8, e]; rfl)
  simp only [hk8', ↓reduceIte]
  have hlen : cs.length = cl := decPL_length _ hcsd
  by_cases hc1 : cl = 1
  · subst hc1
    obtain ⟨cp, c, ys, rfl, hcp, hc, hys⟩ := decPL_cons (l := 0) hcsd
    have : ys = [] := by have := decPL_length _ hys; simpa using this
    subst this
    obtain ⟨-, hcpm⟩ := rec2IwN_trunc (i := (UInt64.ofNat co : Word).toNat + 0) (by rw [t6]; simpa using hcp)
    obtain ⟨e9, t9⟩ := rec2RdN (w := UInt64.ofNat co) (k := 0) hcpm hsz
    simp only [decCN, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
    obtain ⟨_, -, cv, -, nF, hnF, hceq⟩ := hc
    subst hceq
    obtain ⟨-, hnFm⟩ := rec2IwN_trunc (i := (UInt64.ofNat cp : Word).toNat + 1) (by rw [t9]; exact hnF)
    obtain ⟨e10, t10⟩ := rec2RdN (w := UInt64.ofNat cp) (k := 1) hnFm hsz
    simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl,
      UInt64.add_zero] at e9 e10
    have h1' : ¬ (UInt64.ofNat 1 : Word) ≠ 1 := by decide
    simp only [h1', ↓reduceIte]
    rw [e6, e9, e10, e1]
    refine ⟨_, rfl, ?_⟩
    simp only [decON, hk0, ite_false, ek]
    rw [← eP, ← t1, ← t10]
    generalize (UInt64.ofNat ml : Word) = a
    generalize (UInt64.ofNat nF : Word) = b
    generalize rdW (m.arr64 IW) (p + 8) = c
    have ha' : a.toNat = 1 ↔ a = 1 := by rw [← UInt64.toNat_inj]; rfl
    have hb' : b.toNat = 0 ↔ b = 0 := by rw [← UInt64.toNat_inj]; rfl
    by_cases ha : a = 1 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;> simp [ha, hb, hc, ha', hb']
  · have h7 : (UInt64.ofNat cl : Word) ≠ 1 := by
      intro e; apply hc1; rw [← t7, e]; rfl
    simp only [ne_eq, h7, not_false_eq_true, ↓reduceIte]
    refine ⟨0, rfl, ?_⟩
    simp only [decON, hk0, ite_false]
    match cs, hlen with
    | [], _ => rfl
    | [_], h => exact absurd h.symm hc1
    | _ :: _ :: _, _ => rfl

/-! ## `block_rec_infos_tf` -/

l_model bri_spec (p : Prog) (hL : CbrLook p) (hpu : p.lookup "erec_put" = some erecPut)
  fns [hL.bri ↦ briW list]
  specs [rp_spec p hL.rpa n, tsr_spec p hL.tsr hpu n, mj_spec p hL.mi n, rk_spec p hL n, rte_spec p hL hpu n,
    ri_spec p hL hpu n, slCons_specW p hL.tsr.rc.rx.ha hL.tsr.ic hL.tsr.sc n]
  grind [arena_grind]

/-- A record pointer consed onto a slice of `EREC` record pointers (`sl_cons`). -/
theorem consW_ci {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {cis : List IConstantInfo} {ci : IConstantInfo}
    (h : consW n m x o l = some (r, m')) (hS : StageR vis fe m a) (hb : o.toNat + l.toNat ≤ iwTop m)
    (hd : decPL m (decCI (erecP m)) o.toNat l.toNat = some cis) (hx : decCI (erecP m) x.toNat = some ci) :
    decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some (ci :: cis) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' ∧ StageR vis fe m' a ∧ IWGrow m m' := by
  rw [decPL_eq_bind] at hd
  rcases hps : decNL m o.toNat l.toNat with _ | ps <;> rw [hps] at hd
  · cases hd
  simp only [Option.bind_some] at hd
  obtain ⟨hS', hg, hd', ht'⟩ := consW_stageN h hS hb hps
  have hext := IWGrow.ext hg
  refine ⟨?_, ht', hS', hg⟩
  rw [decPL_eq_bind, hd']
  simp only [Option.bind_some, List.mapM_cons]
  rw [show decCI (erecP m') x.toNat = some ci from hext.decCI hx,
    ArrExt.mapM (f := decCI (erecP m)) (g := decCI (erecP m')) (fun _ _ hy => hext.decCI hy) _ _ hd]
  rfl

/-- A slice of `EREC` record pointers below the `IW` top, across pool growth. -/
theorem decPL_ci_grow {m m' : Mem} (hg : IWGrow m m') {o l : Nat} {cis : List IConstantInfo}
    (hb : o + l ≤ iwTop m) (hd : decPL m (decCI (erecP m)) o l = some cis) :
    decPL m' (decCI (erecP m')) o l = some cis := by
  rw [decPL_eq_bind] at hd ⊢
  rcases hps : decNL m o l with _ | ps <;> rw [hps] at hd
  · cases hd
  have hps' : decNL m' o l = some ps := by
    rw [← hps]; simp only [decNL]; apply mapM_opt_congr; intro j hj
    simp only [iwN, nat?, iwA, aread_apply, aread_apply]; rw [hg.iwGet _ (by simp at hj; omega)]
  rw [hps']
  simp only [Option.bind_some] at hd ⊢
  exact ArrExt.mapM (fun _ _ hy => (IWGrow.ext hg).decCI hy) _ _ hd

/-- **`block_rec_infos_tf` refines `blockRecInfosTF`**: the records at the returned slice of
`EREC` pointers. -/
theorem briW_ok (n : Nat) : ∀ {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {pp mm lo ll : Word} {r : List Word} {bs : BlockShape} {xs : List (IConstantVal × TargetMajor × List EIdx)},
    briW n m pp mm lo ll = some (r, m') → StageR vis fe m a →
    DecB (fun m => decBS m pp.toNat) m bs → PSlR decRR xs lo ll m → mm.toNat + ll.toNat < 2 ^ 64 →
    AbsOK m →
    ∃ infos a', (ConRon.Arena.blockRecInfosTF bs mm.toNat xs).run a = .ok (infos, a') ∧
      decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some infos ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' := by
  induction n with
  | zero => intro m m' a vis fe pp mm lo ll r bs xs h; simp [briW] at h
  | succ n ih =>
  intro m m' a vis fe pp mm lo ll r bs xs h hS hbs hxs hml hA
  by_cases hl : ll = 0
  · rw [briW.arm1 n m pp mm lo ll hl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hl
    have : xs = [] := by
      have := decPL_length _ (hxs.1.get (OMono.decPL decRR_mono _ _)); simpa using this
    subst this
    exact ⟨[], a, rfl, by simp [decPL], by simp, hS, IWGrow.refl _, hA⟩
  rw [briW.arm2 n m pp mm lo ll hl] at h
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
  obtain ⟨-, hrp⟩ := bmjW_rpW_eq (r := mm) hbs hsz
  -- the generated rules
  rcases h1 : tsrW n m (brpW m pp mm) (UInt64.ofNat mp) (UInt64.ofNat o) (UInt64.ofNat l) with _ | ⟨rr, m1⟩
  · rw [h1, briW.k_generated_rules.none] at h; cases h
  rw [h1, briW.k_generated_rules.arm1] at h
  obtain ⟨rules, a1, run1, hd1, hR1, hb1, hS1, hg1, hA1⟩ := tsrW_ok fe vis n h1 hS hM hrh hA
  rw [hrp] at run1
  -- the tail's records
  have hl0 : ll.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
  have hmm1 : (mm + 1).toNat = mm.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hll1 : (ll - 1).toNat = ll.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  rcases h2 : briW n m1 pp (mm + 1) (lo + 1) (ll - 1) with _ | ⟨ri, m2⟩
  · rw [h2] at h; simp [briW.k_block_rec_infos_tf] at h
  rw [h2, briW.k_block_rec_infos_tf.arm1] at h
  obtain ⟨infos, a2, run2, hd2, hb2, hS2, hg2, hA2⟩ := ih h2 hS1 (hbs.grow (decBS_mono _) hg1)
    (hys.grow (fun q => decRR_mono q) hg1) (by rw [hmm1, hll1]; omega) hA1
  rw [hmm1] at run2
  -- the K flag, the major index
  have hsz2 := hS2.iw.iwSize
  have hg12 := hg1.trans hg2
  obtain ⟨isK, hk, hkE⟩ := rkW_ok (hbs.grow (decBS_mono _) hg12) (hM.grow (decTM_mono _) hg12) hsz2
  obtain ⟨hmj, -⟩ := bmjW_rpW_eq (r := mm) (hbs.grow (decBS_mono _) hg12) hsz2
  rw [hk, briW.k_rec_k_expected.arm1] at h
  -- the rules copied
  rcases h3 : rteW n m2 (rr.headD 0) (rr.tail.headD 0) with _ | ⟨re, m3⟩
  · rw [h3] at h; simp [briW.k_rules_to_erec] at h
  rw [h3, briW.k_rules_to_erec.arm1] at h
  obtain ⟨hS3, hg3, hrl3, hru3⟩ := rteW_ok n h3 hS2 (decPL_rl_grow hg2 hb1 hd1) (hR1.grow hg2 hb1)
  rw [← hrl3] at hru3
  -- the record
  rcases h4 : riW m3 (UInt64.ofNat cvp) (bmjW m2 pp mm) (brpW m pp mm) isK (re.headD 0) (re.tail.headD 0)
    with _ | ⟨q, m4⟩
  · rw [h4] at h; simp [briW.k_rec_info_rec] at h
  rw [h4, briW.k_rec_info_rec.arm1] at h
  have hg13 := hg12.trans hg3
  obtain ⟨hS4, hg4, hci⟩ := riRec_stage h4 hS3 ((IWGrow.ext hg13).decCV hcvE) hru3
  -- consed
  rcases h5 : consW n m4 q (ri.headD 0) (ri.tail.headD 0) with _ | ⟨r5, m5⟩
  · rw [h5] at h; simp [briW.k_sl_cons] at h
  rw [h5, briW.k_sl_cons.arm1] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hg34 := hg3.trans hg4
  obtain ⟨hd5, hb5, hS5, hg5⟩ := consW_ci h5 hS4 (by have := hg34.iw; omega)
    (decPL_ci_grow hg34 hb2 hd2) hci
  refine ⟨_, a2, ?_, by simpa using hd5, by simp only [List.headD_cons, List.tail_cons]; omega, hS5, hg13.trans (hg4.trans hg5),
    consW_afr h5 (riW_afr h4 (rteW_afr h3 hA2))⟩
  simp only [ConRon.Arena.blockRecInfosTF, StateT.run_bind, run1, except_ok_bind, run2]
  rw [hmj, hrp, hkE]
  rfl

/-- **`block_rec_infos_tf` refines `blockRecInfosTF`**: the shape and the family's `rec4` records
decoded below the tops; the records (each recursor at its record's major index and rule prefix, its
K flag `rec_k_expected`, its rules at its major by `generated_rules`) at the returned slice of
`EREC` pointers. -/
@[refines ConRon.Arena.blockRecInfosTF]
theorem blockRecInfosTF_refines (p : Prog) (hL : CbrLook p) (hpu : p.lookup "erec_put" = some erecPut)
    (n : Nat) (s₀ : St) (a₀ : AState)
    (fe : IFEnv) (vis pp mm lo ll : Word) (bs : BlockShape) (xs : List (IConstantVal × TargetMajor × List EIdx))
    (hS : StageR vis fe s₀.mem a₀) (hbs : DecB (fun m => decBS m pp.toNat) s₀.mem bs)
    (hxs : PSlR decRR xs lo ll s₀.mem) (hml : mm.toNat + ll.toNat < 2 ^ 64) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_infos_tf" [pp, mm, lo, ll]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ infos a',
      (ConRon.Arena.blockRecInfosTF bs mm.toNat xs).run a₀ = .ok (infos, a') ∧
      decPL s'.mem (decCI (erecP s'.mem)) (r.headD 0).toNat (r.tail.headD 0).toNat = some infos ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧ StageR vis fe s'.mem a' ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (bri_spec p hL hpu n s₀ pp mm lo ll) fun _ _ ⟨hl, hm⟩ =>
    ⟨hl, briW_ok n hm hS hbs hxs hml hA⟩



end L.Ind

end

end
