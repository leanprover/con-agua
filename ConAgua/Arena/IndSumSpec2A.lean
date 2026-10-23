import ConAgua.Arena.IndInstallSpec
import ConAgua.Arena.IndMaster
import ConAgua.Arena.IndView
import ConAgua.Arena.StageInst1

/-!
# Refinements of `IndSum`, second file (lane `indproofs`)

Functions of `IndSum.lean` whose proofs reuse `IndInstallSpec.lean` (which imports `IndSumSpec`).

* `check_struct_doms_at` refines `checkStructDomsAt`: its model is `check_block_doms_at`'s
  (`domsW`) with the empty result list, and the twin is `checkBlockDomsAt` up to the error
  message, so the relational lemma is `domsW_ok` and an `ok`-run transfer.
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_struct_doms_at` -/

mutual
/-- **The model of `check_struct_doms_at`**: `domsW` returning no words. -/
def sdomsW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, off, fo, fl, dO, dl, j =>
    if j = 0 then some ([], m)
    else if fl ≤ j - 1 then none
    else if dl ≤ j - 1 then none
    else
      sdomsK1 n vis off fo fl dO dl j (rdW (m.arr64 IW) (dO + (j - 1)))
        (stubM "fvar_type_d" m [rdW (m.arr64 IW) (fo + (j - 1))])

/-- After `fvar_type_d`. -/
def sdomsK1 (n : Nat) (vis off fo fl dO dl j b : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m1) =>
    sdomsK2 n vis off fo fl dO dl j
      (stubM "is_def_eq_core" m1 [vis, off + (j - 1), ra.headD 0, b])

/-- After `is_def_eq_core`. -/
def sdomsK2 (n : Nat) (vis off fo fl dO dl j : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m2) =>
    if rb.headD 0 = 0 then none else sdomsK3 (sdomsW n m2 vis off fo fl dO dl (j - 1))

/-- After the recursive call (its result discarded). -/
def sdomsK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([], m)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (vis off fo fl dO dl j b : Word) (ra rb : List Word)

theorem sdomsW_zero (hj : j = 0) : sdomsW (n + 1) m vis off fo fl dO dl j = some ([], m) := by
  simp [sdomsW, hj]
theorem sdomsW_abortF (hj : j ≠ 0) (hfl : fl ≤ j - 1) :
    sdomsW (n + 1) m vis off fo fl dO dl j = none := by simp [sdomsW, hj, hfl]
theorem sdomsW_abortD (hj : j ≠ 0) (hfl : ¬ fl ≤ j - 1) (hdl : dl ≤ j - 1) :
    sdomsW (n + 1) m vis off fo fl dO dl j = none := by simp [sdomsW, hj, hfl, hdl]
theorem sdomsW_cons (hj : j ≠ 0) (hfl : ¬ fl ≤ j - 1) (hdl : ¬ dl ≤ j - 1) :
    sdomsW (n + 1) m vis off fo fl dO dl j =
      sdomsK1 n vis off fo fl dO dl j (rdW (m.arr64 IW) (dO + (j - 1)))
        (stubM "fvar_type_d" m [rdW (m.arr64 IW) (fo + (j - 1))]) := by
  simp [sdomsW, hj, hfl, hdl]
theorem sdomsK1_some :
    sdomsK1 n vis off fo fl dO dl j b (some (ra, m1)) =
      sdomsK2 n vis off fo fl dO dl j
        (stubM "is_def_eq_core" m1 [vis, off + (j - 1), ra.headD 0, b]) := by
  rw [sdomsK1]
theorem sdomsK2_abort (heq : rb.headD 0 = 0) :
    sdomsK2 n vis off fo fl dO dl j (some (rb, m2)) = none := by
  rw [sdomsK2, if_pos heq]
theorem sdomsK2_ok (heq : rb.headD 0 ≠ 0) :
    sdomsK2 n vis off fo fl dO dl j (some (rb, m2)) =
      sdomsK3 (sdomsW n m2 vis off fo fl dO dl (j - 1)) := by
  rw [sdomsK2, if_neg heq]
theorem sdomsK3_some (r : List Word) (m : Mem) : sdomsK3 (some (r, m)) = some ([], m) := rfl
end arms

grind_pattern [ind_grind] sdomsW_zero => sdomsW (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] sdomsW_abortF => sdomsW (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] sdomsW_abortD => sdomsW (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] sdomsW_cons => sdomsW (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] sdomsK1_some => sdomsK1 n vis off fo fl dO dl j b (some (ra, m1))
grind_pattern [ind_grind] sdomsK2_abort => sdomsK2 n vis off fo fl dO dl j (some (rb, m2))
grind_pattern [ind_grind] sdomsK2_ok => sdomsK2 n vis off fo fl dO dl j (some (rb, m2))
grind_pattern [ind_grind] sdomsK3_some => sdomsK3 (some (r, m))

section spec
variable (p : Prog) (hg : p.lookup "sl_get" = some slGet)
  (hp : p.lookup "check_struct_doms_at" = some checkStructDomsAtL)
include hg hp

theorem sdomsW_spec (n : Nat) : ∀ (s₀ : St) (vis off fo fl dO dl j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_struct_doms_at" [vis, off, fo, fl, dO, dl, j]
    ⦃fun r s' => LocEq s' s₀ ∧ sdomsW n s₀.mem vis off fo fl dO dl j = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis off fo fl dO dl j
    rw [invoke_eq _ hp]; simp only [callFn, checkStructDomsAtL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis off fo fl dO dl j
    rw [invoke_eq _ hp]
    simp only [callFn, checkStructDomsAtL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slGet_specW p hg n, stubM_spec p "fvar_type_d" n, stubM_spec p "is_def_eq_core" n, ih] <;>
      finish (gen := 20) [getW]

end spec

/-- `sdomsW` is `domsW` with the result words dropped. -/
theorem sdomsW_eq (n : Nat) : ∀ (m : Mem) (vis off fo fl dO dl j : Word),
    sdomsW n m vis off fo fl dO dl j =
      (domsW n m vis off fo fl dO dl j).map (fun r => ([], r.2)) := by
  induction n with
  | zero => intro m vis off fo fl dO dl j; simp [sdomsW, domsW]
  | succ n ih =>
    intro m vis off fo fl dO dl j
    simp only [sdomsW, domsW]
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    cases stubM "fvar_type_d" m [rdW (m.arr64 IW) (fo + (j - 1))] with
    | none => simp [sdomsK1, domsK1]
    | some x =>
      obtain ⟨ra, m1⟩ := x
      simp only [sdomsK1, domsK1]
      cases stubM "is_def_eq_core" m1 [vis, off + (j - 1), ra.headD 0, rdW (m.arr64 IW) (dO + (j - 1))] with
      | none => simp [sdomsK2, domsK2]
      | some y =>
        obtain ⟨rb, m2⟩ := y
        simp only [sdomsK2, domsK2]
        split <;> try rfl
        rw [ih]
        cases domsW n m2 vis off fo fl dO dl (j - 1) with
        | none => simp [sdomsK3, domsK3]
        | some z => rfl

/-- The twins agree on successful runs (they differ in the error message only). -/
theorem checkStructDomsAt_of_block (fe : IFEnv) (off : Nat) (fvs doms : List EIdx) :
    ∀ (j : Nat) (a a' : AState),
    (ConRon.Arena.checkBlockDomsAt V fe off fvs doms j).run a = .ok ((), a') →
    (ConRon.Arena.checkStructDomsAt V fe off fvs doms j).run a = .ok ((), a') := by
  intro j
  induction j with
  | zero => intro a a' h; simpa [ConRon.Arena.checkBlockDomsAt, ConRon.Arena.checkStructDomsAt] using h
  | succ j ih =>
    intro a a' h
    simp only [ConRon.Arena.checkBlockDomsAt, ConRon.Arena.checkStructDomsAt] at h ⊢
    cases hf : fvs[j]? with
    | none => simp [hf, unwrapOr] at h; cases h
    | some x =>
    cases hd : doms[j]? with
    | none => simp [hf, hd, unwrapOr] at h; cases h
    | some y =>
    simp only [hf, hd, unwrapOr, pure_bind, StateT.run_bind] at h ⊢
    cases h1 : (fvarTypeD x).run a with
    | error e => rw [h1] at h; cases h
    | ok v =>
    obtain ⟨t, a1⟩ := v
    simp only [h1] at h ⊢
    simp only [bind, Except.bind] at h ⊢
    cases h2 : (isDefEqCore V fe checkFuel (off + j) t y).run a1 with
    | error e => rw [h2] at h; cases h
    | ok w =>
    obtain ⟨bv, a2⟩ := w
    simp only [h2] at h ⊢
    cases bv with
    | false => simp [fail] at h; cases h
    | true => simp only [bind, Except.bind] at h ⊢; exact ih _ _ (by simpa using h)

/-- **`check_struct_doms_at` refines `checkStructDomsAt .verified`** (through the stubs
`fvar_type_d`, `is_def_eq_core`). -/
@[refines ConRon.Arena.checkStructDomsAt]
theorem checkStructDomsAt_refines (p : Prog) (hg : p.lookup "sl_get" = some slGet)
    (hp : p.lookup "check_struct_doms_at" = some checkStructDomsAtL) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis off fo fl dO dl j : Word)
    (fvs doms : List EIdx) (hStage : StageR dn vis fe s₀.mem a₀)
    (hfvs : decHL s₀.mem fo.toNat fl.toNat = some fvs)
    (hdoms : decHL s₀.mem dO.toNat dl.toNat = some doms)
    (hfob : fo.toNat + fl.toNat < 2 ^ 64) (hdob : dO.toNat + dl.toNat < 2 ^ 64)
    (hfot : fo.toNat + fl.toNat ≤ iwTop s₀.mem) (hdot : dO.toNat + dl.toNat ≤ iwTop s₀.mem)
    (hoob : off.toNat + fl.toNat < 2 ^ 64) (hjf : j.toNat ≤ fl.toNat) (hjd : j.toNat ≤ dl.toNat) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_struct_doms_at" [vis, off, fo, fl, dO, dl, j]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.checkStructDomsAt V fe off.toNat fvs doms j.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.checkStructDomsAt V fe off.toNat fvs doms j.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (sdomsW_spec p hg hp n s₀ vis off fo fl dO dl j) ?_
  rintro r s' ⟨hl, hm⟩
  rw [sdomsW_eq] at hm
  cases hd : domsW n s₀.mem vis off fo fl dO dl j with
  | none => rw [hd] at hm; cases hm
  | some x =>
  obtain ⟨r0, m0⟩ := x
  rw [hd] at hm
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨-, rfl⟩ := hm
  obtain ⟨a', hrun, hStage', hg'⟩ := domsW_ok n dn fe s₀.mem _ a₀ vis off fo fl dO dl j fvs doms r0
    hd hStage hfvs hdoms hfob hdob hfot hdot hoob hjf hjd
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ (checkStructDomsAt_of_block fe _ fvs doms _ _ _ hrun)
  exact ⟨hl, hok, by rw [hst]; exact hStage', hg'⟩

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Slices, head first -/

/-- **A decoding slice of length `l ≥ 1`**: its head is the word at `o`, its tail decodes at
`o + 1`. -/
theorem decHL_cons {k : IdxKind} {m : Mem} {o l : Word} {xs : List (Idx k)}
    (h : decHL m o.toNat l.toNat = some xs) (hl : l ≠ 0) (hb : o.toNat + l.toNat < 2 ^ 64) :
    ∃ w xs', xs = decI w :: xs' ∧ rdW (m.arr64 IW) o = w ∧ w.toNat < 2 ^ 32 ∧
      decHL m (o + 1).toNat (l - 1).toNat = some xs' := by
  have hl1 : 1 ≤ l.toNat := by
    rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl
    · omega
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hlm : (l - 1).toNat = l.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hl1))]; simp
  rw [ho1, hlm]
  have hs : l.toNat = (l.toNat - 1) + 1 := by omega
  rw [hs] at h
  simp only [decHL] at h
  rw [hslice?_succ] at h
  cases hx : hd? (iwA m) o.toNat with
  | none => rw [hx] at h; cases h
  | some x =>
    cases ht : (hslice? (iwA m) (o.toNat + 1) (l.toNat - 1) : Option (List (Idx k))) with
    | none => rw [hx, ht] at h; cases h
    | some xs' =>
      rw [hx, ht] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
      obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW (m := m) (i := o.toNat) (x := x) hx (by omega)
      refine ⟨w, xs', by rw [← h, hw3], by simpa using hw1, hw2, ht⟩

/-! ## `field_doms_resolve`, `idx_args_resolve` -/

mutual
/-- **The model of `field_doms_resolve`.** -/
def fdrW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, v, o, l =>
    if l = 0 then some ([1], m)
    else fdrK1 n v o l (stubM "fvar_type_d" m [rdW (m.arr64 IW) o])
/-- After `fvar_type_d`. -/
def fdrK1 (n : Nat) (v o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m1) => fdrK2 n v o l (stubM "consts_resolve_ffast" m1 [v, ra.headD 0])
/-- After `consts_resolve_ffast`. -/
def fdrK2 (n : Nat) (v o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m2) => if rb.headD 0 = 0 then some ([0], m2) else resK (fdrW n m2 v (o + 1) (l - 1))
/-- After a recursive call: its first word. -/
def resK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

mutual
/-- **The model of `idx_args_resolve`.** -/
def iarW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, v, o, l =>
    if l = 0 then some ([1], m)
    else iarK n v o l (stubM "consts_resolve_ffast" m [v, rdW (m.arr64 IW) o])
/-- After `consts_resolve_ffast`. -/
def iarK (n : Nat) (v o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m2) => if rb.headD 0 = 0 then some ([0], m2) else resK' (iarW n m2 v (o + 1) (l - 1))
/-- After a recursive call: its first word. -/
def resK' : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (v o l : Word) (ra rb r : List Word)
theorem fdrW_nil (hl : l = 0) : fdrW (n + 1) m v o l = some ([1], m) := by simp [fdrW, hl]
theorem fdrW_cons (hl : l ≠ 0) :
    fdrW (n + 1) m v o l = fdrK1 n v o l (stubM "fvar_type_d" m [rdW (m.arr64 IW) o]) := by
  simp [fdrW, hl]
theorem fdrK1_some : fdrK1 n v o l (some (ra, m1)) =
    fdrK2 n v o l (stubM "consts_resolve_ffast" m1 [v, ra.headD 0]) := by rw [fdrK1]
theorem fdrK2_no (h : rb.headD 0 = 0) : fdrK2 n v o l (some (rb, m2)) = some ([0], m2) := by
  rw [fdrK2, if_pos h]
theorem fdrK2_yes (h : rb.headD 0 ≠ 0) :
    fdrK2 n v o l (some (rb, m2)) = resK (fdrW n m2 v (o + 1) (l - 1)) := by rw [fdrK2, if_neg h]
theorem resK_some : resK (some (r, m)) = some ([r.headD 0], m) := rfl
theorem iarW_nil (hl : l = 0) : iarW (n + 1) m v o l = some ([1], m) := by simp [iarW, hl]
theorem iarW_cons (hl : l ≠ 0) :
    iarW (n + 1) m v o l = iarK n v o l (stubM "consts_resolve_ffast" m [v, rdW (m.arr64 IW) o]) := by
  simp [iarW, hl]
theorem iarK_no (h : rb.headD 0 = 0) : iarK n v o l (some (rb, m2)) = some ([0], m2) := by
  rw [iarK, if_pos h]
theorem iarK_yes (h : rb.headD 0 ≠ 0) :
    iarK n v o l (some (rb, m2)) = resK' (iarW n m2 v (o + 1) (l - 1)) := by rw [iarK, if_neg h]
theorem resK'_some : resK' (some (r, m)) = some ([r.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] fdrW_nil => fdrW (n + 1) m v o l
grind_pattern [ind_grind] fdrW_cons => fdrW (n + 1) m v o l
grind_pattern [ind_grind] fdrK1_some => fdrK1 n v o l (some (ra, m1))
grind_pattern [ind_grind] fdrK2_no => fdrK2 n v o l (some (rb, m2))
grind_pattern [ind_grind] fdrK2_yes => fdrK2 n v o l (some (rb, m2))
grind_pattern [ind_grind] resK_some => resK (some (r, m))
grind_pattern [ind_grind] iarW_nil => iarW (n + 1) m v o l
grind_pattern [ind_grind] iarW_cons => iarW (n + 1) m v o l
grind_pattern [ind_grind] iarK_no => iarK n v o l (some (rb, m2))
grind_pattern [ind_grind] iarK_yes => iarK n v o l (some (rb, m2))
grind_pattern [ind_grind] resK'_some => resK' (some (r, m))

section spec
variable (p : Prog)

theorem fdrW_spec (hp : p.lookup "field_doms_resolve" = some fieldDomsResolveL) (n : Nat) :
    ∀ (s₀ : St) (v o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "field_doms_resolve" [v, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ fdrW n s₀.mem v o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ v o l; rw [invoke_eq _ hp]; simp only [callFn, fieldDomsResolveL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ v o l
    rw [invoke_eq _ hp]
    simp only [callFn, fieldDomsResolveL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "fvar_type_d" n, stubM_spec p "consts_resolve_ffast" n, ih] <;>
      finish (gen := 20)

theorem iarW_spec (hp : p.lookup "idx_args_resolve" = some idxArgsResolveL) (n : Nat) :
    ∀ (s₀ : St) (v o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "idx_args_resolve" [v, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ iarW n s₀.mem v o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ v o l; rw [invoke_eq _ hp]; simp only [callFn, idxArgsResolveL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ v o l
    rw [invoke_eq _ hp]
    simp only [callFn, idxArgsResolveL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "consts_resolve_ffast" n, ih] <;>
      finish (gen := 20)

end spec

/-! ## The relational lemmas -/

theorem toNat_succ_of_lt {o l : Word} (hb : o.toNat + l.toNat < 2 ^ 64) (hl : l ≠ 0) :
    (o + 1).toNat + (l - 1).toNat = o.toNat + l.toNat ∧ (o + 1).toNat = o.toNat + 1 := by
  have hl1 : 1 ≤ l.toNat := by
    rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl
    · omega
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hlm : (l - 1).toNat = l.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hl1))]; simp
  omega

theorem fdrW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (v o l : Word) (xs : List EIdx) (r : List Word),
    fdrW n m v o l = some (r, m') → StageR dn v fe m a → decHL m o.toNat l.toNat = some xs →
    o.toNat + l.toNat < 2 ^ 64 → o.toNat + l.toNat ≤ iwTop m →
    ∃ b a', (fieldDomsResolve fe xs).run a = .ok (b, a') ∧ KeepPost dn v fe decW0B m m' a' r b := by
  induction n with
  | zero => intro m m' a v o l xs r h; simp [fdrW] at h
  | succ n ih =>
    intro m m' a v o l xs r h hS hd hb ht
    by_cases hl : l = 0
    · subst hl
      rw [fdrW_nil n m v o 0 rfl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : xs = [] := by simpa [decHL, hslice?] using hd.symm
      subst this
      exact ⟨true, a, rfl, hS, IWGrow.refl m, by simp [decW0B]⟩
    · obtain ⟨w, xs', rfl, hw, hw32, hd'⟩ := decHL_cons hd hl hb
      obtain ⟨hsum, -⟩ := toNat_succ_of_lt hb hl
      rw [fdrW_cons n m v o l hl, hw] at h
      cases h1 : stubM "fvar_type_d" m [w] with
      | none => rw [h1] at h; simp [fdrK1] at h
      | some x1 =>
      obtain ⟨ra, m1⟩ := x1
      rw [h1, fdrK1_some] at h
      obtain ⟨t, a1, hrun1, hS1, hg1, ht32, hteq⟩ := fvarTypeD_spec dn v fe w hw32 m m1 a ra h1 hS
      cases h2 : stubM "consts_resolve_ffast" m1 [v, ra.headD 0] with
      | none => rw [h2] at h; simp [fdrK2] at h
      | some x2 =>
      obtain ⟨rb, m2⟩ := x2
      rw [h2] at h
      obtain ⟨c, a2, hrun2, hS2, hg2, hceq, hc1⟩ :=
        constsResolveFFast_spec dn v fe (ra.headD 0) ht32 m1 m2 a1 rb h2 hS1
      have hrun12 : ∀ (k : Bool → AM Bool),
          (do let t ← fvarTypeD (decI w); let c ← constsResolveFFast fe t; k c).run a = (k c).run a2 := by
        intro k
        simp only [StateT.run_bind]
        rw [hrun1]
        simp only [bind, Except.bind]
        rw [← hteq, hrun2]
      by_cases hz : rb.headD 0 = 0
      · rw [fdrK2_no n m2 v o l rb hz] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hc : c = false := by rw [← hceq, hz]; rfl
        subst hc
        refine ⟨false, a2, ?_, hS2, hg1.trans hg2, by simp [decW0B]⟩
        have := hrun12 (fun c => if c then fieldDomsResolve fe xs' else pure false)
        simp only [fieldDomsResolve]
        rw [this]; rfl
      · rw [fdrK2_yes n m2 v o l rb hz] at h
        have hc : c = true := by rw [← hceq]; exact bne_iff_ne.mpr hz
        subst hc
        cases h3 : fdrW n m2 v (o + 1) (l - 1) with
        | none => rw [h3] at h; simp [resK] at h
        | some x3 =>
        obtain ⟨r3, m3⟩ := x3
        rw [h3, resK_some] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hg12 := hg1.trans hg2
        obtain ⟨b3, a3, hrun3, hS3, hg3, hd3, hd31⟩ := ih m2 m3 a2 v (o + 1) (l - 1) xs' r3 h3 hS2
          (by rw [decHL_grow hg12 (by omega)]; exact hd') (by omega) (by have := hg12.1; omega)
        refine ⟨b3, a3, ?_, hS3, hg12.trans hg3, by simpa [decW0B] using And.intro hd3 hd31⟩
        have := hrun12 (fun c => if c then fieldDomsResolve fe xs' else pure false)
        simp only [fieldDomsResolve]
        rw [this]; exact hrun3

theorem iarW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (v o l : Word) (xs : List EIdx) (r : List Word),
    iarW n m v o l = some (r, m') → StageR dn v fe m a → decHL m o.toNat l.toNat = some xs →
    o.toNat + l.toNat < 2 ^ 64 → o.toNat + l.toNat ≤ iwTop m →
    ∃ b a', (idxArgsResolve fe xs).run a = .ok (b, a') ∧ KeepPost dn v fe decW0B m m' a' r b := by
  induction n with
  | zero => intro m m' a v o l xs r h; simp [iarW] at h
  | succ n ih =>
    intro m m' a v o l xs r h hS hd hb ht
    by_cases hl : l = 0
    · subst hl
      rw [iarW_nil n m v o 0 rfl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : xs = [] := by simpa [decHL, hslice?] using hd.symm
      subst this
      exact ⟨true, a, rfl, hS, IWGrow.refl m, by simp [decW0B]⟩
    · obtain ⟨w, xs', rfl, hw, hw32, hd'⟩ := decHL_cons hd hl hb
      obtain ⟨hsum, -⟩ := toNat_succ_of_lt hb hl
      rw [iarW_cons n m v o l hl, hw] at h
      cases h2 : stubM "consts_resolve_ffast" m [v, w] with
      | none => rw [h2] at h; simp [iarK] at h
      | some x2 =>
      obtain ⟨rb, m2⟩ := x2
      rw [h2] at h
      obtain ⟨c, a2, hrun2, hS2, hg2, hceq, hc1⟩ :=
        constsResolveFFast_spec dn v fe w hw32 m m2 a rb h2 hS
      have hrun12 : ∀ (k : Bool → AM Bool),
          (do let c ← constsResolveFFast fe (decI w); k c).run a = (k c).run a2 := by
        intro k
        simp only [StateT.run_bind]
        rw [hrun2]
        rfl
      by_cases hz : rb.headD 0 = 0
      · rw [iarK_no n m2 v o l rb hz] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hc : c = false := by rw [← hceq, hz]; rfl
        subst hc
        refine ⟨false, a2, ?_, hS2, hg2, by simp [decW0B]⟩
        have := hrun12 (fun c => if c then idxArgsResolve fe xs' else pure false)
        simp only [idxArgsResolve]
        rw [this]; rfl
      · rw [iarK_yes n m2 v o l rb hz] at h
        have hc : c = true := by rw [← hceq]; exact bne_iff_ne.mpr hz
        subst hc
        cases h3 : iarW n m2 v (o + 1) (l - 1) with
        | none => rw [h3] at h; simp [resK'] at h
        | some x3 =>
        obtain ⟨r3, m3⟩ := x3
        rw [h3, resK'_some] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨b3, a3, hrun3, hS3, hg3, hd3, hd31⟩ := ih m2 m3 a2 v (o + 1) (l - 1) xs' r3 h3 hS2
          (by rw [decHL_grow hg2 (by omega)]; exact hd') (by omega) (by have := hg2.1; omega)
        refine ⟨b3, a3, ?_, hS3, hg2.trans hg3, by simpa [decW0B] using And.intro hd3 hd31⟩
        have := hrun12 (fun c => if c then idxArgsResolve fe xs' else pure false)
        simp only [idxArgsResolve]
        rw [this]; exact hrun3

/-! ## The census theorems -/

/-- **`field_doms_resolve` refines `fieldDomsResolve`** (through the stubs `fvar_type_d`,
`consts_resolve_ffast`), at the view `vis0` of the pre-block environment `fe₀`. -/
@[refines ConRon.Arena.fieldDomsResolve]
theorem fieldDomsResolve_refines (p : Prog)
    (hp : p.lookup "field_doms_resolve" = some fieldDomsResolveL) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe₀ : IFEnv) (vis0 o l : Word) (xs : List EIdx)
    (hS : StageR dn vis0 fe₀ s₀.mem a₀) (hd : decHL s₀.mem o.toNat l.toNat = some xs)
    (hb : o.toNat + l.toNat < 2 ^ 64) (ht : o.toNat + l.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "field_doms_resolve" [vis0, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (fieldDomsResolve fe₀ xs) a₀ ∧
      KeepPost dn vis0 fe₀ decW0B s₀.mem s'.mem (AM.st (fieldDomsResolve fe₀ xs) a₀) r
        (AM.res (fieldDomsResolve fe₀ xs) a₀); ⊤⦄ := by
  refine triple_post (fdrW_spec p hp n s₀ vis0 o l) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hpost⟩ := fdrW_ok dn fe₀ n _ _ a₀ vis0 o l xs r hm hS hd hb ht
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hpost⟩

/-- **`idx_args_resolve` refines `idxArgsResolve`** (through the stub `consts_resolve_ffast`),
at the view `vis0` of the pre-block environment `fe₀`. -/
@[refines ConRon.Arena.idxArgsResolve]
theorem idxArgsResolve_refines (p : Prog)
    (hp : p.lookup "idx_args_resolve" = some idxArgsResolveL) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe₀ : IFEnv) (vis0 o l : Word) (xs : List EIdx)
    (hS : StageR dn vis0 fe₀ s₀.mem a₀) (hd : decHL s₀.mem o.toNat l.toNat = some xs)
    (hb : o.toNat + l.toNat < 2 ^ 64) (ht : o.toNat + l.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "idx_args_resolve" [vis0, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (idxArgsResolve fe₀ xs) a₀ ∧
      KeepPost dn vis0 fe₀ decW0B s₀.mem s'.mem (AM.st (idxArgsResolve fe₀ xs) a₀) r
        (AM.res (idxArgsResolve fe₀ xs) a₀); ⊤⦄ := by
  refine triple_post (iarW_spec p hp n s₀ vis0 o l) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hpost⟩ := iarW_ok dn fe₀ n _ _ a₀ vis0 o l xs r hm hS hd hb ht
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hpost⟩

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `struct_proj_arg_p`: `t.j` -/

/-- After `mk_proj`. -/
def spaK2 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (e, m2) => some ([e], m2)
/-- After `intern_bvar`. -/
def spaK (T j : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (b, m1) => spaK2 (mkProjW m1 T j b)
/-- **The model of `struct_proj_arg_p`.** -/
def spaW (m : Mem) (T j : Word) : Option (List Word × Mem) := spaK T j (binternW m 0)

theorem spaK_some (T j b : Word) (m1 : Mem) : spaK T j (some (b, m1)) = spaK2 (mkProjW m1 T j b) := rfl
theorem spaK2_some (e : Word) (m2 : Mem) : spaK2 (some (e, m2)) = some ([e], m2) := rfl
grind_pattern [ind_grind] spaK_some => spaK T j (some (b, m1))
grind_pattern [ind_grind] spaK2_some => spaK2 (some (e, m2))

theorem spaW_spec (p : Prog) (hd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hjf : p.lookup "proj_find" = some projFind) (hjp : p.lookup "proj_push" = some projPush)
    (hji : p.lookup "intern_proj" = some internProj) (hmp : p.lookup "mk_proj" = some mkProj)
    (hp : p.lookup "struct_proj_arg_p" = some structProjArgPL) (n : Nat) (s₀ : St) (T j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_arg_p" [T, j]
    ⦃fun r s' => LocEq s' s₀ ∧ spaW s₀.mem T j = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structProjArgPL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        internBVar_spec p hpf hpp hib n, mkProj_spec p hd hjf hjp hji hmp n] <;>
      finish [spaW]

/-- **`struct_proj_arg_p` refines `structProjArgP`** under the stage relation. -/
@[refines ConRon.Arena.structProjArgP]
theorem structProjArgP_refines (p : Prog) (hd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hjf : p.lookup "proj_find" = some projFind) (hjp : p.lookup "proj_push" = some projPush)
    (hji : p.lookup "intern_proj" = some internProj) (hmp : p.lookup "mk_proj" = some mkProj)
    (hp : p.lookup "struct_proj_arg_p" = some structProjArgPL) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (T j : Word)
    (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_arg_p" [T, j]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structProjArgP (decI T) j.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (structProjArgP (decI T) j.toNat) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      AM.res (structProjArgP (decI T) j.toNat) a₀ = decE (r.headD 0); ⊤⦄ := by
  refine triple_post (spaW_spec p hd hpf hpp hib hjf hjp hji hmp hp n s₀ T j) ?_
  rintro r s' ⟨hl, hm⟩
  simp only [spaW] at hm
  cases h1 : binternW s₀.mem 0 with
  | none => rw [h1] at hm; cases hm
  | some x =>
  obtain ⟨b, m1⟩ := x
  rw [h1, spaK_some] at hm
  cases h2 : mkProjW m1 T j b with
  | none => rw [h2] at hm; cases hm
  | some y =>
  obtain ⟨e, m2⟩ := y
  rw [h2, spaK2_some] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  obtain ⟨a1, hr1, hS1, hg1⟩ := internBVar_stage hS 0 h1
  obtain ⟨a2, hr2, hS2, hg2⟩ := mkProj_stage hS1 T j b h2
  have hrun : (structProjArgP (decI T) j.toNat).run a₀ = .ok (decE e, a2) := by
    simp only [structProjArgP, StateT.run_bind]
    rw [show (0 : Word).toNat = 0 from rfl] at hr1
    rw [hr1]
    exact hr2
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS2, hg1.trans hg2, by rw [hres]; rfl⟩

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `struct_ps_at`, `struct_proj_ps`: the spine wrappers -/

/-- **The model of `struct_ps_at`** (the callee runs at the caller's fuel less one). -/
def psAtW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, o, nP => psK3 (psGoW n m o nP nP 0)

theorem psAtW_succ (n : Nat) (m : Mem) (o nP : Word) :
    psAtW (n + 1) m o nP = psK3 (psGoW n m o nP nP 0) := rfl
grind_pattern [ind_grind] psAtW_succ => psAtW (n + 1) m o nP

/-- **The model of `struct_proj_ps`.** -/
def projPsW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, nP => psK3 (psAtW n m 1 nP)

theorem projPsW_succ (n : Nat) (m : Mem) (nP : Word) :
    projPsW (n + 1) m nP = psK3 (psAtW n m 1 nP) := rfl
grind_pattern [ind_grind] projPsW_succ => projPsW (n + 1) m nP

section
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
  (hib : p.lookup "intern_bvar" = some internBVar)
  (hg : p.lookup "struct_ps_at_go" = some structPsAtGoL)
  (hp : p.lookup "struct_ps_at" = some structPsAtL)
include ha hc hsc hpf hpp hib hg hp

theorem psAtW_spec (n : Nat) (s₀ : St) (o nP : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_ps_at" [o, nP]
    ⦃fun r s' => LocEq s' s₀ ∧ psAtW n s₀.mem o nP = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structPsAtL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        structPsAtGo_spec p ha hc hsc hpf hpp hib hg n] <;>
      finish

theorem projPsW_spec (hq : p.lookup "struct_proj_ps" = some structProjPsL) (n : Nat) (s₀ : St)
    (nP : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_ps" [nP]
    ⦃fun r s' => LocEq s' s₀ ∧ projPsW n s₀.mem nP = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq]
  simp only [callFn, structProjPsL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        psAtW_spec p ha hc hsc hpf hpp hib hg hp n] <;>
      finish

end

/-- The model of `struct_ps_at` refines `structPsAt`. -/
theorem psAtW_ok (n : Nat) (m m' : Mem) (a : AState) (o nP : Word) (r : List Word)
    (h : psAtW n m o nP = some (r, m')) (hR : ArenaR m a) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hon : o.toNat + nP.toNat < 2 ^ 64) :
    ∃ xs a', (structPsAt o.toNat nP.toNat).run a = .ok (xs, a') ∧
      ArenaR m' a' ∧ IWGrow m m' ∧ (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  cases n with
  | zero => cases h
  | succ n =>
    rw [psAtW_succ] at h
    cases hg : psGoW n m o nP nP 0 with
    | none => rw [hg] at h; cases h
    | some x =>
    obtain ⟨r0, m0⟩ := x
    rw [hg, psK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨xs, a', hrun, hR', hgr, hs, hd, ht⟩ :=
      psGoW_ok n m m0 a o nP nP 0 r0 hg hR hsz hc hon (by simp)
    exact ⟨xs, a', by simpa [structPsAt] using hrun, hR', hgr, hs, by simpa using hd, by simpa using ht⟩

/-- **`struct_ps_at` refines `structPsAt`** under `ArenaR`. -/
@[refines ConRon.Arena.structPsAt]
theorem structPsAt_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hg : p.lookup "struct_ps_at_go" = some structPsAtGoL)
    (hp : p.lookup "struct_ps_at" = some structPsAtL) (n : Nat) (s₀ : St) (a₀ : AState)
    (o nP : Word) (hR : ArenaR s₀.mem a₀) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hc2 : 200 < (s₀.mem.arr64 CTL).size) (hon : o.toNat + nP.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_ps_at" [o, nP]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structPsAt o.toNat nP.toNat) a₀ ∧
      ArenaR s'.mem (AM.st (structPsAt o.toNat nP.toNat) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (structPsAt o.toNat nP.toNat) a₀); ⊤⦄ := by
  refine triple_post (psAtW_spec p ha hc hsc hpf hpp hib hg hp n s₀ o nP) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨xs, a', hrun, hR', hgr, -, hd, -⟩ := psAtW_ok n _ _ _ _ _ _ hm hR hsz hc2 hon
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hR', hgr, by rw [hres]; exact hd⟩

/-- **`struct_proj_ps` refines `structProjPs`** under `ArenaR`. -/
@[refines ConRon.Arena.structProjPs]
theorem structProjPs_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hg : p.lookup "struct_ps_at_go" = some structPsAtGoL)
    (hp : p.lookup "struct_ps_at" = some structPsAtL)
    (hq : p.lookup "struct_proj_ps" = some structProjPsL) (n : Nat) (s₀ : St) (a₀ : AState)
    (nP : Word) (hR : ArenaR s₀.mem a₀) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hc2 : 200 < (s₀.mem.arr64 CTL).size) (hon : 1 + nP.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_ps" [nP]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structProjPs nP.toNat) a₀ ∧
      ArenaR s'.mem (AM.st (structProjPs nP.toNat) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (structProjPs nP.toNat) a₀); ⊤⦄ := by
  refine triple_post (projPsW_spec p ha hc hsc hpf hpp hib hg hp hq n s₀ nP) ?_
  rintro r s' ⟨hl, hm⟩
  cases n with
  | zero => cases hm
  | succ n =>
  rw [projPsW_succ] at hm
  cases h1 : psAtW n s₀.mem 1 nP with
  | none => rw [h1] at hm; cases hm
  | some x =>
  obtain ⟨r0, m0⟩ := x
  rw [h1, psK3_some] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  obtain ⟨xs, a', hrun, hR', hgr, -, hd, -⟩ := psAtW_ok n _ _ _ _ _ _ h1 hR hsz hc2 (by simpa using hon)
  have hrun' : (structProjPs nP.toNat).run a₀ = .ok (xs, a') := by simpa [structProjPs] using hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  exact ⟨hl, hok, by rw [hst]; exact hR', hgr, by rw [hres]; simpa using hd⟩

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `whnf_telescope` -/

/-- After `sl_cons`: the slice and the sort. -/
def wtK6 (s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ro, m5) => some ([ro.headD 0, ro.tail.headD 0, s], m5)

mutual
/-- **The model of `whnf_telescope`.** -/
def wtW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, vis, i, n, e => wtK1 k vis i n (stubM "whnf_top" m [vis, i, e])
/-- After `whnf`: the view. -/
def wtK1 (k : Nat) (vis i n : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => wtK2 k vis i n m1 (eViewW m1 (r1.headD 0))
/-- The view's arms. -/
def wtK2 (k : Nat) (vis i n : Word) (m1 : Mem) (v : List Word) : Option (List Word × Mem) :=
  if v.headD 0 = 2 ∧ n = 0 then some ([0, 0, v.tail.headD 0], m1)
  else if v.headD 0 = 6 ∧ n ≠ 0 then
    wtK3 k vis i n (v.tail.headD 0) (v.tail.tail.headD 0) (fvinternW m1 i (v.tail.headD 0))
  else none
/-- After `intern_fvar`. -/
def wtK3 (k : Nat) (vis i n x y : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (fv, m2) =>
    if 4294967296 ≤ fv then none
    else wtK4 k vis i n x (i1F m2 [CWF, y, fv, 0])
/-- After `instantiate1_fast`: the recursion. -/
def wtK4 (k : Nat) (vis i n x : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m3) => wtK5 k x (wtW k m3 vis (i + 1) (n - 1) (rb.headD 0))
/-- After the recursion: the cons. -/
def wtK5 (k : Nat) (x : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m4) => wtK6 (rr.tail.tail.headD 0) (consW k m4 x (rr.headD 0) (rr.tail.headD 0))
end

section arms
variable (k : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis i n e x y s fv : Word) (v r1 rb rr ro : List Word)
theorem wtW_succ : wtW (k + 1) m vis i n e = wtK1 k vis i n (stubM "whnf_top" m [vis, i, e]) := by
  simp [wtW]
theorem wtK1_some : wtK1 k vis i n (some (r1, m1)) = wtK2 k vis i n m1 (eViewW m1 (r1.headD 0)) := by
  rw [wtK1]
theorem wtK2_sort (h : v.headD 0 = 2) (hn : n = 0) :
    wtK2 k vis i n m1 v = some ([0, 0, v.tail.headD 0], m1) := by
  rw [wtK2, if_pos ⟨h, hn⟩]
theorem wtK2_pi (h : v.headD 0 = 6) (hn : n ≠ 0) :
    wtK2 k vis i n m1 v =
      wtK3 k vis i n (v.tail.headD 0) (v.tail.tail.headD 0) (fvinternW m1 i (v.tail.headD 0)) := by
  rw [wtK2, if_neg (fun h' => by rw [h] at h'; exact absurd h'.1 (by decide)), if_pos ⟨h, hn⟩]
theorem wtK2_none (h1 : ¬ (v.headD 0 = 2 ∧ n = 0)) (h2 : ¬ (v.headD 0 = 6 ∧ n ≠ 0)) :
    wtK2 k vis i n m1 v = none := by simp only [wtK2, if_neg h1, if_neg h2]
theorem wtK3_big (h : 4294967296 ≤ fv) : wtK3 k vis i n x y (some (fv, m2)) = none := by
  simp [wtK3, h]
theorem wtK3_ok (h : ¬ 4294967296 ≤ fv) : wtK3 k vis i n x y (some (fv, m2)) =
    wtK4 k vis i n x (i1F m2 [CWF, y, fv, 0]) := by
  simp only [wtK3, if_neg h]
theorem wtK4_some : wtK4 k vis i n x (some (rb, m3)) =
    wtK5 k x (wtW k m3 vis (i + 1) (n - 1) (rb.headD 0)) := by rw [wtK4]
theorem wtK5_some : wtK5 k x (some (rr, m4)) =
    wtK6 (rr.tail.tail.headD 0) (consW k m4 x (rr.headD 0) (rr.tail.headD 0)) := by rw [wtK5]
theorem wtK6_some : wtK6 s (some (ro, m5)) = some ([ro.headD 0, ro.tail.headD 0, s], m5) := rfl
end arms

grind_pattern [ind_grind] wtW_succ => wtW (k + 1) m vis i n e
grind_pattern [ind_grind] wtK1_some => wtK1 k vis i n (some (r1, m1))
grind_pattern [ind_grind] wtK2_sort => wtK2 k vis i n m1 v
grind_pattern [ind_grind] wtK2_pi => wtK2 k vis i n m1 v
grind_pattern [ind_grind] wtK2_none => wtK2 k vis i n m1 v
grind_pattern [ind_grind] wtK3_big => wtK3 k vis i n x y (some (fv, m2))
grind_pattern [ind_grind] wtK3_ok => wtK3 k vis i n x y (some (fv, m2))
grind_pattern [ind_grind] wtK4_some => wtK4 k vis i n x (some (rb, m3))
grind_pattern [ind_grind] wtK5_some => wtK5 k x (some (rr, m4))
grind_pattern [ind_grind] wtK6_some => wtK6 s (some (ro, m5))

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hv : p.lookup "e_view" = some eView)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hp : p.lookup "whnf_telescope" = some whnfTelescopeL) (hi1 : I1Prog p)
include ha hc hsc hv hff hfp hif hp hi1

theorem wtW_spec (k : Nat) : ∀ (s₀ : St) (vis i n e : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "whnf_telescope" [vis, i, n, e]
    ⦃fun r s' => LocEq s' s₀ ∧ wtW k s₀.mem vis i n e = some (r, s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ vis i n e; rw [invoke_eq _ hp]; simp only [callFn, whnfTelescopeL]
    vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ vis i n e
    rw [invoke_eq _ hp]
    simp only [callFn, whnfTelescopeL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        stubM_spec p "whnf_top" k, eView_spec p hv k, internFVar_spec p hff hfp hif k,
        i1F_spec p hi1 k, slCons_specW p ha hc hsc k, ih] <;>
      finish (gen := 20)

end spec

local notation "V" => ConLeche.CheckMode.verified

/-! ### The twin, one level unfolded

`whnfTelescope` is structural recursion that matches under a bind, so Lean generates no equation
lemma for it (PLAN.md's vcgen gaps). `wtArm` is its body after the view, and `whnfTelescope_eq`
the unfolding, by `Nat.brecOn` and a case split on the view. -/

/-- The arms of `whnfTelescope` after the view. -/
def wtArm (mode : ConLeche.CheckMode) (fe : IFEnv) (i : Nat) :
    ENodeView → Nat → AM (List EIdx × LIdx)
  | .sort s, 0 => pure ([], s)
  | .sort _, _ + 1 => fail (.invalid "direct sum: type former does not reduce to a telescope")
  | .forallE _ _, 0 => fail (.invalid "direct sum: type former does not reduce to a sort")
  | .forallE dom body, n + 1 => do
      let fv ← internE (.fvar i dom)
      let b ← instantiate1Fast coreWalkFuel body fv 0
      let x ← whnfTelescope mode fe (i + 1) n b
      pure (dom :: x.1, x.2)
  | _, 0 => fail (.invalid "direct sum: type former does not reduce to a sort")
  | _, _ + 1 => fail (.invalid "direct sum: type former does not reduce to a telescope")

theorem whnfTelescope_eq (mode : ConLeche.CheckMode) (fe : IFEnv) (i n : Nat) (e : EIdx) :
    whnfTelescope mode fe i n e = (do
      let e' ← whnf mode fe checkFuel i e
      let v ← view e'
      wtArm mode fe i v n) := by
  cases n <;>
  · delta whnfTelescope
    dsimp only [Nat.brecOn, Nat.brecOn.go, whnfTelescope._f]
    refine congrArg (whnf mode fe checkFuel i e >>= ·) (funext fun e' => ?_)
    refine congrArg (view e' >>= ·) (funext fun v => ?_)
    cases v <;> first | rfl |
      (simp only [wtArm]; delta whnfTelescope; dsimp only [Nat.brecOn, Nat.brecOn.go])

/-- **The model of `whnf_telescope` refines `whnfTelescope`.** -/
theorem wtW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (vis i n e : Word) (r : List Word),
    wtW k m vis i n e = some (r, m') → StageR dn vis fe m a → H e →
    i.toNat + n.toNat < 2 ^ 64 →
    ∃ bs s a', (whnfTelescope V fe i.toNat n.toNat (decI e)).run a = .ok ((bs, s), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some bs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧
      (r.tail.tail.headD 0).toNat < 2 ^ 32 ∧ decI (r.tail.tail.headD 0) = s := by
  induction k with
  | zero => intro m m' a vis i n e r h; simp [wtW] at h
  | succ k ih =>
    intro m m' a vis i n e r h hS he hin
    rw [wtW_succ] at h
    cases h1 : stubM "whnf_top" m [vis, i, e] with
    | none => rw [h1] at h; simp [wtK1] at h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1, wtK1_some] at h
    obtain ⟨e', a1, hrun1, hS1, hg1, he'32, he'eq⟩ := whnf_spec dn vis fe i e he m m1 a r1 h1 hS
    rw [whnfTelescope_eq, StateT.run_bind, hrun1]
    simp only [bind, Except.bind]
    rw [← he'eq]
    generalize hw : r1.headD 0 = w at h he'32
    generalize hv : eViewW m1 w = v at h
    by_cases hs : v.headD 0 = 2 ∧ n = 0
    · rw [wtK2_sort k m1 vis i n v hs.1 hs.2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hne : v ≠ [] := fun h0 => by rw [h0] at hs; simp at hs
      obtain ⟨vv, hview, hVR⟩ := eViewW_ok m1 a1 hS1.1.arena.1 w (hv ▸ hne)
      rw [hv] at hVR
      have hb : ∀ {β : Type} (f : ENodeView → AM β),
          (StateT.bind (view (decI w)) f).run a1 = (f vv).run a1 := by
        intro β f
        show (view (decI w) >>= f).run a1 = _
        rw [StateT.run_bind, ← decE_eq, view_run _ _ _ hview]; rfl
      rw [hb]
      cases vv with
      | sort u =>
        obtain ⟨-, hu32, hu⟩ := hVR
        rw [hs.2]
        refine ⟨[], u, a1, rfl, hS1, hg1, by simp [decHL, hslice?], by simp, ?_, ?_⟩
        · simpa [List.getD] using hu32
        · simpa [List.getD] using hu
      | _ => simp [ViewR] at hVR <;> (try omega) <;> (have := hs.1; simp_all)
    by_cases hp : v.headD 0 = 6 ∧ n ≠ 0
    · rw [wtK2_pi k m1 vis i n v hp.1 hp.2] at h
      have hne : v ≠ [] := fun h0 => by rw [h0] at hp; simp at hp
      obtain ⟨vv, hview, hVR⟩ := eViewW_ok m1 a1 hS1.1.arena.1 w (hv ▸ hne)
      rw [hv] at hVR
      have hb : ∀ {β : Type} (f : ENodeView → AM β),
          (StateT.bind (view (decI w)) f).run a1 = (f vv).run a1 := by
        intro β f
        show (view (decI w) >>= f).run a1 = _
        rw [StateT.run_bind, ← decE_eq, view_run _ _ _ hview]; rfl
      rw [hb]
      cases vv with
      | forallE ty body =>
        obtain ⟨-, hx32, hxe, hy32, hye⟩ := hVR
        have hx1 : v.getD 1 0 = v.tail.headD 0 := by cases v with | nil => rfl | cons _ t => cases t <;> rfl
        have hy1 : v.getD 2 0 = v.tail.tail.headD 0 := by
          cases v with | nil => rfl | cons _ t => cases t with | nil => rfl | cons _ u => cases u <;> rfl
        rw [hx1] at hx32 hxe
        rw [hy1] at hy32 hye
        generalize v.tail.headD 0 = x at h hx32 hxe
        generalize v.tail.tail.headD 0 = y at h hy32 hye
        have hn1 : 1 ≤ n.toNat := by
          rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
          · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hp.2
          · omega
        have hnm : (n - 1).toNat = n.toNat - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hn1))]; simp
        have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
        have hns : n.toNat = (n.toNat - 1) + 1 := by omega
        rw [hns]
        simp only [wtArm]
        cases h2 : fvinternW m1 i x with
        | none => rw [h2] at h; simp [wtK3] at h
        | some x2 =>
        obtain ⟨fv, m2⟩ := x2
        rw [h2] at h
        by_cases hfv : 4294967296 ≤ fv
        · rw [wtK3_big k m2 vis i n x y fv hfv] at h; cases h
        rw [wtK3_ok k m2 vis i n x y fv hfv] at h
        have hfv32 : fv.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ fv.toNat := hfv; omega
        obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 i x hx32 h2
        cases h3 : i1F m2 [CWF, y, fv, 0] with
        | none => rw [h3] at h; simp [wtK4] at h
        | some x3 =>
        obtain ⟨rb, m3⟩ := x3
        rw [h3, wtK4_some] at h
        obtain ⟨b', a3, hrun3, hS3, hg3, hb32, hbeq⟩ :=
          i1F_ok dn vis fe y fv 0 hy32 m2 m3 a2 rb h3 hS2
        cases h4 : wtW k m3 vis (i + 1) (n - 1) (rb.headD 0) with
        | none => rw [h4] at h; simp [wtK5] at h
        | some x4 =>
        obtain ⟨rr, m4⟩ := x4
        rw [h4, wtK5_some] at h
        obtain ⟨bs, s', a4, hrun4, hS4, hg4, hd4, ht4, hs32, hseq⟩ :=
          ih m3 m4 a3 vis (i + 1) (n - 1) (rb.headD 0) rr h4 hS3 hb32 (by omega)
        cases h5 : consW k m4 x (rr.headD 0) (rr.tail.headD 0) with
        | none => rw [h5] at h; simp [wtK6] at h
        | some x5 =>
        obtain ⟨ro, m5⟩ := x5
        rw [h5, wtK6_some] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hS5, hg5, hd5, ht5⟩ := consW_stage h5 hS4 ht4 hx32 hd4
        refine ⟨ty :: bs, s', a4, ?_, hS5, (((hg1.trans hg2).trans hg3).trans hg4).trans hg5,
          by rw [← hxe, decE_eq]; exact hd5, Nat.le_of_eq ht5, hs32, hseq⟩
        simp only [StateT.run_bind, StateT.run_pure]
        have hrun2' : (internE (.fvar i.toNat ty)).run a1 = .ok (decE fv, a2) := by
          rw [← hxe]; exact hrun2
        rw [hrun2']
        simp only [bind, Except.bind]
        rw [CWF_eq, show (0 : Word).toNat = 0 from rfl, ← decE_eq y, hye, ← decE_eq fv] at hrun3
        rw [hrun3]
        simp only [bind, Except.bind]
        rw [hi1, hnm, hbeq] at hrun4
        rw [hrun4]
        rfl
      | _ => simp [ViewR] at hVR <;> (try omega) <;> (have := hp.1; simp_all)
    · rw [wtK2_none k m1 vis i n v hs hp] at h; cases h

/-- **`whnf_telescope` refines `whnfTelescope .verified`** (through the stub `whnf`): the binders' domains as an `IW` slice, the sort as a word. -/
@[refines ConRon.Arena.whnfTelescope]
theorem whnfTelescope_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hv : p.lookup "e_view" = some eView)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hp : p.lookup "whnf_telescope" = some whnfTelescopeL) (hi1 : I1Prog p) (k : Nat) (s₀ : St)
    (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis i n e : Word)
    (hS : StageR dn vis fe s₀.mem a₀) (he : H e) (hin : i.toNat + n.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "whnf_telescope" [vis, i, n, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (whnfTelescope V fe i.toNat n.toNat (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (whnfTelescope V fe i.toNat n.toNat (decI e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (whnfTelescope V fe i.toNat n.toNat (decI e)) a₀).1 ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧
      (r.tail.tail.headD 0).toNat < 2 ^ 32 ∧
      decI (r.tail.tail.headD 0) = (AM.res (whnfTelescope V fe i.toNat n.toNat (decI e)) a₀).2; ⊤⦄ := by
  refine triple_post (wtW_spec p ha hc hsc hv hff hfp hif hp hi1 k s₀ vis i n e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨bs, s, a', hrun, hS', hg, hd, ht, hs32, hs⟩ := wtW_ok dn fe k _ _ _ _ _ _ _ _ hm hS he hin
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hd, ht, hs32, by rw [hres]; exact hs⟩

end L.Ind

