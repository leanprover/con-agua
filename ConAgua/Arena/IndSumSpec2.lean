import ConAgua.Arena.IndInstallSpec

/-!
# Refinements of `IndSum`, second file (lane `indproofs`)

Functions of `IndSum.lean` whose proofs reuse `IndInstallSpec.lean` (which imports `IndSumSpec`).

* `check_struct_doms_at` refines `checkStructDomsAt`: its model is `check_block_doms_at`'s
  (`domsW`) with the empty result list, and the twin is `checkBlockDomsAt` up to the error
  message, so the relational lemma is `domsW_ok` and an `ok`-run transfer.
-/

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
