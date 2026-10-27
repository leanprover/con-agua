import ConAgua.Arena.IndInstall
import ConAgua.Arena.IndRealFvtD
import ConAgua.Arena.IndCallM

/-!
# Refinements of `IndInstall` (lane `induct`)

`check_block_doms_at` refines `ConRon.Arena.checkBlockDomsAt .verified`, by the lane's template
(`IndSumSpec.lean`'s `struct_ps_at_go`): a word model `domsW` that calls the stubs' word models
(`stubM`) and itself, a `vcgen` spec of `domsW` with no twin values in sight, a relational lemma
(by induction on the model's fuel) using the stubs' `RelAM` facts, and the census theorem by
`triple_post` + `AM.of_run_ok`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `domsW`: the word model of `check_block_doms_at` -/

mutual
/-- **The model of `check_block_doms_at`.** `j = 0`: `return 0`, no callee touched. Otherwise:
abort if either index is out of the (logical) list length, else call `fvar_type_d` then
`is_def_eq_core`, then recurse at `j - 1`. -/
def domsW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, off, fo, fl, dO, dl, j =>
    if j = 0 then some ([0], m)
    else if fl ≤ j - 1 then none
    else if dl ≤ j - 1 then none
    else
      domsK1 cR n vis off fo fl dO dl j (rdW (m.arr64 IW) (dO + (j - 1)))
        (ftdF m [rdW (m.arr64 IW) (fo + (j - 1))])

/-- After `fvar_type_d`: call `is_def_eq_core`. -/
def domsK1 (cR : CallM) (n : Nat) (vis off fo fl dO dl j b : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m1) =>
    domsK2 cR n vis off fo fl dO dl j
      (cR n "is_def_eq_core" [vis, off + (j - 1), ra.headD 0, b] m1)

/-- After `is_def_eq_core`: `unless ok do abort`, then the recursive call. -/
def domsK2 (cR : CallM) (n : Nat) (vis off fo fl dO dl j : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m2) =>
    if rb.headD 0 = 0 then none else domsK3 (domsW cR n m2 vis off fo fl dO dl (j - 1))

/-- After the recursive call: `u := call …; return u` returns the callee's first word. -/
def domsK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

section arms
variable (cR : CallM) (n : Nat) (m m1 m2 : Mem) (vis off fo fl dO dl j b : Word) (ra rb : List Word)

theorem domsW_zero (hj : j = 0) : domsW cR (n + 1) m vis off fo fl dO dl j = some ([0], m) := by
  simp [domsW, hj]
theorem domsW_abortF (hj : j ≠ 0) (hfl : fl ≤ j - 1) :
    domsW cR (n + 1) m vis off fo fl dO dl j = none := by simp [domsW, hj, hfl]
theorem domsW_abortD (hj : j ≠ 0) (hfl : ¬ fl ≤ j - 1) (hdl : dl ≤ j - 1) :
    domsW cR (n + 1) m vis off fo fl dO dl j = none := by simp [domsW, hj, hfl, hdl]
theorem domsW_cons (hj : j ≠ 0) (hfl : ¬ fl ≤ j - 1) (hdl : ¬ dl ≤ j - 1) :
    domsW cR (n + 1) m vis off fo fl dO dl j =
      domsK1 cR n vis off fo fl dO dl j (rdW (m.arr64 IW) (dO + (j - 1)))
        (ftdF m [rdW (m.arr64 IW) (fo + (j - 1))]) := by
  simp [domsW, hj, hfl, hdl]
theorem domsK1_some :
    domsK1 cR n vis off fo fl dO dl j b (some (ra, m1)) =
      domsK2 cR n vis off fo fl dO dl j
        (cR n "is_def_eq_core" [vis, off + (j - 1), ra.headD 0, b] m1) := by
  rw [domsK1]
theorem domsK2_abort (heq : rb.headD 0 = 0) : domsK2 cR n vis off fo fl dO dl j (some (rb, m2)) = none := by
  rw [domsK2, ite_eq_left heq]
theorem domsK2_ok (heq : rb.headD 0 ≠ 0) :
    domsK2 cR n vis off fo fl dO dl j (some (rb, m2)) = domsK3 (domsW cR n m2 vis off fo fl dO dl (j - 1)) := by
  rw [domsK2, ite_eq_right heq]
theorem domsK3_some (r : List Word) (m : Mem) : domsK3 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] domsW_zero => domsW cR (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] domsW_abortF => domsW cR (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] domsW_abortD => domsW cR (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] domsW_cons => domsW cR (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] domsK1_some => domsK1 cR n vis off fo fl dO dl j b (some (ra, m1))
grind_pattern [ind_grind] domsK2_abort => domsK2 cR n vis off fo fl dO dl j (some (rb, m2))
grind_pattern [ind_grind] domsK3_some => domsK3 (some (r, m))
grind_pattern [ind_grind] domsK2_ok => domsK2 cR n vis off fo fl dO dl j (some (rb, m2))

/-! ## `domsW_spec`: the `vcgen` proof against the L code (no twin values) -/

section spec
variable (p : Prog) (hp : p.lookup "check_block_doms_at" = some checkBlockDomsAt) (hftd : FtdF p)
include hp hftd

theorem domsW_spec (cR : CallM) (hcR : CallSpec p cR) (n : Nat) : ∀ (s₀ : St) (vis off fo fl dO dl j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_doms_at" [vis, off, fo, fl, dO, dl, j]
    ⦃fun r s' => LocEq s' s₀ ∧ domsW cR n s₀.mem vis off fo fl dO dl j = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis off fo fl dO dl j
    rw [invoke_eq _ hp]; simp only [callFn, checkBlockDomsAt]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis off fo fl dO dl j
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockDomsAt]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        ftdF_spec0 p hftd n, hcR n "is_def_eq_core", ih] <;>
      finish (gen := 20)

end spec

/-! ## `domsW_ok`: the relational lemma, by induction on the model's fuel -/

theorem mapM_opt_congr {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons]
    rw [h x (List.mem_cons_self ..), mapM_opt_congr f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem decHL_grow {k : IdxKind} {m m' : Mem} (hg : IWGrow m m') {o l : Nat}
    (h : o + l ≤ iwTop m) : (decHL m' o l : Option (List (Idx k))) = decHL m o l := by
  simp only [decHL, hslice?]
  apply mapM_opt_congr
  intro j hj
  have hj' : j < l := List.mem_range.mp hj
  simp only [hd?, iwA]
  rw [hg.2.2.1 (o + j) (by omega)]

theorem decHL_getI {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL m o l = some xs) (j : Nat) (hj : j < l) :
    iwH m (o + j) = some (xs[j]'(by rw [decHL_length m h]; exact hj)) := by
  have hl := decHL_length m h
  simp only [decHL, hslice?] at h
  have hget := mapM_opt_get (fun j => hd? (iwA m) (o + j)) (List.range l) xs h j (by simpa using hj)
  simpa [iwH] using hget

theorem decHL_get' {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL m o l = some xs) (j : Nat) (hj : j < l) (hb : o + l < 2 ^ 64) :
    ∃ w, rdW (m.arr64 IW) (UInt64.ofNat (o + j)) = w ∧ w.toNat < 2 ^ 32 ∧
      xs[j]'(by rw [decHL_length m h]; exact hj) = decI w := by
  obtain ⟨w, h1, h2, h3⟩ := iwH_rdW (decHL_getI h j hj) (by omega)
  exact ⟨w, h1, h2, h3.symm⟩

/-! ## The census theorem -/

section census
variable (p : Prog) (hp : p.lookup "check_block_doms_at" = some checkBlockDomsAt) (hftd : FtdF p)
include hp hftd

end census

end L.Ind
