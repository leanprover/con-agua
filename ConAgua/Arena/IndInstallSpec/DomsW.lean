import ConAgua.Arena.IndInstallSpec.LvlEqFueledSpecC
import ConAgua.Arena.IndRealSpine
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# DomsW

`domsW`, `domsK1`, `domsK2`, `domsK3`, `domsW_zero`, `domsW_abortF` and the lemmas only they use.
-/

section

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

/-! ## `check_block_agree_one` -/

mutual
/-- **The model of `check_block_agree_one`**: the opened telescope, the member 0 domains, the
doms comparison, the universe comparison. -/
def agW (cR : CallM) (n : Nat) (m : Mem) (vis nP fvs0O fvs0L s0 cvTa s : Word) : Option (List Word × Mem) :=
  agK1 cR (n - 1) vis nP fvs0O fvs0L s0 s
    (cR (n - 1) "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (cvTa + 3), 0] m)

/-- After `open_pis_at_fvars_f`: `ok = 0` and a length mismatch abort, then `fvar_type_ds`. -/
def agK1 (cR : CallM) (n : Nat) (vis nP fvs0O fvs0L s0 s : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then none
    else if r.tail.tail.headD 0 ≠ fvs0L then none
    else agK2 cR n vis nP fvs0L s0 s r (ftdsF m1 [fvs0O, fvs0L])

/-- After `fvar_type_ds`: the doms comparison. -/
def agK2 (cR : CallM) (n : Nat) (vis nP _fvs0L s0 s : Word) (r : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rd, m2) =>
    agK3 cR n s0 s (domsW cR n m2 vis 0 (r.tail.headD 0) (r.tail.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) nP)

/-- After `check_block_doms_at`: `lvl_eq_fueled`. -/
def agK3 (cR : CallM) (n : Nat) (s0 s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m3) => agK4 (lveC cR n m3 s s0)

/-- After `lvl_eq_fueled`: `eq = 0` aborts. -/
def agK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (re, m4) => if re.headD 0 = 0 then none else some ([], m4)
end

section arms
variable (cR : CallM) (n : Nat) (m m1 m2 m3 : Mem) (vis nP fvs0O fvs0L s0 s : Word) (r rd re : List Word)
theorem agK1_abort0 (h : r.headD 0 = 0) : agK1 cR n vis nP fvs0O fvs0L s0 s (some (r, m1)) = none := by
  rw [agK1, ite_eq_left h]
theorem agK1_abortL (h0 : r.headD 0 ≠ 0) (h : r.tail.tail.headD 0 ≠ fvs0L) :
    agK1 cR n vis nP fvs0O fvs0L s0 s (some (r, m1)) = none := by
  rw [agK1, ite_eq_right h0, ite_eq_left h]
theorem agK1_ok (h0 : r.headD 0 ≠ 0) (h : r.tail.tail.headD 0 = fvs0L) :
    agK1 cR n vis nP fvs0O fvs0L s0 s (some (r, m1)) =
      agK2 cR n vis nP fvs0L s0 s r (ftdsF m1 [fvs0O, fvs0L]) := by
  rw [agK1, ite_eq_right h0, ite_eq_right (by simpa using h)]
theorem agK2_some : agK2 cR n vis nP fvs0L s0 s r (some (rd, m2)) =
    agK3 cR n s0 s (domsW cR n m2 vis 0 (r.tail.headD 0) (r.tail.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) nP) := rfl
theorem agK3_some (r' : List Word) : agK3 cR n s0 s (some (r', m3)) = agK4 (lveC cR n m3 s s0) := rfl
theorem agK4_ok (h : re.headD 0 ≠ 0) : agK4 (some (re, m1)) = some ([], m1) := by
  rw [agK4, ite_eq_right h]
theorem agK4_abort (h : re.headD 0 = 0) : agK4 (some (re, m1)) = none := by
  rw [agK4, ite_eq_left h]
end arms

grind_pattern [ind_grind] agK1_abort0 => agK1 cR n vis nP fvs0O fvs0L s0 s (some (r, m1))
grind_pattern [ind_grind] agK1_abortL => agK1 cR n vis nP fvs0O fvs0L s0 s (some (r, m1))
grind_pattern [ind_grind] agK1_ok => agK1 cR n vis nP fvs0O fvs0L s0 s (some (r, m1))
grind_pattern [ind_grind] agK2_some => agK2 cR n vis nP fvs0L s0 s r (some (rd, m2))
grind_pattern [ind_grind] agK3_some => agK3 cR n s0 s (some (r', m3))
grind_pattern [ind_grind] agK4_ok => agK4 (some (re, m1))
grind_pattern [ind_grind] agK4_abort => agK4 (some (re, m1))

theorem checkBlockAgreeOne_spec (p : Prog)
    (hd : p.lookup "check_block_doms_at" = some checkBlockDomsAt)
    (hl : p.lookup "lvl_eq_fueled" = some lvlEqFueled)
    (hp : p.lookup "check_block_agree_one" = some checkBlockAgreeOne) (had : AdF p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St)
    (vis nP fvs0O fvs0L s0 cvTa s : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_agree_one"
      [vis, nP, fvs0O, fvs0L, s0, cvTa, s]
    ⦃fun r s' => LocEq s' s₀ ∧ agW cR n s₀.mem vis nP fvs0O fvs0L s0 cvTa s = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockAgreeOne]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        hcR n "open_pis_at_fvars_f", ftdsF_spec p had n,
        domsW_spec p hd had.ftd cR hcR n, lvlEqFueled_specC p hl cR hcR n] <;>
      finish (gen := 20) [agW]

/-- A successful `domsW cR` has `j` within both lists. -/
theorem domsW_le {cR : CallM} {n : Nat} {m : Mem} {vis off fo fl dO dl j : Word} {r : List Word} {m' : Mem}
    (h : domsW cR n m vis off fo fl dO dl j = some (r, m')) :
    j.toNat ≤ fl.toNat ∧ j.toNat ≤ dl.toNat := by
  cases n with
  | zero => simp [domsW] at h
  | succ n =>
    by_cases hj : j = 0
    · subst hj; simp
    · have hjpos : 1 ≤ j.toNat := Nat.pos_of_ne_zero fun h0 => hj (UInt64.toNat_inj.mp (by simpa using h0))
      have hj1 : (j - 1).toNat = j.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hjpos))]
        simp
      by_cases hfl : fl ≤ j - 1
      · rw [domsW_abortF cR n m vis off fo fl dO dl j hj hfl] at h; simp at h
      by_cases hdl : dl ≤ j - 1
      · rw [domsW_abortD cR n m vis off fo fl dO dl j hj hfl hdl] at h; simp at h
      have h1 : ¬ fl.toNat ≤ (j - 1).toNat := by rw [← UInt64.le_iff_toNat_le]; exact hfl
      have h2 : ¬ dl.toNat ≤ (j - 1).toNat := by rw [← UInt64.le_iff_toNat_le]; exact hdl
      omega

theorem agGetD1 (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, c⟩⟩ <;> rfl
theorem agGetD2 (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, d⟩⟩⟩ <;> rfl
theorem agGetD0 (r : List Word) : r.getD 0 0 = r.headD 0 := by
  rcases r with _ | ⟨a, b⟩ <;> rfl

theorem exc_ok_bind {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

end L.Ind

end

end
