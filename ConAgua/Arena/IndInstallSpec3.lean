import ConAgua.Arena.IndRealSpine

/-!
# Refinements of `IndInstall`, part 3 (lane `indproofs`, helper `install`)

`lvl_eq_fueled` (through the `lvl_eq` stub) and `check_block_agree_one`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `lvl_eq_fueled` -/

/-- The model of `lvl_eq_fueled(u, v)`: the stub `lvl_eq`, `none` (word `0`) aborts. -/
def lveW (m : Mem) (u v : Word) : Option (List Word × Mem) :=
  match stubM "lvl_eq_c" m [u, v] with
  | none => none
  | some (r, m1) => if r.headD 0 = 0 then none else some ([if r.headD 0 = 2 then 1 else 0], m1)

/-- The model of `lvl_eq_fueled(u, v)` at L fuel `k`, its call of `lvl_eq_c` read through `cR`
(`lveW` is the stubs' reading, `lveC_stub`). -/
def lveC (cR : CallM) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, u, v =>
    match cR k "lvl_eq_c" [u, v] m with
    | none => none
    | some (r, m1) => if r.headD 0 = 0 then none else some ([if r.headD 0 = 2 then 1 else 0], m1)

theorem lvlEqFueled_specC (p : Prog) (hp : p.lookup "lvl_eq_fueled" = some lvlEqFueled) (cR : CallM)
    (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (u v : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "lvl_eq_fueled" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ lveC cR n s₀.mem u v = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lvlEqFueled]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, hcR n "lvl_eq_c"] <;>
      finish (gen := 20) [lveC]

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

/-- The per-member body of `checkBlockAgree` after member 0's telescope `fvs0` is opened. -/
def agreeBodyAM (fe : IFEnv) (nP : Nat) (fvs0 : List EIdx) (cvTa : IConstantVal) (s s₀ : LIdx) :
    AM Unit := do
  let tq ← unwrapOr (← openPisAtFvarsF nP cvTa.type 0)
    (.invalid "parameters of all inductive datatypes must match")
  unless tq.1.length == fvs0.length do
    fail (.invalid "parameters of all inductive datatypes must match")
  let doms ← fvarTypeDs fvs0
  ConRon.Arena.checkBlockDomsAt V fe 0 tq.1 doms nP
  unless ← liftFueled "level comparison" (← lvlEq? s s₀) do
    fail (.invalid "mutually inductive types must live in the same universe")

theorem agGetD1 (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, c⟩⟩ <;> rfl
theorem agGetD2 (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, d⟩⟩⟩ <;> rfl
theorem agGetD0 (r : List Word) : r.getD 0 0 = r.headD 0 := by
  rcases r with _ | ⟨a, b⟩ <;> rfl

theorem exc_ok_bind {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

end L.Ind
