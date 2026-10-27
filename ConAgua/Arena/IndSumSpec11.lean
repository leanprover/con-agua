import ConAgua.Arena.IndPos2SpecB

/-!
# `check_struct_field_sorts_i` refines `checkStructFieldSortsI` (lane `indproofs2`)

The fields' sorts over the opened constructor telescope: per field (last to first) `fvar_type_d`,
`infer_type_core`, `ensure_sort_core` (stubs), then the universe bound — `lv_leq_top` (a stub
contract in `IndStubs.lean`: no stage-level model yet) unless the family is propositional, else
(large elimination) `lvl_eq_true` against `zeroLevel` or membership in the index arguments.
`check_struct_field_sorts_i_go` is the twin's recursion (L: rewritten from a `while` loop); the
sorts are written into a pre-allocated `IW` slice from its end, so its relational lemma carries
the already-written suffix (`acc`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `lvl_eq_true` -/

/-- After `lvl_eq_c`. -/
def eqTrueK : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m) => some (if r.headD 0 = 2 then 1 else 0, m)

theorem eqTrueK_some (r : List Word) (m : Mem) :
    eqTrueK (some (r, m)) = some (if r.headD 0 = 2 then 1 else 0, m) := rfl
attribute [ind_grind] eqTrueK_some

/-- The model of `lvl_eq_true(u, v)` at L fuel `k`, its `lvl_eq_c` call read through `cR`
(`eqTrueW` is the stubs' reading). -/
def eqTrueC (cR : CallM) : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, u, v => eqTrueK (cR k "lvl_eq_c" [u, v] m)

theorem eqTrueC_succ (cR : CallM) (k : Nat) (m : Mem) (u v : Word) :
    eqTrueC cR (k + 1) m u v = eqTrueK (cR k "lvl_eq_c" [u, v] m) := rfl

theorem eqTrue_specC (p : Prog) (hp : p.lookup "lvl_eq_true" = some lvlEqTrue) (cR : CallM)
    (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (u v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lvl_eq_true" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ eqTrueC cR n s₀.mem u v = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lvlEqTrue]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hcR n "lvl_eq_c"] <;>
      finish (gen := 20) [eqTrueC]

/-! ## `check_field_sort_bound`: the word model -/

/-- After `sl_contains`. -/
def cfbK4 (eq : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some ct => if eq = 0 ∧ ct = 0 then none else some ([0], m)
/-- After `lvl_eq_true`. -/
def cfbK3 (n : Nat) (io il fv : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (eq, m) => cfbK4 eq m (containsW n m io il fv)
/-- After `pin_word(53)`. -/
def cfbK2 (cR : CallM) (n : Nat) (io il fv u : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some z => cfbK3 n io il fv (eqTrueC cR n m u z)
/-- After `lv_leq_top`. -/
def cfbK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 2 then some ([0], m) else none

/-- **The model of `check_field_sort_bound(isProp, large, s, io, il, fv, u)`** at exec fuel `n`. -/
def cfbW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, isProp, large, s, io, il, fv, u =>
    if isProp = 0 then cfbK1 (cR n "lv_leq_top" [u, s] m)
    else if large ≠ 0 then cfbK2 cR n io il fv u m (pinWordV m 53)
    else some ([0], m)

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (isProp large s io il fv u eq ct z : Word) (r : List Word)
theorem cfbK4_fail (h : eq = 0 ∧ ct = 0) : cfbK4 eq m (some ct) = none := by simp [cfbK4, h]
theorem cfbK4_ok (h : ¬ (eq = 0 ∧ ct = 0)) : cfbK4 eq m (some ct) = some ([0], m) := by
  simp only [cfbK4, ite_eq_right h]
theorem cfbK3_some : cfbK3 n io il fv (some (eq, m)) = cfbK4 eq m (containsW n m io il fv) := rfl
theorem cfbK2_some : cfbK2 cR n io il fv u m (some z) = cfbK3 n io il fv (eqTrueC cR n m u z) := rfl
theorem cfbK1_ok (h : r.headD 0 = 2) : cfbK1 (some (r, m)) = some ([0], m) := by
  simp only [cfbK1]; rw [ite_eq_left h]
theorem cfbK1_fail (h : r.headD 0 ≠ 2) : cfbK1 (some (r, m)) = none := by
  simp only [cfbK1]; rw [ite_eq_right h]
theorem cfbW_leq (h : isProp = 0) :
    cfbW cR (n + 1) m isProp large s io il fv u = cfbK1 (cR n "lv_leq_top" [u, s] m) := by
  simp [cfbW, h]
theorem cfbW_large (h : isProp ≠ 0) (hl : large ≠ 0) :
    cfbW cR (n + 1) m isProp large s io il fv u = cfbK2 cR n io il fv u m (pinWordV m 53) := by
  simp [cfbW, h, hl]
theorem cfbW_none (h : isProp ≠ 0) (hl : large = 0) :
    cfbW cR (n + 1) m isProp large s io il fv u = some ([0], m) := by simp [cfbW, h, hl]
end arms
attribute [ind_grind] cfbK4_fail cfbK4_ok cfbK3_some cfbK2_some cfbK1_ok cfbK1_fail cfbW_leq
  cfbW_large cfbW_none

section spec
variable (p : Prog) (hpw : p.lookup "pin_word" = some pinWordL)
  (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
  (hp : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
include hpw het hc hp

theorem cfbW_spec (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (isProp large s io il fv u : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_field_sort_bound" [isProp, large, s, io, il, fv, u]
    ⦃fun r s' => LocEq s' s₀ ∧ cfbW cR n s₀.mem isProp large s io il fv u = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkFieldSortBoundL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        hcR n "lv_leq_top", pinWord_specV p hpw n, eqTrue_specC p het cR hcR n,
        slContains_spec p hc n] <;>
      finish (gen := 20)

end spec

/-! ## `check_struct_field_sorts_i_go`: the word model -/

section model
variable (rest : Mem → Option (List Word × Mem))

/-- After the fields below. -/
def csfK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([0], m)
/-- After the bound: write the sort, then the fields below. -/
def csfK4 (res j u : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => csfK5 (rest (m.set64 IW (res + (j - 1)) u))
/-- After `ensure_sort_core`: the bound. -/
def csfK3 (cR : CallM) (n : Nat) (isProp large s io il fv res j : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ru, m) => csfK4 rest res j (ru.headD 0) (cfbW cR n m isProp large s io il fv (ru.headD 0))
/-- After `infer_type_core`. -/
def csfK2 (cR : CallM) (n : Nat) (vis isProp large s nP io il fv res j : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ry, m) => csfK3 rest cR n isProp large s io il fv res j
      (cR n "ensure_sort_core" [vis, nP + (j - 1), ry.headD 0] m)
/-- After `fvar_type_d`. -/
def csfK1 (cR : CallM) (n : Nat) (vis isProp large s nP io il fv res j : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rt, m) => csfK2 rest cR n vis isProp large s nP io il fv res j
      (cR n "infer_type_core" [vis, nP + (j - 1), rt.headD 0] m)

end model

/-- **The model of `check_struct_field_sorts_i_go(vis, isProp, large, s, nP, fo, fl, io, il, res,
j)`** at exec fuel `n`. -/
def csfW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, isProp, large, s, nP, fo, fl, io, il, res, j =>
    if j = 0 then some ([0], m)
    else if fl ≤ j - 1 then none
    else csfK1 (fun m' => csfW cR n m' vis isProp large s nP fo fl io il res (j - 1)) cR n vis isProp large
      s nP io il (rdW (m.arr64 IW) (fo + (j - 1))) res j
      (ftdF m [rdW (m.arr64 IW) (fo + (j - 1))])

section arms
variable (rest : Mem → Option (List Word × Mem)) (cR : CallM) (n : Nat) (m : Mem)
  (vis isProp large s nP fo fl io il fv res j u : Word) (r : List Word)
theorem csfW_zero (h : j = 0) :
    csfW cR (n + 1) m vis isProp large s nP fo fl io il res j = some ([0], m) := by simp [csfW, h]
theorem csfW_oob (h : j ≠ 0) (hl : fl ≤ j - 1) :
    csfW cR (n + 1) m vis isProp large s nP fo fl io il res j = none := by simp [csfW, h, hl]
theorem csfW_step (h : j ≠ 0) (hl : ¬ fl ≤ j - 1) :
    csfW cR (n + 1) m vis isProp large s nP fo fl io il res j =
      csfK1 (fun m' => csfW cR n m' vis isProp large s nP fo fl io il res (j - 1)) cR n vis isProp large
        s nP io il (rdW (m.arr64 IW) (fo + (j - 1))) res j
        (ftdF m [rdW (m.arr64 IW) (fo + (j - 1))]) := by simp [csfW, h, hl]
theorem csfK5_some : csfK5 (some (r, m)) = some ([0], m) := rfl
theorem csfK4_some : csfK4 rest res j u (some (r, m)) = csfK5 (rest (m.set64 IW (res + (j - 1)) u)) :=
  rfl
theorem csfK3_some : csfK3 rest cR n isProp large s io il fv res j (some (r, m)) =
    csfK4 rest res j (r.headD 0) (cfbW cR n m isProp large s io il fv (r.headD 0)) := rfl
theorem csfK2_some : csfK2 rest cR n vis isProp large s nP io il fv res j (some (r, m)) =
    csfK3 rest cR n isProp large s io il fv res j
      (cR n "ensure_sort_core" [vis, nP + (j - 1), r.headD 0] m) := rfl
theorem csfK1_some : csfK1 rest cR n vis isProp large s nP io il fv res j (some (r, m)) =
    csfK2 rest cR n vis isProp large s nP io il fv res j
      (cR n "infer_type_core" [vis, nP + (j - 1), r.headD 0] m) := rfl
end arms
attribute [ind_grind] csfW_zero csfW_oob csfW_step csfK5_some csfK4_some csfK3_some csfK2_some
  csfK1_some

section spec
variable (p : Prog) (hg : p.lookup "sl_get" = some slGet) (hpw : p.lookup "pin_word" = some pinWordL)
  (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
  (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
  (hp : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL) (hftd : FtdF p)
include hg hpw het hc hb hp hftd

theorem csfW_spec (cR : CallM) (hcR : CallSpec p cR) (n : Nat) : ∀ (s₀ : St) (vis isProp large s nP fo fl io il res j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_struct_field_sorts_i_go"
      [vis, isProp, large, s, nP, fo, fl, io, il, res, j]
    ⦃fun r s' => LocEq s' s₀ ∧
      csfW cR n s₀.mem vis isProp large s nP fo fl io il res j = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis isProp large s nP fo fl io il res j
    rw [invoke_eq _ hp]; simp only [callFn, checkStructFieldSortsIGoL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis isProp large s nP fo fl io il res j
    rw [invoke_eq _ hp]
    simp only [callFn, checkStructFieldSortsIGoL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        slGet_specW p hg n, ftdF_spec0 p hftd n, hcR n "infer_type_core",
        hcR n "ensure_sort_core", cfbW_spec p hpw het hc hb cR hcR n, ih] <;>
      finish (gen := 30) (instances := 5000) [getW, rdW_eq]

end spec

/-! ## The relation to the twin -/

/-- The twin's universe bound for one field (`checkStructFieldSortsI`'s middle, verbatim). -/
def sfbT (isProp large : Bool) (s : LIdx) (idxArgs : List EIdx) (fv : EIdx) (u : LIdx) : AM Unit := do
  if !isProp then do
    let lu ← readLevelM u
    let ls ← readLevelM s
    unless ← liftFueled "level comparison" (ConLeche.Level.leq lu ls) do
      fail (.invalid "direct sum: field universe too large")
  else if large then do
    let z ← zeroLevel
    unless (← lvlEq? u z) == some true || idxArgs.contains fv do
      fail (.invalid "direct sum: large eliminator with a non-propositional \
        field outside the indices")

/-- **`checkStructFieldSortsI` at `j + 1`**, its steps named. -/
theorem checkStructFieldSortsI_succ (fe : IFEnv) (isProp large : Bool) (s : LIdx) (nP : Nat)
    (fvs idxArgs : List EIdx) (j : Nat) :
    checkStructFieldSortsI V fe isProp large s nP fvs idxArgs (j + 1) = (do
      let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
      let t ← fvarTypeD fv
      let ty ← inferTypeCore V fe checkFuel (nP + j) t
      let u ← ensureSortCore V fe checkFuel (nP + j) ty
      sfbT isProp large s idxArgs fv u
      let rest ← checkStructFieldSortsI V fe isProp large s nP fvs idxArgs j
      pure (rest ++ [u])) := by
  simp only [checkStructFieldSortsI, sfbT]
  congr; funext fv; congr; funext t; congr; funext ty; congr; funext u
  cases isProp <;> cases large <;>
    simp only [Bool.not_false, Bool.not_true, ite_true, ite_false, Bool.false_eq_true, bind_assoc,
      pure_bind]
  all_goals first
    | rfl
    | (congr; funext lu; congr; funext ls; congr; funext d; cases d <;> simp; done)
    | (congr; funext z; congr; funext d; by_cases hc : d = some true ∨ fv ∈ idxArgs <;> simp [hc]; done)

theorem sfb_leq_eq (u s : LIdx) (k : Bool → AM Unit) :
    (do let lu ← readLevelM u; let ls ← readLevelM s
        let b ← liftFueled "level comparison" (ConLeche.Level.leq lu ls); k b) =
      ((do let lu ← readLevelM u; let ls ← readLevelM s; pure (ConLeche.Level.leq lu ls)) >>=
        fun o => liftFueled "level comparison" o >>= k) := by
  simp only [bind_assoc, pure_bind]

theorem sumContains_decI {k : IdxKind} (x : Word) (hx : H x) : ∀ (ws : List Word),
    (∀ w ∈ ws, H w) → (ws.map (decI : Word → Idx k)).contains (decI x) = ws.contains x
  | [], _ => rfl
  | w :: ws, h => by
    simp only [List.map_cons, List.contains_cons]
    rw [decI_beq' x w hx (h w (by simp)), sumContains_decI x hx ws (fun v hv => h v (by simp [hv]))]
    by_cases e : w = x
    · subst e; simp
    · simp [Ne.symm e]

/-- **A handle written right before a decoded slice** extends it at the front. -/
theorem sumDecHL_write_front {k : IdxKind} (m : Mem) (o kk : Nat) (w v : Word) (acc : List (Idx k))
    (hw : w.toNat = o) (hsz : o < (m.arr64 IW).size) (hv : H v)
    (h : decHL m (o + 1) kk = some acc) :
    decHL (m.set64 IW w v) o (kk + 1) = some (decI v :: acc) := by
  simp only [decHL, hslice?_succ] at h ⊢
  have e1 : (hslice? (iwA (m.set64 IW w v)) (o + 1) kk : Option (List (Idx k))) =
      hslice? (iwA m) (o + 1) kk :=
    hslice?_congr _ _ _ _ _ fun i _ => by simp only [iwA, set64IW_get]; rw [ite_eq_right (by omega)]
  have e0 : (hd? (iwA (m.set64 IW w v)) o : Option (Idx k)) = some (decI v) := by
    simp [hd?, iwA, set64IW_get, hw, hsz, hv]
  rw [e1, e0, h]; rfl

theorem sum_toNat_add {a b : Word} (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

/-! ## `check_struct_field_sorts_i` -/

/-- After the fields. -/
def fsortsK2 (res nW : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => some ([res, nW], m2)
/-- After the allocation. -/
def fsortsK1 (cR : CallM) (n : Nat) (vis isProp large s nP fo fl io il nW : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (res, m1) => fsortsK2 res nW (csfW cR n m1 vis isProp large s nP fo fl io il res nW)

/-- **The model of `check_struct_field_sorts_i(vis, isProp, large, s, nP, fo, fl, io, il, n)`** at
callee fuel `n`. -/
def fsortsW (cR : CallM) (n : Nat) (m : Mem) (vis isProp large s nP fo fl io il nW : Word) : Option (List Word × Mem) :=
  fsortsK1 cR n vis isProp large s nP fo fl io il nW (allocW m nW)

theorem fsortsK1_some (cR : CallM) (n : Nat) (vis isProp large s nP fo fl io il nW res : Word) (m1 : Mem) :
    fsortsK1 cR n vis isProp large s nP fo fl io il nW (some (res, m1)) =
      fsortsK2 res nW (csfW cR n m1 vis isProp large s nP fo fl io il res nW) := rfl
theorem fsortsK2_some (res nW : Word) (r : List Word) (m2 : Mem) :
    fsortsK2 res nW (some (r, m2)) = some ([res, nW], m2) := rfl
attribute [ind_grind] fsortsK1_some fsortsK2_some

section spec2
variable (p : Prog) (hg : p.lookup "sl_get" = some slGet) (hpw : p.lookup "pin_word" = some pinWordL)
  (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
  (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
  (hgo : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL)
  (hia : p.lookup "iw_alloc" = some iwAlloc)
  (hp : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL) (hftd : FtdF p)
include hg hpw het hc hb hgo hia hp hftd

theorem fsortsW_spec (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (vis isProp large s nP fo fl io il nW : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_struct_field_sorts_i"
      [vis, isProp, large, s, nP, fo, fl, io, il, nW]
    ⦃fun r s' => LocEq s' s₀ ∧ fsortsW cR n s₀.mem vis isProp large s nP fo fl io il nW = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkStructFieldSortsIL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      iwAlloc_specW p hia n, csfW_spec p hg hpw het hc hb hgo hftd cR hcR n] <;>
    finish (gen := 30) (instances := 5000) [fsortsW]

end spec2

section census
variable (p : Prog) (hg : p.lookup "sl_get" = some slGet) (hpw : p.lookup "pin_word" = some pinWordL)
  (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
  (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
  (hgo : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL)
  (hia : p.lookup "iw_alloc" = some iwAlloc)
  (hp : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL) (hftd : FtdF p)
include hg hpw het hc hb hgo hia hp hftd

end census

end L.Ind
