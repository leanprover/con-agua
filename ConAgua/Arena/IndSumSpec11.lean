import ConAgua.Arena.IndSumSpec10

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

/-- The model of `lvl_eq_true(u, v)`. -/
def eqTrueW (m : Mem) (u v : Word) : Option (Word × Mem) := eqTrueK (stubM "lvl_eq_c" m [u, v])

theorem eqTrueK_some (r : List Word) (m : Mem) :
    eqTrueK (some (r, m)) = some (if r.headD 0 = 2 then 1 else 0, m) := rfl
attribute [ind_grind] eqTrueK_some

theorem eqTrue_specW (p : Prog) (hp : p.lookup "lvl_eq_true" = some lvlEqTrue) (n : Nat) (s₀ : St)
    (u v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lvl_eq_true" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ eqTrueW s₀.mem u v = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lvlEqTrue]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, stubM_spec p "lvl_eq_c" n] <;>
      finish (gen := 20) [eqTrueW]

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
def cfbK2 (n : Nat) (io il fv u : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some z => cfbK3 n io il fv (eqTrueW m u z)
/-- After `lv_leq_top`. -/
def cfbK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 2 then some ([0], m) else none

/-- **The model of `check_field_sort_bound(isProp, large, s, io, il, fv, u)`** at exec fuel `n`. -/
def cfbW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, isProp, large, s, io, il, fv, u =>
    if isProp = 0 then cfbK1 (stubM "lv_leq_top" m [u, s])
    else if large ≠ 0 then cfbK2 n io il fv u m (pinWordV m 53)
    else some ([0], m)

section arms
variable (n : Nat) (m : Mem) (isProp large s io il fv u eq ct z : Word) (r : List Word)
theorem cfbK4_fail (h : eq = 0 ∧ ct = 0) : cfbK4 eq m (some ct) = none := by simp [cfbK4, h]
theorem cfbK4_ok (h : ¬ (eq = 0 ∧ ct = 0)) : cfbK4 eq m (some ct) = some ([0], m) := by
  simp only [cfbK4, if_neg h]
theorem cfbK3_some : cfbK3 n io il fv (some (eq, m)) = cfbK4 eq m (containsW n m io il fv) := rfl
theorem cfbK2_some : cfbK2 n io il fv u m (some z) = cfbK3 n io il fv (eqTrueW m u z) := rfl
theorem cfbK1_ok (h : r.headD 0 = 2) : cfbK1 (some (r, m)) = some ([0], m) := by
  simp only [cfbK1]; rw [if_pos h]
theorem cfbK1_fail (h : r.headD 0 ≠ 2) : cfbK1 (some (r, m)) = none := by
  simp only [cfbK1]; rw [if_neg h]
theorem cfbW_leq (h : isProp = 0) :
    cfbW (n + 1) m isProp large s io il fv u = cfbK1 (stubM "lv_leq_top" m [u, s]) := by
  simp [cfbW, h]
theorem cfbW_large (h : isProp ≠ 0) (hl : large ≠ 0) :
    cfbW (n + 1) m isProp large s io il fv u = cfbK2 n io il fv u m (pinWordV m 53) := by
  simp [cfbW, h, hl]
theorem cfbW_none (h : isProp ≠ 0) (hl : large = 0) :
    cfbW (n + 1) m isProp large s io il fv u = some ([0], m) := by simp [cfbW, h, hl]
end arms
attribute [ind_grind] cfbK4_fail cfbK4_ok cfbK3_some cfbK2_some cfbK1_ok cfbK1_fail cfbW_leq
  cfbW_large cfbW_none

section spec
variable (p : Prog) (hpw : p.lookup "pin_word" = some pinWordL)
  (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
  (hp : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
include hpw het hc hp

theorem cfbW_spec (n : Nat) (s₀ : St) (isProp large s io il fv u : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_field_sort_bound" [isProp, large, s, io, il, fv, u]
    ⦃fun r s' => LocEq s' s₀ ∧ cfbW n s₀.mem isProp large s io il fv u = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkFieldSortBoundL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        stubM_spec p "lv_leq_top" n, pinWord_specV p hpw n, eqTrue_specW p het n,
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
def csfK3 (n : Nat) (isProp large s io il fv res j : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ru, m) => csfK4 rest res j (ru.headD 0) (cfbW n m isProp large s io il fv (ru.headD 0))
/-- After `infer_type_core`. -/
def csfK2 (n : Nat) (vis isProp large s nP io il fv res j : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ry, m) => csfK3 rest n isProp large s io il fv res j
      (stubM "ensure_sort_core" m [vis, nP + (j - 1), ry.headD 0])
/-- After `fvar_type_d`. -/
def csfK1 (n : Nat) (vis isProp large s nP io il fv res j : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rt, m) => csfK2 rest n vis isProp large s nP io il fv res j
      (stubM "infer_type_core" m [vis, nP + (j - 1), rt.headD 0])

end model

/-- **The model of `check_struct_field_sorts_i_go(vis, isProp, large, s, nP, fo, fl, io, il, res,
j)`** at exec fuel `n`. -/
def csfW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, isProp, large, s, nP, fo, fl, io, il, res, j =>
    if j = 0 then some ([0], m)
    else if fl ≤ j - 1 then none
    else csfK1 (fun m' => csfW n m' vis isProp large s nP fo fl io il res (j - 1)) n vis isProp large
      s nP io il (rdW (m.arr64 IW) (fo + (j - 1))) res j
      (stubM "fvar_type_d" m [rdW (m.arr64 IW) (fo + (j - 1))])

section arms
variable (rest : Mem → Option (List Word × Mem)) (n : Nat) (m : Mem)
  (vis isProp large s nP fo fl io il fv res j u : Word) (r : List Word)
theorem csfW_zero (h : j = 0) :
    csfW (n + 1) m vis isProp large s nP fo fl io il res j = some ([0], m) := by simp [csfW, h]
theorem csfW_oob (h : j ≠ 0) (hl : fl ≤ j - 1) :
    csfW (n + 1) m vis isProp large s nP fo fl io il res j = none := by simp [csfW, h, hl]
theorem csfW_step (h : j ≠ 0) (hl : ¬ fl ≤ j - 1) :
    csfW (n + 1) m vis isProp large s nP fo fl io il res j =
      csfK1 (fun m' => csfW n m' vis isProp large s nP fo fl io il res (j - 1)) n vis isProp large
        s nP io il (rdW (m.arr64 IW) (fo + (j - 1))) res j
        (stubM "fvar_type_d" m [rdW (m.arr64 IW) (fo + (j - 1))]) := by simp [csfW, h, hl]
theorem csfK5_some : csfK5 (some (r, m)) = some ([0], m) := rfl
theorem csfK4_some : csfK4 rest res j u (some (r, m)) = csfK5 (rest (m.set64 IW (res + (j - 1)) u)) :=
  rfl
theorem csfK3_some : csfK3 rest n isProp large s io il fv res j (some (r, m)) =
    csfK4 rest res j (r.headD 0) (cfbW n m isProp large s io il fv (r.headD 0)) := rfl
theorem csfK2_some : csfK2 rest n vis isProp large s nP io il fv res j (some (r, m)) =
    csfK3 rest n isProp large s io il fv res j
      (stubM "ensure_sort_core" m [vis, nP + (j - 1), r.headD 0]) := rfl
theorem csfK1_some : csfK1 rest n vis isProp large s nP io il fv res j (some (r, m)) =
    csfK2 rest n vis isProp large s nP io il fv res j
      (stubM "infer_type_core" m [vis, nP + (j - 1), r.headD 0]) := rfl
end arms
attribute [ind_grind] csfW_zero csfW_oob csfW_step csfK5_some csfK4_some csfK3_some csfK2_some
  csfK1_some

section spec
variable (p : Prog) (hg : p.lookup "sl_get" = some slGet) (hpw : p.lookup "pin_word" = some pinWordL)
  (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
  (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
  (hp : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL)
include hg hpw het hc hb hp

theorem csfW_spec (n : Nat) : ∀ (s₀ : St) (vis isProp large s nP fo fl io il res j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_struct_field_sorts_i_go"
      [vis, isProp, large, s, nP, fo, fl, io, il, res, j]
    ⦃fun r s' => LocEq s' s₀ ∧
      csfW n s₀.mem vis isProp large s nP fo fl io il res j = some (r, s'.mem); ⊤⦄ := by
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
        slGet_specW p hg n, stubM_spec p "fvar_type_d" n, stubM_spec p "infer_type_core" n,
        stubM_spec p "ensure_sort_core" n, cfbW_spec p hpw het hc hb n, ih] <;>
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
    · simp [e, Ne.symm e]

/-- **`check_field_sort_bound`'s model refines the twin's bound.** -/
theorem cfbW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) (m : Mem)
    (a : AState) (isProp large s io il fv u : Word) (idxArgs : List EIdx) (hS : StageR dn vis fe m a)
    (hu : H u) (hs : H s) (hfv : H fv) (hidx : decHL m io.toNat il.toNat = some idxArgs)
    (hib : io.toNat + il.toNat ≤ iwTop m) :
    Sim (cfbW n m isProp large s io il fv u)
      (sfbT (isProp != 0) (large != 0) (decI s) idxArgs (decI fv) (decI u)) a
      (fun _ _ m' a' => StageR dn vis fe m' a' ∧ IWGrow m m') := by
  cases n with
  | zero => exact Sim.of_none
  | succ n =>
  by_cases hp : isProp = 0
  · rw [cfbW_leq n m isProp large s io il fv u hp]
    simp only [sfbT, hp, bne_self_eq_false, Bool.not_false, ite_true]
    rw [sfb_leq_eq]
    refine Sim.bindK (K := cfbK1) rfl (fun _ _ => rfl)
      (sumSim_of_relAM (lvLeqTopStub_spec dn vis fe u s hu hs) hS) fun r x m1 a1 hQ => ?_
    obtain ⟨hS1, hg1, hx⟩ := hQ
    by_cases h2 : r.headD 0 = 2
    · rw [cfbK1_ok m1 r h2]
      have : x = some true := by
        simp only [decLvlEq] at hx; rw [h2] at hx
        rcases x with _ | _ | _
        · exact absurd hx (by decide)
        · exact absurd hx (by decide)
        · rfl
      subst this
      exact Sim.congr (Sim.ret (x := ()) ⟨hS1, hg1⟩) rfl
    · rw [cfbK1_fail m1 r h2]; exact Sim.of_none
  have hp' : (isProp != 0) = true := by simpa using hp
  by_cases hl : large = 0
  · rw [cfbW_none n m isProp large s io il fv u hp hl]
    simp only [sfbT, hp', hl, bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ite_false]
    exact Sim.congr (Sim.ret (x := ()) ⟨hS, IWGrow.refl _⟩) rfl
  have hl' : (large != 0) = true := by simpa using hl
  rw [cfbW_large n m isProp large s io il fv u hp hl]
  simp only [sfbT, hp', hl', Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  cases hz' : pinWordV m 53 with
  | none => exact Sim.of_none
  | some z =>
  obtain ⟨hrun0, hz⟩ := pinZero_stage hS hz'
  refine Sim.bind_twin hrun0 ?_
  rw [cfbK2_some, eqTrueW]
  cases he : stubM "lvl_eq_c" m [u, z] with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨r1, m1⟩ := y
  obtain ⟨x, a1, hrun1, hS1, hg1, hx⟩ := lvlEqStub_spec dn vis fe u z hu hz m m1 a r1 he hS
  refine Sim.bind_twin hrun1 ?_
  rw [eqTrueK_some, cfbK3_some]
  have hidx1 : decHL m1 io.toNat il.toNat = some idxArgs := by
    rw [decHL_grow hg1 hib]; exact hidx
  cases hc : containsW n m1 io il fv with
  | none => exact Sim.of_none
  | some ct =>
  obtain ⟨ws, hws, hwsd, hwlt⟩ := slR_of_decHL m1 _ _ idxArgs hidx1 (hS1.lt64 (by have := hg1.1; omega))
  simp only [UInt64.ofNat_toNat] at hws
  have hct := containsW_ok n _ _ _ _ _ _ hws hc
  by_cases hf : (if r1.headD 0 = 2 then (1 : Word) else 0) = 0 ∧ ct = 0
  · rw [cfbK4_fail _ _ _ hf]; exact Sim.of_none
  rw [cfbK4_ok _ _ _ hf]
  have hcond : (x == some true || idxArgs.contains (decI fv)) = true := by
    by_cases h2 : r1.headD 0 = 2
    · have : x = some true := by
        simp only [decLvlEq] at hx; rw [h2] at hx
        rcases x with _ | _ | _
        · exact absurd hx (by decide)
        · exact absurd hx (by decide)
        · rfl
      rw [this]; rfl
    · have hct1 : ct ≠ 0 := fun e => hf ⟨by rw [if_neg h2], e⟩
      have hin : ws.contains fv = true := by
        rw [hct] at hct1
        cases hcw : ws.contains fv
        · rw [hcw] at hct1; exact absurd rfl hct1
        · rfl
      rw [hwsd, sumContains_decI fv hfv ws hwlt, hin, Bool.or_true]
  exact Sim.congr (Sim.ret (x := ()) ⟨hS1, hg1⟩) (by simp only [hcond]; rfl)

/-- **A handle written right before a decoded slice** extends it at the front. -/
theorem sumDecHL_write_front {k : IdxKind} (m : Mem) (o kk : Nat) (w v : Word) (acc : List (Idx k))
    (hw : w.toNat = o) (hsz : o < (m.arr64 IW).size) (hv : H v)
    (h : decHL m (o + 1) kk = some acc) :
    decHL (m.set64 IW w v) o (kk + 1) = some (decI v :: acc) := by
  simp only [decHL, hslice?_succ] at h ⊢
  have e1 : (hslice? (iwA (m.set64 IW w v)) (o + 1) kk : Option (List (Idx k))) =
      hslice? (iwA m) (o + 1) kk :=
    hslice?_congr _ _ _ _ _ fun i _ => by simp only [iwA, set64IW_get]; rw [if_neg (by omega)]
  have e0 : (hd? (iwA (m.set64 IW w v)) o : Option (Idx k)) = some (decI v) := by
    simp [hd?, iwA, set64IW_get, hw, hsz, hv]
  rw [e1, e0, h]; rfl

theorem sum_toNat_add {a b : Word} (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

/-- **`check_struct_field_sorts_i_go`'s model refines `checkStructFieldSortsI`** at `j`: the sorts of
fields `0 ‥ j - 1` written in front of the already-written suffix `acc` at `res + j`, the slots
allocated above `m0`'s top. -/
theorem csfW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m : Mem) (a : AState) (isProp large s nP fo fl io il res j : Word) (m0 : Mem) (k : Nat)
      (acc : List LIdx) (fvs idxArgs : List EIdx),
    StageR dn vis fe m a → IWGrow m0 m → iwTop m0 ≤ res.toNat → res.toNat + j.toNat + k ≤ iwTop m →
    decHL m (res.toNat + j.toNat) k = some acc →
    decHL m0 fo.toNat fl.toNat = some fvs → fo.toNat + fl.toNat ≤ iwTop m0 →
    decHL m0 io.toNat il.toNat = some idxArgs → io.toNat + il.toNat ≤ iwTop m0 →
    H s → nP.toNat + j.toNat < 2 ^ 64 →
    Sim (csfW n m vis isProp large s nP fo fl io il res j)
      (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs j.toNat) a
      (fun _ xs m' a' => StageR dn vis fe m' a' ∧ IWGrow m0 m' ∧
        decHL m' res.toNat (j.toNat + k) = some (xs ++ acc) ∧ res.toNat + j.toNat + k ≤ iwTop m') := by
  induction n with
  | zero => intro m a isProp large s nP fo fl io il res j m0 k acc fvs idxArgs _ _ _ _ _ _ _ _ _ _ _
            exact Sim.of_none
  | succ n ih =>
  intro m a isProp large s nP fo fl io il res j m0 k acc fvs idxArgs hS hg0 hr0 hroom hacc hfvs hfb
    hidx hib hs hnj
  by_cases hj : j = 0
  · subst hj
    rw [csfW_zero n m vis isProp large s nP fo fl io il res 0 rfl]
    simp only [UInt64.toNat_zero, Nat.add_zero, Nat.zero_add] at hacc hroom ⊢
    simp only [checkStructFieldSortsI]
    exact Sim.ret ⟨hS, hg0, by simpa using hacc, hroom⟩
  obtain ⟨J, hjJ⟩ : ∃ J, j.toNat = J + 1 :=
    ⟨j.toNat - 1, by have : j.toNat ≠ 0 := fun e => hj (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hJ : (j - 1).toNat = J := by rw [toNat_pred_of_ne hj]; omega
  by_cases hl : fl ≤ j - 1
  · rw [csfW_oob n m vis isProp large s nP fo fl io il res j hj hl]; exact Sim.of_none
  rw [csfW_step n m vis isProp large s nP fo fl io il res j hj hl]
  have hJl : J < fl.toNat := by
    have : ¬ fl.toNat ≤ (j - 1).toNat := fun e => hl (UInt64.le_iff_toNat_le.mpr e)
    omega
  have hT := hS.lt64 (x := iwTop m) (Nat.le_refl _)
  have hgT := hg0.1
  -- the field
  have hfvs' : decHL m fo.toNat fl.toNat = some fvs := by rw [decHL_grow hg0 hfb]; exact hfvs
  obtain ⟨w, hw, hwl, hwd⟩ := decHL_get' hfvs' J hJl (by omega)
  have efo : fo + (j - 1) = UInt64.ofNat (fo.toNat + J) := by
    apply UInt64.toNat_inj.mp; rw [sum_toNat_add (by omega), hJ]; simp; omega
  rw [efo, hw]
  rw [hjJ, checkStructFieldSortsI_succ]
  have hget : fvs[J]? = some (decI w) := by
    rw [List.getElem?_eq_getElem (by rw [decHL_length m hfvs']; exact hJl), hwd]
  refine Sim.bind_twin (x := decI w) (a₁ := a) (by rw [hget]; rfl) ?_
  have hdep : (nP + (j - 1)).toNat = nP.toNat + J := by rw [sum_toNat_add (by omega), hJ]
  refine Sim.bindK (K := csfK1 _ n vis isProp large s nP io il w res j) rfl (fun _ _ => rfl)
    (sumSim_of_relAM (fvarTypeD_spec dn vis fe w hwl) hS) fun rt t m1 a1 hQ => ?_
  obtain ⟨hS1, hg1, ht1, ht⟩ := hQ
  rw [csfK1_some]
  have h2 := inferTypeCore_spec dn vis fe (nP + (j - 1)) (rt.headD 0) ht1
  rw [hdep, ht] at h2
  refine Sim.bindK (K := csfK2 _ n vis isProp large s nP io il w res j) rfl (fun _ _ => rfl)
    (sumSim_of_relAM h2 hS1) fun ry ty m2 a2 hQ => ?_
  obtain ⟨hS2, hg2, hy1, hy⟩ := hQ
  rw [csfK2_some]
  have h3 := ensureSortCore_spec dn vis fe (nP + (j - 1)) (ry.headD 0) hy1
  rw [hdep, hy] at h3
  refine Sim.bindK (K := csfK3 _ n isProp large s io il w res j) rfl (fun _ _ => rfl)
    (sumSim_of_relAM h3 hS2) fun ru u m3 a3 hQ => ?_
  obtain ⟨hS3, hg3, hu1, hu⟩ := hQ
  rw [csfK3_some]
  have hg03 := ((hg0.trans hg1).trans hg2).trans hg3
  have hidx3 : decHL m3 io.toNat il.toNat = some idxArgs := by rw [decHL_grow hg03 hib]; exact hidx
  have h4 := cfbW_ok n m3 a3 isProp large s io il w (ru.headD 0) idxArgs hS3 hu1 hs hwl hidx3
    (by have := hg03.1; omega)
  rw [hu] at h4
  refine Sim.bindK (K := csfK4 _ res j (ru.headD 0)) rfl (fun _ _ => rfl) h4 fun _ _ m4 a4 hQ => ?_
  obtain ⟨hS4, hg4⟩ := hQ
  rw [csfK4_some]
  -- the write
  have hg14 := ((hg1.trans hg2).trans hg3).trans hg4
  have hres1 : (res + (j - 1)).toNat = res.toNat + J := by rw [sum_toNat_add (by omega), hJ]
  have hsz4 : res.toNat + J < (m4.arr64 IW).size := by
    obtain ⟨h1, -, -, -, -⟩ := hS4.2; have := hg14.1; omega
  have hacc4 : decHL m4 (res.toNat + J + 1) k = some acc := by
    rw [decHL_grow hg14 (by omega)]; rw [show res.toNat + J + 1 = res.toNat + j.toNat by omega]; exact hacc
  have hacc' := sumDecHL_write_front m4 _ k _ (ru.headD 0) acc hres1 hsz4 hu1 hacc4
  rw [hu] at hacc'
  have htop' : iwTop (m4.set64 IW (res + (j - 1)) (ru.headD 0)) = iwTop m4 := by
    simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have h5 := ih (m4.set64 IW (res + (j - 1)) (ru.headD 0)) a4 isProp large s nP fo fl io il res (j - 1)
    m0 (k + 1) (u :: acc) fvs idxArgs (hS4.set_iw _ _)
    ((hg03.trans hg4).set_iw _ _ (by omega)) hr0 (by rw [htop', hJ]; have := hg14.1; omega)
    (by rw [hJ]; exact hacc') hfvs hfb hidx hib hs (by omega)
  rw [hJ] at h5
  refine Sim.bindK (K := csfK5) rfl (fun _ _ => rfl) h5 fun _ xs m5 a5 hQ => ?_
  obtain ⟨hS5, hg5, hd5, ht5⟩ := hQ
  refine Sim.ret ⟨hS5, hg5, ?_, by omega⟩
  rw [show J + 1 + k = J + (k + 1) by omega, hd5]; simp

/-! ## `check_struct_field_sorts_i` -/

/-- After the fields. -/
def cfK2 (res nW : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => some ([res, nW], m2)
/-- After the allocation. -/
def cfK1 (n : Nat) (vis isProp large s nP fo fl io il nW : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (res, m1) => cfK2 res nW (csfW n m1 vis isProp large s nP fo fl io il res nW)

/-- **The model of `check_struct_field_sorts_i(vis, isProp, large, s, nP, fo, fl, io, il, n)`** at
callee fuel `n`. -/
def cfW (n : Nat) (m : Mem) (vis isProp large s nP fo fl io il nW : Word) : Option (List Word × Mem) :=
  cfK1 n vis isProp large s nP fo fl io il nW (allocW m nW)

theorem cfK1_some (n : Nat) (vis isProp large s nP fo fl io il nW res : Word) (m1 : Mem) :
    cfK1 n vis isProp large s nP fo fl io il nW (some (res, m1)) =
      cfK2 res nW (csfW n m1 vis isProp large s nP fo fl io il res nW) := rfl
theorem cfK2_some (res nW : Word) (r : List Word) (m2 : Mem) :
    cfK2 res nW (some (r, m2)) = some ([res, nW], m2) := rfl
attribute [ind_grind] cfK1_some cfK2_some

section spec2
variable (p : Prog) (hg : p.lookup "sl_get" = some slGet) (hpw : p.lookup "pin_word" = some pinWordL)
  (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
  (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
  (hgo : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL)
  (hia : p.lookup "iw_alloc" = some iwAlloc)
  (hp : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL)
include hg hpw het hc hb hgo hia hp

theorem cfW_spec (n : Nat) (s₀ : St) (vis isProp large s nP fo fl io il nW : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_struct_field_sorts_i"
      [vis, isProp, large, s, nP, fo, fl, io, il, nW]
    ⦃fun r s' => LocEq s' s₀ ∧ cfW n s₀.mem vis isProp large s nP fo fl io il nW = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkStructFieldSortsIL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      iwAlloc_specW p hia n, csfW_spec p hg hpw het hc hb hgo n] <;>
    finish (gen := 30) (instances := 5000) [cfW]

end spec2

/-- **`check_struct_field_sorts_i`'s model refines `checkStructFieldSortsI`**: the sorts in a fresh
`IW` slice. -/
theorem cfW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) (m : Mem)
    (a : AState) (isProp large s nP fo fl io il nW : Word) (fvs idxArgs : List EIdx)
    (hS : StageR dn vis fe m a) (hfvs : decHL m fo.toNat fl.toNat = some fvs)
    (hfb : fo.toNat + fl.toNat ≤ iwTop m) (hidx : decHL m io.toNat il.toNat = some idxArgs)
    (hib : io.toNat + il.toNat ≤ iwTop m) (hs : H s) (hnj : nP.toNat + nW.toNat < 2 ^ 64) :
    Sim (cfW n m vis isProp large s nP fo fl io il nW)
      (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs nW.toNat) a
      (fun r xs m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m') := by
  unfold cfW
  cases hal : allocW m nW with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨res, m1⟩ := y
  rw [cfK1_some]
  obtain ⟨hS1, hg1, hrt, ht1⟩ := allocW_stage hal hS
  refine sumSim_map (K := cfK2 res nW) rfl (fun _ _ => rfl)
    (csfW_ok n m1 a isProp large s nP fo fl io il res nW m 0 [] fvs idxArgs hS1 hg1 (by omega)
      (by omega) (by simp [decHL, hslice?]) hfvs hfb hidx hib hs hnj) fun _ xs m' a' hQ => ?_
  obtain ⟨hS', hg', hd', ht'⟩ := hQ
  exact ⟨hS', hg', by simpa using hd', by simpa using ht'⟩

section census
variable (p : Prog) (hg : p.lookup "sl_get" = some slGet) (hpw : p.lookup "pin_word" = some pinWordL)
  (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
  (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
  (hgo : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL)
  (hia : p.lookup "iw_alloc" = some iwAlloc)
  (hp : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL)
include hg hpw het hc hb hgo hia hp

/-- **`check_struct_field_sorts_i` refines `checkStructFieldSortsI .verified`** (through the stubs
`fvar_type_d`, `infer_type_core`, `ensure_sort_core`, `lv_leq_top`, `lvl_eq_c`): from the stage
relation, the field variables and the index arguments decoded below the pool's top, the sorts in a
fresh `IW` slice. -/
@[refines ConRon.Arena.checkStructFieldSortsI]
theorem checkStructFieldSortsI_refines (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis isProp large s nP fo fl io il nW : Word)
    (fvs idxArgs : List EIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hfvs : decHL s₀.mem fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem)
    (hidx : decHL s₀.mem io.toNat il.toNat = some idxArgs) (hib : io.toNat + il.toNat ≤ iwTop s₀.mem)
    (hs : H s) (hnj : nP.toNat + nW.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_struct_field_sorts_i"
      [vis, isProp, large, s, nP, fo, fl, io, il, nW]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs
        nW.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s)
        nP.toNat fvs idxArgs nW.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs
          idxArgs nW.toNat) a₀); ⊤⦄ := by
  refine triple_post (cfW_spec p hg hpw het hc hb hgo hia hp n s₀ vis isProp large s nP fo fl io il nW) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hok, hS', hg', hd, -⟩ :=
    (cfW_ok n _ a₀ isProp large s nP fo fl io il nW fvs idxArgs hS hfvs hfb hidx hib hs hnj).run hm
  exact ⟨hl, hok, hS', hg', hd⟩

end census

end L.Ind
