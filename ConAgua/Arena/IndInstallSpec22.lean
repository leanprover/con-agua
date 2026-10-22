import ConAgua.Arena.IndInstallSpec21

/-!
# Refinements of `IndInstall`, part 22 (lane `indproofs2`, helper `install`): `checkBlockCtors`,
the word models

Per member: `check_sum_ctors` (the lead's `IndSum`, not proved yet: a pending contract below), the
two results wrapped (`rec2`), recursion as the twin's with both pointers consed (D18).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Pending callee contract (`sorry` until the owner's refinement lands) -/

/-- `check_sum_ctors(vis0, vis, T, lps.off, lps.len, nP, nIdx, resSort, isProp, large, cvTa,
ctors.off, ctors.len)` (lane `indproofs2`'s `IndSum`, pending), at one environment (`vis0 = vis`,
as `check_block_pass` calls it): the constructors checked; the stored constructors and their
fields' sorts, two slices of pointers decoded below the tops. -/
theorem checkSumCtors_pending (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (T lo ll nP nIdx rs isP lg cvTa co cl : Word) (hT : H T) (hrs : H rs) (lps : List NIdx)
    (cvv : IConstantVal) (cs : List (IConstantVal × Nat)) :
    RelAM "check_sum_ctors" [vis, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvTa, co, cl]
      (fun m a => StageR dn vis fe m a ∧ decHL m lo.toNat ll.toNat = some lps ∧
        lo.toNat + ll.toNat ≤ iwTop m ∧ DecB (fun m => decCVp m cvTa.toNat) m cvv ∧
        DecB (fun m => decPL m (decCN m) co.toNat cl.toNat) m cs ∧ (cl = 0 ∨ co.toNat + cl.toNat ≤ iwTop m))
      (checkSumCtors V fe fe (decI T) lps nP.toNat nIdx.toNat (decI rs) (isP != 0) (lg != 0) cvv cs)
      (fun m m' a' r x => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        PSlR decCN x.1 (r.headD 0) (r.tail.headD 0) m' ∧
        PSlR decIS x.2 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) m') := sorry

/-! ## `check_block_ctors_one` -/

def icboK3 (r2 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r2.headD 0, r.headD 0], m)
def icboK2 (p : Prog) (n : Nat) (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icboK3 r (callW p n "rec2" [r1.tail.tail.headD 0, r1.tail.tail.tail.headD 0] m)
def icboK1 (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icboK2 p n r (callW p n "rec2" [r.headD 0, r.tail.headD 0] m)

/-- **The model of `check_block_ctors_one(vis0, vis, p, lps.off, lps.len, ms, cvTa)`** (body fuel
`n`). -/
def icboW (p : Prog) (n : Nat) (m : Mem) (vis0 vis pp lo ll ms cv : Word) : Option (List Word × Mem) :=
  icboK1 p n (callW p n "check_sum_ctors" [vis0, vis, rdW (m.arr64 EREC) (rdW (m.arr64 IW) ms), lo, ll,
    rdW (m.arr64 IW) (pp + 4), rdW (m.arr64 IW) (ms + 1), rdW (m.arr64 IW) (pp + 6),
    rdW (m.arr64 IW) (pp + 8), rdW (m.arr64 IW) (pp + 7), cv, rdW (m.arr64 IW) (ms + 2),
    rdW (m.arr64 IW) (ms + 3)] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (r r1 r2 : List Word)
theorem icboK3_some : icboK3 r2 (some (r, m)) = some ([r2.headD 0, r.headD 0], m) := rfl
theorem icboK2_some : icboK2 p n r1 (some (r, m)) =
    icboK3 r (callW p n "rec2" [r1.tail.tail.headD 0, r1.tail.tail.tail.headD 0] m) := rfl
theorem icboK1_some : icboK1 p n (some (r, m)) = icboK2 p n r (callW p n "rec2" [r.headD 0, r.tail.headD 0] m) := rfl
end arms
attribute [ind_grind] icboK3_some icboK2_some icboK1_some

set_option maxHeartbeats 1600000 in
theorem icbo_spec (p : Prog) (hp : p.lookup "check_block_ctors_one" = some checkBlockCtorsOne) (n : Nat)
    (s₀ : St) (vis0 vis pp lo ll ms cv : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_ctors_one" [vis0, vis, pp, lo, ll, ms, cv]
    ⦃fun r s' => LocEq s' s₀ ∧ icboW p n s₀.mem vis0 vis pp lo ll ms cv = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockCtorsOne]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "check_sum_ctors", callW_spec p n "rec2"] <;>
    finish (gen := 40) (instances := 20000) [icboW, rdW_eq]

/-! ## `check_block_ctors_go` -/

def icbgK4 (r3 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r3.headD 0, r3.tail.headD 0, r.headD 0, r.tail.headD 0], m)
def icbgK3 (p : Prog) (n : Nat) (r1 r2 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbgK4 r (callW p n "sl_cons" [r1.tail.headD 0, r2.tail.tail.headD 0,
      r2.tail.tail.tail.headD 0] m)
def icbgK2 (p : Prog) (n : Nat) (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbgK3 p n r1 r (callW p n "sl_cons" [r1.headD 0, r.headD 0, r.tail.headD 0] m)

mutual
/-- **The model of `check_block_ctors_go`** at exec fuel `n`. -/
def icbgW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis0, vis, pp, lo, ll, mo, ml, co, cl =>
    if ml = 0 then some ([0, 0, 0, 0], m) else if cl = 0 then some ([0, 0, 0, 0], m)
    else icbgK1 p n vis0 vis pp lo ll mo ml co cl (callW p n "check_block_ctors_one"
      [vis0, vis, pp, lo, ll, rdW (m.arr64 IW) mo, rdW (m.arr64 IW) co] m)
def icbgK1 (p : Prog) (n : Nat) (vis0 vis pp lo ll mo ml co cl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbgK2 p n r (icbgW p n m vis0 vis pp lo ll (mo + 1) (ml - 1) (co + 1) (cl - 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis0 vis pp lo ll mo ml co cl : Word) (r r1 r2 r3 : List Word)
theorem icbgW_zero : icbgW p 0 m vis0 vis pp lo ll mo ml co cl = none := by simp [icbgW]
theorem icbgW_nil1 (h : ml = 0) : icbgW p (n + 1) m vis0 vis pp lo ll mo ml co cl = some ([0, 0, 0, 0], m) := by
  simp [icbgW, h]
theorem icbgW_nil2 (h1 : ml ≠ 0) (h : cl = 0) :
    icbgW p (n + 1) m vis0 vis pp lo ll mo ml co cl = some ([0, 0, 0, 0], m) := by simp [icbgW, h1, h]
theorem icbgW_cons (h1 : ml ≠ 0) (h2 : cl ≠ 0) : icbgW p (n + 1) m vis0 vis pp lo ll mo ml co cl =
    icbgK1 p n vis0 vis pp lo ll mo ml co cl (callW p n "check_block_ctors_one"
      [vis0, vis, pp, lo, ll, rdW (m.arr64 IW) mo, rdW (m.arr64 IW) co] m) := by simp [icbgW, h1, h2]
theorem icbgK1_some : icbgK1 p n vis0 vis pp lo ll mo ml co cl (some (r, m)) =
    icbgK2 p n r (icbgW p n m vis0 vis pp lo ll (mo + 1) (ml - 1) (co + 1) (cl - 1)) := by simp [icbgK1]
theorem icbgK2_some : icbgK2 p n r1 (some (r, m)) =
    icbgK3 p n r1 r (callW p n "sl_cons" [r1.headD 0, r.headD 0, r.tail.headD 0] m) := rfl
theorem icbgK3_some : icbgK3 p n r1 r2 (some (r, m)) = icbgK4 r (callW p n "sl_cons"
    [r1.tail.headD 0, r2.tail.tail.headD 0, r2.tail.tail.tail.headD 0] m) := rfl
theorem icbgK4_some : icbgK4 r3 (some (r, m)) =
    some ([r3.headD 0, r3.tail.headD 0, r.headD 0, r.tail.headD 0], m) := rfl
end arms
attribute [ind_grind] icbgW_nil1 icbgW_nil2 icbgW_cons icbgK1_some icbgK2_some icbgK3_some icbgK4_some

set_option maxHeartbeats 1600000 in
theorem icbg_spec (p : Prog) (hp : p.lookup "check_block_ctors_go" = some checkBlockCtorsGo) (n : Nat) :
    ∀ (s₀ : St) (vis0 vis pp lo ll mo ml co cl : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_ctors_go" [vis0, vis, pp, lo, ll, mo, ml, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ icbgW p n s₀.mem vis0 vis pp lo ll mo ml co cl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis0 vis pp lo ll mo ml co cl; rw [invoke_eq _ hp]; simp only [callFn, checkBlockCtorsGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis0 vis pp lo ll mo ml co cl
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockCtorsGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "check_block_ctors_one", callW_spec p n "sl_cons", ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

/-! ## `check_block_ctors` -/

def ictK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], m)
def ictK1 (p : Prog) (n : Nat) (vis0 vis pp mo ml co cl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => ictK2 (callW p n "check_block_ctors_go" [vis0, vis, pp, r.headD 0, r.tail.headD 0,
      mo, ml, co, cl] m)

/-- **The model of `check_block_ctors`** (body fuel `n`). -/
def ictW (p : Prog) (n : Nat) (m : Mem) (vis0 vis pp mo ml co cl : Word) : Option (List Word × Mem) :=
  ictK1 p n vis0 vis pp mo ml co cl (callW p n "block_shape_lps" [pp] m)

theorem ictK1_some (p : Prog) (n : Nat) (vis0 vis pp mo ml co cl : Word) (r : List Word) (m : Mem) :
    ictK1 p n vis0 vis pp mo ml co cl (some (r, m)) = ictK2 (callW p n "check_block_ctors_go"
      [vis0, vis, pp, r.headD 0, r.tail.headD 0, mo, ml, co, cl] m) := rfl
theorem ictK2_some (r : List Word) (m : Mem) : ictK2 (some (r, m)) =
    some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], m) := rfl
attribute [ind_grind] ictK1_some ictK2_some

theorem ict_spec (p : Prog) (hp : p.lookup "check_block_ctors" = some checkBlockCtors) (n : Nat) (s₀ : St)
    (vis0 vis pp mo ml co cl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_ctors" [vis0, vis, pp, mo, ml, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ ictW p n s₀.mem vis0 vis pp mo ml co cl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockCtors]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "block_shape_lps", callW_spec p n "check_block_ctors_go"] <;>
    finish (gen := 40) (instances := 20000) [ictW]

end L.Ind
