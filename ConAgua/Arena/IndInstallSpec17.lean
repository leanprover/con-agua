import ConAgua.Arena.IndInstallSpec16
import ConAgua.Arena.IndSumSpec13

/-!
# Refinements of `IndInstall`, part 17 (lane `indproofs2`, helper `install`): `checkBlockIdxSorts`

Per member: the former's telescope opened (`open_pis_at_fvars_f`'s stub), the index binders'
universes (`check_struct_field_sorts_i`, `IndSumSpec11`'s refinement, `installSimFsorts`), recursion as the twin's with the pointers consed (D18).
-/


noncomputable section

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_struct_field_sorts_i` as a callee (lane `indproofs2`'s `IndSumSpec11`) -/

/-- **`check_struct_field_sorts_i(vis, isProp, large, s, nP, fvs.off, fvs.len, idx.off, idx.len,
j)` as a `Sim`** on its run (`fsortsW_ok`, sorry-free up to its own stubs): the fields' sorts, a
fresh handle slice below the top. Its hypotheses are the caller's: the stage relation, the two
slices decoded below the top, `s` a handle, and `nP + j` below `2^64` (the callers' L code guards
it). -/
theorem installSimFsorts {p : Prog} (hP : SumProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} (isP large s nP fo fl io il j : Word) (hs : H s)
    (fvs idx : List EIdx)
    (hpre : StageR dn vis fe m a ∧ decHL m fo.toNat fl.toNat = some fvs ∧
        fo.toNat + fl.toNat ≤ iwTop m ∧ decHL m io.toNat il.toNat = some idx ∧
        io.toNat + il.toNat ≤ iwTop m)
    (hnj : nP.toNat + j.toNat < 2 ^ 64) :
    Sim (callW p n "check_struct_field_sorts_i" [vis, isP, large, s, nP, fo, fl, io, il, j] m)
      (checkStructFieldSortsI V fe (isP != 0) (large != 0) (decI s) nP.toNat fvs idx j.toNat) a
      (fun r x m' a' => KeepPost dn vis fe (decRL (fun m => decHL m) 0) m m' a' r x) := by
  rcases n with _ | k
  · intro r m' e; rw [callW_zero] at e; cases e
  intro r m' e
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (fsortsW_spec p hP.hg hP.hpw hP.het hP.hcn hP.hfsb hP.hcfg hP.ha hP.hcfs hP.ad.ftd k _ vis isP large s nP
      fo fl io il j) e
  obtain ⟨hS, hfd, hfb, hid, hib⟩ := hpre
  obtain ⟨x, a', h1, hS', hg', hd, hb⟩ :=
    fsortsW_ok k m a isP large s nP fo fl io il j fvs idx hS hfd hfb hid hib hs hnj r s'.mem hW
  have g0 : r.getD 0 0 = r.headD 0 := by rcases r with _ | ⟨_, _⟩ <;> rfl
  have g1 : r.getD (0 + 1) 0 = r.tail.headD 0 := by rcases r with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  refine ⟨x, a', h1, hS', hg', ?_⟩
  show decHL s'.mem (r.getD 0 0).toNat (r.getD (0 + 1) 0).toNat = some x ∧ _
  rw [g0, g1]; exact ⟨hd, hb⟩

/-! ## `check_block_idx_sorts_one` -/

/-- The index binders' slice: the telescope's tail past `nP`, `(0, 0)` when empty. -/
def idxTail (nP o l : Word) : Word × Word := if nP < l then (o + nP, l - nP) else (0, 0)

def iisK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
def iisK2 (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => iisK3 (callW p n "rec2" [r.headD 0, r.tail.headD 0] m)
def iisK1 (p : Prog) (n : Nat) (vis nP ni srt : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else iisK2 p n (callW p n "check_struct_field_sorts_i" [vis, 1, 0, srt, nP,
      (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).1,
      (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).2, 0, 0, ni] m)

/-- **The model of `check_block_idx_sorts_one(vis, p, ms, cvTa)`** (body fuel `n`). -/
def iisW (p : Prog) (n : Nat) (m : Mem) (vis pp ms cv : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (ms + 1) < rdW (m.arr64 IW) (pp + 4) then none
  else iisK1 p n vis (rdW (m.arr64 IW) (pp + 4)) (rdW (m.arr64 IW) (ms + 1)) (rdW (m.arr64 IW) (pp + 6))
    (callW p n "open_pis_at_fvars_f" [rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (ms + 1),
      rdW (m.arr64 EREC) (cv + 3), 0] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis nP ni srt : Word) (r : List Word)
theorem iisK3_some : iisK3 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem iisK2_some : iisK2 p n (some (r, m)) = iisK3 (callW p n "rec2" [r.headD 0, r.tail.headD 0] m) := rfl
theorem iisK1_none (h : r.headD 0 = 0) : iisK1 p n vis nP ni srt (some (r, m)) = none := by
  simp only [iisK1, h, ↓reduceIte]
theorem iisK1_some (h : ¬ r.headD 0 = 0) : iisK1 p n vis nP ni srt (some (r, m)) =
    iisK2 p n (callW p n "check_struct_field_sorts_i" [vis, 1, 0, srt, nP,
      (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).1,
      (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).2, 0, 0, ni] m) := by
  simp only [iisK1, h, ↓reduceIte, if_false]
end arms
attribute [ind_grind] iisK3_some iisK2_some iisK1_none iisK1_some

set_option maxHeartbeats 1600000 in
theorem iis_spec (p : Prog) (hp : p.lookup "check_block_idx_sorts_one" = some checkBlockIdxSortsOne)
    (n : Nat) (s₀ : St) (vis pp ms cv : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_idx_sorts_one" [vis, pp, ms, cv]
    ⦃fun r s' => LocEq s' s₀ ∧ iisW p n s₀.mem vis pp ms cv = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockIdxSortsOne]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "open_pis_at_fvars_f", callW_spec p n "check_struct_field_sorts_i",
    callW_spec p n "rec2"]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    List.headD_nil, List.tail_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval, BinOp.eval,
    Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, iisW, idxTail, rdW_eq]

/-! ## `check_block_idx_sorts` -/

def iisrK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

mutual
/-- **The model of `check_block_idx_sorts(vis, p, msO, msL, cvO, cvL)`** at exec fuel `n`. -/
def iisrW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, pp, mo, ml, co, cl =>
    if ml = 0 then some ([0, 0], m) else if cl = 0 then some ([0, 0], m)
    else iisrK1 p n vis pp mo ml co cl (callW p n "check_block_idx_sorts_one"
      [vis, pp, rdW (m.arr64 IW) mo, rdW (m.arr64 IW) co] m)
def iisrK1 (p : Prog) (n : Nat) (vis pp mo ml co cl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => iisrK2 p n (r.headD 0) (iisrW p n m vis pp (mo + 1) (ml - 1) (co + 1) (cl - 1))
def iisrK2 (p : Prog) (n : Nat) (hp : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => iisrK3 (callW p n "sl_cons" [hp, r.headD 0, r.tail.headD 0] m)
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis pp mo ml co cl hp : Word) (r : List Word)
theorem iisrW_zero : iisrW p 0 m vis pp mo ml co cl = none := by simp [iisrW]
theorem iisrW_nil1 (h : ml = 0) : iisrW p (n + 1) m vis pp mo ml co cl = some ([0, 0], m) := by
  simp [iisrW, h]
theorem iisrW_nil2 (h1 : ml ≠ 0) (h : cl = 0) : iisrW p (n + 1) m vis pp mo ml co cl = some ([0, 0], m) := by
  simp [iisrW, h1, h]
theorem iisrW_cons (h1 : ml ≠ 0) (h2 : cl ≠ 0) : iisrW p (n + 1) m vis pp mo ml co cl =
    iisrK1 p n vis pp mo ml co cl (callW p n "check_block_idx_sorts_one"
      [vis, pp, rdW (m.arr64 IW) mo, rdW (m.arr64 IW) co] m) := by simp [iisrW, h1, h2]
theorem iisrK1_some : iisrK1 p n vis pp mo ml co cl (some (r, m)) =
    iisrK2 p n (r.headD 0) (iisrW p n m vis pp (mo + 1) (ml - 1) (co + 1) (cl - 1)) := by simp [iisrK1]
theorem iisrK2_some : iisrK2 p n hp (some (r, m)) =
    iisrK3 (callW p n "sl_cons" [hp, r.headD 0, r.tail.headD 0] m) := by simp [iisrK2]
theorem iisrK3_some : iisrK3 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
end arms
attribute [ind_grind] iisrW_nil1 iisrW_nil2 iisrW_cons iisrK1_some iisrK2_some iisrK3_some

theorem iisr_spec (p : Prog) (hp : p.lookup "check_block_idx_sorts" = some checkBlockIdxSorts) (n : Nat) :
    ∀ (s₀ : St) (vis pp mo ml co cl : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_idx_sorts" [vis, pp, mo, ml, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ iisrW p n s₀.mem vis pp mo ml co cl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis pp mo ml co cl; rw [invoke_eq _ hp]; simp only [callFn, checkBlockIdxSorts]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis pp mo ml co cl
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockIdxSorts]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "check_block_idx_sorts_one", callW_spec p n "sl_cons", ih] <;>
      finish (gen := 20) [rdW_eq]

end L.Ind
