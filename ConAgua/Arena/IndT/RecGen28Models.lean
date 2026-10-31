module

public import ConAgua.Arena.RecGenSpec.DecB
public import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr

@[expose] public section

/-!
# `classes_nfs`' hand model and its `unified` specs

The model `cnfsE` (its loop `cnsE`) and the specs `cnsLoop_specE`, `cnfsE_spec`, apart from the
loop's refinement (`RecGen28.lean`): they need the code and the copy loop's spec (`RecGenSpec/DecB`),
not the refinements before `RecGen28`, so they build beside that chain instead of on it.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The model -/

section model
variable (p : Prog)

/-- After the copy loop: the record's tail and the result slot (a store out of bounds: `oob`). -/
def cnsEK3 (nm mw eo el qr j : Word) (rest : Mem → Except Err Mem) : Option Mem → Except Err Mem
  | none => .error .oob
  | some m =>
    if (nm + 9).toNat < (m.arr64 IW).size ∧ (nm + 10).toNat < (m.arr64 IW).size ∧
        (nm + 11).toNat < (m.arr64 IW).size ∧ (nm + 12).toNat < (m.arr64 IW).size ∧
        (qr + j).toNat < (m.arr64 IW).size then rest (wrTail m nm mw eo el qr j)
    else .error .oob

/-- After `iw_alloc(13)` (its failure claims nothing): the copy loop. -/
def cnsEK2 (k : Nat) (mw eo el qr j : Word) (rest : Mem → Except Err Mem) :
    Option (List Word × Mem) → Except Err Mem
  | none => .error .oob
  | some (r, m) => cnsEK3 (r.headD 0) mw eo el qr j rest (ncpW (k + 1) m (r.headD 0) mw 0)

/-- After `target_major_nfs`: its error passed on, else the fresh record. -/
def cnsEK1 (k : Nat) (mw qr j : Word) (rest : Mem → Except Err Mem) :
    Except Err (List Word × Mem) → Except Err Mem
  | .error ε => .error ε
  | .ok (r, m) => cnsEK2 k mw (r.headD 0) (r.tail.headD 0) qr j rest (callW p k "iw_alloc" [13] m)

/-- **The model of `classes_nfs`' loop** at L fuel `k`, from cursor `j`: the memory at the exit. -/
def cnsE : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Except Err Mem
  | 0, _, _, _, _, _, _, _, _, _, _, _ => .error .outOfFuel
  | k + 1, m, vis, q, fto, ftl, tblo, tbll, mo, ml, qr, j =>
    if j < ml then
      cnsEK1 p k (rdW (m.arr64 IW) (mo + j)) qr j
        (fun m' => cnsE k m' vis q fto ftl tblo tbll mo ml qr (j + 1))
        (callE p k "target_major_nfs" [vis, q, fto, ftl,
          rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 11), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 12),
          rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 1), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 2),
          rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 3), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 6),
          rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 7), tblo, tbll] m)
    else .ok m

section arms
variable (k : Nat) (m : Mem) (vis q fto ftl tblo tbll mo ml qr j nm mw eo el : Word) (r : List Word)
  (rest : Mem → Except Err Mem) (ε : Err)
theorem cnsEK3_none : cnsEK3 nm mw eo el qr j rest none = .error .oob := rfl
theorem cnsEK3_ok (h : (nm + 9).toNat < (m.arr64 IW).size ∧ (nm + 10).toNat < (m.arr64 IW).size ∧
    (nm + 11).toNat < (m.arr64 IW).size ∧ (nm + 12).toNat < (m.arr64 IW).size ∧
    (qr + j).toNat < (m.arr64 IW).size) :
    cnsEK3 nm mw eo el qr j rest (some m) = rest (wrTail m nm mw eo el qr j) := by
  simp only [cnsEK3]; rw [ite_eq_left h]
theorem cnsEK3_bad (h : ¬ ((nm + 9).toNat < (m.arr64 IW).size ∧ (nm + 10).toNat < (m.arr64 IW).size ∧
    (nm + 11).toNat < (m.arr64 IW).size ∧ (nm + 12).toNat < (m.arr64 IW).size ∧
    (qr + j).toNat < (m.arr64 IW).size)) :
    cnsEK3 nm mw eo el qr j rest (some m) = .error .oob := by
  simp only [cnsEK3]; rw [ite_eq_right h]
theorem cnsEK2_none : cnsEK2 k mw eo el qr j rest none = .error .oob := rfl
theorem cnsEK2_some : cnsEK2 k mw eo el qr j rest (some (r, m)) =
    cnsEK3 (r.headD 0) mw eo el qr j rest (ncpW (k + 1) m (r.headD 0) mw 0) := rfl
theorem cnsEK1_err : cnsEK1 p k mw qr j rest (.error ε) = .error ε := rfl
theorem cnsEK1_ok : cnsEK1 p k mw qr j rest (.ok (r, m)) =
    cnsEK2 k mw (r.headD 0) (r.tail.headD 0) qr j rest (callW p k "iw_alloc" [13] m) := rfl
theorem cnsE_zero : cnsE p 0 m vis q fto ftl tblo tbll mo ml qr j = .error .outOfFuel := rfl
theorem cnsE_exit (h : ¬ j < ml) : cnsE p (k + 1) m vis q fto ftl tblo tbll mo ml qr j = .ok m := by
  simp only [cnsE]; rw [ite_eq_right h]
theorem cnsE_step (h : j < ml) : cnsE p (k + 1) m vis q fto ftl tblo tbll mo ml qr j =
    cnsEK1 p k (rdW (m.arr64 IW) (mo + j)) qr j
      (fun m' => cnsE p k m' vis q fto ftl tblo tbll mo ml qr (j + 1))
      (callE p k "target_major_nfs" [vis, q, fto, ftl,
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 11), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 12),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 1), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 2),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 3), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 6),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 7), tblo, tbll] m) := by
  simp only [cnsE]; rw [ite_eq_left h]
end arms

/-- After the loop: the result slice. -/
def cnfsEK2 (qr ml : Word) : Except Err Mem → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok m => .ok ([qr, ml], m)

/-- After the result slice's allocation: the loop. -/
def cnfsEK1 (n : Nat) (vis q fto ftl tblo tbll mo ml : Word) :
    Option (List Word × Mem) → Except Err (List Word × Mem)
  | none => .error .oob
  | some (r, m) => cnfsEK2 (r.headD 0) ml (cnsE p (n + 1) m vis q fto ftl tblo tbll mo ml (r.headD 0) 0)

/-- **The model of `classes_nfs`** at exec fuel `n`. -/
def cnfsE : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word →
    Except Err (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => .error .outOfFuel
  | n + 1, m, vis, q, fto, ftl, tblo, tbll, mo, ml =>
    cnfsEK1 p n vis q fto ftl tblo tbll mo ml (callW p n "iw_alloc" [ml] m)

section arms
variable (n : Nat) (m : Mem) (vis q fto ftl tblo tbll mo ml qr : Word) (r : List Word) (ε : Err)
theorem cnfsEK2_err : cnfsEK2 qr ml (.error ε) = .error ε := rfl
theorem cnfsEK2_ok : cnfsEK2 qr ml (.ok m) = .ok ([qr, ml], m) := rfl
theorem cnfsEK1_none : cnfsEK1 p n vis q fto ftl tblo tbll mo ml none = .error .oob := rfl
theorem cnfsEK1_some : cnfsEK1 p n vis q fto ftl tblo tbll mo ml (some (r, m)) =
    cnfsEK2 (r.headD 0) ml (cnsE p (n + 1) m vis q fto ftl tblo tbll mo ml (r.headD 0) 0) := rfl
theorem cnfsE_zero : cnfsE p 0 m vis q fto ftl tblo tbll mo ml = .error .outOfFuel := rfl
theorem cnfsE_succ : cnfsE p (n + 1) m vis q fto ftl tblo tbll mo ml =
    cnfsEK1 p n vis q fto ftl tblo tbll mo ml (callW p n "iw_alloc" [ml] m) := rfl
end arms

end model

attribute [ind_grind =] cnsEK3_none cnsEK3_ok cnsEK3_bad cnsEK2_none cnsEK2_some cnsEK1_err cnsEK1_ok
  cnsE_zero cnsE_exit cnsE_step cnfsEK2_err cnfsEK2_ok cnfsEK1_none cnfsEK1_some

/-! ## The `unified` specs -/

/-- `iw_alloc`'s ok model and its failures' class `0` (outside the verdict closure). -/
theorem iwAlloc_specU (p : Prog) (k : Nat) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "iw_alloc" vs
    ⦃fun r s' => LocEq s' s₀ ∧ callW p k "iw_alloc" vs s₀.mem = some (r, s'.mem);
     fun e => closedNV p _root_.L.Checker.nvFns = true → e.cls = 0⦄ :=
  Triple.nv (_root_.L.Checker.nv_mem (by decide +kernel)) (callW_spec p k "iw_alloc" vs s₀)

/-- The copy loop's ok model and its failures' class `0`. -/
theorem ncpLoop_specU (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p f ncpLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
      s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 6 = s₀.loc 6 ∧
      s'.loc 7 = s₀.loc 7 ∧ s'.loc 8 = s₀.loc 8 ∧ s'.loc 9 = s₀.loc 9 ∧ s'.loc 10 = s₀.loc 10 ∧
      s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧
      ncpW f s₀.mem (s₀.loc 13) (s₀.loc 10) (s₀.loc 14) = some s'.mem;
     fun e => closedNV p _root_.L.Checker.nvFns = true → e.cls = 0⦄ :=
  Triple.and_err (ncpLoop_spec p f s₀)
    (M.triple_of_run' (fun _ _ _ _ _ => trivial) fun _ _ _ hr hnv =>
      M.of_run_err (P := fun _ => True) trivial hr (exec_nv p hnv f ncpLoop (by decide +kernel)))

set_option maxHeartbeats 1600000 in
/-- The loop's `unified` spec. -/
theorem cnsLoop_specE (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p k cnsLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 7 = s₀.loc 7 ∧ s'.loc 8 = s₀.loc 8 ∧
      cnsE p k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)
        (s₀.loc 7) (s₀.loc 8) (s₀.loc 9) = .ok s'.mem;
     fun ε => closedNV p _root_.L.Checker.nvFns = true → ε.cls ≠ 0 →
      cnsE p k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)
        (s₀.loc 7) (s₀.loc 8) (s₀.loc 9) = .error ε⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := cnsLoop) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih,
        callE_spec p k "target_major_nfs", iwAlloc_specU p k,
        fun s => Triple.step_exec' (ncpLoop_specU p (k + 1) s)] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq, wrTail, Err.cls]

set_option maxHeartbeats 1600000 in
/-- **`classes_nfs`' `unified` spec**: an ok run is the model's value, an error of class `≠ 0` the
model's error (`iw_alloc` and the copy loop outside the verdict closure). -/
theorem cnfsE_spec (p : Prog) (hp : p.lookup "classes_nfs" = some classesNfsL) (n : Nat) (s₀ : St)
    (vis q fto ftl tblo tbll mo ml : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "classes_nfs" [vis, q, fto, ftl, tblo, tbll, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ cnfsE p n s₀.mem vis q fto ftl tblo tbll mo ml = .ok (r, s'.mem);
     fun ε => closedNV p _root_.L.Checker.nvFns = true → ε.cls ≠ 0 →
      cnfsE p n s₀.mem vis q fto ftl tblo tbll mo ml = .error ε⦄ := by
  rw [invoke_eq _ hp, classesNfsL_eq]
  simp only [callFn, classesNfsL']
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, iwAlloc_specU p n,
      fun s => Triple.step_exec' (cnsLoop_specE p (n + 1) s)] <;>
    finish (gen := 40) (instances := 20000) [cnfsE_succ, loc_init4, loc_init5, loc_init6, loc_init7]

end L.Ind
