module

public import ConAgua.Front.Preserve
public import ConAgua.L.Notation
public import ConAgua.Arena.Pool
public import ConAgua.Scan.Common
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

@[expose] public section

/-!
# The whole-buffer driver: `front_run()`

`front_run()` is `front_init()` and then `front_line(i)` from `i = 0` while `i` is inside the
input, as con-ron's `parseBytes` runs `feedChunk` over a whole buffer and then `applyFinalLine` on
the tail: `0` when every line applied, else the number of the first line that did not scan (a
line `front_line` cannot apply aborts the run). A last line without a newline is applied by
`front_line` itself (its `next` is `0`), where `feedChunk` leaves it as the tail and
`applyFinalLine` applies it.

The spec is generic in the models of `front_init` and `front_line` (`initW`, `lineW`): the
caller supplies their triples. A call is made only at a memory whose input bytes are `B` and
whose pool has `Z` words, and every call keeps both (`Keep`, `ConAgua.Front.Preserve`); so the
callee specs may assume them.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Front

open L.Arena (POOL)

/-- The input buffer (byte array 0). -/
abbrev IN0 : ArrId := 0

def runLoop : Stmt := lblk (i, ok, nx, ln) {
  while i < len(IN0.u8) {
    (ok, nx) := call front_line(i);
    ln += 1;
    if ok == 0 { return ln };
    if nx == 0 { return 0 };
    if nx <= i { return ln };
    i := nx
  }
}

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:561-574 ConRon.Arena.Frontend.parseBytes -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:520-549 ConRon.Arena.Frontend.feedChunk
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:506-518 ConRon.Arena.Frontend.applyFinalLine
@[l_impl ConRon.Arena.Frontend.parseBytes ConRon.Arena.Frontend.feedChunk
  ConRon.Arena.Frontend.applyFinalLine]
def frontRun : FunDecl := lfn () locals (i, ok, nx, ln) {
  ok := call front_init();
  ⟪runLoop⟫;
  return 0
}

/-- **The model of the loop**: from position `i` after `ln` lines, `(0, memory)` when every line
applied, `(k, memory)` when line `k` did not scan or made no progress, `none` where the L code
aborts (a line model is `none`). -/
def runW (lineW : Mem → Word → Option (Word × Word × Mem)) (sz : Nat) (m : Mem) (i ln : Word) :
    Option (Word × Mem) :=
  if _h : i < UInt64.ofNat sz then
    match lineW m i with
    | none => none
    | some (ok, nx, m') =>
      if ok = 0 then some (ln + 1, m')
      else if nx = 0 then some (0, m')
      else if _hx : i < nx then runW lineW sz m' nx (ln + 1)
      else some (ln + 1, m')
  else some (0, m)
termination_by sz - i.toNat
decreasing_by
  have := L.Scan.lt_of_lt_ofNat _h
  rw [UInt64.lt_iff_toNat_lt] at _hx
  omega

/-- After the line: its result `o` (`none`: the L code aborted). -/
def runK (lineW : Mem → Word → Option (Word × Word × Mem)) (sz : Nat) (i ln : Word) :
    Option (Word × Word × Mem) → Option (Word × Mem)
  | none => none
  | some (ok, nx, m') =>
    if ok = 0 then some (ln + 1, m')
    else if nx = 0 then some (0, m')
    else if i < nx then runW lineW sz m' nx (ln + 1)
    else some (ln + 1, m')

section
variable (lineW : Mem → Word → Option (Word × Word × Mem)) (sz : Nat) (m m' : Mem) (i ln ok nx : Word)
theorem runW_end (h : ¬ i < UInt64.ofNat sz) : runW lineW sz m i ln = some (0, m) := by
  rw [runW, dite_eq_right h]
theorem runW_step (h : i < UInt64.ofNat sz) : runW lineW sz m i ln = runK lineW sz i ln (lineW m i) := by
  rw [runW, dite_eq_left h]
  cases lineW m i with
  | none => rfl
  | some x => obtain ⟨ok, nx, m'⟩ := x; simp only [runK, dite_eq_ite]
theorem runK_none : runK lineW sz i ln none = none := rfl
theorem runK_fail (hok : ok = 0) : runK lineW sz i ln (some (ok, nx, m')) = some (ln + 1, m') := by
  simp [runK, hok]
theorem runK_last (hok : ok ≠ 0) (hnx : nx = 0) :
    runK lineW sz i ln (some (ok, nx, m')) = some (0, m') := by
  simp [runK, hok, hnx]
theorem runK_next (hok : ok ≠ 0) (hnx : nx ≠ 0) (hx : i < nx) :
    runK lineW sz i ln (some (ok, nx, m')) = runW lineW sz m' nx (ln + 1) := by
  simp [runK, hok, hnx, hx]
theorem runK_noprog (hok : ok ≠ 0) (hnx : nx ≠ 0) (hx : ¬ i < nx) :
    runK lineW sz i ln (some (ok, nx, m')) = some (ln + 1, m') := by
  simp [runK, hok, hnx, hx]
end
grind_pattern [lang_grind] runW_end => runW lineW sz m i ln
grind_pattern [lang_grind] runW_step => runW lineW sz m i ln
attribute [lang_grind =] runK_none
grind_pattern [lang_grind] runK_fail => runK lineW sz i ln (some (ok, nx, m'))
grind_pattern [lang_grind] runK_last => runK lineW sz i ln (some (ok, nx, m'))
grind_pattern [lang_grind] runK_next => runK lineW sz i ln (some (ok, nx, m'))
grind_pattern [lang_grind] runK_noprog => runK lineW sz i ln (some (ok, nx, m'))



section spec
variable (p : Prog) (lineW : Mem → Word → Option (Word × Word × Mem)) (B : Array UInt8) (Z : Nat)
  (hline : ∀ n (s₀ : St) (i : Word), s₀.mem.arr8 IN0 = B → (s₀.mem.arr64 POOL).size = Z →
    i < UInt64.ofNat B.size →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "front_line" [i]
    ⦃fun r s' => lineW s₀.mem i = some (r.headD 0, r.tail.headD 0, s'.mem) ∧ Keep s₀.mem s'.mem ∧
      LocEq s' s₀; ⊤⦄)
include hline

theorem runLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN0 = B ∧ (s.mem.arr64 POOL).size = Z⦄
    exec p n runLoop
    ⦃fun r s' => r ≠ .brk ∧
      runW lineW B.size s₀.mem (s₀.loc 0) (s₀.loc 3) = some ((r.retOr [0]).headD 0, s'.mem); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := runLoop) rfl]
    sym only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih, hline n] <;> finish

theorem runLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN0 = B ∧ (s.mem.arr64 POOL).size = Z⦄
    step p (exec p n) runLoop
    ⦃fun r s' => r ≠ .brk ∧
      runW lineW B.size s₀.mem (s₀.loc 0) (s₀.loc 3) = some ((r.retOr [0]).headD 0, s'.mem); ⊤⦄ :=
  Triple.step_exec (runLoop_spec p lineW B Z hline (n + 1) s₀)

/-- After `front_init`: its result (`none`: the L code aborted). -/
def runI (sz : Nat) : Option Mem → Option (Word × Mem)
  | none => none
  | some m₁ => runW lineW sz m₁ 0 0

omit hline in
@[lang_grind =] theorem runI_none (sz : Nat) : runI lineW sz none = none := rfl
omit hline in
@[lang_grind =] theorem runI_some (sz : Nat) (m₁ : Mem) : runI lineW sz (some m₁) = runW lineW sz m₁ 0 0 :=
  rfl

/-- **`front_run()`**: `front_init`'s model, then the loop's from position `0`. -/
theorem frontRun_spec (initW : Mem → Option Mem)
    (hinit : ∀ n (s₀ : St), s₀.mem.arr8 IN0 = B → (s₀.mem.arr64 POOL).size = Z →
      ⦃fun s => s = s₀⦄ invoke p (exec p n) "front_init" []
      ⦃fun _ s' => initW s₀.mem = some s'.mem ∧ Keep s₀.mem s'.mem ∧ LocEq s' s₀; ⊤⦄)
    (hp : p.lookup "front_run" = some frontRun) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN0 = B)
    (hz : (s₀.mem.arr64 POOL).size = Z) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "front_run" []
    ⦃fun r s' => runI lineW B.size (initW s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, frontRun]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hinit n,
        runLoop_step_spec p lineW B Z hline n] <;> finish

end spec


/-! ## With a run invariant

The same, with a run invariant `Inv` of the memory in place of the pool's size: `front_line` may
assume it and must re-establish it when it applies a line (`ok ≠ 0`); `front_init` establishes it
(lane tierpool: the pool's top lies below its capacity, which only the arena relation knows). -/

section specI
variable (p : Prog) (lineW : Mem → Word → Option (Word × Word × Mem)) (B : Array UInt8)
  (Inv : Mem → Prop)
  (hline : ∀ n (s₀ : St) (i : Word), s₀.mem.arr8 IN0 = B → Inv s₀.mem →
    i < UInt64.ofNat B.size →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "front_line" [i]
    ⦃fun r s' => lineW s₀.mem i = some (r.headD 0, r.tail.headD 0, s'.mem) ∧ Keep s₀.mem s'.mem ∧
      (r.headD 0 ≠ 0 → Inv s'.mem) ∧ LocEq s' s₀; ⊤⦄)
include hline

theorem runLoop_specI (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN0 = B ∧ Inv s.mem⦄
    exec p n runLoop
    ⦃fun r s' => r ≠ .brk ∧
      runW lineW B.size s₀.mem (s₀.loc 0) (s₀.loc 3) = some ((r.retOr [0]).headD 0, s'.mem); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := runLoop) rfl]
    sym only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih, hline n] <;> finish

theorem runLoop_step_specI (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN0 = B ∧ Inv s.mem⦄
    step p (exec p n) runLoop
    ⦃fun r s' => r ≠ .brk ∧
      runW lineW B.size s₀.mem (s₀.loc 0) (s₀.loc 3) = some ((r.retOr [0]).headD 0, s'.mem); ⊤⦄ :=
  Triple.step_exec (runLoop_specI p lineW B Inv hline (n + 1) s₀)

/-- **`front_run()`**, with a run invariant: `front_init` establishes it on the memory `M` the run
starts from. -/
theorem frontRun_specI (initW : Mem → Option Mem) (M : Mem)
    (hinit : ∀ n (s₀ : St), s₀.mem = M →
      ⦃fun s => s = s₀⦄ invoke p (exec p n) "front_init" []
      ⦃fun _ s' => initW s₀.mem = some s'.mem ∧ Keep s₀.mem s'.mem ∧ Inv s'.mem ∧ LocEq s' s₀; ⊤⦄)
    (hp : p.lookup "front_run" = some frontRun) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN0 = B)
    (hM : s₀.mem = M) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "front_run" []
    ⦃fun r s' => runI lineW B.size (initW s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, frontRun]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hinit n,
        runLoop_step_specI p lineW B Inv hline n] <;> finish

end specI

end L.Front
