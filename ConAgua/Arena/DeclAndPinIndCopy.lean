import ConAgua.Arena.DeclStep
import ConAgua.Arena.IndMaster
import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic

/-!
# The `And` pin's inductive arm, part 2b: the word models of `ind_block_to_erec`

`dind_copy(d, s, l)` (`dindCopyW`), `ind_rec_copy(s)` (`ircW`), `ind_copy_go(o, bo, bl)`
(`icgW`), `ind_block_to_erec(i)` (`ibeW`), each with its `vcgen` spec (`…_specW`). What they
leave is `DeclAndPinIndCopy2.lean`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Front (DECL DLP)
open L.Ind (erAllocW erecAlloc erecAlloc_specW)

/-! ## `dind_copy` -/

/-- The model of `dind_copy(d, s, l)`. -/
def dindCopyW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, d, s, l =>
    if l = 0 then some m
    else if s = 0 then none
    else dindCopyW n (m.set64 EREC d (rdW (m.arr64 DLP) s)) (d + 1) (s + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (d s l : Word)
theorem dindCopyW_nil (hl : l = 0) : dindCopyW (n + 1) m d s l = some m := by simp [dindCopyW, hl]
theorem dindCopyW_src (hl : l ≠ 0) (hs : s = 0) : dindCopyW (n + 1) m d s l = none := by
  simp [dindCopyW, hl, hs]
theorem dindCopyW_step (hl : l ≠ 0) (hs : s ≠ 0) :
    dindCopyW (n + 1) m d s l =
      dindCopyW n (m.set64 EREC d (rdW (m.arr64 DLP) s)) (d + 1) (s + 1) (l - 1) := by
  simp [dindCopyW, hl, hs]
end arms

grind_pattern [ind_grind] dindCopyW_nil => dindCopyW (n + 1) m d s l
grind_pattern [ind_grind] dindCopyW_src => dindCopyW (n + 1) m d s l
grind_pattern [ind_grind] dindCopyW_step => dindCopyW (n + 1) m d s l

theorem dindCopy_specW (p : Prog) (hp : p.lookup "dind_copy" = some dindCopy) (n : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "dind_copy" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ dindCopyW n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ d s l; rw [invoke_eq _ hp]; simp only [callFn, dindCopy]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ d s l
    rw [invoke_eq _ hp]
    simp only [callFn, dindCopy]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20)

/-! ## `ind_rec_copy` -/

section irc

/-- After the record's own copy: the relocated words. -/
def ircT2 (pp q r k : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m6 => some (pp, if k = 5 then (m6.set64 EREC (pp + 2) q).set64 EREC (pp + 7) r
      else m6.set64 EREC (pp + 2) q)

/-- After the record's allocation (`nn` words). -/
def ircT (n : Nat) (s q r nn k : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (pp, m5) => ircT2 pp q r k (dindCopyW n m5 pp s nn)

/-- After a recursor's rule copy. -/
def ircR2 (n : Nat) (s q r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m4 => ircT n s q r 9 5 (erAllocW m4 9)

/-- After a recursor's rule allocation. -/
def ircR1 (n : Nat) (s q : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m3) => ircR2 n s q r
      (dindCopyW n m3 r (rdW (m3.arr64 DLP) (s + 7)) (11 * rdW (m3.arr64 DLP) (s + 8)))

/-- After the level parameters' copy: the dispatch on the kind `k`. -/
def ircK2 (n : Nat) (s q k : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 =>
    if k = 3 then ircT n s q 0 20 k (erAllocW m2 20)
    else if k = 4 then ircT n s q 0 7 k (erAllocW m2 7)
    else if k = 5 then
      if 1152921504606846976 ≤ rdW (m2.arr64 DLP) (s + 8) then none
      else ircR1 n s q (erAllocW m2 (11 * rdW (m2.arr64 DLP) (s + 8)))
    else none

/-- After the level parameters' allocation. -/
def ircK1 (n : Nat) (s k : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q, m1) => ircK2 n s q k
      (dindCopyW n m1 q (rdW (m1.arr64 DLP) (s + 2)) (rdW (m1.arr64 DLP) (s + 3)))

/-- **The model of `ind_rec_copy(s)`.** -/
def ircW : Nat → Mem → Word → Option (Word × Mem)
  | 0, _, _ => none
  | n + 1, m, s => ircK1 n s (rdW (m.arr64 DLP) s) (erAllocW m (rdW (m.arr64 DLP) (s + 3)))

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (s q r pp nn k : Word)
theorem ircW_step : ircW (n + 1) m s =
    ircK1 n s (rdW (m.arr64 DLP) s) (erAllocW m (rdW (m.arr64 DLP) (s + 3))) := rfl
theorem ircK1_some : ircK1 n s k (some (q, m1)) = ircK2 n s q k
    (dindCopyW n m1 q (rdW (m1.arr64 DLP) (s + 2)) (rdW (m1.arr64 DLP) (s + 3))) := rfl
theorem ircK2_some : ircK2 n s q k (some m2) =
    if k = 3 then ircT n s q 0 20 k (erAllocW m2 20)
    else if k = 4 then ircT n s q 0 7 k (erAllocW m2 7)
    else if k = 5 then
      if 1152921504606846976 ≤ rdW (m2.arr64 DLP) (s + 8) then none
      else ircR1 n s q (erAllocW m2 (11 * rdW (m2.arr64 DLP) (s + 8)))
    else none := rfl
theorem ircR1_some : ircR1 n s q (some (r, m3)) = ircR2 n s q r
    (dindCopyW n m3 r (rdW (m3.arr64 DLP) (s + 7)) (11 * rdW (m3.arr64 DLP) (s + 8))) := rfl
theorem ircR2_some : ircR2 n s q r (some m4) = ircT n s q r 9 5 (erAllocW m4 9) := rfl
theorem ircT_some : ircT n s q r nn k (some (pp, m5)) = ircT2 pp q r k (dindCopyW n m5 pp s nn) := rfl
theorem ircT2_some : ircT2 pp q r k (some m6) = some (pp, if k = 5 then
    (m6.set64 EREC (pp + 2) q).set64 EREC (pp + 7) r else m6.set64 EREC (pp + 2) q) := rfl
end arms

grind_pattern [ind_grind] ircW_step => ircW (n + 1) m s
grind_pattern [ind_grind] ircK1_some => ircK1 n s k (some (q, m1))
grind_pattern [ind_grind] ircK2_some => ircK2 n s q k (some m2)
grind_pattern [ind_grind] ircR1_some => ircR1 n s q (some (r, m3))
grind_pattern [ind_grind] ircR2_some => ircR2 n s q r (some m4)
grind_pattern [ind_grind] ircT_some => ircT n s q r nn k (some (pp, m5))
grind_pattern [ind_grind] ircT2_some => ircT2 pp q r k (some m6)

end irc

theorem indRecCopy_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hd : p.lookup "dind_copy" = some dindCopy) (hp : p.lookup "ind_rec_copy" = some indRecCopy)
    (n : Nat) (s₀ : St) (s : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "ind_rec_copy" [s]
    ⦃fun r s' => LocEq s' s₀ ∧ ircW n s₀.mem s = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, indRecCopy]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        erecAlloc_specW p ha n, dindCopy_specW p hd n] <;>
      finish (gen := 20) [rdW_eq]

/-! ## `ind_copy_go`, `ind_block_to_erec` -/

/-- After a record's copy: its pointer into the slot, then the rest. -/
def icgK (f : Mem → Word → Word → Word → Option Mem) (o bo bl : Word) :
    Option (Word × Mem) → Option Mem
  | none => none
  | some (p, m1) => f (m1.set64 EREC o p) (o + 1) (bo + 1) (bl - 1)

/-- **The model of `ind_copy_go(o, bo, bl)`.** -/
def icgW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, o, bo, bl =>
    if bl = 0 then some m else icgK (icgW n) o bo bl (ircW n m (rdW (m.arr64 DLP) bo))

section arms
variable (n : Nat) (m m1 : Mem) (o bo bl p : Word) (f : Mem → Word → Word → Word → Option Mem)
theorem icgW_nil (hl : bl = 0) : icgW (n + 1) m o bo bl = some m := by simp [icgW, hl]
theorem icgW_step (hl : bl ≠ 0) :
    icgW (n + 1) m o bo bl = icgK (icgW n) o bo bl (ircW n m (rdW (m.arr64 DLP) bo)) := by
  simp [icgW, hl]
theorem icgK_some : icgK f o bo bl (some (p, m1)) = f (m1.set64 EREC o p) (o + 1) (bo + 1) (bl - 1) :=
  rfl
end arms

grind_pattern [ind_grind] icgW_nil => icgW (n + 1) m o bo bl
grind_pattern [ind_grind] icgW_step => icgW (n + 1) m o bo bl
grind_pattern [ind_grind] icgK_some => icgK f o bo bl (some (p, m1))

theorem indCopyGo_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hd : p.lookup "dind_copy" = some dindCopy) (hr : p.lookup "ind_rec_copy" = some indRecCopy)
    (hp : p.lookup "ind_copy_go" = some indCopyGo) (n : Nat) :
    ∀ (s₀ : St) (o bo bl : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "ind_copy_go" [o, bo, bl]
    ⦃fun _ s' => LocEq s' s₀ ∧ icgW n s₀.mem o bo bl = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ o bo bl; rw [invoke_eq _ hp]; simp only [callFn, indCopyGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o bo bl
    rw [invoke_eq _ hp]
    simp only [callFn, indCopyGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih,
        indRecCopy_specW p ha hd hr n] <;>
      finish (gen := 20)

/-- **The model of `ind_block_to_erec(i)`.** -/
def ibeW (n : Nat) (m : Mem) (i : Word) : Option (List Word × Mem) :=
  match erAllocW m (rdW (m.arr64 DECL) (4 + 8 * i)) with
  | none => none
  | some (o, m1) =>
    match icgW n m1 o (rdW (m.arr64 DECL) (3 + 8 * i)) (rdW (m.arr64 DECL) (4 + 8 * i)) with
    | none => none
    | some m2 => some ([o, rdW (m.arr64 DECL) (4 + 8 * i)], m2)

theorem indBlockToErec_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hd : p.lookup "dind_copy" = some dindCopy) (hr : p.lookup "ind_rec_copy" = some indRecCopy)
    (hg : p.lookup "ind_copy_go" = some indCopyGo)
    (hp : p.lookup "ind_block_to_erec" = some indBlockToErec) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "ind_block_to_erec" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ n', ibeW n' s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, indBlockToErec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hk : ∀ o m1 m2, erAllocW s₀.mem (rdW (s₀.mem.arr64 DECL) (4 + 8 * i)) = some (o, m1) →
        icgW n m1 o (rdW (s₀.mem.arr64 DECL) (3 + 8 * i)) (rdW (s₀.mem.arr64 DECL) (4 + 8 * i)) = some m2 →
        ibeW n s₀.mem i = some ([o, rdW (s₀.mem.arr64 DECL) (4 + 8 * i)], m2) := by
      intro o m1 m2 h1 h2; simp [ibeW, h1, h2]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        erecAlloc_specW p ha n, indCopyGo_specW p ha hd hr hg n] <;>
      finish (gen := 20)

end L.Arena
