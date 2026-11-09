module

public import ConAgua.Arena.IndDeclConstsTable
public import ConAgua.Arena.IndDeclConstsFrame
public import ConAgua.Arena.IndDeclConstsTwin
public import ConAgua.Arena.IndRealPartsC2
public import ConAgua.Arena.DeclBasisRef
public import ConAgua.Arena.DeclAndPinIndCopy2
public import ConAgua.Arena.DeclRec
public import ConAgua.Arena.DeclBasisSpec
public import ConAgua.Arena.IndPosSpec.GgW2
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndDeclConsts

@[expose] public section

/-!
# What a declaration installs: the refinements (lane `ronsync2`, stage 3)

`decl_constants(i)` refines con-ron's `declConstants d` and `decl_tables(i)` its `declTables d`
(`Arena/Install.lean`), at the statements of `IndDeclConstsSpec.lean`. Each L function has a
model (`dconW`, `daW`, `diW`, `dtW`: calls as `callW`, continuations in the `bkW` style); the
proofs follow the twin's arms: `erec_ci` (`erecCiW_ok`), `quot_at`/`basis_name_hit`/
`basis_at_block` (`BasisRefs`), `ind_block_to_erec` (`indBlockToErec_ok`), `block_shape`
(`blockShape_refinesC`), `block_constants` (`bkW_ok`), `block_tables` (`btsW_ok`). The frame
facts come from the write set (`IndDeclConstsFrame.lean`: `dc_keep`, `dc0_keepI1`), `CheckOK`
across the twin's run from `IndDeclConstsTwin.lean`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena
open L.Front (DECL DLP)

/-! ## The models -/

/-- After `sl_new1`/`basis_at_block`/…: the pair. -/
abbrev dcPair : Option (List Word × Mem) → Option (List Word × Mem) := bfgK4

/-- After a record: `sl_new1` of it. -/
def dcNew1 (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bfgK4 (callW p n "sl_new1" [r.headD 0] m)

/-- `decl_constants_axiom`, after the second pin (`sorryAx`). -/
def daK2 (p : Prog) (n : Nat) (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if erRd m (q + 1) = r.headD 0 then some ([0, 0], m)
      else bfgK4 (callW p n "sl_new1" [q] m)

/-- `decl_constants_axiom`, after the first pin (`Quot.sound`). -/
def daK1 (p : Prog) (n : Nat) (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if erRd m (q + 1) = r.headD 0 then dcNew1 p n (callW p n "quot_at" [4, q + 1] m)
      else daK2 p n q (callW p n "pin_at" [13] m)

/-- **The model of `decl_constants_axiom(q)`**. -/
def daW (p : Prog) : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, q => daK1 p n q (callW p n "pin_at" [4] m)

/-- `decl_constants_ind`, after `block_shape`. -/
def diK2 (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then some ([0, 0], m)
      else bfgK4 (callW p n "block_constants" [r.tail.headD 0] m)

/-- `decl_constants_ind`, after `basis_name_hit`. -/
def diK1 (p : Prog) (n : Nat) (bo bl nP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then diK2 p n (callW p n "block_shape" [nP, bo, bl] m)
      else bfgK4 (callW p n "basis_at_block" [r.tail.headD 0, bo, bl] m)

/-- **The model of `decl_constants_ind(bo, bl, nP)`**. -/
def diW (p : Prog) : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, bo, bl, nP => diK1 p n bo bl nP (callW p n "basis_name_hit" [bo, bl] m)

/-- The quotient slot of a record's kind word. -/
def qSlot (w : Word) : Word := if w = 1 then 0 else if w = 2 then 1 else if w = 3 then 2 else 3

/-- `decl_constants`, a quotient record after `erec_ci`. -/
def dcKq (p : Prog) (n : Nat) (i : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => dcNew1 p n (callW p n "quot_at" [qSlot (rdW (m.arr64 DECL) (7 + 8 * i)), r.headD 0 + 1] m)

/-- `decl_constants`, an axiom after `erec_ci`. -/
def dcKa (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bfgK4 (callW p n "decl_constants_axiom" [r.headD 0] m)

/-- `decl_constants`, an inductive block after `ind_block_to_erec`. -/
def dcKi (p : Prog) (n : Nat) (i : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bfgK4 (callW p n "decl_constants_ind"
      [r.headD 0, r.tail.headD 0, rdW (m.arr64 DECL) (5 + 8 * i)] m)

/-- **The model of `decl_constants(i)`**, by the record's kind. -/
def dconW (p : Prog) : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, i =>
    let k := rdW (m.arr64 DECL) (1 + 8 * i)
    if k = 2 then dcNew1 p n (callW p n "erec_ci" [i, 1] m)
    else if k = 3 then dcNew1 p n (callW p n "erec_ci" [i, 2] m)
    else if k = 4 then dcNew1 p n (callW p n "erec_ci" [i, 0] m)
    else if k = 1 then dcKa p n (callW p n "erec_ci" [i, 0] m)
    else if k = 5 then dcKq p n i (callW p n "erec_ci" [i, 0] m)
    else if k = 6 then dcKi p n i (callW p n "ind_block_to_erec" [i] m)
    else none

/-- `decl_tables`, after `block_shape`. -/
def dtK3 (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then some ([0, 0], m)
      else bfgK4 (callW p n "block_tables" [r.tail.headD 0, rdW (m.arr64 IW) (r.tail.headD 0),
        rdW (m.arr64 IW) (r.tail.headD 0 + 1)] m)

/-- `decl_tables`, after `basis_name_hit`. -/
def dtK2 (p : Prog) (n : Nat) (i bo bl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0
      then dtK3 p n (callW p n "block_shape" [rdW (m.arr64 DECL) (5 + 8 * i), bo, bl] m)
      else some ([0, 0], m)

/-- `decl_tables`, after `ind_block_to_erec`. -/
def dtK1 (p : Prog) (n : Nat) (i : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => dtK2 p n i (r.headD 0) (r.tail.headD 0)
      (callW p n "basis_name_hit" [r.headD 0, r.tail.headD 0] m)

/-- **The model of `decl_tables(i)`**. -/
def dtW (p : Prog) : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, i => if rdW (m.arr64 DECL) (1 + 8 * i) = 6
      then dtK1 p n i (callW p n "ind_block_to_erec" [i] m) else some ([0, 0], m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (q i bo bl nP : Word) (r : List Word)
theorem dcNew1_some : dcNew1 p n (some (r, m)) = bfgK4 (callW p n "sl_new1" [r.headD 0] m) := rfl
theorem daK2_some : daK2 p n q (some (r, m)) = if erRd m (q + 1) = r.headD 0 then some ([0, 0], m)
    else bfgK4 (callW p n "sl_new1" [q] m) := rfl
theorem daK1_some : daK1 p n q (some (r, m)) =
    if erRd m (q + 1) = r.headD 0 then dcNew1 p n (callW p n "quot_at" [4, q + 1] m)
    else daK2 p n q (callW p n "pin_at" [13] m) := rfl
theorem daW_succ : daW p (n + 1) m q = daK1 p n q (callW p n "pin_at" [4] m) := rfl
theorem diK2_some : diK2 p n (some (r, m)) = if r.headD 0 = 0 then some ([0, 0], m)
    else bfgK4 (callW p n "block_constants" [r.tail.headD 0] m) := rfl
theorem diK1_some : diK1 p n bo bl nP (some (r, m)) =
    if r.headD 0 = 0 then diK2 p n (callW p n "block_shape" [nP, bo, bl] m)
    else bfgK4 (callW p n "basis_at_block" [r.tail.headD 0, bo, bl] m) := rfl
theorem diW_succ : diW p (n + 1) m bo bl nP = diK1 p n bo bl nP (callW p n "basis_name_hit" [bo, bl] m) := rfl
theorem dcKq_some : dcKq p n i (some (r, m)) =
    dcNew1 p n (callW p n "quot_at" [qSlot (rdW (m.arr64 DECL) (7 + 8 * i)), r.headD 0 + 1] m) := rfl
theorem dcKa_some : dcKa p n (some (r, m)) = bfgK4 (callW p n "decl_constants_axiom" [r.headD 0] m) := rfl
theorem dcKi_some : dcKi p n i (some (r, m)) = bfgK4 (callW p n "decl_constants_ind"
      [r.headD 0, r.tail.headD 0, rdW (m.arr64 DECL) (5 + 8 * i)] m) := rfl
theorem dtK3_some : dtK3 p n (some (r, m)) = if r.headD 0 = 0 then some ([0, 0], m)
      else bfgK4 (callW p n "block_tables" [r.tail.headD 0, rdW (m.arr64 IW) (r.tail.headD 0),
        rdW (m.arr64 IW) (r.tail.headD 0 + 1)] m) := rfl
theorem dtK2_some : dtK2 p n i bo bl (some (r, m)) = if r.headD 0 = 0
      then dtK3 p n (callW p n "block_shape" [rdW (m.arr64 DECL) (5 + 8 * i), bo, bl] m)
      else some ([0, 0], m) := rfl
theorem dtK1_some : dtK1 p n i (some (r, m)) = dtK2 p n i (r.headD 0) (r.tail.headD 0)
      (callW p n "basis_name_hit" [r.headD 0, r.tail.headD 0] m) := rfl
theorem dtW_succ : dtW p (n + 1) m i = if rdW (m.arr64 DECL) (1 + 8 * i) = 6
      then dtK1 p n i (callW p n "ind_block_to_erec" [i] m) else some ([0, 0], m) := rfl
end arms
attribute [ind_grind] dcNew1_some daK2_some daK1_some daW_succ diK2_some diK1_some diW_succ dcKq_some
  dcKa_some dcKi_some dtK3_some dtK2_some dtK1_some dtW_succ

/-! ## The specs -/

theorem da_spec (p : Prog) (hp : p.lookup "decl_constants_axiom" = some declConstantsAxiom) (n : Nat)
    (s₀ : St) (q : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "decl_constants_axiom" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ daW p n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, declConstantsAxiom]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "pin_at", callW_spec p n "quot_at", callW_spec p n "sl_new1"] <;>
      finish (gen := 20) [erRd, rdW_eq]

theorem di_spec (p : Prog) (hp : p.lookup "decl_constants_ind" = some declConstantsInd) (n : Nat)
    (s₀ : St) (bo bl nP : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "decl_constants_ind" [bo, bl, nP]
    ⦃fun r s' => LocEq s' s₀ ∧ diW p n s₀.mem bo bl nP = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, declConstantsInd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "basis_name_hit", callW_spec p n "basis_at_block",
        callW_spec p n "block_shape", callW_spec p n "block_constants"] <;>
      finish (gen := 20) [rdW_eq]

theorem dcon_spec (p : Prog) (hp : p.lookup "decl_constants" = some declConstants) (n : Nat)
    (s₀ : St) (i : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "decl_constants" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ dconW p n s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, declConstants]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "erec_ci", callW_spec p n "sl_new1", callW_spec p n "decl_constants_axiom",
        callW_spec p n "quot_at", callW_spec p n "ind_block_to_erec",
        callW_spec p n "decl_constants_ind"] <;>
      finish (gen := 20) [dconW, qSlot, rdW_eq]

theorem dt_spec (p : Prog) (hp : p.lookup "decl_tables" = some declTables) (n : Nat)
    (s₀ : St) (i : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "decl_tables" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ dtW p n s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, declTables]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "ind_block_to_erec", callW_spec p n "basis_name_hit",
        callW_spec p n "block_shape", callW_spec p n "block_tables"] <;>
      finish (gen := 20) [rdW_eq]

end L.Ind

end
