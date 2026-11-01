module

public import ConAgua.L.Syntax
public meta import Lean

@[expose] public section

/-!
# Array tables: names, kinds and tiers of a program's arrays

The syntax names an array by a number, `ArrId := Nat`, so that two arrays are distinct by
`decide`; the semantics names a word array by its number and tier (`TieredArray`). The numbers
are names, not addresses: where an array lives is the compiler's choice. This file is the layer
above the syntax that a program's arrays are declared in:

* **A table** (`ArrTable`) lists every array with its name, its number, its kind (byte or word;
  one name space for both kinds) and whether it is **tiered** (word arrays only: tier
  `t` of array `a` is the array `tierA a t`, §"Tiers" below). `declare_arrays` declares the
  arrays as Lean constants and the table from one list of rows, so each number is written once.
  `ArrTable.wf` checks that the numbers are distinct.
* **The surface check** (`ArrTable.progOK`) reads a program's text: a byte access names a byte
  array of the table, a tiered access (`A⟨t⟩[i]`) a tiered array, and a plain word access a word
  array of the table.
* **Tiers.** Proofs name tier 1 of `a` as `tier1 a` and both tiers as `tiers a`, and reason with
  the lemmas below and in `L/Syntax.lean` (`tierA_mem_tiers`, `tierA_ne`, `tier1_ne_t0`, …).
-/

namespace L

/-! ## Tiers

`TieredArray`, `tier1`, `tiers` and `tierA` are defined with the syntax (`L/Syntax.lean`). -/

theorem and_one_cases' (t : Word) : (t &&& 1).toNat = 0 ∨ (t &&& 1).toNat = 1 := by
  rw [UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]; omega

@[simp] theorem tierA_zero (a : ArrId) : tierA a 0 = ↑a := rfl

theorem tierA_one_eq (a : ArrId) : tierA a 1 = tier1 a := rfl

/-- An array that is neither tier of `a` is not `tierA a t`. -/
theorem tierA_ne {a : ArrId} {b : TieredArray} (h : b ∉ tiers a) (t : Word) : tierA a t ≠ b :=
  fun e => h (e ▸ tierA_mem_tiers a t)

theorem ne_tierA {a : ArrId} {b : TieredArray} (h : b ∉ tiers a) (t : Word) : b ≠ tierA a t :=
  fun e => tierA_ne h t e.symm

theorem not_mem_tiers {a : ArrId} {b : TieredArray} : b ∉ tiers a ↔ b ≠ ↑a ∧ b ≠ tier1 a := by
  simp [tiers]

/-- Distinct arrays have disjoint tiers. -/
theorem not_mem_tiers_of_ne {a b : ArrId} (h : b ≠ a) :
    (b : TieredArray) ∉ tiers a ∧ tier1 b ∉ tiers a := by
  simp [tiers, h]

/-- The tiers of distinct arrays are distinct. -/
theorem tierA_ne_tierA {a b : ArrId} (h : a ≠ b) (t u : Word) : tierA a t ≠ tierA b u := by
  intro e; exact h (by simpa using congrArg TieredArray.arr e)

/-! ### Tier-1 arrays by range

Frame lemmas name sets of tier-1 arrays by these predicates. They are `@[simp] abbrev`s, so
`decide` and `simp` read them. -/

/-- `b` is a tier-1 array: `tier1 a` for some `a` (`IsTier1.tier1`). -/
@[simp] abbrev IsTier1 (b : TieredArray) : Prop := b.hi = true

/-- `b` is the tier-1 array of an array numbered in `[lo, hi)`: `tier1 a` with `lo ≤ a < hi`
(`Tier1In.tier1`). -/
@[simp] abbrev Tier1In (lo hi : Nat) (b : TieredArray) : Prop := b.hi = true ∧ lo ≤ b.arr ∧ b.arr < hi

/-- `b` is the tier-0 array of an array numbered in `[lo, hi)`. -/
@[simp] abbrev Tier0In (lo hi : Nat) (b : TieredArray) : Prop := b.hi = false ∧ lo ≤ b.arr ∧ b.arr < hi

theorem IsTier1.tier1 (a : Nat) : IsTier1 (tier1 a) := rfl

theorem Tier1In.tier1 {lo hi a : Nat} (h1 : lo ≤ a) (h2 : a < hi) : Tier1In lo hi (tier1 a) :=
  ⟨rfl, h1, h2⟩

/-- Tier 0 of each array of `l`, and tier 1 of each: lists of word arrays written by their
names. (A long list literal mixing `ArrId`s and `TieredArray`s does not elaborate: Lean
elaborates it in pieces, without the expected element type.) -/
abbrev tier0s (l : List ArrId) : List TieredArray := l.map TieredArray.t0
@[inherit_doc tier0s] abbrev tier1s (l : List ArrId) : List TieredArray := l.map tier1

/-! ## Tables -/

/-- The kind of an array: bytes or words (one name space: a number names one array). -/
inductive ArrKind where
  | byte
  | word
  deriving Repr, DecidableEq, Inhabited

/-- One array: its name, number, kind, and whether it is tiered (a word array with a tier-1
array `tier1 id`). -/
structure ArrDecl where
  name : String
  id : ArrId
  kind : ArrKind
  tiered : Bool
  /-- A minimum length in words (a hint for the compiler, word arrays only): every entry stub
  gives the array at least this many words (both tiers), so a constant index below it needs no
  bounds check in the machine code. L's semantics still checks every access. -/
  min : Nat := 0
  /-- Table-relative (a hint for the compiler, `at table`): the array lives at a fixed offset inside
  the descriptor table's region, with exactly `min` words, and the code addresses it from the
  table's register without loading its base. A word array, not tiered, with a minimum length. -/
  atTable : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- A program's arrays. -/
abbrev ArrTable := List ArrDecl

namespace ArrTable

/-- The numbers of the arrays of kind `k`. -/
def ids (T : ArrTable) (k : ArrKind) : List ArrId := (T.filter (·.kind == k)).map (·.id)

/-- The tiered arrays' numbers. -/
def tieredIds (T : ArrTable) : List ArrId := (T.filter (·.tiered)).map (·.id)

/-- The word arrays of the table: every word array (its tier 0) and the tier-1 array of every
tiered one. -/
def wordSlots (T : ArrTable) : List TieredArray :=
  (T.ids .word).map TieredArray.t0 ++ T.tieredIds.map tier1

/-- `l` has no duplicates (a `Bool` check: sorted, then neighbours; `List.Nodup`'s instance is
slow under `decide`). -/
def nodupB (l : List Nat) : Bool :=
  let s := l.mergeSort
  (s.zip s.tail).all fun (x, y) => x != y

/-- The word arrays with a minimum length (`ArrDecl.min`), as `(code, minimum)`
(`TieredArray.code`): tier 0 of the array, and tier 1 of a tiered one. -/
def mins (T : ArrTable) : List (Nat × Nat) :=
  (T.filter fun d => d.kind == .word && d.min != 0).flatMap fun d =>
    ((TieredArray.t0 d.id).code :: if d.tiered then [(tier1 d.id).code] else []).map fun c => (c, d.min)

/-- The table-relative array (`ArrDecl.atTable`), if there is one, with its length. -/
def tblArr (T : ArrTable) : Option (ArrId × Nat) :=
  (T.find? (·.atTable)).map fun d => (d.id, d.min)

/-- **Well-formed**: the numbers distinct (one name space for both kinds), only word arrays tiered or with a
minimum length; at most one table-relative array, a word array with a minimum length (its
length), not tiered. -/
def wf (T : ArrTable) : Bool :=
  T.all (fun d => d.tiered → d.kind == .word) && T.all (fun d => d.min != 0 → d.kind == .word) &&
    T.all (fun d => d.atTable → d.kind == .word && !d.tiered && d.min != 0) &&
    decide ((T.filter (·.atTable)).length ≤ 1) &&
    nodupB (T.map (·.id))

/-! ### The surface check -/

/-- One array operand of a program: a byte array, a plain word access, a tiered access. -/
inductive Use where
  | byte (a : ArrId)
  | word (a : ArrId)
  | tier (a : ArrId)
  deriving Repr, DecidableEq

/-- Whether `T` allows the operand: a byte array of `T`; a word array of `T` (by its tier-0
number); a tiered array of `T`. -/
def useOK (T : ArrTable) : Use → Bool
  | .byte a => T.ids .byte |>.contains a
  | .word a => T.ids .word |>.contains a
  | .tier a => T.tieredIds.contains a

end ArrTable

/-! ### Array operands of a program's text -/

namespace Uses
open ArrTable (Use)

def bsrc : BSrc → List Use
  | .arr a => [.byte a]
  | .rom _ => []

def warr : WArr → List Use
  | .plain a => [.word a]
  | .tier a _ => [.tier a]

def expr : Expr → List Use
  | .const _ | .var _ | .glob _ => []
  | .bin _ a b | .cmpw _ a b => expr a ++ expr b
  | .ld8 a i => .byte a :: expr i
  | .len8 a => [.byte a]
  | .ldc _ i => expr i
  | .ld8x8 s i => bsrc s ++ expr i
  | .ld64 a i => .word a :: expr i
  | .len64 a => [.word a]
  | .ld64t a t i => .tier a :: (expr t ++ expr i)
  | .len64t a t => .tier a :: expr t
  | .ld32t a t i => (if t = .const 0 then .word a else .tier a) :: (expr t ++ expr i)
  | .ld32h a t i _ => .tier a :: (expr t ++ expr i)

def cond : Cond → List Use
  | .cmp _ a b => expr a ++ expr b
  | .and p q | .or p q => cond p ++ cond q
  | .not p => cond p

/-- The tier word of a block operand. -/
def warrT : WArr → List Use
  | .plain _ => []
  | .tier _ t => expr t

def exprs : List Expr → List Use
  | [] => []
  | e :: es => expr e ++ exprs es

def stmt : Stmt → List Use
  | .skip | .brk => []
  | .set _ e | .gset _ e | .abort e => expr e
  | .st8 a i e => .byte a :: (expr i ++ expr e)
  | .st64 a i e => .word a :: (expr i ++ expr e)
  | .st64t a t i e => .tier a :: (expr t ++ expr i ++ expr e)
  | .seq s t => stmt s ++ stmt t
  | .ite c s t => cond c ++ stmt s ++ stmt t
  | .while c s => cond c ++ stmt s
  | .ret es | .call _ _ es => exprs es
  | .copy64 d di s si n => warr d ++ warrT d ++ warr s ++ warrT s ++ expr di ++ expr si ++ expr n
  | .copy8w d di s si n => warr d ++ warrT d ++ bsrc s ++ expr di ++ expr si ++ expr n
  | .scan8 _ s i e _ => bsrc s ++ expr i ++ expr e
  | .st32t a t i e => (if t = .const 0 then .word a else .tier a) :: (expr t ++ expr i ++ expr e)

end Uses

/-- **The surface check**: every array operand of every function of `p` is allowed by `T`
(`useOK`). -/
def ArrTable.progOK (T : ArrTable) (p : Prog) : Bool :=
  p.all fun (_, fd) => (Uses.stmt fd.body).all T.useOK

/-! ## `declare_arrays` -/

/-- The table-relative hint of a row, `at table` (`ArrDecl.atTable`). -/
syntax atTableHint := &" at" &" table"

/-- One row of `declare_arrays`: `| /-- doc -/ NAME : byte := n`, `| … NAME : word := n`, or
`| … NAME : word tiered := n`; a word array may carry a minimum length, `… : word min k := n`
(`ArrDecl.min`), and such an array may be table-relative, `… : word min k at table := n`
(`ArrDecl.atTable`). -/
syntax arrRow := "| " docComment ident " : " ident (&" tiered")? (&" min" num)? (atTableHint)?
  " := " num

/-- `declare_arrays T` followed by rows declares each row's array as `abbrev NAME : L.ArrId := n`
(with the row's doc comment) and `T : L.ArrTable` listing them all, so each number is written
once. -/
syntax (docComment)? "declare_arrays " ident (ppLine arrRow)* : command

macro_rules
  | `($[$tdoc:docComment]? declare_arrays $tbl:ident $rows:arrRow*) => do
    let mut cmds : Array Lean.Syntax.Command := #[]
    let mut rowsT : Array Lean.Term := #[]
    for r in rows do
      match r with
      | `(arrRow| | $doc:docComment $n:ident : $k:ident $[tiered%$t]? $[min $mn:num]? $[$ath:atTableHint]? := $v:num) =>
        cmds := cmds.push (← `($doc:docComment abbrev $n : L.ArrId := $v))
        let nm := Lean.Syntax.mkStrLit n.getId.getString!
        let kind ← match k.getId with
          | `byte => `(L.ArrKind.byte)
          | `word => `(L.ArrKind.word)
          | _ => Lean.Macro.throwErrorAt k "expected `byte` or `word`"
        let tiered ← if t.isSome then `(true) else `(false)
        let mn : Lean.Term := match mn with
          | some m => m
          | none => Lean.Syntax.mkNumLit "0"
        let atT ← if ath.isSome then `(true) else `(false)
        let row ← `(({ name := $nm, id := $n, kind := $kind, tiered := $tiered, min := $mn, atTable := $atT } : L.ArrDecl))
        rowsT := rowsT.push row
      | _ => Lean.Macro.throwUnsupported
    let tdef ← match tdoc with
      | some d => `($d:docComment def $tbl : L.ArrTable := [$rowsT,*])
      | none => `(def $tbl : L.ArrTable := [$rowsT,*])
    cmds := cmds.push tdef
    return Lean.mkNullNode (cmds.map (·.raw))

/-! ## Test memories -/

/-- Test memories: each entry `(a, xs)` of a list of named arrays (`Mem.ofWords`) also as the
entry for its tier-1 array, `[(a, xs), (tier1 a, xs)]`. Only the tiered arrays go through it. -/
def withTiers {α : Type} (l : List (ArrId × α)) : List (TieredArray × α) :=
  l.flatMap fun p => [(↑p.1, p.2), (tier1 p.1, p.2)]

/-- Test memories: every word array of `T` as a zero array of `size a` words, entries for
`Mem.ofWords` (a test overrides some by later entries). Tier 0 only; `zeroTiers` has the tier-1
arrays. -/
def ArrTable.zeroWords (T : ArrTable) (size : ArrId → Nat) : List (TieredArray × Array Word) :=
  (T.ids .word).map fun (a : ArrId) => (↑a, Array.replicate (size a) 0)

/-- The tier-1 array `tier1 a` of every tiered array `a` of `T` as a zero array of `size a` words. -/
def ArrTable.zeroTiers (T : ArrTable) (size : ArrId → Nat) : List (TieredArray × Array Word) :=
  T.tieredIds.map fun a => (tier1 a, Array.replicate (size a) 0)

/-- `zeroWords` and `zeroTiers`: both tiers of every array. -/
def ArrTable.zeroBoth (T : ArrTable) (size : ArrId → Nat) : List (TieredArray × Array Word) :=
  T.zeroWords size ++ T.zeroTiers size

end L
