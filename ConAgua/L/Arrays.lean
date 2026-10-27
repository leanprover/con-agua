module

public import ConAgua.L.Syntax
public meta import Lean

public section

/-!
# Array tables: names, kinds and tiers of a program's arrays

The core (`Syntax`, the semantics, the compiler) names an array by a number, `ArrId := Nat`, so
that two arrays are distinct by `decide`. This file is the layer above it that a program's
arrays are declared in:

* **A table** (`ArrTable`) lists every array with its name, its number, its kind (byte or word;
  the two kinds are separate number spaces) and whether it is **tiered** (word arrays only: tier
  `t` of array `a` is the array `tierA a t`, §"Tiers" below). `declare_arrays` declares the
  arrays as Lean constants and the table from one list of rows, so each number is written once.
  `ArrTable.wf` checks that the numbers are distinct within a kind and below `tierOff`, so no
  array is another one's tier 1.
* **The surface check** (`ArrTable.progOK`) reads a program's text: a byte access names a byte
  array of the table, a tiered access (`A⟨t⟩[i]`) a tiered array, and a plain word access a word
  array of the table, so never a tier-1 number. A function on the exemption list may name any word
  slot below the table's extent (a capacity check that walks every slot by number).
* **Tiers.** Proofs name tier 1 of `a` as `tier1 a` and both tiers as `tiers a`, and reason with
  the lemmas below (`tierA_mem_tiers`, `tierA_ne`, `tier1_ne`, …) instead of the encoding.
-/

namespace L

/-! ## Tiers -/

/-- Tier `1` of the tiered array `a`. -/
@[expose, reducible] def tier1 (a : ArrId) : ArrId := a + tierOff

/-- The two tiers of the tiered array `a`. -/
@[expose, reducible] def tiers (a : ArrId) : List ArrId := [a, tier1 a]

theorem and_one_cases' (t : Word) : (t &&& 1).toNat = 0 ∨ (t &&& 1).toNat = 1 := by
  rw [UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]; omega

@[simp] theorem tierA_zero (a : ArrId) : tierA a 0 = a := rfl

theorem tierA_one_eq (a : ArrId) : tierA a 1 = tier1 a := rfl

/-- Tier `t` of `a` is `a` or `tier1 a`. -/
theorem tierA_eq_or (a : ArrId) (t : Word) : tierA a t = a ∨ tierA a t = tier1 a := by
  rcases and_one_cases' t with h | h <;> simp [tierA, tier1, h]

/-- **The arrays `tierA a t` can be are `tiers a`.** -/
theorem tierA_mem_tiers (a : ArrId) (t : Word) : tierA a t ∈ tiers a := by
  rcases tierA_eq_or a t with h | h <;> simp [tiers, h]

/-- An array that is neither tier of `a` is not `tierA a t`. -/
theorem tierA_ne {a b : ArrId} (h : b ∉ tiers a) (t : Word) : tierA a t ≠ b := fun e =>
  h (e ▸ tierA_mem_tiers a t)

theorem ne_tierA {a b : ArrId} (h : b ∉ tiers a) (t : Word) : b ≠ tierA a t := fun e =>
  tierA_ne h t e.symm

theorem not_mem_tiers {a b : ArrId} : b ∉ tiers a ↔ b ≠ a ∧ b ≠ tier1 a := by
  simp [tiers]

/-- `simp` evaluates `tier1 n` for a numeral `n` (pre-order, before `tier1 0` could be rewritten
as `0 + tierOff`): a concrete tier-1 array reads as its number, so `simp` decides
`tier1 REC ≠ CTL` once the names are unfolded, as it does `2 ≠ 1`. The value is `n + 256`, the
encoding (`tierOff`); the result is checked by definitional unfolding (the examples below). -/
simproc ↓ [simp] reduceTier1 (tier1 _) := fun e => do
  let_expr tier1 a ← e | return .continue
  let some n := a.rawNatLit? <|> a.nat? | return .continue
  return .done { expr := Lean.mkNatLit (n + 256) }

example : tier1 2 = 258 := by simp
example : tier1 0 ≠ 1 := by simp

/-! The proofs below see the encoding (`tier1 a = a + 256`) through `show` with `Nat` binders:
`omega` does not read a comparison at type `ArrId`. -/

/-- Tier 1 of an array is no array below `tierOff`. -/
theorem tier1_ne {a b : Nat} (hb : b < tierOff) : tier1 a ≠ b := by
  have h1 : b < 256 := hb
  show ¬ (a + 256 = b); omega

theorem ne_tier1 {a b : Nat} (hb : b < tierOff) : b ≠ tier1 a := fun e => tier1_ne hb e.symm

theorem tier1_inj {a b : Nat} (h : tier1 a = tier1 b) : a = b := by
  have h2 : a + 256 = b + 256 := h
  omega

/-- Distinct arrays below `tierOff` have disjoint tiers. -/
theorem not_mem_tiers_of_lt {a b : ArrId} (ha : a < tierOff) (hb : b < tierOff) (h : b ≠ a) :
    b ∉ tiers a ∧ tier1 b ∉ tiers a := by
  refine ⟨not_mem_tiers.2 ⟨h, ne_tier1 hb⟩, not_mem_tiers.2 ⟨tier1_ne ha, fun e => h (tier1_inj e)⟩⟩

/-- On arrays below `tierOff`, the tiers of distinct arrays are distinct. -/
theorem tierA_ne_tierA {a b : ArrId} (ha : a < tierOff) (hb : b < tierOff) (h : a ≠ b)
    (t u : Word) : tierA a t ≠ tierA b u := by
  rcases tierA_eq_or b u with e | e <;> rw [e]
  · exact tierA_ne (not_mem_tiers_of_lt ha hb (Ne.symm h)).1 t
  · exact tierA_ne (not_mem_tiers_of_lt ha hb (Ne.symm h)).2 t

/-- The tiers of `a < n` are below `tierOff + n`. -/
theorem tierA_lt {a n : Nat} (h : a < n) (t : Word) : tierA a t < tierOff + n := by
  rcases tierA_eq_or a t with e | e <;> rw [e]
  · show a < 256 + n; omega
  · show a + 256 < 256 + n; omega

/-! ## Tables -/

/-- The kind of an array: bytes or words (two separate number spaces). -/
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
  deriving Repr, DecidableEq, Inhabited

/-- A program's arrays. -/
abbrev ArrTable := List ArrDecl

namespace ArrTable

/-- The numbers of the arrays of kind `k`. -/
def ids (T : ArrTable) (k : ArrKind) : List ArrId := (T.filter (·.kind == k)).map (·.id)

/-- The tiered arrays' numbers. -/
def tieredIds (T : ArrTable) : List ArrId := (T.filter (·.tiered)).map (·.id)

/-- The word slots the table occupies: every word array and the tier-1 array of every tiered
one. -/
def wordSlots (T : ArrTable) : List ArrId := T.ids .word ++ T.tieredIds.map tier1

/-- `l` has no duplicates (a `Bool` check: sorted, then neighbours; `List.Nodup`'s instance is
slow under `decide`). -/
def nodupB (l : List Nat) : Bool :=
  let s := l.mergeSort
  (s.zip s.tail).all fun (x, y) => x != y

/-- **Well-formed**: every number below `tierOff`, the numbers of each kind distinct, only word
arrays tiered. -/
def wf (T : ArrTable) : Bool :=
  T.all (fun d => d.id < tierOff && (d.tiered → d.kind == .word)) &&
    nodupB (T.ids .byte) && nodupB (T.ids .word)

/-- The table's extent `(nb, nw)`: one more than the largest byte array and word slot (the
compiler's `Prog.arrs` of a program that names them all). -/
def extent (T : ArrTable) : Nat × Nat :=
  ((T.ids .byte).foldl (fun m a => max m (a + 1)) 0, T.wordSlots.foldl (fun m a => max m (a + 1)) 0)

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

/-- Whether an exempt function may use the operand: any word slot below the table's extent
(the slots between the arrays included), else as `useOK`. -/
def slotOK (T : ArrTable) : Use → Bool
  | .byte a => T.ids .byte |>.contains a
  | .word a => a < T.extent.2
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

end Uses

/-- **The surface check**: every array operand of every function of `p` is allowed by `T`
(`useOK`); a function in `exempt` may name any word slot below `T`'s extent (`slotOK`). -/
def ArrTable.progOK (T : ArrTable) (exempt : List FnName) (p : Prog) : Bool :=
  p.all fun (f, fd) =>
    if exempt.contains f then (Uses.stmt fd.body).all T.slotOK
    else (Uses.stmt fd.body).all T.useOK

/-! ## `declare_arrays` -/

/-- One row of `declare_arrays`: `| /-- doc -/ NAME : byte := n`, `| … NAME : word := n`, or
`| … NAME : word tiered := n`. -/
syntax arrRow := "| " docComment ident " : " ident (&" tiered")? " := " num

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
      | `(arrRow| | $doc:docComment $n:ident : $k:ident $[tiered%$t]? := $v:num) =>
        cmds := cmds.push (← `($doc:docComment abbrev $n : L.ArrId := $v))
        let nm := Lean.Syntax.mkStrLit n.getId.getString!
        let kind ← match k.getId with
          | `byte => `(L.ArrKind.byte)
          | `word => `(L.ArrKind.word)
          | _ => Lean.Macro.throwErrorAt k "expected `byte` or `word`"
        let tiered ← if t.isSome then `(true) else `(false)
        rowsT := rowsT.push (← `(({ name := $nm, id := $n, kind := $kind, tiered := $tiered } : L.ArrDecl)))
      | _ => Lean.Macro.throwUnsupported
    let tdef ← match tdoc with
      | some d => `($d:docComment def $tbl : L.ArrTable := [$rowsT,*])
      | none => `(def $tbl : L.ArrTable := [$rowsT,*])
    cmds := cmds.push tdef
    return Lean.mkNullNode (cmds.map (·.raw))

end L
