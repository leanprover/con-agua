module

public import ConAgua.Arena.Store
public import ConAgua.Arena.LpCol
public import ConAgua.Arena.ConsLibSpec
meta import ConAgua.Arena.LpCol
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.ConsLib
import ConAgua.Census.Attr

@[expose] public section

/-!
# The `const` node store in L: an expression store with a two-field, mixed-kind key

The arena's `const` constructor is a `Tbl ConstNode EIdx UInt64` per tier, `ConstNode { n : NIdx,
us : LsIdx }` (`Arena/Store.lean:278`): a name handle and a level-list handle (both just words in
L; the variable names below are `f`/`a`, the `app` store's, standing for `n`/`us` here — the two
handle words of the key, of whichever kind). Its L representation follows `app`'s exactly, the
same width-2, scratch-skipping shape:

* **Records.** Word array `CREC`, two words per node (the handle words of `n` and `us`), tiers
  interleaved: node `i` of tier `t` at `CREC[4 i + 2 t ..]`. No stored hash: the hash is a
  cheap function of the two words. The node count of tier `t` is `CTL[18 + t]`.
* **Cons table.** Word array `CSLOT`, the cons-table library's layout (`ConsLib.lean`): one table
  per tier, the key word the key itself (an exact table), linear probing from `homeW`.
* **The scratch skip.** `internE (.const n us)` does not probe the persistent tier when the
  scratch tier is open and a child is a scratch handle (`EStore.persFindMaybe`,
  `eViewHasScratchChild`): bit 27 of `n | us`.

The functions: `const_find(t, n, us, h)` (the probe, the match inline: two word comparisons),
`const_push(t, n, us, j)` and `intern_const(n, us)`. They are the cons-table library's templates
(`ConsLib.lean`) at the schema `constCS`, the derived column written by the template's prelude;
their specs are the library's (`ConsLibSpec.lean`) from this table's obligations.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `const` records, both tiers interleaved (two words per node). -/
abbrev CREC : ArrId := 18
/-- The `const` cons-table slots, both tiers interleaved. -/
abbrev CSLOT : ArrId := 19

/-- The hash of a `const` record (FNV-1a over its two words). -/
def constHashW (f a : Word) : Word := ((fnvBasis ^^^ f) * fnvPrime ^^^ a) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(f, a)`. -/
def cematchW (r : Array Word) (t i f a : Word) : Bool :=
  rdW r (i * 4 + t * 2) == f && rdW r (i * 4 + t * 2 + 1) == a

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `const` tier (tag `3`). -/
def constP : Word := 0x30000000
def constS : Word := 0x38000000

/-- The hash of node `i` of tier `t`. -/
def cehash (m : Mem) (t i : Word) : Word :=
  constHashW (rdW (m.arr64 CREC) (i * 4 + t * 2)) (rdW (m.arr64 CREC) (i * 4 + t * 2 + 1))

/-- The `const` table as a cons schema (`ConsLib.lean`); the derived column `CLP`
(the level list's `hasParam` bit, `lsBlkC`). -/
def constCS : ConsSch where
  ra := CREC
  sa := CSLOT
  w := 2
  st := 4
  ca := 18
  P := constP
  S := constS
  tag := 3
  fname := "const_find"
  pname := "const_push"
  nk := 2
  exact := true
  mc := condOf (lblk (t, f, a, h, n, j, d, v, b) {
    if CREC⟨t⟩[(v - 1) * 2] == f && CREC⟨t⟩[(v - 1) * 2 + 1] == a { skip } })
  np := 2
  room := condOf (lblk (t, f, a, j, c) {
    if len(CREC⟨t⟩) >> 1 <= c || len(CLP⟨t⟩) <= c { skip } })
  recW := [.var 1, .var 2]
  ihash := lblk (f, a, h) { h := ((⟪fnvBasis⟫ ^ f) * ⟪fnvPrime⟫ ^ a) * ⟪fnvPrime⟫ }
  skipW := some (rhsOf (lblk (f, a, h, sk) { sk := ((f | a) >> 27) & 1 }))
  xloc := 4
  pre := some lsBlkC
  col := some CLP
  colM m as := lsHPW m (as.getD 1 0)
  mtM m ks t i := cematchW (m.arr64 CREC) t i (ks.getD 0 0) (ks.getD 1 0)
  qhM _ ks := constHashW (ks.getD 0 0) (ks.getD 1 0)
  hsM := cehash
  vsM as := as
  roomM m _ c := decide (m.len64 CREC >>> (2 : Word) ≤ c) || decide (m.len64 CLP >>> (1 : Word) ≤ c)
  skM ks := ((ks.getD 0 0 ||| ks.getD 1 0) >>> 27) &&& 1

/-! ## `const_find(t, n, us, h)`: the probe -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def constFind : FunDecl := consFindG constCS

/-! ## `const_push(t, n, us, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `const` table, `CTL[18 + t]`. -/
def cecnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (18 + t)

/-- `const_push`'s room checks: the handle index, the record array. -/
def cepushOK (m : Mem) (t : Word) : Bool :=
  decide (cecnt m t < (134217728 : Word)) && decide (cecnt m t < m.len64 CREC >>> (2 : Word)) &&
    decide (cecnt m t < m.len64 CLP >>> (1 : Word))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def constPush : FunDecl := consPushG constCS

/-! ## `intern_const(n, us)`: hash-cons the `const` node with children `n` and `us`

con-ron's `EStore::intern` at `const` and the arena's `internE (.const n us)`: the persistent
probe unless the scratch tier is open and a child is a scratch handle, the scratch probe if the
scratch tier is open, the append to the tier the store is in. -/

/-- The scratch skip: the scratch tier is open and `f` or `a` is a scratch handle. -/
def ceskipW (m : Mem) (f a : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then ((f ||| a) >>> 27) &&& 1 else 0

/-- The model of `intern_const`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def ceinternW (m : Mem) (f a : Word) : Option (Word × Mem) := consInternM constCS m [f, a]

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internConst : FunDecl := consInternG constCS

/-- The `const` store functions, as one `#eval`-able program. -/
def constProg : Prog :=
  [("const_find", constFind), ("const_push", constPush), ("intern_const", internConst)]

/-- A memory with 8 `const` nodes and `SN0` slots per tier, the scratch tier closed or open.
Arrays 0‥17 (the other tables') are unused here and left empty. -/
def constMem (scratch : Word) : Mem :=
  { words := withTiers <| #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[],
      #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[],
      Array.replicate consTestWords 0, Array.replicate consTestWords 0] ++ Array.replicate 62 (Array.replicate consTestWords 0) }

/-- Intern each pair in turn; the handles. -/
def internConsts (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (f, a) :: xs => match run constProg 100 "intern_const" [f, a] m with
    | .ok (r, m') => (internConsts m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2)`, `(2, 1)`, `(1, 2)`: persistent handles 0, 1, 0. -/
#guard internConsts (constMem 0) [(1, 2), (2, 1), (1, 2)] == some [0x30000000, 0x30000001, 0x30000000]

/- Scratch open: persistent children are probed in the persistent tier (empty), the nodes go to
the scratch tier; a scratch child (`0x38000000`) skips the persistent probe. -/
#guard internConsts (constMem 1) [(1, 2), (0x38000000, 1), (1, 2), (0x38000000, 1)] ==
  some [0x38000000, 0x38000001, 0x38000000, 0x38000001]

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

/-- **The `const` table's obligations.** -/
theorem constOK : ConsOK p constCS := by sorry

theorem cepushOK_eqC (m : Mem) (t : Word) : cepushOK m t = pushOKC constCS m t := by
  simp only [cepushOK, pushOKC, constCS, Bool.not_or, ← decide_not, UInt64.not_le, Bool.and_assoc]
  rfl

theorem internConst_spec (hpf : p.lookup "const_find" = some constFind)
    (hpp : p.lookup "const_push" = some constPush) (hp : p.lookup "intern_const" = some internConst)
    (n : Nat) (s₀ : St) (f a : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_const" [f, a]
    ⦃fun r s' => LocEq s' s₀ ∧ ceinternW s₀.mem f a = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p constCS (constOK p) hpf hpp "intern_const" hp n s₀ [f, a] rfl trivial

end specs

end L.Arena
