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
* **Cons table.** Word array `CSLOT`, the same open addressing as `SLOT` (slot `j` of tier `t`
  at `CSLOT[2 j + t]`, `0` free, `i + 1` node `i`, linear probing from `homeW`).
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

/-- The growth schema of this table (`SlotGrow.lean`). -/
def constGS : GrowSch :=
  ⟨CSLOT, CREC, 2, 18, lblk (n, k, t, i, c, h) {
    h := ((⟪fnvBasis⟫ ^ CREC.u64[i * 4 + t * 2]) * ⟪fnvPrime⟫ ^ CREC.u64[i * 4 + t * 2 + 1]) * ⟪fnvPrime⟫
  }⟩

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
  mc := condOf (lblk (t, f, a, h, n, j, d, v, b) {
    if CREC.u64[(v - 1) * 4 + t * 2] == f && CREC.u64[(v - 1) * 4 + t * 2 + 1] == a { skip } })
  np := 2
  room := condOf (lblk (t, f, a, j, c) {
    if len(CREC.u64) >> 2 <= c || len(CLP.u64) >> 1 <= c { skip } })
  recW := [.var 1, .var 2]
  ghash := constGS.hash
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

/-- The model of the probe, from slot `j` after `d` steps (the library's `cprobeW`). -/
def ceprobeW (sl r : Array Word) (t f a b n j d : Word) : List Word :=
  cprobeW sl (fun i => cematchW r t i f a) t b n j d

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def constFind : FunDecl := consFindG constCS

/-- The slot count of a tier of the `const` table. -/
def nSlotsCe (m : Mem) : Word := rdW (m.arr64 CSLOT) (m.len64 CSLOT - 1) + SN0

/-! ## `const_push(t, n, us, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `const` table, `CTL[18 + t]`. -/
def cecnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (18 + t)

/-- `const_push`'s room checks: the handle index, the record array. -/
def cepushOK (m : Mem) (t : Word) : Bool :=
  decide (cecnt m t < (134217728 : Word)) && decide (cecnt m t < m.len64 CREC >>> (2 : Word)) &&
    decide (cecnt m t < m.len64 CLP >>> (1 : Word))

/-- The memory after `const_push(t, n, us, j)` appended node `c`. -/
def cepushMem (m : Mem) (t f a j c : Word) : Mem :=
  ((((m.set64 CREC (c * 4 + t * 2) f).set64 CREC (c * 4 + t * 2 + 1) a).set64 CSLOT (j * 2 + t)
    (baseW m t + c + 1)).set64 CTL (18 + (t &&& 1)) (c + 1)).set64 CLP (c * 2 + t) (lsHPW m a)

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

/-- A memory with 8 `const` nodes and 16 slots per tier, the scratch tier closed or open.
Arrays 0‥17 (the other tables') are unused here and left empty. -/
def constMem (scratch : Word) : Mem :=
  { words := #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[],
      #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[],
      Array.replicate 32 0, Array.replicate 32 0] ++ Array.replicate 62 (Array.replicate 32 0) }

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

/-- The growth's hash block computes `cehash`. -/
theorem cehash_ok : HashOK p constGS 10 cehash := by
  intro k s₀
  simp only [constGS, shiftS, shiftE, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalArgs, setLoc, ld64] <;> finish [cehash, constHashW, LocEq, St.setLoc]

/-- **The `const` table's obligations.** -/
theorem constOK : ConsOK p constCS where
  match_ := by
    intro s
    simp [constCS, condOf, Cond.pval, Expr.pval, cematchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ghash := cehash_ok p
  ihash := by
    intro n s₀
    simp only [constCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, constHashW, argsOf, BinOp.eval]
  pre := by
    intro n s₀
    vcgen [lsBlkC_spec p (exec p n) s₀]
    all_goals obtain ⟨h0, h1, h2, h3, -, -, hx⟩ := ‹_ ∧ _›
    · assumption
    · intro x hx'
      simp only [constCS] at hx'
      rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) with rfl | rfl | rfl | rfl <;> assumption
    · simp [constCS, argsOf, List.range_succ, hx]
  colA := by
    intro A h
    simp only [constCS, Option.some.injEq] at h
    subst h; decide
  recs := ⟨by
      intro e he s s' h
      simp only [constCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [constCS, argsOf, Expr.pval, List.range_succ]⟩
  room := fun s => by
    simp only [constCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval, BinOp.eval]; rfl
  skips := by
    intro e he s
    simp only [constCS, Option.some.injEq] at he
    subst he
    simp [constCS, rhsOf, L.Notation.blk, Expr.pval, argsOf, BinOp.eval, List.range_succ]
  push_np := by decide
  arrs := by decide

theorem constFind_spec (hp : p.lookup "const_find" = some constFind) (n : Nat) (s₀ : St)
    (t f a h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "const_find" [t, f, a, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = ceprobeW (s₀.mem.arr64 CSLOT) (s₀.mem.arr64 CREC) t f a
        (baseW s₀.mem t) (nSlotsCe s₀.mem) (homeW h (nSlotsCe s₀.mem)) 0; ⊤⦄ :=
  consFindG_spec p constCS ((constOK p).match_) hp n s₀ t [f, a] rfl h trivial

theorem cepushOK_eqC (m : Mem) (t : Word) : cepushOK m t = pushOKC constCS m t := by
  simp only [cepushOK, pushOKC, constCS, Bool.not_or, ← decide_not, UInt64.not_le, Bool.and_assoc]
  rfl

theorem cepushMem_eqC (m : Mem) (t f a j c : Word) :
    cepushMem m t f a j c = pushMX constCS m t [f, a] (lsHPW m a) j c := by
  simp [cepushMem, pushMX, colW, pushMC, tailM, wrRecK, constCS, baseW,
    Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ CREC by decide)]

theorem constPush_spec (hp : p.lookup "const_push" = some constPush) (n : Nat) (s₀ : St)
    (t f a j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "const_push" [t, f, a, j]
    ⦃fun r s' => LocEq s' s₀ ∧ cepushOK s₀.mem t = true ∧ r = [cecnt s₀.mem t] ∧
      growIf CSLOT 18 cehash s₀.mem (cepushMem s₀.mem t f a j (cecnt s₀.mem t))
        (cecnt s₀.mem t) = some s'.mem; ⊤⦄ := by
  rw [cepushOK_eqC]
  simp only [cepushMem_eqC]
  exact consPushG_spec p constCS (constOK p) hp n s₀ t [f, a] rfl j

theorem internConst_spec (hpf : p.lookup "const_find" = some constFind)
    (hpp : p.lookup "const_push" = some constPush) (hp : p.lookup "intern_const" = some internConst)
    (n : Nat) (s₀ : St) (f a : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_const" [f, a]
    ⦃fun r s' => LocEq s' s₀ ∧ ceinternW s₀.mem f a = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p constCS (constOK p) hpf hpp "intern_const" hp n s₀ [f, a] rfl trivial

end specs

end L.Arena
