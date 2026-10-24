module

public import ConAgua.Arena.ConsLibSpec
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.ConsLib
import ConAgua.Census.Attr

@[expose] public section

/-!
# The level `zero` node store in L: a table with no fields

The arena's level store keeps the single `zero` node in a `Tbl ZeroNode LIdx LDer` per tier
(`Arena/Store.lean:159`, `LTables.zeros`). `ZeroNode` has no fields (`mk ::`), so there is at
most one node per tier and the cons key never distinguishes two nodes: the match function is the
constant `true` (**any** node that is there is the `zero` node). Following the schema library's
recommendation for a fieldless constructor, this uses a one-word dummy record (`w = 0` is excluded
by `Schema.WF`'s shape; a genuine `w = 0` schema would also collide every node's address, which a
dummy field avoids needing to reason about).

* **Records.** Word array `ZREC`, one (unused) word per node, tiers interleaved: node `i` of tier
  `t` at `ZREC[2 i + t]`. The node count of tier `t` is `CTL[8 + t]`.
* **Cons table.** Word array `ZSLOT`, the same open addressing as `SLOT`/`SSLOT`.

The functions `zero_find(t, h)`, `zero_push(t, j)` and `intern_zero()` are the
cons-table library's templates (`ConsLib.lean`) at the schema `zeroCS` (no scratch skip); their
specs are the library's (`ConsLibSpec.lean`) from this table's obligations (`zeroOK`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `zero` records, both tiers interleaved (one dummy word per node). -/
abbrev ZREC : ArrId := 8
/-- The `zero` cons-table slots, both tiers interleaved. -/
abbrev ZSLOT : ArrId := 9


/-- The (constant) hash of the `zero` record: there is only one key, so the home slot of every
probe is the same, fixed slot. -/
def zeroHashW : Word := fnvBasis

/-- The growth schema of this table (`SlotGrow.lean`; one node per tier, so it never grows). -/
def zeroGS : GrowSch :=
  ⟨ZSLOT, ZREC, 1, 8, lblk (n, k, t, i, c, h) {
    h := ⟪zeroHashW⟫
  }⟩

/-- The model of the match: **every** node of this table is the `zero` node. -/
def zmatchW (_r : Array Word) (_t _i : Word) : Bool := true

/-- The (constant) hash of node `i` of tier `t`. -/
def zhash (_m : Mem) (_t _i : Word) : Word := zeroHashW

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `zero` tier (tag `0`). -/
def zeroP : Word := 0x00000000
def zeroS : Word := 0x08000000

/-- The `zero` table as a cons schema: no key word, a dummy record word `0`; every node matches;
no scratch skip. -/
def zeroCS : ConsSch where
  ra := ZREC
  sa := ZSLOT
  w := 1
  st := 2
  ca := 8
  P := zeroP
  S := zeroS
  fname := "zero_find"
  pname := "zero_push"
  nk := 0
  mc := condOf (lblk (t, h, n, j, d, v, b) { if 0 == 0 { skip } })
  np := 0
  room := condOf (lblk (t, j, c) { if len(ZREC.u64) >> 1 <= c { skip } })
  recW := [.const 0]
  ghash := zeroGS.hash
  ihash := lblk (h) { h := ⟪zeroHashW⟫ }
  skipW := none
  mtM m _ t i := zmatchW (m.arr64 ZREC) t i
  qhM _ _ := zeroHashW
  hsM := zhash
  vsM _ := [0]
  roomM m _ c := decide (m.len64 ZREC >>> (1 : Word) ≤ c)

/-! ## `zero_find(t, h)`: the probe -/

/-- The model of the probe, from slot `j` after `d` steps (the library's `cprobeW`). -/
def zprobeW (sl r : Array Word) (t b n j d : Word) : List Word :=
  cprobeW sl (fun i => zmatchW r t i) t b n j d

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def zeroFind : FunDecl := consFindG zeroCS

/-- The slot count of a tier of the `zero` table. -/
def nSlotsZ (m : Mem) : Word := rdW (m.arr64 ZSLOT) (m.len64 ZSLOT - 1) + SN0

/-! ## `zero_push(t, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `zero` table, `CTL[8 + t]`. -/
def zcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (8 + t)

/-- `zero_push`'s room checks: the handle index, the record array. -/
def zpushOK (m : Mem) (t : Word) : Bool :=
  decide (zcnt m t < (134217728 : Word)) && decide (zcnt m t < m.len64 ZREC >>> (1 : Word))

/-- The memory after `zero_push(t, j)` appended node `c`. -/
def zpushMem (m : Mem) (t j c : Word) : Mem :=
  (((m.set64 ZREC (c * 2 + t) 0).set64 ZSLOT (j * 2 + t) (baseW m t + c + 1)).set64 CTL (8 + (t &&& 1)) (c + 1))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def zeroPush : FunDecl := consPushG zeroCS

/-! ## `intern_zero()`: hash-cons the level `zero`

con-ron's `LStore::intern` at `zero` and the arena's `internLNode .zero`: the persistent probe,
the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The model of `intern_zero`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def zinternW (m : Mem) : Option (Word × Mem) := consInternM zeroCS m []

/-- con-ron: ConRon/Arena/Monad.lean:441-457 ConRon.Arena.internLNode -/
@[l_impl ConRon.Arena.internLNode]
def internZero : FunDecl := consInternG zeroCS

/-- The `zero` store functions, as one `#eval`-able program. -/
def zeroProg : Prog :=
  [("zero_find", zeroFind), ("zero_push", zeroPush), ("intern_zero", internZero)]

/-- A memory with 8 `zero` slots per tier, the scratch tier closed or open. -/
def zeroMem (scratch : Word) : Mem :=
  { words := #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[], #[], #[], #[], #[],
      Array.replicate 16 0, Array.replicate 32 0] }

/-- Intern `zero` `k` times in a row: the handle, every time, is the first persistent node. -/
def internZeros (m : Mem) : Nat → Option (List Word)
  | 0 => some []
  | k + 1 => match run zeroProg 100 "intern_zero" [] m with
    | .ok (r, m') => (internZeros m' k).map (r.headD 0 :: ·)
    | .error _ => none

/- Interning `zero` three times in a row: the same persistent handle every time (sharing). -/
#guard internZeros (zeroMem 0) 3 == some [0x00000000, 0x00000000, 0x00000000]

/- Scratch open: the one node goes to the scratch tier (the persistent tier is empty). -/
#guard internZeros (zeroMem 1) 2 == some [0x08000000, 0x08000000]

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

/-- The growth's hash block computes `zhash`. -/
theorem zhash_ok : HashOK p zeroGS 4 zhash := by
  intro k s₀
  simp only [zeroGS, shiftS, shiftE, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalArgs, setLoc, ld64] <;> finish [zhash, zeroHashW, LocEq, St.setLoc]

/-- **The `zero` table's obligations.** -/
theorem zeroOK : ConsOK p zeroCS where
  match_ := by
    intro s
    simp [zeroCS, condOf, Cond.pval, Expr.pval, zmatchW, Cmp.eval, L.Notation.blk]
  ghash := zhash_ok p
  ihash := by
    intro n s₀
    simp only [zeroCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, zeroHashW]
  recs := ⟨by
      intro e he s s' _
      simp only [zeroCS, List.mem_cons, List.not_mem_nil, or_false] at he
      subst he; simp [Expr.pval],
    fun s => by simp [zeroCS, Expr.pval]⟩
  room := fun s => by
    simp only [zeroCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval, BinOp.eval]; rfl
  skips := by intro e he; simp [zeroCS] at he
  pre := rfl
  colA := by simp [zeroCS]
  push_np := by decide
  arrs := by decide

theorem zeroFind_spec (hp : p.lookup "zero_find" = some zeroFind) (n : Nat) (s₀ : St) (t h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "zero_find" [t, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = zprobeW (s₀.mem.arr64 ZSLOT) (s₀.mem.arr64 ZREC) t
        (baseW s₀.mem t) (nSlotsZ s₀.mem) (homeW h (nSlotsZ s₀.mem)) 0; ⊤⦄ :=
  consFindG_spec p zeroCS (((zeroOK p).match_)) hp n s₀ t [] rfl h trivial

theorem zpushOK_eqC (m : Mem) (t : Word) : zpushOK m t = pushOKC zeroCS m t := by
  simp only [zpushOK, pushOKC, zcnt, cntC, zeroCS, ← decide_not, UInt64.not_le]; rfl

theorem zpushMem_eqC (m : Mem) (t j c : Word) :
    zpushMem m t j c = pushMC zeroCS m t [0] j c := by
  simp [zpushMem, pushMC, tailM, wrRecK, zeroCS, baseW,
    Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ ZREC by decide)]

theorem zeroPush_spec (hp : p.lookup "zero_push" = some zeroPush) (n : Nat) (s₀ : St) (t j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "zero_push" [t, j]
    ⦃fun r s' => LocEq s' s₀ ∧ zpushOK s₀.mem t = true ∧ r = [zcnt s₀.mem t] ∧
      growIf ZSLOT 8 zhash s₀.mem (zpushMem s₀.mem t j (zcnt s₀.mem t))
        (zcnt s₀.mem t) = some s'.mem; ⊤⦄ := by
  rw [zpushOK_eqC]
  simp only [zpushMem_eqC]
  exact consPushG_spec p zeroCS (zeroOK p) hp n s₀ t [] rfl j

theorem internZero_spec (hpf : p.lookup "zero_find" = some zeroFind)
    (hpp : p.lookup "zero_push" = some zeroPush) (hp : p.lookup "intern_zero" = some internZero)
    (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_zero" []
    ⦃fun r s' => LocEq s' s₀ ∧ zinternW s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p zeroCS (zeroOK p) hpf hpp "intern_zero" hp n s₀ [] rfl trivial

end specs

end L.Arena
