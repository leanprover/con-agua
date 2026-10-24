module

public import ConAgua.Arena.ConsLibSpec
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.ConsLib
import ConAgua.Census.Attr

@[expose] public section

/-!
# The name store's `num` node store in L: a prefix handle and a `Nat` field per node

The arena's name store keeps `num pre n` nodes in a `Tbl NumNode NIdx UInt64` per tier
(`vendor/con-ron/ConRon/Arena/Store.lean:119`, `NTables.nums`). Its L representation is the
`max` store's (`MaxStore.lean`) two-word shape, but the second field is the `Nat` itself (as
`bvar` stores its index, `BVarStore.lean`), not a handle:

* **Records.** Word array `NNREC`, two words per node: the prefix's handle word, then the number
  as a word. Tiers interleaved: node `i` of tier `t` at `NNREC[4 i + 2 t ..]`. The node count of
  tier `t` is `CTL[38 + t]`.
* **Cons table.** Word array `NNSLOT`, the same open addressing as `SLOT`/`MSLOT`.

A `num` node has one child (its prefix), but the name store's `NStore.find?` probes the persistent
tier unconditionally (no scratch skip), as the level store's `LStore.find?` does.

The functions `nnum_find(t, pre, u, h)`, `nnum_push(t, pre, u, j)` and `intern_nnum(pre, u)` are the
cons-table library's templates (`ConsLib.lean`) at the schema `nnumCS` (no scratch skip); their
specs are the library's (`ConsLibSpec.lean`) from this table's obligations (`nnumOK`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `num` records, both tiers interleaved (two words per node). -/
abbrev NNREC : ArrId := 37
/-- The `num` cons-table slots, both tiers interleaved. -/
abbrev NNSLOT : ArrId := 38

/-- The growth schema of this table (`SlotGrow.lean`). -/
def nnumGS : GrowSch :=
  ⟨NNSLOT, NNREC, 2, 38, lblk (n, k, t, i, c, h) {
    h := ((⟪fnvBasis⟫ ^ NNREC.u64[i * 4 + t * 2]) * ⟪fnvPrime⟫ ^ NNREC.u64[i * 4 + t * 2 + 1]) * ⟪fnvPrime⟫
  }⟩

/-- The hash of a `num` record (FNV-1a over its two words). -/
def nnumHashW (pre u : Word) : Word := ((fnvBasis ^^^ pre) * fnvPrime ^^^ u) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(pre, u)`. -/
def nnmatchW (r : Array Word) (t i pre u : Word) : Bool :=
  rdW r (i * 4 + t * 2) == pre && rdW r (i * 4 + t * 2 + 1) == u

/-- The hash of node `i` of tier `t`. -/
def nnhash (m : Mem) (t i : Word) : Word :=
  nnumHashW (rdW (m.arr64 NNREC) (i * 4 + t * 2)) (rdW (m.arr64 NNREC) (i * 4 + t * 2 + 1))

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `num` tier (tag `2`). -/
def nnP : Word := 0x20000000
def nnS : Word := 0x28000000

/-- The `nnum` table as a cons schema: two key words, stored as the record; the match is two word comparisons;
no scratch skip. -/
def nnumCS : ConsSch where
  ra := NNREC
  sa := NNSLOT
  w := 2
  st := 4
  ca := 38
  P := nnP
  S := nnS
  tag := 2
  fname := "nnum_find"
  pname := "nnum_push"
  nk := 2
  mc := condOf (lblk (t, pre, u, h, n, j, d, w, b) {
    if NNREC.u64[(w - 1) * 4 + t * 2] == pre && NNREC.u64[(w - 1) * 4 + t * 2 + 1] == u { skip } })
  np := 2
  room := condOf (lblk (t, pre, u, j, c) { if len(NNREC.u64) >> 2 <= c { skip } })
  recW := [.var 1, .var 2]
  ghash := nnumGS.hash
  ihash := lblk (pre, u, h) { h := ((⟪fnvBasis⟫ ^ pre) * ⟪fnvPrime⟫ ^ u) * ⟪fnvPrime⟫ }
  skipW := none
  mtM m ks t i := nnmatchW (m.arr64 NNREC) t i (ks.getD 0 0) (ks.getD 1 0)
  qhM _ ks := nnumHashW (ks.getD 0 0) (ks.getD 1 0)
  hsM := nnhash
  vsM as := as
  roomM m _ c := decide (m.len64 NNREC >>> (2 : Word) ≤ c)

/-! ## `nnum_find(t, pre, u, h)`: the probe -/

/-- The model of the probe, from slot `j` after `d` steps (the library's `cprobeW`). -/
def nnprobeW (sl r : Array Word) (t pre u b n j d : Word) : List Word :=
  cprobeW sl (fun i => nnmatchW r t i pre u) t b n j d

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def nnumFind : FunDecl := consFindG nnumCS

/-- The slot count of a tier of the `num` table. -/
def nSlotsNN (m : Mem) : Word := rdW (m.arr64 NNSLOT) (m.len64 NNSLOT - 1) + SN0

/-! ## `nnum_push(t, pre, u, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `num` table, `CTL[38 + t]`. -/
def nncnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (38 + t)

/-- `nnum_push`'s room checks: the handle index, the record array. -/
def nnpushOK (m : Mem) (t : Word) : Bool :=
  decide (nncnt m t < (134217728 : Word)) && decide (nncnt m t < m.len64 NNREC >>> (2 : Word))

/-- The memory after `nnum_push(t, pre, u, j)` appended node `c`. -/
def nnpushMem (m : Mem) (t pre u j c : Word) : Mem :=
  ((((m.set64 NNREC (c * 4 + t * 2) pre).set64 NNREC (c * 4 + t * 2 + 1) u).set64 NNSLOT
    (j * 2 + t) (baseW m t + c + 1)).set64 CTL (38 + (t &&& 1)) (c + 1))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def nnumPush : FunDecl := consPushG nnumCS

/-! ## `intern_nnum(pre, u)`: hash-cons the name `num pre u`

con-ron's `NStore::intern` at `num` and the arena's `internNNode (.num pre n)`: the persistent
probe, the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The model of `intern_nnum`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def nninternW (m : Mem) (pre u : Word) : Option (Word × Mem) := consInternM nnumCS m [pre, u]

/-- con-ron: ConRon/Arena/Monad.lean:381-397 ConRon.Arena.internNNode -/
@[l_impl ConRon.Arena.internNNode]
def internNNum : FunDecl := consInternG nnumCS

/-- The `num` store functions, as one `#eval`-able program. -/
def nnumProg : Prog :=
  [("nnum_find", nnumFind), ("nnum_push", nnumPush), ("intern_nnum", internNNum)]

/-- A memory with 8 `num` nodes and 16 slots per tier, the scratch tier closed or open. Arrays
0‥36 (the other tables') are unused here and left empty. -/
def nnumMem (scratch : Word) : Mem :=
  { words := ((Array.replicate 37 #[]).set! 1 ((Array.replicate 64 0).set! 1 scratch)) ++
      #[Array.replicate 32 0, Array.replicate 32 0] }

/-- Intern each `(pre, u)` pair in turn; the handles. -/
def internNNums (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (pre, u) :: xs => match run nnumProg 100 "intern_nnum" [pre, u] m with
    | .ok (r, m') => (internNNums m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2)`, `(2, 1)`, `(1, 2)`: persistent handles 0, 1, 0 (sharing). -/
#guard internNNums (nnumMem 0) [(1, 2), (2, 1), (1, 2)] == some [0x20000000, 0x20000001, 0x20000000]

/- Scratch open: the nodes go to the scratch tier (the persistent tier is empty). -/
#guard internNNums (nnumMem 1) [(1, 2), (2, 1), (1, 2)] == some [0x28000000, 0x28000001, 0x28000000]

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

/-- The growth's hash block computes `nnhash`. -/
theorem nnhash_ok : HashOK p nnumGS 6 nnhash := by
  intro k s₀
  simp only [nnumGS, shiftS, shiftE, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalArgs, setLoc, ld64] <;> finish [nnhash, nnumHashW, LocEq, St.setLoc]

/-- **The `nnum` table's obligations.** -/
theorem nnumOK : ConsOK p nnumCS where
  match_ := by
    intro s
    simp [nnumCS, condOf, Cond.pval, Expr.pval, nnmatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ghash := nnhash_ok p
  ihash := by
    intro n s₀
    simp only [nnumCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, nnumHashW, argsOf, BinOp.eval]
  recs := ⟨by
      intro e he s s' h
      simp only [nnumCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [nnumCS, argsOf, Expr.pval, List.range_succ]⟩
  room := fun s => by
    simp only [nnumCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval, BinOp.eval]; rfl
  skips := by intro e he; simp [nnumCS] at he
  pre := rfl
  colA := by simp [nnumCS]
  push_np := by decide
  arrs := by decide

theorem nnumFind_spec (hp : p.lookup "nnum_find" = some nnumFind) (n : Nat) (s₀ : St) (t pre u h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nnum_find" [t, pre, u, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = nnprobeW (s₀.mem.arr64 NNSLOT) (s₀.mem.arr64 NNREC) t pre u
        (baseW s₀.mem t) (nSlotsNN s₀.mem) (homeW h (nSlotsNN s₀.mem)) 0; ⊤⦄ :=
  consFindG_spec p nnumCS (((nnumOK p).match_)) hp n s₀ t [pre, u] rfl h trivial

theorem nnpushOK_eqC (m : Mem) (t : Word) : nnpushOK m t = pushOKC nnumCS m t := by
  simp only [nnpushOK, pushOKC, nncnt, cntC, nnumCS, ← decide_not, UInt64.not_le]; rfl

theorem nnpushMem_eqC (m : Mem) (t pre u j c : Word) :
    nnpushMem m t pre u j c = pushMC nnumCS m t [pre, u] j c := by
  simp [nnpushMem, pushMC, tailM, wrRecK, nnumCS, baseW,
    Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ NNREC by decide)]

theorem nnumPush_spec (hp : p.lookup "nnum_push" = some nnumPush) (n : Nat) (s₀ : St) (t pre u j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nnum_push" [t, pre, u, j]
    ⦃fun r s' => LocEq s' s₀ ∧ nnpushOK s₀.mem t = true ∧ r = [nncnt s₀.mem t] ∧
      growIf NNSLOT 38 nnhash s₀.mem (nnpushMem s₀.mem t pre u j (nncnt s₀.mem t))
        (nncnt s₀.mem t) = some s'.mem; ⊤⦄ := by
  rw [nnpushOK_eqC]
  simp only [nnpushMem_eqC]
  exact consPushG_spec p nnumCS (nnumOK p) hp n s₀ t [pre, u] rfl j

theorem internNNum_spec (hpf : p.lookup "nnum_find" = some nnumFind)
    (hpp : p.lookup "nnum_push" = some nnumPush) (hp : p.lookup "intern_nnum" = some internNNum)
    (n : Nat) (s₀ : St) (pre u : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_nnum" [pre, u]
    ⦃fun r s' => LocEq s' s₀ ∧ nninternW s₀.mem pre u = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p nnumCS (nnumOK p) hpf hpp "intern_nnum" hp n s₀ [pre, u] rfl trivial

end specs

end L.Arena
