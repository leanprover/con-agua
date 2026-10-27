module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.ConsLib
public import ConAgua.Arena.ConsLibSpec
import ConAgua.Census.Attr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The `lam` node store in L: a binder record, two handle fields per node

The arena's `lam` constructor is a `Tbl BindNode EIdx UInt64` per tier (`Arena/Store.lean:287`,
`ETables.lams`), shared with `forallE` (`ForallStore.lean`). `BindNode { ty body : EIdx }` has the
`app`/`AppNode` shape exactly (two handle fields), so the L representation is `app`'s, written out
again for this record:

* **Records.** Word array `LAREC`, one word per node (the handle words of `ty` and `body`, packed: `ty | body << 32`),
  tiers interleaved: node `i` of tier `t` at `LAREC⟨t⟩[i]`. The node count of tier `t` is
  `CTL[28 + t]`.
* **Cons table.** Word array `LASLOT`, the same open addressing as `SLOT`/`ASLOT`.
* **The scratch skip.** `internE (.lam ty body)` does not probe the persistent tier when the
  scratch tier is open and a child is a scratch handle (`EStore.persFindBindMaybe`,
  `bindHasScratchChild`): bit 27 of `ty | body`.

Unlike `app`, `internE` at `lam` does **not** go through `internNodeE`: it is `internLamE`
(`ConRon/Arena/Monad.lean`), which probes with `EStore.findBind ETag.lam ty body`, tests
`bindSizeOf` at the tier the append goes to, then calls `EStore.internLam = EStore.internBind
ETag.lam`, which re-probes and pushes via `ETables.pushBind` (`ConRon/Arena/Store.lean`). The L
side (this file) is unaffected: it is still one probe-loop, one push, one dispatcher, as `app`'s.
`LamRefine.lean` carries the different unfolding to `protoRun`.

The functions `lam_find(t, ty, body, h)` (the probe, the match inline: two half-word comparisons),
`lam_push(t, ty, body, j)` and `intern_lam(ty, body)` are the cons-table library's templates
(`ConsLib.lean`) at the schema `lamCS`; their specs are the library's (`ConsLibSpec.lean`) from
this table's obligations (`lamOK`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The hash of a `lam` record (FNV-1a over its two handle words). -/
def lamHashW (ty body : Word) : Word := ((fnvBasis ^^^ ty) * fnvPrime ^^^ body) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(ty, body)`. -/
def lamatchW (r : Array Word) (_t i ty body : Word) : Bool :=
  rdW r i &&& 4294967295 == ty && rdW r i >>> 32 == body

/-- The hash of node `i` of tier `t`. -/
def lahash (m : Mem) (t i : Word) : Word :=
  lamHashW (rdW (m.arr64 (tierA LAREC t)) i &&& 4294967295) (rdW (m.arr64 (tierA LAREC t)) i >>> 32)

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `lam` tier (tag `5`). -/
def lamP : Word := 0x50000000
def lamS : Word := 0x58000000

/-- The `lam` table as a cons schema: two key words `ty body`, stored as the record; the match
is two word comparisons; the scratch skip is bit 27 of `ty | body`. -/
def lamCS : ConsSch where
  ra := LAREC
  sa := LASLOT
  w := 1
  ca := 28
  P := lamP
  S := lamS
  tag := 5
  fname := "lam_find"
  pname := "lam_push"
  nk := 2
  exact := true
  kpk := true
  mc := condOf (lblk (t, ty, body, h, n, j, d, v, b) {
    if (LAREC⟨t⟩[v - 1] & 4294967295) == ty && (LAREC⟨t⟩[v - 1] >> 32) == body { skip } })
  np := 2
  room := condOf (lblk (t, ty, body, j, c) { if len(LAREC⟨t⟩) <= c { skip } })
  recW := [.bin .or (.var 1) (.bin .shl (.var 2) (.const 32))]
  ihash := lblk (ty, body, h) { h := ((⟪fnvBasis⟫ ^ ty) * ⟪fnvPrime⟫ ^ body) * ⟪fnvPrime⟫ }
  skipW := some (rhsOf (lblk (ty, body, h, sk) { sk := ((ty | body) >> 27) & 1 }))
  mtM m ks t i := lamatchW (m.arr64 (tierA LAREC t)) t i (ks.getD 0 0) (ks.getD 1 0)
  qhM _ ks := lamHashW (ks.getD 0 0) (ks.getD 1 0)
  hsM := lahash
  vsM as := [as.getD 0 0 ||| as.getD 1 0 <<< 32]
  roomM m t c := decide (m.len64 (tierA LAREC t) ≤ c)
  skM ks := ((ks.getD 0 0 ||| ks.getD 1 0) >>> 27) &&& 1

/-! ## `lam_find(t, ty, body, h)`: the probe -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def lamFind : FunDecl := consFindG lamCS

/-! ## `lam_push(t, ty, body, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `lam` table, `CTL[28 + t]`. -/
def lacnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (28 + t)

/-- `lam_push`'s room checks: the handle index, the record array. -/
def lapushOK (m : Mem) (t : Word) : Bool :=
  decide (lacnt m t < (134217728 : Word)) && decide (lacnt m t < m.len64 (tierA LAREC t))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def lamPush : FunDecl := consPushG lamCS

/-! ## `intern_lam(ty, body)`: hash-cons the `lam` binder with binder type `ty` and body `body`

con-ron's `EStore::internLam` (through `internBind`) and the arena's `internLamE`: the persistent
probe unless the scratch tier is open and a child is a scratch handle, the scratch probe if the
scratch tier is open, the append to the tier the store is in. Same L shape as `app`'s
`intern_app`; `LamRefine.lean` carries the different unfolding of `internLamE` to `protoRun`. -/

/-- The scratch skip: the scratch tier is open and `ty` or `body` is a scratch handle. -/
def laskipW (m : Mem) (ty body : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then ((ty ||| body) >>> 27) &&& 1 else 0

/-- The model of `intern_lam`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def lainternW (m : Mem) (ty body : Word) : Option (Word × Mem) := consInternM lamCS m [ty, body]

/-- The L FunDecl for `intern_lam`. Named `internLamL`, not `internLam`: con-ron's
`EStore.internLam` (`ConRon/Arena/Store.lean`) is a sibling name in a different namespace, but the
`L`-suffix keeps the two visually apart in this file, which `open`s `ConRon.Arena`. -/
-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
-- con-ron: ConRon/Arena/Monad.lean:169-197 ConRon.Arena.internLamE
@[l_impl ConRon.Arena.internE ConRon.Arena.internLamE]
def internLamL : FunDecl := consInternG lamCS

/-- The `lam` store functions, as one `#eval`-able program. -/
def lamProg : Prog :=
  [("lam_find", lamFind), ("lam_push", lamPush), ("intern_lam", internLamL)]

/-- A memory with 8 `lam` nodes and `SN0` slots per tier, the scratch tier closed or open. Arrays
other than `CTL`/`LAREC`/`LASLOT` are unused here and left empty; `CTL` reaches `28 + 2 = 30`
words. -/
def lamMem (scratch : Word) : Mem :=
  { words := withTiers <| #[#[],
      (#[0, scratch] ++ Array.replicate 62 0),
      #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[],
      #[], #[], #[], #[], #[], #[], #[],
      Array.replicate consTestWords 0, Array.replicate consTestWords 0] }

/-- Intern each pair in turn; the handles. -/
def internLams (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (ty, body) :: xs => match run lamProg 100 "intern_lam" [ty, body] m with
    | .ok (r, m') => (internLams m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2)`, `(2, 1)`, `(1, 2)`: persistent handles 0, 1, 0. -/
#guard internLams (lamMem 0) [(1, 2), (2, 1), (1, 2)] == some [0x50000000, 0x50000001, 0x50000000]

/- Scratch open: persistent children are probed in the persistent tier (empty), the nodes go to
the scratch tier; a scratch child (`0x58000000`) skips the persistent probe. -/
#guard internLams (lamMem 1) [(1, 2), (0x58000000, 1), (1, 2), (0x58000000, 1)] ==
  some [0x58000000, 0x58000001, 0x58000000, 0x58000001]

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

/-- **The `lam` table's obligations.** -/
theorem lamOK : ConsOK p lamCS where
  match_ := by
    intro s
    simp [lamCS, condOf, Cond.pval, Expr.pval, lamatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ihash := by
    intro n s₀
    simp only [lamCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, lamHashW, argsOf, BinOp.eval]
  ihashG := fun _ => by
    intro n s₀
    simp only [ihashAt, lamCS, gO, shiftS, shiftE, L.Notation.blk, Nat.reduceAdd]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, lamHashW, argsOf, BinOp.eval]
  recs := ⟨by
      intro e he s s' h
      simp only [lamCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [lamCS, argsOf, Expr.pval, BinOp.eval, List.range_succ]⟩
  room := fun s => by
    simp only [lamCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval]; rfl
  skips := by
    intro e he s
    simp only [lamCS, Option.some.injEq] at he
    subst he
    simp [lamCS, rhsOf, L.Notation.blk, Expr.pval, argsOf, BinOp.eval, List.range_succ]
  pre := rfl
  colA := by simp [lamCS]
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [lamCS, reduceCtorEq] at h; (try subst h); (try decide)⟩
  qpure := fun h => by simp [lamCS] at h
  mloc := fun h => by simp [lamCS] at h
  exnk := fun _ => by decide

theorem lapushOK_eqC (m : Mem) (t : Word) : lapushOK m t = pushOKC lamCS m t := by
  simp only [lapushOK, pushOKC, lamCS, lacnt, cntC, ← decide_not, UInt64.not_le]; rfl

theorem internLamL_spec (hpf : p.lookup "lam_find" = some lamFind)
    (hpp : p.lookup "lam_push" = some lamPush) (hp : p.lookup "intern_lam" = some internLamL)
    (n : Nat) (s₀ : St) (ty body : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lam" [ty, body]
    ⦃fun r s' => LocEq s' s₀ ∧ lainternW s₀.mem ty body = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p lamCS (lamOK p) hpf hpp "intern_lam" hp n s₀ [ty, body] rfl trivial

end specs

end L.Arena
