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
# The `app` node store in L: a second store, two handle fields per node

The arena's `app` constructor is a `Tbl AppNode EIdx UInt64` per tier, `AppNode { f a : EIdx }`
(`Arena/Store.lean:278`). Its L representation follows the `lit` store's
(`ConAgua/Arena/Store.lean`), written out again for this record:

* **Records.** Word array `AREC`, one word per node (the handle words of `f` and `a`, packed: `f | a << 32`), tiers
  interleaved: node `i` of tier `t` at `AREC⟨t⟩[i]`. No stored hash: the hash is a
  cheap function of the two handle words. The node count of tier `t` is `CTL[4 + t]`.
* **Cons table.** Word array `ASLOT`, the cons-table library's layout (`ConsLib.lean`): one table
  per tier, the key word the key itself (an exact table), linear probing from `homeW`.
* **The scratch skip.** `internE (.app f a)` does not probe the persistent tier when the scratch
  tier is open and a child is a scratch handle (`EStore.persFindMaybe`,
  `eViewHasScratchChild`): bit 27 of `f | a`.

The functions `app_find(t, f, a, h)` (the probe, the match inline: two half-word comparisons),
`app_push(t, f, a, j)` and `intern_app(f, a)` are the cons-table library's templates
(`ConsLib.lean`) at the schema `appCS`; their specs are the library's (`ConsLibSpec.lean`) from
this table's obligations (`appOK`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `app` records, both tiers interleaved (one packed word per node). -/
abbrev AREC : ArrId := 4
/-- The `app` cons-table slots, both tiers interleaved. -/
abbrev ASLOT : ArrId := 5

/-- The hash of an `app` record (FNV-1a over its two handle words). -/
def appHashW (f a : Word) : Word := ((fnvBasis ^^^ f) * fnvPrime ^^^ a) * fnvPrime

/-- The hash of node `i` of tier `t`. -/
def ahash (m : Mem) (t i : Word) : Word :=
  appHashW (rdW (m.arr64 (tierA AREC t)) i &&& 4294967295) (rdW (m.arr64 (tierA AREC t)) i >>> 32)

/-- The model of the match: node `i` of tier `t` is `(f, a)`. -/
def amatchW (r : Array Word) (_t i f a : Word) : Bool :=
  rdW r i &&& 4294967295 == f && rdW r i >>> 32 == a

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `app` tier (tag `4`). -/
def appP : Word := 0x40000000
def appS : Word := 0x48000000

/-- The `app` table as a cons schema: two key words `f a`, packed into the record word; the match compares
its two halves; the scratch skip is bit 27 of `f | a`. -/
def appCS : ConsSch where
  ra := AREC
  sa := ASLOT
  w := 1
  ca := 4
  P := appP
  S := appS
  tag := 4
  fname := "app_find"
  pname := "app_push"
  nk := 2
  exact := true
  kpk := true
  mc := condOf (lblk (t, f, a, h, n, j, d, v, b) {
    if (AREC⟨t⟩[v - 1] & 4294967295) == f && (AREC⟨t⟩[v - 1] >> 32) == a { skip } })
  np := 2
  room := condOf (lblk (t, f, a, j, c) { if len(AREC⟨t⟩) <= c { skip } })
  recW := [.bin .or (.var 1) (.bin .shl (.var 2) (.const 32))]
  ihash := lblk (f, a, h) { h := ((⟪fnvBasis⟫ ^ f) * ⟪fnvPrime⟫ ^ a) * ⟪fnvPrime⟫ }
  skipW := some (rhsOf (lblk (f, a, h, sk) { sk := ((f | a) >> 27) & 1 }))
  mtM m ks t i := amatchW (m.arr64 (tierA AREC t)) t i (ks.getD 0 0) (ks.getD 1 0)
  qhM _ ks := appHashW (ks.getD 0 0) (ks.getD 1 0)
  hsM := ahash
  vsM as := [as.getD 0 0 ||| as.getD 1 0 <<< 32]
  roomM m t c := decide (m.len64 (tierA AREC t) ≤ c)
  skM ks := ((ks.getD 0 0 ||| ks.getD 1 0) >>> 27) &&& 1

/-! ## `app_find(t, f, a, h)`: the probe -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def appFind : FunDecl := consFindG appCS

/-! ## `app_push(t, f, a, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `app` table, `CTL[4 + t]`. -/
def acnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (4 + t)

/-- `app_push`'s room checks: the handle index, the record array. -/
def apushOK (m : Mem) (t : Word) : Bool :=
  decide (acnt m t < (134217728 : Word)) && decide (acnt m t < m.len64 (tierA AREC t))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def appPush : FunDecl := consPushG appCS

/-! ## `intern_app(f, a)`: hash-cons the `app` node with children `f` and `a`

con-ron's `EStore::intern` at `app` and the arena's `internE (.app f a)`: the persistent probe
unless the scratch tier is open and a child is a scratch handle, the scratch probe if the
scratch tier is open, the append to the tier the store is in. -/

/-- The scratch skip: the scratch tier is open and `f` or `a` is a scratch handle. -/
def askipW (m : Mem) (f a : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then ((f ||| a) >>> 27) &&& 1 else 0

/-- The model of `intern_app`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def ainternW (m : Mem) (f a : Word) : Option (Word × Mem) := consInternM appCS m [f, a]

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internApp : FunDecl := consInternG appCS

/-- The `app` store functions, as one `#eval`-able program. -/
def appProg : Prog :=
  [("app_find", appFind), ("app_push", appPush), ("intern_app", internApp)]

/-- A memory with 8 `app` nodes and `SN0` slots per tier, the scratch tier closed or open. -/
def appMem (scratch : Word) : Mem :=
  { words := withTiers <| #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[], Array.replicate consTestWords 0,
      Array.replicate consTestWords 0] }

/-- Intern each pair in turn; the handles. -/
def internApps (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (f, a) :: xs => match run appProg 100 "intern_app" [f, a] m with
    | .ok (r, m') => (internApps m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2)`, `(2, 1)`, `(1, 2)`: persistent handles 0, 1, 0. -/
#guard internApps (appMem 0) [(1, 2), (2, 1), (1, 2)] == some [0x40000000, 0x40000001, 0x40000000]

/- Scratch open: persistent children are probed in the persistent tier (empty), the nodes go to
the scratch tier; a scratch child (`0x48000000`) skips the persistent probe. -/
#guard internApps (appMem 1) [(1, 2), (0x48000000, 1), (1, 2), (0x48000000, 1)] ==
  some [0x48000000, 0x48000001, 0x48000000, 0x48000001]

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

/-- **The `app` table's obligations.** -/
theorem appOK : ConsOK p appCS where
  match_ := by
    intro s
    simp [appCS, condOf, Cond.pval, Expr.pval, amatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ihash := by
    intro n s₀
    simp only [appCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, appHashW, argsOf, BinOp.eval]
  ihashG := fun _ => by
    intro n s₀
    simp only [ihashAt, appCS, gO, shiftS, shiftE, L.Notation.blk, Nat.reduceAdd]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, appHashW, argsOf, BinOp.eval]
  recs := ⟨by
      intro e he s s' h
      simp only [appCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [appCS, argsOf, Expr.pval, BinOp.eval, List.range_succ]⟩
  room := fun s => by
    simp only [appCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval]; rfl
  skips := by
    intro e he s
    simp only [appCS, Option.some.injEq] at he
    subst he
    simp [appCS, rhsOf, L.Notation.blk, Expr.pval, argsOf, BinOp.eval, List.range_succ]
  pre := rfl
  colA := by simp [appCS]
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [appCS, reduceCtorEq] at h; (try subst h); (try decide)⟩
  qpure := fun h => by simp [appCS] at h
  mloc := fun h => by simp [appCS] at h
  exnk := fun _ => by decide

theorem dec_lt_not_le (x y : Word) : decide (x < y) = !decide (y ≤ x) := by
  by_cases h : y ≤ x
  · have : ¬ x < y := fun h' => absurd h (UInt64.not_le.mpr h')
    simp [h, this]
  · have : x < y := UInt64.not_le.mp h
    simp [h, this]

theorem apushOK_eqC (m : Mem) (t : Word) : apushOK m t = pushOKC appCS m t := by
  rw [apushOK, pushOKC, dec_lt_not_le (acnt m t) (m.len64 (tierA AREC t))]; rfl

theorem internApp_spec (hpf : p.lookup "app_find" = some appFind)
    (hpp : p.lookup "app_push" = some appPush) (hp : p.lookup "intern_app" = some internApp)
    (n : Nat) (s₀ : St) (f a : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_app" [f, a]
    ⦃fun r s' => LocEq s' s₀ ∧ ainternW s₀.mem f a = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p appCS (appOK p) hpf hpp "intern_app" hp n s₀ [f, a] rfl trivial

end specs

end L.Arena
