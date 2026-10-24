module

public import ConAgua.Arena.ConsLibSpec
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.ConsLib
import ConAgua.Census.Attr

@[expose] public section

/-!
# The `app` node store in L: a second store, two handle fields per node

The arena's `app` constructor is a `Tbl AppNode EIdx UInt64` per tier, `AppNode { f a : EIdx }`
(`Arena/Store.lean:278`). Its L representation follows the `lit` store's
(`ConAgua/Arena/Store.lean`), written out again for this record:

* **Records.** Word array `AREC`, two words per node (the handle words of `f` and `a`), tiers
  interleaved: node `i` of tier `t` at `AREC[4 i + 2 t ..]`. No stored hash: the hash is a
  cheap function of the two words. The node count of tier `t` is `CTL[4 + t]`.
* **Cons table.** Word array `ASLOT`, the same open addressing as `SLOT` (slot `j` of tier `t`
  at `ASLOT[2 j + t]`, `0` free, `i + 1` node `i`, linear probing from `homeW`).
* **The scratch skip.** `internE (.app f a)` does not probe the persistent tier when the scratch
  tier is open and a child is a scratch handle (`EStore.persFindMaybe`,
  `eViewHasScratchChild`): bit 27 of `f | a`.

The functions `app_find(t, f, a, h)` (the probe, the match inline: two word comparisons),
`app_push(t, f, a, j)` and `intern_app(f, a)` are the cons-table library's templates
(`ConsLib.lean`) at the schema `appCS`; their specs are the library's (`ConsLibSpec.lean`) from
this table's obligations (`appOK`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `app` records, both tiers interleaved (two words per node). -/
abbrev AREC : ArrId := 4
/-- The `app` cons-table slots, both tiers interleaved. -/
abbrev ASLOT : ArrId := 5

/-- The growth schema of this table (`SlotGrow.lean`). -/
def appGS : GrowSch :=
  ⟨ASLOT, AREC, 2, 4, lblk (n, k, t, i, c, h) {
    h := ((⟪fnvBasis⟫ ^ AREC.u64[i * 4 + t * 2]) * ⟪fnvPrime⟫ ^ AREC.u64[i * 4 + t * 2 + 1]) * ⟪fnvPrime⟫
  }⟩

/-- The hash of an `app` record (FNV-1a over its two words). -/
def appHashW (f a : Word) : Word := ((fnvBasis ^^^ f) * fnvPrime ^^^ a) * fnvPrime

/-- The hash of node `i` of tier `t`. -/
def ahash (m : Mem) (t i : Word) : Word :=
  appHashW (rdW (m.arr64 AREC) (i * 4 + t * 2)) (rdW (m.arr64 AREC) (i * 4 + t * 2 + 1))

/-- The model of the match: node `i` of tier `t` is `(f, a)`. -/
def amatchW (r : Array Word) (t i f a : Word) : Bool :=
  rdW r (i * 4 + t * 2) == f && rdW r (i * 4 + t * 2 + 1) == a

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `app` tier (tag `4`). -/
def appP : Word := 0x40000000
def appS : Word := 0x48000000

/-- The `app` table as a cons schema: two key words `f a`, stored as the record; the match is
two word comparisons; the scratch skip is bit 27 of `f | a`. -/
def appCS : ConsSch where
  ra := AREC
  sa := ASLOT
  w := 2
  st := 4
  ca := 4
  P := appP
  S := appS
  tag := 4
  fname := "app_find"
  pname := "app_push"
  nk := 2
  mc := condOf (lblk (t, f, a, h, n, j, d, v, b) {
    if AREC.u64[(v - 1) * 4 + t * 2] == f && AREC.u64[(v - 1) * 4 + t * 2 + 1] == a { skip } })
  np := 2
  room := condOf (lblk (t, f, a, j, c) { if len(AREC.u64) >> 2 <= c { skip } })
  recW := [.var 1, .var 2]
  ghash := appGS.hash
  ihash := lblk (f, a, h) { h := ((⟪fnvBasis⟫ ^ f) * ⟪fnvPrime⟫ ^ a) * ⟪fnvPrime⟫ }
  skipW := some (rhsOf (lblk (f, a, h, sk) { sk := ((f | a) >> 27) & 1 }))
  mtM m ks t i := amatchW (m.arr64 AREC) t i (ks.getD 0 0) (ks.getD 1 0)
  qhM _ ks := appHashW (ks.getD 0 0) (ks.getD 1 0)
  hsM := ahash
  vsM as := as
  roomM m _ c := decide (m.len64 AREC >>> (2 : Word) ≤ c)
  skM ks := ((ks.getD 0 0 ||| ks.getD 1 0) >>> 27) &&& 1

/-! ## `app_find(t, f, a, h)`: the probe -/

/-- The model of the probe, from slot `j` after `d` steps (the library's `cprobeW`). -/
def aprobeW (sl r : Array Word) (t f a b n j d : Word) : List Word :=
  cprobeW sl (fun i => amatchW r t i f a) t b n j d

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def appFind : FunDecl := consFindG appCS

/-- The slot count of a tier of the `app` table. -/
def nSlotsA (m : Mem) : Word := rdW (m.arr64 ASLOT) (m.len64 ASLOT - 1) + SN0

/-! ## `app_push(t, f, a, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `app` table, `CTL[4 + t]`. -/
def acnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (4 + t)

/-- `app_push`'s room checks: the handle index, the record array. -/
def apushOK (m : Mem) (t : Word) : Bool :=
  decide (acnt m t < (134217728 : Word)) && decide (acnt m t < m.len64 AREC >>> (2 : Word))

/-- The memory after `app_push(t, f, a, j)` appended node `c`. -/
def apushMem (m : Mem) (t f a j c : Word) : Mem :=
  ((((m.set64 AREC (c * 4 + t * 2) f).set64 AREC (c * 4 + t * 2 + 1) a).set64 ASLOT (j * 2 + t)
    (baseW m t + c + 1)).set64 CTL (4 + (t &&& 1)) (c + 1))

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

/-- A memory with 8 `app` nodes and 16 slots per tier, the scratch tier closed or open. -/
def appMem (scratch : Word) : Mem :=
  { words := #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[], Array.replicate 32 0,
      Array.replicate 32 0] }

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

/-- The growth's hash block computes `ahash`. -/
theorem appHash_ok : HashOK p appGS 6 ahash := by
  intro k s₀
  simp only [appGS, shiftS, shiftE, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalArgs, setLoc, ld64] <;> finish [ahash, appHashW, LocEq, St.setLoc]

/-- **The `app` table's obligations.** -/
theorem appOK : ConsOK p appCS where
  match_ := by
    intro s
    simp [appCS, condOf, Cond.pval, Expr.pval, amatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ghash := appHash_ok p
  ihash := by
    intro n s₀
    simp only [appCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, appHashW, argsOf, BinOp.eval]
  recs := ⟨by
      intro e he s s' h
      simp only [appCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [appCS, argsOf, Expr.pval, List.range_succ]⟩
  room := fun s => by
    simp only [appCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval, BinOp.eval]; rfl
  skips := by
    intro e he s
    simp only [appCS, Option.some.injEq] at he
    subst he
    simp [appCS, rhsOf, L.Notation.blk, Expr.pval, argsOf, BinOp.eval, List.range_succ]
  pre := rfl
  colA := by simp [appCS]
  push_np := by decide
  arrs := by decide

theorem appFind_spec (hp : p.lookup "app_find" = some appFind) (n : Nat) (s₀ : St) (t f a h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "app_find" [t, f, a, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = aprobeW (s₀.mem.arr64 ASLOT) (s₀.mem.arr64 AREC) t f a
        (baseW s₀.mem t) (nSlotsA s₀.mem) (homeW h (nSlotsA s₀.mem)) 0; ⊤⦄ :=
  consFindG_spec p appCS ((appOK p).match_) hp n s₀ t [f, a] rfl h trivial

theorem dec_lt_not_le (x y : Word) : decide (x < y) = !decide (y ≤ x) := by
  by_cases h : y ≤ x
  · have : ¬ x < y := fun h' => absurd h (UInt64.not_le.mpr h')
    simp [h, this]
  · have : x < y := UInt64.not_le.mp h
    simp [h, this]

theorem apushOK_eqC (m : Mem) (t : Word) : apushOK m t = pushOKC appCS m t := by
  rw [apushOK, pushOKC, dec_lt_not_le (acnt m t) (m.len64 AREC >>> 2)]; rfl

theorem apushMem_eqC (m : Mem) (t f a j c : Word) :
    apushMem m t f a j c = pushMC appCS m t [f, a] j c := by
  simp [apushMem, pushMC, tailM, wrRecK, appCS, baseW,
    Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ AREC by decide)]

theorem appPush_spec (hp : p.lookup "app_push" = some appPush) (n : Nat) (s₀ : St) (t f a j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "app_push" [t, f, a, j]
    ⦃fun r s' => LocEq s' s₀ ∧ apushOK s₀.mem t = true ∧ r = [acnt s₀.mem t] ∧
      growIf ASLOT 4 ahash s₀.mem (apushMem s₀.mem t f a j (acnt s₀.mem t)) (acnt s₀.mem t) = some s'.mem;
      ⊤⦄ := by
  rw [apushOK_eqC]
  simp only [apushMem_eqC]
  exact consPushG_spec p appCS (appOK p) hp n s₀ t [f, a] rfl j

theorem internApp_spec (hpf : p.lookup "app_find" = some appFind)
    (hpp : p.lookup "app_push" = some appPush) (hp : p.lookup "intern_app" = some internApp)
    (n : Nat) (s₀ : St) (f a : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_app" [f, a]
    ⦃fun r s' => LocEq s' s₀ ∧ ainternW s₀.mem f a = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p appCS (appOK p) hpf hpp "intern_app" hp n s₀ [f, a] rfl trivial

end specs

end L.Arena
