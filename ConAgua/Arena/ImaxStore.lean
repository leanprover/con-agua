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
# The level `imax` node store in L: a fourth store, two level-handle fields per node

The arena's level store keeps `imax u v` nodes in a `Tbl BinLNode LIdx LDer` per tier
(`Arena/Store.lean:159`, `LTables.imaxs`). Its L representation is the `app` store's
(`AppStore.lean`) with two handle fields and no scratch skip (the level store's `LStore.find?`
probes the persistent tier unconditionally, as for `succ`):

* **Records.** Word array `IREC`, two words per node (the handle words of `u` and `v`), tiers
  interleaved: node `i` of tier `t` at `IREC[4 i + 2 t ..]`. The node count of tier `t` is
  `CTL[12 + t]`.
* **Cons table.** Word array `ISLOT`, the same open addressing as `SLOT`/`ASLOT`/`SSLOT`.

The functions: `imax_find(t, u, v, h)`, `imax_push(t, u, v, j)` and `intern_imax(u, v)`. They are the cons-table library's templates
(`ConsLib.lean`) at the schema `imaxCS`, the derived column written by the template's prelude;
their specs are the library's (`ConsLibSpec.lean`) from this table's obligations.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `imax` records, both tiers interleaved (two words per node). -/
abbrev IREC : ArrId := 12
/-- The `imax` cons-table slots, both tiers interleaved. -/
abbrev ISLOT : ArrId := 13

/-- The growth schema of this table (`SlotGrow.lean`). -/
def imaxGS : GrowSch :=
  ⟨ISLOT, IREC, 2, 12, lblk (n, k, t, i, c, h) {
    h := ((⟪fnvBasis⟫ ^ IREC.u64[i * 4 + t * 2]) * ⟪fnvPrime⟫ ^ IREC.u64[i * 4 + t * 2 + 1]) * ⟪fnvPrime⟫
  }⟩

/-- The hash of an `imax` record (FNV-1a over its two words). -/
def imaxHashW (u v : Word) : Word := ((fnvBasis ^^^ u) * fnvPrime ^^^ v) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(u, v)`. -/
def immatchW (r : Array Word) (t i u v : Word) : Bool :=
  rdW r (i * 4 + t * 2) == u && rdW r (i * 4 + t * 2 + 1) == v

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `imax` tier (tag `3`). -/
def imaxP : Word := 0x30000000
def imaxS : Word := 0x38000000

/-- The hash of node `i` of tier `t`. -/
def imhash (m : Mem) (t i : Word) : Word :=
  imaxHashW (rdW (m.arr64 IREC) (i * 4 + t * 2)) (rdW (m.arr64 IREC) (i * 4 + t * 2 + 1))

/-- The column's prelude: `x := lvlHP(u) | lvlHP(v)`. -/
def imPre : Stmt :=
  .seq hpBlkM1 (.seq hpBlkM2 (lblk (t, u, v, j, c, k, x, g, ti, ix, y) { x := x | y }))

/-- The `imax` table as a cons schema (`ConsLib.lean`); the derived column `IHP`
(either child's `hasParam` bit, `hpBlkM1`, `hpBlkM2`). -/
def imaxCS : ConsSch where
  ra := IREC
  sa := ISLOT
  w := 2
  st := 4
  ca := 12
  P := imaxP
  S := imaxS
  tag := 3
  fname := "imax_find"
  pname := "imax_push"
  nk := 2
  mc := condOf (lblk (t, u, v, h, n, j, d, w, b) {
    if IREC.u64[(w - 1) * 4 + t * 2] == u && IREC.u64[(w - 1) * 4 + t * 2 + 1] == v { skip } })
  np := 2
  room := condOf (lblk (t, u, v, j, c) {
    if len(IREC.u64) >> 2 <= c || len(IHP.u64) >> 1 <= c { skip } })
  recW := [.var 1, .var 2]
  ghash := imaxGS.hash
  ihash := lblk (u, v, h) { h := ((⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫ ^ v) * ⟪fnvPrime⟫ }
  skipW := none
  xloc := 5
  pre := some imPre
  col := some IHP
  colM m as := lvlHPW m (as.getD 0 0) ||| lvlHPW m (as.getD 1 0)
  mtM m ks t i := immatchW (m.arr64 IREC) t i (ks.getD 0 0) (ks.getD 1 0)
  qhM _ ks := imaxHashW (ks.getD 0 0) (ks.getD 1 0)
  hsM := imhash
  vsM as := as
  roomM m _ c := decide (m.len64 IREC >>> (2 : Word) ≤ c) || decide (m.len64 IHP >>> (1 : Word) ≤ c)

/-! ## `imax_find(t, u, v, h)`: the probe -/

/-- The model of the probe, from slot `j` after `d` steps (the library's `cprobeW`). -/
def improbeW (sl r : Array Word) (t u v b n j d : Word) : List Word :=
  cprobeW sl (fun i => immatchW r t i u v) t b n j d

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def imaxFind : FunDecl := consFindG imaxCS

/-- The slot count of a tier of the `imax` table. -/
def nSlotsI (m : Mem) : Word := rdW (m.arr64 ISLOT) (m.len64 ISLOT - 1) + SN0

/-! ## `imax_push(t, u, v, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `imax` table, `CTL[12 + t]`. -/
def imcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (12 + t)

/-- `imax_push`'s room checks: the handle index, the record array. -/
def impushOK (m : Mem) (t : Word) : Bool :=
  decide (imcnt m t < (134217728 : Word)) && decide (imcnt m t < m.len64 IREC >>> (2 : Word)) &&
    decide (imcnt m t < m.len64 IHP >>> (1 : Word))

/-- The memory after `imax_push(t, u, v, j)` appended node `c`. -/
def impushMem (m : Mem) (t u v j c : Word) : Mem :=
  ((((m.set64 IREC (c * 4 + t * 2) u).set64 IREC (c * 4 + t * 2 + 1) v).set64 ISLOT (j * 2 + t)
    (baseW m t + c + 1)).set64 CTL (12 + (t &&& 1)) (c + 1)).set64 IHP (c * 2 + t)
    (lvlHPW m u ||| lvlHPW m v)

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def imaxPush : FunDecl := consPushG imaxCS

/-! ## `intern_imax(u, v)`: hash-cons the level `imax u v`

con-ron's `LStore::intern` at `imax` and the arena's `internLNode (.imax u v)`: the persistent
probe, the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The model of `intern_imax`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def iminternW (m : Mem) (u v : Word) : Option (Word × Mem) := consInternM imaxCS m [u, v]

/-- con-ron: ConRon/Arena/Monad.lean:441-457 ConRon.Arena.internLNode -/
@[l_impl ConRon.Arena.internLNode]
def internImax : FunDecl := consInternG imaxCS

/-- The `imax` store functions, as one `#eval`-able program. -/
def imaxProg : Prog :=
  [("imax_find", imaxFind), ("imax_push", imaxPush), ("intern_imax", internImax)]

/-- A memory with 8 `imax` nodes and 16 slots per tier, the scratch tier closed or open. -/
def imaxMem (scratch : Word) : Mem :=
  { words := #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[], #[], #[], #[],
      #[], #[], #[], #[], #[], Array.replicate 32 0, Array.replicate 32 0] ++
      Array.replicate 62 (Array.replicate 32 0) }

/-- Intern each pair in turn; the handles. -/
def internImaxs (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (u, v) :: xs => match run imaxProg 100 "intern_imax" [u, v] m with
    | .ok (r, m') => (internImaxs m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `(1, 2)`, `(2, 1)`, `(1, 2)`: persistent handles 0, 1, 0. -/
#guard internImaxs (imaxMem 0) [(1, 2), (2, 1), (1, 2)] == some [0x30000000, 0x30000001, 0x30000000]

/- Scratch open: the nodes go to the scratch tier (the persistent tier is empty). -/
#guard internImaxs (imaxMem 1) [(1, 2), (2, 1), (1, 2)] == some [0x38000000, 0x38000001, 0x38000000]

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

/-- The growth's hash block computes `imhash`. -/
theorem imhash_ok : HashOK p imaxGS 11 imhash := by
  intro k s₀
  simp only [imaxGS, shiftS, shiftE, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalArgs, setLoc, ld64] <;> finish [imhash, imaxHashW, LocEq, St.setLoc]

theorem imPre_spec (k : Stmt → M Sig) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p k imPre
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
      s'.loc 6 = lvlHPW s₀.mem (s₀.loc 1) ||| lvlHPW s₀.mem (s₀.loc 2); ⊤⦄ := by
  simp only [imPre, L.Notation.blk]
  vcgen [step, evalE_spec, setLoc, hpBlkM1_spec p k, hpBlkM2_spec p k]
  all_goals simp_all [Expr.pval, BinOp.eval, St.setLoc_loc, St.setLoc_mem]

/-- **The `imax` table's obligations.** -/
theorem imaxOK : ConsOK p imaxCS where
  match_ := by
    intro s
    simp [imaxCS, condOf, Cond.pval, Expr.pval, immatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ghash := imhash_ok p
  ihash := by
    intro n s₀
    simp only [imaxCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, imaxHashW, argsOf, BinOp.eval]
  pre := by
    intro n s₀
    vcgen [imPre_spec p (exec p n) s₀]
    all_goals obtain ⟨h0, h1, h2, h3, hx⟩ := ‹_ ∧ _›
    · assumption
    · intro x hx'
      simp only [imaxCS] at hx'
      rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) with rfl | rfl | rfl | rfl <;> assumption
    · simp [imaxCS, argsOf, List.range_succ, hx]
  colA := by
    intro A h
    simp only [imaxCS, Option.some.injEq] at h
    subst h; decide
  recs := ⟨by
      intro e he s s' h
      simp only [imaxCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [imaxCS, argsOf, Expr.pval, List.range_succ]⟩
  room := fun s => by
    simp only [imaxCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval, BinOp.eval]; rfl
  skips := by
    intro e he
    simp [imaxCS] at he
  push_np := by decide
  arrs := by decide

theorem imaxFind_spec (hp : p.lookup "imax_find" = some imaxFind) (n : Nat) (s₀ : St)
    (t u v h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "imax_find" [t, u, v, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = improbeW (s₀.mem.arr64 ISLOT) (s₀.mem.arr64 IREC) t u v
        (baseW s₀.mem t) (nSlotsI s₀.mem) (homeW h (nSlotsI s₀.mem)) 0; ⊤⦄ :=
  consFindG_spec p imaxCS ((imaxOK p).match_) hp n s₀ t [u, v] rfl h trivial

theorem impushOK_eqC (m : Mem) (t : Word) : impushOK m t = pushOKC imaxCS m t := by
  simp only [impushOK, pushOKC, imaxCS, Bool.not_or, ← decide_not, UInt64.not_le, Bool.and_assoc]
  rfl

theorem impushMem_eqC (m : Mem) (t u v j c : Word) :
    impushMem m t u v j c = pushMX imaxCS m t [u, v] (lvlHPW m u ||| lvlHPW m v) j c := by
  simp [impushMem, pushMX, colW, pushMC, tailM, wrRecK, imaxCS, baseW,
    Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ IREC by decide)]

theorem imaxPush_spec (hp : p.lookup "imax_push" = some imaxPush) (n : Nat) (s₀ : St)
    (t u v j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "imax_push" [t, u, v, j]
    ⦃fun r s' => LocEq s' s₀ ∧ impushOK s₀.mem t = true ∧ r = [imcnt s₀.mem t] ∧
      growIf ISLOT 12 imhash s₀.mem (impushMem s₀.mem t u v j (imcnt s₀.mem t))
        (imcnt s₀.mem t) = some s'.mem; ⊤⦄ := by
  rw [impushOK_eqC]
  simp only [impushMem_eqC]
  exact consPushG_spec p imaxCS (imaxOK p) hp n s₀ t [u, v] rfl j

theorem internImax_spec (hpf : p.lookup "imax_find" = some imaxFind)
    (hpp : p.lookup "imax_push" = some imaxPush) (hp : p.lookup "intern_imax" = some internImax)
    (n : Nat) (s₀ : St) (u v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_imax" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ iminternW s₀.mem u v = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p imaxCS (imaxOK p) hpf hpp "intern_imax" hp n s₀ [u, v] rfl trivial

end specs

end L.Arena
