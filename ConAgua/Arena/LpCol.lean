module

public import ConAgua.Arena.ViewL
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The level-parameter bit of the derived words: the L columns and their read models

con-ron's stores keep, per node, a derived record: for expressions the packed word
(`packData hash bvarRange fvarRange lp`, `EStore.derOfView`), for levels and level lists an
`LDer` (`hash`, `hasParam`, `LStore.derOfView`, `LsStore.derOfView`). L keeps the hash nowhere
(no verdict reads it), the two ranges of the five compound tables in `XDER` (`ExprMk.lean`), and
(helper `whnf4-d23`, deviation D23) **the level-parameter bit of every table whose bit is not a
constant**, so that `instLP` can cut off at a parameter-free node exactly as the twin does:

| array | table | written by | value |
|---|---|---|---|
| 55 `SHP` | level `succ` | `succ_push` | `hasParam` of the child |
| 56 `MHP` | level `max` | `max_push` | `hasParam` of either child |
| 57 `IHP` | level `imax` | `imax_push` | `hasParam` of either child |
| 58 `LSHP` | level lists | `ls_push` | `hasParam` of any element |
| 59 `SOLP` | `sort` | `sort_push` | `hasParam` of the level |
| 60 `CLP` | `const` | `const_push` | `hasParam` of the level list |
| 61 `FVLP` | `fvar` | `fvar_push` | `lp` of the type |
| 42‥46 `XDER` bit 30 | the compound tables | `mk_*` | `lp` of any child |

One word (`0`/`1`) per node at `A[2 i + t]`, as the records. `zero`, `param`, `bvar`, `lit` have a
constant bit (`false`, `true`, `false`, `false`) and no column. Each column is written **when the
node is pushed**, from the children's bits read on the memory before the push (the twin computes
`derOfView` before `Tbl.push`): never later, so a bit is the twin's stored one even for a node
whose child handle dangled when it was interned.

The read models: `lvlHPW m u` (a level handle's bit), `lsHPW m us` (a level list's), `exprLPW m h`
(an expression's, `der_b`'s third result): the tier check, the tag, the count check, then the
column (`0` for a handle that does not view, as the twin's `derived` is `default`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

abbrev SHP : ArrId := 55
abbrev MHP : ArrId := 56
abbrev IHP : ArrId := 57
abbrev LSHP : ArrId := 58
abbrev SOLP : ArrId := 59
abbrev CLP : ArrId := 60
abbrev FVLP : ArrId := 61

/-- The compound tables' derived words (`ExprMk.lean`, `DerRel.lean`). -/
abbrev ADER : ArrId := 42
abbrev LADER : ArrId := 43
abbrev FADER : ArrId := 44
abbrev LEDER : ArrId := 45
abbrev PJDER : ArrId := 46

theorem tierW_le (h : Word) : tierW h ≤ 1 := by
  simp only [tierW]; exact UInt64.and_le_right

/-- A boolean as the word `1`/`0`. -/
def b2w (b : Bool) : Word := if b then 1 else 0

theorem b2w_or (x y : Bool) : b2w (x || y) = b2w x ||| b2w y := by
  cases x <;> cases y <;> rfl

theorem b2w_le (x : Bool) : b2w x ≤ 1 := by cases x <;> decide

/-- **A level handle's `hasParam` bit** (the model of the inline block of `succ_push`, `max_push`,
`imax_push`, `sort_push` and of `ls_push`'s loop body): `param` (tag 4) is `1` when it views,
`succ`/`max`/`imax` (tags 1‥3) read their column, everything else (`zero`, a handle that does not
view) is `0`. Counts: `CTL[14 + t]` (`param`), `CTL[6 + t]`, `CTL[10 + t]`, `CTL[12 + t]`. -/
def lvlHPW (m : Mem) (u : Word) : Word :=
  if tierW u ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then 0
  else if u >>> 28 = 4 then (if idxW u < tcnt m PARAM (tierW u) then 1 else 0)
  else if u >>> 28 = 1 then
    (if idxW u < tcnt m SUCC (tierW u) then tfld m SUCC_HP (tierW u) (idxW u) 0
     else 0)
  else if u >>> 28 = 2 then
    (if idxW u < tcnt m MAX (tierW u) then tfld m MAX_HP (tierW u) (idxW u) 0
     else 0)
  else if u >>> 28 = 3 then
    (if idxW u < tcnt m IMAX (tierW u) then tfld m IMAX_HP (tierW u) (idxW u) 0
     else 0)
  else 0

/-- **A level list's `hasParam` bit** (the model of `const_push`'s inline block): tag `0`, count
`CTL[40 + t]`, column `LSHP`. -/
def lsHPW (m : Mem) (us : Word) : Word :=
  if tierW us ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then 0
  else if us >>> 28 = 0 then
    (if idxW us < tcnt m LVLS (tierW us) then tfld m LS_HP (tierW us) (idxW us) 0
     else 0)
  else 0

/-- **The `hasParam` bit of the level list in the pool slice at `o`, of length `k`**: the `or` of
its elements' bits (`ls_push`'s loop; con-ron's `LsStore.derOfView`). It reads the slice
through tagged addresses (`prd`), as the loop does. -/
def lsOrW (m : Mem) (o : Word) : Nat → Word
  | 0 => 0
  | k + 1 => lsOrW m o k ||| lvlHPW m (prd m (o + UInt64.ofNat k))

theorem lsOrW_zero (m : Mem) (o : Word) : lsOrW m o 0 = 0 := rfl

theorem lsOrW_succ (m : Mem) (o : Word) (k : Nat) :
    lsOrW m o (k + 1) = lsOrW m o k ||| lvlHPW m (prd m (o + UInt64.ofNat k)) := rfl

/-- `lsOrW` from the front: the first element's bit, then the rest's. -/
theorem lsOrW_cons (m : Mem) (o : Word) : ∀ n : Nat,
    lsOrW m o (n + 1) = lvlHPW m (prd m o) ||| lsOrW m (o + 1) n := by
  intro n
  induction n with
  | zero => simp [lsOrW]
  | succ n ih =>
    rw [lsOrW_succ, ih, lsOrW_succ]
    have e : o + UInt64.ofNat (n + 1) = o + 1 + UInt64.ofNat n := by
      rw [UInt64.ofNat_add]; simp; ac_rfl
    rw [e, UInt64.or_assoc]

/-- **An expression handle's `lp` bit** (`der_b`'s third result, the model of `fvar_push`'s inline
block): `sort`, `const`, `fvar` read their column (`SOLP`, `CLP`, `FVLP`; counts `CTL[16 + t]`,
`CTL[18 + t]`, `CTL[26 + t]`), the five compound tables bit 30 of their `XDER` word (arrays 42‥46,
`ExprMk.lean`; counts `CTL[4 + t]`, `CTL[28 + t]`, `CTL[30 + t]`, `CTL[20 + t]`, `CTL[32 + t]`),
`bvar`, `lit` and a handle that does not view `0`. -/
def exprLPW (m : Mem) (h : Word) : Word :=
  if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then 0
  else if h >>> 28 = 1 then
    (if idxW h < tcnt m FVAR (tierW h) then tfld m FVAR_LP (tierW h) (idxW h) 0
     else 0)
  else if h >>> 28 = 2 then
    (if idxW h < tcnt m SORT (tierW h) then tfld m SORT_LP (tierW h) (idxW h) 0
     else 0)
  else if h >>> 28 = 3 then
    (if idxW h < tcnt m CONST (tierW h) then tfld m CONST_LP (tierW h) (idxW h) 0
     else 0)
  else if h >>> 28 = 4 then
    (if idxW h < tcnt m APP (tierW h) then tfld m APP_DER (tierW h) (idxW h) 0 >>> 30
     else 0)
  else if h >>> 28 = 5 then
    (if idxW h < tcnt m LAM (tierW h) then tfld m LAM_DER (tierW h) (idxW h) 0 >>> 30
     else 0)
  else if h >>> 28 = 6 then
    (if idxW h < tcnt m FORALL (tierW h) then tfld m FORALL_DER (tierW h) (idxW h) 0 >>> 30
     else 0)
  else if h >>> 28 = 7 then
    (if idxW h < tcnt m LET (tierW h) then tfld m LET_DER (tierW h) (idxW h) 0 >>> 30
     else 0)
  else if h >>> 28 = 9 then
    (if idxW h < tcnt m PROJ (tierW h) then tfld m PROJ_DER (tierW h) (idxW h) 0 >>> 30
     else 0)
  else 0

/-- Pack the two ranges and the `lp` bit (`l ≤ 1`) into a compound table's `XDER` word: bvar range
in bits 0‥14, fvar range in bits 15‥29 (`packBF`), `lp` in bit 30. -/
def packBFL (b f l : Word) : Word := packBF b f + l * 1073741824

theorem packBFL_bvar (b f l : Word) (hb : b.toNat < 32768) (hf : f.toNat < 32768) (hl : l ≤ 1) :
    packBFL b f l &&& 32767 = b := by
  have hl' : l.toNat ≤ 1 := hl
  apply UInt64.toNat_inj.mp
  simp only [packBFL, packBF, UInt64.toNat_and, UInt64.toNat_add, UInt64.toNat_mul]
  have e : (32767 : Word).toNat = 2 ^ 15 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  have e2 : (32768 : Word).toNat = 2 ^ 15 := rfl
  have e3 : (1073741824 : Word).toNat = 2 ^ 30 := rfl
  rw [e2, e3]
  omega

theorem packBFL_fvar (b f l : Word) (hb : b.toNat < 32768) (hf : f.toNat < 32768) (hl : l ≤ 1) :
    (packBFL b f l >>> 15) &&& 32767 = f := by
  have hl' : l.toNat ≤ 1 := hl
  apply UInt64.toNat_inj.mp
  simp only [packBFL, packBF, UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_add,
    UInt64.toNat_mul, Nat.shiftRight_eq_div_pow]
  have e : (32767 : Word).toNat = 2 ^ 15 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  have e15 : (15 : Word).toNat % 64 = 15 := rfl
  have e2 : (32768 : Word).toNat = 2 ^ 15 := rfl
  have e3 : (1073741824 : Word).toNat = 2 ^ 30 := rfl
  rw [e15, e2, e3]
  omega

theorem packBFL_lp (b f l : Word) (hb : b.toNat < 32768) (_hf : f.toNat < 32768) (hl : l ≤ 1) :
    packBFL b f l >>> 30 = l := by
  have hl' : l.toNat ≤ 1 := hl
  apply UInt64.toNat_inj.mp
  simp only [packBFL, packBF, UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_mul,
    Nat.shiftRight_eq_div_pow]
  have e30 : (30 : Word).toNat % 64 = 30 := rfl
  have e2 : (32768 : Word).toNat = 2 ^ 15 := rfl
  have e3 : (1073741824 : Word).toNat = 2 ^ 30 := rfl
  rw [e30, e2, e3]
  omega

/-! ## The inline blocks that compute a bit, and their specs

Each `*_push` computes the new node's bit on the memory before the push (the twin's `derOfView`
before `Tbl.push`), in a named block spliced into its body; the block's spec says which local
gets the bit and that the others before it stay. One block per local layout. -/

/-- `sort_push`, `succ_push` (`(t, u, j) locals (c, x, g, ti, ix)`): `x := lvlHP(u)`. -/
def hpBlkS : Stmt := lblk (t, u, j, c, x, g, ti, ix) {
  x := 0;
  g := u >> 28;
  ti := ⟦u⟧.tier;
  ix := ⟦u⟧.idx;
  if ti == 0 || CTL.u64[1] != 0 {
    if g == 4 { if ix < PARAM⟨ti⟩.count { x := 1 } }
    else if g == 1 { if ix < SUCC⟨ti⟩.count { x := SUCC_HP⟨ti, ix⟩ } }
    else if g == 2 { if ix < MAX⟨ti⟩.count { x := MAX_HP⟨ti, ix⟩ } }
    else if g == 3 { if ix < IMAX⟨ti⟩.count { x := IMAX_HP⟨ti, ix⟩ } }
  }
}

/-- `max_push`, `imax_push` (`(t, u, v, j) locals (c, k, x, g, ti, ix, y)`): `x := lvlHP(u)`. -/
def hpBlkM1 : Stmt := lblk (t, u, v, j, c, k, x, g, ti, ix) {
  x := 0;
  g := u >> 28;
  ti := ⟦u⟧.tier;
  ix := ⟦u⟧.idx;
  if ti == 0 || CTL.u64[1] != 0 {
    if g == 4 { if ix < PARAM⟨ti⟩.count { x := 1 } }
    else if g == 1 { if ix < SUCC⟨ti⟩.count { x := SUCC_HP⟨ti, ix⟩ } }
    else if g == 2 { if ix < MAX⟨ti⟩.count { x := MAX_HP⟨ti, ix⟩ } }
    else if g == 3 { if ix < IMAX⟨ti⟩.count { x := IMAX_HP⟨ti, ix⟩ } }
  }
}

/-- The same layout: `y := lvlHP(v)`. -/
def hpBlkM2 : Stmt := lblk (t, u, v, j, c, k, x, g, ti, ix, y) {
  y := 0;
  g := v >> 28;
  ti := ⟦v⟧.tier;
  ix := ⟦v⟧.idx;
  if ti == 0 || CTL.u64[1] != 0 {
    if g == 4 { if ix < PARAM⟨ti⟩.count { y := 1 } }
    else if g == 1 { if ix < SUCC⟨ti⟩.count { y := SUCC_HP⟨ti, ix⟩ } }
    else if g == 2 { if ix < MAX⟨ti⟩.count { y := MAX_HP⟨ti, ix⟩ } }
    else if g == 3 { if ix < IMAX⟨ti⟩.count { y := IMAX_HP⟨ti, ix⟩ } }
  }
}

/-- `const_push` (`(t, f, a, j) locals (c, k, x, g, ti, ix)`): `x := lsHP(a)`. -/
def lsBlkC : Stmt := lblk (t, f, a, j, c, k, x, g, ti, ix) {
  x := 0;
  g := a >> 28;
  ti := ⟦a⟧.tier;
  ix := ⟦a⟧.idx;
  if ti == 0 || CTL.u64[1] != 0 {
    if g == 0 { if ix < LVLS⟨ti⟩.count { x := LS_HP⟨ti, ix⟩ } }
  }
}

/-- `fvar_push` (`(t, u, ty, j) locals (c, k, x, g, ti, ix)`): `x := exprLP(ty)`. -/
def lpBlkF : Stmt := lblk (t, u, ty, j, c, k, x, g, ti, ix) {
  x := 0;
  g := ty >> 28;
  ti := ⟦ty⟧.tier;
  ix := ⟦ty⟧.idx;
  if ti == 0 || CTL.u64[1] != 0 {
    if g == 1 { if ix < FVAR⟨ti⟩.count { x := FVAR_LP⟨ti, ix⟩ } }
    else if g == 2 { if ix < SORT⟨ti⟩.count { x := SORT_LP⟨ti, ix⟩ } }
    else if g == 3 { if ix < CONST⟨ti⟩.count { x := CONST_LP⟨ti, ix⟩ } }
    else if g == 4 { if ix < APP⟨ti⟩.count { x := APP_DER⟨ti, ix⟩ >> 30 } }
    else if g == 5 { if ix < LAM⟨ti⟩.count { x := LAM_DER⟨ti, ix⟩ >> 30 } }
    else if g == 6 { if ix < FORALL⟨ti⟩.count { x := FORALL_DER⟨ti, ix⟩ >> 30 } }
    else if g == 7 { if ix < LET⟨ti⟩.count { x := LET_DER⟨ti, ix⟩ >> 30 } }
    else if g == 9 { if ix < PROJ⟨ti⟩.count { x := PROJ_DER⟨ti, ix⟩ >> 30 } }
  }
}

/-- `ls_push`'s loop body (`(t, o, l, h, j) locals (c, k, x, g, ti, ix, u, q, y)`): `y := lvlHP(u)`. -/
def hpBlkL : Stmt := lblk (t, o, l, h, j, c, k, x, g, ti, ix, u, q, y) {
  y := 0;
  g := u >> 28;
  ti := ⟦u⟧.tier;
  ix := ⟦u⟧.idx;
  if ti == 0 || CTL.u64[1] != 0 {
    if g == 4 { if ix < PARAM⟨ti⟩.count { y := 1 } }
    else if g == 1 { if ix < SUCC⟨ti⟩.count { y := SUCC_HP⟨ti, ix⟩ } }
    else if g == 2 { if ix < MAX⟨ti⟩.count { y := MAX_HP⟨ti, ix⟩ } }
    else if g == 3 { if ix < IMAX⟨ti⟩.count { y := IMAX_HP⟨ti, ix⟩ } }
  }
}

/-- `ls_push`'s loop: `x := x | lvlHP(u)` for each element `u` of the slice `(o, l)`, from `q`. -/
def hpLoopLs : Stmt := lblk (t, o, l, h, j, c, k, x, g, ti, ix, u, q, y) {
  while q < l {
    u := POOL⦃o + q⦄;
    ⟪hpBlkL⟫;
    x := x | y;
    q += 1
  }
}

section blocks
variable (p : Prog) (k : Stmt → M Sig)

theorem hpBlkM1_spec (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p k hpBlkM1
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧
      s'.loc 6 = lvlHPW s₀.mem (s₀.loc 1); ⊤⦄ := by
  simp only [hpBlkM1, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    finish [lvlHPW, tierW, idxW]

theorem hpBlkM2_spec (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p k hpBlkM2
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧
      s'.loc 6 = s₀.loc 6 ∧ s'.loc 10 = lvlHPW s₀.mem (s₀.loc 2); ⊤⦄ := by
  simp only [hpBlkM2, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    finish [lvlHPW, tierW, idxW]

theorem hpBlkL_spec (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p k hpBlkL
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧
      s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = s₀.loc 7 ∧ s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧
      s'.loc 13 = lvlHPW s₀.mem (s₀.loc 11); ⊤⦄ := by
  simp only [hpBlkL, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    finish [lvlHPW, tierW, idxW]

theorem lsBlkC_spec (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p k lsBlkC
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧
      s'.loc 6 = lsHPW s₀.mem (s₀.loc 2); ⊤⦄ := by
  simp only [lsBlkC, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    finish [lsHPW, tierW, idxW]

set_option maxHeartbeats 1000000 in
theorem lpBlkF_spec (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p k lpBlkF
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧
      s'.loc 6 = exprLPW s₀.mem (s₀.loc 2); ⊤⦄ := by
  simp only [lpBlkF, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    finish [exprLPW, tierW, idxW]

/-- One more element of the slice (`k' = q + 1`, as words: `q < l`). -/
theorem lsOrW_step (m : Mem) (o q : Word) (k' : Nat) (hk : k' = q.toNat + 1) :
    lsOrW m o k' = lsOrW m o q.toNat ||| lvlHPW m (prd m (o + q)) := by
  subst hk; simp [lsOrW_succ]

theorem hpLoopLs_spec (n : Nat) (s₀ : St) (hq : s₀.loc 12 ≤ s₀.loc 2)
    (hx : s₀.loc 7 = lsOrW s₀.mem (s₀.loc 1) (s₀.loc 12).toNat) :
    ⦃fun s => s = s₀⦄
    exec p n hpLoopLs
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧
      s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = lsOrW s₀.mem (s₀.loc 1) (s₀.loc 2).toNat; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := hpLoopLs) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, hpBlkL_spec p (exec p n), ih] <;>
      finish [lsOrW_step]

theorem hpLoopLs_step_spec (n : Nat) (s₀ : St) (hq : s₀.loc 12 ≤ s₀.loc 2)
    (hx : s₀.loc 7 = lsOrW s₀.mem (s₀.loc 1) (s₀.loc 12).toNat) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) hpLoopLs
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧
      s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = lsOrW s₀.mem (s₀.loc 1) (s₀.loc 2).toNat; ⊤⦄ :=
  Triple.step_exec (hpLoopLs_spec p (n + 1) s₀ hq hx)

end blocks

/-! ## The tail of every `mk_*` (moved here from `ExprMk.lean`) -/

/-- The sum of a table's two counts `CTL[c] + CTL[c + 1]`. -/
def cnt2 (m : Mem) (c : Word) : Word := rdW (m.arr64 CTL) c + rdW (m.arr64 CTL) (c + 1)

/-- After `intern_*` (from `m` to `m₁`, result `r`): if the table grew (`cnt2` changed from `s`),
write the range `d` at `A[idx * 2 + tier]` of `r` (an `abort` past the array). -/
def derPutW (A : ArrId) (c : Word) (m₁ : Mem) (s r d : Word) : Option Mem :=
  if cnt2 m₁ c = s then some m₁
  else if m₁.len64 (tierA A (tierW r)) ≤ idxW r then none
  else some (m₁.set64 (tierA A (tierW r)) (idxW r) d)

/-- The result of a `mk_*`: `r` and the memory after the tail, or `none`. -/
def mkK (A : ArrId) (c s d : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    match derPutW A c m₁ s r d with
    | none => none
    | some m₂ => some (r, m₂)

theorem mkK_some (A : ArrId) (c s d r : Word) (m₁ : Mem) :
    mkK A c s d (some (r, m₁)) =
      (match derPutW A c m₁ s r d with | none => none | some m₂ => some (r, m₂)) := rfl

end L.Arena
