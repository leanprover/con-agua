import ConAgua.Arena.ArenaRel

/-!
# The parse state's id tables in L: `front_init`, `apply_nstr`, `apply_nnum`, `apply_level`

con-ron's `StateD` (`vendor/con-ron/ConRon/Arena/Frontend/ExportC.lean:99`) maps the export
file's name and level ids to the handles the store interned them at (`IdTable`, a dense array with
a sparse overflow). Here the two tables are dense word arrays:

* `NID` (64): export name id `i` ↦ the name handle word `+ 1`, `0` = unset.
* `LID` (65): export level id `i` ↦ the level handle word `+ 1`, `0` = unset.

Their sizes are fixed by the harness. An id at or past the array's end aborts where the twin would
use its sparse overflow (an `abort` is a defined failure; partial correctness claims nothing).

The functions:
* `name_get(i)`, `level_get(i)`: the handle of a bound id (`StateD.name`/`level`), abort if unset.
* `name_fresh(i)`, `level_fresh(i)`: abort if the id is bound (`StateD.freshName`/`freshLevel`).
* `front_init()`: id `0` of each table is `Name.anonymous` / `Level.zero` (`StateD.init`).
* `apply_nstr(i, pre, o, l)`, `apply_nnum(i, pre, x)`: a name entry (`parseNameEntryD`), the string
  given as the pool slice `(o, l)`.
* `apply_level(i, k, a, c)`: a level entry (`parseLevelEntryD`), `k` = 1 `succ a`, 2 `max a c`,
  3 `imax a c`, 4 `param a` (`a` a name id).
* `str_put(vs, ve)`: copies the input bytes `[vs, ve)` to the pool top, one byte per word (the
  name `str` table's `strWords`), and returns the slice `(o, l)`.

Each spec's post is an equation about a named model (`applyNStrW`, …, `putW`); the facts about the
models (`putW`'s frame and contents) and the refinement are in `StateDR.lean`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open L.Arena

namespace L.Front

/-- Export name id ↦ name handle word `+ 1`. -/
abbrev NID : ArrId := 64
/-- Export level id ↦ level handle word `+ 1`. -/
abbrev LID : ArrId := 65
/-- Export expression id ↦ expression handle word `+ 1` (`ConAgua.Front.ApplyExpr`). -/
abbrev EID : ArrId := 66
/-- The input buffer (byte array 0). -/
abbrev IN : ArrId := 0

/-! ## Models of the table reads -/

/-- Entry `i` of table `b` is bound: in range and nonzero. -/
def tblOK (m : Mem) (b : ArrId) (i : Word) : Bool :=
  decide (i < m.len64 b) && rdW (m.arr64 b) i != 0

/-- Entry `i` of table `b` is unbound and in range. -/
def tblFresh (m : Mem) (b : ArrId) (i : Word) : Bool :=
  decide (i < m.len64 b) && rdW (m.arr64 b) i == 0

/-- The handle word entry `i` of table `b` holds. -/
def tblW (m : Mem) (b : ArrId) (i : Word) : Word := rdW (m.arr64 b) i - 1

/-- After an interning returned `(h, m')`: entry `i` of table `b` is `h + 1` (`h` must be a
32-bit handle, `i` in range). -/
def putK (b : ArrId) (i : Word) : Option (Word × Mem) → Option Mem
  | some (h, m') =>
    if h < 0x100000000 ∧ i.toNat < (m'.arr64 b).size then some (m'.set64 b i (h + 1)) else none
  | none => none

@[arena_grind =] theorem putK_none (b : ArrId) (i : Word) : putK b i none = none := rfl
@[arena_grind =] theorem putK_some (b : ArrId) (i h : Word) (m' : Mem) :
    putK b i (some (h, m')) =
      if h < 0x100000000 ∧ i.toNat < (m'.arr64 b).size then some (m'.set64 b i (h + 1)) else none :=
  rfl

/-! ## `name_get`, `level_get`, `name_fresh`, `level_fresh` -/

def nameGet : FunDecl := lfn (i) locals (e) {
  if len(NID.u64) <= i { abort };
  e := NID.u64[i];
  if e == 0 { abort };
  return e - 1
}

def levelGet : FunDecl := lfn (i) locals (e) {
  if len(LID.u64) <= i { abort };
  e := LID.u64[i];
  if e == 0 { abort };
  return e - 1
}

def nameFresh : FunDecl := lfn (i) {
  if len(NID.u64) <= i { abort };
  if NID.u64[i] != 0 { abort };
  return 0
}

def levelFresh : FunDecl := lfn (i) {
  if len(LID.u64) <= i { abort };
  if LID.u64[i] != 0 { abort };
  return 0
}

/-! ## `front_init()` -/

def frontInit : FunDecl := lfn () locals (h) {
  h := call intern_nanon();
  if h >= 4294967296 { abort };
  if len(NID.u64) == 0 { abort };
  NID.u64[0] := h + 1;
  h := call intern_zero();
  if h >= 4294967296 { abort };
  if len(LID.u64) == 0 { abort };
  LID.u64[0] := h + 1;
  return 0
}

/-- The second half of `front_init`, after `NID[0]` was written. -/
def initK : Option Mem → Option Mem
  | some m₁ => putK LID 0 (zinternW m₁)
  | none => none

@[arena_grind =] theorem initK_none : initK none = none := rfl
@[arena_grind =] theorem initK_some (m₁ : Mem) : initK (some m₁) = putK LID 0 (zinternW m₁) := rfl

/-- The model of `front_init`: the memory after, or `none` where the L code aborts. -/
def frontInitW (m : Mem) : Option Mem := initK (putK NID 0 (nainternW m))

/-! ## `apply_nstr(i, pre, o, l)`, `apply_nnum(i, pre, x)` -/

def applyNStr : FunDecl := lfn (i, pre, o, l) locals (q, z, h) {
  q := call name_get(pre);
  z := call name_fresh(i);
  h := call intern_nstr(q, o, l);
  if h >= 4294967296 { abort };
  NID.u64[i] := h + 1;
  return 0
}

/-- The model of `apply_nstr`. -/
def applyNStrW (m : Mem) (i pre o l : Word) : Option Mem :=
  if tblOK m NID pre = true ∧ tblFresh m NID i = true then
    putK NID i (nsinternW m (tblW m NID pre) o l)
  else none

def applyNNum : FunDecl := lfn (i, pre, x) locals (q, z, h) {
  q := call name_get(pre);
  z := call name_fresh(i);
  h := call intern_nnum(q, x);
  if h >= 4294967296 { abort };
  NID.u64[i] := h + 1;
  return 0
}

/-- The model of `apply_nnum`. -/
def applyNNumW (m : Mem) (i pre x : Word) : Option Mem :=
  if tblOK m NID pre = true ∧ tblFresh m NID i = true then
    putK NID i (nninternW m (tblW m NID pre) x)
  else none

/-! ## `apply_level(i, k, a, c)` -/

def applyLevel : FunDecl := lfn (i, k, a, c) locals (u, v, h, z) {
  z := call level_fresh(i);
  if k == 1 {
    u := call level_get(a);
    h := call intern_succ(u)
  } else if k == 2 {
    u := call level_get(a);
    v := call level_get(c);
    h := call intern_max(u, v)
  } else if k == 3 {
    u := call level_get(a);
    v := call level_get(c);
    h := call intern_imax(u, v)
  } else if k == 4 {
    u := call name_get(a);
    h := call intern_param(u)
  } else { abort };
  if h >= 4294967296 { abort };
  LID.u64[i] := h + 1;
  return 0
}

/-- The interning of `apply_level`, per kind `k`. -/
def levelW (m : Mem) (k a c : Word) : Option (Word × Mem) :=
  if k = 1 then
    if tblOK m LID a = true then sinternW m (tblW m LID a) else none
  else if k = 2 then
    if tblOK m LID a = true ∧ tblOK m LID c = true then minternW m (tblW m LID a) (tblW m LID c)
    else none
  else if k = 3 then
    if tblOK m LID a = true ∧ tblOK m LID c = true then iminternW m (tblW m LID a) (tblW m LID c)
    else none
  else if k = 4 then
    if tblOK m NID a = true then pinternW m (tblW m NID a) else none
  else none

/-- The model of `apply_level`. -/
def applyLevelW (m : Mem) (i k a c : Word) : Option Mem :=
  if tblFresh m LID i = true then putK LID i (levelW m k a c) else none

/-! ## `str_put(vs, ve)` -/

/-- Byte `x` of a byte array, as a word (`0` out of range). -/
def rdB (a : Array UInt8) (x : Word) : Word := (a[x.toNat]?.getD 0).toUInt64

/-- The model of the copy loop: the memory after copying bytes `vs + j ‥ vs + n` of the input to
`POOL[top + j ‥ top + n]`. -/
def putW (m : Mem) (top vs n j : Word) : Mem :=
  if j < n then putW (m.set64 POOL (top + j) (rdB (m.arr8 IN) (vs + j))) top vs n (j + 1) else m
termination_by n.toNat - j.toNat
decreasing_by
  have : j.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹j < n›
  have := n.toNat_lt
  have : (j + 1).toNat = j.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section putArms
variable (m m' : Mem) (top vs n j j' : Word)

theorem putW_end (hj : ¬ j < n) : putW m top vs n j = m := by
  rw [putW]; simp only [hj, ↓reduceIte]

theorem putW_step (k : Nat) (hj : j < n) (hk : k = (vs + j).toNat) (hks : k < (m.arr8 IN).size)
    (hj' : j' = j + 1) (hm' : m' = m.set64 POOL (top + j) (m.arr8 IN)[k].toUInt64) :
    putW m top vs n j = putW m' top vs n j' := by
  subst hj' hm' hk
  rw [putW]; simp only [hj, ↓reduceIte, rdB, hks, getElem?_pos, Option.getD_some]

end putArms

grind_pattern [arena_grind] putW_end => putW m top vs n j
grind_pattern [arena_grind] putW_step => putW m top vs n j, (m.arr8 IN)[k], putW m' top vs n j'

def putLoop : Stmt := lblk (vs, ve, top, n, j) {
  while j < n {
    POOL.u64[top + j] := IN.u8[vs + j];
    j += 1
  }
}

def strPut : FunDecl := lfn (vs, ve) locals (top, n, j) {
  if ve < vs { abort };
  if len(IN.u8) < ve { abort };
  top := CTL.u64[0];
  n := ve - vs;
  if len(POOL.u64) < top { abort };
  if len(POOL.u64) - top < n { abort };
  ⟪putLoop⟫;
  CTL.u64[0] := top + n;
  return (top, n)
}

/-! ## The program -/

/-- The front functions with the store functions they call, as one `#eval`-able program. -/
def frontProg : Prog :=
  [("nanon_find", nanonFind), ("nanon_push", nanonPush), ("intern_nanon", internNAnon),
   ("zero_find", zeroFind), ("zero_push", zeroPush), ("intern_zero", internZero),
   ("lit_hash", litHash), ("limbs_eq", limbsEq), ("nstr_match", nsMatch), ("nstr_find", nsFind),
   ("nstr_push", nsPush), ("intern_nstr", internNStr),
   ("nnum_find", nnumFind), ("nnum_push", nnumPush), ("intern_nnum", internNNum),
   ("succ_find", succFind), ("succ_push", succPush), ("intern_succ", internSucc),
   ("max_find", maxFind), ("max_push", maxPush), ("intern_max", internMax),
   ("imax_find", imaxFind), ("imax_push", imaxPush), ("intern_imax", internImax),
   ("param_find", paramFind), ("param_push", paramPush), ("intern_param", internParam),
   ("name_get", nameGet), ("level_get", levelGet), ("name_fresh", nameFresh),
   ("level_fresh", levelFresh), ("front_init", frontInit), ("apply_nstr", applyNStr),
   ("apply_nnum", applyNNum), ("apply_level", applyLevel), ("str_put", strPut)]

/-- A memory with every word array 64 words (all zero) and the input `"abcab"`. -/
def frontMem : Mem :=
  { bytes := #["abcab".toUTF8.data], words := Array.replicate 66 (Array.replicate 64 0) }

/-- Run the calls in turn; the results. -/
def frontRuns (m : Mem) : List (FnName × List Word) → Option (List (List Word))
  | [] => some []
  | (f, vs) :: xs => match run frontProg 200 f vs m with
    | .ok (r, m') => (frontRuns m' xs).map (r :: ·)
    | .error _ => none

/- The names `abc` (1), `ab` (2) (`str_put` copies `"abc"` to pool slice `(0, 3)`, then `"ab"` to
`(3, 2)`), `abc.7` (3), the levels `succ zero` (1), `param abc.7` (2), `max 1 2` (3); then the
handles of names 0‥3 and levels 0‥3 (tag in bits 28‥31, tier bit 27). -/
#guard frontRuns frontMem
  [("front_init", []), ("str_put", [0, 3]), ("apply_nstr", [1, 0, 0, 3]), ("str_put", [3, 5]),
   ("apply_nstr", [2, 0, 3, 2]), ("apply_nnum", [3, 1, 7]), ("apply_level", [1, 1, 0, 0]),
   ("apply_level", [2, 4, 3, 0]), ("apply_level", [3, 2, 1, 2]),
   ("name_get", [0]), ("name_get", [1]), ("name_get", [2]), ("name_get", [3]),
   ("level_get", [0]), ("level_get", [1]), ("level_get", [2]), ("level_get", [3])] ==
  some [[0], [0, 3], [0], [3, 2], [0], [0], [0], [0], [0],
    [0], [0x10000000], [0x10000001], [0x20000000],
    [0], [0x10000000], [0x40000000], [0x20000000]]

/- A rebound id aborts, an unbound one aborts, an unknown level kind aborts. -/
#guard (frontRuns frontMem [("front_init", []), ("apply_nnum", [0, 0, 1])]).isNone
#guard (frontRuns frontMem [("front_init", []), ("apply_nnum", [1, 2, 1])]).isNone
#guard (frontRuns frontMem [("front_init", []), ("apply_level", [1, 5, 0, 0])]).isNone
/- `str_put` past the input's end aborts. -/
#guard (frontRuns frontMem [("str_put", [3, 6])]).isNone

/-! ## The specs -/

/-- Every function the front functions call, at its name in `p`. -/
structure FrontLookups (p : Prog) : Prop where
  nanon_find : p.lookup "nanon_find" = some nanonFind
  nanon_push : p.lookup "nanon_push" = some nanonPush
  intern_nanon : p.lookup "intern_nanon" = some internNAnon
  zero_find : p.lookup "zero_find" = some zeroFind
  zero_push : p.lookup "zero_push" = some zeroPush
  intern_zero : p.lookup "intern_zero" = some internZero
  lit_hash : p.lookup "lit_hash" = some litHash
  limbs_eq : p.lookup "limbs_eq" = some limbsEq
  nstr_match : p.lookup "nstr_match" = some nsMatch
  nstr_find : p.lookup "nstr_find" = some nsFind
  nstr_push : p.lookup "nstr_push" = some nsPush
  intern_nstr : p.lookup "intern_nstr" = some internNStr
  nnum_find : p.lookup "nnum_find" = some nnumFind
  nnum_push : p.lookup "nnum_push" = some nnumPush
  intern_nnum : p.lookup "intern_nnum" = some internNNum
  succ_find : p.lookup "succ_find" = some succFind
  succ_push : p.lookup "succ_push" = some succPush
  intern_succ : p.lookup "intern_succ" = some internSucc
  max_find : p.lookup "max_find" = some maxFind
  max_push : p.lookup "max_push" = some maxPush
  intern_max : p.lookup "intern_max" = some internMax
  imax_find : p.lookup "imax_find" = some imaxFind
  imax_push : p.lookup "imax_push" = some imaxPush
  intern_imax : p.lookup "intern_imax" = some internImax
  param_find : p.lookup "param_find" = some paramFind
  param_push : p.lookup "param_push" = some paramPush
  intern_param : p.lookup "intern_param" = some internParam
  name_get : p.lookup "name_get" = some nameGet
  level_get : p.lookup "level_get" = some levelGet
  name_fresh : p.lookup "name_fresh" = some nameFresh
  level_fresh : p.lookup "level_fresh" = some levelFresh

theorem frontProg_lookups : FrontLookups frontProg := by
  constructor <;> rfl

section specs
variable (p : Prog) (hL : FrontLookups p)
include hL

theorem nameGet_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "name_get" [i]
    ⦃fun r s' => s' = s₀ ∧ tblOK s₀.mem NID i = true ∧ r = [tblW s₀.mem NID i]; ⊤⦄ := by
  rw [invoke_eq _ hL.name_get]
  simp only [callFn, nameGet]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64] <;> finish [tblOK, tblW]

theorem levelGet_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "level_get" [i]
    ⦃fun r s' => s' = s₀ ∧ tblOK s₀.mem LID i = true ∧ r = [tblW s₀.mem LID i]; ⊤⦄ := by
  rw [invoke_eq _ hL.level_get]
  simp only [callFn, levelGet]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64] <;> finish [tblOK, tblW]

theorem nameFresh_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "name_fresh" [i]
    ⦃fun _ s' => s' = s₀ ∧ tblFresh s₀.mem NID i = true; ⊤⦄ := by
  rw [invoke_eq _ hL.name_fresh]
  simp only [callFn, nameFresh]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64] <;> finish [tblFresh]

theorem levelFresh_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "level_fresh" [i]
    ⦃fun _ s' => s' = s₀ ∧ tblFresh s₀.mem LID i = true; ⊤⦄ := by
  rw [invoke_eq _ hL.level_fresh]
  simp only [callFn, levelFresh]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64] <;> finish [tblFresh]

theorem frontInit_spec (hp : p.lookup "front_init" = some frontInit) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "front_init" []
    ⦃fun _ s' => LocEq s' s₀ ∧ frontInitW s₀.mem = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, frontInit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64,
        internNAnon_spec p hL.nanon_find hL.nanon_push hL.intern_nanon n,
        internZero_spec p hL.zero_find hL.zero_push hL.intern_zero n] <;>
      finish [frontInitW]

theorem applyNStr_spec (hp : p.lookup "apply_nstr" = some applyNStr) (n : Nat) (s₀ : St)
    (i pre o l : Word) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64)
    (hb : o.toNat + l.toNat ≤ (s₀.mem.arr64 POOL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_nstr" [i, pre, o, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ applyNStrW s₀.mem i pre o l = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, applyNStr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64,
        nameGet_spec p hL n, nameFresh_spec p hL n,
        internNStr_spec p hL.lit_hash hL.limbs_eq hL.nstr_match hL.nstr_find hL.nstr_push
          hL.intern_nstr n] <;>
      finish [applyNStrW]

theorem applyNNum_spec (hp : p.lookup "apply_nnum" = some applyNNum) (n : Nat) (s₀ : St)
    (i pre x : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_nnum" [i, pre, x]
    ⦃fun _ s' => LocEq s' s₀ ∧ applyNNumW s₀.mem i pre x = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, applyNNum]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64,
        nameGet_spec p hL n, nameFresh_spec p hL n,
        internNNum_spec p hL.nnum_find hL.nnum_push hL.intern_nnum n] <;>
      finish [applyNNumW]

theorem applyLevel_spec (hp : p.lookup "apply_level" = some applyLevel) (n : Nat) (s₀ : St)
    (i k a c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_level" [i, k, a, c]
    ⦃fun _ s' => LocEq s' s₀ ∧ applyLevelW s₀.mem i k a c = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, applyLevel]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64,
        nameGet_spec p hL n, levelGet_spec p hL n, levelFresh_spec p hL n,
        internSucc_spec p hL.succ_find hL.succ_push hL.intern_succ n,
        internMax_spec p hL.max_find hL.max_push hL.intern_max n,
        internImax_spec p hL.imax_find hL.imax_push hL.intern_imax n,
        internParam_spec p hL.param_find hL.param_push hL.intern_param n] <;>
      finish [applyLevelW, levelW]

end specs

section put
variable (p : Prog)

theorem putLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n putLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
      s'.mem = putW s₀.mem (s₀.loc 2) (s₀.loc 0) (s₀.loc 3) (s₀.loc 4); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := putLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, ld8, st64, ih] <;> finish

theorem putLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) putLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
      s'.mem = putW s₀.mem (s₀.loc 2) (s₀.loc 0) (s₀.loc 3) (s₀.loc 4); ⊤⦄ :=
  Triple.step_exec (putLoop_spec p (n + 1) s₀)

/-- `str_put`'s checks: a range of the input that fits above the pool top. -/
def strPutOK (m : Mem) (vs ve : Word) : Prop :=
  vs ≤ ve ∧ ve ≤ m.len8 IN ∧ m.top ≤ m.len64 POOL ∧ ve - vs ≤ m.len64 POOL - m.top

theorem strPut_specW (hp : p.lookup "str_put" = some strPut) (n : Nat) (s₀ : St) (vs ve : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "str_put" [vs, ve]
    ⦃fun r s' => LocEq s' s₀ ∧ strPutOK s₀.mem vs ve ∧ r = [s₀.mem.top, ve - vs] ∧
      s'.mem = (putW s₀.mem s₀.mem.top vs (ve - vs) 0).set64 CTL 0 (s₀.mem.top + (ve - vs)); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strPut]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64, putLoop_step_spec p n] <;>
      finish [strPutOK]

end put

end L.Front
