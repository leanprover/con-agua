import ConAgua.Front.IdTable
import ConAgua.Arena.ImaxStore
import ConAgua.Arena.LevelStore
import ConAgua.Arena.MaxStore
import ConAgua.Arena.NAnonStore
import ConAgua.Arena.NNumStore
import ConAgua.Arena.NStrStore
import ConAgua.Arena.ParamStore
import ConAgua.Arena.ZeroStore
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Layout

/-!
# The parse state's id tables in L: `front_init`, `apply_nstr`, `apply_nnum`, `apply_level`

con-ron's `StateD` (`vendor/con-ron/ConRon/Arena/Frontend/ExportC.lean:99`) maps the export
file's name and level ids to the handles the store interned them at (`IdTable`, a dense array with
a sparse overflow). Here they are `IdTable.lean`'s tables `NID` (64) and `LID` (65): a dense word
array with its size in `CTL`, and a memo-library table for the ids past it.

The functions:
* `name_get(i)`, `level_get(i)`: the handle of a bound id (`StateD.name`/`level`), abort if unset.
* `name_fresh(i)`, `level_fresh(i)`: abort if the id is bound (`StateD.freshName`/`freshLevel`).
* `name_put(i, h)`, `level_put(i, h)`: bind the id (`IdTable.insert`).
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

/-! ## `name_get`, `level_get`, `name_fresh`, `level_fresh`, `name_put`, `level_put` -/

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:113-118 ConRon.Arena.Frontend.StateD.name
con-leche: ConLeche/Frontend/Scan/Types.lean:334-336 ConLeche.Frontend.IdTable.get? -/
def nameGet : FunDecl := tblGetG NID "nsp_find"

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:120-125 ConRon.Arena.Frontend.StateD.level
con-leche: ConLeche/Frontend/Scan/Types.lean:334-336 ConLeche.Frontend.IdTable.get? -/
def levelGet : FunDecl := tblGetG LID "lsp_find"

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:147-152 ConRon.Arena.Frontend.StateD.freshName
con-leche: ConLeche/Frontend/Scan/Types.lean:351-360 ConLeche.Frontend.IdTable.bound -/
def nameFresh : FunDecl := tblFreshG NID "nsp_find"

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:154-157 ConRon.Arena.Frontend.StateD.freshLevel
con-leche: ConLeche/Frontend/Scan/Types.lean:351-360 ConLeche.Frontend.IdTable.bound -/
def levelFresh : FunDecl := tblFreshG LID "lsp_find"

/-- con-leche: ConLeche/Frontend/Scan/Types.lean:338-345 ConLeche.Frontend.IdTable.insert -/
def namePut : FunDecl := tblPutG NID "nsp_find" "nsp_put"

/-- con-leche: ConLeche/Frontend/Scan/Types.lean:338-345 ConLeche.Frontend.IdTable.insert -/
def levelPut : FunDecl := tblPutG LID "lsp_find" "lsp_put"

/-! ## `front_init()` -/

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:490-499 ConRon.Arena.Frontend.StateD.init -/
@[l_impl ConRon.Arena.Frontend.StateD.init]
def frontInit : FunDecl := lfn () locals (h, z) {
  h := call intern_nanon();
  if h >= 4294967296 { abort };
  z := call name_put(0, h);
  h := call intern_zero();
  if h >= 4294967296 { abort };
  z := call level_put(0, h);
  return 0
}

/-- The second half of `front_init`, after name id `0` was bound. -/
def initK : Option Mem → Option Mem
  | some m₁ => putK LID 0 (zinternW m₁)
  | none => none

@[arena_grind =] theorem initK_some (m₁ : Mem) : initK (some m₁) = putK LID 0 (zinternW m₁) := rfl

/-- The model of `front_init`: the memory after, or `none` where the L code aborts. -/
def frontInitW (m : Mem) : Option Mem := initK (putK NID 0 (nainternW m))

/-! ## `apply_nstr(i, pre, o, l)`, `apply_nnum(i, pre, x)` -/

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:166-178 ConRon.Arena.Frontend.parseNameEntryD -/
@[l_impl ConRon.Arena.Frontend.parseNameEntryD]
def applyNStr : FunDecl := lfn (i, pre, o, l) locals (q, z, h) {
  q := call name_get(pre);
  z := call name_fresh(i);
  h := call intern_nstr(q, o, l);
  if h >= 4294967296 { abort };
  z := call name_put(i, h);
  return 0
}

/-- The model of `apply_nstr`. -/
def applyNStrW (m : Mem) (i pre o l : Word) : Option Mem :=
  if tblOK m NID pre = true ∧ tblFresh m NID i = true then
    putK NID i (nsinternW m (tblW m NID pre) o l)
  else none

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:166-178 ConRon.Arena.Frontend.parseNameEntryD -/
@[l_impl ConRon.Arena.Frontend.parseNameEntryD]
def applyNNum : FunDecl := lfn (i, pre, x) locals (q, z, h) {
  q := call name_get(pre);
  z := call name_fresh(i);
  h := call intern_nnum(q, x);
  if h >= 4294967296 { abort };
  z := call name_put(i, h);
  return 0
}

/-- The model of `apply_nnum`. -/
def applyNNumW (m : Mem) (i pre x : Word) : Option Mem :=
  if tblOK m NID pre = true ∧ tblFresh m NID i = true then
    putK NID i (nninternW m (tblW m NID pre) x)
  else none

/-! ## `apply_level(i, k, a, c)` -/

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:180-189 ConRon.Arena.Frontend.parseLevelEntryD -/
@[l_impl ConRon.Arena.Frontend.parseLevelEntryD]
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
  z := call level_put(i, h);
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

section putArms
variable (m m' : Mem) (top vs n j j' : Word)

end putArms

def putLoop : Stmt := lblk (vs, ve, top, n, j, pt, pb) {
  while j < n {
    POOL⟨pt⟩[pb + j] := IN.u8[vs + j];
    j += 1
  }
}

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:166-178 ConRon.Arena.Frontend.parseNameEntryD -/
def strPut : FunDecl := lfn (vs, ve) locals (top, n, j, pt, pb) {
  if ve < vs { abort };
  if len(IN.u8) < ve { abort };
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  n := ve - vs;
  if len(POOL⟨pt⟩) < pb { abort };
  if len(POOL⟨pt⟩) - pb < n { abort };
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
   ("nsp_find", memoFindG (spS NID)), ("nsp_put", memoPutG (spS NID)),
   ("lsp_find", memoFindG (spS LID)), ("lsp_put", memoPutG (spS LID)),
   ("name_get", nameGet), ("level_get", levelGet), ("name_fresh", nameFresh),
   ("level_fresh", levelFresh), ("name_put", namePut), ("level_put", levelPut),
   ("front_init", frontInit), ("apply_nstr", applyNStr),
   ("apply_nnum", applyNNum), ("apply_level", applyLevel), ("str_put", strPut)]

/-- A memory with 75 word arrays of 128 words (all zero) and the input `"abcab"`. -/
def frontMem : Mem :=
  { bytes := #["abcab".toUTF8.data], words := Array.replicate 75 (Array.replicate 128 0) }

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
/- Ids past the dense array (128 words, 256 entries) and out of order go to the sparse map (`rounds_huge_gaps`):
name `3·10^15` = `anon.7`, name `200` = `anon.7.8`, then `130`, `129` below it; a rebound sparse
id aborts. -/
#guard frontRuns frontMem
  [("front_init", []), ("apply_nnum", [3000000000000000, 0, 7]),
   ("apply_nnum", [200, 3000000000000000, 8]), ("apply_nnum", [130, 200, 9]),
   ("apply_nnum", [129, 0, 9]), ("name_get", [3000000000000000]), ("name_get", [200]),
   ("name_get", [130]), ("name_get", [129])] ==
  some [[0], [0], [0], [0], [0], [0x20000000], [0x20000001], [0x20000002], [0x20000003]]
#guard (frontRuns frontMem [("front_init", []), ("apply_nnum", [300, 0, 1]),
  ("apply_nnum", [300, 0, 2])]).isNone
#guard (frontRuns frontMem [("front_init", []), ("name_get", [300])]).isNone
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
  nsp_find : p.lookup "nsp_find" = some (memoFindG (spS NID))
  nsp_put : p.lookup "nsp_put" = some (memoPutG (spS NID))
  lsp_find : p.lookup "lsp_find" = some (memoFindG (spS LID))
  lsp_put : p.lookup "lsp_put" = some (memoPutG (spS LID))
  name_put : p.lookup "name_put" = some namePut
  level_put : p.lookup "level_put" = some levelPut

section specs
variable (p : Prog) (hL : FrontLookups p)
include hL

theorem nameGet_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "name_get" [i]
    ⦃fun r s' => s' = s₀ ∧ tblOK s₀.mem NID i = true ∧ r = [tblW s₀.mem NID i]; ⊤⦄ :=
  tblGetG_spec p NID "nsp_find" hL.nsp_find _ hL.name_get n s₀ i

theorem levelGet_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "level_get" [i]
    ⦃fun r s' => s' = s₀ ∧ tblOK s₀.mem LID i = true ∧ r = [tblW s₀.mem LID i]; ⊤⦄ :=
  tblGetG_spec p LID "lsp_find" hL.lsp_find _ hL.level_get n s₀ i

theorem nameFresh_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "name_fresh" [i]
    ⦃fun _ s' => s' = s₀ ∧ tblFresh s₀.mem NID i = true; ⊤⦄ :=
  tblFreshG_spec p NID "nsp_find" hL.nsp_find _ hL.name_fresh n s₀ i

theorem levelFresh_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "level_fresh" [i]
    ⦃fun _ s' => s' = s₀ ∧ tblFresh s₀.mem LID i = true; ⊤⦄ :=
  tblFreshG_spec p LID "lsp_find" hL.lsp_find _ hL.level_fresh n s₀ i

theorem namePut_spec (n : Nat) (s₀ : St) (i h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "name_put" [i, h]
    ⦃fun _ s' => LocEq s' s₀ ∧ tblPutW s₀.mem NID i h = some s'.mem; ⊤⦄ :=
  tblPutG_spec p NID "nsp_find" "nsp_put" hL.nsp_find hL.nsp_put _ hL.name_put n s₀ i h

theorem levelPut_spec (n : Nat) (s₀ : St) (i h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "level_put" [i, h]
    ⦃fun _ s' => LocEq s' s₀ ∧ tblPutW s₀.mem LID i h = some s'.mem; ⊤⦄ :=
  tblPutG_spec p LID "lsp_find" "lsp_put" hL.lsp_find hL.lsp_put _ hL.level_put n s₀ i h

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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        internNAnon_spec p hL.nanon_find hL.nanon_push hL.intern_nanon n,
        internZero_spec p hL.zero_find hL.zero_push hL.intern_zero n,
        namePut_spec p hL n, levelPut_spec p hL n] <;>
      finish [frontInitW]

theorem applyNStr_spec (hp : p.lookup "apply_nstr" = some applyNStr) (n : Nat) (s₀ : St)
    (i pre o l : Word) (hs : pcap s₀.mem < 2 ^ 64)
    (hb : o.toNat + l.toNat ≤ pcap s₀.mem) :
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
        nameGet_spec p hL n, nameFresh_spec p hL n, namePut_spec p hL n,
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
        nameGet_spec p hL n, nameFresh_spec p hL n, namePut_spec p hL n,
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
        nameGet_spec p hL n, levelGet_spec p hL n, levelFresh_spec p hL n, levelPut_spec p hL n,
        internSucc_spec p hL.succ_find hL.succ_push hL.intern_succ n,
        internMax_spec p hL.max_find hL.max_push hL.intern_max n,
        internImax_spec p hL.imax_find hL.imax_push hL.intern_imax n,
        internParam_spec p hL.param_find hL.param_push hL.intern_param n] <;>
      finish [applyLevelW, levelW]

end specs

section put
variable (p : Prog)

end put

end L.Front
