module

public import ConAgua.Arena.ErecVocab
public import ConRon.Arena.Inductives.GenRec
meta import ConAgua.Arena.Tiers
meta import ConRon.Arena.Inductives.GenRec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The inductive stage in L: the interface (lane `induct`)

The twin's inductive route (`vendor/con-ron/ConRon/Arena/Inductives/**`, phase 8, and
`checkDecl`'s `.indDecl` arm) threads rich values: lists of handles, records (`BlockShape`,
`MemberShape`, `NestCtx`, `TargetMajor`, …), lists of lists, sums (`ClassSlot`,
`NestFieldKind`). This file fixes how they live in L memory, how the L functions call each
other, and the not-yet-translated callees (**stubs**) with their specs (stated, proved by
`sorry`, listed in DESIGN.md). The L code is in `IndParts`, `IndInstall`, `IndSum`, `IndPos*`,
`RecClass`, `RecGen`, `RecCheck` (one file per twin module group).

## Conventions

* **Mode and fuels.** L implements `CheckMode.verified` only (the final theorem's mode). The knot
  fuel `checkFuel` is not passed (the core's callees own it). `coreWalkFuel` (`4·10^9`) and the
  positivity walk's fuels are explicit word arguments, decremented where the twin decrements
  them; the constant is `CWF`.
* **Errors.** Every twin `fail` (`.invalid`, `.notImplemented`, `.internal`, a dangling handle)
  is an `abort` (`fail R` with the twin's message as the reason `R` where the twin rejects or
  declines, `Arena/Reasons.lean`).
* **Handles** are words below `2^32` (`decI`).
* **Environments.** The memory holds one environment (`EnvR`, lane `pinsenv`); a twin `fe : IFEnv`
  argument is the **view word** `vis` (`fe.visibleBelow`), and a function returning an `IFEnv`
  returns the new view word. `fe.restrictTo k` is the view `k`. A lookup is
  `env_find(w, vis)` → `(found, q)`; a push writes a constant record into `EREC` and calls
  `env_push(vis, q)` → `vis + 1`.
* **The work pool `IW`** (word array 200, top `CTL[200]`): every composite value the stage builds
  lives here, bump-allocated by `iw_alloc(n)` → offset; nothing is freed (`iw_reset()` at the
  stage's entry). Values are immutable once built: a functional update allocates a new record.
* **Lists** are slices `(off, len)` of `IW` (two words wherever a list is passed, returned or
  stored); element `j` is `IW[off + j]`, a word. A list of handles or numbers holds them; a list
  of composite values holds **pointers** (`IW` offsets) to records. `take n` is `(off, min len n)`,
  `drop n` is `(off + n, len - n)` (no copy); `++` copies (`sl_append`).
* **Constants** (`IConstantVal`) are pointers `q` into `EREC` (4 words: name, `lps.off`,
  `lps.len`, type; the `lps` slice is in `EREC`, lane `pinsenv`'s layout, `decCV`). A new constant
  value (`{cv with type := t}`, a generated recursor) is allocated in `EREC` by `erec_alloc(n)`
  (top `CTL[129]`). `er_to_iw(off, len)` copies an `EREC` slice (a constant's level parameters,
  an inductive block's record pointers) into `IW`: **every list a function takes is an `IW`
  slice.**
* **`Option α`** is two words `(ok, v)` (`ok ∈ {0, 1}`; `v` meaningless at `0`); an `Option` of a
  pair or of a list returns `(ok, …)` with the components after the flag. `Bool` is `0`/`1`.
  `Option Bool` from the level algorithms is the word `0` (none), `1` (false), `2` (true).
* **At most 6 result words** (the compiler's `maxRes`).

## The records in `IW` (offsets from the record pointer)

| twin type | words |
|---|---|
| `IConstantVal × Nat` (a constructor with its field count) | `[cv, nF]` (`cv` an `EREC` pointer) |
| `MemberShape` | `[cvT, nIdx, ctors.off, ctors.len, declared]` (ctors: pointers to `[cv, nF]`; `cvT` the former at its telescope, `declared` as the stream declares it, both `EREC` pointers) |
| `RecShape` | `[cvR, rP, mI, tgt, rules.off, rules.len, isK]` (rules: the record's `EREC` slice of 11-word rules) |
| `BlockShape` | `[members.off, members.len, recs.off, recs.len, nP, elim, resSort, large, isProp]` |
| `NestCtx` | `[names.off, names.len, lps.off, lps.len, nP, nIdxs.off, nIdxs.len, params.off, params.len, sort, lvls, formers.off, formers.len]` (formers: `EREC` pointers) |
| `NestKey`, `ClassKey` | `[name, lvls, ds.off, ds.len]` |
| `NestHole` | `[key, base, nIdx]` (`key` a `NestKey` pointer) |
| `NestCtorNf` | `[ctor, lvls, ds.off, ds.len, ty]` |
| `NestState` | `[keys.off, keys.len, active.off, active.len, nfs.off, nfs.len]` (keys/active: `NestKey` pointers; nfs: `NestCtorNf` pointers) |
| `ClassSlot` | `.motive key`: `[0, key]`; `.minor cls ctor ihs`: `[1, cls, ctor, ihs.off, ihs.len]` (ihs: pointers to `[field, cls]`) |
| `ClassRead` | `[slots.off, slots.len, recCls.off, recCls.len]` |
| `TargetMajor` | `[ind, lvls, ds.off, ds.len, nPc, nIdx, ctors.off, ctors.len, member, nfs.off, nfs.len, pfvs.off, pfvs.len]` (`member`: `0` none, `t + 1` some `t`) |
| `ClassField` | `[0]` ordinary, `[1, cls, tele]` recursive |
| `ClassCtor` | `[cv, nF, kinds.off, kinds.len, tyD, tyN]` |
| `ClassGen` | `[nP, params.off, params.len, cls.off, cls.len, formerTys.off, formerTys.len, slots.off, slots.len, ctors.off, ctors.len, elim, pre.off, pre.len]` (ctors: pointers to list headers) |
| `List α` as an element | a pointer to a 2-word header `[off, len]` |
| `BlockPass` | `[env1, p, kinds.off, kinds.len, params.off, params.len, rd, cls.off, cls.len, tbl.off, tbl.len]` |
| `IConstantVal × TargetMajor × List EIdx` | `[cv, M, rhss.off, rhss.len]` |
| `NIdx × Option IConstantInfo` (a displaced env row) | `[name, c, q]` (the own layer's raw row: counter `+ 1` or `0`, record) |

`NestFieldKind` is one word: `.ordinary` `0`, `.recursive t` `1 + 8 t`, `.reflexive t` `2 + 8 t`,
`.inProgress` `3`, `.nested r` `4 + 8 r` (`r ∈ {0, 1}`). `IIndCaps` and `IRecRule` are `EREC`
records (lane `pinsenv`'s `decCaps`, `decRule`).

## Arrays and `CTL` words (lane `induct`)

`IW` = 200 (`CTL[200]` its top). The per-call walk memos (`MemoLib` schemas, four words a slot):
`MAM` 201 (`mentionsAnyGo`, `CTL[202]`), `NOM` 202 (`nestOccGo`, `CTL[204]`), `DPM` 203 (`depthGo`,
`CTL[206]`), `RFM` 204 (`replaceFVarsGo`, banked: `CTL[208]`, bank counters `CTL[218]`, `[219]`),
`RAM` 205 (`replaceAppsGo`, `CTL[210]`), `TAM` 206 (`targetAbsGo`, `CTL[212]`), `HBM` 207
(`hasLooseBVarBGo`, `CTL[214]`), `MCM` 208 (`mentionsConstGo`, `CTL[216]`). A walk's top call
clears its memo (the twin's fresh `∅`); `replaceFVars` nests inside itself (`nestHoleImg`), so it
enters a fresh bank instead and leaves it on return (lane `libs`' `MemoBank`): `s := call
rf_bank_enter()` … `u := call rf_bank_leave(s)`, its keys `(h, g << 32)` with `g = CTL[219]` the
current generation. A memo hit's value is `X.u64[j * 4 + 3]` (`(fd, j, d) := call X_find(k1, k2)`,
then `u := call X_put(k1, k2, v, fd, j)` after probing again if the walk recursed since).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

/-! ## Arrays -/

/-- The memo schemas. -/
def maSch : MemoSch := ⟨MAM, 202⟩
def noSch : MemoSch := ⟨NOM, 204⟩
def dpSch : MemoSch := ⟨DPM, 206⟩
def rfSch : MemoSch := ⟨RFM, 208⟩
def raSch : MemoSch := ⟨RAM, 210⟩
def taSch : MemoSch := ⟨TAM, 212⟩
def hbSch : MemoSch := ⟨HBM, 214⟩
def mcSch : MemoSch := ⟨MCM, 216⟩

/-- `coreWalkFuel` as a word. -/
def CWF : Word := 4000000000

theorem CWF_eq : CWF.toNat = coreWalkFuel := by decide

/-- `fuelSlack` as a word. -/
def SLACK : Word := 1024

/-! ## Decoders: the value relations of the stage's records

Each reads the memory `m` (`IW` and, for constants, `EREC`) and is `Option`-valued; `decX m p = some
x` says the record at `p` denotes `x`. Lists: `decL` (words), `decHL` (handles), `decNL` (numbers),
`decPL f` (pointers to records decoded by `f`). -/

section dec
variable (m : Mem)

/-- The work pool. -/
def iwA : Nat → Option Word := aread (m.arr64 IW)

/-- Word `i` of `IW`, a number. -/
def iwN (i : Nat) : Option Nat := nat? (iwA m) i
/-- Word `i` of `IW`, a `Bool`. -/
def iwB (i : Nat) : Option Bool := bool? (iwA m) i
/-- Word `i` of `IW`, a handle. -/
def iwH {k : IdxKind} (i : Nat) : Option (Idx k) := hd? (iwA m) i

/-- A slice of `IW` handles. -/
def decHL {k : IdxKind} (o l : Nat) : Option (List (Idx k)) := hslice? (iwA m) o l

/-- A slice of `IW` numbers. -/
def decNL (o l : Nat) : Option (List Nat) := (List.range l).mapM fun j => iwN m (o + j)

/-- A slice of `IW` pointers, each decoded by `f`. -/
def decPL {α : Type} (f : Nat → Option α) (o l : Nat) : Option (List α) :=
  (List.range l).mapM fun j => do f (← iwN m (o + j))

/-- The list whose `(off, len)` is at words `i`, `i + 1` of `IW`, decoded by `g`. -/
def decAt {α : Type} (g : Nat → Nat → Option (List α)) (i : Nat) : Option (List α) := do
  g (← iwN m i) (← iwN m (i + 1))

/-- A constant: an `EREC` pointer. -/
def decCVp (q : Nat) : Option IConstantVal := decCV (erA m) q

/-- `[cv, nF]`. -/
def decCN (p : Nat) : Option (IConstantVal × Nat) := do
  pure (← decCVp m (← iwN m p), ← iwN m (p + 1))

/-- `MemberShape`: `cvT` (an `EREC` pointer), `nIdx`, the constructors' slice, `declared` (an
`EREC` pointer) at `p + 4`. -/
def decMS (p : Nat) : Option MemberShape := do
  pure ⟨← decCVp m (← iwN m p), ← decCVp m (← iwN m (p + 4)), ← iwN m (p + 1),
    ← decAt m (decPL m (decCN m)) (p + 2)⟩

/-- `RecShape`: `cvR` (an `EREC` pointer), `rP`, `mI`, `tgt`, the rules (the stored recursor's
`EREC` slice of 11-word rule records, `(off, cnt)` at `p + 4`, `p + 5`), `isK` at `p + 6`. -/
def decRS (p : Nat) : Option RecShape := do
  pure ⟨← decCVp m (← iwN m p), ← iwN m (p + 1), ← iwN m (p + 2), ← iwN m (p + 3),
    ← decRules (erA m) (← iwN m (p + 4)) (← iwN m (p + 5)), ← iwB m (p + 6)⟩

/-- `BlockShape`. -/
def decBS (p : Nat) : Option BlockShape := do
  pure ⟨← decAt m (decPL m (decMS m)) p, ← decAt m (decPL m (decRS m)) (p + 2), ← iwN m (p + 4),
    ← iwH m (p + 5), ← iwH m (p + 6), ← iwB m (p + 7), ← iwB m (p + 8)⟩

/-- `NestCtx`: … `sort` at `p + 9`, `lvls` at `p + 10`, the formers (a slice of `EREC` pointers)
at `p + 11`, `p + 12`. -/
def decCtx (p : Nat) : Option NestCtx := do
  pure ⟨← decAt m (decHL m) p, ← decAt m (decHL m) (p + 2), ← iwN m (p + 4),
    ← decAt m (decNL m) (p + 5), ← decAt m (decHL m) (p + 7), ← iwH m (p + 9),
    ← decAt m (decPL m (decCVp m)) (p + 11), ← iwH m (p + 10)⟩

/-- `NestKey`. -/
def decNK (p : Nat) : Option NestKey := do
  pure ⟨← iwH m p, ← iwH m (p + 1), ← decAt m (decHL m) (p + 2)⟩

/-- `ClassKey` (the same layout). -/
def decCK (p : Nat) : Option ClassKey := do
  pure ⟨← iwH m p, ← iwH m (p + 1), ← decAt m (decHL m) (p + 2)⟩

/-- `NestHole`: the key (a pointer), `base`, `nIdx`. -/
def decNH (p : Nat) : Option NestHole := do
  pure ⟨← decNK m (← iwN m p), ← iwN m (p + 1), ← iwN m (p + 2)⟩

/-- `NestCtorNf`. -/
def decNCN (p : Nat) : Option NestCtorNf := do
  pure ⟨← iwH m p, ← iwH m (p + 1), ← decAt m (decHL m) (p + 2), ← iwH m (p + 4)⟩

/-- `NestState`. -/
def decNS (p : Nat) : Option NestState := do
  pure ⟨(← decAt m (decPL m (decNK m)) p).toArray, ← decAt m (decPL m (decNK m)) (p + 2),
    (← decAt m (decPL m (decNCN m)) (p + 4)).toArray⟩

/-- `NestFieldKind`, one word. -/
def decNFK (w : Word) : Option NestFieldKind :=
  let t := w.toNat % 8
  let x := w.toNat / 8
  match t with
  | 0 => if x = 0 then some .ordinary else none
  | 1 => some (.recursive x)
  | 2 => some (.reflexive x)
  | 3 => if x = 0 then some .inProgress else none
  | 4 => if x ≤ 1 then some (.nested (x == 1)) else none
  | _ => none

/-- A slice of `NestFieldKind` words. -/
def decKL (o l : Nat) : Option (List NestFieldKind) :=
  (List.range l).mapM fun j => do decNFK (← iwA m (o + j))

/-- A `(Nat × Nat)` record. -/
def decNN (p : Nat) : Option (Nat × Nat) := do pure (← iwN m p, ← iwN m (p + 1))

/-- `ClassSlot`. -/
def decCS (p : Nat) : Option ClassSlot := do
  match ← iwN m p with
  | 0 => pure (.motive (← decCK m (← iwN m (p + 1))))
  | 1 => pure (.minor (← iwN m (p + 1)) (← iwH m (p + 2)) (← decAt m (decPL m (decNN m)) (p + 3)))
  | _ => none

/-- `ClassRead`. -/
def decCR (p : Nat) : Option ClassRead := do
  pure ⟨← decAt m (decPL m (decCS m)) p, ← decAt m (decNL m) (p + 2)⟩

/-- `Option Nat` as `0` / `t + 1`. -/
def decON (w : Nat) : Option Nat := if w = 0 then none else some (w - 1)

/-- `TargetMajor`. -/
def decTM (p : Nat) : Option TargetMajor := do
  pure { ind := ← iwH m p, lvls := ← iwH m (p + 1), ds := ← decAt m (decHL m) (p + 2),
         nPc := ← iwN m (p + 4), nIdx := ← iwN m (p + 5),
         ctors := ← decAt m (decPL m (decCN m)) (p + 6), member := decON (← iwN m (p + 8)),
         nfs := ← decAt m (decPL m (decNCN m)) (p + 9), pfvs := ← decAt m (decHL m) (p + 11) }

/-- `ClassField`. -/
def decCF (p : Nat) : Option ClassField := do
  match ← iwN m p with
  | 0 => pure .ordinary
  | 1 => pure (.recursive (← iwN m (p + 1)) (← iwN m (p + 2)))
  | _ => none

/-- `ClassCtor`. -/
def decCC (p : Nat) : Option ClassCtor := do
  pure ⟨← decCVp m (← iwN m p), ← iwN m (p + 1), ← decAt m (decPL m (decCF m)) (p + 2),
    ← iwH m (p + 4), ← iwH m (p + 5)⟩

/-- A pointer to a list header `[off, len]`, decoded by `g`. -/
def decLH {α : Type} (g : Nat → Nat → Option (List α)) (p : Nat) : Option (List α) := decAt m g p

/-- `ClassGen`. -/
def decCG (p : Nat) : Option ClassGen := do
  pure ⟨← iwN m p, ← decAt m (decHL m) (p + 1), ← decAt m (decPL m (decTM m)) (p + 3),
    ← decAt m (decHL m) (p + 5), ← decAt m (decPL m (decCS m)) (p + 7),
    ← decAt m (decPL m (decLH m (decPL m (decCC m)))) (p + 9), ← iwH m (p + 11),
    ← decAt m (decHL m) (p + 12)⟩

end dec

/-! ## The stage relation and the shape of a refinement

`IWOK m`: the pool's top is within the array. `IWGrow m m'`: the pool and the constant records
only grew (every word below the old tops is unchanged), so every decoding of `m` below the tops
stays valid in `m'`. -/

/-- The pool's top `CTL[200]`. -/
def iwTop (m : Mem) : Nat := (rdW (m.arr64 CTL) 200).toNat

/-- The pool is in bounds, and the arrays an allocation computes with have word-sized lengths
(lane `indproofs`: a stub's post carries these, so a caller's allocation after a stub works). -/
structure IWOK (m : Mem) : Prop where
  iw : iwTop m ≤ (m.arr64 IW).size
  er : erTop m ≤ (m.arr64 EREC).size
  iwSize : (m.arr64 IW).size < 2 ^ 64
  erSize : (m.arr64 EREC).size < 2 ^ 64
  ctl : 200 < (m.arr64 CTL).size
  /-- The tier-1 record pool (a job's own records, `erec_alloc` with the scratch flag on). -/
  er1 : erecTop1 m ≤ (m.arr64 (tier1 EREC)).size
  er1Size : (m.arr64 (tier1 EREC)).size < 2 ^ 64
  /-- Both record tiers are addressable by a tagged address (offset below `2^40`). -/
  erCap : (m.arr64 EREC).size < 2 ^ 40
  er1Cap : (m.arr64 (tier1 EREC)).size < 2 ^ 40

/-- `IWOK` as its conjunction, for `simp` (a memory changed only where `IWOK` does not read). -/
theorem IWOK_iff (m : Mem) : IWOK m ↔ iwTop m ≤ (m.arr64 IW).size ∧ erTop m ≤ (m.arr64 EREC).size ∧
    (m.arr64 IW).size < 2 ^ 64 ∧ (m.arr64 EREC).size < 2 ^ 64 ∧ 200 < (m.arr64 CTL).size ∧
    erecTop1 m ≤ (m.arr64 (tier1 EREC)).size ∧ (m.arr64 (tier1 EREC)).size < 2 ^ 64 ∧
    (m.arr64 EREC).size < 2 ^ 40 ∧ (m.arr64 (tier1 EREC)).size < 2 ^ 40 :=
  ⟨fun h => ⟨h.iw, h.er, h.iwSize, h.erSize, h.ctl, h.er1, h.er1Size, h.erCap, h.er1Cap⟩,
   fun ⟨a, b, c, d, e, f, g, i, j⟩ => ⟨a, b, c, d, e, f, g, i, j⟩⟩

/-- The pool and the constant records only grew. -/
structure IWGrow (m m' : Mem) : Prop where
  iw : iwTop m ≤ iwTop m'
  er : erTop m ≤ erTop m'
  iwGet : ∀ i < iwTop m, (m'.arr64 IW)[i]? = (m.arr64 IW)[i]?
  erGet : ∀ i < erTop m, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?
  /-- The tier-1 record pool only grew too. -/
  er1 : erecTop1 m ≤ erecTop1 m'
  er1Get : ∀ i < erecTop1 m, (m'.arr64 (tier1 EREC))[i]? = (m.arr64 (tier1 EREC))[i]?

theorem IWGrow.refl (m : Mem) : IWGrow m m :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl⟩

theorem IWGrow.trans {m₁ m₂ m₃ : Mem} (h₁ : IWGrow m₁ m₂) (h₂ : IWGrow m₂ m₃) : IWGrow m₁ m₃ :=
  ⟨Nat.le_trans h₁.iw h₂.iw, Nat.le_trans h₁.er h₂.er,
   fun i hi => (h₂.iwGet i (Nat.lt_of_lt_of_le hi h₁.iw)).trans (h₁.iwGet i hi),
   fun i hi => (h₂.erGet i (Nat.lt_of_lt_of_le hi h₁.er)).trans (h₁.erGet i hi),
   Nat.le_trans h₁.er1 h₂.er1,
   fun i hi => (h₂.er1Get i (Nat.lt_of_lt_of_le hi h₁.er1)).trans (h₁.er1Get i hi)⟩

/-- The record pool part of `IWGrow`. -/
theorem IWGrow.erecGrow {m m' : Mem} (h : IWGrow m m') : ErecGrow m m' :=
  ⟨h.er, h.erGet, h.er1, h.er1Get⟩

/-- Every record decoding of `m` stays valid in `m'`. -/
theorem IWGrow.ext {m m' : Mem} (h : IWGrow m m') : ArrExt (erecP m) (erecP m') := h.erecGrow.ext

/-- `IWGrow` from a frame that keeps the pool arrays and the tops (`IW`, `EREC` in both tiers,
`CTL[129]`, `CTL[130]`, `CTL[200]`). -/
theorem IWGrow.of_keep {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (IW : TieredArray) ∉ A ∧ (EREC : TieredArray) ∉ A ∧ tier1 EREC ∉ A)
    (hC : (129 : Word) ∉ C ∧ (130 : Word) ∉ C ∧ (200 : Word) ∉ C) : IWGrow m m' := by
  have hI := hf.arr IW hA.1 (by decide)
  have hE := hf.arr EREC hA.2.1 (by decide)
  have hE1 := hf.arr (tier1 EREC) hA.2.2 (by decide)
  have h129 := hf.ctl 129 hC.1
  have h130 := hf.ctl 130 hC.2.1
  have h200 := hf.ctl 200 hC.2.2
  exact ⟨by simp [iwTop, h200], by simp [erTop, h129], fun i _ => by rw [hI], fun i _ => by rw [hE],
    by simp [erecTop1, h130], fun i _ => by rw [hE1]⟩

/-- **The stage relation**: the checker state at the view `vis` of `fe`, and the pool. -/
structure StageR (vis : Word) (fe : IFEnv) (m : Mem) (a : AState) :
    Prop where
  check : CheckR m a vis fe
  iw : IWOK m

/-- **A refinement of the twin's `op` by the L call `f(args)`**: from any memory satisfying `pre`
against `a₀`, a returning run keeps the caller's locals, the twin's run succeeds, and `post`
relates the memories before and after, the twin's state after, the L results and the twin's
result. Every stub spec and every refinement of the stage has this shape. -/
def RefAM {α : Type} [Inhabited α] (p : Prog) (f : FnName) (args : List Word)
    (pre : Mem → AState → Prop) (op : AM α)
    (post : Mem → Mem → AState → List Word → α → Prop) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState), pre s₀.mem a₀ →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok op a₀ ∧
      post s₀.mem s'.mem (AM.st op a₀) r (AM.res op a₀); ⊤⦄

/-- The usual post: the stage relation at the same environment, the pool grown, and the results
decoding the twin's result by `dec`. -/
def KeepPost {α : Type} (vis : Word) (fe : IFEnv)
    (dec : Mem → List Word → α → Prop) (m m' : Mem) (a : AState) (r : List Word) (x : α) : Prop :=
  StageR vis fe m' a ∧ IWGrow m m' ∧ dec m' r x

/-- Result decoders. -/
def decW0E (_m : Mem) (r : List Word) (e : EIdx) : Prop := (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = e
def decW0L (_m : Mem) (r : List Word) (e : LIdx) : Prop := (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = e
def decW0N (_m : Mem) (r : List Word) (e : NIdx) : Prop := (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = e
def decW0B (_m : Mem) (r : List Word) (b : Bool) : Prop := (r.headD 0 != 0) = b ∧ (r.headD 0).toNat ≤ 1
def decW0Nat (_m : Mem) (r : List Word) (k : Nat) : Prop := (r.headD 0).toNat = k
def decUnit (_m : Mem) (_r : List Word) (_u : Unit) : Prop := True
/-- An `IW` list `(r[i], r[i+1])`, below the pool's top (so it stays decoded while the pool grows,
and can be passed to `sl_cons`; lane `indproofs`, at helper `rec`'s request). -/
def decRL {α : Type} (g : Mem → Nat → Nat → Option (List α)) (i : Nat) (m : Mem) (r : List Word)
    (l : List α) : Prop :=
  g m (r.getD i 0).toNat (r.getD (i + 1) 0).toNat = some l ∧
    (r.getD i 0).toNat + (r.getD (i + 1) 0).toNat ≤ iwTop m
/-- `Option (List EIdx × EIdx)` as `(ok, off, len, e)`. -/
def decOLE (m : Mem) (r : List Word) : Option (List EIdx × EIdx) → Prop
  | none => r.headD 0 = 0
  | some (l, e) => r.headD 0 = 1 ∧ decRL (fun m => decHL m) 1 m r l ∧ decW0E m (r.drop 3) e
/-- `Option EIdx` as `(ok, e)`. -/
def decOE (m : Mem) (r : List Word) : Option EIdx → Prop
  | none => r.headD 0 = 0
  | some e => r.headD 0 = 1 ∧ decW0E m r.tail e

/-! ## The L library: the pool, slices -/

/-- `iw_alloc(n)`: `n` fresh words of `IW` (zero or garbage), returns their offset. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def iwAlloc : FunDecl := lfn (n) locals (o) {
  o := CTL.u64[200];
  if len(IW.u64) < o { abort };
  if len(IW.u64) - o < n { abort };
  CTL.u64[200] := o + n;
  return o
}

/-- `iw_reset()`: empty the pool (the stage's entry). -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def iwReset : FunDecl := lfn () locals () {
  CTL.u64[200] := 0
}

/-- `erec_alloc(n)`: `n` fresh words of `EREC`, returns their tagged address: tier 0 (below
`CTL[129]`) while the scratch flag `CTL[1]` is off (the stream index, the pins), tier 1 (below
`CTL[130]`, emptied with the scratch tier) inside a job. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def erecAlloc : FunDecl := lfn (n) locals (o) {
  if CTL.u64[1] == 0 {
    o := CTL.u64[129];
    if len(EREC⟨0⟩) < o { abort };
    if len(EREC⟨0⟩) - o < n { abort };
    CTL.u64[129] := o + n;
    return o
  };
  o := CTL.u64[130];
  if len(EREC⟨1⟩) < o { abort };
  if len(EREC⟨1⟩) - o < n { abort };
  CTL.u64[130] := o + n;
  return 1099511627776 + o
}

/-- `erec_put(a, v)`: word `v` at the tagged address `a` of `EREC`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def erecPut : FunDecl := lfn (a, v) locals (t, i) {
  t := ⦃a⦄.tier;
  i := ⦃a⦄.idx;
  EREC⟨t⟩[i] := v;
  return 0
}

/-! ## The record pool: `erec_alloc` and `erec_put`

`erec_alloc(k)` allocates in the tier of the scratch flag `CTL[1]`: tier 0 at the top `CTL[129]`
while it is off (the stream index, the pins), tier 1 at `2^40 + CTL[130]` while it is on (a
job's own records). `erec_put(a, v)` writes at the tagged address `a`. Both keep every record
below the old tops (`ErecGrow`), so every decoding through `erecP` stays valid. -/

section erec
open ConRon.Arena Std.WP
open scoped Lean.Order
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

/-- The memory after `erec_alloc(k)`: the top of the flag's tier moved up by `k`. -/
def erAllocMem (m : Mem) (k : Word) : Mem :=
  if rdW (m.arr64 CTL) 1 = 0 then m.set64 CTL 129 (rdW (m.arr64 CTL) 129 + k)
  else m.set64 CTL 130 (rdW (m.arr64 CTL) 130 + k)

/-- The model of `erec_alloc(k)`: the tagged address of the first fresh word and the memory. -/
def erAllocW (m : Mem) (k : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 1 = 0 then
    let o := rdW (m.arr64 CTL) 129
    if m.len64 EREC < o then none
    else if m.len64 EREC - o < k then none
    else some (o, erAllocMem m k)
  else
    let o := rdW (m.arr64 CTL) 130
    if m.len64 (tier1 EREC) < o then none
    else if m.len64 (tier1 EREC) - o < k then none
    else some (1099511627776 + o, erAllocMem m k)

theorem erecAlloc_specW (p : Prog) (hp : p.lookup "erec_alloc" = some erecAlloc) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_alloc" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ erAllocW s₀.mem k = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erecAlloc]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs, st64]
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons,
      St.setLocs_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      Cmp.eval, BinOp.eval, rd64_rdWC, beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, erAllocW, erAllocMem, ctl_t0, tierA, Locals.init,
      List.getD_cons_zero, List.getD_cons_succ]

theorem erecPut_specW (p : Prog) (hp : p.lookup "erec_put" = some erecPut) (n : Nat) (s₀ : St)
    (a v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_put" [a, v]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = erecPutMem s₀.mem a v ∧
      (a &&& 0xFFFFFFFFFF).toNat < (s₀.mem.arr64 (tierA EREC (a >>> 40))).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erecPut]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs, st64]
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons,
      St.setLocs_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      Cmp.eval, BinOp.eval, rd64_rdWC, beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, erecPutMem, Locals.init,
      List.getD_cons_zero, List.getD_cons_succ]

/-- **`erec_alloc`'s effect**: the pool grows (`ErecGrow`), the address is the old top of the
flag's tier (tier 1 at `2^40`), that top moved up by `k` within the array, only `CTL[129]` or
`CTL[130]` changed. -/
theorem erAllocW_spec {m m' : Mem} {k a : Word} (h : erAllocW m k = some (a, m'))
    (hW : IWOK m) :
    ErecGrow m m' ∧ MemFrame [] [129, 130] m m' ∧ erOff a = erTopOf m a ∧
      erTopOf m' a = erTopOf m a + k.toNat ∧ erTopOf m' a ≤ (m.arr64 (erTier a)).size ∧
      (a.toNat / 2 ^ 40 % 2 = 0 ↔ rdW (m.arr64 CTL) 1 = 0) ∧ a.toNat < 2 ^ 41 ∧ IWOK m' := by
  have hc : 130 < (m.arr64 CTL).size := by have := hW.ctl; omega
  have hs0 := hW.erCap
  have hs1 := hW.er1Cap
  have e129 : (129 : Word).toNat < (m.arr64 CTL).size := by simp; omega
  have e130 : (130 : Word).toNat < (m.arr64 CTL).size := by simp; omega
  unfold erAllocW at h
  split at h
  · rename_i hf
    dsimp only at h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i h1 h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [erAllocMem, hf, ite_true]
    simp only [Mem.len64, UInt64.lt_iff_toNat_lt] at h1 h2
    generalize ho : rdW (m.arr64 CTL) 129 = o at h1 h2 ⊢
    have hS : (UInt64.ofNat (m.arr64 EREC).size).toNat = (m.arr64 EREC).size := by simp; omega
    rw [hS] at h1
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hS]; omega)), hS] at h2
    have hok : (o + k).toNat = o.toNat + k.toNat := by rw [UInt64.toNat_add]; omega
    have hmem := MemFrame.setCtl m 129 (o + k)
    have t0 : erTop (m.set64 CTL 129 (o + k)) = o.toNat + k.toNat := by
      simp only [erTop, rdW_set64, e129, and_self, ite_true, hok]
    have t1 : erecTop1 (m.set64 CTL 129 (o + k)) = erecTop1 m := by
      simp only [erecTop1, rdW_set64]; rw [ite_eq_right (by simp)]
    have hE : (m.set64 CTL 129 (o + k)).arr64 EREC = m.arr64 EREC := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have hE1 : (m.set64 CTL 129 (o + k)).arr64 (tier1 EREC) = m.arr64 (tier1 EREC) :=
      Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have hd : o.toNat / 2 ^ 40 % 2 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
    have hok' : IWOK (m.set64 CTL 129 (o + k)) := by
      have hI : (m.set64 CTL 129 (o + k)).arr64 IW = m.arr64 IW := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
      have h200 : iwTop (m.set64 CTL 129 (o + k)) = iwTop m := by
        simp only [iwTop, rdW_set64]; rw [ite_eq_right (by simp)]
      have h0 : erTop (m.set64 CTL 129 (o + k)) = o.toNat + k.toNat := t0
      refine ⟨by rw [h200, hI]; exact hW.iw, by rw [h0, hE]; omega, by rw [hI]; exact hW.iwSize,
        by rw [hE]; exact hW.erSize, by rw [Mem.size_arr64_set64]; exact hW.ctl,
        by rw [t1, hE1]; exact hW.er1, by rw [hE1]; exact hW.er1Size, by rw [hE]; exact hs0,
        by rw [hE1]; exact hs1⟩
    have hof : erOff o = o.toNat := Nat.mod_eq_of_lt (by omega)
    have htop : erTop m = o.toNat := by simp [erTop, ho]
    refine ⟨⟨by omega, fun i _ => by rw [hE], by rw [t1]; exact Nat.le_refl _, fun i _ => by rw [hE1]⟩,
      hmem.mono (by simp) (by simp), ?_, ?_, ?_, ?_, by omega, hok'⟩
    · simp only [hof, erTopOf, hd, ite_true, htop]
    · simp only [erTopOf, hd, ite_true, t0, htop]
    · simp only [erTopOf, erTier, hd, ite_true, t0]; omega
    · simp [hd, hf]
  · rename_i hf
    dsimp only at h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i h1 h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [erAllocMem, hf, ite_false]
    simp only [Mem.len64, UInt64.lt_iff_toNat_lt] at h1 h2
    generalize ho : rdW (m.arr64 CTL) 130 = o at h1 h2 ⊢
    have hS : (UInt64.ofNat (m.arr64 (tier1 EREC)).size).toNat = (m.arr64 (tier1 EREC)).size := by simp; omega
    rw [hS] at h1
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hS]; omega)), hS] at h2
    have hok : (o + k).toNat = o.toNat + k.toNat := by rw [UInt64.toNat_add]; omega
    have hmem := MemFrame.setCtl m 130 (o + k)
    have t1 : erecTop1 (m.set64 CTL 130 (o + k)) = o.toNat + k.toNat := by
      simp only [erecTop1, rdW_set64, e130, and_self, ite_true, hok]
    have t0 : erTop (m.set64 CTL 130 (o + k)) = erTop m := by
      simp only [erTop, rdW_set64]; rw [ite_eq_right (by simp)]
    have hE : (m.set64 CTL 130 (o + k)).arr64 EREC = m.arr64 EREC := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have hE1 : (m.set64 CTL 130 (o + k)).arr64 (tier1 EREC) = m.arr64 (tier1 EREC) :=
      Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have ha : (1099511627776 + o).toNat = 2 ^ 40 + o.toNat := by rw [UInt64.toNat_add]; simp; omega
    have hok' : IWOK (m.set64 CTL 130 (o + k)) := by
      have hI : (m.set64 CTL 130 (o + k)).arr64 IW = m.arr64 IW := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
      have h200 : iwTop (m.set64 CTL 130 (o + k)) = iwTop m := by
        simp only [iwTop, rdW_set64]; rw [ite_eq_right (by simp)]
      have h0 : erTop (m.set64 CTL 130 (o + k)) = erTop m := t0
      refine ⟨by rw [h200, hI]; exact hW.iw, by rw [h0, hE]; exact hW.er, by rw [hI]; exact hW.iwSize,
        by rw [hE]; exact hW.erSize, by rw [Mem.size_arr64_set64]; exact hW.ctl,
        by rw [t1, hE1]; omega, by rw [hE1]; exact hW.er1Size, by rw [hE]; exact hs0,
        by rw [hE1]; exact hs1⟩
    have hd : (1099511627776 + o).toNat / 2 ^ 40 % 2 = 1 := by rw [ha]; omega
    have hof : erOff (1099511627776 + o) = o.toNat := by simp only [erOff, ha]; omega
    have htop : erecTop1 m = o.toNat := by simp [erecTop1, ho]
    refine ⟨⟨by rw [t0]; exact Nat.le_refl _, fun i _ => by rw [hE], by omega, fun i _ => by rw [hE1]⟩,
      hmem.mono (by simp) (by simp), ?_, ?_, ?_, ?_, by omega, hok'⟩
    · simp only [hof, erTopOf, hd, htop]; simp
    · simp only [erTopOf, hd, t1, htop]; simp
    · simp only [erTopOf, erTier, hd, t1]; simp; omega
    · simp only [hd, hf]; simp

end erec

/-- `er_to_iw(off, len)`: the `EREC` slice copied into `IW`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def erToIw : FunDecl := lfn (o, l) locals (q, u) {
  q := call iw_alloc(l);
  u := call er_copy(q, o, l);
  return (q, l)
}

/-- `er_copy(d, s, l)`: `IW[d + j] := EREC[s + j]` for `j < l`, recursively. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def erCopy : FunDecl := lfn (d, s, l) locals (u) {
  if l == 0 { return 0 };
  IW.u64[d] := EREC⦃s⦄;
  u := call er_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `iw_copy(d, s, l)`: `IW[d + j] := IW[s + j]` for `j < l` (ascending, recursively). -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def iwCopy : FunDecl := lfn (d, s, l) locals (u) {
  if l == 0 { return 0 };
  IW.u64[d] := IW.u64[s];
  u := call iw_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `pool_copy(d, s, l)`: `IW[d + j] := POOL[s + j]` for `j < l`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def poolCopy : FunDecl := lfn (d, s, l) locals (u) {
  if l == 0 { return 0 };
  IW.u64[d] := POOL⦃s⦄;
  u := call pool_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `sl_new1(x)`: the one-element list `[x]`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def slNew1 : FunDecl := lfn (x) locals (q) {
  q := call iw_alloc(1);
  IW.u64[q] := x;
  return (q, 1)
}

/-- `sl_append(o1, l1, o2, l2)`: `xs ++ ys`, a copy. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def slAppend : FunDecl := lfn (o1, l1, o2, l2) locals (q, u) {
  if l1 + l2 < l1 { abort };
  q := call iw_alloc(l1 + l2);
  u := call iw_copy(q, o1, l1);
  u := call iw_copy(q + l1, o2, l2);
  return (q, l1 + l2)
}

/-- `sl_snoc(o, l, x)`: `xs ++ [x]`, a copy. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def slSnoc : FunDecl := lfn (o, l, x) locals (q, u) {
  if l + 1 == 0 { abort };
  q := call iw_alloc(l + 1);
  u := call iw_copy(q, o, l);
  IW.u64[q + l] := x;
  return (q, l + 1)
}

/-- `sl_cons(x, o, l)`: `x :: xs`, a copy. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def slCons : FunDecl := lfn (x, o, l) locals (q, u) {
  if l + 1 == 0 { abort };
  q := call iw_alloc(l + 1);
  IW.u64[q] := x;
  u := call iw_copy(q + 1, o, l);
  return (q, l + 1)
}

/-- `sl_contains(o, l, x)`: `xs.contains x` (word equality). -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def slContains : FunDecl := lfn (o, l, x) locals (r) {
  if l == 0 { return 0 };
  if IW.u64[o] == x { return 1 };
  r := call sl_contains(o + 1, l - 1, x);
  return r
}

/-- `sl_find(o, l, x)`: `xs.findIdx? (· == x)` as `(ok, i)`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def slFind : FunDecl := lfn (o, l, x) locals (f, i) {
  if l == 0 { return (0, 0) };
  if IW.u64[o] == x { return (1, 0) };
  (f, i) := call sl_find(o + 1, l - 1, x);
  if f == 0 { return (0, 0) };
  return (1, i + 1)
}

/-- `sl_eq(o1, l1, o2, l2)`: word-wise list equality. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def slEq : FunDecl := lfn (o1, l1, o2, l2) locals (r) {
  if l1 != l2 { return 0 };
  if l1 == 0 { return 1 };
  if IW.u64[o1] != IW.u64[o2] { return 0 };
  r := call sl_eq(o1 + 1, l1 - 1, o2 + 1, l2 - 1);
  return r
}

/-- `sl_nodup(o, l)`: `nameNodup` (no word twice). -/
-- con-ron: ConRon/Arena/CheckerBase.lean:39-44 ConRon.Arena.nameNodup
@[no_expose, l_impl ConRon.Arena.nameNodup]
def slNodup : FunDecl := lfn (o, l) locals (b, r) {
  if l == 0 { return 1 };
  b := call sl_contains(o + 1, l - 1, IW.u64[o]);
  if b != 0 { return 0 };
  r := call sl_nodup(o + 1, l - 1);
  return r
}

/-- `sl_get(o, l, i)`: `xs[i]`, aborting off the list. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def slGet : FunDecl := lfn (o, l, i) locals () {
  if l <= i { abort };
  return IW.u64[o + i]
}

/-- `sl_getd(o, l, i, d)`: `xs.getD i d`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def slGetD : FunDecl := lfn (o, l, i, d) locals () {
  if l <= i { return d };
  return IW.u64[o + i]
}

/-- `sl_set_eq(o1, l1, o2, l2)`: the same length, and every element of each is in the other
(`blockRecNameSetOk`'s test). -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def slSetEq : FunDecl := lfn (o1, l1, o2, l2) locals (b) {
  if l1 != l2 { return 0 };
  b := call sl_all_in(o1, l1, o2, l2);
  if b == 0 { return 0 };
  b := call sl_all_in(o2, l2, o1, l1);
  return b
}

/-- `sl_all_in(o1, l1, o2, l2)`: every element of the first list is in the second. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def slAllIn : FunDecl := lfn (o1, l1, o2, l2) locals (b) {
  if l1 == 0 { return 1 };
  b := call sl_contains(o2, l2, IW.u64[o1]);
  if b == 0 { return 0 };
  b := call sl_all_in(o1 + 1, l1 - 1, o2, l2);
  return b
}

/-- `rec2(a, b)`: a fresh 2-word record. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def rec2 : FunDecl := lfn (a, b) locals (q) {
  q := call iw_alloc(2);
  IW.u64[q] := a;
  IW.u64[q + 1] := b;
  return q
}

/-- `rec3(a, b, c)`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def rec3 : FunDecl := lfn (a, b, c) locals (q) {
  q := call iw_alloc(3);
  IW.u64[q] := a;
  IW.u64[q + 1] := b;
  IW.u64[q + 2] := c;
  return q
}

/-- `rec4(a, b, c, d)`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def rec4 : FunDecl := lfn (a, b, c, d) locals (q) {
  q := call iw_alloc(4);
  IW.u64[q] := a;
  IW.u64[q + 1] := b;
  IW.u64[q + 2] := c;
  IW.u64[q + 3] := d;
  return q
}

/-- `rec5(a, b, c, d, e)`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def rec5 : FunDecl := lfn (a, b, c, d, e) locals (q) {
  q := call iw_alloc(5);
  IW.u64[q] := a;
  IW.u64[q + 1] := b;
  IW.u64[q + 2] := c;
  IW.u64[q + 3] := d;
  IW.u64[q + 4] := e;
  return q
}

/-- `rec6(a, b, c, d, e, f)`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def rec6 : FunDecl := lfn (a, b, c, d, e, f) locals (q) {
  q := call iw_alloc(6);
  IW.u64[q] := a;
  IW.u64[q + 1] := b;
  IW.u64[q + 2] := c;
  IW.u64[q + 3] := d;
  IW.u64[q + 4] := e;
  IW.u64[q + 5] := f;
  return q
}

/-- `rec7(a, b, c, d, e, f, g)`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def rec7 : FunDecl := lfn (a, b, c, d, e, f, g) locals (q) {
  q := call iw_alloc(7);
  IW.u64[q] := a;
  IW.u64[q + 1] := b;
  IW.u64[q + 2] := c;
  IW.u64[q + 3] := d;
  IW.u64[q + 4] := e;
  IW.u64[q + 5] := f;
  IW.u64[q + 6] := g;
  return q
}

/-- `cv_new(name, lo, ll, ty)`: a fresh constant value in `EREC` (`lo`, `ll` an `EREC` slice). -/
-- con-ron: none — constant-value records in `EREC` (the twin's `ConstantVal` structure)
@[no_expose] def cvNew : FunDecl := lfn (nm, lo, ll, ty) locals (q, ez) {
  q := call erec_alloc(⟪CV.size⟫);
  ez := call erec_put(q, nm);
  ez := call erec_put(q + ⟪CV.lpsOff⟫, lo);
  ez := call erec_put(q + ⟪CV.lpsLen⟫, ll);
  ez := call erec_put(q + ⟪CV.type⟫, ty);
  return q
}

/-- `cv_lps(cv)`: a constant's level parameters, copied into `IW`. -/
-- con-ron: none — constant-value records in `EREC` (the twin's `ConstantVal` structure)
@[no_expose] def cvLps : FunDecl := lfn (q) locals (o, l) {
  (o, l) := call er_to_iw(EREC⦃q + ⟪CV.lpsOff⟫⦄, EREC⦃q + ⟪CV.lpsLen⟫⦄);
  return (o, l)
}

/-- `reserved_contains(n)`: `(← reservedBasisNames).contains n` (the 16 reserved names,
`PINS[55‥70]`). -/
-- con-ron: ConRon/Arena/Core.lean:1565-1569 ConRon.Arena.reservedBasisNames
@[no_expose] def reservedContains : FunDecl := lfn (n) locals (r) {
  if PINS.u64[0] == 0 { abort };
  r := call reserved_from(n, 0);
  return r
}

/-- `reserved_from(n, j)`: `n` among `PINS[55 + j‥70]`. -/
-- con-ron: ConRon/Arena/Core.lean:1565-1569 ConRon.Arena.reservedBasisNames
@[no_expose] def reservedFrom : FunDecl := lfn (n, j) locals (r) {
  if 16 <= j { return 0 };
  if PINS.u64[55 + j] == n { return 1 };
  r := call reserved_from(n, j + 1);
  return r
}

/-- `lvl_eq_true(u, v)`: `lvlEq? u v == some true` as `0`/`1`. -/
-- con-ron: ConRon/Arena/Core.lean:168-185 ConRon.Arena.lvlEq?
@[no_expose] def lvlEqTrue : FunDecl := lfn (u, v) locals (r) {
  r := call lvl_eq_c(u, v);
  return u64(r == 2)
}

/-- `lvl_eq_fueled(u, v)`: `liftFueled (← lvlEq? u v)`: `none` declines. -/
-- con-ron: ConRon/Arena/Core.lean:168-185 ConRon.Arena.lvlEq?
-- con-ron: ConRon/Arena/Core.lean:349-354 ConRon.Arena.liftFueled
@[no_expose] def lvlEqFueled : FunDecl := lfn (u, v) locals (r) {
  r := call lvl_eq_c(u, v);
  if r == 0 { fail R_RESOURCE_LIMIT_FUEL };
  return u64(r == 2)
}

/-- **`e_view(h)`: the twin's `view h`**, as `(tag, x, y, z)`: `bvar i` `(0, i)`, `fvar i ty`
`(1, i, ty)`, `sort u` `(2, u)`, `const n us` `(3, n, us)`, `app f a` `(4, f, a)`, `lam ty b`
`(5, ty, b)`, `forallE ty b` `(6, ty, b)`, `letE t v b` `(7, t, v, b)`, `lit` `(8)`, `proj s i e`
`(9, s, i, e)`; unused fields `0`. A dangling handle (a closed scratch tier, an index past the
count, an unknown tag) aborts, as the twin's `view` fails. The projections `viewBind`,
`viewApp`, … are reads of this (the twin tests the tag first). -/
-- con-ron: ConRon/Arena/Monad.lean:156-163 ConRon.Arena.view
@[no_expose] def eView : FunDecl := lfn (h) locals (g, t, i) {
  g := ⟦h⟧.tag;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if 4294967295 < h { abort };
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if BVAR⟨t⟩.count <= i { abort }; return (0, BVAR⟨t, i⟩.i, 0, 0) };
  if g == 1 {
    if FVAR⟨t⟩.count <= i { abort };
    return (1, FVAR⟨t, i⟩.i, FVAR⟨t, i⟩.ty, 0)
  };
  if g == 2 { if SORT⟨t⟩.count <= i { abort }; return (2, SORT⟨t, i⟩.u, 0, 0) };
  if g == 3 {
    if CONST⟨t⟩.count <= i { abort };
    return (3, CONST⟨t, i⟩.n, CONST⟨t, i⟩.us, 0)
  };
  if g == 4 {
    i := ⟦h⟧.aidx;
    if APP⟨t⟩.count <= i { abort };
    return (4, APP⟨t, i⟩.f, APP⟨t, i⟩.a, 0)
  };
  if g == 5 {
    if LAM⟨t⟩.count <= i { abort };
    return (5, LAM⟨t, i⟩.ty, LAM⟨t, i⟩.b, 0)
  };
  if g == 6 {
    if FORALL⟨t⟩.count <= i { abort };
    return (6, FORALL⟨t, i⟩.ty, FORALL⟨t, i⟩.b, 0)
  };
  if g == 7 {
    if LET⟨t⟩.count <= i { abort };
    return (7, LET⟨t, i⟩.ty, LET⟨t, i⟩.v, LET⟨t, i⟩.b)
  };
  if g == 8 { if LIT⟨t⟩.count <= i { abort }; return (8, 0, 0, 0) };
  if g == 9 {
    if PROJ⟨t⟩.count <= i { abort };
    return (9, PROJ⟨t, i⟩.n, PROJ⟨t, i⟩.i, PROJ⟨t, i⟩.e)
  };
  abort
}

/-- `view_ls(us)`: the level handles of a level list (`viewLs`), copied from `POOL` into `IW`. -/
-- con-ron: ConRon/Arena/Monad.lean:494-500 ConRon.Arena.viewLs
@[no_expose] def viewLsL : FunDecl := lfn (us) locals (o, l, q, u) {
  (o, l) := call ls_node(us);
  q := call iw_alloc(l);
  u := call pool_copy(q, o, l);
  return (q, l)
}

/-- `view_ls_len(us)`: `viewLsLen us` as `(1, n)` (a dangling list aborts in `ls_node`, where the
twin answers `none` and its callers fail). -/
-- con-ron: ConRon/Arena/Monad.lean:542-547 ConRon.Arena.viewLsLen
@[no_expose] def viewLsLenL : FunDecl := lfn (us) locals (o, l) {
  (o, l) := call ls_node(us);
  return (1, l)
}

/-- The library's functions. -/
def libFns : Prog :=
  [("iw_alloc", iwAlloc), ("iw_reset", iwReset), ("erec_alloc", erecAlloc), ("er_to_iw", erToIw),
   ("er_copy", erCopy), ("iw_copy", iwCopy), ("pool_copy", poolCopy), ("sl_all_in", slAllIn),
   ("reserved_from", reservedFrom),
   ("sl_new1", slNew1), ("sl_append", slAppend), ("sl_snoc", slSnoc), ("sl_cons", slCons),
   ("sl_contains", slContains), ("sl_find", slFind), ("sl_eq", slEq), ("sl_nodup", slNodup),
   ("sl_get", slGet), ("sl_getd", slGetD), ("sl_set_eq", slSetEq),
   ("rec2", rec2), ("rec3", rec3), ("rec4", rec4), ("rec5", rec5), ("rec6", rec6), ("rec7", rec7),
   ("cv_new", cvNew), ("cv_lps", cvLps), ("reserved_contains", reservedContains),
   ("lvl_eq_true", lvlEqTrue), ("lvl_eq_fueled", lvlEqFueled), ("e_view", eView),
   ("view_ls", viewLsL), ("view_ls_len", viewLsLenL)]

/-! ## The stubs: callees owned by other lanes

Each is `abort` until its lane lands it; the convention below is this lane's request (DESIGN.md,
lane `induct`, "Requests"). `vis` is the environment's view word. Lists are `IW` slices. -/

/-- A stub with `k` parameters. -/
-- con-ron: none — a closure-check stub for a callee in another file
def stub (k : Nat) : FunDecl := ⟨k, k, .abort (.const 0)⟩

/-- The stubs: name, parameter count, and (in the doc) the twin and the convention.

* `whnf_top(vis, dep, e)` (lane `whnf`'s entry, `WhnfEntry.lean`) → `e'`: `whnf .verified fe checkFuel dep e`.
* `infer_type_core(vis, dep, e)` → `t`; `ensure_sort_core(vis, dep, t)` → `u` (a level handle);
  `is_def_eq_core(vis, dep, a, b)` → `0`/`1`.
* `check_constant_val(vis, cv, allowOp)` → nothing (`cv` an `EREC` pointer).
* `consts_resolve_ffast(vis, e)` → `0`/`1`.
* `strip_pis(k, e)` → `(ok, bs.off, bs.len, body)`; `strip_lams(k, e)` the same.
* `open_pis_at_fvars_f(n, e, i)` → `(ok, fvs.off, fvs.len, body)`.
* `get_app_fn_f(fuel, e)` → `hd`; `get_app_args_f(fuel, e)` → `(off, len)` (lane `whnf`'s adapters, `WhnfEntry.lean`).
* `mk_app_n_f(f, off, len)` → `e`.
* `fvar_type_d(e)` → `t`; `fvar_type_ds(off, len)` → `(off, len)`.
* `pi_result_f(fuel, e)` → `r`.
* `inst_lp_fast(fuel, ks.off, ks.len, us, e)` → `e'`.
* `instantiate1_fast(fuel, e, v, d)` → `e'`; `instantiate_lift_fast(fuel, e, vs.off, vs.len, d)`
  → `e'`;
  `abstract1_fast(fuel, e, d, k)` → `e'`; `ar_entry(e, d, k, c)` → `e'` (`abstractRangeFast`).
* `bvar_b(fuel, e)`, `fvar_b(fuel, e)` → a number; `has_fvar_fast(fuel, e)` → `0`/`1`;
  `loose_bvars_bounded_fast(fuel, k, e)` → `0`/`1`.
* `all_level_params_defined(lps.off, lps.len, e)` → `0`/`1`.
* `intern_ls_iw(off, len)` → `us` (`internLsNode` of the `IW` slice of level handles).
* `name_rec(n)` → `internNNode (.str n "rec")`; `name_rec_i(n, i)` → `internNNode (.str n
  s!"rec_{i}")`; `proj_table_name(T)` → `projTableName T`.
* `reserved_rec_name(n)` → `0`/`1`.
* `basis_name_hit(off, len)` → `(hit, kind)` (the block's record pointers, an `EREC` slice);
  `check_basis_block(vis, kind, off, len)` → `vis'`; `ind_params_ok(nP, off, len)` → `0`/`1`.
* `former_def_headed(ty)` → `0`/`1` (`Core.lean`'s `formerDefHeaded`, at the former's type); `lit_shape_ok(q)` → `0`/`1`
  (`Core.lean`'s `litShapeOk`, `q` a constant record in `EREC`). -/
def stubFns : Prog :=
  [("whnf_top", stub 3), ("infer_type_core", stub 3), ("ensure_sort_core", stub 3),
   ("is_def_eq_core", stub 4), ("check_constant_val", stub 3), ("consts_resolve_ffast", stub 2),
   ("strip_pis", stub 2), ("strip_lams", stub 2), ("open_pis_at_fvars_f", stub 3),
   ("get_app_fn_f", stub 2), ("get_app_args_f", stub 2), ("mk_app_n_f", stub 3),
   ("fvar_type_d", stub 1), ("fvar_type_ds", stub 2), ("pi_result_f", stub 2),
   ("inst_lp_fast", stub 5), ("instantiate1_fast", stub 4),
   ("instantiate_lift_fast", stub 5), ("abstract1_fast", stub 4), ("ar_entry", stub 4),
   ("fvar_b", stub 2), ("has_fvar_fast", stub 2), ("loose_bvars_bounded_fast", stub 3),
   ("all_level_params_defined", stub 3),
   ("intern_ls_iw", stub 2), ("name_rec", stub 1), ("name_rec_i", stub 2),
   ("proj_table_name", stub 1), ("reserved_rec_name", stub 1),
   ("basis_name_hit", stub 2), ("check_basis_block", stub 4),
   ("ind_params_ok", stub 3), ("former_def_headed", stub 1), ("lit_shape_ok", stub 1)]

/-- The callees that exist on master, as stubs here so that each module's program can be checked
for closure (`Prog.wf`) on its own: `env_find(w, vis)`, `env_push(vis, q)`,
`env_pop_temp(vis, w, c, q)`, `env_row_get(w)`, `flush_caches()`, `pin_at(i)`, `pin_word(k)`,
`lvl_eq(u, v)`, `lvls_eq(us, vs)`, `lv_nz(l)` (`isNeverZero`, a level pointer), `lv_leq_top(l, r)`
(`Level.leq`, `Option Bool`), `intern_bvar(i)`, `intern_sort(u)`, `intern_const(n, us)`,
`intern_fvar(i, ty)`, `mk_app(f, a)`, `mk_lam(t, b)`, `mk_forall(t, b)`, `mk_let(t, v, b)`,
`mk_proj(n, i, e)`, `intern_param(n)`, `intern_zero()`, `intern_max(u, v)`, `intern_nanon()`,
`bvar_b(fuel, e)` (lane `exprops4`'s `bvarBL`, a stub until lane `indproofs2`),
`lv_node(p)` (a level's view: `(tag, a, b)`), `bm_clear()`, …, and the memo functions of the
schemas above (`X_find`, `X_put`, `X_clear`, `X_bank_enter`, `X_bank_leave`, instantiated by
`MemoLib`). The whole program uses the real ones. -/
def masterFns : Prog :=
  [("env_find", stub 2), ("env_push", stub 2), ("env_pop_temp", stub 4), ("env_row_get", stub 1),
   ("flush_caches", stub 0), ("pin_at", stub 1), ("pin_word", stub 1), ("lvl_eq", stub 2), ("lvl_eq_c", stub 2),
   ("lvls_eq", stub 2), ("lvls_eq_c", stub 2), ("lv_nz", stub 1), ("lv_leq_top", stub 2), ("intern_bvar", stub 1),
   ("intern_sort", stub 1), ("intern_const", stub 2), ("intern_fvar", stub 2), ("mk_app", stub 2),
   ("mk_lam", stub 2), ("mk_forall", stub 2), ("mk_let", stub 3), ("mk_proj", stub 3),
   ("intern_param", stub 1), ("intern_zero", stub 0), ("intern_max", stub 2), ("bvar_b", stub 2),
   ("intern_nanon", stub 0), ("lv_node", stub 1), ("ls_node", stub 1),
   ("ma_find", memoFindG maSch), ("ma_put", memoPutG maSch), ("ma_clear", memoClearG maSch),
   ("no_find", memoFindG noSch), ("no_put", memoPutG noSch), ("no_clear", memoClearG noSch),
   ("dp_find", memoFindG dpSch), ("dp_put", memoPutG dpSch), ("dp_clear", memoClearG dpSch),
   ("rf_find", memoFindG rfSch), ("rf_put", memoPutG rfSch), ("rf_clear", memoClearG rfSch),
   ("rf_bank_enter", bankEnterG 218), ("rf_bank_leave", bankLeaveG 218),
   ("ra_find", memoFindG raSch), ("ra_put", memoPutG raSch), ("ra_clear", memoClearG raSch),
   ("ta_find", memoFindG taSch), ("ta_put", memoPutG taSch), ("ta_clear", memoClearG taSch),
   ("hb_find", memoFindG hbSch), ("hb_put", memoPutG hbSch), ("hb_clear", memoClearG hbSch),
   ("mc_find", memoFindG mcSch), ("mc_put", memoPutG mcSch), ("mc_clear", memoClearG mcSch)]

end L.Ind

namespace L.Ind

end L.Ind

namespace L.Ind

open L.Arena

/-- A test memory: `CTL` of 256 words, `IW` and `EREC` of 64 words, every other word array empty. -/
def testMem : Mem :=
  Mem.ofWords [(CTL, Array.replicate 256 0), (IW, Array.replicate 64 0), (EREC, Array.replicate 64 0)]

-- `[1, 2] ++ [3]`, then the slice read back; `nameNodup` of it and of `[1, 2, 3, 1]`.
#guard
  match run (libFns ++ stubFns ++ masterFns) 1000 "sl_new1" [3] testMem with
  | .ok ([o3, 1], m1) =>
    match run (libFns ++ stubFns ++ masterFns) 1000 "rec2" [1, 2] m1 with
    | .ok ([o12], m2) =>
      match run (libFns ++ stubFns ++ masterFns) 1000 "sl_append" [o12, 2, o3, 1] m2 with
      | .ok ([o, 3], m3) =>
        (List.range 3).map (fun j => rdW (m3.arr64 IW) (o + UInt64.ofNat j)) == [1, 2, 3] &&
        (match run (libFns ++ stubFns ++ masterFns) 1000 "sl_nodup" [o, 3] m3 with
         | .ok ([1], _) => true | _ => false) &&
        (match run (libFns ++ stubFns ++ masterFns) 1000 "sl_snoc" [o, 3, 1] m3 with
         | .ok ([o', 4], m4) =>
           (match run (libFns ++ stubFns ++ masterFns) 1000 "sl_nodup" [o', 4] m4 with
            | .ok ([0], _) => true | _ => false)
         | _ => false)
      | _ => false
    | _ => false
  | _ => false

end L.Ind
