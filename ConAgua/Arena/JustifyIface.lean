module

public import ConAgua.Arena.Env
public import ConAgua.Arena.Globals
public import ConAgua.Arena.MemoLib
public import ConRon.Arena.Justify
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The comparison with a solution: the interface (lane compare)

con-ron's `--compare` (`Arena/Justify.lean`, `Arena/Needs.lean`; docs/design/compare.md) checks
a challenge's records with its holes justified by a **solution**, an `ISolution`: the solution's
frozen stream index `idx` and the challenge's record mates `mates`. One store holds both streams.
In L:

* **The solution's index** is the stream index moved out of `EIX*`/`TIX*` after the solution's
  check phase (con-ron's `thaw_tier` handing the index back): the rows `SIXA`/`SIXS`/`SIXN`
  (constants) and `STXA`/`STXS`/`STXN` (tables), in `EIX*`'s and `TIX*`'s encoding (by the
  persistent name handle's index `i`, words `2 i`, `2 i + 1`: the counter (resp. the record
  position) plus one, and the record's `EREC` address); `SNEXT` its `next`, `SCNT` its record
  count (`firsts.size`). The records stay in `EREC`'s tier 0, which only grows.
* **The record mates** (`ISolution.mates`, a map from a name to a list of names): rows
  `MATA`/`MATS`/`MATN` by the name handle's index, words `2 i`, `2 i + 1` = the slice's `EREC`
  address plus one (`0`: no entry) and its length; the slice holds the names' handles.
* **The flag** `SOL`: `1` while the challenge's jobs run (`J = some sol`), `0` otherwise (the
  flat run, the solution's jobs): `record_job` reads it.
* **A needs walk's state** (`NeedsSt`): its `seen` map is the memo `ndSch` (`NDM`, keys the
  expression handles, value `1`), its names the stack `NACC[0‥NTOP)`.
* **The cone walk's state** (`coneGo`): `seen` the memo `csSch` (`CSM`, keys the name handles),
  the work list the stack `CWK[0‥CTOP)`, its head on top.

`SolR m J` relates the rows to the twin's `ISolution`; `sol_find`, `sol_find_table` refine
`ISolution.find?`, `ISolution.findTable?`.
-/

namespace L.Arena

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-! ## The arrays and the globals

Declared here until the comparison is wired into `check`; then they move into the checker's
table (`ConAgua/Layout.lean`) and `Arena/Globals.lean` under the same names and numbers. -/

/-- The solution's constant rows of `anonymous` names (the moved stream index). -/
abbrev SIXA : ArrId := 210
/-- The solution's constant rows of `str` names. -/
abbrev SIXS : ArrId := 211
/-- The solution's constant rows of `num` names. -/
abbrev SIXN : ArrId := 212
/-- The solution's table rows of `anonymous` names. -/
abbrev STXA : ArrId := 213
/-- The solution's table rows of `str` names. -/
abbrev STXS : ArrId := 214
/-- The solution's table rows of `num` names. -/
abbrev STXN : ArrId := 215
/-- The record mates' rows of `anonymous` names. -/
abbrev MATA : ArrId := 216
/-- The record mates' rows of `str` names. -/
abbrev MATS : ArrId := 217
/-- The record mates' rows of `num` names. -/
abbrev MATN : ArrId := 218
/-- `needsGo`'s `seen` memo (`ndSch`; min 3). -/
abbrev NDM : ArrId := 219
/-- `coneGo`'s `seen` memo (`csSch`; min 3). -/
abbrev CSM : ArrId := 220
/-- `NeedsSt.acc`: a needs walk's names, `NACC[0‥NTOP)`. -/
abbrev NACC : ArrId := 221
/-- `coneGo`'s work list, as a stack `CWK[0‥CTOP)`, its head on top. -/
abbrev CWK : ArrId := 222

/-- `1` while the challenge's jobs run with the solution, else `0`. -/
abbrev SOL : L.GVar := ⟨4⟩
/-- The solution index's `next` counter. -/
abbrev SNEXT : L.GVar := ⟨5⟩
/-- The solution index's record count (`firsts.size`). -/
abbrev SCNT : L.GVar := ⟨6⟩
/-- The top of `NACC`. -/
abbrev NTOP : L.GVar := ⟨7⟩
/-- The top of `CWK`. -/
abbrev CTOP : L.GVar := ⟨12⟩

/-! ## The arrays by name tag -/

/-- The solution's constant-row array of name tag `g`. -/
def sixArr (g : Nat) : ArrId := if g = 0 then SIXA else if g = 1 then SIXS else SIXN

/-- The solution's table-row array of name tag `g`. -/
def stxArr (g : Nat) : ArrId := if g = 0 then STXA else if g = 1 then STXS else STXN

/-- The record mates' row array of name tag `g`. -/
def matArr (g : Nat) : ArrId := if g = 0 then MATA else if g = 1 then MATS else MATN

/-- The solution's constant row of name handle `w`: counter plus one and record, `(0, 0)` for a
scratch name or another tag. -/
def solRow (m : Mem) (w : Word) : Word × Word :=
  if rowTag w ≤ 2 ∧ rowTier w = 0 then
    (rdN (m.arr64 (sixArr (rowTag w))) (rowIx w), rdN (m.arr64 (sixArr (rowTag w))) (rowIx w + 1))
  else (0, 0)

/-- The solution's table row of name handle `w`: position plus one and record. -/
def solTbl (m : Mem) (w : Word) : Word × Word :=
  if rowTag w ≤ 2 ∧ rowTier w = 0 then
    (rdN (m.arr64 (stxArr (rowTag w))) (rowIx w), rdN (m.arr64 (stxArr (rowTag w))) (rowIx w + 1))
  else (0, 0)

/-- The record mates' row of name handle `w`: the slice's address plus one and its length. -/
def matRow (m : Mem) (w : Word) : Word × Word :=
  if rowTag w ≤ 2 ∧ rowTier w = 0 then
    (rdN (m.arr64 (matArr (rowTag w))) (rowIx w), rdN (m.arr64 (matArr (rowTag w))) (rowIx w + 1))
  else (0, 0)

/-- The mates' list of a row, as the twin's `mates[n]?`. -/
def matList (m : Mem) (w : Word) : Option (List NIdx) :=
  if (matRow m w).1 = 0 then none
  else hslice? (erecP m) ((matRow m w).1.toNat - 1) (matRow m w).2.toNat

/-! ## The relation -/

/-- **The solution** `J` in L's memory: the rows are the solution index's `base.idx`/`base.tbls`
(as `IndexR`'s `base`/`btbl`, at the solution's arrays), `SNEXT` its `next`, `SCNT` its
`firsts.size`, the mates' rows its `mates`. -/
structure SolR (m : Mem) (J : ISolution) : Prop where
  base : ∀ n : NIdx,
    (J.idx.base.idx[n]?).map (fun e => (e.1, some e.2)) =
      (if (solRow m n.word.toUInt64).1 = 0 then none
       else some ((solRow m n.word.toUInt64).1.toNat - 1,
         decCI (erecP m) (solRow m n.word.toUInt64).2.toNat))
  btbl : ∀ n : NIdx,
    (J.idx.base.tbls[n]?).map (fun e => (e.1, some e.2)) =
      (if (solTbl m n.word.toUInt64).1 = 0 then none
       else some ((solTbl m n.word.toUInt64).1.toNat - 1,
         decTbl (erecP m) (solTbl m n.word.toUInt64).2.toNat))
  next : (m.glob SNEXT).toNat = J.idx.next
  size : (m.glob SCNT).toNat = J.idx.firsts.size
  mates : ∀ n : NIdx, J.mates[n]? = matList m n.word.toUInt64
  /-- A row's counter and position words are below `2^32` (the index build's capacity). -/
  rows : ∀ w : Word, (solRow m w).1.toNat < 2 ^ 32 ∧ (solTbl m w).1.toNat < 2 ^ 32

/-- **The run's solution**: `SOL = 0` and none, or `SOL = 1` and `SolR`. -/
def OptSolR (m : Mem) : Option ISolution → Prop
  | none => m.glob SOL = 0
  | some J => m.glob SOL = 1 ∧ SolR m J

/-! ## The memos of the walks -/

/-- `needsGo`'s `seen` memo: `NDM`, stamp and count `CTL[220]`, `CTL[221]`. -/
def ndSch : MemoSch := ⟨NDM, 220⟩

/-- `coneGo`'s `seen` memo: `CSM`, stamp and count `CTL[222]`, `CTL[223]`. -/
def csSch : MemoSch := ⟨CSM, 222⟩

/-! ## The row access (L plumbing) -/

/-- `sol_row_get(w)`: the solution's constant row of name handle `w`. -/
-- con-ron: none — row access of L's solution index (the twin's `ISolution.idx.base.idx`)
@[no_expose] def solRowGetL : FunDecl := lfn (w) locals (g, ix) {
  if ⟦w⟧.tier != 0 { return (0, 0) };
  g := ⟦w⟧.tag;
  ix := ⟦w⟧.idx << 1;
  if g == 0 { return (SIXA.u64[ix], SIXA.u64[ix + 1]) };
  if g == 1 { return (SIXS.u64[ix], SIXS.u64[ix + 1]) };
  if g == 2 { return (SIXN.u64[ix], SIXN.u64[ix + 1]) };
  abort
}

/-- `sol_row_set(w, c, p)`: the solution's constant row of the persistent name handle `w`. -/
-- con-ron: none — row access of L's solution index (the twin's `ISolution.idx.base.idx`)
@[no_expose] def solRowSetL : FunDecl := lfn (w, c, p) locals (g, ix) {
  if ⟦w⟧.tier != 0 { abort };
  g := ⟦w⟧.tag;
  ix := ⟦w⟧.idx << 1;
  if g == 0 { SIXA.u64[ix] := c; SIXA.u64[ix + 1] := p; return 0 };
  if g == 1 { SIXS.u64[ix] := c; SIXS.u64[ix + 1] := p; return 0 };
  if g == 2 { SIXN.u64[ix] := c; SIXN.u64[ix + 1] := p; return 0 };
  abort
}

/-- `sol_tbl_get(w)`: the solution's table row of name handle `w`. -/
-- con-ron: none — row access of L's solution index (the twin's `ISolution.idx.base.tbls`)
@[no_expose] def solTblGetL : FunDecl := lfn (w) locals (g, ix) {
  if ⟦w⟧.tier != 0 { return (0, 0) };
  g := ⟦w⟧.tag;
  ix := ⟦w⟧.idx << 1;
  if g == 0 { return (STXA.u64[ix], STXA.u64[ix + 1]) };
  if g == 1 { return (STXS.u64[ix], STXS.u64[ix + 1]) };
  if g == 2 { return (STXN.u64[ix], STXN.u64[ix + 1]) };
  abort
}

/-- `sol_tbl_set(w, r, p)`: the solution's table row of the persistent name handle `w`. -/
-- con-ron: none — row access of L's solution index (the twin's `ISolution.idx.base.tbls`)
@[no_expose] def solTblSetL : FunDecl := lfn (w, r, p) locals (g, ix) {
  if ⟦w⟧.tier != 0 { abort };
  g := ⟦w⟧.tag;
  ix := ⟦w⟧.idx << 1;
  if g == 0 { STXA.u64[ix] := r; STXA.u64[ix + 1] := p; return 0 };
  if g == 1 { STXS.u64[ix] := r; STXS.u64[ix + 1] := p; return 0 };
  if g == 2 { STXN.u64[ix] := r; STXN.u64[ix + 1] := p; return 0 };
  abort
}

/-- `mates_get(w)`: the record mates' row of name handle `w`: `(o + 1, len)`, `(0, 0)` for none. -/
-- con-ron: none — row access of L's record mates (the twin's `ISolution.mates`)
@[no_expose] def matesGetL : FunDecl := lfn (w) locals (g, ix) {
  if ⟦w⟧.tier != 0 { return (0, 0) };
  g := ⟦w⟧.tag;
  ix := ⟦w⟧.idx << 1;
  if g == 0 { return (MATA.u64[ix], MATA.u64[ix + 1]) };
  if g == 1 { return (MATS.u64[ix], MATS.u64[ix + 1]) };
  if g == 2 { return (MATN.u64[ix], MATN.u64[ix + 1]) };
  abort
}

/-- `mates_set(w, o, l)`: the record mates' row of the persistent name handle `w`. -/
-- con-ron: none — row access of L's record mates (the twin's `ISolution.mates`)
@[no_expose] def matesSetL : FunDecl := lfn (w, o, l) locals (g, ix) {
  if ⟦w⟧.tier != 0 { abort };
  g := ⟦w⟧.tag;
  ix := ⟦w⟧.idx << 1;
  if g == 0 { MATA.u64[ix] := o; MATA.u64[ix + 1] := l; return 0 };
  if g == 1 { MATS.u64[ix] := o; MATS.u64[ix + 1] := l; return 0 };
  if g == 2 { MATN.u64[ix] := o; MATN.u64[ix + 1] := l; return 0 };
  abort
}

/-! ## The solution's lookups -/

/-- `sol_find(w)`: `ISolution.find?`: `(1, record)` for the solution index's first entry of
name `w` below its `next` counter, `(0, 0)` otherwise. -/
-- con-ron: ConRon/Arena/Justify.lean:180-185 ConRon.Arena.ISolution.find?
@[no_expose, l_impl ConRon.Arena.ISolution.find?]
def solFindL : FunDecl := lfn (w) locals (c, p) {
  (c, p) := call sol_row_get(w);
  if c == 0 { return (0, 0) };
  if c - 1 < SNEXT { return (1, p) };
  return (0, 0)
}

/-- `sol_find_table(w)`: `ISolution.findTable?`: the table record's address plus one for name
`w`'s first table in the solution index, if the constant `w` is in it and the table's record
position is one of the solution's records; `0` otherwise. -/
-- con-ron: ConRon/Arena/Justify.lean:187-194 ConRon.Arena.ISolution.findTable?
@[no_expose, l_impl ConRon.Arena.ISolution.findTable?]
def solFindTableL : FunDecl := lfn (w) locals (f, q, r, p) {
  (f, q) := call sol_find(w);
  if f == 0 { return 0 };
  (r, p) := call sol_tbl_get(w);
  if r == 0 { return 0 };
  if r - 1 < SCNT { return p + 1 };
  return 0
}

/-! ## The rows read off by tag -/

section rows
variable {m : Mem} {w : Word}

theorem solRow_t1 (ht : tierW w ≠ 0) : solRow m w = (0, 0) := by
  have h1 : rowTier w ≠ 0 := fun e => ht (UInt64.toNat_inj.mp (by rw [tierW_toNat_row, e]; rfl))
  simp [solRow, h1]
theorem solTbl_t1 (ht : tierW w ≠ 0) : solTbl m w = (0, 0) := by
  have h1 : rowTier w ≠ 0 := fun e => ht (UInt64.toNat_inj.mp (by rw [tierW_toNat_row, e]; rfl))
  simp [solTbl, h1]
theorem matRow_t1 (ht : tierW w ≠ 0) : matRow m w = (0, 0) := by
  have h1 : rowTier w ≠ 0 := fun e => ht (UInt64.toNat_inj.mp (by rw [tierW_toNat_row, e]; rfl))
  simp [matRow, h1]

theorem solRow_g {A : ArrId} (g : Word) (ht : tierW w = 0) (hg : tagW w = g) (hg2 : g.toNat ≤ 2)
    (hA : sixArr g.toNat = A) :
    solRow m w = (rdW (m.arr64 A) (idxW w <<< 1), rdW (m.arr64 A) ((idxW w <<< 1) + 1)) := by
  have h1 : rowTier w = 0 := rowTier_of ht
  simp only [solRow, rowTag_of hg, h1, rdN_ixW, rdN_ixW1, hA, hg2, and_self, ite_true]
theorem solTbl_g {A : ArrId} (g : Word) (ht : tierW w = 0) (hg : tagW w = g) (hg2 : g.toNat ≤ 2)
    (hA : stxArr g.toNat = A) :
    solTbl m w = (rdW (m.arr64 A) (idxW w <<< 1), rdW (m.arr64 A) ((idxW w <<< 1) + 1)) := by
  have h1 : rowTier w = 0 := rowTier_of ht
  simp only [solTbl, rowTag_of hg, h1, rdN_ixW, rdN_ixW1, hA, hg2, and_self, ite_true]
theorem matRow_g {A : ArrId} (g : Word) (ht : tierW w = 0) (hg : tagW w = g) (hg2 : g.toNat ≤ 2)
    (hA : matArr g.toNat = A) :
    matRow m w = (rdW (m.arr64 A) (idxW w <<< 1), rdW (m.arr64 A) ((idxW w <<< 1) + 1)) := by
  have h1 : rowTier w = 0 := rowTier_of ht
  simp only [matRow, rowTag_of hg, h1, rdN_ixW, rdN_ixW1, hA, hg2, and_self, ite_true]

theorem solRow_0 (ht : tierW w = 0) (hg : tagW w = 0) :
    solRow m w = (rdW (m.arr64 SIXA) (idxW w <<< 1), rdW (m.arr64 SIXA) ((idxW w <<< 1) + 1)) :=
  solRow_g 0 ht hg (by decide) rfl
theorem solRow_1 (ht : tierW w = 0) (hg : tagW w = 1) :
    solRow m w = (rdW (m.arr64 SIXS) (idxW w <<< 1), rdW (m.arr64 SIXS) ((idxW w <<< 1) + 1)) :=
  solRow_g 1 ht hg (by decide) rfl
theorem solRow_2 (ht : tierW w = 0) (hg : tagW w = 2) :
    solRow m w = (rdW (m.arr64 SIXN) (idxW w <<< 1), rdW (m.arr64 SIXN) ((idxW w <<< 1) + 1)) :=
  solRow_g 2 ht hg (by decide) rfl
theorem solTbl_0 (ht : tierW w = 0) (hg : tagW w = 0) :
    solTbl m w = (rdW (m.arr64 STXA) (idxW w <<< 1), rdW (m.arr64 STXA) ((idxW w <<< 1) + 1)) :=
  solTbl_g 0 ht hg (by decide) rfl
theorem solTbl_1 (ht : tierW w = 0) (hg : tagW w = 1) :
    solTbl m w = (rdW (m.arr64 STXS) (idxW w <<< 1), rdW (m.arr64 STXS) ((idxW w <<< 1) + 1)) :=
  solTbl_g 1 ht hg (by decide) rfl
theorem solTbl_2 (ht : tierW w = 0) (hg : tagW w = 2) :
    solTbl m w = (rdW (m.arr64 STXN) (idxW w <<< 1), rdW (m.arr64 STXN) ((idxW w <<< 1) + 1)) :=
  solTbl_g 2 ht hg (by decide) rfl
theorem matRow_0 (ht : tierW w = 0) (hg : tagW w = 0) :
    matRow m w = (rdW (m.arr64 MATA) (idxW w <<< 1), rdW (m.arr64 MATA) ((idxW w <<< 1) + 1)) :=
  matRow_g 0 ht hg (by decide) rfl
theorem matRow_1 (ht : tierW w = 0) (hg : tagW w = 1) :
    matRow m w = (rdW (m.arr64 MATS) (idxW w <<< 1), rdW (m.arr64 MATS) ((idxW w <<< 1) + 1)) :=
  matRow_g 1 ht hg (by decide) rfl
theorem matRow_2 (ht : tierW w = 0) (hg : tagW w = 2) :
    matRow m w = (rdW (m.arr64 MATN) (idxW w <<< 1), rdW (m.arr64 MATN) ((idxW w <<< 1) + 1)) :=
  matRow_g 2 ht hg (by decide) rfl

end rows

/-! ## What the lookups return -/

/-- A hit of name `w` in the solution's index: a row below `SNEXT`. -/
def solHit (m : Mem) (w : Word) : Prop :=
  (solRow m w).1 ≠ 0 ∧ (solRow m w).1 - 1 < m.glob SNEXT

instance (m : Mem) (w : Word) : Decidable (solHit m w) := by unfold solHit; infer_instance

/-- A table row of name `w` at one of the solution's records. -/
def solTblHit (m : Mem) (w : Word) : Prop :=
  (solTbl m w).1 ≠ 0 ∧ (solTbl m w).1 - 1 < m.glob SCNT

instance (m : Mem) (w : Word) : Decidable (solTblHit m w) := by unfold solTblHit; infer_instance

/-- What `sol_find(w)` returns. -/
def solFindRes (m : Mem) (w : Word) : List Word :=
  if solHit m w then [1, (solRow m w).2] else [0, 0]

/-- What `sol_find_table(w)` returns. -/
def solTblRes (m : Mem) (w : Word) : Word :=
  if solHit m w ∧ solTblHit m w then (solTbl m w).2 + 1 else 0

section facts
variable {m : Mem} {J : ISolution}

theorem ISolution.find?_eq (J : ISolution) (n : NIdx) :
    J.find? n = match J.idx.base.idx[n]? with
      | some (c, ci) => if c < J.idx.next then some ci else none
      | none => none := rfl

/-- **`ISolution.find?` in L's terms.** -/
theorem SolR.find_eq (h : SolR m J) {w : Word} (hw : w.toNat < 2 ^ 32) :
    J.find? (decI w) = if solHit m w then decCI (erecP m) (solRow m w).2.toNat else none := by
  have hb := h.base (decI w); rw [decI_word_self (k := .name) w hw] at hb
  rw [ISolution.find?_eq]
  simp only [solHit]
  cases e : J.idx.base.idx[(decI w : NIdx)]? with
  | none =>
    rw [e] at hb
    by_cases b0 : (solRow m w).1 = 0
    · simp [b0]
    · simp [b0] at hb
  | some x =>
    obtain ⟨c, ci⟩ := x
    rw [e] at hb
    by_cases b0 : (solRow m w).1 = 0
    · simp [b0] at hb
    · simp only [b0, ite_false, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨hc, hci⟩ := hb
      subst hc
      rw [← hci]
      dsimp only
      rw [← h.next]
      by_cases l : UInt64.toNat (solRow m w).fst - 1 < (m.glob SNEXT).toNat
      · rw [ite_eq_left l, ite_eq_left ⟨b0, (sub1_lt_iff b0).mpr l⟩]
      · rw [ite_eq_right l, ite_eq_right (fun e => l ((sub1_lt_iff b0).mp e.2))]

/-- A hit decodes. -/
theorem SolR.hit_dec (h : SolR m J) {w : Word} (hw : w.toNat < 2 ^ 32) (hh : solHit m w) :
    ∃ ci, decCI (erecP m) (solRow m w).2.toNat = some ci := by
  have hb := h.base (decI w); rw [decI_word_self (k := .name) w hw] at hb
  simp only [hh.1, ite_false] at hb
  cases e : J.idx.base.idx[(decI w : NIdx)]? with
  | none => rw [e] at hb; cases hb
  | some x =>
    rw [e] at hb
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
    exact ⟨x.2, hb.2.symm⟩

theorem ISolution.findTable?_eq (J : ISolution) (n : NIdx) :
    J.findTable? n = if (J.find? n).isSome then
      (match J.idx.base.tbls[n]? with
       | some (r, t) => if r < J.idx.firsts.size then some t else none
       | none => none) else none := rfl

/-- **`ISolution.findTable?` in L's terms.** -/
theorem SolR.findTable_eq (h : SolR m J) {w : Word} (hw : w.toNat < 2 ^ 32) :
    J.findTable? (decI w) =
      if solHit m w ∧ solTblHit m w then decTbl (erecP m) (solTbl m w).2.toNat else none := by
  rw [ISolution.findTable?_eq, h.find_eq hw]
  by_cases hh : solHit m w
  · obtain ⟨ci, hci⟩ := h.hit_dec hw hh
    simp only [hh, ite_true, hci]
    simp only [Option.isSome_some, ite_true, true_and]
    have hb := h.btbl (decI w); rw [decI_word_self (k := .name) w hw] at hb
    simp only [solTblHit]
    cases e : J.idx.base.tbls[(decI w : NIdx)]? with
    | none =>
      rw [e] at hb
      by_cases b0 : (solTbl m w).1 = 0
      · simp [b0]
      · simp [b0] at hb
    | some x =>
      obtain ⟨r, t⟩ := x
      rw [e] at hb
      by_cases b0 : (solTbl m w).1 = 0
      · simp [b0] at hb
      · simp only [b0, ite_false, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨hc, hti⟩ := hb
        subst hc
        rw [← hti]
        dsimp only
        rw [← h.size]
        by_cases l : UInt64.toNat (solTbl m w).fst - 1 < (m.glob SCNT).toNat
        · rw [ite_eq_left l, ite_eq_left ⟨b0, (sub1_lt_iff b0).mpr l⟩]
        · rw [ite_eq_right l, ite_eq_right (fun e => l ((sub1_lt_iff b0).mp e.2))]
  · simp [hh]

/-- A table hit decodes. -/
theorem SolR.tbl_dec (h : SolR m J) {w : Word} (hw : w.toNat < 2 ^ 32) (hh : solTblHit m w) :
    ∃ t, decTbl (erecP m) (solTbl m w).2.toNat = some t := by
  have hb := h.btbl (decI w); rw [decI_word_self (k := .name) w hw] at hb
  simp only [hh.1, ite_false] at hb
  cases e : J.idx.base.tbls[(decI w : NIdx)]? with
  | none => rw [e] at hb; cases hb
  | some x =>
    rw [e] at hb
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
    exact ⟨x.2, hb.2.symm⟩

end facts

/-! ## The calls -/

section specs
variable (p : Prog)

theorem solRowGet_spec (hp : p.lookup "sol_row_get" = some solRowGetL) (n : Nat) (s₀ : St)
    (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sol_row_get" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r = [(solRow s₀.mem w).1, (solRow s₀.mem w).2]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, solRowGetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs]
    all_goals simp only [Cond.pval, Expr.pval, Expr.pval_tagE, Expr.pval_tierE, Expr.pval_idxE,
      St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Cmp.eval, BinOp.eval, rd64_rdWC,
      beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, solRow_t1, solRow_0, solRow_1, solRow_2]

theorem solTblGet_spec (hp : p.lookup "sol_tbl_get" = some solTblGetL) (n : Nat) (s₀ : St)
    (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sol_tbl_get" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r = [(solTbl s₀.mem w).1, (solTbl s₀.mem w).2]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, solTblGetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs]
    all_goals simp only [Cond.pval, Expr.pval, Expr.pval_tagE, Expr.pval_tierE, Expr.pval_idxE,
      St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Cmp.eval, BinOp.eval, rd64_rdWC,
      beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, solTbl_t1, solTbl_0, solTbl_1, solTbl_2]

theorem matesGet_spec (hp : p.lookup "mates_get" = some matesGetL) (n : Nat) (s₀ : St)
    (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mates_get" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r = [(matRow s₀.mem w).1, (matRow s₀.mem w).2]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, matesGetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs]
    all_goals simp only [Cond.pval, Expr.pval, Expr.pval_tagE, Expr.pval_tierE, Expr.pval_idxE,
      St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Cmp.eval, BinOp.eval, rd64_rdWC,
      beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, matRow_t1, matRow_0, matRow_1, matRow_2]

theorem solFind_spec (hg : p.lookup "sol_row_get" = some solRowGetL)
    (hp : p.lookup "sol_find" = some solFindL) (n : Nat) (s₀ : St) (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sol_find" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r = solFindRes s₀.mem w; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, solFindL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs,
      solRowGet_spec p hg n]
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons,
      St.setLocs_nil, List.headD_cons, List.tail_cons, Locals.init_cons_zero, Cmp.eval, BinOp.eval,
      beq_iff_eq] at *
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, solFindRes, solHit, SNEXT]

/-- **`sol_find` refines `ISolution.find?`**: a hit returns `1` and a record decoding to the
twin's constant, a miss `0`. -/
@[refines ConRon.Arena.ISolution.find?]
theorem solFind_refines (hg : p.lookup "sol_row_get" = some solRowGetL)
    (hp : p.lookup "sol_find" = some solFindL) (n : Nat) (s₀ : St) {J : ISolution} (w : Word)
    (hJ : SolR s₀.mem J) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sol_find" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      (J.find? (decI w) = none ↔ r.headD 0 = 0) ∧
      (∀ ci, J.find? (decI w) = some ci ↔
        (r.headD 0 = 1 ∧ decCI (erecP s₀.mem) (r.tail.headD 0).toNat = some ci)); ⊤⦄ :=
  triple_post (solFind_spec p hg hp n s₀ w) fun r s ⟨h1, h2, h3⟩ => by
    subst h3
    refine ⟨h1, h2, ?_⟩
    rw [hJ.find_eq hw]
    by_cases hh : solHit s₀.mem w
    · obtain ⟨ci, hci⟩ := hJ.hit_dec hw hh
      simp [solFindRes, hh, hci]
    · simp [solFindRes, hh]

theorem solFindTable_spec (hg : p.lookup "sol_row_get" = some solRowGetL)
    (hf : p.lookup "sol_find" = some solFindL) (ht : p.lookup "sol_tbl_get" = some solTblGetL)
    (hp : p.lookup "sol_find_table" = some solFindTableL) (n : Nat) (s₀ : St) (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sol_find_table" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r = [solTblRes s₀.mem w]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, solFindTableL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs,
      solFind_spec p hg hf n, solTblGet_spec p ht n]
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons,
      St.setLocs_nil, List.headD_cons, List.tail_cons, Locals.init_cons_zero, Cmp.eval, BinOp.eval,
      beq_iff_eq] at *
    all_goals (by_cases hh : solHit s₀.mem w <;>
      simp_all [LocEq, Sig.retVal, Sig.retOr, solFindRes, solTblRes, solTblHit, Locals.init_cons_zero, SCNT])
    all_goals (intro hx; exact absurd hx (UInt64.not_lt.mpr ‹_›))

/-- **`sol_find_table` refines `ISolution.findTable?`**: `0` for none, else the table record's
address plus one, decoding to the twin's table. -/
@[refines ConRon.Arena.ISolution.findTable?]
theorem solFindTable_refines (hg : p.lookup "sol_row_get" = some solRowGetL)
    (hf : p.lookup "sol_find" = some solFindL) (ht : p.lookup "sol_tbl_get" = some solTblGetL)
    (hp : p.lookup "sol_find_table" = some solFindTableL) (n : Nat) (s₀ : St) {J : ISolution}
    (w : Word) (hJ : SolR s₀.mem J) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sol_find_table" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      J.findTable? (decI w) = (if r.headD 0 = 0 then none
        else decTbl (erecP s₀.mem) ((r.headD 0).toNat - 1)) ∧
      (r.headD 0 ≠ 0 → ∃ t, decTbl (erecP s₀.mem) ((r.headD 0).toNat - 1) = some t); ⊤⦄ :=
  triple_post (solFindTable_spec p hg hf ht hp n s₀ w) fun r s ⟨h1, h2, h3⟩ => by
    subst h3
    refine ⟨h1, h2, ?_⟩
    rw [hJ.findTable_eq hw]
    have hlt := (hJ.rows w).2
    by_cases hh : solHit s₀.mem w ∧ solTblHit s₀.mem w
    · obtain ⟨t, ht⟩ := hJ.tbl_dec hw hh.2
      have hl := decTbl_lt ht
      have hv : ((solTbl s₀.mem w).2 + 1).toNat = (solTbl s₀.mem w).2.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      have hp1 : ((solTbl s₀.mem w).2 + 1) ≠ 0 := fun e => by
        have := congrArg UInt64.toNat e; rw [hv] at this; simp at this
      simp [solTblRes, hh, hp1, hv, ht]
    · simp [solTblRes, hh]

end specs

/-- The interface's functions. -/
def justifyIfaceProg : Prog :=
  [("sol_row_get", solRowGetL), ("sol_row_set", solRowSetL), ("sol_tbl_get", solTblGetL),
   ("sol_tbl_set", solTblSetL), ("mates_get", matesGetL), ("mates_set", matesSetL),
   ("sol_find", solFindL), ("sol_find_table", solFindTableL),
   ("nd_find", memoFindG ndSch), ("nd_put", memoPutG ndSch), ("nd_clear", memoClearG ndSch),
   ("cs_find", memoFindG csSch), ("cs_put", memoPutG csSch), ("cs_clear", memoClearG csSch)]

end L.Arena
