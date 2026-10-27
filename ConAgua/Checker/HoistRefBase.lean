import ConAgua.Checker.Hoist
import ConAgua.Front.StateDR
import Std.Data.HashSet.Basic

/-!
# The ground hoist's refinement: shared relations (lane `front4`)

What the pieces of the refinement of `hoist_nat_op_ground` against `hoistNatOpGround`
(`ConRon/Arena/Frontend/NatOpGround.lean`) share:

* **The stream** (`OrdR`): position `k` is the `DECL` record `IW[ord + k]`, which represents
  `ds[k]` (`DeclAtF`, the front's records).
* **The visited set** (`SeenR`): the memo `HSEEN` represents the twin's `Std.HashSet EIdx` (its
  inner `Std.HashMap EIdx Unit`, keys `bmKey`: a handle word, second word `0`).
* **The name index** (`NixR`): the memo `HNIX` represents `Std.HashMap NIdx Nat` (keys `nmKey`, a
  name word; the value word is the position plus one).
* **The targets** (`TgtR`): `IW[tg + k]` is `t + 1` when the twin's map sends `k` to `t`, `0` when
  it has no entry.
* **The notes** (`notesW`): `hoist_note` on each of a list of name words in order, the walk's
  effect on everything but the visited set.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-- The name index's keys: a name word, second word `0`. -/
def nmKey : MemoKey NIdx where
  dk k1 _ := decI k1
  ek x := (x.word.toUInt64, 0)
  ok k1 k2 := k1.toNat < 2 ^ 32 ∧ k2 = 0
  ek_dk k1 k2 h := by simp only [decI_word_self k1 h.1, h.2]
  ok_tomb k1 k2 h e := by subst e; exact absurd h.1 (by decide)

/-- **The visited set**: `HSEEN` represents `seen`. -/
def SeenR (m : Mem) (seen : Std.HashSet EIdx) : Prop :=
  MemoRG hsSch bmKey (fun _ => ()) m seen.inner

/-- **The name index**: `HNIX` represents `idx` (value word = position `+ 1`). -/
def NixR (m : Mem) (idx : Std.HashMap NIdx Nat) : Prop :=
  MemoRV hnSch nmKey (fun _ w j => w.toNat = j + 1) m idx

/-- The word encoding a target entry: `t + 1`, or `0` for none. -/
def tgW : Option Nat → Word
  | some t => UInt64.ofNat (t + 1)
  | none => 0

/-- **The targets**: the `c` words `IW[tg ‥ tg + c)` encode the twin's map `T`, which has no
entry at or beyond `c`. -/
def TgtR (m : Mem) (tg : Word) (c : Nat) (T : Std.HashMap Nat Nat) : Prop :=
  (∀ k < c, rdW (m.arr64 IW) (tg + UInt64.ofNat k) = tgW T[k]?) ∧ (∀ k, c ≤ k → T[k]? = none)

/-- The handle words of a one-constant record are below `2 ^ 32` (its name, type and value: the
words the hoist reads; an inductive block's members are decoded by `hd?`, which checks it), and an
inductive block's member pointers do not start at the pool's word `0` (its top, which `trunc`
clears: `IndDeclAt` would decode another word than L reads), nor point to it. -/
def RecOK (D P : Array Word) (r : Nat) : Prop :=
  (dw D r 0 ≠ 6 → (dw D r 1).toNat < 2 ^ 32 ∧ (dw D r 4).toNat < 2 ^ 32 ∧ (dw D r 5).toNat < 2 ^ 32) ∧
  (dw D r 0 = 6 → (dw D r 2).toNat ≠ 0 ∧
    ∀ j < (dw D r 3).toNat, P[(dw D r 2).toNat + j]?.getD 0 ≠ 0)

/-- **The stream in the order `ord`**: position `k` is the record `IW[ord + k]` of `DECL` (below
`2 ^ 59`), which represents `ds[k]` (`RecOK`). -/
def OrdR (m : Mem) (ord : Word) (ds : Array IDeclaration) : Prop :=
  ∀ k (h : k < ds.size), (rdW (m.arr64 IW) (ord + UInt64.ofNat k)).toNat < 2 ^ 59 ∧
    DeclAtF (m.arr64 DECL) (m.arr64 DLP) (rdW (m.arr64 IW) (ord + UInt64.ofNat k)).toNat ds[k] ∧
    RecOK (m.arr64 DECL) (m.arr64 DLP) (rdW (m.arr64 IW) (ord + UInt64.ofNat k)).toNat

/-- **The notes**: `hoist_note(w, i, k, tg, ws, sp)` for each name word `w` of the list in
order (the walk of record `k` for the operation at `i`); the stack size after. -/
def notesW (m : Mem) (i k tg ws sp : Word) : List Word → Option (Word × Mem)
  | [] => some (sp, m)
  | w :: rest =>
    match hNoteW m w i k tg ws sp with
    | none => none
    | some (sp', m') => notesW m' i k tg ws sp' rest

theorem notesW_append (m : Mem) (i k tg ws sp : Word) (xs ys : List Word) :
    notesW m i k tg ws sp (xs ++ ys) =
      (notesW m i k tg ws sp xs).bind fun (sp', m') => notesW m' i k tg ws sp' ys := by
  induction xs generalizing m sp with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, notesW]
    cases hNoteW m x i k tg ws sp with
    | none => rfl
    | some r => exact ih _ _

end L.Checker
