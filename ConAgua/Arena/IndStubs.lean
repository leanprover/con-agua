import ConAgua.Arena.IndIface
import ConAgua.Arena.WhnfBase

/-!
# The inductive stage's shared predicates (lane `induct`; once the stubs' specs)

This file held the stub contracts of the inductive stage's callees (`stubM_spec` and a `RelAM`
statement per stub, all `sorry`). Every callee is now the program's own call (`realCall`) or a
pure model, and the contracts and the `StageR` theorems through them are gone (lane `cleanup`).
What is left: the opaque word model `stubM` (still named in a few
models, e.g. `IndPartsSpec4`'s `wsK2`), `RelAM`, the walk-memo predicates that
make up `AbsOK`, and the result decoders `pwWords`, `decZC`, `decLvlEq`.

`H w`: a handle word (below `2^32`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A handle word. -/
abbrev H (w : Word) : Prop := w.toNat < 2 ^ 32

/-! ## The stubs as word models -/

/-- The word model of the stub `f`: what a call `f(args)` leaves. Opaque: nothing is known about
it. -/
opaque stubM (f : FnName) : Mem → List Word → Option (List Word × Mem)

/-- **The `abstract1` walk's memo is well formed** (lane `indproofs4`, helper `abs`): array 49
(`ABMEMO`) with epoch word `CTL[48]` (`Abs1.lean`'s `abSch`, the core's `coreAbSch`) at some map.
`abstract1_fast` clears it on entry and exit, so it needs this of the memory it starts from and
leaves it so (`IndRealAbs.lean`); `StageR` says nothing about array 49, so callers thread it. -/
def AbMemo (m : Mem) : Prop :=
  ∃ mp : Std.HashMap (EIdx × Nat) EIdx, MemoRG (⟨49, 48⟩ : MemoSch) lfKey decE m mp

/-- **The `instantiate1Lift` walk's memo is well formed** (helper `indproofs4-memo`): array 51
(`ILFM`) with epoch word `CTL[52]` (`WalkLift.lean`'s `i1lSch`), what `instantiate1_lift_fast`
needs (`IndRealMemo.lean`). -/
def I1Memo (m : Mem) : Prop :=
  ∃ mp : Std.HashMap (EIdx × Nat) EIdx, MemoRG (⟨51, 52⟩ : MemoSch) lfKey decE m mp

/-- **The `constsResolveF` walk's memo table is related to some memo** (helper `indproofs4-memo`):
array 155 (`CRM`) with epoch word `CTL[158]` (`ConstsResolveF.lean`'s `crSch`; lane `tails`'
`CrOK`, `ConstsResolveFRefine2.lean`), what `consts_resolve_ffast` needs. -/
def CrMemo (m : Mem) : Prop :=
  ∃ mp : Std.HashMap EIdx Bool,
    MemoRV (⟨155, 158⟩ : MemoSch) bmKey (fun _ w b => w = if b then 1 else 0) m mp

/-- **The `instantiateList` walk's memo is well formed** (helper `indproofs4-memo`): array 50
with epoch word `CTL[50]` (`InstList.lean`'s `ilSch`, the core's `coreIlSch`), what `inst_list`
(under `open_pis_at_fvars_f`) needs. -/
def IlMemo (m : Mem) : Prop :=
  ∃ mp : Std.HashMap (EIdx × Nat) EIdx, MemoRG (⟨50, 50⟩ : MemoSch) lfKey decE m mp

/-- **The rest of the memory's half of `TwinOK`** (lane `indstaget`): the core's other walk memos
(`WalkMemos`: arrays 151‥153, 52‥54), the three arrays whose sizes `TwinOK` bounds, the pin flag.
Carried in `AbsOK` so that every model frame (`AFr`) carries it too: what lifts a stage theorem
to `StageC` (`IndT/Lift.lean`). -/
def WkOK (m : Mem) : Prop :=
  WalkMemos m ∧ (m.arr64 EREC).size < 2 ^ 63 ∧ (m.arr64 SPN).size < 2 ^ 63 ∧
    (m.arr64 145).size < 2 ^ 63 ∧ pinW m 0 ≠ 0

/-- **The walk memos outside the stage relation are well formed** (lane `indproofs4`, helpers
`abs`, `memo`): the memos of `abstract1` (array 49), `instantiate1Lift` (51), `constsResolveF`
(155) and `instantiateList` (50). Each walk clears its memo on entry and exit, so it needs the
memo well formed in the memory it starts from and leaves it so; `StageR` says nothing about these
arrays, so the stage's theorems thread it as a hypothesis and a post. (The name is helper `abs`'s,
from when it held the `abstract1` memo only.) The core's `CoreMemos` holds the first and the last
(`IndRealAbsT.lean`). -/
def AbsOK (m : Mem) : Prop := AbMemo m ∧ I1Memo m ∧ CrMemo m ∧ IlMemo m ∧ WkOK m

/-- **The twin side of a stub**: a model run of `f(args)` from a memory satisfying `pre` against
`a` is a successful twin run of `op` with `post` after. -/
def RelAM {α : Type} (f : FnName) (args : List Word) (pre : Mem → AState → Prop) (op : AM α)
    (post : Mem → Mem → AState → List Word → α → Prop) : Prop :=
  ∀ (m m' : Mem) (a : AState) (r : List Word), stubM f m args = some (r, m') → pre m a →
    ∃ x a', op.run a = .ok (x, a') ∧ post m m' a' r x

section specs
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

local notation "V" => ConLeche.CheckMode.verified

/-- A `PropWhen` from its three words (`decPW`'s layout: `0` `never`, `1` `ifAllZero` with the
names the handle slice `(o, l)` of `a`). -/
def pwWords (a : Array Word) (t o l : Word) : Option ConLeche.PropWhen :=
  match t.toNat with
  | 0 => some .never
  | 1 => do
    let ns : List NIdx ← hslice? a o.toNat l.toNat
    pure (.ifAllZero (← ns.mapM dn))
  | _ => none

/-- `lv_zero_caps`' result `(tag, off, len)`: the zero-ness of the level `lv`, decoded in every
array that agrees with the record pool below its top. -/
def decZC (m : Mem) (r : List Word) (lv : ConLeche.Level) : Prop :=
  ∀ a : Array Word, (∀ i < erTop m, a[i]? = (erA m)[i]?) →
    pwWords dn a (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) = some (ConLeche.Level.zeronessOf lv)

end specs

/-! ## Master callees without a model yet (lane indproofs) -/

section masterSpecs
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- Result decoder of `lvl_eq`: `0` for `none`, `1` for `some false`, `2` for `some true`. -/
def decLvlEq (_m : Mem) (r : List Word) (x : Option Bool) : Prop :=
  r.headD 0 = (match x with | none => 0 | some false => 1 | some true => 2)

end masterSpecs

end L.Ind
