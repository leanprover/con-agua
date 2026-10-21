import ConAgua.Spike.WriteSet
import ConAgua.Arena.Inst1Spec
import ConAgua.Front.StateDR

/-! Spike (lane `scale`): the write set of `instProg` (instantiate1, lift, the `mk_*`, six stores),
from the text. Not imported by `ConAgua`. -/

open L L.Arena L.Spike L.Front ConRon.Arena.Frontend

set_option linter.unusedVariables false

/-- The stores of a statement: `(array, index)` with the index printed only for `CTL`. -/
def wrs : Stmt → List (ArrId × Option Expr)
  | .st64 a i _ => [(a, if a = CTL then some i else none)]
  | .seq s t | .ite _ s t => wrs s ++ wrs t
  | .while _ s => wrs s
  | _ => []

#eval (instProg.flatMap fun (f, fd) => (wrs fd.body).map fun w => (f, w.1, w.2.map ctlIdx)).filter
  fun (_, a, i) => a = CTL ∧ i.join.isNone

#eval (instProg.flatMap fun (f, fd) => (wrs fd.body).map (·.1)).eraseDups

/-- The proposed L change: a tier-indexed count store `CTL[k + t]` masks the tier, `CTL[k + (t &&& 1)]`. -/
def maskE : Expr → Expr
  | .bin .add (.const k) (.var t) => .bin .add (.const k) (.bin .and (.var t) (.const 1))
  | e => e

def maskS : Stmt → Stmt
  | .st64 a i e => .st64 a (if a = CTL then maskE i else i) e
  | .seq s t => .seq (maskS s) (maskS t)
  | .ite c s t => .ite c (maskS s) (maskS t)
  | .while c s => .while c (maskS s)
  | s => s

def instProgM : Prog := instProg.map fun (f, fd) => (f, { fd with body := maskS fd.body })

def instCtl : List Word :=
  ((instProgM.flatMap fun (_, fd) => wrs fd.body).filterMap fun (a, i) =>
    if a = CTL then i.bind ctlIdx else none).flatten.eraseDups

#eval instCtl

def instArrs : List ArrId := [47, 41, 42, 43, 44, 45, 46, 22, 23, 4, 5, 27, 28, 29, 30, 20, 21, 31, 32]
def instFns : List FnName := instProgM.map (·.1)

theorem instProgM_closed :
    closedW instProgM instArrs [44, 45, 42, 43, 22, 23, 4, 5, 28, 29, 30, 31, 20, 21, 32, 33] instFns = true := by
  decide +kernel

/-- **`inst_entry` changes only its write set**, for every run, from the text. -/
theorem instEntry_frame (n : Nat) (vs : List Word) (m m' : Mem) (rs : List Word)
    (h : run instProgM n "inst_entry" vs m = .ok (rs, m')) :
    MemFrame instArrs [44, 45, 42, 43, 22, 23, 4, 5, 28, 29, 30, 31, 20, 21, 32, 33] m m' :=
  run_frame instProgM _ _ instFns instProgM_closed "inst_entry" (by decide) n vs m rs m' h

/-- **A relation of another lane survives `inst_entry` with no lemma about `inst_entry`**: the
front's id tables (`StateDR`, arrays 64‥66) across any run, by the text's frame. -/
theorem stateDR_instEntry (n : Nat) (vs : List Word) (m m' : Mem) (rs : List Word) (st : StateD)
    (h : run instProgM n "inst_entry" vs m = .ok (rs, m')) (hD : StateDR m st) : StateDR m' st :=
  StateDR.frame (instEntry_frame n vs m m' rs h) (by decide) (by decide) (by decide) hD
