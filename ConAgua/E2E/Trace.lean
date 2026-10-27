import ConAgua.L.Semantics
import Std.Data.HashMap.Basic

/-!
# A tracing interpreter for L (lane `e2e`, diagnosis only)

`L.run` (`ConAgua/L/Semantics.lean`) is the semantics; this is a second interpreter with mutable
frames, used only to say *where* a run stops: on an `abort` or an out-of-bounds access it reports
the call stack, the function and which `abort` of its body (in pre-order) was reached. It has no
fuel (a call depth limit instead). `e2e.py` uses `L.run` for verdicts; disagreements between the
two would be a bug here.
-/

namespace L.E2E.Trace

open L

inductive Stop where
  | abort (k : Nat)
  | oob
  | noFun (f : String)
  | depth
  deriving Inhabited

structure TS where
  mem : Mem
  stack : Array String := #[]
  calls : Std.HashMap String Nat := {}
  /-- where the run stopped: the call stack, innermost last -/
  at_ : Array String := #[]

abbrev TM := ExceptT Stop (StateM TS)

/-- The frame: locals. -/
abbrev Frame := Array Word

def getV (fr : Frame) (x : Nat) : Word := fr.getD x 0

def setV (fr : Frame) (x : Nat) (v : Word) : Frame :=
  if x < fr.size then fr.set! x v else (fr ++ Array.replicate (x + 1 - fr.size) 0).set! x v

def stop {α : Type} (e : Stop) : TM α := do
  modify fun s => { s with at_ := s.stack }
  throw e

def evalE (fr : Frame) : Expr → TM Word
  | .const w => pure w
  | .var x => pure (getV fr x)
  | .bin op a b => do
    let x ← evalE fr a
    let y ← evalE fr b
    return op.eval x y
  | .ld8 a i => do
    let j ← evalE fr i
    let arr := (← get).mem.arr8 a
    if h : j.toNat < arr.size then return arr[j.toNat].toUInt64 else stop .oob
  | .ld64 a i => do
    let j ← evalE fr i
    let arr := (← get).mem.arr64 a
    if h : j.toNat < arr.size then return arr[j.toNat] else stop .oob
  | .len8 a => do return (← get).mem.len8 a
  | .len64 a => do return (← get).mem.len64 a
  | .cmpw c a b => do
    let x ← evalE fr a
    let y ← evalE fr b
    return c.evalW x y
  | .ldc d i => do
    let j ← evalE fr i
    if h : j.toNat < d.length then return d[j.toNat].toUInt64 else stop .oob
  | .glob g => do return (← get).mem.glob g
  | .ld64t a t i => do
    let u ← evalE fr t
    let j ← evalE fr i
    let arr := (← get).mem.arr64 (tierA a u)
    if h : j.toNat < arr.size then return arr[j.toNat] else stop .oob
  | .len64t a t => do
    let u ← evalE fr t
    return (← get).mem.len64 (tierA a u)
  | .ld8x8 b i => do
    let j ← evalE fr i
    let bs := (← get).mem.src8 b
    if j.toNat + 8 ≤ bs.size then return le64 bs j.toNat else stop .oob

def warrT (fr : Frame) : WArr → TM ArrId
  | .plain a => pure a
  | .tier a t => do return tierA a (← evalE fr t)

def evalC (fr : Frame) : Cond → TM Bool
  | .cmp c a b => do
    let x ← evalE fr a
    let y ← evalE fr b
    return c.eval x y
  | .and p q => do if (← evalC fr p) then evalC fr q else return false
  | .or p q => do if (← evalC fr p) then return true else evalC fr q
  | .not p => do return !(← evalC fr p)

/-- The number of `abort`s in a statement (pre-order numbering). -/
def nAborts : Stmt → Nat
  | .abort _ => 1
  | .seq s t | .ite _ s t => nAborts s + nAborts t
  | .while _ s => nAborts s
  | _ => 0

/-- A program as a hash map (first binding wins, as `List.lookup`). -/
def index (p : Prog) : Std.HashMap String FunDecl :=
  p.foldl (fun m (f, d) => if m.contains f then m else m.insert f d) {}

mutual
partial def exec (P : Std.HashMap String FunDecl) (fr : Frame) (base : Nat) : Stmt → TM (Sig × Frame)
  | .skip => pure (.normal, fr)
  | .set x e => do return (.normal, setV fr x (← evalE fr e))
  | .st8 a i e => do
    let j ← evalE fr i
    let v ← evalE fr e
    if j.toNat < ((← get).mem.arr8 a).size then modify fun s => { s with mem := s.mem.set8 a j v }
    else stop .oob
    return (.normal, fr)
  | .st64 a i e => do
    let j ← evalE fr i
    let v ← evalE fr e
    if j.toNat < ((← get).mem.arr64 a).size then modify fun s => { s with mem := s.mem.set64 a j v }
    else stop .oob
    return (.normal, fr)
  | .st64t a t i e => do
    let u ← evalE fr t
    let j ← evalE fr i
    let v ← evalE fr e
    if j.toNat < ((← get).mem.arr64 (tierA a u)).size then
      modify fun s => { s with mem := s.mem.set64 (tierA a u) j v }
    else stop .oob
    return (.normal, fr)
  | .copy64 d di s si n => do
    let da ← warrT fr d
    let i ← evalE fr di
    let sa ← warrT fr s
    let j ← evalE fr si
    let k ← evalE fr n
    let m := (← get).mem
    if i.toNat + k.toNat ≤ (m.arr64 da).size ∧ j.toNat + k.toNat ≤ (m.arr64 sa).size then
      modify fun st => { st with mem := m.copy64 da i sa j k.toNat }
    else stop .oob
    return (.normal, fr)
  | .copy8w d di s si n => do
    let da ← warrT fr d
    let i ← evalE fr di
    let j ← evalE fr si
    let k ← evalE fr n
    let m := (← get).mem
    if i.toNat + k.toNat ≤ (m.arr64 da).size ∧ j.toNat + k.toNat ≤ (m.src8 s).size then
      modify fun st => { st with mem := m.copy8w da i (m.src8 s) j k.toNat }
    else stop .oob
    return (.normal, fr)
  | .scan8 x s i e c => do
    let vi ← evalE fr i
    let ve ← evalE fr e
    let b := (← get).mem.src8 s
    if vi ≤ ve ∧ ve.toNat ≤ b.size then
      return (.normal, setV fr x (UInt64.ofNat (scanN b c vi.toNat ve.toNat)))
    else stop .oob
  | .seq s t => do
    let (r, fr) ← exec P fr base s
    match r with
    | .normal => exec P fr (base + nAborts s) t
    | r => return (r, fr)
  | .ite c s t => do
    if (← evalC fr c) then exec P fr base s else exec P fr (base + nAborts s) t
  | .while c s => do
    let mut fr := fr
    repeat
      if !(← evalC fr c) then return (.normal, fr)
      let (r, fr') ← exec P fr base s
      fr := fr'
      match r with
      | .normal => pure ()
      | .brk => return (.normal, fr)
      | .ret v => return (.ret v, fr)
    return (.normal, fr)
  | .brk => pure (.brk, fr)
  | .ret es => do return (.ret (← es.mapM (evalE fr)), fr)
  | .call xs f args => do
    let vs ← args.mapM (evalE fr)
    let rs ← invoke P f vs
    let fr := (xs.zipIdx).foldl (fun fr (x, i) => setV fr x (rs.getD i 0)) fr
    return (.normal, fr)
  | .abort _ => stop (.abort base)
  | .gset g e => do
    let v ← evalE fr e
    modify fun s => { s with mem := s.mem.setG g v }
    return (.normal, fr)

partial def invoke (P : Std.HashMap String FunDecl) (f : String) (vs : List Word) : TM (List Word) := do
  let some d := P[f]? | stop (.noFun f)
  if (← get).stack.size > 200000 then stop .depth
  modify fun s => { s with stack := s.stack.push f, calls := s.calls.insert f (s.calls.getD f 0 + 1) }
  let fr : Frame := (vs.toArray ++ Array.replicate (d.nlocals - vs.length) 0)
  let (r, _) ← exec P fr 0 d.body
  modify fun s => { s with stack := s.stack.pop }
  return r.retVal
end

/-- Run `entry`: the outcome line, the call stack at a stop (innermost last), the call counts. -/
def run (p : Prog) (entry : String) (m : Mem) : String × Array String × Std.HashMap String Nat :=
  let P := index p
  let (r, s) := (invoke P entry []).run.run { mem := m }
  match r with
  | .ok rs => (s!"ok {rs.headD 0}", #[], s.calls)
  | .error e =>
    let msg := match e with
      | .abort k => s!"abort #{k}"
      | .oob => "oob"
      | .noFun f => s!"nofun {f}"
      | .depth => "depth"
    (msg, s.at_, s.calls)

end L.E2E.Trace
