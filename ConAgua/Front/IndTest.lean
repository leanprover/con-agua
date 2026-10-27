import ConAgua.Front.FrontRun

/-!
# Tests of the inductive lines (`IndFields.lean`, `IndApply.lean`)

Runs of the whole frontend program (`frontAllProg`) on a `Unit`-shaped block.
-/

open L.Arena

namespace L.Front.Ind

open L.Front

/-! ## Tests -/

-- `ind_caps`' 15 words decode to the default `IIndCaps` (`decI 0` is the default handle).
#guard decCaps #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] (fun _ => none) 0 ==
  some ({} : ConRon.Arena.IIndCaps)

/-- The lines before the inductive line: name 1 = `Unit`, 2 = `Unit.unit`, 3 = `Unit.rec`,
4 = `motive`; level 1 = `succ 0`; expressions: 0 = `Sort 1`, 1 = `Unit`, 2 = `Sort 0`
(stand-in for a motive's type and the rule's right-hand side). -/
def unitPre : String :=
  "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Unit\"}}\n{\"in\":2,\"str\":{\"pre\":1,\"str\":\"unit\"}}\n\
  {\"in\":3,\"str\":{\"pre\":1,\"str\":\"rec\"}}\n{\"il\":1,\"succ\":0}\n\
  {\"ie\":0,\"sort\":1}\n{\"ie\":1,\"const\":{\"name\":1,\"us\":[]}}\n{\"ie\":2,\"sort\":0}\n"

/-- A `Unit`-shaped block: one type `Unit : Sort 1` with the constructor `Unit.unit : Unit`
(no fields), the recursor `Unit.rec` (one motive, one minor, `k := false`: `Sort 1` is not
`zero`). `kr` is the recursor's `k`, `nf` the constructor's `numFields`. -/
def unitLine (kr : String) (nf : Nat) : String :=
  "{\"inductive\":{\"ctors\":[{\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"numFields\":" ++
  toString nf ++ ",\"numParams\":0,\"type\":1,\"cidx\":0,\"induct\":1}],\"recs\":[{\"all\":[1],\
  \"isUnsafe\":false,\"k\":" ++ kr ++ ",\"levelParams\":[],\"name\":3,\"numIndices\":0,\
  \"numMinors\":1,\"numMotives\":1,\"numParams\":0,\"rules\":[{\"ctor\":2,\"nfields\":0,\
  \"rhs\":2}],\"type\":2}],\"types\":[{\"all\":[1],\"ctors\":[2],\"isRec\":false,\
  \"isReflexive\":false,\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"numIndices\":0,\
  \"numNested\":0,\"numParams\":0,\"type\":0}]}}"

/-- The whole input through `front_run` (`frontAllProg`, `apply_dline`'s `inductive` hook): the
memory after, if it accepts. -/
def unitRun (kr : String) (nf : Nat) : Option Mem :=
  match run frontAllProg 1000000 "front_run" [] (frontMemOf (unitPre ++ unitLine kr nf)) with
  | .ok ([0], m) => some m
  | _ => none

-- The block validates and installs: one `DECL` record of kind 6 with 3 constants and 0
-- parameters, decoding (`IndDeclAt`'s `decCIs`) to `indInfo`, `ctorInfo`, `recInfo`.
#guard (unitRun "false" 0).map (fun m =>
    let D := m.arr64 DECL
    (dw D 0 0, dw D 0 3, dw D 0 4,
      ((decCIs (m.arr64 DIND) (fun _ => none) (dw D 0 2).toNat (dw D 0 3).toNat).map
        (·.map fun
          | .indInfo _ _ => 3 | .ctorInfo _ np nf => 40 + 10 * np + nf
          | .recInfo _ maj pre rs => 500 + 100 * maj + 10 * pre + rs.length | _ => 0)))) ==
  some (6, 3, 0, some [3, 40, 721])
-- `k := true` is refused (the generated recursor is not K-like: `Sort 1`).
#guard (unitRun "true" 0).isNone
-- A constructor whose `numFields` disagrees with its type's telescope is refused.
#guard (unitRun "false" 1).isNone

end L.Front.Ind
