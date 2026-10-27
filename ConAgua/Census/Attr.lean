module

public import Lean.Attributes
public import Lean.Environment
public meta import Lean.Elab.Term

public section

/-!
# Census links: which L code and which theorem stand for which twin function

Three attributes, read by the census tool (`ConAgua/Census/Main.lean`, `scripts/census.sh`):

* `@[l_impl X Y …]` on an L `FunDecl`: this L function implements (part of) the target(s) `X`, `Y`.
* `@[refines X]` on a theorem: it proves that the L code refines the WHOLE target `X` (every result
  the twin's callers read). If the proof is a chain (L ⊑ model, model = `X`), put `@[refines X]` on
  every link: the census counts `X` proven only when every theorem tagged for it is sorry-free.
* `@[refines_part X "label"]` on a theorem: a PART of `X` is refined (one arm of a dispatcher, the
  validity half of a scanner, …). Parts are reported separately and never make `X` proven, except
  where the census's own `completeByParts` table lists the parts that together make up `X`.

`X` is a fully qualified name of the target (`ConRon.Arena.bvarBoundMemo`,
`ConLeche.Frontend.scanLineFwd`). It is not resolved here, because most L files are `module` files
that cannot import con-ron's arena; the census tool checks that every `X` names a target.
-/

namespace ConAgua.Census

/-- What a link says. -/
inductive LinkKind where
  | impl | refines | part
  deriving Inhabited, BEq, Repr

/-- One link: declaration `decl` stands for target `target` (with a label for parts). -/
structure Link where
  kind : LinkKind
  decl : Lean.Name
  target : Lean.Name
  label : String := ""
  deriving Inhabited, Repr

open Lean in
meta initialize linkExt : SimplePersistentEnvExtension Link (Array Link) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun _ => #[]
  }

/-- `@[l_impl X …]`: the L function implements the target(s). -/
syntax (name := l_impl) "l_impl" (ppSpace ident)+ : attr
/-- `@[refines X …]`: the theorem proves the whole refinement of the target(s). -/
syntax (name := refines) "refines" (ppSpace ident)+ : attr
/-- `@[refines_part X "label"]`: the theorem proves a part of the target. -/
syntax (name := refines_part) "refines_part" ppSpace ident ppSpace str : attr

open Lean in
private meta def addLinks (kind : LinkKind) (decl : Name) (ids : Array Syntax) (label : String) :
    AttrM Unit :=
  for id in ids do
    modifyEnv (linkExt.addEntry · { kind, decl, target := id.getId.eraseMacroScopes, label })

open Lean in
meta initialize
  registerBuiltinAttribute {
    name := `l_impl
    descr := "census: this L function implements the given con-ron/con-leche target(s)"
    add := fun decl stx _ => addLinks .impl decl stx[1].getArgs ""
  }
  registerBuiltinAttribute {
    name := `refines
    descr := "census: this theorem proves the refinement of the given target(s)"
    add := fun decl stx _ => addLinks .refines decl stx[1].getArgs ""
  }
  registerBuiltinAttribute {
    name := `refines_part
    descr := "census: this theorem proves a part (arm, half) of the given target"
    add := fun decl stx _ => addLinks .part decl #[stx[1]] (stx[2].isStrLit?.getD "")
  }

end ConAgua.Census
