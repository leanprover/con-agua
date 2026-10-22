import ConAgua.Arena.DeclBasisSpec

/-!
# The ROM stubs' specs (lane `decls3`)

The `checkDecl` arms read con-leche values the twin interns at the point of use (`eqA`,
`propextA`, the basis blocks, the reduce pins: `internCI`/`internCV`/`internExpr` of a constant).
In L they are the stubs `rom_ci(id)`, `rom_cv(id)`, `rom_expr(id)`, `rom_basis_decls(kind)`,
`rom_basis_decls_a(kind)` of `DeclArmsNat.lean` (`romStubs`; lane `decls2`'s conventions: a
constant record or value in `EREC`, a handle, an `IW` slice of record pointers). This file states
what the real readers must prove, in lane `induct`'s stub shape (`stubM` + `RelAM`, proved by
`sorry`, listed in DESIGN.md): from the stage relation, the twin's intern of the value runs, the
stage relation holds after it at the same environment, the pools only grew, and the result
decodes to the twin's value **below the tops** (so it stays decoded as later callees grow the
pools). The startup data these come from is lane `romload`'s (`romData` in the pin buffer `PB`).

`rom_pin_sets()` (the `Nat.div`-family variants) is lane `romload`'s pin input (`CTL[150]`,
`CTL[151]`); its spec waits for their record layout.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-! ## The twin's values by the stubs' ids -/

/-- `rom_ci(id)`'s constant. -/
def romCiT : Nat → AM IConstantInfo
  | 0 => eqA | 1 => natA | 2 => iffA | 3 => iffIntroA | 4 => iffRecA | 5 => nonemptyA
  | 6 => nonemptyIntroA | _ => nonemptyRecA

/-- `rom_cv(id)`'s constant value. -/
def romCvT : Nat → AM IConstantVal
  | 0 => propextA | 1 => choiceA | 2 => trueCvA | 3 => trueIntroCvA | 4 => trustCompilerA
  | 5 => boolCvA | 6 => reduceNatCvA | 7 => reduceBoolCvA | 8 => ofReduceNatA | _ => ofReduceBoolA

/-- `rom_expr(id)`'s expression. -/
def romExprT : Nat → AM EIdx
  | 0 => reduceNatDeclPin | _ => reduceBoolDeclPin

/-- The basis block of `rom_basis_decls(kind)`'s word. -/
def basisOfW : Nat → ConLeche.BasisKind
  | 0 => .eqK | 1 => .natK | 2 => .emptyK | 3 => .falseK | _ => .quotK

/-! ## Result decoders (below the tops) -/

/-- A constant record at `r[0]`, decoded below the record pool's top. -/
def decRCI (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : List Word) (ci : IConstantInfo) :
    Prop :=
  DecB (fun m => decCI (erA m) dn (r.headD 0).toNat) m ci

/-- A constant value at `r[0]`, decoded below the record pool's top. -/
def decRCV (m : Mem) (r : List Word) (cv : IConstantVal) : Prop :=
  DecB (fun m => decCV (erA m) (r.headD 0).toNat) m cv

/-- An `IW` slice `(r[0], r[1])` of constant-record pointers, decoded below the tops. -/
def decRBlk (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : List Word)
    (cis : List IConstantInfo) : Prop :=
  DecB (basisDec dn (r.headD 0).toNat (r.tail.headD 0).toNat) m cis ∧ r = [r.headD 0, r.tail.headD 0]

/-! ## The specs -/

section specs
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- `rom_ci(id)`: `eqA`, `natA`, the `Iff` and `Nonempty` families (ids `0‥7`). -/
theorem romCi_spec (id : Word) (hid : id.toNat < 8) :
    RelAM "rom_ci" [id] (StageR dn vis fe) (romCiT id.toNat) (KeepPost dn vis fe (decRCI dn)) :=
  sorry

/-- `rom_cv(id)`: `propextA`, `choiceA`, the `True` family, `trustCompilerA`, `boolCvA`, the reduce
operations' types, the `ofReduce*` axioms (ids `0‥9`). -/
theorem romCv_spec (id : Word) (hid : id.toNat < 10) :
    RelAM "rom_cv" [id] (StageR dn vis fe) (romCvT id.toNat) (KeepPost dn vis fe decRCV) := sorry

/-- `rom_expr(id)`: the reduce operations' pinned values (ids `0`, `1`). -/
theorem romExpr_spec (id : Word) (hid : id.toNat < 2) :
    RelAM "rom_expr" [id] (StageR dn vis fe) (romExprT id.toNat) (KeepPost dn vis fe decW0E) :=
  sorry

/-- `rom_basis_decls(kind)`: the raw basis block (`BasisKind.decls`). -/
theorem romBasisDecls_spec (k : Word) (hk : k.toNat < 5) :
    RelAM "rom_basis_decls" [k] (StageR dn vis fe) (BasisKind.decls (basisOfW k.toNat))
      (KeepPost dn vis fe (decRBlk dn)) := sorry

/-- `rom_basis_decls_a(kind)`: the annotated basis block (`BasisKind.declsA`). -/
theorem romBasisDeclsA_spec (k : Word) (hk : k.toNat < 5) :
    RelAM "rom_basis_decls_a" [k] (StageR dn vis fe) (BasisKind.declsA (basisOfW k.toNat))
      (KeepPost dn vis fe (decRBlk dn)) := sorry

/-- `rom_and_pin()`: the pinned `And` block (`andPinDecls`), for `and_pin_ok`'s inductive arm. -/
theorem romAndPin_spec :
    RelAM "rom_and_pin" [] (StageR dn vis fe) andPinDecls (KeepPost dn vis fe (decRBlk dn)) := sorry

end specs

end L.Ind
