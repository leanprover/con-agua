module

public import ConAgua.Arena.DeclBasisSpec
public import ConAgua.Arena.RomDen

@[expose] public section

/-!
# The ROM stubs' specs (lane `decls3`)

The `checkDecl` arms read con-leche values the twin interns at the point of use (`eqA`,
`propextA`, the basis blocks, the reduce pins: `internCI`/`internCV`/`internExpr` of a constant).
In L they are the stubs `rom_ci(id)`, `rom_cv(id)`, `rom_expr_pin(id)`, `rom_basis_decls(kind)`,
`rom_basis_decls_a(kind)` of `DeclArmsNat.lean` (`romStubs`; lane `decls2`'s conventions: a
constant record or value in `EREC`, a handle, an `IW` slice of record pointers). This file states
what the real readers must prove (now `ConAgua/Rom/CIReadSpec.lean`'s `RomRefs`, in `CallRef`
shape over the real code): from the stage relation, the twin's intern of the value runs, the
stage relation holds after it at the same environment, the pools only grew, and the result
decodes to the twin's value **below the tops** (so it stays decoded as later callees grow the
pools). The startup data these come from is lane `romload`'s (`romData` in the pin buffer `PB`).

`rom_pin_sets()` (the `Nat.div`-family variants) is lane `romload`'s pin input (`CTL[150]`,
`CTL[151]`); its spec waits for their record layout.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-! The twin's values by the readers' ids (`romCiT`, `romCvT`, `romExprT`, `basisOfW`) are in
`RomDen.lean`. -/

/-! ## Result decoders (below the tops) -/

/-- A constant record at `r[0]`, decoded below the record pool's top. -/
def decRCI (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : List Word) (ci : IConstantInfo) :
    Prop :=
  DecB (fun m => decCI (erA m) (r.headD 0).toNat) m ci

/-- A constant value at `r[0]`, decoded below the record pool's top. -/
def decRCV (m : Mem) (r : List Word) (cv : IConstantVal) : Prop :=
  DecB (fun m => decCV (erA m) (r.headD 0).toNat) m cv

/-- An `IW` slice `(r[0], r[1])` of constant-record pointers, decoded below the tops. -/
def decRBlk (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : List Word)
    (cis : List IConstantInfo) : Prop :=
  DecB (basisDec dn (r.headD 0).toNat (r.tail.headD 0).toNat) m cis ∧ r = [r.headD 0, r.tail.headD 0]

/-! The specs: `ConAgua/Rom/CIReadSpec.lean` (`RomRefs`, about the real readers of
`CIRead.lean`; lane `decls4`). The arms take them as a field of their program bundles
(`RedProg.rom`, `QuotProg.rom`, `DmProg7.lRom`). -/

end L.Ind
