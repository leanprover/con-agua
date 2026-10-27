import ConAgua.Rom.CIRead
import ConAgua.Arena.DeclRomStubs

/-!
# The ROM constant readers' refinements: the statements (lane `decls4`)

The readers of `CIRead.lean` (`rom_basis_decls`, `rom_basis_decls_a`, `rom_ci`, `rom_cv`,
`rom_expr_pin`, `rom_and_pin`) read the pin-data buffer `PB`. As for the startup readers
(`Stage.lean`), a run of the real program `P` over `PB` holding `bs` is a run of the substituted
program `P.subPB bs` (`triple_subPB`), in which the readers read the constant `bs`. The arms'
theorems are stated for any program `p` whose readers are these (`RomCIProg bs p`), with `bs`
starting with `romData` (`pb_check`). They replace the `sorry`'d `RelAM` stub specs of
`DeclRomStubs.lean`: same pre (`StageR`), same twin values, same posts (`KeepPost`, the results
decoded below the tops), now about the real code (`callW`, `RomRef`, which is `CallRef`).
-/

open ConRon.Arena

namespace L.Rom

open L.Arena L.Ind

/-- **The ROM constant readers' lookups**, for a buffer `rom`: the startup readers over `rom`
(`ItemsProg`), the allocators, and `romCIProg`'s functions. -/
structure RomCIProg (rom : List UInt8) (p : Prog) : Prop extends ItemsProg rom p where
  rom_exprs_to : p.lookup "rom_exprs_to" = some romExprsTo
  erec_alloc : p.lookup "erec_alloc" = some erecAlloc
  iw_alloc : p.lookup "iw_alloc" = some iwAlloc
  rom_basis_decls : p.lookup "rom_basis_decls" = some romBasisDeclsL
  rom_basis_decls_a : p.lookup "rom_basis_decls_a" = some romBasisDeclsAL
  rom_ci : p.lookup "rom_ci" = some romCiL
  rom_cv : p.lookup "rom_cv" = some romCvL
  rom_expr_pin : p.lookup "rom_expr_pin" = some romExprPinL
  rom_and_pin : p.lookup "rom_and_pin" = some romAndPinL
  rci_slot : p.lookup "rci_slot" = some rciSlot
  rci_fresh : p.lookup "rci_fresh" = some rciFresh
  rci_names_to : p.lookup "rci_names_to" = some rciNamesTo
  rci_name_sl : p.lookup "rci_name_sl" = some rciNameSl
  rci_lvls_to : p.lookup "rci_lvls_to" = some rciLvlsTo
  rci_cv : p.lookup "rci_cv" = some rciCv
  rci_caps : p.lookup "rci_caps" = some rciCaps
  rci_rule : p.lookup "rci_rule" = some rciRule
  rci_rules_to : p.lookup "rci_rules_to" = some rciRulesTo
  rci_ci : p.lookup "rci_ci" = some rciCi
  rci_block_to : p.lookup "rci_block_to" = some rciBlockTo
  rci_block : p.lookup "rci_block" = some rciBlock

/-- **The ROM a program reads**: some buffer starting with `romData`, whose readers `p` has. -/
def RomReady (p : Prog) : Prop :=
  ∃ (rom rest : List UInt8), RomOK rom ∧ rom = romData ++ rest ∧ RomCIProg rom p

/-- `DeclNatBase.lean`'s `CallRef`, restated here so that the arms' modules below it can import
this file (the two are the same definition: `romRef_callRef`). -/
def RomRef {α : Type} (p : Prog) (f : FnName) (args : List Word) (pre : Mem → AState → Prop)
    (op : AM α) (post : Mem → Mem → AState → List Word → α → Prop) : Prop :=
  ∀ (n : Nat) (m : Mem) (a : AState) (r : List Word) (m' : Mem), pre m a →
    callW p n f args m = some (r, m') → ∃ x a', op.run a = .ok (x, a') ∧ post m m' a' r x

/-- **Names `dn` reads back from the twin's store**: each has a handle that both `dn` and the
store decode to it. For a `sortZ`'s names (`Quot`'s `u`), the reader interns them again
(`rci_caps`), a no-op on such a state (`CIReadRefCaps.lean`). -/
def NamesDn (dn : NIdx → Option ConLeche.Name) (a : AState) (ns : List ConLeche.Name) : Prop :=
  ∀ x ∈ ns, ∃ k, dn k = some x ∧ denoteN a.store.ns k = some x

theorem NamesDn.ext {dn : NIdx → Option ConLeche.Name} {a a' : AState} {ns : List ConLeche.Name}
    (h : NamesDn dn a ns) (hx : Ext a.store a'.store) : NamesDn dn a' ns := fun x hx' => by
  obtain ⟨k, h1, h2⟩ := h x hx'
  exact ⟨k, h1, ConRon.Bridge.denoteN_ext h2 hx⟩

theorem NamesDn.mono {dn : NIdx → Option ConLeche.Name} {a : AState} {ns ns' : List ConLeche.Name}
    (h : NamesDn dn a ns) (hs : ∀ x ∈ ns', x ∈ ns) : NamesDn dn a ns' := fun x hx => h x (hs x hx)

/-- The `sortZ` names of the quotient blocks (`Quot`'s level parameter `u`; `quotNames_eq`). -/
def quotNames : List ConLeche.Name := [.str .anonymous "u"]

section specs
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- **`rom_ci(id)` refines `romCiT id`** (`eqA`, `natA`, the `Iff`/`Nonempty` families). -/
def RomCiRef : Prop := ∀ id : Word, id.toNat < 8 →
  RomRef p "rom_ci" [id] (StageR dn vis fe) (romCiT id.toNat) (KeepPost dn vis fe (decRCI dn))

/-- **`rom_cv(id)` refines `romCvT id`**. -/
def RomCvRef : Prop := ∀ id : Word, id.toNat < 10 →
  RomRef p "rom_cv" [id] (StageR dn vis fe) (romCvT id.toNat) (KeepPost dn vis fe decRCV)

/-- **`rom_expr_pin(id)` refines `romExprT id`** (the reduce operations' pinned values). -/
def RomExprPinRef : Prop := ∀ id : Word, id.toNat < 2 →
  RomRef p "rom_expr_pin" [id] (StageR dn vis fe) (romExprT id.toNat) (KeepPost dn vis fe decW0E)

/-- **`rom_basis_decls(k)` refines `BasisKind.decls`**, for the kinds without `sortZ` names
(all but the quotient block, `RomQuotRef`). -/
def RomBasisRef : Prop := ∀ k : Word, k.toNat < 4 →
  RomRef p "rom_basis_decls" [k] (StageR dn vis fe) (BasisKind.decls (basisOfW k.toNat))
    (KeepPost dn vis fe (decRBlk dn))

/-- **`rom_basis_decls_a(k)` refines `BasisKind.declsA`** (as `RomBasisRef`). -/
def RomBasisARef : Prop := ∀ k : Word, k.toNat < 4 →
  RomRef p "rom_basis_decls_a" [k] (StageR dn vis fe) (BasisKind.declsA (basisOfW k.toNat))
    (KeepPost dn vis fe (decRBlk dn))

/-- **`rom_basis_decls(4)` refines the quotient block**, from a well-formed twin state that
names `Quot`'s `sortZ` names (`quotNames`) through `dn`. -/
def RomQuotRef : Prop :=
  RomRef p "rom_basis_decls" [4]
    (fun m a => StageR dn vis fe m a ∧ ConRon.Bridge.StateOK a ∧ NamesDn dn a quotNames)
    (BasisKind.decls (basisOfW 4)) (KeepPost dn vis fe (decRBlk dn))

/-- **`rom_basis_decls_a(4)` refines the annotated quotient block** (as `RomQuotRef`). -/
def RomQuotARef : Prop :=
  RomRef p "rom_basis_decls_a" [4]
    (fun m a => StageR dn vis fe m a ∧ ConRon.Bridge.StateOK a ∧ NamesDn dn a quotNames)
    (BasisKind.declsA (basisOfW 4)) (KeepPost dn vis fe (decRBlk dn))

/-- **`rom_and_pin()` refines `andPinDecls`**. -/
def RomAndPinRef : Prop :=
  RomRef p "rom_and_pin" [] (StageR dn vis fe) andPinDecls (KeepPost dn vis fe (decRBlk dn))

/-- All six (the basis readers in two parts, `basis`/`quot`), at every stage. -/
structure RomRefs : Prop where
  ci : ∀ dn vis fe, RomCiRef p dn vis fe
  cv : ∀ dn vis fe, RomCvRef p dn vis fe
  expr : ∀ dn vis fe, RomExprPinRef p dn vis fe
  basis : ∀ dn vis fe, RomBasisRef p dn vis fe
  basisA : ∀ dn vis fe, RomBasisARef p dn vis fe
  quot : ∀ dn vis fe, RomQuotRef p dn vis fe
  quotA : ∀ dn vis fe, RomQuotARef p dn vis fe
  andPin : ∀ dn vis fe, RomAndPinRef p dn vis fe

end specs

/- `romRefs_of` (the readers refine the twin) is in `CIReadRefs.lean`, above the proofs. -/

end L.Rom
