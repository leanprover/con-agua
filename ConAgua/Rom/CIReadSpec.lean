module

public import ConAgua.Rom.CIRead
public import ConAgua.Rom.Rename
public import ConAgua.Arena.DeclRomStubs

@[expose] public section

/-!
# The ROM constant readers' refinements: the statements (lane `decls4`)

The readers of `CIRead.lean` (`rom_basis_decls`, `rom_ci`, `rom_cv`, `rom_expr_pin`,
`rom_and_pin`) read the program's constant data `romDataLit` through the ROM readers' copies
(`rom_u64_c`, `rom_name_c`, …, `CIConst.lean`), which are the ROM readers at `rom := romDataLit`
with their calls renamed (`romC`). The arms' theorems are stated for any program `p` whose readers
are these (`RomCIProg p`): its copies are the readers of `Prog.viaC romDataLit p` (the ROM readers over the
constant data under their own names, then `p`) renamed, so the generic reader proofs run in
`Prog.viaC p`. They replace the `sorry`'d `RelAM` stub specs of `DeclRomStubs.lean`: same pre
(`StageR`), same twin values, same posts (`KeepPost`, the results decoded below the tops), now
about the real code (`callW`, `RomRef`, which is `CallRef`).
-/

open ConRon.Arena

namespace L.Rom

open L.Arena L.Ind

/-- The ROM readers over `rom` under their own names (a function of `rom`, not a program of the
checker: these names are the pin-data readers' there). -/
def romCTabR (rom : List UInt8) : Prog :=
  [("rom_u64", romU64 rom), ("rom_put", romPut rom), ("rom_name", romName rom),
   ("rom_level", romLevel rom), ("rom_levels", romLevels), ("rom_lvls_go", romLvlsGo),
   ("rom_expr", romExpr rom), ("rom_ex_ref", romExRef), ("rom_ex_leaf", romExLeaf),
   ("rom_ex_one", romExOne), ("rom_ex_two", romExTwo), ("rom_exprs_to", romExprsTo)]

/-- **The ROM readers over `rom` under their own names**, then `p`: the program in which the
copies' callees are the generic readers (at `rom := romDataLit`, `RomReady`). -/
def Prog.viaC (rom : List UInt8) (p : Prog) : Prog := romCTabR rom ++ p

/-- The ROM readers over the constant data and the functions they call (closed under the calls of
`Prog.viaC` at the checker's program). -/
def romCN : List FnName :=
  ["rom_u64", "rom_put", "rom_name", "intern_nanon", "nanon_find", "nanon_push", "intern_nstr",
   "lit_hash", "nstr_find", "nstr_match", "limbs_eq", "nstr_push", "intern_nnum", "nnum_find",
   "nnum_push", "rom_level", "intern_zero", "zero_find", "zero_push", "intern_param", "param_find",
   "param_push", "intern_succ", "succ_find", "succ_push", "intern_max", "max_find", "max_push",
   "intern_imax", "imax_find", "imax_push", "rom_levels", "rom_lvls_go", "stk_push", "stk_pool",
   "intern_ls", "ls_find", "ls_match", "ls_push", "rom_expr", "rom_ex_ref", "memo_get",
   "rom_ex_leaf", "intern_bvar", "bvar_find", "bvar_push", "intern_sort", "sort_find", "sort_push",
   "rom_lit", "intern_lit", "lit_find", "lit_match", "lit_push", "intern_const", "const_find",
   "const_push", "rom_ex_one", "intern_fvar", "fvar_find", "fvar_push", "memo_push", "rset_find",
   "rset_put", "mk_proj", "der_b", "intern_proj", "proj_find", "proj_push", "rom_ex_two", "mk_app",
   "intern_app", "app_find", "app_push", "mk_lam", "intern_lam", "lam_find", "lam_push",
   "mk_forall", "intern_forall", "forall_find", "forall_push", "mk_let", "intern_letE",
   "letE_find", "letE_push", "rom_exprs_to", "erec_put"]

/-- **The ROM constant readers' lookups**: the readers' copies are `Prog.viaC p`'s ROM readers
renamed (`ren`), which are the generic readers over `romDataLit` with the store's interners of
`p` (`via`); the allocators, the memo reset and `romCIProg`'s functions. -/
structure RomCIProg (rom : List UInt8) (p : Prog) : Prop where
  via : ExprProg rom (Prog.viaC rom p)
  ren : RenameOK romC p (Prog.viaC rom p) romCN
  rset_clear : p.lookup "rset_clear" = some (memoClearG rsetSch)
  erec_alloc : p.lookup "erec_alloc" = some erecAlloc
  iw_alloc : p.lookup "iw_alloc" = some iwAlloc
  rom_basis_decls : p.lookup "rom_basis_decls" = some romBasisDeclsL
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

/-- **The ROM a program reads**: its readers are the copies over the constant data. -/
def RomReady (p : Prog) : Prop := RomCIProg romDataLit p

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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`rom_ci(id)` refines `romCiT id`** (`eqA`, `natA`, the `Iff`/`Nonempty` families). -/
def RomCiRef : Prop := ∀ id : Word, id.toNat < 8 →
  RomRef p "rom_ci" [id] (StageR vis fe) (romCiT id.toNat) (KeepPost vis fe (decRCI dn))
-/

/-- **`rom_cv(id)` refines `romCvT id`**. -/
def RomCvRef : Prop := ∀ id : Word, id.toNat < 10 →
  RomRef p "rom_cv" [id] (StageR vis fe) (romCvT id.toNat) (KeepPost vis fe decRCV)

/-- **`rom_expr_pin(id)` refines `romExprT id`** (the reduce operations' pinned values). -/
def RomExprPinRef : Prop := ∀ id : Word, id.toNat < 2 →
  RomRef p "rom_expr_pin" [id] (StageR vis fe) (romExprT id.toNat) (KeepPost vis fe decW0E)

/-- **`rom_basis_decls(k)` refines `BasisKind.decls`**, for the kinds without `sortZ` names
(all but the quotient block, `RomQuotRef`). -/
def RomBasisRef : Prop := ∀ k : Word, k.toNat < 4 →
  RomRef p "rom_basis_decls" [k] (StageR vis fe) (BasisKind.decls (basisOfW k.toNat))
    (KeepPost vis fe (decRBlk dn))

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`rom_basis_decls_a(k)` refines `BasisKind.declsA`** (as `RomBasisRef`). -/
def RomBasisARef : Prop := ∀ k : Word, k.toNat < 4 →
  RomRef p "rom_basis_decls_a" [k] (StageR vis fe) (BasisKind.declsA (basisOfW k.toNat))
    (KeepPost vis fe (decRBlk dn))
-/

/-- **`rom_basis_decls(4)` refines the quotient block**, from a well-formed twin state that
names `Quot`'s `sortZ` names (`quotNames`) through `dn`. -/
def RomQuotRef : Prop :=
  RomRef p "rom_basis_decls" [4]
    (fun m a => StageR vis fe m a ∧ ConRon.Bridge.StateOK a ∧ NamesDn dn a quotNames)
    (BasisKind.decls (basisOfW 4)) (KeepPost vis fe (decRBlk dn))

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`rom_basis_decls_a(4)` refines the annotated quotient block** (as `RomQuotRef`). -/
def RomQuotARef : Prop :=
  RomRef p "rom_basis_decls_a" [4]
    (fun m a => StageR vis fe m a ∧ ConRon.Bridge.StateOK a ∧ NamesDn dn a quotNames)
    (BasisKind.declsA (basisOfW 4)) (KeepPost vis fe (decRBlk dn))
-/

/-- **`rom_and_pin()` refines `andPinDecls`**. -/
def RomAndPinRef : Prop :=
  RomRef p "rom_and_pin" [] (StageR vis fe) andPinDecls (KeepPost vis fe (decRBlk dn))

/-- All six (the basis readers in two parts, `basis`/`quot`), at every stage. -/
structure RomRefs : Prop where
  basis : ∀ dn vis fe, RomBasisRef p dn vis fe
  quot : ∀ dn vis fe, RomQuotRef p dn vis fe
  andPin : ∀ dn vis fe, RomAndPinRef p dn vis fe

end specs

/- `romRefs_of` (the readers refine the twin) is in `CIReadRefs.lean`, above the proofs. -/

end L.Rom
