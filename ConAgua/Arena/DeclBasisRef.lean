module

public import ConAgua.Arena.BasisL
public import ConAgua.Rom.CIReadSpec
public import ConAgua.Front.StateDR
public import ConAgua.Arena.StageTLift
public import ConRon.Bridge.Checker.Basis

@[expose] public section

/-!
# The pinned basis blocks' refinements: the statements (lane `ronsync2`, stage 3)

The entry points of `BasisL.lean` that the stream index's `decl_constants` (`IndDeclConsts.lean`)
and the declaration arms call, in the ROM readers' style (`L.Rom.RomRef`: from `StageR` and the
arguments' decodings, the twin's run, `KeepPost` after it):

* `basis_name_hit(o, l)` refines `basisNameHit block` (`BasisNameHitRef`; the result `(hit,
  kind)` as `decHit`);
* `basis_at_block(k, o, l)` refines `BasisKind.atBlock (basisOfW k) block` (`BasisAtBlockRef`; an
  `IW` slice of constant records, `decRBlk`);
* `quot_at(k.slot, q)` refines `quotAt k cv` (`QuotAtRef`; a constant record, `decRCI`).

The block is an `EREC` slice of record pointers (`ind_block_to_erec`'s post: `BlockAt`). The
quotient readers read `rom_basis_decls(4)`, whose refinement wants `Quot`'s `sortZ` names under
`dn` (`L.Rom.RomQuotRef`): `quot_at`'s pre has them.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena L.Rom

/-- **A block at an `EREC` slice** of constant-record pointers `(o, l)`, below the record pool's
top (`ind_block_to_erec`'s post). -/
def BlockAt (o l : Word) (block : List IConstantInfo) (m : Mem) : Prop :=
  L.Front.decCIsR (erecP m) o.toNat l.toNat = some block ∧ o.toNat + l.toNat ≤ erTop m

/-- `basis_name_hit`'s result `Option BasisKind` as `(hit, kind)`: the kind a word below `4`
(`basisOfW`). -/
def decHit (_m : Mem) (r : List Word) : Option ConLeche.BasisKind → Prop
  | none => r.headD 0 = 0
  | some k => r.headD 0 = 1 ∧ (r.tail.headD 0).toNat < 4 ∧ basisOfW (r.tail.headD 0).toNat = k

section specs
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- **`basis_name_hit(o, l)` refines `basisNameHit block`.** -/
def BasisNameHitRef : Prop := ∀ (o l : Word) (block : List IConstantInfo),
  RomRef p "basis_name_hit" [o, l]
    (fun m a => StageT dn vis fe m a ∧ ConRon.Bridge.StateOK a ∧ ConRon.Bridge.ReadOK a ∧
      BlockAt o l block m ∧ ∃ bs, Frontend.denoteCIList a.store block = some bs)
    (ConRon.Arena.basisNameHit block) (KeepPostT dn vis fe decHit)

/-- **`basis_at_block(k, o, l)` refines `BasisKind.atBlock (basisOfW k) block`**, for the four
block kinds `basis_name_hit` returns; the result slice lies below the pool's top (`at_block_go`
returns `(0, 0)` or an `sl_cons` slice), also when it is empty. -/
def BasisAtBlockRef : Prop := ∀ (k o l : Word) (block : List IConstantInfo), k.toNat < 4 →
  RomRef p "basis_at_block" [k, o, l]
    (fun m a => StageT dn vis fe m a ∧ ConRon.Bridge.StateOK a ∧ ConRon.Bridge.ReadOK a ∧
      BlockAt o l block m ∧ ∃ bs, Frontend.denoteCIList a.store block = some bs)
    (ConRon.Arena.BasisKind.atBlock (basisOfW k.toNat) block)
    (fun m m' a r x => KeepPostT dn vis fe (decRBlk dn) m m' a r x ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m')

/-- **`quot_at(k.slot, q)` refines `quotAt k cv`** (`q` an `EREC` constant value), from a
well-formed twin state that names `Quot`'s `sortZ` names through `dn`. -/
def QuotAtRef : Prop := ∀ (k : ConLeche.QuotKind) (q : Word) (cv : IConstantVal),
  RomRef p "quot_at" [UInt64.ofNat k.slot, q]
    (fun m a => StageT dn vis fe m a ∧ ConRon.Bridge.StateOK a ∧ ConRon.Bridge.ReadOK a ∧
      NamesDn dn a quotNames ∧ decCV (erecP m) q.toNat = some cv ∧
      ∃ c, Frontend.denoteCV a.store cv = some c)
    (ConRon.Arena.quotAt k cv) (KeepPostT dn vis fe (decRCI dn))

/-- The three, at every stage. -/
structure BasisRefs : Prop where
  nameHit : ∀ dn vis fe, BasisNameHitRef p dn vis fe
  atBlock : ∀ dn vis fe, BasisAtBlockRef p dn vis fe
  quotAt : ∀ dn vis fe, QuotAtRef p dn vis fe

end specs

/-- **The program `BasisL.lean`'s entry points run in**: its functions, the ROM readers'
refinements (`RomRefs`); the callees outside the module come with the proofs. Consumers take
`BasisRefs`, so this bundle may grow. -/
structure BasisLProg (p : Prog) : Prop where
  fns : ProgHas p basisFns
  rom : RomRefs p

/-- **The basis entry points refine the twin** (stage 3: the proofs). -/
theorem basisRefs_of {p : Prog} (h : BasisLProg p) : BasisRefs p := by
  sorry

end L.Ind
