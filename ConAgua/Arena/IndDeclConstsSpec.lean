module

public import ConAgua.Arena.IndDeclConsts
public import ConAgua.Arena.DeclAndPinIndDec
public import ConAgua.Front.StateDR
public import ConRon.Arena.Install
public import ConAgua.Arena.LoopT
public import ConAgua.Rom.CIReadSpec
public import ConAgua.Arena.IndStubs
public import ConAgua.Arena.TwinStep

@[expose] public section

/-!
# What a declaration installs: the refinements (lane `ronsync2`, stage 3)

`decl_constants(i)` refines `declConstants d` and `decl_tables(i)` refines `declTables d` for
every record `i` the front produces (`DeclAtF`), in the stage's shape (`RefAM`, `StageR`,
`KeepPost`, `IndIface.lean`): the stream index's builder (`idx_add`, `CheckerL.lean`) reads its
rows off these. The results are `IW` slices of `EREC` record pointers (`decCIL`, `decTblL`), below
the pool's top; the inductive memos (`IndMemos`) and what the builder reads (`IdxKeep`) are kept.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena
open L.Front (DECL DLP)

/-- The results `(off, len)`: an `IW` slice of `EREC` constant-record pointers. -/
def decCIL (m : Mem) (r : List Word) (L : List IConstantInfo) : Prop :=
  decRL (fun m o l => decPL m (fun q => decCI (erecP m) q) o l) 0 m r L

/-- The results `(off, len)`: an `IW` slice of `EREC` table-record pointers. -/
def decTblL (m : Mem) (r : List Word) (Q : List IProjTable) : Prop :=
  decRL (fun m o l => decPL m (fun q => decTbl (erecP m) q) o l) 0 m r Q

/-- **The twin-side invariants both need and give back**: the twin's invariants beyond `CheckR`
(`TwinOK`), the pin table filled, the walk memos outside the stage relation (`AbsOK`), and con-ron's
`CheckOK` at some environment (with `TwinOK`, `StageC`: `block_shape`'s refinement,
`blockShape_refinesC`, needs it; `struct_proj_bodies`' needs `AbsOK`). -/
structure DeclTwin (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (m : Mem) (a : AState) : Prop where
  twin : TwinOK dn m a fe
  pin : pinW m 0 ≠ 0
  abs : AbsOK m
  chk : ∃ env, ConRon.Bridge.CheckOK false env fe a

/-- The pre-condition of both: the stage relation, the record `i` the declaration `d` (an
inductive block of the front's shape), the twin state's invariant, the inductive memos. -/
structure DeclConstsPre (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (i : Word)
    (d : IDeclaration) (m : Mem) (a : AState) : Prop where
  stage : StageR vis fe m a
  decl : L.Front.DeclAtF (m.arr64 DECL) (m.arr64 DLP) i.toNat d
  front : ∀ b nP, d = .indDecl b nP → FrontBlock b
  ok : ConRon.Bridge.StateOK a
  /-- `Quot`'s `sortZ` names under `dn` (`quot_at`'s pre, `L.Rom.QuotAtRef`). -/
  quotDn : L.Rom.NamesDn dn a L.Rom.quotNames
  memos : IndMemos m
  dsize : (m.arr64 DECL).size < 2 ^ 63
  psize : (m.arr64 DLP).size < 2 ^ 63
  /-- The scratch tier is closed (the stream index's build): every record lands in `EREC` tier 0,
  `CTL[130]` stays. -/
  off : a.store.scratchOn = false
  /-- The twin-side invariants (`DeclTwin`). -/
  tw : DeclTwin dn fe m a

/-- What the stream index's builder keeps across the two: the front's records (`DECL`, `DLP`), the
first counters (`FIRSTS`), the index rows (arrays 129‥134, both tiers) and the counters `CTL[128]`, `CTL[130]` and the core's memos. -/
structure IdxKeep (m m' : Mem) : Prop where
  arr : ∀ b : TieredArray, (b.arr = DECL ∨ b.arr = DLP ∨ b.arr = L.Arena.FIRSTS ∨
    (129 ≤ b.arr ∧ b.arr ≤ 134)) → m'.arr64 b = m.arr64 b
  ctl128 : rdW (m'.arr64 CTL) 128 = rdW (m.arr64 CTL) 128
  ctl130 : rdW (m'.arr64 CTL) 130 = rdW (m.arr64 CTL) 130
  memos : CoreMemos m → CoreMemos m'

/-- The lookups the two refinements take. -/
structure DeclConstsProg (p : Prog) : Prop where
  decl_constants : p.lookup "decl_constants" = some declConstants
  decl_constants_axiom : p.lookup "decl_constants_axiom" = some declConstantsAxiom
  decl_constants_ind : p.lookup "decl_constants_ind" = some declConstantsInd
  decl_tables : p.lookup "decl_tables" = some declTables
  block_constants : p.lookup "block_constants" = some blockConstants
  block_tables : p.lookup "block_tables" = some blockTables

/-- **`decl_constants(i)` refines `declConstants d`**: the constants record `i` installs, in
push order, an `IW` slice of `EREC` constant records. -/
@[refines ConRon.Arena.declConstants]
theorem declConstants_refines {p : Prog} (hp : DeclConstsProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv)
    (i : Word) (d : IDeclaration) :
    RefAM p "decl_constants" [i] (DeclConstsPre dn vis fe i d) (ConRon.Arena.declConstants d)
      (fun m m' a r x => KeepPost vis fe decCIL m m' a r x ∧ IndMemos m' ∧ IdxKeep m m' ∧
        DeclTwin dn fe m' a) := by
  sorry

/-- **`decl_tables(i)` refines `declTables d`**: the projection tables record `i` installs, an
`IW` slice of `EREC` table records. -/
@[refines ConRon.Arena.declTables]
theorem declTables_refines {p : Prog} (hp : DeclConstsProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv)
    (i : Word) (d : IDeclaration) :
    RefAM p "decl_tables" [i] (DeclConstsPre dn vis fe i d) (ConRon.Arena.declTables d)
      (fun m m' a r x => KeepPost vis fe decTblL m m' a r x ∧ IndMemos m' ∧ IdxKeep m m' ∧
        DeclTwin dn fe m' a) := by
  sorry

end L.Ind
