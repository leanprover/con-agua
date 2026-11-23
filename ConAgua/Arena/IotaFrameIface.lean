module

public import ConAgua.Arena.IotaFrameModels
public import ConAgua.Arena.StripTeleSpec
public import ConAgua.Arena.IndPartsSpec.IndPartsProg2
public import ConAgua.Arena.IndRealSpine
public import ConAgua.Arena.RecClass

@[expose] public section

/-!
# The ι reading rule, part 1: the statements phase 2 builds on (lane ronsync8)

The refinements of the three functions `rule_reads`/`rec_reads` call (`iota_rec_of`,
`iota_parts_of_at`, `iota_parts_at`), each a `RelW` of its run under `StageR` with the record
in memory decoded (`decCV`, `decRule` over `erecP`), the results decoding the twin's by
`IotaReadDec`'s `decOIR`/`decOIP`/`decOIPD` (`KeepPost`: the stage kept, the pool grown).
`IotaFrameProg` names what the proofs need of the program; it gains fields as the proofs land
(callers only pass it on).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- What the phase-1 refinements need of a program. -/
structure IotaFrameProg (p : Prog) : Prop where
  pi_tele : p.lookup "pi_tele" = some piTeleL
  motive_level : p.lookup "motive_level" = some motiveLevelL
  iota_frame : p.lookup "iota_frame" = some iotaFrameL
  is_minor_at : p.lookup "is_minor_at" = some isMinorAtL
  minors_from : p.lookup "minors_from" = some minorsFromL
  iota_read_major : p.lookup "iota_read_major" = some iotaReadMajorL
  iota_rec_of : p.lookup "iota_rec_of" = some iotaRecOfL
  lift_field_doms : p.lookup "lift_field_doms" = some liftFieldDomsL
  lift_idx_args : p.lookup "lift_idx_args" = some liftIdxArgsL
  iota_parts_of_at : p.lookup "iota_parts_of_at" = some iotaPartsOfAtL
  ctor_levels_at : p.lookup "ctor_levels_at" = some ctorLevelsAtL
  iota_bvars : p.lookup "iota_bvars" = some iotaBVarsL
  iota_params_at : p.lookup "iota_params_at" = some iotaParamsAtL
  iota_parts_at_body : p.lookup "iota_parts_at_body" = some iotaPartsAtBodyL
  iota_parts_at : p.lookup "iota_parts_at" = some iotaPartsAtL
  e_view : p.lookup "e_view" = some eView
  gaf : GafF p
  pir : PirF p
  bvar_find : p.lookup "bvar_find" = some bvarFind
  bvar_push : p.lookup "bvar_push" = some bvarPush
  intern_bvar : p.lookup "intern_bvar" = some internBVar
  expr_get_d : p.lookup "expr_get_d" = some exprGetD

/-- **`iota_rec_of(q, mI, rP)` refines `iotaRecOf cv mI rP`** (`q` the recursor's constant value
in `EREC`). -/
theorem iotaRecOf_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (q mI rP : Word) (cv : IConstantVal) :
    RelW (fun m args => callW p n "iota_rec_of" args m) [q, mI, rP]
      (fun m a => StageR vis fe m a ∧ decCV (erecP m) q.toNat = some cv)
      (iotaRecOf cv mI.toNat rP.toNat) (KeepPost vis fe decOIR) := by
  sorry

/-- **`iota_parts_of_at(IotaRec, rP, nIdx, i, r)` refines `iotaPartsOfAt rr rP nIdx i rl`** (the
frame's seven words as decoded by `decIRAt 0`, `r` the rule's record in `EREC`). -/
theorem iotaPartsOfAt_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (r1 r2 r3 r4 r5 r6 r7 rP nIdx i r : Word) (rr : IotaRec) (rl : IRecRule) :
    RelW (fun m args => callW p n "iota_parts_of_at" args m) [r1, r2, r3, r4, r5, r6, r7, rP, nIdx, i, r]
      (fun m a => StageR vis fe m a ∧ decIRAt 0 m [r1, r2, r3, r4, r5, r6, r7] rr ∧
        decRule (erecP m) r.toNat = some rl)
      (iotaPartsOfAt rr rP.toNat nIdx.toNat i.toNat rl) (KeepPost vis fe decOIP) := by
  sorry

/-- **`iota_parts_at(qj, cnP, mI, rP, r)` refines `iotaPartsAt cvj cnP mI rP rl`** (`qj` the
constructor's constant value, `r` the rule's record, both in `EREC`). -/
theorem iotaPartsAt_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (qj cnP mI rP r : Word) (cvj : IConstantVal) (rl : IRecRule) :
    RelW (fun m args => callW p n "iota_parts_at" args m) [qj, cnP, mI, rP, r]
      (fun m a => StageR vis fe m a ∧ decCV (erecP m) qj.toNat = some cvj ∧
        decRule (erecP m) r.toNat = some rl)
      (iotaPartsAt cvj cnP.toNat mI.toNat rP.toNat rl) (KeepPost vis fe decOIPD) := by
  sorry

end L.Ind
