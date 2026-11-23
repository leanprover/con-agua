module

public import ConAgua.Arena.IotaFrameTwin

@[expose] public section

/-!
# The ι reading rule, part 1: the statements phase 2 builds on (lane ronsync8)

The refinements of the three functions `rule_reads`/`rec_reads` call (`iota_rec_of`,
`iota_parts_of_at`, `iota_parts_at`), each a `RelW` of its run under `StageR` with the record
in memory decoded (`decCV`, `decRule` over `erecP`), the results decoding the twin's by
`IotaReadDec`'s `decOIR`/`decOIP`/`decOIPD` (`KeepPost`: the stage kept, the pool grown), the walk
memos `AbsOK` kept (so that the arm restores `StageC` after each call). `iota_parts_at` calls the
core walks `inst_lp_fast` and `instantiate_lift_fast`, so its relation is `StageT` (`KeepPostT`).
`IotaFrameProg` (`IotaFrameBase.lean`) names what the proofs need of the program.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- **`iota_rec_of(q, mI, rP)` refines `iotaRecOf cv mI rP`** (`q` the recursor's constant value
in `EREC`). -/
@[refines ConRon.Arena.iotaRecOf]
theorem iotaRecOf_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (q mI rP : Word) (cv : IConstantVal) :
    RelW (fun m args => callW p n "iota_rec_of" args m) [q, mI, rP]
      (fun m a => StageR vis fe m a ∧ AbsOK m ∧ decCV (erecP m) q.toNat = some cv)
      (iotaRecOf cv mI.toNat rP.toNat)
      (fun m m' a r x => KeepPost vis fe decOIR m m' a r x ∧ AbsOK m') := by
  intro m m' a r hc ⟨hS, hA, hcv⟩
  obtain ⟨x, a', hrun, hK⟩ := iotaRecOf_rel' P n vis fe q mI rP cv m m' a r hc ⟨hS, hcv⟩
  exact ⟨x, a', hrun, hK, iota_afr P (by decide) hc hA⟩

/-- **`iota_parts_of_at(IotaRec, rP, nIdx, i, r)` refines `iotaPartsOfAt rr rP nIdx i rl`** (the
frame's seven words as decoded by `decIRAt 0`, `r` the rule's record in `EREC`). -/
@[refines ConRon.Arena.iotaPartsOfAt]
theorem iotaPartsOfAt_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (r1 r2 r3 r4 r5 r6 r7 rP nIdx i r : Word) (rr : IotaRec) (rl : IRecRule) :
    RelW (fun m args => callW p n "iota_parts_of_at" args m) [r1, r2, r3, r4, r5, r6, r7, rP, nIdx, i, r]
      (fun m a => StageR vis fe m a ∧ AbsOK m ∧ decIRAt 0 m [r1, r2, r3, r4, r5, r6, r7] rr ∧
        decRule (erecP m) r.toNat = some rl)
      (iotaPartsOfAt rr rP.toNat nIdx.toNat i.toNat rl)
      (fun m m' a r x => KeepPost vis fe decOIP m m' a r x ∧ AbsOK m') := by
  intro m m' a r0 hc ⟨hS, hA, hrr, hrl⟩
  obtain ⟨x, a', hrun, hK⟩ :=
    iotaPartsOfAt_rel' P n vis fe r1 r2 r3 r4 r5 r6 r7 rP nIdx i r rr rl m m' a r0 hc ⟨hS, hrr, hrl⟩
  exact ⟨x, a', hrun, hK, iota_afr P (by decide) hc hA⟩

/-- **`iota_parts_at(qj, cnP, mI, rP, r)` refines `iotaPartsAt cvj cnP mI rP rl`** (`qj` the
constructor's constant value, `r` the rule's record, both in `EREC`). It calls the core walk
`inst_lp_fast` after `ctor_levels_at` and `iota_params_at` intern, so it starts from `StageT` and
the twin's `StateOK` with the record's denotations (the interning steps' `PStep`s keep `TwinOK`);
the arm restores `StageT` after it as after the other two (`iotaPartsAt_run`'s `CoreStep`). -/
@[refines ConRon.Arena.iotaPartsAt]
theorem iotaPartsAt_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (qj cnP mI rP r : Word) (cvj : IConstantVal) (rl : IRecRule) :
    RelW (fun m args => callW p n "iota_parts_at" args m) [qj, cnP, mI, rP, r]
      (fun m a => StageT dn vis fe m a ∧ AbsOK m ∧ ConRon.Bridge.StateOK a ∧
        decCV (erecP m) qj.toNat = some cvj ∧ decRule (erecP m) r.toNat = some rl ∧
        (∃ c, ConRon.Arena.Frontend.denoteCV a.store cvj = some c) ∧
        (∃ R, ConRon.Arena.Frontend.denoteRule a.store rl = some R))
      (iotaPartsAt cvj cnP.toNat mI.toNat rP.toNat rl)
      (fun m m' a r x => KeepPost vis fe decOIPD m m' a r x ∧ AbsOK m') :=
  iotaPartsAt_rel' P n dn vis fe qj cnP mI rP r cvj rl

end L.Ind
