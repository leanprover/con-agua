module

public import ConAgua.Final.TwinVerdict
public import ConAgua.Final.CompareTwin
public import ConRon.Arena.Main

@[expose] public section

/-!
# The twin's compared run failing: what a reject or a decline of `--compare` claims

`TwinComparesAccepts` (`Final/CompareTwin.lean`) is the twin's compared run accepting, stage by
stage. `twinCompareRun` is the same run as one twin computation that ends in a verdict, in the
order of con-ron's `compare_json` (`compareJsonTail`, `ConRon/Arena/Main.lean`): the reserved-name
pins, the built-in prelude, the challenge's parse, the solution's, the solution's preparation, the
pins, the solution's check phase (`checkStreamJ` with no solution: the stream index, then every
record's job in order on the index state's worker; the index is kept), the challenge's
preparation, its side records, and its check phase with the solution (`checkStreamJ` at
`solutionOf IS recsC`).

**`TwinCompareVerdict bC bS c`**: at some pin list, `twinCompareRun` fails with an error of class
`c` (`twinCls`: `1` reject, `2` decline), in a stage, in the solution's jobs or in the
challenge's.

**The pool** (`--jobs`): `TwinCompareVerdictPooled` is `TwinCompareVerdict`, or the stages and the
solution's stream index ran ok and some worker's list of the solution's jobs fails, or the
solution's check phase accepted as a pool (`PooledAccepts`), the challenge's stages and stream
index ran ok, and some worker's list of the challenge's jobs fails with the solution.

`twinCompareRun_of_accepts`: `TwinComparesAccepts` is `twinCompareRun` accepting, so at one pin
list the two are exclusive (`twinCompareVerdict_not_accepts`).

The constructors `TwinCompareVerdict.prelude`, `.frontC`, `.frontS`, `.indexS`, `.jobsS`,
`.indexC`, `.jobsC` build it from the stage that failed and the stages before it, which ran ok.
-/

namespace ConAgua.Final

open ConLeche ConRon.Arena ConRon.Arena.Frontend L.Arena

/-- **The twin's compared run as one computation** (con-ron's `compare_json` after its argument
checks, `compareJsonTail`): the stages `TwinComparesAccepts` lists, each check phase a
`checkStreamJ` (the stream index, then every record's job in order, the index kept). -/
def twinCompareRun (pins : List NatOpPinSet) (bC bS : ByteArray) :
    AM (Except (ConRon.Arena.CheckError × Nat) Unit) :=
  internReservedPins >>= fun _ =>
  thenV builtinPreludeE fun pre =>
  thenV (parseChunks [bC]) fun rC =>
  thenV (parseChunks [bS]) fun rS =>
  preparePrelude pre rS.decls >>= fun dsS =>
  internAllPins pins maxNatSizeDefault >>= fun ipins =>
  thenV (checkStreamJ .verified ipins none dsS) fun IS =>
  preparePrelude pre rC.decls >>= fun dsC =>
  sideRecordsGo [] dsC.toList >>= fun recsC =>
  thenV (checkStreamJ .verified ipins (some (solutionOf IS recsC)) recsC.toArray) fun _ =>
  pure (.ok ())

/-- **The twin rejects (`c = 1`) or declines (`c = 2`) the comparison of the challenge `bC` with
the solution `bS`**: at some pin list, its compared run from the start state fails with an error
of class `c`. -/
def TwinCompareVerdict (bC bS : ByteArray) (c : L.Word) : Prop :=
  ∃ pins, TwinFailsV (twinCompareRun pins bC bS) (AState.init EStore.empty) c

/-- **The twin's pooled compared run rejects or declines**: the run fails before the jobs or in
them (`TwinCompareVerdict`), or the stages and the solution's stream index ran ok and some
worker's list of the solution's jobs (record positions) fails from the index state's worker, or
the solution's check phase accepted as a pool, the challenge's stages and stream index ran ok, and
some worker's list of the challenge's jobs fails with the solution, with an error of class `c`. -/
def TwinCompareVerdictPooled (bC bS : ByteArray) (c : L.Word) : Prop :=
  TwinCompareVerdict bC bS c ∨
  (∃ (pins : List NatOpPinSet) (sA sB sC sC' sD sE sF : AState) (pre : PreludeIx)
    (rC rS : ParseResultD) (dsS : Array IDeclaration) (ipins : List INatOpPinSet)
    (IS : IStreamIndex) (w : List Nat),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧
    parseChunks [bC] sB = .ok (.ok rC, sC) ∧
    parseChunks [bS] sC = .ok (.ok rS, sC') ∧
    preparePrelude pre rS.decls sC' = .ok (dsS, sD) ∧
    internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE) ∧
    buildIndex dsS sE = .ok (.ok IS, sF) ∧
    (∀ t ∈ w, t < dsS.size) ∧
    TwinFailsV (checkJobList .verified ipins none IS dsS w) sF.worker c) ∨
  (∃ (pins : List NatOpPinSet) (sA sB sC sC' sD sE sF sG sH sI : AState) (pre : PreludeIx)
    (rC rS : ParseResultD) (dsS dsC : Array IDeclaration) (recsC : List IDeclaration)
    (ipins : List INatOpPinSet) (IS IC : IStreamIndex) (w : List Nat),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧
    parseChunks [bC] sB = .ok (.ok rC, sC) ∧
    parseChunks [bS] sC = .ok (.ok rS, sC') ∧
    preparePrelude pre rS.decls sC' = .ok (dsS, sD) ∧
    internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE) ∧
    PooledAccepts .verified ipins dsS sE IS sF ∧
    preparePrelude pre rC.decls sF = .ok (dsC, sG) ∧
    sideRecordsGo [] dsC.toList sG = .ok (recsC, sH) ∧
    buildIndex recsC.toArray sH = .ok (.ok IC, sI) ∧
    (∀ t ∈ w, t < recsC.length) ∧
    TwinFailsV (checkJobList .verified ipins (some (solutionOf IS recsC)) IC recsC.toArray w)
      sI.worker c)

theorem TwinCompareVerdict.pooled {bC bS : ByteArray} {c : L.Word}
    (h : TwinCompareVerdict bC bS c) : TwinCompareVerdictPooled bC bS c := .inl h

/-! ## `twinCompareRun` is `TwinComparesAccepts`' run -/

theorem checkStreamJ_run_ok {mode : CheckMode} {pins : List INatOpPinSet} {J : Option ISolution}
    {ds : Array IDeclaration} {s s' s'' : AState} {I : IStreamIndex}
    (hI : buildIndex ds s = .ok (.ok I, s'))
    (hJ : checkJobList mode pins J I ds (List.range ds.size) s'.worker = .ok (.ok (), s'')) :
    (checkStreamJ mode pins J ds).run s = .ok (.ok I, s') := by
  show checkStreamJ mode pins J ds s = _
  simp only [checkStreamJ, hI, hJ]

theorem twinCompareRun_of_accepts {bC bS : ByteArray} (h : TwinComparesAccepts bC bS) :
    ∃ pins s, (twinCompareRun pins bC bS).run (AState.init EStore.empty) = .ok (.ok (), s) := by
  obtain ⟨pins, sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, pre, rC, rS, dsS, dsC, recsC, ipins, IS, IC,
    hA, hB, hC, hCS, hDS, hE, ⟨sF', hIS, hJS⟩, hDC, hside, ⟨sI', hIC, hJC⟩⟩ := h
  refine ⟨pins, sI, ?_⟩
  simp only [twinCompareRun, StateT.run_bind, show (internReservedPins).run _ = _ from hA,
    except_ok_bind]
  rw [thenV_run_ok (x := builtinPreludeE) hB, thenV_run_ok (x := parseChunks [bC]) hC,
    thenV_run_ok (x := parseChunks [bS]) hCS]
  simp only [StateT.run_bind, show (preparePrelude pre rS.decls).run sC' = _ from hDS, except_ok_bind,
    show (internAllPins pins maxNatSizeDefault).run sD = _ from hE]
  rw [thenV_run_ok (checkStreamJ_run_ok hIS hJS)]
  simp only [StateT.run_bind, show (preparePrelude pre rC.decls).run sF = _ from hDC, except_ok_bind,
    show (sideRecordsGo [] dsC.toList).run sG = _ from hside]
  rw [thenV_run_ok (checkStreamJ_run_ok hIC hJC)]
  rfl

/-- At one pin list, the compared run does not both accept and fail. -/
theorem twinCompareVerdict_not_accepts {pins : List NatOpPinSet} {bC bS : ByteArray} {c : L.Word}
    {s : AState}
    (hacc : (twinCompareRun pins bC bS).run (AState.init EStore.empty) = .ok (.ok (), s))
    (h : TwinFailsV (twinCompareRun pins bC bS) (AState.init EStore.empty) c) : False := by
  rcases h with ⟨ce, hce, -⟩ | ⟨ce, i, a', hce, -⟩
  · rw [hacc] at hce; cases hce
  · rw [hacc] at hce; cases hce

/-! ## From the stage that failed -/

section stages
variable {bC bS : ByteArray} {c : L.Word}

/-- A check phase's stream index failing ends it. -/
theorem TwinFailsV.checkStreamJ_index {mode : CheckMode} {pins : List INatOpPinSet}
    {J : Option ISolution} {ds : Array IDeclaration} {a : AState} (h : TwinFailsV (buildIndex ds) a c) :
    TwinFailsV (checkStreamJ mode pins J ds) a c := by
  rcases h with ⟨ce, hce, hc⟩ | ⟨ce, i, a', hce, hc⟩
  · exact .inl ⟨ce, by show checkStreamJ mode pins J ds a = _; simp only [checkStreamJ, show buildIndex ds a = _ from hce], hc⟩
  · exact .inr ⟨ce, i, a', by show checkStreamJ mode pins J ds a = _; simp only [checkStreamJ, show buildIndex ds a = _ from hce], hc⟩

/-- A check phase's jobs failing, after its stream index, end it. -/
theorem TwinFailsV.checkStreamJ_jobs {mode : CheckMode} {pins : List INatOpPinSet}
    {J : Option ISolution} {ds : Array IDeclaration} {a a₁ : AState} {I : IStreamIndex}
    (hI : buildIndex ds a = .ok (.ok I, a₁))
    (h : TwinFailsV (checkJobList mode pins J I ds (List.range ds.size)) a₁.worker c) :
    TwinFailsV (checkStreamJ mode pins J ds) a c := by
  rcases h with ⟨ce, hce, hc⟩ | ⟨ce, i, a', hce, hc⟩
  · exact .inl ⟨ce, by
      show checkStreamJ mode pins J ds a = _
      simp only [checkStreamJ, hI, show checkJobList mode pins J I ds (List.range ds.size) a₁.worker = _ from hce], hc⟩
  · exact .inr ⟨ce, i, a₁, by
      show checkStreamJ mode pins J ds a = _
      simp only [checkStreamJ, hI, show checkJobList mode pins J I ds (List.range ds.size) a₁.worker = _ from hce], hc⟩

/-- **The built-in prelude failed.** -/
theorem TwinCompareVerdict.prelude {sA : AState}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (h : TwinFailsV builtinPreludeE sA c) : TwinCompareVerdict bC bS c :=
  ⟨[], TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV h)⟩

/-- **The challenge's parse failed.** -/
theorem TwinCompareVerdict.frontC {sA sB : AState} {pre : PreludeIx}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (h : TwinFailsV (parseChunks [bC]) sB c) : TwinCompareVerdict bC bS c :=
  ⟨[], TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV_ok hB (TwinFailsV.of_thenV h))⟩

/-- **The solution's parse failed**, after the challenge's. -/
theorem TwinCompareVerdict.frontS {sA sB sC : AState} {pre : PreludeIx} {rC : ParseResultD}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks [bC] sB = .ok (.ok rC, sC))
    (h : TwinFailsV (parseChunks [bS]) sC c) : TwinCompareVerdict bC bS c :=
  ⟨[], TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV_ok hB (TwinFailsV.of_thenV_ok hC
    (TwinFailsV.of_thenV h)))⟩

/-- **The solution's stream index failed** (at the pin list `pins`). -/
theorem TwinCompareVerdict.indexS {pins : List NatOpPinSet} {sA sB sC sC' sD sE : AState}
    {pre : PreludeIx} {rC rS : ParseResultD} {dsS : Array IDeclaration} {ipins : List INatOpPinSet}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks [bC] sB = .ok (.ok rC, sC))
    (hCS : parseChunks [bS] sC = .ok (.ok rS, sC'))
    (hDS : preparePrelude pre rS.decls sC' = .ok (dsS, sD))
    (hE : internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE))
    (h : TwinFailsV (buildIndex dsS) sE c) : TwinCompareVerdict bC bS c :=
  ⟨pins, TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV_ok hB (TwinFailsV.of_thenV_ok hC
    (TwinFailsV.of_thenV_ok hCS (TwinFailsV.bind_ok (v := dsS) hDS (TwinFailsV.bind_ok (v := ipins) hE
      (TwinFailsV.of_thenV (TwinFailsV.checkStreamJ_index h)))))))⟩

/-- **The solution's jobs failed** (at the pin list `pins`): every solution record's job, in
order, on the index state's worker, without a solution. -/
theorem TwinCompareVerdict.jobsS {pins : List NatOpPinSet} {sA sB sC sC' sD sE sF : AState}
    {pre : PreludeIx} {rC rS : ParseResultD} {dsS : Array IDeclaration} {ipins : List INatOpPinSet}
    {IS : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks [bC] sB = .ok (.ok rC, sC))
    (hCS : parseChunks [bS] sC = .ok (.ok rS, sC'))
    (hDS : preparePrelude pre rS.decls sC' = .ok (dsS, sD))
    (hE : internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE))
    (hIS : buildIndex dsS sE = .ok (.ok IS, sF))
    (h : TwinFailsV (checkJobList .verified ipins none IS dsS (List.range dsS.size)) sF.worker c) :
    TwinCompareVerdict bC bS c :=
  ⟨pins, TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV_ok hB (TwinFailsV.of_thenV_ok hC
    (TwinFailsV.of_thenV_ok hCS (TwinFailsV.bind_ok (v := dsS) hDS (TwinFailsV.bind_ok (v := ipins) hE
      (TwinFailsV.of_thenV (TwinFailsV.checkStreamJ_jobs hIS h)))))))⟩

/-- **The challenge's stream index failed** (at the pin list `pins`), after the solution's check
phase accepted and the challenge's records were prepared and read with the solution. -/
theorem TwinCompareVerdict.indexC {pins : List NatOpPinSet} {sA sB sC sC' sD sE sF sG sH : AState}
    {pre : PreludeIx} {rC rS : ParseResultD} {dsS dsC : Array IDeclaration}
    {recsC : List IDeclaration} {ipins : List INatOpPinSet} {IS : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks [bC] sB = .ok (.ok rC, sC))
    (hCS : parseChunks [bS] sC = .ok (.ok rS, sC'))
    (hDS : preparePrelude pre rS.decls sC' = .ok (dsS, sD))
    (hE : internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE))
    (hFS : SeqAcceptsJ .verified ipins none dsS sE IS sF)
    (hDC : preparePrelude pre rC.decls sF = .ok (dsC, sG))
    (hside : sideRecordsGo [] dsC.toList sG = .ok (recsC, sH))
    (h : TwinFailsV (buildIndex recsC.toArray) sH c) : TwinCompareVerdict bC bS c := by
  obtain ⟨sF', hIS, hJS⟩ := hFS
  exact ⟨pins, TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV_ok hB (TwinFailsV.of_thenV_ok hC
    (TwinFailsV.of_thenV_ok hCS (TwinFailsV.bind_ok (v := dsS) hDS (TwinFailsV.bind_ok (v := ipins) hE
      (TwinFailsV.of_thenV_ok (checkStreamJ_run_ok hIS hJS) (TwinFailsV.bind_ok (v := dsC) hDC
        (TwinFailsV.bind_ok (v := recsC) hside
          (TwinFailsV.of_thenV (TwinFailsV.checkStreamJ_index h))))))))))⟩

/-- **The challenge's jobs failed** (at the pin list `pins`): every challenge record's job, in
order, on the index state's worker, with the solution `solutionOf IS recsC`. -/
theorem TwinCompareVerdict.jobsC {pins : List NatOpPinSet} {sA sB sC sC' sD sE sF sG sH sI : AState}
    {pre : PreludeIx} {rC rS : ParseResultD} {dsS dsC : Array IDeclaration}
    {recsC : List IDeclaration} {ipins : List INatOpPinSet} {IS IC : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks [bC] sB = .ok (.ok rC, sC))
    (hCS : parseChunks [bS] sC = .ok (.ok rS, sC'))
    (hDS : preparePrelude pre rS.decls sC' = .ok (dsS, sD))
    (hE : internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE))
    (hFS : SeqAcceptsJ .verified ipins none dsS sE IS sF)
    (hDC : preparePrelude pre rC.decls sF = .ok (dsC, sG))
    (hside : sideRecordsGo [] dsC.toList sG = .ok (recsC, sH))
    (hIC : buildIndex recsC.toArray sH = .ok (.ok IC, sI))
    (h : TwinFailsV (checkJobList .verified ipins (some (solutionOf IS recsC)) IC recsC.toArray
      (List.range recsC.toArray.size)) sI.worker c) : TwinCompareVerdict bC bS c := by
  obtain ⟨sF', hIS, hJS⟩ := hFS
  exact ⟨pins, TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV_ok hB (TwinFailsV.of_thenV_ok hC
    (TwinFailsV.of_thenV_ok hCS (TwinFailsV.bind_ok (v := dsS) hDS (TwinFailsV.bind_ok (v := ipins) hE
      (TwinFailsV.of_thenV_ok (checkStreamJ_run_ok hIS hJS) (TwinFailsV.bind_ok (v := dsC) hDC
        (TwinFailsV.bind_ok (v := recsC) hside
          (TwinFailsV.of_thenV (TwinFailsV.checkStreamJ_jobs hIC h))))))))))⟩

end stages

end ConAgua.Final
