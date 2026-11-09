module

public import ConAgua.Final.Twin
public import ConAgua.Arena.Verdict

@[expose] public section

/-!
# The twin's pipeline failing: what a reject or a decline claims

`TwinAccepts` (`Final/Twin.lean`) is the twin's pipeline accepting, stage by stage. `twinRun` is
the same pipeline as one twin computation that ends in the fold's verdict: the reserved-name pins,
the built-in prelude, the input's parse, `preparePrelude`, the pins, phase A (`installFold`), and
phase B (`checkPendingList`) over every pending record on the phase-A state's worker. A stage that
fails either fails in the monad or reports the failure as a value (`.ok (.error (ce, i))`: the
frontend's line, the fold's position); `TwinFailsV` (`Arena/Verdict.lean`) covers both.

**`TwinVerdict chunks c`**: at some pin list, `twinRun` fails with an error of class `c`
(`twinCls`: `1` for `invalid`, con-ron's exit code 1, a reject; `2` for `notImplemented`, exit
code 2, a decline). The verdict theorems say: when the compiled checker reports an abort of class
`1` or `2`, `TwinVerdict [b] c` holds for that class.

`twinRun_of_accepts`: `TwinAccepts` is `twinRun` accepting, so at one pin list the two are
exclusive (`twinVerdict_not_accepts`).

The constructors `TwinVerdict.prelude`, `.front`, `.fold`, `.phaseB` build it from the stage that
failed and the stages before it, which ran ok.

**The pool** (`--jobs`, con-ron's `PooledAccepts`): phase B is shared among workers, each checking
the records it claimed in order on one state from the phase-A state's worker. `TwinVerdictPooled`
is `TwinVerdict`, or: the stages and phase A ran ok, and some worker's list of pending records,
drawn from the pending list, fails with an error of class `c`.
-/

namespace ConAgua.Final

open ConLeche ConRon.Arena ConRon.Arena.Frontend L.Arena

/-- A stage that reports its failure as a value: on `.error`, the pipeline stops with it. -/
def thenV {α β : Type} (x : AM (Except (ConRon.Arena.CheckError × Nat) α))
    (f : α → AM (Except (ConRon.Arena.CheckError × Nat) β)) :
    AM (Except (ConRon.Arena.CheckError × Nat) β) := fun s =>
  match x s with
  | .ok (.error e, s') => .ok (.error e, s')
  | .ok (.ok v, s') => f v s'
  | .error e => .error e

/-- **The twin's pipeline as one computation**, the stages `TwinAccepts` lists, phase B on the
phase-A state's worker. -/
def twinRun (pins : List NatOpPinSet) (chunks : List ByteArray) :
    AM (Except (ConRon.Arena.CheckError × Nat) Unit) :=
  internReservedPins >>= fun _ =>
  thenV builtinPreludeE fun pre =>
  thenV (parseChunks chunks) fun r =>
  preparePrelude pre r.decls >>= fun ds =>
  internAllPins pins >>= fun ipins =>
  checkStream .verified ipins ds

/-- **The twin rejects (`c = 1`) or declines (`c = 2`) `chunks`**: at some pin list, its pipeline
from the start state fails with an error of class `c`. -/
def TwinVerdict (chunks : List ByteArray) (c : L.Word) : Prop :=
  ∃ pins, TwinFailsV (twinRun pins chunks) (AState.init EStore.empty) c

/-! ## `twinRun` is `TwinAccepts`' pipeline -/

theorem thenV_run_ok {α β : Type} {x : AM (Except (ConRon.Arena.CheckError × Nat) α)}
    {f : α → AM (Except (ConRon.Arena.CheckError × Nat) β)} {a a₁ : AState} {v : α}
    (hx : x.run a = .ok (.ok v, a₁)) : (thenV x f).run a = (f v).run a₁ := by
  show thenV x f a = f v a₁
  simp only [thenV, show x a = _ from hx]

theorem twinRun_of_accepts {chunks : List ByteArray} (h : TwinAccepts chunks) :
    ∃ pins s, (twinRun pins chunks).run (AState.init EStore.empty) = .ok (.ok (), s) := by
  obtain ⟨pins, sA, sB, sC, sD, sE, sF, pre, r, ds, ipins, I, hA, hB, hC, hD, hE, hF⟩ := h
  obtain ⟨s'', hI, hP⟩ := hF
  refine ⟨pins, s'', ?_⟩
  simp only [twinRun, StateT.run_bind, show (internReservedPins).run _ = _ from hA, except_ok_bind]
  rw [thenV_run_ok (x := builtinPreludeE) hB, thenV_run_ok (x := parseChunks chunks) hC]
  simp only [StateT.run_bind, show (preparePrelude pre r.decls).run sC = _ from hD, except_ok_bind,
    show (internAllPins pins).run sD = _ from hE]
  show checkStream .verified ipins ds sE = _
  simp only [checkStream, hI, hP]

/-- At one pin list, the pipeline does not both accept and fail. -/
theorem twinVerdict_not_accepts {pins : List NatOpPinSet} {chunks : List ByteArray} {c : L.Word}
    {s : AState} (hacc : (twinRun pins chunks).run (AState.init EStore.empty) = .ok (.ok (), s))
    (h : TwinFailsV (twinRun pins chunks) (AState.init EStore.empty) c) : False := by
  rcases h with ⟨ce, hce, -⟩ | ⟨ce, i, a', hce, -⟩
  · rw [hacc] at hce; cases hce
  · rw [hacc] at hce; cases hce

/-! ## From the stage that failed -/

section stages
variable {chunks : List ByteArray} {c : L.Word}

theorem TwinFailsV.bind_ok {α γ δ : Type} {x : AM α} {f : α → AM (Except (ConRon.Arena.CheckError × γ) δ)}
    {a a₁ : AState} {v : α} (hx : x.run a = .ok (v, a₁)) (h : TwinFailsV (f v) a₁ c) :
    TwinFailsV (x >>= f) a c := by
  rcases h with ⟨ce, hce, hc⟩ | ⟨ce, i, a', hce, hc⟩
  · exact .inl ⟨ce, by simp only [StateT.run_bind, hx, except_ok_bind]; exact hce, hc⟩
  · exact .inr ⟨ce, i, a', by simp only [StateT.run_bind, hx, except_ok_bind]; exact hce, hc⟩

/-- A stage that fails ends the pipeline. -/
theorem TwinFailsV.of_thenV {α β : Type} {x : AM (Except (ConRon.Arena.CheckError × Nat) α)}
    {f : α → AM (Except (ConRon.Arena.CheckError × Nat) β)} {a : AState}
    (h : TwinFailsV x a c) : TwinFailsV (ConAgua.Final.thenV x f) a c := by
  rcases h with ⟨ce, hce, hc⟩ | ⟨ce, i, a', hce, hc⟩
  · exact .inl ⟨ce, by show ConAgua.Final.thenV x f a = _; simp only [ConAgua.Final.thenV, show x a = _ from hce], hc⟩
  · exact .inr ⟨ce, i, a', by show ConAgua.Final.thenV x f a = _; simp only [ConAgua.Final.thenV, show x a = _ from hce], hc⟩

/-- A stage that ran ok, the rest failing. -/
theorem TwinFailsV.of_thenV_ok {α β : Type} {x : AM (Except (ConRon.Arena.CheckError × Nat) α)}
    {f : α → AM (Except (ConRon.Arena.CheckError × Nat) β)} {a a₁ : AState} {v : α}
    (hx : x.run a = .ok (.ok v, a₁)) (h : TwinFailsV (f v) a₁ c) : TwinFailsV (ConAgua.Final.thenV x f) a c := by
  have hx' : x a = .ok (.ok v, a₁) := hx
  rcases h with ⟨ce, hce, hc⟩ | ⟨ce, i, a', hce, hc⟩
  · exact .inl ⟨ce, by show ConAgua.Final.thenV x f a = _; simp only [ConAgua.Final.thenV, hx']; exact hce, hc⟩
  · exact .inr ⟨ce, i, a', by show ConAgua.Final.thenV x f a = _; simp only [ConAgua.Final.thenV, hx']; exact hce, hc⟩

/-- The stream index failing ends the check phase. -/
theorem TwinFailsV.checkStream_index {mode : CheckMode} {pins : List INatOpPinSet}
    {ds : Array IDeclaration} {a : AState} (h : TwinFailsV (buildIndex ds) a c) :
    TwinFailsV (checkStream mode pins ds) a c := by
  rcases h with ⟨ce, hce, hc⟩ | ⟨ce, i, a', hce, hc⟩
  · exact .inl ⟨ce, by show checkStream mode pins ds a = _; simp only [checkStream, show buildIndex ds a = _ from hce], hc⟩
  · exact .inr ⟨ce, i, a', by show checkStream mode pins ds a = _; simp only [checkStream, show buildIndex ds a = _ from hce], hc⟩

/-- The jobs failing, after the index, end the check phase. -/
theorem TwinFailsV.checkStream_jobs {mode : CheckMode} {pins : List INatOpPinSet}
    {ds : Array IDeclaration} {a a₁ : AState} {I : IStreamIndex}
    (hI : buildIndex ds a = .ok (.ok I, a₁))
    (h : TwinFailsV (checkJobList mode pins I ds (List.range ds.size)) a₁.worker c) :
    TwinFailsV (checkStream mode pins ds) a c := by
  rcases h with ⟨ce, hce, hc⟩ | ⟨ce, i, a', hce, hc⟩
  · exact .inl ⟨ce, by show checkStream mode pins ds a = _; simp only [checkStream, hI]; exact hce, hc⟩
  · exact .inr ⟨ce, i, a', by show checkStream mode pins ds a = _; simp only [checkStream, hI]; exact hce, hc⟩

/-- **The built-in prelude failed.** -/
theorem TwinVerdict.prelude {sA : AState}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (h : TwinFailsV builtinPreludeE sA c) : TwinVerdict chunks c :=
  ⟨[], TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV h)⟩

/-- **The input's parse failed.** -/
theorem TwinVerdict.front {sA sB : AState} {pre : PreludeIx}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (h : TwinFailsV (parseChunks chunks) sB c) : TwinVerdict chunks c :=
  ⟨[], TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV_ok hB (TwinFailsV.of_thenV h))⟩

/-- **The stream index failed** (at the pin list `pins`). -/
theorem TwinVerdict.index {pins : List NatOpPinSet} {sA sB sC sD sE : AState} {pre : PreludeIx}
    {r : ParseResultD} {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunks sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE))
    (h : TwinFailsV (buildIndex ds) sE c) :
    TwinVerdict chunks c :=
  ⟨pins, TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV_ok hB (TwinFailsV.of_thenV_ok hC
    (TwinFailsV.bind_ok (v := ds) hD (TwinFailsV.bind_ok (v := ipins) hE
      (TwinFailsV.checkStream_index h)))))⟩

/-- **The jobs failed** (at the pin list `pins`): every record's job, in order, on the index
state's worker. -/
theorem TwinVerdict.jobs {pins : List NatOpPinSet} {sA sB sC sD sE sF : AState}
    {pre : PreludeIx} {r : ParseResultD} {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    {I : IStreamIndex}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunks sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE))
    (hF : buildIndex ds sE = .ok (.ok I, sF))
    (h : TwinFailsV (checkJobList .verified ipins I ds (List.range ds.size)) sF.worker c) :
    TwinVerdict chunks c :=
  ⟨pins, TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV_ok hB (TwinFailsV.of_thenV_ok hC
    (TwinFailsV.bind_ok (v := ds) hD (TwinFailsV.bind_ok (v := ipins) hE
      (TwinFailsV.checkStream_jobs hF h)))))⟩

end stages

/-! ## The pool -/

/-- **The twin's pool rejects or declines `chunks`**: the pipeline fails before the jobs
(`TwinVerdict`), or the stages and the stream index ran ok and some worker's list of jobs (record
positions) fails from the index state's worker with an error of class `c`, or some record before
the list's jobs does not pass on its own (the approved weakening: "the job fails with class `c`,
or some record below is rejected"). -/
def TwinVerdictPooled (chunks : List ByteArray) (c : L.Word) : Prop :=
  TwinVerdict chunks c ∨
  ∃ (pins : List NatOpPinSet) (sA sB sC sD sE sF : AState) (pre : PreludeIx) (r : ParseResultD)
    (ds : Array IDeclaration) (ipins : List INatOpPinSet) (I : IStreamIndex) (w : List Nat),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧
    parseChunks chunks sB = .ok (.ok r, sC) ∧
    preparePrelude pre r.decls sC = .ok (ds, sD) ∧
    internAllPins pins sD = .ok (ipins, sE) ∧
    buildIndex ds sE = .ok (.ok I, sF) ∧
    (∀ t ∈ w, t < ds.size) ∧
    (TwinFailsV (checkJobList .verified ipins I ds w) sF.worker c ∨
      ∃ i, (∀ t ∈ w, i < t) ∧
        ¬ ∃ s', checkJobList .verified ipins I ds [i] sF.worker = .ok (.ok (), s'))

/-- **Record `i`'s job passes on its own**: at every run of the stages and the stream index, the
twin's job of record `i` from the index state's worker accepts. -/
def TwinJobPasses (chunks : List ByteArray) (i : Nat) : Prop :=
  ∀ (pins : List NatOpPinSet) (sA sB sC sD sE sF : AState) (pre : PreludeIx) (r : ParseResultD)
    (ds : Array IDeclaration) (ipins : List INatOpPinSet) (I : IStreamIndex),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) →
    builtinPreludeE sA = .ok (.ok pre, sB) →
    parseChunks chunks sB = .ok (.ok r, sC) →
    preparePrelude pre r.decls sC = .ok (ds, sD) →
    internAllPins pins sD = .ok (ipins, sE) →
    buildIndex ds sE = .ok (.ok I, sF) →
    ∃ s', checkJobList .verified ipins I ds [i] sF.worker = .ok (.ok (), s')

/-- A record below `j` that does not pass on its own gives the pool's weakened verdict (with the
list `[j]`, `j` a record). -/
theorem TwinVerdictPooled.of_not_passes {chunks : List ByteArray} {c : L.Word} {j : Nat}
    (hj : ∀ (pins : List NatOpPinSet) (sA sB sC sD sE sF : AState) (pre : PreludeIx)
      (r : ParseResultD) (ds : Array IDeclaration) (ipins : List INatOpPinSet) (I : IStreamIndex),
      internReservedPins (AState.init EStore.empty) = .ok ((), sA) →
      builtinPreludeE sA = .ok (.ok pre, sB) →
      parseChunks chunks sB = .ok (.ok r, sC) →
      preparePrelude pre r.decls sC = .ok (ds, sD) →
      internAllPins pins sD = .ok (ipins, sE) →
      buildIndex ds sE = .ok (.ok I, sF) → j < ds.size)
    {i : Nat} (hij : i < j) (h : ¬ TwinJobPasses chunks i) : TwinVerdictPooled chunks c := by
  simp only [TwinJobPasses, Classical.not_forall] at h
  obtain ⟨pins, sA, sB, sC, sD, sE, sF, pre, r, ds, ipins, I, hA, hB, hC, hD, hE, hF, hn⟩ := h
  exact .inr ⟨pins, sA, sB, sC, sD, sE, sF, pre, r, ds, ipins, I, [j], hA, hB, hC, hD, hE, hF,
    by simpa using hj pins sA sB sC sD sE sF pre r ds ipins I hA hB hC hD hE hF,
    .inr ⟨i, by simpa using hij, hn⟩⟩

theorem TwinVerdict.pooled {chunks : List ByteArray} {c : L.Word} (h : TwinVerdict chunks c) :
    TwinVerdictPooled chunks c := .inl h

end ConAgua.Final
