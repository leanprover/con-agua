module

public import ConAgua.Front.FrontPreOK
public import ConAgua.Front.DriverRefine
import ConAgua.Front.ChunkBridge
public import ConAgua.Checker.FrontProg
import ConAgua.Verdict.FrontValidE
import ConAgua.Final.TwinVerdict
import all ConAgua.Front.Driver

@[expose] public section

/-!
# Bytes → stores, both outcomes: `front_run`

One unified model and one refinement (`docs/design/unifiede.md`). `front_run()` is `front_init()`
(lifted) and then `front_line(i)` from `i = 0` while `i` is inside the input, as con-ron's
`parseBytes` runs `feedChunk` over the buffer and `applyFinalLine` on its tail (`finishFrom`,
`DriverRefine.lean`). The loop reads `front_line` through its run (`RefC.run_ok`/`RefC.run_err` of
`frontLine_ref`): the next line needs the input bytes kept, a fact of the run (`Keep`).

`loop_ref` is one induction on the fuel, under the driver's invariant after the prelude's records
`D` (`FrontInvOK`; the stream's blank start is `D = #[]`): a `0` result is `finishFrom`'s
acceptance with the invariant after, a failure of class `≠ 0` claims that `finishFrom` fails with
that class (`ErrClaimV`): the lines before ran ok (`finishFrom_next`), the failing one is
`front_line`'s claim (`finishFrom_fail`). `frontRun_ref` adds `front_init` and `StateD.init`.
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open ConLeche.Frontend hiding StateD RecordVerdict applyLine parseBytes ParseResultD parseChunks
  feedChunk applyFinalLine processLineCoreD
open ConRon.Arena ConRon.Arena.Frontend

set_option experimental.vcgen true

namespace L.Front

/-- **`front_run`'s unified model**: `front_init` (outside the verdict closure) lifted, `front_line`
through its run. -/
l_model frontRun_specE (p : Prog) (hf : p.lookup "front_run" = some frontRun)
  fns [hf ↦ frontRunE]
  specs [callW_spec p n "front_init"]
  grind [arena_grind] unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## A failing line ends the twin's parse -/

/-- **A line whose `applyLine` fails or gives a verdict of class `c` ends `finishFrom` so**
(through `feedChunk`, or `applyFinalLine` for a last line without a newline). -/
theorem finishFrom_fail (st : StateD) (b : ByteArray) (i : USize) (lineNo : Nat) (a : AState)
    (r : LineRec) (q : USize) (hi : i < b.usize) (hs : scanLineFwd b i = .ok r q) (c : Word)
    (h : (∃ ce, (applyRecord st r).run a = .error ce ∧ twinCls ce = c) ∨
      ∃ v a', (applyRecord st r).run a = .ok (.inr v, a') ∧ twinCls v.toError = c) :
    TwinFailsV (finishFrom st b i lineNo) a c := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- A claim at the prefixed parse state is one at the twin's own (`applyLine_pre_run`). -/
theorem claimR_of_pre (D : Array IDeclaration) {st : StateD} {r : LineRec} {a : AState} {e : Err}
    (h : VerdictClaimR (applyLine (st.pre D) r) a e) : VerdictClaimR (applyRecord st r) a e := by
  intro hk
  rcases h hk with ⟨ce, hce, hc⟩ | ⟨v, a', hv, hc⟩
  · refine .inl ⟨ce, ?_, hc⟩
    rw [applyLine_pre_run] at hce
    cases hr : (applyRecord st r).run a with
    | error e' => rw [hr] at hce; cases hce; rfl
    | ok x => rw [hr] at hce; cases hce
  · rw [applyLine_pre_run] at hv
    cases hr : (applyRecord st r).run a with
    | error e' => rw [hr] at hv; cases hv
    | ok x =>
      obtain ⟨y, a''⟩ := x
      rw [hr] at hv
      cases y with
      | inl s => exfalso; simp [preL, Except.map] at hv
      | inr w =>
        simp [preL, Except.map] at hv
        obtain ⟨rfl, rfl⟩ := hv
        exact .inr ⟨w, a'', rfl, hc⟩
-/

theorem twinFailsV_of_run_eq {α β : Type} {T T' : AM (Except (ConRon.Arena.CheckError × α) β)}
    {a a' : AState} {c : Word} (h : T.run a = T'.run a') (h' : TwinFailsV T' a' c) : TwinFailsV T a c := by
  rcases h' with ⟨ce, hce, hc⟩ | ⟨ce, i, a'', hce, hc⟩
  · exact .inl ⟨ce, h.trans hce, hc⟩
  · exact .inr ⟨ce, i, a'', h.trans hce, hc⟩

/-! ## One line keeps the invariant -/

/-- **A line con-ron applies keeps the driver's invariant**: `front_line`'s ok fact at the prefixed
parse state (`FrontLinePost`), the input kept, is the twin's step at its own parse state
(`applyLine_pre_*`), with the bridge invariant (`TwinOK.line`), the records' words
(`recOK_line`) and the twin's records (`applyLine_decls`) after. -/
theorem lineStep_ok (D : Array IDeclaration) (b : ByteArray) {m m' : Mem} {i : USize} {nx : Word}
    {st : StateD} {a : AState} (hI : FrontInvOK D b m a st) (hk : m'.arr8 IN = m.arr8 IN)
    (first : Bool) (hS : LineStep b i first nx (st.pre D) a m') (hg : DGrow m m') (hmo : ModeOK m') :
    LineStepI (FrontInvOK D b) b i nx st a m' := by
  sorry

/-! ## The driver -/

/-- What the driver's error arms assume: the lifted callees' closure and the scanner's `safety`
converse on the input (the twin's name reads, `XV`, come from the invariant: `xOfTwin`). -/
structure FrontRunG (p : Prog) (b : ByteArray) : Prop where
  nv : closedNV p _root_.L.Checker.nvFns = true
  safe : SafeLink b

section loop
variable {p : Prog} (hP : LineLookups p) (D : Array IDeclaration) (b : ByteArray)
  (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include hP h64 hsize

/-- **The driver's loop, both outcomes**: from position `i` under the invariant, a `0` result is
`finishFrom`'s acceptance with the invariant after; a failure of class `≠ 0` ends `finishFrom`
with that class. -/
theorem loop_ref : ∀ (n : Nat) (i : USize) (m : Mem) (ln : Word) (st : StateD) (a : AState)
    (lineNo : Nat), FrontInvOK D b m a st → ln.toNat ≤ i.toNat →
    RefC (FrontRunG p b) (frontRunE.loop1 p n m i.toUInt64 ln)
      (fun x => x.1 = 0 → ∃ st' a', (finishFrom st b i lineNo).run a = .ok (.ok (.ofState st'), a') ∧
        FrontInvOK D b x.2 a' st')
      (ErrClaimV (finishFrom st b i lineNo) a) := by
  sorry

/-- **`front_run`, both outcomes**: from a memory holding `b`, related to `a₀` and the blank parse
state after the prelude's records `D`, a `0` result is `parseBytes b`'s acceptance with the
driver's invariant after; a failure of class `≠ 0` claims that `parseBytes b` fails with that
class. -/
theorem frontRun_ref (hpi : p.lookup "front_init" = some frontInit) (n : Nat) {m : Mem}
    {a₀ : AState}
    (h₀ : m.arr8 IN = b.data ∧ ArenaD m a₀ ∧ StateDR m (StateD.blank.pre D) ∧
      ConRon.Bridge.StateOK a₀ ∧ a₀.store.scratchOn = false ∧ ConRon.Bridge.PinsOK a₀ ∧
      (∀ x < D.size, L.Checker.RecOK (m.arr64 DECL) (m.arr64 DLP) x) ∧ ModeOK m) :
    RefC (FrontRunG p b) (frontRunE p n m)
      (fun x => x.1 = 0 → ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧
        FrontInvOK D b x.2 a' st')
      (ErrClaimV (parseBytes b) a₀) := by
  cases n with
  | zero => exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n =>
  simp only [frontRunE]
  rcases h1 : callW p n "front_init" [] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, frontRunE.k_front_init.none]; exact fun _ hk => absurd (by simp) hk
  rw [liftE_some, frontRunE.k_front_init.arm1]
  obtain ⟨s1, rfl, hK1, -, -⟩ := triple_of_callW (frontInitK_spec p hP.apply.decl.expr.front
    hP.apply.decl.expr hpi n ⟨m, Locals.init []⟩) h1
  obtain ⟨st₀, a₁, hrun, hI⟩ := initKW_inv_ok D b m _ a₀ h₀ hK1
  have hu : parseBytes b = (StateD.init >>= fun st => finishFrom st b 0 0) :=
    parseBytes_eq b (by rw [show USize.size = 2 ^ 64 by simp [USize.size, h64]]; omega)
  have hR := loop_ref hP D b h64 hsize (n + 1) 0 s1.mem 0 st₀ a₁ 0 hI (by simp)
  refine RefC.mono hR (fun x hx h0 => ?_) (fun e _ h hk => ?_)
  · obtain ⟨st', a', h1, h2⟩ := hx h0
    exact ⟨st', a', by rw [hu, StateT.run_bind, hrun]; exact h1, h2⟩
  · rw [hu]; exact ConAgua.Final.TwinFailsV.bind_ok hrun (h hk)

end loop

/-! ## The ok half as triples -/

theorem blank_pre_nil : StateD.blank.pre #[] = StateD.blank := by
  simp [StateD.pre, StateD.blank]

theorem pre_nil (st : StateD) : st.pre #[] = st := by
  cases st; simp [StateD.pre]

/-- **Bytes → stores**: when `front_run()` returns `0` on a memory holding the input `b` and
related to the arena state `a₀` (by `ArenaD`) and to the blank parse state, con-ron's
`parseBytes b` accepts from `a₀`, and the memory after is related to its final arena state by
`ArenaD` and to its final parse state by `StateDR` (`frontRun_ref`'s ok half, `D = #[]`). -/
@[refines ConRon.Arena.Frontend.parseBytes]
theorem frontRun_refines {p : Prog} (hP : LineLookups p) (hpi : p.lookup "front_init" = some frontInit)
    (hpd : p.lookup "front_run" = some frontRun) (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data) (a₀ : AState)
    (hA : ArenaD s₀.mem a₀) (hD : StateDR s₀.mem StateD.blank) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem st'; ⊤⦄ :=
  triple_post (RefC.triple (frontRun_specE p hpd n s₀) (frontRun_ref hP #[] b h64 hsize hpi n
      ⟨hm, hA, by rw [blank_pre_nil]; exact hD, hok, hoff, hpins, fun x hx => absurd hx (by simp),
        hmode⟩)) fun _ _ ⟨_, h⟩ h0 => by
    obtain ⟨st', a', h1, ⟨-, h2, h3, -⟩, -⟩ := h h0
    exact ⟨st', a', h1, h2, by rw [← pre_nil st']; exact h3⟩

/-- **Bytes → stores at the checker's program, after the prelude's records `D`**: when `front_run()`
returns `0`, con-ron's `parseBytes b` accepts, the memory after is related to the arena state and
the twin's parse state prefixed by `D`, and every record is `RecOK` (`frontRun_ref`'s ok half,
through `checkerProg_front_run`). -/
theorem frontRunOK_checker (D : Array IDeclaration) (b : ByteArray)
    (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b.data) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem (StateD.blank.pre D)) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀)
    (hR : ∀ x < D.size, L.Checker.RecOK (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) x)
    (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke L.Checker.checkerProg (exec L.Checker.checkerProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem (st'.pre D) ∧ TwinOK a' st' ∧ ModeOK s'.mem ∧
      (∀ x < D.size + st'.decls.size, L.Checker.RecOK (s'.mem.arr64 DECL) (s'.mem.arr64 DLP) x); ⊤⦄ := by
  rw [L.Checker.checkerProg_front_run n]
  exact triple_post (RefC.triple (frontRun_specE frontAllProg rfl n s₀)
      (frontRun_ref frontAllProg_line D b h64 hsize rfl n
        ⟨hm, hA, hD, hok, hoff, hpins, hR, hmode⟩)) fun _ _ ⟨_, h⟩ h0 => by
    obtain ⟨st', a', h1, ⟨-, h2, h3, h4, hM⟩, h5, -⟩ := h h0
    exact ⟨st', a', h1, h2, h3, h4, hM, h5⟩

/-- **`front_run` of the checker's program refines the twin's streaming parse of one chunk**
(`parseChunks [b]`, the checker statement's form; `parseChunks_single`). -/
@[refines ConRon.Arena.Frontend.parseChunks]
theorem frontRun_checker_chunks (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data) (a₀ : AState)
    (hA : ArenaD s₀.mem a₀) (hD : StateDR s₀.mem StateD.blank) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke L.Checker.checkerProg (exec L.Checker.checkerProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseChunks [b]).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem st'; ⊤⦄ := by
  have hu : b.size < USize.size := by
    rw [show USize.size = 2 ^ 64 by simp [USize.size, h64]]; omega
  rw [ConAgua.Front.ChunkBridge.parseChunks_single b hu]
  exact triple_post (frontRunOK_checker #[] b h64 hsize n s₀ hm a₀ hA (by rw [blank_pre_nil]; exact hD)
      hok hoff hpins (fun x hx => absurd hx (by simp)) hmode) fun _ _ h h0 => by
    obtain ⟨st', a', h1, h2, h3, -⟩ := h h0
    exact ⟨st', a', h1, h2, by rw [← pre_nil st']; exact h3⟩

/-- A call into the frontend runs in `frontAllProg` as in `checkerProg`. -/
theorem callE_frontAll {g : FnName} (hg : L.Checker.inFront g = true) (n : Nat) (args : List Word)
    (m : Mem) : callE frontAllProg n g args m = callE L.Checker.checkerProg n g args m := by
  sorry

/-- A failing run is a failing call (`callE`) from its memory. -/
theorem callE_of_run_err {p : Prog} {k : Nat} {f : FnName} {vs : List Word} {s : St} {e : Err}
    (h : (invoke p (exec p k) f vs).run s = .error e) : callE p k f vs s.mem = .error e := by
  rw [invoke_run_loc'] at h
  unfold callE
  cases hr : (invoke p (exec p k) f vs).run ⟨s.mem, Locals.init []⟩ with
  | error e' => rw [hr] at h; cases h; rfl
  | ok v => rw [hr] at h; cases h

/-- **`front_run` at the checker's program, the error half**: a failing call (class `≠ 0`) from
the driver's start claims that `parseBytes b` fails with that class. -/
theorem frontRun_errClaim (D : Array IDeclaration) (b : ByteArray)
    (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) (hSL : SafeLink b) (n : Nat)
    (m : Mem) (a₀ : AState)
    (h₀ : m.arr8 IN = b.data ∧ ArenaD m a₀ ∧ StateDR m (StateD.blank.pre D) ∧
      ConRon.Bridge.StateOK a₀ ∧ a₀.store.scratchOn = false ∧ ConRon.Bridge.PinsOK a₀ ∧
      (∀ x < D.size, L.Checker.RecOK (m.arr64 DECL) (m.arr64 DLP) x) ∧ ModeOK m)
    {e : Err} (he : callE L.Checker.checkerProg n "front_run" [] m = .error e) :
    ErrClaimV (parseBytes b) a₀ e :=
  RefC.run_err (frontRun_specE frontAllProg rfl n ⟨m, Locals.init []⟩) (fun _ h0 h => absurd h0 h)
    L.Front.Ind.frontAllProg_nv ⟨L.Front.Ind.frontAllProg_nv, hSL⟩
    (frontRun_ref frontAllProg_line D b h64 hsize rfl n h₀)
    (by rw [callE_frontAll (by decide) n [] m]; exact he)

end L.Front
