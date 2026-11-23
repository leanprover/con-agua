module

public import ConAgua.Checker.PhaseBReads
public import ConAgua.Checker.JobsStart
import ConAgua.Checker.RomProgInit
import ConRon.Bridge.Checker.Pool
import ConRon.Bridge.Checker.Hyp
import ConRon.Bridge.Checker.Install
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Stages
import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.PhaseBReads
meta import ConAgua.Arena.FreezeRel
meta import ConAgua.Checker.LoopProgTac
meta import ConAgua.Final.Statement
import ConAgua.L.Blocks
import all ConAgua.Checker.Entry
import ConAgua.Arena.JobStart
public import ConAgua.Arena.PoolJobs

@[expose] public section

/-!
# The jobs of the sequential driver's entry 2, in L (lane parmode, stage 3 of lane ronsync2)

docs/design/parmode.md, "Redesign". The driver's entry 2 (`ca_check_seq`) runs `check` with the mode
word `2` on a memory `w` that is phase A's memory `m` except in the arrays the jobs never name
(`OUT`, the header `HDRF`, the seed `CTLF`, the byte arrays) and in the globals. `check_b` flushes
the core caches and runs `check_jobs(0, k)`. Then:

* `flushMem_agree`: the flush keeps an agreement that covers `CTL`;
* `poolHyps_of_phaseA`: the twin's side of the pool's induction (`PoolHyps`) at an accepting
  phase A, as con-ron's `pooledAccepts_bridge` assembles it;
* `checkJobs_seq`: a returning `check_jobs(0, k)` on a memory that agrees with the flushed `m` is
  the twin's `checkJobList` over every record accepting from the index state's worker
  (`L/Agree.lean`'s non-interference over `checkerProg_phaseBReads`, then `checkJobsLoop_chain`
  and `pool_twin` with one worker over `JobRel`).
-/

set_option experimental.vcgen true

open ConRon.Arena ConRon.Bridge
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena

universe w

-- `check_b` (`checkBL`, `ConAgua/Checker/Entry.lean`) returns the literal `ACCEPT`.
example : (71757147230292 : Word) = ConAgua.Final.ACCEPT := rfl

/-- The arrays phase B's loop may name: every word array but `OUT`, `HDRF`, `CTLF`. -/
abbrev phaseBS : TieredArray → Bool := phaseBPa

theorem checkerProg_lookup_check_b : checkerProg.lookup "check_b" = some checkBL := by chk_lk
theorem checkerProg_lookup_check' : checkerProg.lookup "check" = some checkL := by chk_lk

/-! ## The flush keeps an agreement -/

theorem mclearG_agree {S : TieredArray → Bool} {S8 : ArrId → Bool} {m₁ m₂ : Mem}
    (h : Agree S S8 m₁ m₂) (hc : S CTL = true) (Sch : MemoSch) :
    Agree S S8 (mclearG Sch m₁) (mclearG Sch m₂) := by
  unfold mclearG
  have e : m₁.arr64 CTL = m₂.arr64 CTL := h.1 CTL hc
  have h1 := h.set64 hc Sch.cs (rdW (m₁.arr64 CTL) Sch.cs + 1)
  have h2 := h1.set64 hc (Sch.cs + 1) 0
  rw [e] at h2 ⊢
  exact h2

theorem flushMem_agree {S : TieredArray → Bool} {S8 : ArrId → Bool} {m₁ m₂ : Mem}
    (h : Agree S S8 m₁ m₂) (hc : S CTL = true) : Agree S S8 (flushMem m₁) (flushMem m₂) := by
  have g := fun (Sch : MemoSch) {x y : Mem} (hxy : Agree S S8 x y) => mclearG_agree hxy hc Sch
  exact g _ (g _ (g _ (g _ (g _ (g _ (g _ (g _ (g _ (g _ (g _ h))))))))))

/-! ## The twin's side of the pool at an accepting phase A -/

local notation "VM" => ConLeche.CheckMode.verified

/-- **The pool's twin facts at an accepting phase A** (con-ron's `pooledAccepts_bridge`): the
driver state after the index build, its pins and records denoting, the index denoting, for any
worker step `hstep`. -/
theorem poolHyps_of_phaseA {b : ByteArray} (PA : PhaseA b) {σ : Type} (Rel : σ → AState → Prop)
    (Call : Nat → σ → σ → Prop) :
    ∃ (pinsP : List ConLeche.NatOpPinSet) (dsP : List ConLeche.Declaration),
      StateOK PA.sF ∧ (ConRon.Bridge.RecordSpec PA.ipins pinsP) ∧ PersPinSets PA.ipins ∧
      (∀ x ∈ PA.ds.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl PA.sF.store x = some d) ∧
      PinsDenote PA.sF.store PA.ipins pinsP ∧
      ((∀ (k : Nat) (r r' : σ) (a : AState) (hk : k < PA.ds.size), Rel r a → Call k r r' →
        (∃ env, FoldOK env (PA.I.view k) (AM.st enterScratch a)) →
        ∃ a', recordJob VM PA.ipins none PA.I k PA.ds[k] a = .ok ((), a') ∧ Rel r' a') →
      PoolHyps (pins := PA.ipins) (pinsP := pinsP) (ds := PA.ds) (dsP := dsP) (I := PA.I)
        (s₁ := PA.sF) Rel Call) := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := PA.pfx
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpd, rc, preC, -, hden⟩ :=
    ConRon.Bridge.stages_frame (chunks := [b]) hA hB hC hD hE
  obtain ⟨hst', hx, hp', -, hI, hpI⟩ := buildIndex_run constsSpec tablesSpec hst hpp hoff hpd hden PA.idx
  have hx' := PExt.of_ext hx
  obtain ⟨hlen, hget⟩ := denoteDecls_getElem hden
  have hden' : ∀ (i : Nat) (hi : i < PA.ds.size), ∃ hi' : i < (ConLeche.Frontend.preparePrelude preC rc.decls).toList.length,
      Frontend.denoteDecl PA.sF.store PA.ds[i] = some (ConLeche.Frontend.preparePrelude preC rc.decls).toList[i] :=
    fun i hi => by
      obtain ⟨hi', h⟩ := hget i (by simpa using hi)
      exact ⟨hi', Frontend.denoteDecl_ext hx (by simpa using h)⟩
  have hrec : RecordSpec PA.ipins PA.pins :=
    recordSpec (CoreSpec.of_core) ConRon.Bridge.Inductives.indSpec_of_bridge
  have hPD := PinsDenote.mono hx PA.ipins PA.pins hipins
  refine ⟨PA.pins, _, hst'.state, hrec, hpps, fun x hx'' => ⟨hpd x hx'', ?_⟩, hPD, fun hstep =>
    { hrec := hrec, hpush := kernelPushes _, hpp := hpps,
      hpinsOK := hst.pins.pmono hpp hx' hp', hpersPins := hpp.mono hp', hpins := hPD,
      hpd := hpd, hlen := by simpa using hlen, hden := hden', hI := hI, hpI := hpI,
      hstep := hstep }⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx''
  obtain ⟨_, hd⟩ := hden' i (by simpa using hi)
  exact ⟨_, by simpa using hd⟩

/-! ## The jobs on the sequential driver's memory -/

theorem mclearG_bytes (Sch : MemoSch) (m : Mem) : (mclearG Sch m).bytes = m.bytes := rfl

theorem flushMem_bytes (m : Mem) : (flushMem m).bytes = m.bytes := by
  simp only [flushMem, flushClears, mclearG_bytes]

theorem mclearG_glob (Sch : MemoSch) (m : Mem) : (mclearG Sch m).glob = m.glob := rfl

theorem flushMem_glob (m : Mem) : (flushMem m).glob = m.glob := by
  simp only [flushMem, flushClears, mclearG_glob]

theorem callE_of_run {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {s : St} {r : List Word}
    {s' : St} (h : (invoke p (exec p n) f vs).run s = .ok (r, s')) :
    callE p n f vs s.mem = .ok (r, s'.mem) := by
  rw [invoke_run_loc'] at h
  simp only [callE]
  cases hh : (invoke p (exec p n) f vs).run { mem := s.mem, loc := Locals.init [] } with
  | error e => simp [hh, Except.map] at h
  | ok q =>
    simp [hh, Except.map] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- **The sequential driver's jobs**: a returning `check_jobs(0, k)` (`k` the number of records)
on a memory that agrees with the flushed memory after the index build on every array the jobs
name means the twin's jobs over every record accept from the index state's worker. -/
theorem checkJobs_seq {b pb : ByteArray}
    {sz : TieredArray → Nat} {PA : PhaseA b} {m₇ m : Mem}
    (hF : FoldAt b pb sz PA m₇ m) (hfok : FlushOK m)
    (hJP : JobProg PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg))
    {n : Nat} (hn : n ≤ 2 ^ 62) {s : St} {hi : Word} (hhi : hi.toNat = PA.ds.size)
    (hag : ∀ a, phaseBS a = true → s.mem.arr64 a = (flushMem m).arr64 a)
    {rs : List Word} {s' : St}
    (hrun : (invoke checkerProg (exec checkerProg n) "check_jobs" [0, hi]).run s = .ok (rs, s')) :
    ∃ s'', checkJobList VM PA.ipins none PA.I PA.ds (List.range PA.ds.size) PA.sF.worker =
      .ok (.ok (), s'') := by
  let p := Prog.subPB pb.data.toList checkerProg
  have hJ0 : JobR PA.ipins (dnOf PA.sE.store) PA.ds PA.I (flushMem m) { PA.sF with caches := Caches.empty } :=
    hF.jobR hfok
  have hby : (flushMem m).bytes = m₇.bytes := by rw [flushMem_bytes, hF.bytes]
  generalize flushMem m = F at hJ0 hag hby
  -- the flushed memory with the run's globals
  let s₂ : St := ⟨⟨F.bytes, F.words, s.mem.glob⟩, s.loc⟩
  have hAg : Agree phaseBS (fun _ => false) s.mem s₂.mem :=
    ⟨fun a ha => hag a ha, fun _ h => absurd h (by simp), rfl⟩
  obtain ⟨s₂', hrun₂, -, -⟩ :=
    invoke_agree_ok checkerProg_phaseBReads check_jobs_mem_phaseBJobFns hAg rfl hrun
  have hPB : s₂.mem.arr8 L.Rom.PB = pb.data.toList.toArray := by
    show F.bytes L.Rom.PB = _
    rw [hby, ← Mem.arr8, hF.r7.since.keep.arr8]
    exact loadMem_pb b pb sz
  rw [← L.Rom.invoke_subPB (bs := pb.data.toList) checkerProg_noSt8PB n _ _ (s := s₂) hPB] at hrun₂
  have hc := callE_of_run hrun₂
  -- the model of `check_jobs`
  obtain ⟨_s3, -, -, hx⟩ := triple_of_callE
    (checkJobs_specE p hJP.check_jobs n ⟨s₂.mem, Locals.init []⟩ 0 hi) hc
  rcases n with _ | n
  · obtain ⟨e, he, -⟩ := callE_zero p "check_jobs" [0, hi] s₂.mem
    rw [hc] at he; cases he
  have hx' : checkJobsE.k_loop1 p (checkJobsE.loop1 p (n + 1) s₂.mem 0 hi) = _ := hx
  cases hl : checkJobsE.loop1 p (n + 1) s₂.mem 0 hi with
  | error ε => rw [hl] at hx'; cases hx'
  | ok q =>
  have hch := checkJobsLoop_chain (n + 1) (by omega) s₂.mem 0 q hl
  simp only [UInt64.toNat_zero, Nat.sub_zero, hhi] at hch
  -- the twin's side
  obtain ⟨pinsP, dsP, hst, hrec, hpp, hden, hPD, hH⟩ := poolHyps_of_phaseA PA
    (JobRel PA.ipins (dnOf PA.sE.store) PA.ds PA.I { PA.sF with caches := Caches.empty }) (RecCall p)
  have hpx := PA.pfx
  obtain ⟨hA, hB, hC, hD, hE⟩ := hpx
  obtain ⟨-, -, -, -, -, hpd, _rc, _preC, -, hden0⟩ :=
    ConRon.Bridge.stages_frame (chunks := [b]) hA hB hC hD hE
  have hFD : FrontDecls PA.ds := frontDecls_of_prefix PA.pfx
  have hLD : DeclsLpsDn (dnOf PA.sE.store) PA.ds := declsLpsDn_dnOf hpd ⟨_, hden0⟩
  have hdn : DnPers (dnOf PA.sE.store) := fun k x hk => by
    simp only [dnOf] at hk; split at hk
    · assumption
    · cases hk
  have hds : PA.ds.size < 2 ^ 64 := by rw [← hhi]; exact UInt64.toNat_lt hi
  have H := hH (recCall_stepE hJP hFD hLD hdn hrec hpp hds hden hPD)
  have hJ : JobR PA.ipins (dnOf PA.sE.store) PA.ds PA.I s₂.mem { PA.sF with caches := Caches.empty } :=
    hJ0.setGlob _
  obtain ⟨-, hacc⟩ := pool_twin H hst [(s₂.mem, List.range PA.ds.size)]
    (fun t ht => by
      rw [List.mem_singleton] at ht; subst ht
      exact ⟨_, ⟨hJ, PExt.of_ext (Ext.refl _), rfl⟩, sameEnter_worker.symm⟩)
    (fun t ht => by rw [List.mem_singleton] at ht; subst ht; rw [List.range_eq_range']; exact hch)
    (fun t ht => by rw [List.mem_singleton] at ht; subst ht; exact List.pairwise_lt_range)
    (fun t ht k hk => by rw [List.mem_singleton] at ht; subst ht; exact List.mem_range.mp hk)
    (fun k hk => ⟨_, List.mem_singleton_self _, List.mem_range.mpr hk⟩)
  exact hacc _ (List.mem_singleton_self _)

/-! ## `check_b` in place -/

theorem mclearG_words {m₁ m₂ : Mem} (he : m₁.words = m₂.words) (Sch : MemoSch) :
    (mclearG Sch m₁).words = (mclearG Sch m₂).words := by
  unfold mclearG Mem.set64 Mem.arr64; simp only [he]

theorem flushMem_words {m₁ m₂ : Mem} (he : m₁.words = m₂.words) :
    (flushMem m₁).words = (flushMem m₂).words := by
  have g := fun (Sch : MemoSch) {x y : Mem} (hxy : x.words = y.words) => mclearG_words hxy Sch
  exact g _ (g _ (g _ (g _ (g _ (g _ (g _ (g _ (g _ (g _ (g _ he))))))))))

theorem clearsOK_agree {S : TieredArray → Bool} {S8 : ArrId → Bool} (hc : S CTL = true) :
    ∀ (l : List MemoSch) {m₁ m₂ : Mem}, Agree S S8 m₁ m₂ → ClearsOK l m₁ → ClearsOK l m₂
  | [], _, _, _, _ => trivial
  | Sch :: l, _, _, h, ⟨h1, h2⟩ =>
    ⟨by rw [← h.1 CTL hc]; exact h1, clearsOK_agree hc l (mclearG_agree h hc Sch) h2⟩

theorem clearsOK_words : ∀ (l : List MemoSch) {m₁ m₂ : Mem}, m₁.words = m₂.words →
    ClearsOK l m₁ → ClearsOK l m₂
  | [], _, _, _, _ => trivial
  | Sch :: l, _, _, he, ⟨h1, h2⟩ =>
    ⟨by simp only [Mem.arr64, ← he]; exact h1, clearsOK_words l (mclearG_words he Sch) h2⟩

/-- **`check_jobs` after the flush**, as a triple: from a memory that is the flush of one agreeing
with `m` on every array the jobs name. -/
theorem checkJobs_seqT {b pb : ByteArray}
    {sz : TieredArray → Nat} {PA : PhaseA b} {m₇ m : Mem}
    (hF : FoldAt b pb sz PA m₇ m)
    (hJP : JobProg PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (hi : Word) (hhi : hi.toNat = PA.ds.size) (x y : Word) :
    ⦃fun s => x = 0 ∧ y = hi ∧ ∃ X, FlushOK X ∧ s.mem = flushMem X ∧
      ∀ a, phaseBS a = true → X.arr64 a = m.arr64 a⦄
    invoke checkerProg (exec checkerProg n) "check_jobs" [x, y]
    ⦃fun _ _ => ∃ s'', checkJobList VM PA.ipins none PA.I PA.ds (List.range PA.ds.size) PA.sF.worker =
      .ok (.ok (), s''); ⊤⦄ := by
  apply M.triple_of_run
  rintro s rs s' ⟨rfl, rfl, X, hfx, hsX, hXm⟩ hrun
  let m₂ : Mem := ⟨m.bytes, m.words, X.glob⟩
  have hAg : Agree phaseBS (fun _ => false) X m₂ :=
    ⟨fun a ha => hXm a ha, fun _ h => absurd h (by simp), rfl⟩
  have hc : phaseBS CTL = true := by decide
  have hfok : FlushOK m := by
    rw [flushOK_eq] at hfx ⊢
    exact clearsOK_words _ (m₁ := m₂) (m₂ := m) rfl (clearsOK_agree hc _ hAg hfx)
  have hA2 := flushMem_agree hAg hc
  have hw2 : (flushMem m₂).words = (flushMem m).words := flushMem_words rfl
  exact checkJobs_seq hF hfok hJP hn hhi (fun a ha => by
    rw [hsX, hA2.1 a ha]; show (flushMem m₂).words a = (flushMem m).words a; rw [hw2]) hrun

theorem checkerProg_flushProg : FlushProg checkerProg := by
  constructor <;> chk_lk

/-- **Entry 2 in place, `check_b`**: from a memory that agrees with the memory after the index
build on every array the jobs name, with the range `[0, k)` (`k` the number of records) and an
empty seed `CTLF`, a run that returns `ACCEPT` means the twin's jobs over every record accept from
the index state's worker. -/
theorem checkB_seq {b pb : ByteArray}
    {sz : TieredArray → Nat} {PA : PhaseA b} {m₇ m : Mem}
    (hF : FoldAt b pb sz PA m₇ m)
    (hJP : JobProg PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (hi : Word) (hhi : hi.toNat = PA.ds.size) (s₀ : St)
    (hw : ∀ a, phaseBS a = true → s₀.mem.arr64 a = m.arr64 a)
    (hlo : s₀.mem.glob PLO = 0) (hhi' : s₀.mem.glob PHI = hi) (hctlf : (s₀.mem.arr64 CTLF).size = 0) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun r _ => r.headD 0 = ConAgua.Final.ACCEPT →
      ∃ s'', checkJobList VM PA.ipins none PA.I PA.ds (List.range PA.ds.size) PA.sF.worker =
        .ok (.ok (), s''); ⊤⦄ := by
  have hl : (UInt64.toNat (s₀.mem.len64 CTLF)) = 0 := by simp [Mem.len64, hctlf]
  have hlo' : s₀.mem.glob ⟨9⟩ = 0 := hlo
  have hhi'' : s₀.mem.glob ⟨11⟩ = hi := hhi'
  rw [invoke_eq _ checkerProg_lookup_check_b]
  simp only [callFn, checkBL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hJ := checkJobs_seqT hF hJP n (by omega) hi hhi
    have hFl := flushCaches_spec checkerProg checkerProg_flushProg n
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, setG, ld64, warr, (hJ · ·), (hFl ·)]
    all_goals (try simp only [L.St.setLoc_mem, St.setLoc_loc,
      L.Locals.init_nil, Cmp.eval,
      reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
    all_goals (try simp only [hl, Mem.copy64_zero] at *)
    all_goals (try simp only [St.setG, Mem.setG, St.setLoc] at *)
    all_goals first
      | (simp_all (config := { decide := true }) [Mem.arr64]; done)
      | skip
    all_goals
      obtain ⟨-, hfx, hm⟩ := ‹LocEq _ _ ∧ FlushOK _ ∧ _›
      first
        | exact ⟨_, hfx, by rw [L.St.setLocs_mem]; exact hm, fun a ha => hw a ha⟩
        | (rw [L.St.setLocs_mem, hm, flushMem_glob]; simp_all)

end L.Checker
