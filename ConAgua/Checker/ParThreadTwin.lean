module

public import ConAgua.Checker.ParThreadCall
public import ConAgua.Checker.ParDriverTwin
import ConAgua.Arena.FreezeFresh
import ConAgua.Checker.RomProgInit
public import ConAgua.Final.TwinPooled
import ConAgua.Checker.CheckARun
import ConAgua.Checker.LoopStage
import ConAgua.Checker.RomProg0

@[expose] public section

/-!
# The threads' runs give `TwinAcceptsPooled` (lane parmode)

docs/design/parmode.md, "Step 4". Entry 1 (`check` with the mode word `1`) returns `2^63 + k` and
leaves the buffer `B` (the first `len` words of `OUT`, `len` the header's word `1`). Each thread
then calls entry 2 once per group index it claimed, in order, on its own region: call `i` runs
`check` on `bufMem B rᵢ₋₁ jᵢ` (`r₀` the fresh region) and leaves `rᵢ`.

* `ThreadRuns B r cs`: the calls `cs` (group index, fuel, final memory) from region memory `r`, each
  a run that returns, after which the buffer is unchanged (`BufKept`: the final memory's frozen
  arrays, but the header and the seed, are `B`'s images; the machine level supplies it, the buffer
  is read-only).
* `thread_chain`, `thread_accepts`: the claimed groups, in order, are accepted by
  `checkPendingList` from phase A's worker state (`thrCall_first`, then `thrCall_next`).
* `threads_pool`: threads that together claim every group index below `k` give con-ron's pool
  (`PooledAccepts`'s three parts).
* `threads_twinAcceptsPooled`: with entry 1's run, `TwinAcceptsPooled [b]`.
-/

open ConRon.Arena ConAgua.Final

namespace L.Checker

open L L.Arena L.Rom ConRon.Bridge

universe w

/-- **The buffer is unchanged** at the end of a call: the final memory's frozen arrays (but the
header and the seed) are `B`'s images. -/
def BufKept (B : Array Word) (r : Mem) : Prop :=
  ∀ k (hk : k < frozen.length), 1 ≤ k → r.arr64 frozen[k].1 = bufImg B (k + 1)

/-- **A thread's calls** `cs` (group index `j`, fuel `n`, final memory `r'`) from the region memory
`r`: each is a run of `check` on `bufMem B r j` that returns `r'`, with fuel at most `2^62` and
the buffer unchanged at its end; the next call starts from `r'`. -/
def ThreadRuns (B : Array Word) : Mem → List (Word × Nat × Mem) → Prop
  | _, [] => True
  | r, (j, n, r') :: cs => n ≤ 2 ^ 62 ∧
      (∃ rs, L.run checkerProg n "check" [] (bufMem B r j) = .ok (rs, r')) ∧ BufKept B r' ∧
      ThreadRuns B r' cs

/-! ## With entry 1 -/

/-- The word arrays after a run from the loaded memory are below `2^64` words. -/
theorem run_load_size {b pb : ByteArray} {sz : TieredArray → Nat} (hs : ∀ s, sz s < 2 ^ 64) {w : Word}
    {N : Nat} {rs : List Word} {m' : Mem}
    (h : L.run checkerProg N "check" [] (loadMemM b pb sz w) = .ok (rs, m')) (a : TieredArray) :
    (m'.arr64 a).size < 2 ^ 64 := by
  have t := Triple.keep checkerProg_noSt8 (n := N) (f := "check") (vs := [])
    (s₀ := ⟨loadMemM b pb sz w, Locals.init []⟩) (Q := fun _ _ => True)
    (M.triple_of_run fun _ _ _ _ _ => trivial)
  have hk := run_post (Q := fun _ m => L.Keep (loadMemM b pb sz w) m) h (by
    apply M.triple_of_run
    intro s r s' hs' hrun
    exact (M.of_run (P := fun x => x = _) hs' hrun t).2.1)
  rw [hk.size]
  simp only [loadMemM, Mem.setG, loadMem, Mem.arr64, Array.size_replicate]
  exact hs a

/-- **A thread's calls are a chain of the pool's steps** (a call on record `k` from the region
memory `r` that returns `r'` and keeps the buffer). -/
theorem threadRuns_chain (B : Array Word) :
    ∀ (cs : List (Word × Nat × Mem)) (r : Mem), ThreadRuns B r cs →
      JobChain (fun k r r' => ∃ n rs, n ≤ 2 ^ 62 ∧
        L.run checkerProg n "check" [] (bufMem B r (UInt64.ofNat k)) = .ok (rs, r') ∧ BufKept B r')
        r (cs.map (·.1.toNat))
  | [], r, _ => .nil r
  | (j, n, r') :: cs, r, ⟨hn, ⟨rs, hrun⟩, hkept, hrest⟩ =>
    .cons ⟨n, rs, hn, by rw [UInt64.ofNat_toNat]; exact hrun, hkept⟩ (threadRuns_chain B cs r' hrest)

/-- **The threads' runs accept ⇒ the twin's pool accepts.** Entry 1 (`check` with the mode word
`1`, from the loaded memory) returning `2^63 + k`; the buffer `B`, the first `len` words of `OUT`
(`len` the header's word `1`); and threads `ths`, each a fresh region memory (`INIT = 0`, every owned
array zero at its size in entry 1's memory) with its calls (`ThreadRuns`:
each call's run of `check` on `bufMem B r j` returns, and the buffer is unchanged after it), every
claimed index below `k`, every index below `k` claimed by some thread, and each thread's claims
increasing; given `check_decl`'s program facts (`CheckerCd`). -/
theorem threads_twinAcceptsPooled (hCd : CheckerCd)
    (b pb : ByteArray) (sz : TieredArray → Nat) (hin : InputsOK b pb sz)
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N₁ "check" [] (loadMemM b pb sz 1) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (B : Array Word) (hB : B = (m₁.arr64 OUT).extract 0 ((m₁.arr64 OUT).getD 1 0).toNat)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m₁.arr64 b).size) ∧
      t.1.glob INIT = 0 ∧ ThreadRuns B t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < rs₁.headD 0 - 9223372036854775808)
    (hcov : ∀ j : Word, j < rs₁.headD 0 - 9223372036854775808 → ∃ t ∈ ths, ∃ c ∈ t.2, c.1 = j)
    (hinc : ∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·)) :
    TwinAcceptsPooled [b] := by
  have hr : rs₁.headD 0 ≠ 1 := fun e => by rw [e] at hge; simp at hge
  obtain ⟨PA, m₇, m, hF, hok, hm₁, hres⟩ := checkA_run b pb sz hin 1 (Or.inl rfl) N₁ hN₁ rs₁ m₁ h₁ hr
  have hflag : modeFlag 1 = 1 := rfl
  rw [hflag] at hok hm₁
  have hpb := hin.2.2.1
  have hJP := jobProg_of_cd hCd PA hpb hF.r7.since.pbpre
  let bs := pb.data.toList
  let p := Prog.subPB bs checkerProg
  -- the buffer and the sizes
  have hO := parCompactMem_out m 1
  rw [← hm₁] at hO
  have hlt : (m.arr64 OUT).size < 2 ^ 64 := by
    rw [← hO.size OUT]; exact run_load_size hin.2.2.2 h₁ OUT
  have hBm : B = bufOf m := by
    rw [hB, bufOf, hm₁, (parCompactMem_hdr hok).2.1]
  have hsz : PA.ds.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  have hk : (rs₁.headD 0 - 9223372036854775808).toNat = PA.ds.size := by
    have e : (9223372036854775808 : Word) + UInt64.ofNat PA.ds.size - 9223372036854775808 =
        UInt64.ofNat PA.ds.size := by rw [UInt64.add_comm, UInt64.add_sub_cancel]
    rw [hres, e, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  -- the twin's side
  let a₀ : AState := { PA.sF with caches := Caches.empty }
  let Rel : Mem → AState → Prop := fun r a =>
    ∀ j, ThrAt PA.ipins (dnOf PA.sE.store) PA.ds PA.I a₀ bs (seedMem (bufMem B r j)) a
  let Call : Nat → Mem → Mem → Prop := fun k r r' => ∃ n rs, n ≤ 2 ^ 62 ∧
    L.run checkerProg n "check" [] (bufMem B r (UInt64.ofNat k)) = .ok (rs, r') ∧ BufKept B r'
  obtain ⟨pinsP, dsP, hst, hrec, hpp, hden, hPD, hH⟩ := poolHyps_of_phaseA PA Rel Call
  obtain ⟨hA, hBp, hC, hD, hE⟩ := PA.pfx
  obtain ⟨-, -, -, -, -, hpd, _rc, _preC, -, hden0⟩ :=
    ConRon.Bridge.stages_frame (chunks := [b]) hA hBp hC hD hE
  have hFD : FrontDecls PA.ds := frontDecls_of_prefix PA.pfx
  have hLD : DeclsLpsDn (dnOf PA.sE.store) PA.ds := declsLpsDn_dnOf hpd ⟨_, hden0⟩
  have hdn : DnPers (dnOf PA.sE.store) := fun k x hk => by
    simp only [dnOf] at hk; split at hk
    · assumption
    · cases hk
  have hRS : RecStep PA.ipins (dnOf PA.sE.store) PA.ds PA.I a₀ p :=
    recCall_stepE (J := none) hJP hFD hLD hdn hpp (by omega) hden hPD hrec (fun h => absurd h (by simp))
  have hstep : ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < PA.ds.size), Rel r a → Call k r r' →
      (∃ env, FoldOK env (PA.I.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob .verified PA.ipins none PA.I k PA.ds[k] a = .ok ((), a') ∧ Rel r' a' := by
    intro k r r' a hk hR ⟨n, rs, hn, hrun, hkept⟩ hfo
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI⟩ := runThr hJP.check_jobs hRS hsz n hn a (UInt64.ofNat k)
      (by rw [hk']; exact hk) (by rw [hk']; exact hfo) _ rfl (hR _) rfl rfl hrun
    refine ⟨a', ?_, fun j => ⟨X, hJ, hPB, fun t ht => (thr_next B j hI hkept t ht).trans (hX t ht)⟩⟩
    have e : PA.ds[(UInt64.ofNat k).toNat]'(by rw [hk']; exact hk) = PA.ds[k] := by simp only [hk']
    rw [← e]; simp only [hk'] at hrj ⊢; exact hrj
  have H := hH hstep
  -- the threads
  let ths' : List (Mem × List Nat) := ths.map fun t => (t.1, t.2.map (·.1.toNat))
  have hstart : ∀ t ∈ ths', Rel t.1 PA.sF.worker := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hz, hI, -, -⟩ := hth t₀ ht₀
    intro j
    have hoff := hF.build.off
    have hw := hF.build.drv.state.wf
    have hKI := indexKeysIn_of hF.jobM.arena.base H.hI H.hpI
    have hJR := JobM.fresh (hF.jobM.trunc hoff hKI) hw hoff
    refine ⟨freshMem m, ⟨_, ⟨hJR, PExt.of_ext (Ext.refl _), rfl⟩, ?_⟩, ?_, ?_⟩
    · exact ⟨by simp [AState.worker, enableScratch_dropScratch], rfl, rfl⟩
    · rw [freshMem_arr8]
      show m.bytes L.Rom.PB = _
      rw [hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]; exact loadMem_pb b pb sz
    · rw [hBm]
      exact thr_first hok hlt t₀.1 j (fun b hb => by rw [hz b hb, hO.size]) hI
  have hchain : ∀ t ∈ ths', JobChain Call t.1 t.2 := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    exact threadRuns_chain B _ _ (hth t₀ ht₀).2.2.1
  have hinc' : ∀ t ∈ ths', t.2.Pairwise (· < ·) := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    have := hinc t₀ ht₀
    rw [List.pairwise_map] at this ⊢
    exact this.imp fun h => UInt64.lt_iff_toNat_lt.mp h
  have hrange : ∀ t ∈ ths', ∀ k ∈ t.2, k < PA.ds.size := by
    intro t ht k hk'
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk'
    have := (hth t₀ ht₀).2.2.2 c hc
    rw [UInt64.lt_iff_toNat_lt, hk] at this
    exact this
  have hcov' : ∀ k < PA.ds.size, ∃ t ∈ ths', k ∈ t.2 := by
    intro k hk'
    have hk64 : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨t, ht, c, hc, hcj⟩ := hcov (UInt64.ofNat k) (by rw [UInt64.lt_iff_toNat_lt, hk, hk64]; exact hk')
    exact ⟨_, List.mem_map_of_mem ht, List.mem_map.mpr ⟨c, hc, by rw [hcj, hk64]⟩⟩
  obtain ⟨-, hacc⟩ := pool_twin H hst ths' hstart hchain hinc' hrange hcov'
  exact ⟨PA.pins, PA.sA, PA.sB, PA.sC, PA.sD, PA.sE, PA.sF, PA.pre, PA.rc, PA.ds, PA.ipins, PA.I,
    hA, hBp, hC, hD, hE, ths'.map (·.2), PA.idx,
    fun k hk' => by obtain ⟨t, ht, hkt⟩ := hcov' k hk'; exact ⟨t.2, List.mem_map_of_mem ht, hkt⟩,
    fun w hw k hkw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hrange t ht k hkw,
    fun w hw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hinc' t ht,
    fun w hw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hacc t ht⟩

end L.Checker
