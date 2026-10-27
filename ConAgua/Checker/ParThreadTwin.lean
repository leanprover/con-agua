import ConAgua.Checker.ParThreadCall
import ConAgua.Final.TwinPooled

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

open L L.Arena L.Rom

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

/-- The group list a thread's calls check. -/
def thrGroups (pend : Array PendingCheck) (cs : List (Word × Nat × Mem)) : List PendingCheck :=
  cs.map fun c => pdAt pend c.1

theorem checkPendingList_cons_ok {mode : ConLeche.CheckMode} {fe : IFEnv} {pc : PendingCheck}
    {rest : List PendingCheck} {a : AState} (h : AM.ok (checkPending mode fe pc) a) :
    checkPendingList mode fe (pc :: rest) a =
      checkPendingList mode fe rest (AM.st (checkPending mode fe pc) a) := by
  simp only [AM.ok, AM.st, StateT.run] at h ⊢
  simp only [checkPendingList]
  split at h
  · rename_i x hx
    obtain ⟨u, a'⟩ := x
    simp only [hx]
  · exact h.elim

section chain
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (fe : IFEnv) (pend : Array PendingCheck) (bs : List UInt8)

/-- **A thread's later calls** accept their groups in order, from a memory `ThreadRel` to `a` with
`INIT = 1` and the buffer unchanged. -/
theorem thread_chain (hP : PhaseBProg (Prog.subPB bs checkerProg)) (hm : mode = .verified)
    (hpend : pend.size ≤ 2 ^ 62) {B : Array Word} {v : Word} (hB : (bufImg B 0).getD 3 0 = v) :
    ∀ (cs : List (Word × Nat × Mem)) (r : Mem) (a : AState),
      ThreadRel pins dn ds fe pend bs v r a → r.glob INIT = 1 → BufKept B r → ThreadRuns B r cs →
      (∀ c ∈ cs, c.1.toNat < pend.size) →
      ∃ s'', checkPendingList mode fe (thrGroups pend cs) a = .ok (.ok (), s'')
  | [], _, a, _, _, _, _, _ => ⟨a, rfl⟩
  | (j, n, r') :: cs, r, a, hR, hI, hk, hruns, hj => by
    obtain ⟨hn, ⟨rs, hrun⟩, hk', hrest⟩ := hruns
    have hj' : j.toNat < pend.size := hj _ List.mem_cons_self
    obtain ⟨hok, hR', hI'⟩ := thrCall_next mode pins dn ds fe pend bs hP hm hB hR hI hk j hj'
      (by omega) n hn hrun
    simp only [thrGroups, List.map_cons]
    rw [checkPendingList_cons_ok hok]
    exact thread_chain hP hm hpend hB cs r' _ hR' hI' hk' hrest
      (fun c hc => hj c (List.mem_cons_of_mem _ hc))

/-- **A thread's calls accept their groups**, in order, from phase A's worker state: entry 1's
`PhaseBStart m a v`, the buffer `bufOf m v`, a fresh region memory `r₀` (`INIT = 0`, every owned
array zero at its size in `m`, at least `388` arrays (`checkerTab.nw`)). -/
theorem thread_accepts (hP : PhaseBProg (Prog.subPB bs checkerProg)) (hm : mode = .verified)
    {m : Mem} {a : AState} {v : Word} (hS : PhaseBStart pins dn ds fe pend m a v)
    (hPB : m.arr8 PB = bs.toArray) (hok : parCompactOK m 1 = true)
    (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (r₀ : Mem) (hr : 388 ≤ r₀.words.size)
    (hz : ∀ b ∈ parOwnedL, r₀.arr64 b = zeros (m.arr64 b).size) (hI : r₀.glob INIT = 0)
    (cs : List (Word × Nat × Mem)) (hruns : ThreadRuns (bufOf m v) r₀ cs)
    (hj : ∀ c ∈ cs, c.1.toNat < pend.size) :
    ∃ s'', checkPendingList mode fe (thrGroups pend cs) a.worker = .ok (.ok (), s'') := by
  have hpend : pend.size ≤ 2 ^ 62 := by
    have := hS.loop.pend.bound; rw [hS.loop.pend.count] at this; exact this
  match cs, hruns, hj with
  | [], _, _ => exact ⟨a.worker, rfl⟩
  | (j, n, r') :: cs, ⟨hn, ⟨rs, hrun⟩, hk', hrest⟩, hj =>
    have hj' : j.toNat < pend.size := hj _ List.mem_cons_self
    obtain ⟨hok', hR', hI'⟩ := thrCall_first mode pins dn ds fe pend bs hP hm hS hPB hok hlt r₀ hr hz
      hI j hj' (by omega) n hn hrun
    simp only [thrGroups, List.map_cons]
    rw [checkPendingList_cons_ok hok']
    exact thread_chain mode pins dn ds fe pend bs hP hm hpend (bufImg_hdr hok hlt) cs r' _ hR' hI' hk'
      hrest (fun c hc => hj c (List.mem_cons_of_mem _ hc))

/-- What a thread's harness supplies: a fresh region memory and the calls on it. -/
def ThreadOK (m : Mem) (B : Array Word) (pend : Array PendingCheck)
    (t : Mem × List (Word × Nat × Mem)) : Prop :=
  388 ≤ t.1.words.size ∧ (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m.arr64 b).size) ∧
    t.1.glob INIT = 0 ∧ ThreadRuns B t.1 t.2 ∧ ∀ c ∈ t.2, c.1.toNat < pend.size

/-- **The threads give con-ron's pool**: threads whose calls together claim every group index
below `|pend|` give a family of group lists covering `pend`, drawn from it, each accepted by
`checkPendingList` from phase A's worker state. -/
theorem threads_pool (hP : PhaseBProg (Prog.subPB bs checkerProg)) (hm : mode = .verified)
    {m : Mem} {a : AState} {v : Word} (hS : PhaseBStart pins dn ds fe pend m a v)
    (hPB : m.arr8 PB = bs.toArray) (hok : parCompactOK m 1 = true)
    (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (ths : List (Mem × List (Word × Nat × Mem))) (hth : ∀ t ∈ ths, ThreadOK m (bufOf m v) pend t)
    (hcov : ∀ i < pend.size, ∃ t ∈ ths, ∃ c ∈ t.2, c.1.toNat = i) :
    (∀ pc ∈ pend.toList, ∃ w ∈ ths.map (thrGroups pend ·.2), pc ∈ w) ∧
    (∀ w ∈ ths.map (thrGroups pend ·.2), ∀ pc ∈ w, pc ∈ pend.toList) ∧
    (∀ w ∈ ths.map (thrGroups pend ·.2),
      ∃ s'', checkPendingList mode fe w a.worker = .ok (.ok (), s'')) := by
  refine ⟨fun pc hpc => ?_, fun w hw pc hpc => ?_, fun w hw => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hpc
    rw [Array.length_toList] at hi
    obtain ⟨t, ht, c, hc, hci⟩ := hcov i hi
    refine ⟨thrGroups pend t.2, List.mem_map_of_mem ht, ?_⟩
    have : pdAt pend c.1 = pend.toList[i] := by
      simp [pdAt, hci, Array.getD, hi]
    rw [← this]
    exact List.mem_map_of_mem hc
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hpc
    have hj := (hth t ht).2.2.2.2 c hc
    simp only [pdAt, Array.getD, hj, dite_true]
    exact Array.getElem_mem_toList _
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
    obtain ⟨hr, hz, hI, hruns, hj⟩ := hth t ht
    exact thread_accepts mode pins dn ds fe pend bs hP hm hS hPB hok hlt t.1 hr hz hI t.2 hruns hj

end chain

/-! ## With entry 1 -/

/-- The word arrays after a run from the loaded memory are below `2^64` words. -/
theorem run_load_size {b pb : ByteArray} {s8 s64 : List Nat} (hs : ∀ n ∈ s64, n < 2 ^ 64) {w : Word}
    {N : Nat} {rs : List Word} {m' : Mem}
    (h : L.run checkerProg N "check" [] (loadMemM b pb s8 s64 w) = .ok (rs, m')) (a : ArrId) :
    (m'.arr64 a).size < 2 ^ 64 := by
  have t := Triple.keep checkerProg_noSt8 (n := N) (f := "check") (vs := [])
    (s₀ := ⟨loadMemM b pb s8 s64 w, Locals.init []⟩) (Q := fun _ _ => True)
    (M.triple_of_run fun _ _ _ _ _ => trivial)
  have hk := run_post (Q := fun _ m => L.Keep (loadMemM b pb s8 s64 w) m) h (by
    apply M.triple_of_run
    intro s r s' hs' hrun
    exact (M.of_run (P := fun x => x = _) hs' hrun t).2.1)
  rw [hk.size]
  simp only [loadMemM, Mem.setG, loadMem, Mem.arr64, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map]
  cases e : s64[a]? with
  | none => simp
  | some n => simpa using hs n (List.mem_of_getElem? e)

/-- **The threads' runs accept ⇒ the twin's pool accepts.** Entry 1 (`check` with the mode word
`1`, from the loaded memory) returning `2^63 + k`; the buffer `B`, the first `len` words of `OUT`
(`len` the header's word `1`); and threads `ths`, each a fresh region memory (`INIT = 0`, every owned
array zero at its size in entry 1's memory, at least `388` arrays (`checkerTab.nw`)) with its calls (`ThreadRuns`:
each call's run of `check` on `bufMem B r j` returns, and the buffer is unchanged after it), every
claimed index below `k`, and every index below `k` claimed by some thread. -/
theorem threads_twinAcceptsPooled (b pb : ByteArray) (s8 s64 : List Nat) (hin : InputsOK b pb s64)
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N₁ "check" [] (loadMemM b pb s8 s64 1) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (B : Array Word) (hB : B = (m₁.arr64 OUT).extract 0 ((m₁.arr64 OUT).getD 1 0).toNat)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, 388 ≤ t.1.words.size ∧ (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m₁.arr64 b).size) ∧
      t.1.glob INIT = 0 ∧ ThreadRuns B t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < rs₁.headD 0 - 9223372036854775808)
    (hcov : ∀ j : Word, j < rs₁.headD 0 - 9223372036854775808 → ∃ t ∈ ths, ∃ c ∈ t.2, c.1 = j) :
    TwinAcceptsPooled [b] := by
  have hr : rs₁.headD 0 ≠ 1 := fun e => by rw [e] at hge; simp at hge
  obtain ⟨PA, m, v, hS, hPB, hpre, hok, hm₁, hres⟩ :=
    checkA_run b pb s8 s64 hin 1 (Or.inl rfl) N₁ hN₁ rs₁ m₁ h₁ hr
  have hflag : modeFlag 1 = 1 := rfl
  rw [hflag] at hok hm₁
  -- the twin's facts behind the program bundle (as `drv_twinAccepts`)
  have hrom : RomOK pb.data.toList := by simpa [RomOK] using hin.2.2.1
  have hT := twinFold_of_prefix PA.pfx
  have hdn : L.Ind.DnInj (dnOf PA.sE.store) := dnOf_inj hT.stateOK.wf
  have hQd : QuotDn (dnOf PA.sE.store) := by
    obtain ⟨k, hk, hd⟩ := prefix_quotU PA.pfx
    exact ⟨k, by simp [dnOf, hk, hd]⟩
  have hLC := checkerProg_loopCalleesPB pb.data.toList hrom hpre (dnOf PA.sE.store) hdn
    (indArmSpec_checker _ hrom hpre _ hdn) hQd
  have hTop := checkerProg_loopTopPB pb.data.toList
  have hPB' : PhaseBProg (Prog.subPB pb.data.toList checkerProg) :=
    ⟨hTop.bracket, hLC.cvg, hLC.knot, hLC.leaf, hLC.loop, hTop.pc, hTop.pcg, hTop.pcx,
      hLC.cd.crp.apd, ⟨hLC.indMemo, hLC.crf⟩⟩
  -- the buffer and the sizes
  have hF := parCompactMem_out m v 1
  rw [← hm₁] at hF
  have hlt : (m.arr64 OUT).size < 2 ^ 64 := by
    rw [← hF.size OUT]; exact run_load_size hin.2.2.2 h₁ OUT
  have hBm : B = bufOf m v := by
    rw [hB, bufOf, hm₁, (parCompactMem_hdr hok).2.1]
  -- the number of groups
  have hk : (rs₁.headD 0 - 9223372036854775808).toNat = PA.pend.size := by
    have hc := hS.loop.pend.count
    have hlt' : PA.pend.size < 2 ^ 64 := by rw [← hc]; exact UInt64.toNat_lt_size _
    have e : (9223372036854775808 : Word) + UInt64.ofNat PA.pend.size - 9223372036854775808 =
        UInt64.ofNat PA.pend.size := by rw [UInt64.add_comm, UInt64.add_sub_cancel]
    rw [hres, e, UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hlt')]
  have hth' : ∀ t ∈ ths, ThreadOK m (bufOf m v) PA.pend t := by
    intro t ht
    obtain ⟨h1, h2, h3, h4, h5⟩ := hth t ht
    refine ⟨h1, fun b hb => ?_, h3, hBm ▸ h4, fun c hc => ?_⟩
    · rw [h2 b hb, hF.size]
    · have := h5 c hc
      rw [UInt64.lt_iff_toNat_lt, hk] at this
      exact this
  have hcov' : ∀ i < PA.pend.size, ∃ t ∈ ths, ∃ c ∈ t.2, c.1.toNat = i := by
    intro i hi
    have hi64 : i < 2 ^ 64 := by
      have := hS.loop.pend.bound; rw [hS.loop.pend.count] at this; omega
    obtain ⟨t, ht, c, hc, hcj⟩ := hcov (UInt64.ofNat i) (by
      rw [UInt64.lt_iff_toNat_lt, hk, UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hi64)]
      exact hi)
    exact ⟨t, ht, c, hc, by rw [hcj, UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hi64)]⟩
  obtain ⟨hcv, hsub, hacc⟩ := threads_pool .verified PA.ipins (dnOf PA.sE.store) PA.ds PA.fe PA.pend
    pb.data.toList hPB' rfl hS hPB hok hlt ths hth' hcov'
  obtain ⟨hA, hBp, hC, hD, hE⟩ := PA.pfx
  exact ⟨PA.pins, PA.sA, PA.sB, PA.sC, PA.sD, PA.sE, PA.sF, PA.pre, PA.rc, PA.ds, PA.ipins, PA.fe,
    hA, hBp, hC, hD, hE, PA.k, PA.pend, _, PA.fold, hcv, hsub, hacc⟩

end L.Checker
