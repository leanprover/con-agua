module

public import ConAgua.Checker.ParThreadCall
public import ConAgua.Final.TwinPooled
import ConAgua.Checker.CheckARun
import ConAgua.Checker.IndArm
import ConAgua.Checker.LoopProg
import ConAgua.Checker.LoopStage
import ConAgua.Checker.RomProg0
import ConAgua.Checker.TwinShapeQuot
public import ConAgua.Checker.PresizeStage

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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- The group list a thread's calls check. -/
def thrGroups (pend : Array PendingCheck) (cs : List (Word × Nat × Mem)) : List PendingCheck :=
  cs.map fun c => pdAt pend c.1
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
-/

/- ronsync2 stage 2: commented out (a section at a removed L function)
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
array zero at its size in `m`). -/
theorem thread_accepts (hP : PhaseBProg (Prog.subPB bs checkerProg)) (hm : mode = .verified)
    {m : Mem} {a : AState} {v : Word} (hS : PhaseBStart pins dn ds fe pend m a v)
    (hPB : m.arr8 PB = bs.toArray) (hok : parCompactOK m 1 = true)
    (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (r₀ : Mem)
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
    obtain ⟨hok', hR', hI'⟩ := thrCall_first mode pins dn ds fe pend bs hP hm hS hPB hok hlt r₀ hz
      hI j hj' (by omega) n hn hrun
    simp only [thrGroups, List.map_cons]
    rw [checkPendingList_cons_ok hok']
    exact thread_chain mode pins dn ds fe pend bs hP hm hpend (bufImg_hdr hok hlt) cs r' _ hR' hI' hk'
      hrest (fun c hc => hj c (List.mem_cons_of_mem _ hc))

/-- What a thread's harness supplies: a fresh region memory and the calls on it. -/
def ThreadOK (m : Mem) (B : Array Word) (pend : Array PendingCheck)
    (t : Mem × List (Word × Nat × Mem)) : Prop :=
  (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m.arr64 b).size) ∧
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
    have hj := (hth t ht).2.2.2 c hc
    simp only [pdAt, Array.getD, hj, dite_true]
    exact Array.getElem_mem_toList _
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
    obtain ⟨hz, hI, hruns, hj⟩ := hth t ht
    exact thread_accepts mode pins dn ds fe pend bs hP hm hS hPB hok hlt t.1 hz hI t.2 hruns hj

end chain
-/

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

/-- **The threads' runs accept ⇒ the twin's pool accepts.** Entry 1 (`check` with the mode word
`1`, from the loaded memory) returning `2^63 + k`; the buffer `B`, the first `len` words of `OUT`
(`len` the header's word `1`); and threads `ths`, each a fresh region memory (`INIT = 0`, every owned
array zero at its size in entry 1's memory) with its calls (`ThreadRuns`:
each call's run of `check` on `bufMem B r j` returns, and the buffer is unchanged after it), every
claimed index below `k`, and every index below `k` claimed by some thread. -/
theorem threads_twinAcceptsPooled (b pb : ByteArray) (sz : TieredArray → Nat) (hin : InputsOK b pb sz)
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N₁ "check" [] (loadMemM b pb sz 1) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (B : Array Word) (hB : B = (m₁.arr64 OUT).extract 0 ((m₁.arr64 OUT).getD 1 0).toNat)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m₁.arr64 b).size) ∧
      t.1.glob INIT = 0 ∧ ThreadRuns B t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < rs₁.headD 0 - 9223372036854775808)
    (hcov : ∀ j : Word, j < rs₁.headD 0 - 9223372036854775808 → ∃ t ∈ ths, ∃ c ∈ t.2, c.1 = j) :
    TwinAcceptsPooled [b] := by
  sorry

end L.Checker
