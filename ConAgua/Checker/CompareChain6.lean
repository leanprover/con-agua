module

public import ConAgua.Checker.CompareChain5
public import ConAgua.Arena.JustifySideRefMove
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.LoopProgTac
import all ConAgua.Checker.Entry
import all ConAgua.Checker.CompareEntry
import all ConAgua.Arena.FreezeCmp
import all ConAgua.Checker.CmpSeqEntry
import ConRon.Bridge.Checker.Install
import ConAgua.Arena.IWFrame

@[expose] public section

/-!
# The compared run at the L level, mode `6` (lane compare)

`check` with the mode word `6` runs `check_c3()` (`Checker/CompareEntry.lean`) from mode `5`'s
memory with the frozen buffer's array `OUT` as the solution's jobs left it (`OutEq`: every other
array, the sizes and the bytes as after the solution's index build). Here, step by step:

* the move (`index_to_solution`, `indexToSolution_ref`): the solution's index in its rows
  (`SolIdxR`), the stream index empty.
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend

/-! ## Mode `6`'s start -/

/-- **A memory that agrees with `m` but in `OUT`** (the frozen buffer, which the solution's jobs
may have changed), with the same sizes and bytes. -/
structure OutEq (m m' : Mem) : Prop where
  arr : ∀ a : TieredArray, a ≠ OUT → m'.arr64 a = m.arr64 a
  size : ∀ a : TieredArray, (m'.arr64 a).size = (m.arr64 a).size
  bytes : m'.bytes = m.bytes

theorem OutEq.memFrame {m m' : Mem} (h : OutEq m m') : MemFrame [OUT] [] m m' :=
  ⟨fun b hb _ => h.arr b (fun e => hb (by simp [e])),
   fun x _ => by rw [h.arr CTL (by decide)], h.size⟩

theorem OutEq.of_out {m m' : Mem} (h : OutFrame m m') : OutEq m m' := ⟨h.arr, h.size, h.bytes⟩

theorem OutEq.setG {m m' : Mem} (h : OutEq m m') (g : GVar) (w : Word) : OutEq m (m'.setG g w) :=
  ⟨fun a ha => h.arr a ha, fun a => h.size a, h.bytes⟩

/-! ## The solution's twin facts after its index build -/

/-- **The twin's facts after the solution's index build** (`buildIndex_run`): the driver
invariant, the store extended, the pins kept, the scratch tier closed, the index denoting and
persistent. -/
theorem PhaseS.built {bC bS : ByteArray} (PS : PhaseS bC bS) :
    ConRon.Bridge.DriverOK PS.sF ∧ Ext PS.sE.store PS.sF.store ∧ PS.sF.pins = PS.sE.pins ∧
      PS.sF.store.scratchOn = false ∧
      (∃ J, ConRon.Bridge.IndexDenotes PS.sF.store PS.IS J) ∧ ConRon.Bridge.PersIFBase PS.IS.base := by
  have ho := StagesOut.cmp PS.pfx PS.pinsR
  obtain ⟨_, hden⟩ := ho.den
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ConRon.Bridge.buildIndex_run ConRon.Bridge.constsSpec
    ConRon.Bridge.tablesSpec ho.drv ho.pp ho.off ho.pd hden PS.idx
  exact ⟨h1, h2, h3, h4, ⟨_, h5⟩, h6⟩

/-! ## The move -/

/-- The compared run's arrays (`210‥222`) are zero at mode `6`'s start: no stage before writes
them (`preLoopA`, `biA`). -/
theorem cmp_zero6 {b pb : ByteArray} {sz : TieredArray → Nat} {ds : Array IDeclaration}
    {ipins : List INatOpPinSet} {sE : AState} {I : IStreamIndex} {sF : AState} {m₇ m m0 : Mem}
    (hF : FoldOn b pb sz ds ipins sE I sF m₇ m) (hO : OutEq m m0) {t : TieredArray}
    (ht : 210 ≤ t.arr ∧ t.arr ≤ 222) : m0.arr64 t = Array.replicate (sz t) 0 := by
  have hc : t ≠ CTL := fun e => by subst e; simp [CTL] at ht
  have hpl : t ∉ preLoopA := fun hm => by
    have : (preLoopA.filter (fun b => 210 ≤ b.arr && b.arr ≤ 222)) = [] := by decide +kernel
    have := List.filter_eq_nil_iff.mp this t hm
    simp [ht.1, ht.2] at this
  have hbi : t ∉ biA := fun hm => by
    simp only [biA, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hm
    have := hm.2.2; simp [ht.1, ht.2] at this
  have hout : t ≠ OUT := fun e => by subst e; simp [OUT] at ht
  rw [hO.arr t hout, hF.frame.arr t hbi hc, hF.r7.since.frame.arr t hpl hc, loadMem_arr]

theorem rdN_replicate (n k : Nat) : rdN (Array.replicate n (0 : Word)) k = 0 := by
  simp only [rdN, Array.getElem?_replicate]; split <;> rfl

theorem _root_.L.Arena.IndexR.outEq {m m' : Mem} {I : IStreamIndex} (h : IndexR m I) (hO : OutEq m m') : IndexR m' I :=
  h.grow (fun b _ hb => hO.arr b (fun e => by subst e; simp [OUT] at hb))
    (by rw [hO.arr CTL (by decide)]) (by
      have : erecP m' = erecP m := by
        funext i; simp only [erecP, erTop, erecTop1, hO.arr EREC (by decide),
          hO.arr (tier1 EREC) (by decide), hO.arr CTL (by decide)]
        rfl
      rw [this]; exact ArrExt.refl _)

/-- **The move at mode `6`'s start**: after the solution's index build (`FoldOn`) and the
solution's jobs (`OutEq`), with the row arrays' sizes equal (`hsz6`, the table's), a returning
`index_to_solution(|dsS|)` leaves the solution's index in its rows, the stream index empty, and
writes only the rows and `CTL[225]`, `CTL[226]`, `CTL[128]`. -/
theorem move_step {bC bS pb : ByteArray} {sz : TieredArray → Nat} (PS : PhaseS bC bS) {m₇ m m0 : Mem}
    (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) (hO : OutEq m m0)
    (hsz6 : ∀ g ≤ 2, sz (sixArr g) = sz (eixArr g) ∧ sz (stxArr g) = sz (tixArr g))
    {n : Nat} {cnt : Word} {r : List Word} {m1 : Mem}
    (hc : callW checkerProg n "index_to_solution" [cnt] m0 = some (r, m1))
    (hcnt : cnt.toNat = PS.dsS.size) :
    SolIdxR m1 PS.IS ∧ IndexR m1 {} ∧ MemFrame moveA moveC m0 m1 := by
  obtain ⟨-, -, -, -, ⟨J, hJ⟩, hpI⟩ := PS.built
  have hI := hF.build.idx.outEq hO
  have hA : ArenaR m0 PS.sF := ArenaR.frame_ext [OUT] [] (fun b hb => by
      simp only [List.mem_singleton] at hb; subst hb; decide) (fun _ h => by simp at h) m m0
    hO.memFrame PS.sF hF.build.stage.check.arena.base
  have hK := indexKeysIn_of hA hJ hpI
  have hS7 := hF.r7.since
  have hsize : ∀ t, (m0.arr64 t).size = sz t := fun t => by
    rw [hO.size, hF.frame.size, hS7.frame.size, loadMem_arr, Array.size_replicate]
  refine indexToSolution_ref (by chk_lk) (by chk_lk) (by chk_lk) (by chk_lk) hc hI hK
    (by rw [hF.fsize, hcnt]) (fun g hg j => ?_) (fun g hg => ?_) ?_
  · have h6 : 210 ≤ (sixArr g : TieredArray).arr ∧ (sixArr g : TieredArray).arr ≤ 222 := by
      unfold sixArr; split <;> (try split) <;> decide
    have h7 : 210 ≤ (stxArr g : TieredArray).arr ∧ (stxArr g : TieredArray).arr ≤ 222 := by
      unfold stxArr; split <;> (try split) <;> decide
    rw [cmp_zero6 hF hO h6, cmp_zero6 hF hO h7]
    exact ⟨rdN_replicate _ _, rdN_replicate _ _⟩
  · rw [hsize, hsize, hsize, hsize]; exact hsz6 g hg
  · have := hS7.caps.2.1; rw [hsize]; rw [loadMem_arr, Array.size_replicate] at this
    simp only [ctlMin] at this; omega

/-! ## The challenge's records back -/

theorem restoreM_dlp (m : Mem) : (restoreM m).arr64 DLP = m.arr64 DLP :=
  arr64_copy64_ne _ _ _ _ _ _ (by decide)

theorem restoreM_frame (m : Mem) : MemFrame [DECL] [] m (restoreM m) :=
  (memFrame_copy64 m DECL (by decide) 0 CDECL 0 _).mono (by simp) (by simp)

/-- **`cmp_restore` gives the challenge's records back** (`stash_of` the other way): `DECL` holds
what `CDECL` held, over the same pool. -/
theorem restore_of {m : Mem} {ds : Array IDeclaration} (hD : DeclsF (m.arr64 CDECL) (m.arr64 DLP) ds)
    (hR : ∀ x < ds.size, RecOK (m.arr64 CDECL) (m.arr64 DLP) x) (hok : RestoreOK m)
    (hds : (m.arr64 DECL).size < 2 ^ 63) :
    DeclsF ((restoreM m).arr64 DECL) ((restoreM m).arr64 DLP) ds ∧
      ∀ x < ds.size, RecOK ((restoreM m).arr64 DECL) ((restoreM m).arr64 DLP) x := by
  have hc' : (rdW (m.arr64 CDECL) 0).toNat = ds.size := hD.count
  have h59 := hok.1
  rw [hc'] at h59
  have hn : (restoreN m).toNat = 1 + 8 * ds.size := by
    simp only [restoreN]
    rw [UInt64.toNat_add, UInt64.toNat_mul, hc']
    simp only [UInt64.toNat_one, UInt64.reduceToNat]
    omega
  have hcp : ∀ j, j < 1 + 8 * ds.size →
      ((restoreM m).arr64 DECL)[j]? = (m.arr64 CDECL)[j]? := fun j hj =>
    get?_copy64 (by decide) m _ (by rw [hn]; omega) hok.2.1 hok.2.2 j (by rw [hn]; exact hj)
  have hsz : ((restoreM m).arr64 DECL).size = (m.arr64 DECL).size := size_copy64 _ _ _ _ _ _ _
  rw [restoreM_dlp]
  refine ⟨hD.congr (by rw [hsz]; exact hds) (by rw [hsz, ← hn]; exact hok.2.1) rfl hcp
    (fun _ _ _ => rfl) (Nat.le_refl _) hD.ptop, fun x hx => recOK_congr_rows (hR x hx) fun j _ hj => hcp j (by omega)⟩

end L.Checker
