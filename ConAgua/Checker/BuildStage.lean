module

public import ConAgua.Checker.LoopStage
public import ConAgua.Arena.IndexBuild
import ConAgua.Checker.TwinShapeQuot
import ConAgua.Checker.TwinCaches
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.PreLoopWSBase
import ConRon.Bridge.Checker.Pool
import ConRon.Bridge.Stages
public import ConAgua.Checker.BuildClosed
public import ConAgua.Checker.PipeFinal
public meta import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.LoopProgTac
import all ConAgua.Arena.CheckerL

@[expose] public section

/-!
# The stream index build's start (stage 3 of lane ronsync2)

`buildR_of_R7`: after the stages up to `intern_all_pins` (`R7`, and the twin's stages
`TwinPrefix`), the memory is `BuildR` at the empty stream index, the stage relation at its view
`0` (`bEnv {} 0 0`): the index rows, the own layer, the stamp, the index's control words and the
inductive memos are the loaded memory's zeros, which no stage before the index build writes
(`Since.frame`: `preLoopA`, `preLoopC`).
-/

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena L.Rom

/-- The arrays the index build's start needs zero: the stream index's rows, the own layer (both
tiers), the inductive memos (`IndMemos.zero`). -/
def buildZeroArrs : List TieredArray :=
  tier0s [EIXA, EIXS, EIXN, TIXA, TIXS, TIXN, OIXA, OIXS, OIXN, OTXA, OTXS, OTXN, 51, 155,
    201, 202, 203, 204, 205, 206, 207, 208] ++
  tier1s [OIXA, OIXS, OIXN, OTXA, OTXS, OTXN]

/-- The `CTL` words the index build's start needs zero: the index's counter, the stamp, the
view's bounds, the inductive memos' words. -/
def buildZeroCtls : List Nat :=
  [128, 133, 134, 135, 52, 158, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214,
    215, 216, 217, 218, 219]

theorem preLoopA_buildZero : buildZeroArrs.all (fun b => !preLoopA.contains b) = true := by
  decide +kernel

theorem preLoopC_buildZero :
    (preLoopC.map UInt64.toNat).all (fun x => !buildZeroCtls.contains x) = true := by
  decide +kernel

section since
variable {b pb : ByteArray} {sz : TieredArray → Nat} {m : Mem}
  (h : Since (ConAgua.Final.loadMem b pb sz) m pb)
include h

theorem since_zeroA {t : TieredArray} (ht : t ∈ buildZeroArrs) :
    m.arr64 t = Array.replicate (sz t) 0 := by
  have hn : t ∉ preLoopA := fun hm => by
    have := List.all_eq_true.mp preLoopA_buildZero t ht
    simp [List.contains_iff_mem, hm] at this
  have hc : t ≠ CTL := by rintro rfl; revert ht; decide
  rw [h.frame.arr t hn hc, loadMem_arr]

theorem since_rdN {t : TieredArray} (ht : t ∈ buildZeroArrs) (k : Nat) : rdN (m.arr64 t) k = 0 := by
  rw [since_zeroA h ht]; simp only [rdN, Array.getElem?_replicate]; split <;> rfl

theorem since_rdW {t : TieredArray} (ht : t ∈ buildZeroArrs) (k : Word) : rdW (m.arr64 t) k = 0 := by
  rw [since_zeroA h ht]; simp only [rdW, Array.getElem?_replicate]; split <;> rfl

theorem since_ctl {x : Word} (hx : x.toNat ∈ buildZeroCtls) : rdW (m.arr64 CTL) x = 0 := by
  have hn : x ∉ preLoopC := fun hm => by
    have := List.all_eq_true.mp preLoopC_buildZero x.toNat (List.mem_map.mpr ⟨x, hm, rfl⟩)
    simp [List.contains_iff_mem, hx] at this
  rw [h.frame.ctl x hn, loadMem_rd]

end since

theorem tierA_oix_zero (g : Nat) (t : UInt64) : tierA (oixArr g) t ∈ buildZeroArrs := by
  unfold tierA oixArr; generalize (t &&& 1 != 0) = b
  cases b <;> split <;> (try split) <;> decide

theorem tierA_otx_zero (g : Nat) (t : UInt64) : tierA (otxArr g) t ∈ buildZeroArrs := by
  unfold tierA otxArr; generalize (t &&& 1 != 0) = b
  cases b <;> split <;> (try split) <;> decide

theorem eix_zero (g : Nat) : ((eixArr g : ArrId) : TieredArray) ∈ buildZeroArrs := by
  unfold eixArr; split <;> (try split) <;> decide

theorem tix_zero (g : Nat) : ((tixArr g : ArrId) : TieredArray) ∈ buildZeroArrs := by
  unfold tixArr; split <;> (try split) <;> decide

theorem ind_zero_arr : ∀ i : Fin 8, ((201 + i.val : ArrId) : TieredArray) ∈ buildZeroArrs := by
  decide

section zero
variable {b pb : ByteArray} {sz : TieredArray → Nat} {m : Mem}
  (h : Since (ConAgua.Final.loadMem b pb sz) m pb)
include h

theorem since_stamp : stampW m = 0 := since_ctl h (by decide)

theorem since_ownRow (w : Word) : ownRow m w = (0, 0) := by
  simp only [ownRow, since_rdN h (tierA_oix_zero _ _)]

theorem since_ownEmpty : OwnEmpty m := by
  intro w
  refine ⟨?_, ?_⟩
  · simp only [ownRaw, since_ownRow h]; split <;> rfl
  · simp only [ownTbl, since_rdN h (tierA_otx_zero _ _)]; split <;> rfl

theorem since_ownBelow : OwnBelow m := by
  intro w _
  simp only [since_ownRow h, since_rdN h (tierA_otx_zero _ _), since_stamp h]
  decide

theorem since_baseRow (w : Word) : (baseRow m w).1 = 0 := by
  simp only [baseRow]; split
  · exact since_rdN h (eix_zero _) _
  · rfl

theorem since_baseTbl (w : Word) : (baseTbl m w).1 = 0 := by
  simp only [baseTbl]; split
  · exact since_rdN h (tix_zero _) _
  · rfl

theorem since_indexR : IndexR m {} := by
  refine ⟨fun n => ?_, fun n => ?_, fun i hi => absurd hi (by simp), by simp, ?_⟩
  · rw [if_pos (since_baseRow h _)]; simp
  · rw [if_pos (since_baseTbl h _)]; simp
  · rw [since_ctl h (x := 128) (by decide)]; rfl

theorem since_envR : EnvR m 0 (bEnv ({} : IStreamIndex).base 0 0) :=
  EnvR.ofIndex (k := 0) (since_indexR h) (since_ownEmpty h) (since_ownBelow h)
    (by rw [since_stamp h]; decide) (by rw [since_ctl h (x := 134) (by decide)]; rfl)
    (by rw [since_ctl h (x := 135) (by decide)]; rfl)

theorem since_indMemos (hctl : 220 ≤ (m.arr64 CTL).size) : IndMemos m :=
  IndMemos.zero hctl
    (fun b hb j => since_rdW h (t := (b : TieredArray)) (by
      rcases hb with rfl | rfl | ⟨h1, h2⟩
      · decide
      · decide
      · have h1' : @LE.le Nat _ 201 b := h1
        have h2' : @LE.le Nat _ b 208 := h2
        have e : @Eq Nat (201 + (b - 201)) b := by omega
        have := ind_zero_arr ⟨b - 201, by omega⟩
        simp only [e] at this
        exact this) j)
    (fun x hx => since_ctl h (by simp only [buildZeroCtls, List.mem_cons]; omega))

end zero

/-- **The index build's start**: after the stages up to `intern_all_pins`, the memory is
`BuildR` at the empty stream index, at the twin's state after the stages. -/
theorem buildR_of_R7 {b pb : ByteArray} {sz : TieredArray → Nat} (hsz : ∀ s, sz s < 2 ^ 64)
    {sA : AState} {pre : PreludeIx} {sB : AState} {rc : ParseResultD} {sC : AState}
    {ds : Array IDeclaration} {sD : AState} {pins : List ConLeche.NatOpPinSet}
    {ipins : List INatOpPinSet} {sE : AState} {m : Mem}
    (hpx : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE)
    (h7 : R7 (ConAgua.Final.loadMem b pb sz) m pb ds ipins sE) :
    BuildR (dnOf sE.store) ds 0 0 m sE {} := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := hpx
  obtain ⟨hoff, hdrv, -, -, -, hpd, _rc, _preC, -, hden⟩ := ConRon.Bridge.stages_frame (chunks := [b]) hA hB hC hD hE
  have hS := h7.since
  have hctl : 220 ≤ (m.arr64 CTL).size := by
    have := hS.caps.2.1
    rw [hS.frame.size]; simp only [ctlMin] at this; omega
  refine ⟨⟨⟨h7.arena, core_of_R7 ⟨hA, hB, hC, hD, hE⟩ h7, ⟨fun _ => h7.pinsFull⟩, since_envR hS, h7.mode⟩,
    h7.iw⟩, since_indexR hS, h7.decls, ?_, hdrv, hoff, ?_, ?_, since_indMemos hS hctl, ?_⟩
  · intro i hi b' nP e
    exact frontDecls_of_prefix ⟨hA, hB, hC, hD, hE⟩ i hi b' nP e
  · intro x hx
    refine ⟨hpd x hx, ?_⟩
    obtain ⟨-, hget⟩ := ConRon.Bridge.denoteDecls_getElem hden
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨_, hd⟩ := hget i hi
    exact ⟨_, hd⟩
  · intro x hx
    obtain ⟨k, hk, hd⟩ := prefix_quotU ⟨hA, hB, hC, hD, hE⟩
    simp only [quotNames, List.mem_singleton] at hx
    subst hx
    exact ⟨k, by simp [dnOf, hk, hd], hd⟩
  · rw [hS.frame.size, loadMem_arr, Array.size_replicate]; exact hsz _

/-! ## The index build at the checker's program -/

theorem checkerProg_idxProg : L.Arena.IdxProg checkerProg where
  decl_constants := by chk_lk
  decl_constants_axiom := by chk_lk
  decl_constants_ind := by chk_lk
  decl_tables := by chk_lk
  block_constants := by chk_lk
  block_tables := by chk_lk
  idx_add := by chk_lk
  build_index := by chk_lk
  idx_consts := by chk_lk
  idx_tables := by chk_lk
  base_row_get := by chk_lk
  base_row_set := by chk_lk
  tbl_base_get := by chk_lk
  tbl_base_set := by chk_lk
  iw_reset := by chk_lk

/-- **The twin's side of entry 1**: the stages before the jobs, the stream index `I` built from
`sE`, ending in `sF`. -/
structure PhaseA (b : ByteArray) where
  pins : List ConLeche.NatOpPinSet
  sA : AState
  pre : PreludeIx
  sB : AState
  rc : ParseResultD
  sC : AState
  ds : Array IDeclaration
  sD : AState
  ipins : List INatOpPinSet
  sE : AState
  I : IStreamIndex
  sF : AState
  pfx : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE
  idx : buildIndex ds sE = .ok (.ok I, sF)

/-- **What the index build leaves**: the stages' relation `R7` at the memory `m₇` before the
build, `BuildR` at the built index after it, the record pool's prefix kept, and the build's
write set (`biA`, `biC`). -/
structure FoldAt (b pb : ByteArray) (sz : TieredArray → Nat) (PA : PhaseA b) (m₇ m : Mem) : Prop where
  r7 : R7 (ConAgua.Final.loadMem b pb sz) m₇ pb PA.ds PA.ipins PA.sE
  build : BuildR (dnOf PA.sE.store) PA.ds 0 0 m PA.sF PA.I
  fsize : PA.I.firsts.size = PA.ds.size
  grow : RecGrow m₇ m
  frame : MemFrame biA biC m₇ m
  bytes : m.bytes = m₇.bytes

/-- `FoldAt` at an accepting twin phase A. -/
def FoldA (b pb : ByteArray) (sz : TieredArray → Nat) (m : Mem) : Prop :=
  ∃ (PA : PhaseA b) (m₇ : Mem), FoldAt b pb sz PA m₇ m

/-- **The index build from `R7`**, with `cnt` the count `DECL[0]`, in the form
`checkA_of_stages` takes. -/
theorem buildStage_checker (b pb : ByteArray) (sz : TieredArray → Nat) (hsz : ∀ s, sz s < 2 ^ 64) :
    ∀ n, n ≤ 2 ^ 62 → ∀ (s₀ : St) (cnt : Word),
      ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "build_index" [cnt]
      ⦃fun _ s' => LocEq s' s₀ ∧ (Q7 b (checkerRels b pb sz) s₀.mem →
        (∀ h : 0 < (s₀.mem.arr64 L.Front.DECL).size, cnt = (s₀.mem.arr64 L.Front.DECL)[0]) →
        FoldA b pb sz s'.mem ∧ s'.mem.arr64 L.Front.DECL = s₀.mem.arr64 L.Front.DECL); ⊤⦄ := by
  intro n _ s₀ cnt
  apply M.triple_of_run
  rintro s rs s' rfl hrun
  obtain ⟨F, hF0, hcl⟩ := checkerProg_biW
  obtain ⟨hfr, hby⟩ := M.of_run (P := fun x => x = s) rfl hrun (invoke_memFrame hcl n hF0 [cnt] s)
  obtain ⟨hl, -⟩ := M.of_run (P := fun x => x = s) rfl hrun (callW_spec checkerProg n "build_index" [cnt] s)
  refine ⟨hl, fun hQ hc => ?_⟩
  have hD : s'.mem.arr64 L.Front.DECL = s.mem.arr64 L.Front.DECL :=
    hfr.arr _ (fun h => by simp [biA] at h) (by decide)
  refine ⟨?_, hD⟩
  obtain ⟨sA, pre, sB, rc, sC, ds, sD, pins, ipins, sE, hA, hB, hC, hDp, hE, h7⟩ := hQ
  have hpx : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE := ⟨hA, hB, hC, hDp, hE⟩
  have hR := buildR_of_R7 hsz hpx h7
  have hD0 : 0 < (s.mem.arr64 L.Front.DECL).size := by
    have := h7.since.caps.2.2.1; rw [h7.since.frame.size]; exact this
  have hcnt : cnt.toNat = ds.size := by
    rw [hc hD0]; have := h7.decls.count; simpa [hD0] using this
  obtain ⟨I, a', hI, hR', hsz', hG⟩ := (M.of_run (P := fun x => x = s) rfl hrun
    (buildIndex_refines checkerProg_idxProg cnt hcnt n s sE hR)).2
  exact ⟨⟨pins, sA, pre, sB, rc, sC, ds, sD, ipins, sE, I, a', hpx, hI⟩, s.mem, ⟨h7, hR', hsz', hG, hfr, hby⟩⟩

end L.Checker
