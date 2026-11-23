module

public import ConAgua.Checker.LoopStage
public import ConAgua.Arena.IndexBuild
import ConAgua.Checker.IndDeclConstsProg
import ConAgua.Checker.TwinShapeQuot
import ConAgua.Checker.TwinCaches
import ConAgua.Checker.RomProgInit
import ConRon.Bridge.Checker.Pool
import ConRon.Bridge.Stages
public import ConAgua.Checker.BuildClosed
public import ConAgua.Checker.PipeFinal
public meta import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.LoopProgTac
import all ConAgua.Arena.CheckerL
import all ConAgua.Arena.Pins
import all ConAgua.Arena.Env
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndexLoops
public import ConAgua.Arena.LoopStart

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
tiers), the inductive memos (`IndMemos.zero`), the core's walk memos (`CoreMemos.zero`). -/
def buildZeroArrs : List TieredArray :=
  tier0s [EIXA, EIXS, EIXN, TIXA, TIXS, TIXN, OIXA, OIXS, OIXN, OTXA, OTXS, OTXN, 51, 155,
    201, 202, 203, 204, 205, 206, 207, 208, 49, 50, 52, 53, 54, 151, 152, 153] ++
  tier1s [OIXA, OIXS, OIXN, OTXA, OTXS, OTXN]

/-- The `CTL` words the index build's start needs zero: the index's counter, the stamp, the
view's bounds, the inductive memos' words, the literal flags, names and thresholds. -/
def buildZeroCtls : List Nat :=
  [128, 133, 134, 135, 52, 158, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214,
    215, 216, 217, 218, 219, 48, 50, 54, 56, 58, 152, 154, 156, 160, 161, 162, 163, 164, 165, 166,
    167, 168, 169, 170, 171, 172, 173]

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
    simp [hm] at this
  have hc : t ≠ CTL := by rintro rfl; revert ht; decide
  rw [h.frame.arr t hn hc, loadMem_arr]

theorem since_rdN {t : TieredArray} (ht : t ∈ buildZeroArrs) (k : Nat) : rdN (m.arr64 t) k = 0 := by
  rw [since_zeroA h ht]; simp only [rdN, Array.getElem?_replicate]; split <;> rfl

theorem since_rdW {t : TieredArray} (ht : t ∈ buildZeroArrs) (k : Word) : rdW (m.arr64 t) k = 0 := by
  rw [since_zeroA h ht]; simp only [rdW, Array.getElem?_replicate]; split <;> rfl

theorem since_ctl {x : Word} (hx : x.toNat ∈ buildZeroCtls) : rdW (m.arr64 CTL) x = 0 := by
  have hn : x ∉ preLoopC := fun hm => by
    have := List.all_eq_true.mp preLoopC_buildZero x.toNat (List.mem_map.mpr ⟨x, hm, rfl⟩)
    simp [hx] at this
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

theorem litFrom_empty (k : Nat) (hk : 0 < k) :
    litFrom ({} : IStreamIndex).base.idx (List.replicate 10 (decI 0)) 0 k = none := by
  rw [litFrom.eq_1, ite_eq_right_of_eq_false _ _ (by simp; omega)]
  simp

/-- The builder's environment before the literal names are written (`CTL[162‥171]` still
`0`): the view `0` of the empty index frozen at those words. -/
def bEnvZ : IFEnv := (frozenAt ({} : IStreamIndex) (List.replicate 10 (decI 0))).view 0

theorem bEnvZ_relits (P : Pins) :
    { bEnvZ with base := { bEnvZ.base with lits := drvLits P } } = bEnv ({} : IStreamIndex).base P 0 0 := by
  simp only [bEnvZ, IStreamIndex.view, frozenAt, bEnv, litFrom_empty _ (by decide : 0 < NAT_LIT_COUNT),
    litFrom_empty _ (by decide : 0 < STR_LIT_COUNT)]
  rfl

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
  refine ⟨fun n => ?_, fun n => ?_, fun i hi => absurd hi (by simp), by simp, ?_,
    fun x _ => by rw [since_baseRow h x]; decide⟩
  · rw [ite_eq_left (since_baseRow h _)]; simp
  · rw [ite_eq_left (since_baseTbl h _)]; simp
  · rw [since_ctl h (x := 128) (by decide)]; rfl

theorem since_envR : EnvR m 0 bEnvZ := by
  have hz : ∀ i < 10, rdW (m.arr64 CTL) (162 + UInt64.ofNat i) = 0 := by
    intro i hi; apply since_ctl h; revert hi; revert i; decide
  refine EnvR.ofIndex (k := 0) ((since_indexR h).frozenAt _) ⟨?_, ?_, ?_⟩ (since_ownEmpty h)
    (since_ownBelow h) (by rw [since_stamp h]; decide) (by rw [since_ctl h (x := 134) (by decide)]; rfl)
    (by rw [since_ctl h (x := 135) (by decide)]; rfl) ?_ ?_
  · show (List.replicate 10 (decI 0 : NIdx)).map (·.word.toUInt64) = litWords m
    rw [List.map_replicate, decI_word_self 0 (by decide)]
    apply List.ext_getElem (by simp [litWords])
    intro i h1 h2
    simp only [List.length_replicate] at h1
    rw [List.getElem_replicate]
    simp only [litWords, List.getElem_map, List.getElem_range]
    exact (hz i h1).symm
  · show litFrom _ _ 0 NAT_LIT_COUNT = _
    rw [litFrom_empty _ (by decide), since_ctl h (x := 172) (by decide)]; rfl
  · show litFrom _ _ 0 STR_LIT_COUNT = _
    rw [litFrom_empty _ (by decide), since_ctl h (x := 173) (by decide)]; rfl
  · show _ = fromLe (litFrom _ _ 0 NAT_LIT_COUNT) _
    rw [litFrom_empty _ (by decide), since_ctl h (x := 160) (by decide)]; rfl
  · show _ = fromLe (litFrom _ _ 0 STR_LIT_COUNT) _
    rw [litFrom_empty _ (by decide), since_ctl h (x := 161) (by decide)]; rfl

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

theorem since_coreMemos (hctl : 220 ≤ (m.arr64 CTL).size) : CoreMemos m :=
  CoreMemos.zero (by omega)
    (fun b hb j => since_rdW h (t := (b : TieredArray)) (by
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) j)
    (fun x hx => since_ctl h (by
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))

end zero

/-- **The twin's facts after the stages before the index build** (the flat run's: `stages_frame`,
`StagesOut.flat`; the compared run's solution: `stagesC_frame`): what the index build and the jobs
use of the stages. -/
structure StagesOut (sE : AState) (ds : Array IDeclaration) (ipins : List INatOpPinSet)
    (pins : List ConLeche.NatOpPinSet) : Prop where
  off : sE.store.scratchOn = false
  drv : ConRon.Bridge.DriverOK sE
  pp : ConRon.Bridge.PersPins sE
  pinsDn : ConRon.Bridge.PinsDenote sE.store ipins pins
  pps : ConRon.Bridge.PersPinSets ipins
  pd : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x
  den : ∃ dsP, ConRon.Bridge.denoteDecls sE.store ds.toList = some dsP
  caches : sE.caches = (AState.init EStore.empty).caches
  front : L.Arena.FrontDecls ds
  quot : ∃ k : NIdx, k.isPersistent = true ∧ ConRon.Arena.denoteN sE.store.ns k = some (ConLeche.Name.str .anonymous "u")

/-- The flat run's `StagesOut`. -/
theorem StagesOut.flat {b : ByteArray} {sA : AState} {pre : PreludeIx} {sB : AState}
    {rc : ParseResultD} {sC : AState} {ds : Array IDeclaration} {sD : AState}
    {pins : List ConLeche.NatOpPinSet} {ipins : List INatOpPinSet} {sE : AState}
    (hpx : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE) : StagesOut sE ds ipins pins := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := hpx
  obtain ⟨hoff, hdrv, hpp, hpdn, hpps, hpd, _rc, _preC, -, hden⟩ :=
    ConRon.Bridge.stages_frame (chunks := [b]) hA hB hC hD hE
  exact ⟨hoff, hdrv, hpp, hpdn, hpps, hpd, ⟨_, hden⟩, (prefix_caches ⟨hA, hB, hC, hD, hE⟩).1,
    frontDecls_of_prefix ⟨hA, hB, hC, hD, hE⟩, prefix_quotU ⟨hA, hB, hC, hD, hE⟩⟩

/-- **The index build's start**: after the stages up to `intern_all_pins` (memory `m`, the twin's
facts after them `StagesOut`) and the literal names' writes (`str_lit_names`, memory `m'`), the
memory is `BuildR` at the empty stream index, at the twin's state after the stages. -/
theorem buildR_of_out {b pb : ByteArray} {sz : TieredArray → Nat} (hsz : ∀ s, sz s < 2 ^ 64)
    {ds : Array IDeclaration} {pins : List ConLeche.NatOpPinSet}
    {ipins : List INatOpPinSet} {sE : AState} {m : Mem}
    (ho : StagesOut sE ds ipins pins)
    (h7 : R7 (ConAgua.Final.loadMem b pb sz) m pb ds ipins sE) {m' : Mem}
    (hf : MemFrame [] litCtl m m') (hl : (pinLits m).map (·.word.toUInt64) = litWords m') :
    BuildR (dnOf sE.store) ds m' sE {} := by
  have hoff := ho.off
  have hdrv := ho.drv
  have hpd := ho.pd
  obtain ⟨_dsP, hden⟩ := ho.den
  have hS := h7.since
  have hctl : 220 ≤ (m.arr64 CTL).size := by
    have := hS.caps.2.1
    rw [hS.frame.size]; simp only [ctlMin] at this; omega
  have sz63 : ∀ t : TieredArray, t ∈ checkerArrays.wordSlots → (m.arr64 t).size < 2 ^ 63 := fun t ht => by
    rw [hS.frame.size]; have := (hS.caps.1 t ht).1; omega
  have hT : TwinOK (dnOf sE.store) m sE (bEnv ({} : IStreamIndex).base sE.pins 0 0) :=
    TwinOK.of_check (checkOK_congrFe (fe := ConRon.Bridge.driverFE sE.pins)
      (fun n => (bEnv_find_zero _ _ n).trans (emptyEnv_find _ n).symm)
      (fun n => (bEnv_findTable_zero _ _ n).trans (emptyEnv_findTable _ n).symm) (bEnv_flags _ _) rfl hdrv)
      ⟨sz63 _ (by decide), sz63 _ (by decide), sz63 _ (by decide), since_coreMemos hS hctl,
        fun k x hk => by simp only [dnOf] at hk; split at hk <;> simp_all⟩
  have hS0 : L.Ind.StageR 0 bEnvZ m sE :=
    ⟨⟨h7.arena, core_of_R7' ho.caches h7, ⟨fun _ => h7.pinsFull⟩, since_envR hS, h7.mode⟩, h7.iw⟩
  have hE' : EnvR m' 0 (bEnv ({} : IStreamIndex).base sE.pins 0 0) := by
    have := (since_envR hS).relits hf (L := drvLits sE.pins) (by rw [← pinLits_drv h7.pinsFull]; exact hl)
    rwa [bEnvZ_relits] at this
  have hlo : ∀ x : Word, x.toNat < 160 → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x := fun x hx' =>
    hf.ctl x (fun hx => by
      simp only [litCtl, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h | h | h | h | h | h <;> subst h <;> exact absurd hx' (by decide))
  have ha : ∀ t : TieredArray, t ≠ CTL → m'.arr64 t = m.arr64 t := fun t ht => hf.arr t (by simp) ht
  refine ⟨(L.Ind.StageR.of_lits hS0 hf hE').1,
    hT.frame hf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [pinW_frame hf (by decide)]; exact h7.pin0, (since_indexR hS).ctlHi ha hlo,
    by rw [ha _ (by decide), ha _ (by decide)]; exact h7.decls, ?_, hdrv, hoff, ?_, ?_,
    (since_indMemos hS hctl).frame hf (fun b hb => by simp at hb) (fun x hx => by
      simp only [litCtl, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide), ?_⟩
  · intro i hi b' nP e
    exact ho.front i hi b' nP e
  · intro x hx
    refine ⟨hpd x hx, ?_⟩
    obtain ⟨-, hget⟩ := ConRon.Bridge.denoteDecls_getElem hden
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨_, hd⟩ := hget i hi
    exact ⟨_, hd⟩
  · intro x hx
    obtain ⟨k, hk, hd⟩ := ho.quot
    simp only [quotNames, List.mem_singleton] at hx
    subst hx
    exact ⟨k, by simp [dnOf, hk, hd], hd⟩
  · rw [ha _ (by decide), hS.frame.size, loadMem_arr, Array.size_replicate]; exact hsz _

/-- **The index build's start**, for the flat run (`buildR_of_out`). -/
theorem buildR_of_R7 {b pb : ByteArray} {sz : TieredArray → Nat} (hsz : ∀ s, sz s < 2 ^ 64)
    {sA : AState} {pre : PreludeIx} {sB : AState} {rc : ParseResultD} {sC : AState}
    {ds : Array IDeclaration} {sD : AState} {pins : List ConLeche.NatOpPinSet}
    {ipins : List INatOpPinSet} {sE : AState} {m : Mem}
    (hpx : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE)
    (h7 : R7 (ConAgua.Final.loadMem b pb sz) m pb ds ipins sE) {m' : Mem}
    (hf : MemFrame [] litCtl m m') (hl : (pinLits m).map (·.word.toUInt64) = litWords m') :
    BuildR (dnOf sE.store) ds m' sE {} :=
  buildR_of_out hsz (StagesOut.flat hpx) h7 hf hl

/-! ## The index build at the checker's program -/

/-- **The index build's program facts at the substituted checker** (`decl_constants`' callees
read the ROM: `BasisRefs` needs `RomRefs`, which hold at `Prog.subPB` only). -/
theorem checkerProg_idxProgPB (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length) : L.Arena.IdxProg (Prog.subPB bs checkerProg) := by
  prog_bundle [declConstsProg_checker bs hr hpre]

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
  build : BuildR (dnOf PA.sE.store) PA.ds m PA.sF PA.I
  /-- The index is frozen: its literal names and thresholds in `CTL[162‥173]`. -/
  frozen : FrozenR m PA.I
  fsize : PA.I.firsts.size = PA.ds.size
  grow : BKeep m₇ m
  frame : MemFrame biA biC m₇ m
  bytes : m.bytes = m₇.bytes

/-- `FoldAt` at an accepting twin phase A. -/
def FoldA (b pb : ByteArray) (sz : TieredArray → Nat) (m : Mem) : Prop :=
  ∃ (PA : PhaseA b) (m₇ : Mem), FoldAt b pb sz PA m₇ m

/-- **The index build from `R7`**, with `cnt` the count `DECL[0]`, in the form
`checkA_of_stages` takes. -/
theorem buildStage_checker (b pb : ByteArray) (sz : TieredArray → Nat) (hpb : pb.size < 2 ^ 63)
    (hsz : ∀ s, sz s < 2 ^ 64) :
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
  have hctl : 220 ≤ (s.mem.arr64 CTL).size := by
    have := h7.since.caps.2.1
    rw [h7.since.frame.size]; simp only [ctlMin] at this; omega
  have hD0 : 0 < (s.mem.arr64 L.Front.DECL).size := by
    have := h7.since.caps.2.2.1; rw [h7.since.frame.size]; exact this
  have hcnt : cnt.toNat = ds.size := by
    rw [hc hD0]; have := h7.decls.count; simpa [hD0] using this
  have hPB : s.mem.arr8 L.Rom.PB = pb.data.toList.toArray := by
    rw [h7.since.keep.arr8]; exact loadMem_pb b pb sz
  rw [← L.Rom.invoke_subPB (bs := pb.data.toList) checkerProg_noSt8PB n _ _ hPB] at hrun
  obtain ⟨I, a', hI, hR', hFz, hsz', hG⟩ := (M.of_run (P := fun x => x = s) rfl hrun
    (buildIndex_refines (checkerProg_idxProgPB pb.data.toList
      (by simpa [RomOK] using hpb) h7.since.pbpre) cnt hcnt n s sE h7.pinsFull (by omega)
      (fun _ hf hl => buildR_of_R7 hsz hpx h7 hf hl))).2
  exact ⟨⟨pins, sA, pre, sB, rc, sC, ds, sD, ipins, sE, I, a', hpx, hI⟩, s.mem, ⟨h7, hR', hFz, hsz', hG, hfr, hby⟩⟩

end L.Checker
