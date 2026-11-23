module

public import ConAgua.Checker.CompareChain6R
import ConAgua.Checker.RomProgInit
import ConRon.Bridge.Checker.Pool
import ConRon.Bridge.Stages
import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.RomProg0

@[expose] public section

/-!
# Mode `6`'s index build: its start (lane compare)

`buildR6`: after the mates (`Q65`: the side records `Side6`, the mates' frame `MKeep`), and the
literal names' writes, the memory is `BuildR` at the empty index and the challenge's side records,
at the twin's state after them (as `buildR_of_out` for the flat run).
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend

section build
variable {bC bS pb : ByteArray} {sz : TieredArray → Nat} {PS : PhaseS bC bS} {m₇ m : Mem}

/-- The challenge's twin phase of a `Side6`. -/
def Side6.phase {c : Word} {m2 m3 : Mem} {dsC : Array IDeclaration} {sG : AState}
    {res : List IDeclaration} {m4 : Mem} (h : Side6 PS m c m2 m3 dsC sG res m4) : PhaseC bC bS :=
  { PS with dsC := dsC, sG := sG, recsC := res, sH := sG, prep := h.prep.run, side := h.run }

/-- An array outside mode `6`'s writes before the mates, by its number. -/
theorem not_mem_A64 {b : TieredArray} (h : ¬((129 ≤ b.arr ∧ b.arr ≤ 134) ∨ (210 ≤ b.arr ∧ b.arr ≤ 215) ∨
    b.arr = 240 ∨ b.arr = 67 ∨ b.arr = 208 ∨ b.arr = 33 ∨ b.arr = 34 ∨ b.arr = 75 ∨ b.arr = 76 ∨
    b.arr = 200)) : b ∉ A64 := fun hb => h (A64_arr b hb)

/-- A control word outside mode `6`'s writes before the mates. -/
theorem not_mem_C64 {x : Word} (h : ¬(x = 225 ∨ x = 226 ∨ x = 128 ∨ x = 34 ∨ x = 35 ∨ x = 73 ∨ x = 74 ∨
    x = 75 ∨ x = 76 ∨ x = 200 ∨ x = 216 ∨ x = 217)) : x ∉ C64 := fun hx => h (C64_val x hx)

/-- **`CoreMemos` after the mates**, from the solution's index build. -/
theorem Side6.coreMemos (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) {c : Word}
    {m2 m3 : Mem} {dsC : Array IDeclaration} {sG : AState} {res : List IDeclaration} {m4 m5 : Mem}
    (h : Side6 PS m c m2 m3 dsC sG res m4) (hK : MKeep m4 m5) : CoreMemos m5 :=
  (hF.build.twin.memos.frame h.frameM ⟨not_mem_A64 (by decide), not_mem_A64 (by decide)⟩
    ⟨not_mem_C64 (by decide), not_mem_C64 (by decide)⟩
    ⟨not_mem_A64 (by decide), not_mem_A64 (by decide), not_mem_A64 (by decide)⟩
    ⟨not_mem_C64 (by decide), not_mem_C64 (by decide), not_mem_C64 (by decide)⟩
    ⟨not_mem_A64 (by decide), not_mem_A64 (by decide), not_mem_A64 (by decide)⟩
    ⟨not_mem_C64 (by decide), not_mem_C64 (by decide), not_mem_C64 (by decide)⟩
    (not_mem_A64 (by decide)) (not_mem_C64 (by decide))).frame hK.frame ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩

/-- **The challenge's index build's start**: after the mates and the literal names' writes, `BuildR`
at the empty index, the challenge's side records and the twin's state after them. -/
theorem buildR6 (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) (hst : Stash m PS.pre PS.rC)
    (hk6 : Keep6 m PS.pre) (hsz : ∀ s, sz s < 2 ^ 64) {c : Word}
    {m2 m3 : Mem} {dsC : Array IDeclaration} {sG : AState} {res : List IDeclaration} {m4 m5 : Mem}
    (h : Side6 PS m c m2 m3 dsC sG res m4) (hK : MKeep m4 m5) (hMI : MInv m5) {m' : Mem}
    (hf : MemFrame [] litCtl m5 m') (hl : (pinLits m5).map (·.word.toUInt64) = litWords m') :
    BuildR (dnOf sG.store) res.toArray m' sG {} := by
  obtain ⟨hS5, hI5⟩ := h.stage5 hK hMI
  obtain ⟨-, -, -, -, ho⟩ := h.phase.out
  have hoff := ho.off
  have hdrv := ho.drv
  have hpd := ho.pd
  obtain ⟨_dsP, hden⟩ := ho.den
  have hpe : sG.pins = PS.sF.pins := h.prep.pinsEq
  have hfr := h.frameM
  have hsize : ∀ t, (m'.arr64 t).size = sz t := fun t => by
    rw [hf.size, hK.frame.size, hfr.size, hF.sizeAt]
  have hcaps := hF.r7.since.caps
  have sz63 : ∀ t : TieredArray, t ∈ checkerArrays.wordSlots → (m'.arr64 t).size < 2 ^ 63 := fun t ht => by
    rw [hsize]; have := (hcaps.1 t ht).1; rw [loadMem_arr, Array.size_replicate] at this; omega
  have hpin : pinW m5 0 = pinW m 0 := by
    rw [pinW_frame hK.frame (by decide), pinW_frame hfr (not_mem_A64 (by decide))]
  have hflag : pinW m5 0 ≠ 0 := by rw [hpin]; exact hF.build.pin
  have hPF : PinsFull m5 PS.sF.pins := by rw [← hpe]; exact hS5.check.pins.full hflag
  have hl' : (drvLits PS.sF.pins).map (·.word.toUInt64) = litWords m' := by
    rw [← pinLits_drv hPF]; exact hl
  have hE' := hS5.check.env.relits hf hl'
  have hT : TwinOK (dnOf sG.store) m' sG (bEnv ({} : IStreamIndex).base sG.pins 0 0) :=
    TwinOK.of_check (checkOK_congrFe (fe := ConRon.Bridge.driverFE sG.pins)
      (fun n => (bEnv_find_zero _ _ n).trans (emptyEnv_find _ n).symm)
      (fun n => (bEnv_findTable_zero _ _ n).trans (emptyEnv_findTable _ n).symm) (bEnv_flags _ _) rfl hdrv)
      ⟨sz63 _ (by decide), sz63 _ (by decide), sz63 _ (by decide),
        (h.coreMemos hF hK).frame hf (by simp) (by decide),
        fun k x hk => by simp only [dnOf] at hk; split at hk <;> simp_all⟩
  have P6 := prep6_of hF hst hk6 h.q62
  have hM : IndMemos m' := (((h.prep.memos P6.memos).side h.frame h.mc).frame hK.frame
      (fun b hb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> decide)
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; decide)).frame hf
      (fun b hb => by simp at hb)
      (fun x hx => by
        simp only [litCtl, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide)
  have ha : ∀ t : TieredArray, t ≠ CTL → m'.arr64 t = m5.arr64 t := fun t ht => hf.arr t (by simp) ht
  have hlo : ∀ x : Word, x.toNat < 160 → rdW (m'.arr64 CTL) x = rdW (m5.arr64 CTL) x := fun x hx' =>
    hf.ctl x (fun hx => by
      simp only [litCtl, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h | h | h | h | h | h <;> subst h <;> exact absurd hx' (by decide))
  have eD : m'.arr64 L.Front.DECL = m4.arr64 L.Front.DECL := by
    rw [ha _ (by decide), hK.frame.arr _ (by decide) (by decide)]
  have eP : m'.arr64 L.Front.DLP = m4.arr64 L.Front.DLP := by
    rw [ha _ (by decide), hK.frame.arr _ (by decide) (by decide)]
  refine ⟨by rw [hpe]; exact (L.Ind.StageR.of_lits hS5 hf hE').1, hT,
    by rw [pinW_frame hf (by decide)]; exact hflag, hI5.ctlHi ha hlo,
    by rw [eD, eP]; exact h.decls, ?_, hdrv, hoff, ?_, ?_, hM, by rw [hsize]; exact hsz _,
    show (0 : Nat) < 2 ^ 32 by decide⟩
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
    have hd' : ConRon.Arena.denoteN sG.store.ns k = some (ConLeche.Name.str .anonymous "u") := hd
    exact ⟨k, by simp [dnOf, hk, hd'], hd'⟩

/-- After the challenge's index build, at the count `c`. -/
def G6 (PS : PhaseS bC bS) (m : Mem) (c : Word) (m6 : Mem) : Prop :=
  ∃ m2 m3 dsC sG res m4 m5, Side6 PS m c m2 m3 dsC sG res m4 ∧
    MatesR m5 (recordMatesGo ∅ res.toArray.toList) ∧ MInv m5 ∧ MKeep m4 m5 ∧
    ∃ I a', buildIndex res.toArray sG = .ok (.ok I, a') ∧ BuildR (dnOf sG.store) res.toArray m6 a' I ∧
      FrozenR m6 I ∧ I.firsts.size = res.toArray.size ∧ BKeep m5 m6 ∧ MemFrame biA biC m5 m6 ∧
      m6.bytes = m5.bytes

/-- **`build_index(c)`, as a step**: the challenge's index build (`buildIndex_refines` from
`buildR6`). -/
theorem buildStep6 (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) (hst : Stash m PS.pre PS.rC)
    (hk6 : Keep6 m PS.pre) (hsz : ∀ s, sz s < 2 ^ 64) (hpb : pb.size < 2 ^ 63) :
    StageSpecC checkerProg "build_index" (fun c m5 => Q65 PS m c m5 ∧ m5.bytes = m.bytes) (G6 PS m) := by
  intro n _ s₀ c
  apply M.triple_of_run
  rintro s rs s' rfl hrun
  obtain ⟨F, hF0, hcl⟩ := checkerProg_biW
  obtain ⟨hfr, hby⟩ := M.of_run (P := fun x => x = s) rfl hrun (invoke_memFrame hcl n hF0 [c] s)
  obtain ⟨hl, -⟩ := M.of_run (P := fun x => x = s) rfl hrun (callW_spec checkerProg n "build_index" [c] s)
  refine ⟨hl, fun ⟨⟨m2, m3, dsC, sG, res, m4, h, hMt, hMI, hK⟩, hbytes⟩ => ?_⟩
  obtain ⟨hS5, -⟩ := h.stage5 hK hMI
  have hpin : pinW s.mem 0 = pinW m 0 := by
    rw [pinW_frame hK.frame (by decide), pinW_frame h.frameM (not_mem_A64 (by decide))]
  have hPF : PinsFull s.mem sG.pins := hS5.check.pins.full (by rw [hpin]; exact hF.build.pin)
  have hcnt : c.toNat = res.toArray.size := by simpa using h.count.1
  have hPB : s.mem.arr8 L.Rom.PB = pb.data.toList.toArray := by
    show s.mem.bytes L.Rom.PB = _
    rw [hbytes, hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]
    exact loadMem_pb bS pb sz
  rw [← L.Rom.invoke_subPB (bs := pb.data.toList) checkerProg_noSt8PB n _ _ hPB] at hrun
  obtain ⟨I, a', hI, hR', hFz, hsz', hG⟩ := (M.of_run (P := fun x => x = s) rfl hrun
    (buildIndex_refines (checkerProg_idxProgPB pb.data.toList
      (by simpa [RomOK] using hpb) hF.r7.since.pbpre) c hcnt n s sG hPF
      (by have := hS5.iw.ctl; omega)
      (fun _ hf hl => buildR6 hF hst hk6 hsz h hK hMI hf hl))).2
  exact ⟨m2, m3, dsC, sG, res, m4, s.mem, h, hMt, hMI, hK, I, a', hI, hR', hFz, hsz', hG, hfr, hby⟩

end build

end L.Checker
