module

public import ConAgua.Checker.ParDriverL
import ConAgua.Checker.CheckARun
public import ConAgua.Checker.JobsProg
public import ConAgua.Checker.ArmsT
import all ConAgua.Checker.Entry
import ConAgua.Checker.LoopProg
import ConAgua.Checker.TwinShapeQuot
public import ConAgua.Checker.PresizeStage
public import ConAgua.Final.Twin

@[expose] public section

/-!
# The sequential driver's two runs give `TwinAccepts` (lane parmode, stage 3 of lane ronsync2)

docs/design/parmode.md, "Redesign". `drv_twinAccepts`: entry 1 (`check` with the mode word `3`,
from the loaded memory) returning `2^63 + k`, then entry 2 in place (`check` with the mode word `2`
on a memory `w` that keeps entry 1's final word arrays the jobs name, the range `[0, k)`, an empty
seed) returning `ACCEPT`: the twin's pipeline accepts. Entry 1 is `checkA_run` (the stages and the
stream index, `FoldAt`; the memory is the buffer's `parCompactMem`, with the header only), entry 2
`checkB_seq` (the flush, then the jobs, through non-interference and the pool's induction with one
worker), and the two are `SeqAccepts`, i.e. `TwinAccepts` (`Final/Twin.lean`). The jobs' program
facts at the substituted program (`JobProg`) come from `checkerProg_jobProgPB`, with `check_decl`'s
(`CdProg`, the core area's) a hypothesis (`CheckerCd`).
-/

set_option experimental.vcgen true

open ConRon.Arena ConAgua.Final
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena L.Rom

universe w

/-- **Entry 2 in place, `check` with the mode word `2`**: `check_b` (as `checkB_seq`). -/
theorem checkMode2_seqO {b pb : ByteArray}
    {sz : TieredArray → Nat} {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    {pins : List ConLeche.NatOpPinSet} {sE : AState} {I : IStreamIndex} {sF : AState} {m₇ m : Mem}
    (ho : StagesOut sE ds ipins pins) (hidx : buildIndex ds sE = .ok (.ok I, sF))
    (hF : FoldOn b pb sz ds ipins sE I sF m₇ m)
    (hJP : JobProg ipins (dnOf sE.store) ds (Prog.subPB pb.data.toList checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (hi : Word) (hhi : hi.toNat = ds.size) (s₀ : St)
    (hw : ∀ a, phaseBS a = true → s₀.mem.arr64 a = m.arr64 a) (hmode : s₀.mem.glob MODE = 2)
    (hlo : s₀.mem.glob PLO = 0) (hhi' : s₀.mem.glob PHI = hi) (hctlf : (s₀.mem.arr64 CTLF).size = 0) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun r _ => r.headD 0 = ACCEPT →
      ∃ s'', checkJobList .verified ipins none I ds (List.range ds.size) sF.worker =
        .ok (.ok (), s''); ⊤⦄ := by
  rw [invoke_eq _ checkerProg_lookup_check']
  simp only [callFn, checkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hB := checkB_seqO ho hidx hF hJP n (by omega) hi hhi
    have hmode' : s₀.mem.glob ⟨8⟩ = 2 := hmode
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hB,
      (L.invoke_loc checkerProg (exec checkerProg n) "check_a" [1] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_a" [0] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_c1" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_c2" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_c3" [] ·)]
    all_goals (try simp only [St.setLoc_loc, St.setLocs_cons,
      Cmp.eval, reduceIte, beq_iff_eq, Sig.retVal, Sig.retOr, St.setLocs_nil, List.headD_cons] at *)
    all_goals first
      | (simp_all (config := { decide := true }); done)
      | (simp_all [St.setLoc]; done)

/-- `checkMode2_seqO` at a phase A. -/
theorem checkMode2_seq {b pb : ByteArray}
    {sz : TieredArray → Nat} {PA : PhaseA b} {m₇ m : Mem}
    (hF : FoldAt b pb sz PA m₇ m)
    (hJP : JobProg PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (hi : Word) (hhi : hi.toNat = PA.ds.size) (s₀ : St)
    (hw : ∀ a, phaseBS a = true → s₀.mem.arr64 a = m.arr64 a) (hmode : s₀.mem.glob MODE = 2)
    (hlo : s₀.mem.glob PLO = 0) (hhi' : s₀.mem.glob PHI = hi) (hctlf : (s₀.mem.arr64 CTLF).size = 0) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun r _ => r.headD 0 = ACCEPT →
      ∃ s'', checkJobList .verified PA.ipins none PA.I PA.ds (List.range PA.ds.size) PA.sF.worker =
        .ok (.ok (), s''); ⊤⦄ :=
  checkMode2_seqO PA.out PA.idx hF.on hJP n hn hi hhi s₀ hw hmode hlo hhi' hctlf

/-- **`check_decl`'s program facts at any record decoder** (`CheckerCd` at every record
decoder that is injective, every pin list and every record array): what `CheckerCd`'s proof
uses. -/
def CheckerCdG : Prop :=
  ∀ (pb : ByteArray) (ipins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
    (ds : Array IDeclaration), pb.size < 2 ^ 63 → PbPre pb → L.Ind.DnInj dn →
    (∀ cv v hh, ArmSpecT ipins dn ds (Prog.subPB pb.data.toList checkerProg)
      "check_decl_defn" (.defnDecl cv v hh)) ∧
    IndArmSpec (Prog.subPB pb.data.toList checkerProg) dn

/-- The record decoder after the stages is injective. -/
theorem StagesOut.dnInj {sE : AState} {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    {pins : List ConLeche.NatOpPinSet} (ho : StagesOut sE ds ipins pins) : L.Ind.DnInj (dnOf sE.store) :=
  dnOf_inj ho.drv.state.wf

/-- `Quot`'s universe name has a handle under the record decoder after the stages. -/
theorem StagesOut.quotDn {sE : AState} {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    {pins : List ConLeche.NatOpPinSet} (ho : StagesOut sE ds ipins pins) : L.Ind.QuotDn (dnOf sE.store) := by
  obtain ⟨k, hk, hd⟩ := ho.quot
  exact ⟨k, by simp [dnOf, hk, hd]⟩

/-- The jobs' program facts after the stages, from `CheckerCdG`. -/
theorem jobProg_of_out (hCd : CheckerCdG) {sE : AState} {ds : Array IDeclaration}
    {ipins : List INatOpPinSet} {pins : List ConLeche.NatOpPinSet} (ho : StagesOut sE ds ipins pins)
    {pb : ByteArray} (hpb : pb.size < 2 ^ 63) (hpre : PbPre pb) :
    JobProg ipins (dnOf sE.store) ds (Prog.subPB pb.data.toList checkerProg) :=
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hpb
  let ⟨hdf, hind⟩ := hCd pb ipins (dnOf sE.store) ds hpb hpre ho.dnInj
  checkerProg_jobProgPB pb.data.toList hr hpre
    (checkerProg_cdProgPB pb.data.toList hr hpre ho.dnInj ho.quotDn hdf hind)
    (checkerProg_canonPB _)

/-- **What `check_decl`'s program facts still take** (`checkerProg_cdProgPB`): the definition
arm's claim and the inductive arm's, at every phase A and every pin buffer `pb` that starts with the
ROM, at the program with `pb` substituted (`Final/DrvFinal.lean`'s `checkerCd_proved`). -/
def CheckerCd : Prop :=
  ∀ (b pb : ByteArray) (PA : PhaseA b), pb.size < 2 ^ 63 → PbPre pb →
    (∀ cv v hh, ArmSpecT PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg)
      "check_decl_defn" (.defnDecl cv v hh)) ∧
    IndArmSpec (Prog.subPB pb.data.toList checkerProg) (dnOf PA.sE.store)

/-- `CheckerCdG` gives `CheckerCd`. -/
theorem CheckerCdG.cd (h : CheckerCdG) : CheckerCd := fun _ pb PA hpb hpre =>
  h pb PA.ipins (dnOf PA.sE.store) PA.ds hpb hpre (dnOf_inj PA.out.drv.state.wf)

/-- The record decoder of a phase A is injective. -/
theorem PhaseA.dnInj {b : ByteArray} (PA : PhaseA b) : L.Ind.DnInj (dnOf PA.sE.store) := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := PA.pfx
  obtain ⟨-, hdrv, -⟩ := ConRon.Bridge.stages_frame (chunks := [b]) hA hB hC hD hE
  exact dnOf_inj hdrv.state.wf

/-- `Quot`'s universe name has a handle under a phase A's record decoder. -/
theorem PhaseA.quotDn {b : ByteArray} (PA : PhaseA b) : L.Ind.QuotDn (dnOf PA.sE.store) := by
  obtain ⟨k, hk, hd⟩ := prefix_quotU PA.pfx
  exact ⟨k, by simp [dnOf, hk, hd]⟩

/-- The jobs' program facts at a phase A, from `CheckerCd`. -/
theorem jobProg_of_cd (hCd : CheckerCd) {b pb : ByteArray} (PA : PhaseA b) (hpb : pb.size < 2 ^ 63)
    (hpre : PbPre pb) :
    JobProg PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg) :=
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hpb
  let ⟨hdf, hind⟩ := hCd b pb PA hpb hpre
  checkerProg_jobProgPB pb.data.toList hr hpre
    (checkerProg_cdProgPB pb.data.toList hr hpre PA.dnInj PA.quotDn hdf hind)
    (checkerProg_canonPB _)

/-- **The driver's two runs accept ⇒ the twin accepts**, given `check_decl`'s program facts
(`CheckerCd`). -/
theorem drv_twinAccepts (hCd : CheckerCd) (b pb : ByteArray)
    (sz : TieredArray → Nat) (hin : InputsOK b pb sz)
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N₁ "check" [] (loadMemM b pb sz 3) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (N₂ : Nat) (hN₂ : N₂ ≤ 2 ^ 62) (w : Mem) (rs₂ : List Word) (m₂ : Mem)
    (hw : ∀ a, phaseBS a = true → w.arr64 a = m₁.arr64 a) (hmode : w.glob MODE = 2)
    (hlo : w.glob PLO = 0) (hhi : w.glob PHI = rs₁.headD 0 - 9223372036854775808)
    (hctlf : (w.arr64 CTLF).size = 0)
    (h₂ : L.run checkerProg N₂ "check" [] w = .ok (rs₂, m₂)) (hacc : rs₂.headD 0 = ACCEPT) :
    TwinAccepts [b] := by
  have hr : rs₁.headD 0 ≠ 1 := fun e => by rw [e] at hge; simp at hge
  obtain ⟨PA, m₇, m, hF, -, hm₁, hres⟩ := checkA_run b pb sz hin 3 (Or.inr rfl) N₁ hN₁ rs₁ m₁ h₁ hr
  have hfr := parCompactMem_out m (modeFlag 3)
  rw [← hm₁] at hfr
  have hw' : ∀ a, phaseBS a = true → w.arr64 a = m.arr64 a := fun a ha => by
    rw [hw a ha, hfr.arr a (fun e => by subst e; revert ha; decide)]
  have hsz : PA.ds.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  have hk : (rs₁.headD 0 - 9223372036854775808).toNat = PA.ds.size := by
    have e : (9223372036854775808 : Word) + UInt64.ofNat PA.ds.size - 9223372036854775808 =
        UInt64.ofNat PA.ds.size := by rw [UInt64.add_comm, UInt64.add_sub_cancel]
    rw [hres, e, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  obtain ⟨s'', hB⟩ : ∃ s'', checkJobList .verified PA.ipins none PA.I PA.ds (List.range PA.ds.size)
      PA.sF.worker = .ok (.ok (), s'') := by
    simp only [L.run] at h₂
    cases e : (invoke checkerProg (exec checkerProg N₂) "check" []).run ⟨w, Locals.init []⟩ with
    | error _ => rw [e] at h₂; cases h₂
    | ok x =>
      obtain ⟨r, s⟩ := x
      rw [e] at h₂
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h₂
      obtain ⟨rfl, -⟩ := h₂
      exact M.of_run (P := fun x => x = ⟨w, Locals.init []⟩) rfl e
        (checkMode2_seq hF (jobProg_of_cd hCd PA hin.2.2.1 hF.r7.since.pbpre) N₂ hN₂ _ hk ⟨w, Locals.init []⟩ hw' hmode hlo hhi hctlf) hacc
  obtain ⟨hA, hBp, hC, hD, hE⟩ := PA.pfx
  exact ⟨PA.pins, PA.sA, PA.sB, PA.sC, PA.sD, PA.sE, PA.sF, PA.pre, PA.rc, PA.ds, PA.ipins, PA.I,
    hA, hBp, hC, hD, hE, s'', PA.idx, hB⟩

end L.Checker
