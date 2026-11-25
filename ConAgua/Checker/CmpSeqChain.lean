module

import ConAgua.Checker.JobsStart
import ConAgua.L.Blocks
import ConAgua.Checker.CmpSeqViewC
public import ConAgua.Checker.CmpSeqCheck
public import ConAgua.Checker.CmpSeqW
import ConAgua.Checker.ParDriverL
import ConAgua.Arena.IWFrame

@[expose] public section

/-!
# The sequential compared run's two phases, program-independent parts (lane compare2, the sJ variant)

* `cqSM_bytes`, `cqSM_glob`, `cqCM_bytes`, `cqCM_glob`: the switches store only to word arrays.
* `JobM.frame0`: the jobs' memory half reads no global and no byte array.
* `cq_phaseC`: after the solution's jobs (their job relation at the end `N'`, stored only to the
  flag-`0` write set, the record pool grown), mode `9`'s switch gives the challenge's jobs'
  memory half at the solution's end state.
-/

namespace L.Checker

open L L.Arena
open ConRon.Arena
open ConRon.Bridge (JobChain PExt)

local notation "V" => ConLeche.CheckMode.verified

theorem cq_set64_bytes (m : Mem) (a : TieredArray) (i v : Word) : (m.set64 a i v).bytes = m.bytes := rfl

theorem cq_set64_glob (m : Mem) (a : TieredArray) (i v : Word) : (m.set64 a i v).glob = m.glob := rfl

theorem cqMvs_bytes (l : List CqMv) (m : Mem) : (cqMvs l m).bytes = m.bytes := by
  induction l generalizing m with
  | nil => rfl
  | cons x l ih => simp only [cqMvs, List.foldl_cons] at ih ⊢; rw [ih]; rfl

theorem cqMvs_glob (l : List CqMv) (m : Mem) : (cqMvs l m).glob = m.glob := by
  induction l generalizing m with
  | nil => rfl
  | cons x l ih => simp only [cqMvs, List.foldl_cons] at ih ⊢; rw [ih]; rfl

theorem cqRowStep_bytes (c d s : ArrId) (ca k : Word) (m : Mem) :
    (cqRowStep c d s ca k m).bytes = m.bytes := by
  simp only [cqRowStep, cqRowsM, cq_set64_bytes, Mem.copy64_bytes]

theorem cqRowStep_glob (c d s : ArrId) (ca k : Word) (m : Mem) :
    (cqRowStep c d s ca k m).glob = m.glob := by
  simp only [cqRowStep, cqRowsM, cq_set64_glob, Mem.copy64_glob]

theorem cqBankSM_bytes (m : Mem) : (cqBankSM m).bytes = m.bytes := by
  simp only [cqBankSM, cqTailS, cq_set64_bytes, Mem.copy64_bytes, cqRowsS, cqRowStep_bytes]

theorem cqBankSM_glob (m : Mem) : (cqBankSM m).glob = m.glob := by
  simp only [cqBankSM, cqTailS, cq_set64_glob, Mem.copy64_glob, cqRowsS, cqRowStep_glob]

theorem cqBankCM_bytes (m : Mem) : (cqBankCM m).bytes = m.bytes := by
  simp only [cqBankCM, Mem.copy64_bytes]

theorem cqBankCM_glob (m : Mem) : (cqBankCM m).glob = m.glob := by
  simp only [cqBankCM, Mem.copy64_glob]

theorem cqSM_bytes (m : Mem) : (cqSM m).bytes = m.bytes := by
  simp only [cqSM, flushMem_bytes, cqCtlSM, cq_set64_bytes, cqMvs_bytes, cqBankSM_bytes]

theorem cqSM_glob (m : Mem) : (cqSM m).glob = m.glob := by
  simp only [cqSM, flushMem_glob, cqCtlSM, cq_set64_glob, cqMvs_glob, cqBankSM_glob]

theorem cqCM_bytes (m : Mem) : (cqCM m).bytes = m.bytes := by
  simp only [cqCM, flushMem_bytes, cqCtlCM, cqMvs_bytes, cqBankCM_bytes]

theorem cqCM_glob (m : Mem) : (cqCM m).glob = m.glob := by
  simp only [cqCM, flushMem_glob, cqCtlCM, cqMvs_glob, cqBankCM_glob]

/-- **`JobM` across a memory with the same word arrays** (`JobR.frame0`'s memory half). -/
theorem _root_.L.Arena.JobM.frame0 {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {J : Option ISolution} {I : IStreamIndex} {M M' : Mem} {a : AState}
    (h : JobM pins dn ds J I M a) (hf : MemFrame [] [] M M') : JobM pins dn ds J I M' a := by
  have hA : LoArr [] := loArr_nil
  have hC : LoCtl [] := fun _ h => absurd h (by simp)
  refine ⟨⟨ArenaR.frame_ext [] _ (by simp) (by simp) _ _ hf _ h.arena.base,
      DerR.frameM [] _ _ _ hf (by simp) _ h.arena.der⟩,
    h.core.frame (fun _ h => absurd h (by simp)) (fun _ h => absurd h (by simp)) hf,
    h.pinsR.frame (fun _ h => absurd h (by simp)) hf, h.mode.frame hf (by simp) (by simp),
    h.idx.frameLo hA hC hf, h.below.frameLo hA hC hf,
    by rw [stampW_frameLo hC hf]; exact h.stamp, declsF_frameLo hA hf h.decls, iwOK_frameLo hA hC hf h.iw,
    by rw [hC.ctl hf (by decide)]; exact h.top1, pinSetsR_frameLo hA hC hf h.pinsets,
    h.mem.frameLo hA hC hf fun k x e => h.mem.dnN k x e, by rw [pinW_frame hf (by simp)]; exact h.flag,
    h.memos.frameLo hA hC hf, h.fsize, h.frozen.frameLo hC hf, h.jsol.frameLo hA hC hf⟩

/-- A memory with `M`'s arrays and other globals. -/
theorem memFrame_glob (M : Mem) (g : GVar → Word) : MemFrame [] [] M ⟨M.bytes, M.words, g⟩ :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- **The challenge's jobs' memory half after the solution's jobs** (mode `9`'s switch): the
challenge's at the frozen memory `N` (`hC`), the solution's job relation at the end `N'` of its
jobs from mode `8`'s memory `cqSM N` (`hS`), which stored only to the flag-`0` write set and grew
the record pool: the challenge's at mode `9`'s switch of `N'` (any globals), at the solution's
end state. -/
theorem cq_phaseC {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {J : ISolution} {IS IC : IStreamIndex} {dsS dsC : Array IDeclaration} {N N' : Mem} {a9 a : AState}
    (hC : JobM pins dn dsC (some J) IC N a9) (hS : JobM pins dn dsS none IS N' a)
    (hR : CqRowsSOK N) (hT : CqTailSOK (cqRowsS N)) (hCt : CqCtlSOK (cqBankSM N))
    (hJ : MemFrame cqA cqC (cqSM N) N') (hx : ArrExt (erecP (cqSM N)) (erecP N')) (g : GVar → Word)
    (hCC : CqCtlCOK (cqBankCM ⟨N'.bytes, N'.words, g⟩)) :
    JobM pins dn dsC (some J) IC (cqCtlCM (cqBankCM ⟨N'.bytes, N'.words, g⟩)) a := by
  have hJ9 : MemFrame cqA cqC (cqSM N) ⟨N'.bytes, N'.words, g⟩ :=
    ⟨hJ.arr, hJ.ctl, hJ.size⟩
  have hS9 := hS.frame0 (memFrame_glob N' g)
  exact hS9.csBack hC (cqC_view hR hT hCt hJ9 hCC) (cqS_keep hJ9 hx (hC.jsol.walk J rfl).1)

end L.Checker
