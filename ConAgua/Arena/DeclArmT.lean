module

import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Checker.Base
import all ConRon.Bridge.Checker.Inv
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.DeclStep
import ConAgua.Arena.TwinStep
public import ConAgua.Arena.IndTwin
public import ConAgua.Arena.DeclRec

@[expose] public section

/-!
# The declaration arms under `StageT` (lane `loopt2`)

`DeclArm*.lean`'s arms run from the stage relation, the core's entry points read through their
stubs. Here they run from `StageT`, reading the program's own calls (`realCall p`), through the
`StageT` versions of the value checks (`DeclValT.lean`). An arm's post is the stage relation at its
environment and the core's memos well formed (`CoreMemos`): after an arm no core call follows in
the step, and the loop re-derives the twin's invariants at the next declaration.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


noncomputable section

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)

local notation "V" => ConLeche.CheckMode.verified

/-- **`erec_ci` writes the record pool and its top** (`EREC`, `CTL[129]`). -/
theorem erecCiW_frame {n : Nat} {m m' : Mem} {i k : Word} {r : List Word}
    (h : erecCiW n m i k = some (r, m')) : MemFrame [EREC, tier1 EREC] [129, 130] m m' := by
  cases n with
  | zero => simp [erecCiW] at h
  | succ n =>
  rw [erecCiW_step] at h
  cases h1 : erAllocW m (rdW (m.arr64 DECL) (4 + 8 * i)) with
  | none => rw [h1] at h; cases h
  | some x =>
  obtain ⟨s, m1⟩ := x
  rw [h1, eciK1_some] at h
  cases h2 : dlpCopyW n m1 s (1 + rdW (m.arr64 DECL) (3 + 8 * i)) (rdW (m.arr64 DECL) (4 + 8 * i)) with
  | none => rw [h2] at h; cases h
  | some m2 =>
  rw [h2, eciK2_some] at h
  cases h3 : erAllocW m2 8 with
  | none => rw [h3] at h; cases h
  | some x =>
  obtain ⟨p, m3⟩ := x
  rw [h3, eciK3_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have fA : ∀ {m m1 : Mem} {k q : Word}, erAllocW m k = some (q, m1) →
      MemFrame [EREC, tier1 EREC] [129, 130] m m1 := fun {m m1 k q} hh => by
    rw [erAllocW_mem hh]
    refine ⟨fun b _ hc => ?_, fun x hx => ?_, fun b => ?_⟩
    · unfold erAllocMem; split <;> exact Mem.arr64_set64_ne _ _ _ _ _ hc
    · unfold erAllocMem; split <;> simp only [rdW_set64] <;> grind
    · unfold erAllocMem; split <;> simp [Mem.size64_set64]
  have fW : ∀ (m : Mem) (q : Word) (ws : List Word), MemFrame [EREC, tier1 EREC] [129, 130] m (wrER m q ws) :=
    fun m q ws => (wrER_frame ws m q).mono (fun _ h => h) (fun _ h => by simp at h)
  rw [dlpCopyW_eq _ _ _ _ _ _ h2] at h3
  exact (((fA h1).trans (fW _ _ _)).trans (fA h3)).trans (by rw [eciMem_eq]; exact fW _ _ _)

/-- `StageT` across `erec_ci` (an `EREC` writer: `TwinOK.frame`). -/
theorem erecCiW_okT {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {i ck : Word} {r : List Word} {ds : Array IDeclaration}
    {ci : IConstantInfo}
    (h : erecCiW n m i ck = some (r, m')) (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hci : stepCI ck.toNat ds[i.toNat] = some ci) :
    StageT dn vis fe m' a ∧ IWGrow m m' ∧ decCI (erecP m') (r.headD 0).toNat = some ci ∧
      decCV (erecP m') ((r.headD 0).toNat + 1) = some (stepCV ds[i.toNat]) ∧
      hd? (erecP m') ((r.headD 0).toNat + 5) = some (stepVal ds[i.toNat]) ∧
      erOff (r.headD 0) + 8 ≤ erTopOf m' (r.headD 0) := by
  obtain ⟨hS', hg, h1, h2, h3, h4⟩ := erecCiW_ok h hS.stage hD hi hci
  have hf := erecCiW_frame h
  refine ⟨⟨hS', hS.twin.frame hf ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩,
    by simp only [pinW, hf.arr PINS (by decide) (by decide)]; exact hS.flag⟩, hg, h1, h2, h3, h4⟩

end L.Arena
