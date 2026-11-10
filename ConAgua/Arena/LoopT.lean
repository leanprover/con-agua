module

import ConAgua.Arena.CrOKFrame
import ConAgua.Arena.IndPosSpec.FgW
public import ConAgua.Arena.RecCheckSpec.TaCW
public import ConAgua.Arena.ConstsResolveFRefine2
public import ConAgua.Arena.IndMemoFns
public import ConAgua.Arena.IndPosSpec.BvbWMfr
public import ConAgua.Arena.DeclLvlStage
public import ConAgua.Arena.IndSumSpec.McGoStep

@[expose] public section

/-!
# The jobs' memos and the twin side of the scratch bracket (lane `loopt`)

What a job (`record_job`, `Arena/Jobs.lean`) carries beside its relation: the inductive stage's
per-call memos (`StageMemos`, `IndMemos`) and the core's (`CoreMemos.zero`), each well formed on
the zeroed memory and kept across the functions that do not write them (frame lemmas, the
`IndMemoClosed` leaves); and the twin's side of the scratch bracket's opening: `TwinOK` after
`flushCaches` (`TwinOK.flush`) and after `enterScratch` from a store with the scratch tier off
(`TwinOK.enter`: every handle keeps its view and its denotation).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)

/-! ## The inductive stage's per-call memos (a memory-only clause)

The stage's walks clear their memos on entry by an epoch bump (`mclearG`), whose lemma
(`memoRV_clear`) needs *some* well-formed memo beforehand and the epoch word below `2^64 − 2`.
`StageMemos m` says that of the eight stage memos (arrays 201‥208, `CTL` 202‥219): `nest_occ`,
`depth`, `replace_apps`, `has_loose_bvar_b`, the banked `replace_fvars` (`PosMR`), `mentions_any`
(`maMR`), `mentions_const` (`mcMR`), `target_abs` (`taMR`). Only the stage
writes these words (request of lane `indproofs3`), so across the loop it is a frame fact
(`StageMemos.frame`), and it holds of the zeroed memory (`StageMemos.zero`). -/

/-- **The inductive stage's per-call memos are well formed.** (No epoch bound: a memo clear
aborts at the last epoch, so its post would not keep one; lane `indstaget`.) -/
structure StageMemos (m : Mem) : Prop where
  pos : PosMR m
  ma : ∃ mp, maMR m mp
  mc : ∃ mp, mcMR m mp
  ta : ∃ mp, taMR m mp

theorem memoRG_mfr0 {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} (hS : S.WF) {K : MemoKey κ}
    {dv : Word → ν} {m m' : Mem} (hf : MFr [] [] m m') (hb : 201 ≤ S.arr ∧ S.arr ≤ 208)
    (hx : 202 ≤ S.cs.toNat ∧ S.cs.toNat ≤ 219) {mp : Std.HashMap κ ν} (h : MemoRG S K dv m mp) :
    MemoRG S K dv m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := hf.memo S.arr S.cs hb hx (by simp) (by simp)
  exact memoRG_frame S hS K dv A C hA hC m m' f mp h

/-- **`StageMemos` across a writer outside arrays 201‥208 and `CTL` 202‥219.** -/
theorem StageMemos.frame {A : List TieredArray} {C : List Word} {m m' : Mem} (h : StageMemos m)
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b.arr < 201 ∨ 208 < b.arr)
    (hC : ∀ x ∈ C, x.toNat < 202 ∨ 219 < x.toNat) : StageMemos m' := by
  have hM : MFr [] [] m m' := MFr.of_frame hf hA hC
  obtain ⟨hp, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := h
  exact ⟨hp.fr hM, ⟨a, memoRG_mfr0 maSch_wf hM (by decide) (by decide) ha⟩,
    ⟨b, memoRG_mfr0 mcSch_wf hM (by decide) (by decide) hb⟩,
    ⟨c, memoRG_mfr0 taSch_wf hM (by decide) (by decide) hc⟩⟩

/-- A memo whose stamps are all `0` at epoch word `0` is the empty memo. -/
theorem memoRV_zeroAt {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
    (S : MemoSch) (K : MemoKey κ) (VR : Mem → Word → ν → Prop) (m : Mem)
    (hctl : S.cs.toNat + 2 ≤ (m.arr64 CTL).size) (he : rdW (m.arr64 CTL) S.cs = 0)
    (hz : ∀ j, rdW (m.arr64 S.arr) j = 0) : MemoRV S K VR m (∅ : Std.HashMap κ ν) := by
  have hep : epG S m = 1 := by simp [epG, he]
  exact memoRV_fresh S K VR m hctl (by rw [hep]; decide) (by rw [hep, hz]; decide)
    (fun j _ => by rw [hep]; simp [mstG, hz])

/-- **The zeroed memory has well-formed stage memos** (empty, epoch `0`). -/
theorem StageMemos.zero {m : Mem} (hsz : 220 ≤ (m.arr64 CTL).size)
    (hA : ∀ b : ArrId, 201 ≤ b → b ≤ 208 → ∀ j, rdW (m.arr64 b) j = 0)
    (hC : ∀ x : Word, 202 ≤ x.toNat → x.toNat ≤ 219 → rdW (m.arr64 CTL) x = 0) : StageMemos m := by
  have z : ∀ (S : MemoSch), 201 ≤ S.arr → S.arr ≤ 208 → 202 ≤ S.cs.toNat → S.cs.toNat ≤ 217 →
      ∀ {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ] (K : MemoKey κ)
        (VR : Mem → Word → ν → Prop), MemoRV S K VR m (∅ : Std.HashMap κ ν) :=
    fun S h1 h2 h3 h4 _ _ _ _ _ _ K VR =>
      memoRV_zeroAt S K VR m (by omega) (hC _ h3 (by omega)) (hA _ h1 h2)
  refine ⟨⟨⟨_, z noSch (by decide) (by decide) (by decide) (by decide) _ _⟩,
      ⟨_, z dpSch (by decide) (by decide) (by decide) (by decide) _ _⟩,
      ⟨_, z raSch (by decide) (by decide) (by decide) (by decide) _ _⟩,
      ⟨_, z hbSch (by decide) (by decide) (by decide) (by decide) _ _⟩,
      ⟨∅, 0, 0, z rfSch (by decide) (by decide) (by decide) (by decide) _ _,
        ⟨hC 218 (by decide) (by decide), hC 219 (by decide) (by decide), by decide, by decide,
          by simp; omega⟩, fun _ _ _ h => by simp at h⟩⟩,
    ⟨_, z maSch (by decide) (by decide) (by decide) (by decide) _ _⟩,
    ⟨_, z mcSch (by decide) (by decide) (by decide) (by decide) _ _⟩,
    ⟨_, z taSch (by decide) (by decide) (by decide) (by decide) _ _⟩⟩

/-! ## `consts_resolve_ffast`'s walk memo (a memory-only clause)

`consts_resolve_ffast` (lane `stubs`) memoizes in `CRM` (array 155, epoch word `CTL[158]`, size
word `CTL[159]`) and clears it on entry by an epoch bump, which needs a well-formed memo
beforehand (`L.Stubs.CrOK`, lane `tails`' `constsResolveFFast_refines`). Only that function
writes these words, so across the loop it is a frame fact (`CrOK.frame`), and it holds of the
zeroed memory (`CrOK.zero`). Request of the coordinator, for `install_value_guards`' callers. -/

/-- **The zeroed memory has a well-formed `consts_resolve_ffast` memo** (empty, epoch `0`). -/
theorem CrOK.zero {m : Mem} (hsz : 160 ≤ (m.arr64 CTL).size)
    (hA : ∀ j, rdW (m.arr64 L.Stubs.CRM) j = 0) (hC : rdW (m.arr64 CTL) 158 = 0) :
    L.Stubs.CrOK m :=
  ⟨_, memoRV_zeroAt L.Stubs.crSch bmKey L.Stubs.CrV m (by simp; omega) hC hA⟩

/-! ## The inductive arm's memos: `IndMemos` (a memory-only clause)

`check_ind_decl`'s stage clears three groups of memos on entry, each needing a well-formed memo
beforehand: the stage memos (`StageMemos`), `instantiate1Lift`'s (`I1Memo`, array 51, `CTL[52]`)
and `consts_resolve_ffast`'s (`CrOK`, array 155, `CTL[158]`). The loop carries them beside
`CoreMemos`: the inductive arm's contract (`IndArmSpec`) takes and gives them back, and the loop's
other callees keep them (`IndMemoClosed`: they write none of these words but through
`consts_resolve_ffast`, which keeps its memo, `crfF_keepsCrOK`, `IndRealCrFKeep.lean`). -/

/-- **The memos the inductive arm needs well formed at its entry.** -/
structure IndMemos (m : Mem) : Prop where
  stage : StageMemos m
  i1 : I1Memo m
  cr : L.Stubs.CrOK m

/-- **The zeroed memory has a well-formed `instantiate1Lift` memo** (empty, epoch `0`). -/
theorem I1Memo.zero {m : Mem} (hsz : 54 ≤ (m.arr64 CTL).size) (hA : ∀ j, rdW (m.arr64 ILFM) j = 0)
    (hC : rdW (m.arr64 CTL) 52 = 0) : I1Memo m :=
  ⟨_, memoRV_zeroAt ⟨51, 52⟩ lfKey _ m (by simp; omega) hC hA⟩

/-- **The zeroed memory has well-formed inductive memos.** -/
theorem IndMemos.zero {m : Mem} (hsz : 220 ≤ (m.arr64 CTL).size)
    (hA : ∀ b : ArrId, b = 51 ∨ b = 155 ∨ (201 ≤ b ∧ b ≤ 208) → ∀ j, rdW (m.arr64 b) j = 0)
    (hC : ∀ x : Word, x.toNat = 52 ∨ x.toNat = 158 ∨ (202 ≤ x.toNat ∧ x.toNat ≤ 219) →
      rdW (m.arr64 CTL) x = 0) : IndMemos m :=
  ⟨StageMemos.zero hsz (fun b h1 h2 => hA b (.inr (.inr ⟨h1, h2⟩)))
      (fun x h1 h2 => hC x (.inr (.inr ⟨h1, h2⟩))),
    I1Memo.zero (by omega) (hA 51 (.inl rfl)) (hC 52 (.inl rfl)),
    CrOK.zero (by omega) (hA _ (.inr (.inl rfl))) (hC 158 (.inr (.inl rfl)))⟩

/-- **`IndMemos` across a writer outside its arrays and `CTL` words.** -/
theorem IndMemos.frame {A : List TieredArray} {C : List Word} {m m' : Mem} (h : IndMemos m)
    (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b ≠ ILFM ∧ b ≠ Stubs.CRM ∧ (b.arr < 201 ∨ 208 < b.arr))
    (hC : ∀ x ∈ C, x.toNat ≠ 52 ∧ x.toNat ≠ 158 ∧ (x.toNat < 202 ∨ 219 < x.toNat)) :
    IndMemos m' :=
  ⟨h.stage.frame hf (fun b hb => (hA b hb).2.2) (fun x hx => (hC x hx).2.2),
    I1Memo.frame h.i1 hf (fun hb => (hA _ hb).1 rfl) (fun hx => (hC _ hx).1 rfl),
    CrOK.frame h.cr hf (fun hb => (hA _ hb).2.1 rfl) (fun hx => (hC _ hx).2.1 rfl)⟩

/-- `IndMemos` across a write of one `CTL` word outside its words. -/
theorem IndMemos.setCtl {m : Mem} (h : IndMemos m) (c v : Word)
    (hc : c.toNat ≠ 52 ∧ c.toNat ≠ 158 ∧ (c.toNat < 202 ∨ 219 < c.toNat)) :
    IndMemos (m.set64 CTL c v) :=
  h.frame (MemFrame.setCtl m c v) (by simp) (fun x hx => by simp at hx; subst hx; exact hc)

/-- **The frame relation of `IndMemoClosed`**: the inductive memos, if well formed at the start,
are at the end. -/
theorem indMemos_wframe : WFrame CTL imA imC (fun m₀ m => IndMemos m₀ → IndMemos m) where
  refl _ h := h
  st64 m₀ m a i v h ha h0 := by
    rcases ha with ⟨hc, ha⟩ | ⟨rfl, hi⟩
    · exact (h h0).frame (MemFrame.set64 m a hc i v)
        (fun b hb => by simp at hb; subst hb; exact imA_spec b ha) (by simp)
    · exact (h h0).frame (MemFrame.setCtl m i v) (by simp)
        (fun x hx => by simp at hx; subst hx; exact imC_spec x hi)
  setG _ _ _ _ h h0 := (h h0).frame (A := []) (C := [])
    ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩ (by simp) (by simp)

/-- **The leaves of `imFns` keep `IndMemos`** (`consts_resolve_ffast`, `struct_used_later`: each
writes the inductive memos only through its own memo, which it keeps; their refinements prove it). -/
def IndLeaves (p : Prog) : Prop :=
  ∀ g ∈ imLeaves, ∀ n m₀ vs, ⦃fun s => IndMemos m₀ → IndMemos s.mem⦄ invoke p (exec p n) g vs
    ⦃fun _ s => IndMemos m₀ → IndMemos s.mem; ⊤⦄

/-- **A call of a function of `imFns` keeps `IndMemos`.** -/
theorem invoke_indMemos {p : Prog} (hcl : IndMemoClosed p) (hl : IndLeaves p) (n : Nat)
    {f : FnName} (hf : f ∈ imFns) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun _ s => IndMemos s₀.mem → IndMemos s.mem; ⊤⦄ :=
  invoke_frameL p hcl indMemos_wframe hl n f hf vs s₀

/-- The same through `callW`. -/
theorem callW_indMemos {p : Prog} (hcl : IndMemoClosed p) (hl : IndLeaves p) {n : Nat}
    {f : FnName} (hf : f ∈ imFns) {vs : List Word} {m m' : Mem} {r : List Word}
    (hc : callW p n f vs m = some (r, m')) (hI : IndMemos m) : IndMemos m' := by
  obtain ⟨s', hs', h⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (invoke_indMemos hcl hl n hf vs _) hc
  exact hs' ▸ h hI

/-- **The zeroed memory has well-formed core memos** (empty, epoch `0`): what `TwinMem` needs of
the loaded memory at the loop's start (open end 5). -/
theorem CoreMemos.zero {m : Mem} (hsz : 216 ≤ (m.arr64 CTL).size)
    (hA : ∀ b : ArrId, b = 49 ∨ b = 50 ∨ b = 52 ∨ b = 53 ∨ b = 54 ∨ b = 151 ∨ b = 152 ∨ b = 153 ∨
      b = 207 → ∀ j, rdW (m.arr64 b) j = 0)
    (hC : ∀ x : Word, x = 48 ∨ x = 50 ∨ x = 54 ∨ x = 56 ∨ x = 58 ∨ x = 152 ∨ x = 154 ∨ x = 156 ∨
      x = 214 → rdW (m.arr64 CTL) x = 0) : CoreMemos m :=
  ⟨⟨_, memoRV_zeroAt coreIlSch lfKey _ m (by simp; omega) (hC _ (by simp)) (hA _ (by simp))⟩,
    ⟨_, memoRV_zeroAt coreAbSch lfKey _ m (by simp; omega) (hC _ (by simp)) (hA _ (by simp))⟩,
    ⟨⟨_, memoRV_zeroAt coreWsSch lfKey _ m (by simp; omega) (hC _ (by simp)) (hA _ (by simp))⟩,
    ⟨_, memoRV_zeroAt coreFlSch bmKey _ m (by simp; omega) (hC _ (by simp)) (hA _ (by simp))⟩,
    ⟨_, memoRV_zeroAt coreLsbSch bmKey _ m (by simp; omega) (hC _ (by simp)) (hA _ (by simp))⟩,
    ⟨_, memoRV_zeroAt coreLpSch lfKey _ m (by simp; omega) (hC _ (by simp)) (hA _ (by simp))⟩,
    ⟨_, memoRV_zeroAt coreLplSch ilKey _ m (by simp; omega) (hC _ (by simp)) (hA _ (by simp))⟩,
    ⟨_, memoRV_zeroAt coreLplsSch ilKey _ m (by simp; omega) (hC _ (by simp)) (hA _ (by simp))⟩⟩,
    ⟨_, memoRV_zeroAt L.Ind.hbSch lfKey _ m (by simp [L.Ind.hbSch]; omega) (hC _ (by simp [L.Ind.hbSch]))
      (hA _ (by simp [L.Ind.hbSch, L.Ind.HBM]))⟩⟩

/-! ## The twin's side of the bracket's opening -/

section twin
variable {dn : NIdx → Option ConLeche.Name} {fe : IFEnv}

/-- The twin state after `flushCaches`. -/
theorem flushCaches_st (a : AState) : AM.st flushCaches a = { a with caches := Caches.empty } := rfl

/-- The twin state after `enterScratch`. -/
theorem enterScratch_st (a : AState) :
    AM.st enterScratch a = { a with store := a.store.enableScratch, memos := Memos.empty } := rfl

/-- **`TwinOK` after emptying the caches** (`flushCaches`): the readback caches hold nothing. -/
theorem TwinOK.flush {m : Mem} {a : AState} (h : TwinOK dn m a fe) :
    TwinOK dn m { a with caches := Caches.empty } fe := by
  refine ⟨fun k l hk => ?_, fun k l hk => ?_, h.nwf, h.erec, h.spn, h.memos, h.bstk, ?_⟩
  · simp [Caches.empty] at hk
  · simp [Caches.empty] at hk
  · exact h.den.mono (LsExt.refl _) rfl rfl (fun k x hk => by simp [Caches.empty] at hk)
      (fun _ _ hv => hv) (fun _ _ _ hv => .inl hv) h.den.lvlAll h.den.lsAll

/-! ### Opening the scratch tier when it is off

With the scratch tier off, a well formed store's scratch tables are empty (`scrOff`), so
`enableScratch` only turns the four flags on: every handle has the view it had, and every
denotation is the one it had. -/

theorem denoteNAux_congr_view {st st' : NStore} (hv : ∀ i, st'.view i = st.view i) :
    ∀ f i, denoteNAux st' f i = denoteNAux st f i
  | 0, _ => rfl
  | f + 1, i => by
    simp only [denoteNAux, hv i]
    congr 1; funext v
    cases v <;> simp only [denoteNAux_congr_view hv f]

theorem denoteLAux_congr_view {st st' : LStore} (hv : ∀ i, st'.view i = st.view i)
    (hn : ∀ i, denoteN st'.ns i = denoteN st.ns i) :
    ∀ f i, denoteLAux st' f i = denoteLAux st f i
  | 0, _ => rfl
  | f + 1, i => by
    simp only [denoteLAux, hv i]
    congr 1; funext v
    cases v <;> simp only [denoteLAux_congr_view hv hn f, hn]

theorem denoteLList_congr {st st' : LStore} (hl : ∀ i, denoteL st' i = denoteL st i) :
    ∀ us, denoteLList st' us = denoteLList st us
  | [] => rfl
  | u :: us => by simp only [denoteLList, hl u, denoteLList_congr hl us]

/-- The four stores' views and node counts after `enableScratch`, from a store with the scratch
tier off and well formed. -/
theorem enable_views {st : EStore} (hwf : StoreWF st) (hoff : st.scratchOn = false) :
    (∀ i, st.enableScratch.view i = st.view i) ∧
    (∀ i, st.enableScratch.lss.view i = st.lss.view i) ∧
    (∀ i, st.enableScratch.ls.view i = st.ls.view i) ∧
    (∀ i, st.enableScratch.ns.view i = st.ns.view i) ∧
    st.enableScratch.ls.nodeCount = st.ls.nodeCount ∧
    st.enableScratch.ns.nodeCount = st.ns.nodeCount := by
  obtain ⟨rk, hw⟩ := hwf
  have hLs : LsWF st.lss := hw.lss
  obtain ⟨rkl, hL⟩ := hLs.ls
  obtain ⟨rkn, hN⟩ := hL.ns
  have o1 : st.lss.scratchOn = false := by rw [← hw.sync]; exact hoff
  have o2 : st.lss.ls.scratchOn = false := by rw [← hLs.sync]; exact o1
  have o3 : st.lss.ls.ns.scratchOn = false := by rw [← hL.sync]; exact o2
  have sE := hw.scrOff hoff
  have sLs := hLs.scrOff o1
  have sL := hL.scrOff o2
  have sN := hN.scrOff o3
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · simp only [EStore.view, EStore.enableScratch, hoff]
    split <;> simp [ETables.get_empty]
  · simp only [EStore.enableScratch, LsStore.view, LsStore.enableScratch, o1]
    split <;> simp [LsTables.get_empty]
  · simp only [EStore.ls, EStore.enableScratch, LsStore.enableScratch, LStore.view,
      LStore.enableScratch, o2]
    split <;> simp [LTables.get_empty]
  · simp only [EStore.ns, EStore.enableScratch, LsStore.enableScratch, LStore.enableScratch,
      NStore.view, NStore.enableScratch, o3]
    split <;> simp [NTables.get_empty]
  · simp only [EStore.ls, EStore.enableScratch, LsStore.enableScratch, LStore.enableScratch,
      LStore.nodeCount, LStore.persCount, LStore.scrCount, sL]
  · simp only [EStore.ns, EStore.enableScratch, LsStore.enableScratch, LStore.enableScratch,
      NStore.enableScratch, NStore.nodeCount, NStore.persCount, NStore.scrCount, sN]

/-- **Opening the scratch tier when it is off changes no denotation.** -/
theorem enable_denote {st : EStore} (hwf : StoreWF st) (hoff : st.scratchOn = false) :
    (∀ i, denoteN st.enableScratch.ns i = denoteN st.ns i) ∧
    (∀ i, denoteL st.enableScratch.ls i = denoteL st.ls i) ∧
    (∀ i, denoteLs st.enableScratch.lss i = denoteLs st.lss i) := by
  obtain ⟨-, hvs, hvl, hvn, hcl, hcn⟩ := enable_views hwf hoff
  have hN : ∀ i, denoteN st.enableScratch.ns i = denoteN st.ns i := fun i => by
    simp only [denoteN, hcn]; exact denoteNAux_congr_view hvn _ i
  have hL : ∀ i, denoteL st.enableScratch.ls i = denoteL st.ls i := fun i => by
    simp only [denoteL, hcl]; exact denoteLAux_congr_view hvl hN _ i
  refine ⟨hN, hL, fun i => ?_⟩
  simp only [denoteLs, hvs i]
  cases st.lss.view i with
  | none => rfl
  | some us => exact denoteLList_congr hL us

/-- **`TwinOK` after `enterScratch`** at a state whose store is well formed with the scratch tier
off (the loop head's: `TwinFold.stateOK`, and the last `dropScratch` turned it off). -/
theorem TwinOK.enter {m : Mem} {a : AState} (h : TwinOK dn m a fe) (hwf : StoreWF a.store)
    (hoff : a.store.scratchOn = false) :
    TwinOK dn m { a with store := a.store.enableScratch, memos := Memos.empty } fe := by
  obtain ⟨hvE, hvs, hvl, -, -, -⟩ := enable_views hwf hoff
  obtain ⟨hN, hL, hLs⟩ := enable_denote hwf hoff
  have hx : LsExt a.store.lss a.store.enableScratch.lss :=
    { ls := { ns := fun i x hd => by
                show denoteN a.store.enableScratch.ns i = some x
                rw [hN]; exact hd
              lvl := fun i x hd => by
                show denoteL a.store.enableScratch.ls i = some x
                rw [hL]; exact hd }
      lst := fun i x hd => by rw [hLs]; exact hd }
  refine ⟨fun k l hk => ?_, fun k l hk => ?_, ?_, h.erec, h.spn, h.memos, h.bstk, ?_⟩
  · show denoteL a.store.enableScratch.ls k = some l
    rw [hL]; exact h.readL k l hk
  · show denoteLs a.store.enableScratch.lss k = some l
    rw [hLs]; exact h.readLs k l hk
  · obtain ⟨rk, hn⟩ := h.nwf
    exact ⟨rk, NStore.enableScratch_wfAt hn⟩
  · refine h.den.mono hx rfl rfl (fun k x hk => .inl hk)
      (fun x u hv => by rw [← hvE x]; exact hv) (fun x c us hv => .inl (by rw [← hvE x]; exact hv))
      (fun u hu => ?_) (fun u hu => ?_)
    · have hu' : (a.store.ls.view u).isSome := by
        rw [← hvl u]; exact hu
      obtain ⟨l, hl⟩ := h.den.lvlAll u hu'
      exact ⟨l, by show denoteL a.store.enableScratch.ls u = some l; rw [hL]; exact hl⟩
    · have hu' : (a.store.lss.view u).isSome := by
        rw [← hvs u]; exact hu
      obtain ⟨l, hl⟩ := h.den.lsAll u hu'
      exact ⟨l, by show denoteLs a.store.enableScratch.lss u = some l; rw [hLs]; exact hl⟩

end twin

end L.Arena
