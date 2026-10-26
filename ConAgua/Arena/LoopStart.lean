import ConAgua.Arena.CheckerT

/-!
# The declaration loop's start (lane `loopt3`)

What phase A's fold (`installFoldGo_refines`, `CheckerT.lean`; `installFoldGo_start`,
`PhaseAEntry.lean`) takes of the memory at the loop's start, from
the facts the stages before it leave (lane `pipeline`'s `R7`): the loop's relation `LoopR` at the
empty environment with no pending checks, the memory's half of the twin's invariants (`LoopMem`)
and the core's memos (`CoreMemos`). The loop's memos, the environment's index rows, the pending
count and the promotion memo are the loaded memory's zeros, which no stage before the loop writes
(`LoopZero`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.deprecated false

namespace L.Arena

open L.Front (DECL DLP DeclsF)

/-- The arrays the loop needs zero at its start: the core's memos (49, 50, 52‥54, 151‥153), the
environment's index rows (132‥134), the promotion memo (146‥149), `consts_resolve_ffast`'s memo
(155), the inductive stage's memos (201‥208), `instantiate1Lift`'s memo (51). -/
def loopZeroArr (b : Nat) : Prop :=
  b = 49 ∨ b = 50 ∨ b = 52 ∨ b = 53 ∨ b = 54 ∨ b = 151 ∨ b = 152 ∨ b = 153 ∨
    (132 ≤ b ∧ b ≤ 134) ∨ (146 ≤ b ∧ b ≤ 149) ∨ b = 155 ∨ (201 ≤ b ∧ b ≤ 208) ∨ b = 51 ∨
    (140 ≤ b ∧ b ≤ 142) ∨ (129 ≤ b ∧ b ≤ 131) ∨ (385 ≤ b ∧ b ≤ 387)

/-- The `CTL` words the loop needs zero at its start: the core's memo stamps, the number of
constants (128), of pending checks (130), the promotion memo's words (140‥147),
`consts_resolve_ffast`'s stamp (158), the inductive stage's memo words (202‥219),
`instantiate1Lift`'s stamp (52). -/
def loopZeroCtl (x : Nat) : Prop :=
  x = 48 ∨ x = 50 ∨ x = 54 ∨ x = 56 ∨ x = 58 ∨ x = 152 ∨ x = 154 ∨ x = 156 ∨ x = 158 ∨
    x = 128 ∨ x = 130 ∨ (140 ≤ x ∧ x ≤ 147) ∨ (202 ≤ x ∧ x ≤ 219) ∨ x = 52 ∨ x = 133

/-- **The zeros the loop starts from.** -/
structure LoopZero (m : Mem) : Prop where
  ctl : 220 ≤ (m.arr64 CTL).size
  arr : ∀ b, loopZeroArr b → ∀ j, rdW (m.arr64 b) j = 0
  word : ∀ x : Word, loopZeroCtl x.toNat → rdW (m.arr64 CTL) x = 0

theorem lz_row {b : ArrId} (h1 : 132 ≤ b) (h2 : b ≤ 134) : loopZeroArr b :=
  .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨h1, h2⟩
theorem lz_stage {b : ArrId} (h1 : 201 ≤ b) (h2 : b ≤ 208) : loopZeroArr b :=
  .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨h1, h2⟩
theorem lzc_pm {x : Nat} (h1 : 140 ≤ x) (h2 : x ≤ 147) : loopZeroCtl x :=
  .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨h1, h2⟩

namespace LoopZero
variable {m : Mem} (h : LoopZero m)
include h

theorem coreMemos : CoreMemos m :=
  CoreMemos.zero (by have := h.ctl; omega)
    (fun b hb j => h.arr b (by
      rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [loopZeroArr]) j)
    (fun x hx => h.word x (by
      unfold loopZeroCtl
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide))

theorem crOK : L.Stubs.CrOK m :=
  CrOK.zero (by have := h.ctl; omega) (fun j => h.arr _ (by unfold loopZeroArr; decide) j)
    (h.word 158 (by unfold loopZeroCtl; decide))

theorem indMemos : IndMemos m :=
  IndMemos.zero h.ctl (fun b hb j => h.arr b (by
      rcases hb with rfl | rfl | ⟨h1, h2⟩
      · unfold loopZeroArr; decide
      · unfold loopZeroArr; decide
      · exact lz_stage h1 h2) j)
    (fun x hx => h.word x (by unfold loopZeroCtl; omega))

theorem pmemo : PMemoR m PMemo.empty := by
  have hc : ∀ x : Word, 140 ≤ x.toNat → x.toNat ≤ 147 → rdW (m.arr64 CTL) x = 0 :=
    fun x h1 h2 => h.word x (lzc_pm h1 h2)
  have hs := h.ctl
  exact ⟨memoRV_zeroAt _ _ _ m (by simp; omega) (hc _ (by decide) (by decide))
      (h.arr _ (by unfold loopZeroArr; decide)),
    memoRV_zeroAt _ _ _ m (by simp; omega) (hc _ (by decide) (by decide))
      (h.arr _ (by unfold loopZeroArr; decide)),
    memoRV_zeroAt _ _ _ m (by simp; omega) (hc _ (by decide) (by decide))
      (h.arr _ (by unfold loopZeroArr; decide)),
    memoRV_zeroAt _ _ _ m (by simp; omega) (hc _ (by decide) (by decide))
      (h.arr _ (by unfold loopZeroArr; decide))⟩

theorem pendR : PendR m #[] :=
  ⟨by simp [pendCount, h.word 130 (by unfold loopZeroCtl; decide)], fun j hj => by simp at hj,
    by simp [pendCount, h.word 130 (by unfold loopZeroCtl; decide)]⟩

theorem envR (dn : NIdx → Option ConLeche.Name) : EnvR dn m 0 (mkIFEnv IEnv.empty) := by
  have hrow : ∀ w : Word, rowTag w ≤ 2 → rowC m w = 0 := by
    intro w hw
    simp only [rowC, if_pos hw]
    have htr : rowTier w < 2 := Nat.mod_lt _ (by decide)
    have hl : loopZeroArr (rowArr w) := by
      simp only [loopZeroArr, rowArr]
      rcases (by omega : rowTier w = 0 ∨ rowTier w = 1) with h0 | h0 <;> simp only [h0] <;> omega
    have hz := h.arr (rowArr w) hl (UInt64.ofNat (rowIx w))
    have hlt : rowIx w < 2 ^ 64 := by unfold rowIx; omega
    simpa [rdW, Nat.mod_eq_of_lt hlt] using hz
  have htrow : ∀ w : Word, tblRow m w = 0 := by
    intro w
    unfold tblRow
    split
    · rename_i hw
      have htr : rowTier w < 2 := Nat.mod_lt _ (by decide)
      have hl : loopZeroArr (tblArr w) := by
        simp only [loopZeroArr, tblArr]
        rcases (by omega : rowTier w = 0 ∨ rowTier w = 1) with h0 | h0 <;> simp only [h0] <;> omega
      have hz := h.arr (tblArr w) hl (UInt64.ofNat (tblIx w))
      have hlt : tblIx w < 2 ^ 64 := by unfold tblIx; omega
      simpa [rdW, Nat.mod_eq_of_lt hlt] using hz
    · rfl
  exact EnvR.init (fun w => by
      by_cases hw : rowTag w ≤ 2
      · exact hrow w hw
      · simp [rowC, hw])
    (h.word 128 (by unfold loopZeroCtl; decide)) htrow (h.word 133 (by unfold loopZeroCtl; decide))

end LoopZero

/-- **The record pool's name decoder at the loop's start**: the start store's persistent names
(the startup interned them with the scratch tier off; the loop's steps only grow the persistent
tier, `LoopMem.dnP`). -/
def dnOf (st : EStore) (k : NIdx) : Option ConLeche.Name :=
  if k.isPersistent then denoteN st.ns k else none

theorem dnOf_inj {st : EStore} (hwf : StoreWF st) : L.Ind.DnInj (dnOf st) := by
  intro x y n hx hy
  obtain ⟨rk, hw⟩ := hwf
  simp only [dnOf] at hx hy
  split at hx
  · split at hy
    · exact ConRon.Arena.denoteN_inj hw.nsWF hx hy
    · cases hy
  · cases hx

theorem denoteNList_mem_some {st : NStore} :
    ∀ {hs : List NIdx} {xs : List ConLeche.Name}, Frontend.denoteNList st hs = some xs →
      ∀ k ∈ hs, (denoteN st k).isSome
  | [], _, _, k, hk => absurd hk (by simp)
  | h :: hs, xs, hd, k, hk => by
    simp only [Frontend.denoteNList] at hd
    cases h1 : denoteN st h with
    | none => rw [h1] at hd; simp at hd
    | some x =>
      cases h2 : Frontend.denoteNList st hs with
      | none => rw [h1, h2] at hd; simp at hd
      | some ys =>
        rcases List.mem_cons.mp hk with rfl | hk
        · simp [h1]
        · exact denoteNList_mem_some h2 k hk

theorem denoteCIList_mem_some {st : EStore} :
    ∀ {cs : List IConstantInfo} {xs : List ConLeche.ConstantInfo},
      Frontend.denoteCIList st cs = some xs → ∀ c ∈ cs, ∃ y, Frontend.denoteCI st c = some y
  | [], _, _, c, hc => absurd hc (by simp)
  | c' :: cs, xs, hd, c, hc => by
    simp only [Frontend.denoteCIList] at hd
    cases h1 : Frontend.denoteCI st c' with
    | none => rw [h1] at hd; simp at hd
    | some x =>
      cases h2 : Frontend.denoteCIList st cs with
      | none => rw [h1, h2] at hd; simp at hd
      | some ys =>
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨x, h1⟩
        · exact denoteCIList_mem_some h2 c hc

/-- **The records' level-parameter handles have names under the start decoder**: every handle of
a denoting persistent record is persistent with a `denoteN` name, which `dnOf` keeps. -/
theorem declsLpsDn_dnOf {st : EStore} {ds : Array IDeclaration}
    (hpd : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x)
    (hden : ∃ dsP, ConRon.Bridge.denoteDecls st ds.toList = some dsP) :
    DeclsLpsDn (dnOf st) ds := by
  intro i hi b nP hd cv caps hmem k hk
  obtain ⟨dsP, hD⟩ := hden
  have hm : ds[i] ∈ ds.toList := by simp
  obtain ⟨x, hx⟩ := ConRon.Bridge.denoteDecl_of_mem hD _ hm
  have hp := hpd _ hm
  rw [hd] at hx hp
  simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
  obtain ⟨bs, hbs, -⟩ := hx
  obtain ⟨y, hy⟩ := denoteCIList_mem_some hbs _ hmem
  have hpk : k.isPersistent = true := (hp _ hmem).1.levelParams k hk
  simp only [Frontend.denoteCI] at hy
  cases h1 : Frontend.denoteCV st cv with
  | none => rw [h1] at hy; simp at hy
  | some v =>
  simp only [Frontend.denoteCV] at h1
  cases h2 : Frontend.denoteNList st.ns cv.levelParams with
  | none => rw [h2] at h1; split at h1 <;> simp_all
  | some lps =>
  simp only [dnOf, hpk, if_true]
  exact denoteNList_mem_some h2 k hk

/-- **The loop's relation and the memory's halves at the loop's start**, at the empty environment
with no pending checks. -/
theorem loop_start {pins : List INatOpPinSet} {ds : Array IDeclaration} {m : Mem} {a : AState}
    (hA : ArenaD m a) (hcore : CoreR m a.caches) (hpf : PinsFull m a.pins)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hPS : L.Rom.PinSetsR m pins)
    (hiw : L.Ind.IWOK m) (hz : LoopZero m) (hpin : pinW m 0 ≠ 0)
    (hE : (m.arr64 EREC).size < 2 ^ 63) (hS : (m.arr64 SPN).size < 2 ^ 63)
    (hB : (m.arr64 145).size < 2 ^ 63) (hmode : ModeOK m) :
    LoopR pins (dnOf a.store) m a 0 (mkIFEnv IEnv.empty) #[] ds ∧
      LoopMem (dnOf a.store) m a ∧ CoreMemos m ∧ IndMemos m :=
  ⟨⟨⟨hA, hcore, ⟨fun _ => hpf⟩, hz.envR _, hmode⟩, hz.pendR, hD, hiw, ⟨_, hz.pmemo⟩, hPS⟩,
    ⟨hE, hS, hB, hpin, fun k x h => by
      simp only [dnOf] at h
      split at h
      · exact ⟨by assumption, h⟩
      · cases h⟩, hz.coreMemos, hz.indMemos⟩

/-- The lookups the loop's two phases take beyond `LoopCallees` (`installFoldGo_start`,
`PhaseAEntry.lean`; phase B's `PhaseBProg`), and the bracket. -/
structure LoopTopProg (p : Prog) : Prop where
  bracket : BracketProg p
  pp : p.lookup "pend_push" = some pendPushL
  pn : p.lookup "is_none" = some isNoneL
  ps : p.lookup "is_some" = some isSomeL
  pi : p.lookup "install_step" = some installStepL
  pd : p.lookup "install_decl_step" = some installDeclStepL
  pg : p.lookup "install_fold_go" = some installFoldGoL
  px : p.lookup "install_fold_next" = some installFoldNextL
  pc : p.lookup "check_pending" = some checkPendingL
  pcg : p.lookup "check_pending_go" = some checkPendingGoL
  pcx : p.lookup "check_pending_next" = some checkPendingNextL

end L.Arena
