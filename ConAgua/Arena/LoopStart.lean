import ConAgua.Arena.CheckerT

/-!
# The declaration loop's start (lane `loopt3`)

What `installThenCheck_refines` (`CheckerT.lean`) takes of the memory at the loop's start, from
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
    (132 ≤ b ∧ b ≤ 134) ∨ (146 ≤ b ∧ b ≤ 149) ∨ b = 155 ∨ (201 ≤ b ∧ b ≤ 208) ∨ b = 51

/-- The `CTL` words the loop needs zero at its start: the core's memo stamps, the number of
constants (128), of pending checks (130), the promotion memo's words (140‥147),
`consts_resolve_ffast`'s stamp (158), the inductive stage's memo words (202‥219),
`instantiate1Lift`'s stamp (52). -/
def loopZeroCtl (x : Nat) : Prop :=
  x = 48 ∨ x = 50 ∨ x = 54 ∨ x = 56 ∨ x = 58 ∨ x = 152 ∨ x = 154 ∨ x = 156 ∨ x = 158 ∨
    x = 128 ∨ x = 130 ∨ (140 ≤ x ∧ x ≤ 147) ∨ (202 ≤ x ∧ x ≤ 219) ∨ x = 52

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
theorem lzc_stage {x : Nat} (h1 : 202 ≤ x) (h2 : x ≤ 219) : loopZeroCtl x :=
  .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨h1, h2⟩

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

theorem stageMemos : StageMemos m :=
  StageMemos.zero h.ctl (fun b h1 h2 j => h.arr b (lz_stage h1 h2) j)
    (fun x h1 h2 => h.word x (lzc_stage h1 h2))

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
  ⟨by simp [pendCount, h.word 130 (by unfold loopZeroCtl; decide)], fun j hj => by simp at hj⟩

theorem envR (dn : NIdx → Option ConLeche.Name) : EnvR dn m 0 (mkIFEnv IEnv.empty) := by
  have hrow : ∀ w : Word, rowTag w ≤ 2 → rowC m w = 0 := by
    intro w hw
    simp only [rowC, if_pos hw]
    have h1 : 132 ≤ 132 + rowTag w := by omega
    have h2 : 132 + rowTag w ≤ 134 := by omega
    have hz := h.arr (132 + rowTag w) (lz_row h1 h2) (UInt64.ofNat (rowIx w))
    have hlt : rowIx w < 2 ^ 64 := by unfold rowIx; omega
    simpa [rdW, Nat.mod_eq_of_lt hlt] using hz
  refine ⟨by rfl, fun n hn => ?_, fun n hn hc => absurd (hrow _ hn) hc, ?_⟩
  · simp [rowW, hrow _ hn, mkIFEnv, mkIFEnvGo, IEnv.empty]
  · simp [envConsts, envLen, h.word 128 (by unfold loopZeroCtl; decide), mkIFEnv, IEnv.empty]

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
    (hB : (m.arr64 145).size < 2 ^ 63) :
    LoopR pins (dnOf a.store) m a 0 (mkIFEnv IEnv.empty) #[] ds ∧
      LoopMem (dnOf a.store) m a ∧ CoreMemos m ∧ IndMemos m :=
  ⟨⟨⟨hA, hcore, ⟨fun _ => hpf⟩, hz.envR _⟩, hz.pendR, hD, hiw, ⟨_, hz.pmemo⟩, hPS⟩,
    ⟨hE, hS, hB, hpin, fun k x h => by
      simp only [dnOf] at h
      split at h
      · exact ⟨by assumption, h⟩
      · cases h⟩, hz.coreMemos, hz.indMemos⟩


/-- The lookups `installThenCheck_refines` takes beyond `LoopCallees`, and the bracket. -/
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
  itc : p.lookup "install_then_check" = some installThenCheckL

/-- **The declaration loop from its start**: from the memory facts the stages before it leave
and the twin's fold invariant at its start state `a`, a returning `install_then_check` means the
twin's sequential fold accepts (phase A, then phase B on the phase-A state's worker). The name
decoder is the start store's (`dnOf`). -/
theorem installThenCheck_start {p : Prog} {pins : List INatOpPinSet} {ds : Array IDeclaration}
    {a : AState} (hP : LoopTopProg p) (hdc : LoopCallees (dnOf a.store) p) (hFD : FrontDecls ds)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (hT : TwinFold pins ds (mkIFEnv IEnv.empty) #[] a)
    (hA : ArenaD s₀.mem a) (hcore : CoreR s₀.mem a.caches) (hpf : PinsFull s₀.mem a.pins)
    (hD : DeclsF (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) ds) (hPS : L.Rom.PinSetsR s₀.mem pins)
    (hiw : L.Ind.IWOK s₀.mem) (hz : LoopZero s₀.mem) (hpin : pinW s₀.mem 0 ≠ 0)
    (hE : (s₀.mem.arr64 EREC).size < 2 ^ 63) (hS : (s₀.mem.arr64 SPN).size < 2 ^ 63)
    (hB : (s₀.mem.arr64 145).size < 2 ^ 63) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_then_check" []
    ⦃fun _ s' => LocEq s' s₀ ∧ ∃ (k : Nat) (fe : IFEnv) (pend : Array PendingCheck) (a' s'' : AState),
      installFold .verified pins (0, mkIFEnv IEnv.empty, #[]) ds.toList a = .ok (.ok (k, fe, pend), a') ∧
      checkPendingList .verified fe pend.toList a'.worker = .ok (.ok (), s''); ⊤⦄ := by
  obtain ⟨hR, hM, hc, hIM⟩ := loop_start (pins := pins) hA hcore hpf hD hPS hiw hz hpin hE hS hB
  exact installThenCheck_refines .verified pins (dnOf a.store) ds p rfl hP.bracket hdc hFD
    (declsLpsDn_dnOf hT.pd hT.den) hP.pp
    hP.pn hP.ps hP.pi hP.pd hP.pg hP.px hP.pc hP.pcg hP.pcx hP.itc n hn s₀ a hT hR hM hc hIM

end L.Arena
