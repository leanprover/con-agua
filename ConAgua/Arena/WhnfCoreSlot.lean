import ConAgua.Arena.WhnfCore
import ConAgua.Arena.CoreRefine
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The knot's `whnfCore` slot: stuck tags, the memo, the body

`whnf_core(mode, cheap, vis, d, e)` (`WhnfCore.lean`) refines the `whnfCore` slot of
`coreKnot mode fe id (F + 1)`: a stuck tag answers `e` without touching memo or store
(`whnfCoreStuckTag`, `stuck_iff`), a memo hit (`whnfCoreCheapC` in the cheap mode, `whnfCoreC`
otherwise, at the current generation) answers the entry, a miss runs `whnf_core_loop` (the
body, `whnfCoreBody … (coreKnot … F)`), records it and answers it.

The proof is the pattern for every core function that calls another: a word-level model
(`whnfCoreW`) whose callee is `callW` (the callee's run, `WhnfBase.lean`), the L spec by
`vcgen` + `finish` with `callW_spec`, then the refinement with the callee's own spec applied to
that run (`CoreSpec.of_callW`) and the memo lemmas of `CoreRefine.lean`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Tags -/

theorem toUInt32_beq (a b : Word) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (a.toUInt32 == b.toUInt32) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false]
    apply Bool.eq_false_iff.mpr
    intro hb'
    apply h
    have := congrArg UInt32.toNat (eq_of_beq hb')
    rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact UInt64.toNat_inj.mp this

theorem shr28_lt (e : Word) (he : HW e) : (e >>> 28).toNat < 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]; unfold HW at he; omega

/-- `whnfCoreStuckTag` off the handle word. -/
theorem stuck_iff (e : Word) (he : HW e) :
    whnfCoreStuckTag (decE e) =
      decide (e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0) := by
  have h := shr28_lt e he
  simp only [whnfCoreStuckTag, decE_tag e he, ETag.app, ETag.proj, ETag.letE, ETag.bvar]
  rw [show (4 : UInt32) = (4 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (9 : UInt32) = (9 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (7 : UInt32) = (7 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (0 : UInt32) = (0 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  by_cases h4 : e >>> 28 = 4 <;> by_cases h9 : e >>> 28 = 9 <;> by_cases h7 : e >>> 28 = 7 <;>
    by_cases h0 : e >>> 28 = 0 <;> simp_all

/-! ## The model -/

/-- A mode memo around a body: probe at the second key word `k` (the mode's eager bit), answer a
hit, else take the body's run `res`, probe again on its memory, record, answer. -/
def memoSlotW (S : MemoSch) (m : Mem) (e k : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  if mfindG S m e k = [] then none
  else if (mfindG S m e k).headD 0 ≠ 0 then some (mvG S m ((mfindG S m e k).tail.headD 0), m)
  else match res with
    | none => none
    | some (r, m₁) =>
      match msetG S m₁ e k (r.headD 0) with
      | none => none
      | some m₂ => some (r.headD 0, m₂)

/-- The second key word of a one-handle mode memo at the mode's eager bit. -/
def ebKey (mode : Word) : Word := ((mode >>> 1) &&& 1) <<< 32

/-- **The model of `whnf_core`**, the loop through its run. -/
def whnfCoreW (p : Prog) (n : Nat) (m : Mem) (mode cheap vis d e : Word) : Option (Word × Mem) :=
  if e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0 then some (e, m)
  else if cheap ≠ 0 then
    memoSlotW wkSch m e (ebKey mode) (callW p n "whnf_core_loop" [mode, 1, vis, d, e] m)
  else memoSlotW wcSch m e (ebKey mode) (callW p n "whnf_core_loop" [mode, 0, vis, d, e] m)

section arms
variable (S : MemoSch) (m m₁ m₂ : Mem) (e k : Word) (r : List Word)

theorem memoSlotW_hit (res : Option (List Word × Mem)) (h0 : mfindG S m e k ≠ [])
    (h1 : (mfindG S m e k).headD 0 ≠ 0) :
    memoSlotW S m e k res = some (mvG S m ((mfindG S m e k).tail.headD 0), m) := by
  unfold memoSlotW; rw [ite_eq_right h0, ite_eq_left h1]

theorem memoSlotW_miss (h0 : mfindG S m e k ≠ []) (h1 : (mfindG S m e k).headD 0 = 0)
    (h2 : msetG S m₁ e k (r.headD 0) = some m₂) :
    memoSlotW S m e k (some (r, m₁)) = some (r.headD 0, m₂) := by
  unfold memoSlotW
  rw [ite_eq_right h0, ite_eq_right (by simp only [ne_eq, Decidable.not_not]; exact h1)]
  simp only [h2]

end arms

theorem whnfCoreW_stuck (p : Prog) (n : Nat) (m : Mem) (mode cheap vis d e : Word)
    (h : e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0) :
    whnfCoreW p n m mode cheap vis d e = some (e, m) := by
  unfold whnfCoreW; rw [ite_eq_left h]

theorem whnfCoreW_cheap (p : Prog) (n : Nat) (m : Mem) (mode cheap vis d e : Word)
    (h : ¬ (e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0)) (hc : cheap ≠ 0) :
    whnfCoreW p n m mode cheap vis d e =
      memoSlotW wkSch m e (ebKey mode) (callW p n "whnf_core_loop" [mode, 1, vis, d, e] m) := by
  unfold whnfCoreW; rw [ite_eq_right h, ite_eq_left hc]

theorem whnfCoreW_full (p : Prog) (n : Nat) (m : Mem) (mode cheap vis d e : Word)
    (h : ¬ (e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0)) (hc : cheap = 0) :
    whnfCoreW p n m mode cheap vis d e =
      memoSlotW wcSch m e (ebKey mode) (callW p n "whnf_core_loop" [mode, 0, vis, d, e] m) := by
  unfold whnfCoreW; rw [ite_eq_right h, ite_eq_right (by simpa using hc)]

/-! ## The L spec -/

section spec
variable (p : Prog) (hp : WhnfCoreProg p)

include hp in
theorem whnfCore_spec (n : Nat) (s₀ : St) (mode cheap vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf_core" [mode, cheap, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ whnfCoreW p n s₀.mem mode cheap vis d e = some (r.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp.core]
  simp only [callFn, whnfCoreL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec wkSch p _ hp.wkf n, memoPutG_spec wkSch p _ hp.wkp n,
      memoFindG_spec wcSch p _ hp.wcf n, memoPutG_spec wcSch p _ hp.wcp n,
      callW_spec p n "whnf_core_loop"] <;>
    finish [whnfCoreW_stuck, whnfCoreW_cheap, whnfCoreW_full, memoSlotW_hit, memoSlotW_miss, mvG, ebKey]

end spec

/-! ## The relation across a mode memo's `find; put` -/

theorem genW_zero' (g : Word) : genW 0 g = g <<< 32 := by simp [genW]

theorem ebKey_eq (mode eb : Word) (h : eb = (mode >>> 1) &&& 1) : ebKey mode = genW 0 eb := by
  rw [genW_zero', h]; rfl

/-- `whnfCoreC` gains an entry. -/
theorem CoreS.set_wc {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (e x : Word)
    (he : HW e) (hx : HW x) (hs : msetG wcSch m e (genW 0 eb) x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        whnfCoreC := a.caches.whnfCoreC.insert (decE e) (decE x) } } vis fe
      { M with wc := M.wc.insert (decE e, eb) (decE x) } eb ∧ StackKept m m' := by
  have hf : MemFrame [96] [97] m m' := msetG_frame wcSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  have hq := hS.core.wc.setE (coreSch_wf _ _ (by decide) (by decide)) hS.core.eb1 e x he hx m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ 96 → S.cs ≠ 97 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [96] [97] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {VR : Mem → Word → ν → Prop} {M₀ : Std.HashMap (κ × Word) ν} {t te : Std.HashMap κ ν}, S.WF →
      VConst VR → S.arr ≠ 96 → S.cs ≠ 97 → ModeR S K VR m M₀ eb t te →
      ModeR S K VR m' M₀ eb t te :=
    fun hS' hV h1 h2 h => h.frame hS' hV (by simpa using h1) (by simpa using h2) hf
  have frv : ∀ {κ : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ)
      (mp : Std.HashMap κ EIdx), S.WF → S.arr ≠ 96 → S.cs ≠ 97 → MemoRV S K VH m mp →
      MemoRV S K VH m' mp :=
    fun S K mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [96] [97] (by simpa using h1) (by simpa using h2) m m' hf
        (vh_const m m') mp hR
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [96] [97] (by simp) (by simp) m m' hf a
        hS.arena.1), DerR.of_store _ _ _ (DerR.frameM [96] [97] m m' hf (by simp) a hS.arena.2) rfl⟩,
      ⟨hq,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wk,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wh,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.inf,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.io,
        mr (coreSch_wf _ _ (by decide) (by decide)) vb_const (by decide) (by decide) hS.core.de,
        hS.core.eb1,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.ct,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.cv,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.rr,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.lq,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.lsq⟩,
      hS.pins.congr (hf.1 PINS (by simp [PINS]) (by decide)),
      hS.env.frame (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; decide) hf,
      fun h l e => hS.readL h l e, fun h l e => hS.readLs h l e, hS.nwf,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn, hS.memos.frame hf (by decide) (by decide), hf.2.2.1 145 ▸ hS.bstk,
      (hS.den.frameE (hf.1 EREC (by simp [EREC]) (by decide))).caches rfl rfl rfl,
      hS.mode.frame hf (by simp) (by simp)⟩,
    StackKept.of_frame hf⟩

/-- `whnfCoreCheapC` gains an entry. -/
theorem CoreS.set_wk {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (e x : Word)
    (he : HW e) (hx : HW x) (hs : msetG wkSch m e (genW 0 eb) x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        whnfCoreCheapC := a.caches.whnfCoreCheapC.insert (decE e) (decE x) } } vis fe
      { M with wk := M.wk.insert (decE e, eb) (decE x) } eb ∧ StackKept m m' := by
  have hf : MemFrame [97] [99] m m' := msetG_frame wkSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  have hq := hS.core.wk.setE (coreSch_wf _ _ (by decide) (by decide)) hS.core.eb1 e x he hx m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ 97 → S.cs ≠ 99 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [97] [99] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {VR : Mem → Word → ν → Prop} {M₀ : Std.HashMap (κ × Word) ν} {t te : Std.HashMap κ ν}, S.WF →
      VConst VR → S.arr ≠ 97 → S.cs ≠ 99 → ModeR S K VR m M₀ eb t te →
      ModeR S K VR m' M₀ eb t te :=
    fun hS' hV h1 h2 h => h.frame hS' hV (by simpa using h1) (by simpa using h2) hf
  have frv : ∀ {κ : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ)
      (mp : Std.HashMap κ EIdx), S.WF → S.arr ≠ 97 → S.cs ≠ 99 → MemoRV S K VH m mp →
      MemoRV S K VH m' mp :=
    fun S K mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [97] [99] (by simpa using h1) (by simpa using h2) m m' hf
        (vh_const m m') mp hR
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [97] [99] (by simp) (by simp) m m' hf a
        hS.arena.1), DerR.of_store _ _ _ (DerR.frameM [97] [99] m m' hf (by simp) a hS.arena.2) rfl⟩,
      ⟨mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wc,
        hq,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wh,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.inf,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.io,
        mr (coreSch_wf _ _ (by decide) (by decide)) vb_const (by decide) (by decide) hS.core.de,
        hS.core.eb1,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.ct,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.cv,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.rr,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.lq,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.lsq⟩,
      hS.pins.congr (hf.1 PINS (by simp [PINS]) (by decide)),
      hS.env.frame (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; decide) hf,
      fun h l e => hS.readL h l e, fun h l e => hS.readLs h l e, hS.nwf,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn, hS.memos.frame hf (by decide) (by decide), hf.2.2.1 145 ▸ hS.bstk,
      (hS.den.frameE (hf.1 EREC (by simp [EREC]) (by decide))).caches rfl rfl rfl,
      hS.mode.frame hf (by simp) (by simp)⟩,
    StackKept.of_frame hf⟩

/-! ## The twin's slot -/

section twin
variable (mode : ConLeche.CheckMode) (fe : IFEnv) (F : Nat) (c : Bool) (d : Nat) (e : EIdx)
  (a : AState)

theorem knot_whnfCore_stuck (h : whnfCoreStuckTag e = true) :
    ((coreKnot mode fe id (F + 1)).whnfCore c d e).run a = .ok (e, a) := by
  simp [coreKnot, h]; rfl

theorem knot_whnfCore_hitK (h : whnfCoreStuckTag e = false) (x : EIdx)
    (hm : a.caches.whnfCoreCheapC[e]? = some x) :
    ((coreKnot mode fe id (F + 1)).whnfCore true d e).run a = .ok (x, a) := by
  simp [coreKnot, h, hm]; rfl

theorem knot_whnfCore_hitF (h : whnfCoreStuckTag e = false) (x : EIdx)
    (hm : a.caches.whnfCoreC[e]? = some x) :
    ((coreKnot mode fe id (F + 1)).whnfCore false d e).run a = .ok (x, a) := by
  simp [coreKnot, h, hm]; rfl

theorem knot_whnfCore_missK (h : whnfCoreStuckTag e = false)
    (hm : a.caches.whnfCoreCheapC[e]? = none) (x : EIdx) (a₁ : AState)
    (hb : (whnfCoreBody mode (coreKnot mode fe id F) fe true d e).run a = .ok (x, a₁)) :
    ((coreKnot mode fe id (F + 1)).whnfCore true d e).run a =
      .ok (x, { a₁ with caches := { a₁.caches with
        whnfCoreCheapC := a₁.caches.whnfCoreCheapC.insert e x } }) := by
  simp [coreKnot, h, hm, StateT.run_bind, hb, whnfCoreCheapSet]; rfl

theorem knot_whnfCore_missF (h : whnfCoreStuckTag e = false)
    (hm : a.caches.whnfCoreC[e]? = none) (x : EIdx) (a₁ : AState)
    (hb : (whnfCoreBody mode (coreKnot mode fe id F) fe false d e).run a = .ok (x, a₁)) :
    ((coreKnot mode fe id (F + 1)).whnfCore false d e).run a =
      .ok (x, { a₁ with caches := { a₁.caches with
        whnfCoreC := a₁.caches.whnfCoreC.insert e x } }) := by
  simp [coreKnot, h, hm, StateT.run_bind, hb, whnfCoreSet]; rfl

end twin

/-! ## The slot refines the twin's slot -/

theorem KeptAll.wk {M M' : ModeMaps} {eb : Word} (h : KeptAll M M' eb) (k : EIdx) (v : EIdx) :
    KeptAll M { M' with wk := M'.wk.insert (k, eb) v } eb := fun h0 => by
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := h h0
  refine ⟨a1, fun k' => ?_, c1, d1, e1, f1⟩
  rw [Std.HashMap.getElem?_insert]
  have : ¬ ((k, eb) == (k', (0 : Word))) = true := by simp [h0]
  simp only [this, Bool.false_eq_true, ↓reduceIte]; exact b1 k'

theorem KeptAll.wc {M M' : ModeMaps} {eb : Word} (h : KeptAll M M' eb) (k : EIdx) (v : EIdx) :
    KeptAll M { M' with wc := M'.wc.insert (k, eb) v } eb := fun h0 => by
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := h h0
  refine ⟨fun k' => ?_, b1, c1, d1, e1, f1⟩
  rw [Std.HashMap.getElem?_insert]
  have : ¬ ((k, eb) == (k', (0 : Word))) = true := by simp [h0]
  simp only [this, Bool.false_eq_true, ↓reduceIte]; exact a1 k'

/-! ## The loop -/

/-- **The model of `whnf_core_loop`'s loop** at L fuel `n`: each iteration is a run of
`whnf_core_step` (`callW`), done on `(0, v)`, continuing on `(1, e')`. -/
def coreLoopW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, mode, cheap, vis, d, e =>
    match callW p n "whnf_core_step" [mode, cheap, vis, d, e] m with
    | none => none
    | some (r, m₁) =>
      if r.headD 0 = 0 then some (r.tail.headD 0, m₁)
      else coreLoopW p n m₁ mode cheap vis d (r.tail.headD 0)

section loop
variable (p : Prog) (n : Nat) (m m₁ : Mem) (mode cheap vis d e : Word) (r : List Word)

theorem coreLoopW_done (h : callW p n "whnf_core_step" [mode, cheap, vis, d, e] m = some (r, m₁))
    (h0 : r.headD 0 = 0) :
    coreLoopW p (n + 1) m mode cheap vis d e = some (r.tail.headD 0, m₁) := by
  simp only [coreLoopW, h, h0, ↓reduceIte]

theorem coreLoopW_cont (h : callW p n "whnf_core_step" [mode, cheap, vis, d, e] m = some (r, m₁))
    (h0 : ¬ r.headD 0 = 0) :
    coreLoopW p (n + 1) m mode cheap vis d e = coreLoopW p n m₁ mode cheap vis d (r.tail.headD 0) := by
  simp only [coreLoopW, h, h0, ↓reduceIte]

end loop

theorem whnfCoreLoopB_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n whnfCoreLoopB
    ⦃fun r s' => r ≠ .brk ∧
      coreLoopW p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) =
        some ((r.retOr [0]).headD 0, s'.mem) ∧ r ≠ .normal; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := whnfCoreLoopB) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih, callW_spec p n "whnf_core_step"] <;>
      finish [coreLoopW_done, coreLoopW_cont]

theorem whnfCoreLoop_spec (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St)
    (mode cheap vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf_core_loop" [mode, cheap, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ coreLoopW p (n + 1) s₀.mem mode cheap vis d e =
      some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.loop]
  simp only [callFn, whnfCoreLoopL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (whnfCoreLoopB_spec p (n + 1) s)] <;>
    finish

/-! ## The loop refines `whnfCoreLoop` -/

theorem whnfCoreLoop_done (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (c : Bool)
    (d K : Nat) (e v : EIdx) (a a₁ : AState)
    (hs : (whnfCoreStep mode r fe c d e).run a = .ok (.done v, a₁)) :
    (whnfCoreLoop mode r fe c d (K + 1) e).run a = .ok (v, a₁) := by
  simp only [whnfCoreLoop, StateT.run_bind, hs, except_ok_bind]; rfl

theorem whnfCoreLoop_cont (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (c : Bool)
    (d K : Nat) (e e' : EIdx) (a a₁ : AState)
    (hs : (whnfCoreStep mode r fe c d e).run a = .ok (.cont e', a₁)) :
    (whnfCoreLoop mode r fe c d (K + 1) e).run a = (whnfCoreLoop mode r fe c d K e').run a₁ := by
  simp only [whnfCoreLoop, StateT.run_bind, hs, except_ok_bind]

end L.Arena
