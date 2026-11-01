module

public import ConAgua.Arena.WhnfBase
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
import ConAgua.Arena.DerRel

@[expose] public section

/-!
# The knot's `whnfCore` slot: stuck tags, the memo, the body

`whnf_core(mode, cheap, vis, d, e)` (`WhnfCore.lean`) refines the `whnfCore` slot of
`coreKnot mode fe id (F + 1)`: a stuck tag answers `e` without touching memo or store
(`whnfCoreStuckTag`, `stuck_iff`), a memo hit (`whnfCoreCheapC` in the cheap mode, `whnfCoreC`
otherwise, at the current generation) answers the entry, a miss runs `whnf_core_loop` (the
body, `whnfCoreBody … (coreKnot … F)`), records it and answers it.

Here: the tags, the memo's model `memoSlotW` (the other memo slots' pattern), the relation across a
mode memo's `find; put`, the twin's slot runs. The refinement is `core_ref` (`WhnfCoreLoop.lean`),
over the unified model, with the memo lemmas of `CoreRefine.lean`.
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

/-- `whnfCoreStuckTag` off the handle word. -/
theorem stuck_iff (e : Word) (he : HW e) :
    whnfCoreStuckTag (decE e) =
      decide (tagW e ≠ 4 ∧ tagW e ≠ 9 ∧ tagW e ≠ 7 ∧ tagW e ≠ 0) := by
  have h : (tagW e).toNat < 2 ^ 32 := Nat.lt_trans (tagW_lt e he) (by decide)
  simp only [whnfCoreStuckTag, decE_tag e he, ETag.app, ETag.proj, ETag.letE, ETag.bvar]
  rw [show (4 : UInt32) = (4 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (9 : UInt32) = (9 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (7 : UInt32) = (7 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (0 : UInt32) = (0 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  by_cases h4 : tagW e = 4 <;> by_cases h9 : tagW e = 9 <;> by_cases h7 : tagW e = 7 <;>
    by_cases h0 : tagW e = 0 <;> simp_all

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
  have hf : MemFrame [(WCM : TieredArray)] [97] m m' := msetG_frame wcSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  have hq := hS.core.wc.setE (coreSch_wf _ _ (by decide) (by decide)) hS.core.eb1 e x he hx m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ WCM → S.cs ≠ 97 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [(WCM : TieredArray)] [97] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {VR : Mem → Word → ν → Prop} {M₀ : Std.HashMap (κ × Word) ν} {t te : Std.HashMap κ ν}, S.WF →
      VConst VR → S.arr ≠ WCM → S.cs ≠ 97 → ModeR S K VR m M₀ eb t te →
      ModeR S K VR m' M₀ eb t te :=
    fun hS' hV h1 h2 h => h.frame hS' hV (by simpa using h1) (by simpa using h2) hf
  have frv : ∀ {κ : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ)
      (mp : Std.HashMap κ EIdx), S.WF → S.arr ≠ WCM → S.cs ≠ 97 → MemoRV S K VH m mp →
      MemoRV S K VH m' mp :=
    fun S K mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [(WCM : TieredArray)] [97] (by simpa using h1) (by simpa using h2) m m' hf
        (vh_const m m') mp hR
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.arr SPN (by decide) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.ctl 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [(WCM : TieredArray)] [97] (by decide) (by simp) m m' hf a
        hS.arena.base), DerR.of_store _ _ _ (DerR.frameM [(WCM : TieredArray)] [97] m m' hf (by decide) a hS.arena.der) rfl⟩,
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
      hS.pins.congr (hf.arr PINS (by decide) (by decide)),
      hS.env.frame (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; decide) hf,
      fun h l e => hS.readL h l e, fun h l e => hS.readLs h l e, hS.nwf,
      hf.size EREC ▸ hS.erec, hf.size SPN ▸ hS.spn, hS.memos.frame hf (by decide) (by decide), hf.size BSTK ▸ hS.bstk,
      (hS.den.frameE (hf.arr EREC (by decide) (by decide))).caches rfl rfl rfl,
      hS.mode.frame hf (by simp) (by simp)⟩,
    StackKept.of_frame hf⟩

/-- `whnfCoreCheapC` gains an entry. -/
theorem CoreS.set_wk {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (e x : Word)
    (he : HW e) (hx : HW x) (hs : msetG wkSch m e (genW 0 eb) x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        whnfCoreCheapC := a.caches.whnfCoreCheapC.insert (decE e) (decE x) } } vis fe
      { M with wk := M.wk.insert (decE e, eb) (decE x) } eb ∧ StackKept m m' := by
  have hf : MemFrame [(WKM : TieredArray)] [99] m m' := msetG_frame wkSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  have hq := hS.core.wk.setE (coreSch_wf _ _ (by decide) (by decide)) hS.core.eb1 e x he hx m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ WKM → S.cs ≠ 99 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [(WKM : TieredArray)] [99] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {VR : Mem → Word → ν → Prop} {M₀ : Std.HashMap (κ × Word) ν} {t te : Std.HashMap κ ν}, S.WF →
      VConst VR → S.arr ≠ WKM → S.cs ≠ 99 → ModeR S K VR m M₀ eb t te →
      ModeR S K VR m' M₀ eb t te :=
    fun hS' hV h1 h2 h => h.frame hS' hV (by simpa using h1) (by simpa using h2) hf
  have frv : ∀ {κ : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ)
      (mp : Std.HashMap κ EIdx), S.WF → S.arr ≠ WKM → S.cs ≠ 99 → MemoRV S K VH m mp →
      MemoRV S K VH m' mp :=
    fun S K mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [(WKM : TieredArray)] [99] (by simpa using h1) (by simpa using h2) m m' hf
        (vh_const m m') mp hR
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.arr SPN (by decide) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.ctl 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [(WKM : TieredArray)] [99] (by decide) (by simp) m m' hf a
        hS.arena.base), DerR.of_store _ _ _ (DerR.frameM [(WKM : TieredArray)] [99] m m' hf (by decide) a hS.arena.der) rfl⟩,
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
      hS.pins.congr (hf.arr PINS (by decide) (by decide)),
      hS.env.frame (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; decide) hf,
      fun h l e => hS.readL h l e, fun h l e => hS.readLs h l e, hS.nwf,
      hf.size EREC ▸ hS.erec, hf.size SPN ▸ hS.spn, hS.memos.frame hf (by decide) (by decide), hf.size BSTK ▸ hS.bstk,
      (hS.den.frameE (hf.arr EREC (by decide) (by decide))).caches rfl rfl rfl,
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

end L.Arena
