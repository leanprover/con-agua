import ConAgua.Arena.WhnfCore

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

/-- A mode memo around a body: probe at the current generation (`CTL[115]`), answer a hit, else
take the body's run `res`, probe again on its memory, record, answer. -/
def memoSlotW (S : MemoSch) (m : Mem) (e : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  if mfindG S m e (rdW (m.arr64 CTL) 115 <<< 32) = [] then none
  else if (mfindG S m e (rdW (m.arr64 CTL) 115 <<< 32)).headD 0 ≠ 0 then
    some (mvG S m ((mfindG S m e (rdW (m.arr64 CTL) 115 <<< 32)).tail.headD 0), m)
  else match res with
    | none => none
    | some (r, m₁) =>
      match msetG S m₁ e (rdW (m₁.arr64 CTL) 115 <<< 32) (r.headD 0) with
      | none => none
      | some m₂ => some (r.headD 0, m₂)

/-- **The model of `whnf_core`**, the loop through its run. -/
def whnfCoreW (p : Prog) (n : Nat) (m : Mem) (mode cheap vis d e : Word) : Option (Word × Mem) :=
  if e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0 then some (e, m)
  else if cheap ≠ 0 then memoSlotW wkSch m e (callW p n "whnf_core_loop" [mode, 1, vis, d, e] m)
  else memoSlotW wcSch m e (callW p n "whnf_core_loop" [mode, 0, vis, d, e] m)

section arms
variable (S : MemoSch) (m m₁ m₂ : Mem) (e : Word) (r : List Word)

theorem memoSlotW_hit (res : Option (List Word × Mem))
    (h0 : mfindG S m e (rdW (m.arr64 CTL) 115 <<< 32) ≠ [])
    (h1 : (mfindG S m e (rdW (m.arr64 CTL) 115 <<< 32)).headD 0 ≠ 0) :
    memoSlotW S m e res =
      some (mvG S m ((mfindG S m e (rdW (m.arr64 CTL) 115 <<< 32)).tail.headD 0), m) := by
  unfold memoSlotW; rw [if_neg h0, if_pos h1]

theorem memoSlotW_miss (h0 : mfindG S m e (rdW (m.arr64 CTL) 115 <<< 32) ≠ [])
    (h1 : (mfindG S m e (rdW (m.arr64 CTL) 115 <<< 32)).headD 0 = 0)
    (h2 : msetG S m₁ e (rdW (m₁.arr64 CTL) 115 <<< 32) (r.headD 0) = some m₂) :
    memoSlotW S m e (some (r, m₁)) = some (r.headD 0, m₂) := by
  unfold memoSlotW
  rw [if_neg h0, if_neg (by simp only [ne_eq, Decidable.not_not]; exact h1)]
  simp only [h2]

end arms

theorem whnfCoreW_stuck (p : Prog) (n : Nat) (m : Mem) (mode cheap vis d e : Word)
    (h : e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0) :
    whnfCoreW p n m mode cheap vis d e = some (e, m) := by
  unfold whnfCoreW; rw [if_pos h]

theorem whnfCoreW_cheap (p : Prog) (n : Nat) (m : Mem) (mode cheap vis d e : Word)
    (h : ¬ (e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0)) (hc : cheap ≠ 0) :
    whnfCoreW p n m mode cheap vis d e =
      memoSlotW wkSch m e (callW p n "whnf_core_loop" [mode, 1, vis, d, e] m) := by
  unfold whnfCoreW; rw [if_neg h, if_pos hc]

theorem whnfCoreW_full (p : Prog) (n : Nat) (m : Mem) (mode cheap vis d e : Word)
    (h : ¬ (e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0)) (hc : cheap = 0) :
    whnfCoreW p n m mode cheap vis d e =
      memoSlotW wcSch m e (callW p n "whnf_core_loop" [mode, 0, vis, d, e] m) := by
  unfold whnfCoreW; rw [if_neg h, if_neg (by simpa using hc)]


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
    finish [whnfCoreW_stuck, whnfCoreW_cheap, whnfCoreW_full, memoSlotW_hit, memoSlotW_miss,
      msetG_eq, mvG]

end spec


/-! ## The relation across a mode memo's `find; put` -/

theorem genW_zero' (g : Word) : genW 0 g = g <<< 32 := by simp [genW]

theorem bank_gen {m : Mem} {G g : Word} (h : BankW BANKC m G g) : rdW (m.arr64 CTL) 115 = g := h.2.1

theorem Kept.insert' {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] {M M' : Std.HashMap (κ × Word) ν}
    {G g : Word} (h : Kept M M' G g) (k : κ) (v : ν) : Kept M (M'.insert (k, g) v) G g :=
  h.trans (Kept.insert M' G g k v)

/-- `whnfCoreC` gains an entry. -/
theorem CoreS.set_wc {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {G g : Word} (hS : CoreS dn m a vis fe M G g) (e x : Word)
    (he : HW e) (hs : msetG wcSch m e (genW 0 g) x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        whnfCoreC := a.caches.whnfCoreC.insert (decE e) (decE x) } } vis fe
      { M with wc := M.wc.insert (decE e, g) (decE x) } G g ∧ StackKept m m' := by
  have hf : MemFrame [96] [97] m m' := msetG_frame wcSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  obtain ⟨hq, hB⟩ := hS.core.wc.setE (coreSch_wf _ _ (by decide) (by decide)) ⟨by decide, by decide⟩
    hS.core.bank e x he m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ 96 → S.cs ≠ 97 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [96] [97] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {dv : Word → ν} {M₀ : Std.HashMap (κ × Word) ν} {t : Std.HashMap κ ν}, S.WF → S.arr ≠ 96 →
      S.cs ≠ 97 → ModeR S K dv m M₀ G g t → ModeR S K dv m' M₀ G g t :=
    fun hS' h1 h2 h => h.frame hS' (by simpa using h1) (by simpa using h2) hf
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [96] [97] (by simp) (by simp) m m' hf a
        hS.arena.1), DerR.of_store _ _ _ (DerR.frameM [96] [97] m m' hf (by simp) a hS.arena.2) rfl⟩,
      ⟨hq,
        mr (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.wk,
        mr (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.wh,
        mr (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.inf,
        mr (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.io,
        mr (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.de,
        hB,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.ct,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.cv,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.rr,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.lq,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.lsq⟩,
      hS.pins.congr (hf.1 PINS (by simp [PINS]) (by decide)),
      hS.env.frame (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; decide) hf,
      fun h l e => hS.readL h l e, fun h l e => hS.readLs h l e, hS.nwf⟩,
    by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩

/-- `whnfCoreCheapC` gains an entry. -/
theorem CoreS.set_wk {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {G g : Word} (hS : CoreS dn m a vis fe M G g) (e x : Word)
    (he : HW e) (hs : msetG wkSch m e (genW 0 g) x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        whnfCoreCheapC := a.caches.whnfCoreCheapC.insert (decE e) (decE x) } } vis fe
      { M with wk := M.wk.insert (decE e, g) (decE x) } G g ∧ StackKept m m' := by
  have hf : MemFrame [97] [99] m m' := msetG_frame wkSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  obtain ⟨hq, hB⟩ := hS.core.wk.setE (coreSch_wf _ _ (by decide) (by decide)) ⟨by decide, by decide⟩
    hS.core.bank e x he m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ 97 → S.cs ≠ 99 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [97] [99] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {dv : Word → ν} {M₀ : Std.HashMap (κ × Word) ν} {t : Std.HashMap κ ν}, S.WF → S.arr ≠ 97 →
      S.cs ≠ 99 → ModeR S K dv m M₀ G g t → ModeR S K dv m' M₀ G g t :=
    fun hS' h1 h2 h => h.frame hS' (by simpa using h1) (by simpa using h2) hf
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [97] [99] (by simp) (by simp) m m' hf a
        hS.arena.1), DerR.of_store _ _ _ (DerR.frameM [97] [99] m m' hf (by simp) a hS.arena.2) rfl⟩,
      ⟨mr (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.wc,
        hq,
        mr (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.wh,
        mr (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.inf,
        mr (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.io,
        mr (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.de,
        hB,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.ct,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.cv,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.rr,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.lq,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.lsq⟩,
      hS.pins.congr (hf.1 PINS (by simp [PINS]) (by decide)),
      hS.env.frame (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; decide) hf,
      fun h l e => hS.readL h l e, fun h l e => hS.readLs h l e, hS.nwf⟩,
    by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩


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
  simp [coreKnot, h, hm, StateT.run_bind, hb, except_ok_bind, whnfCoreCheapSet]; rfl

theorem knot_whnfCore_missF (h : whnfCoreStuckTag e = false)
    (hm : a.caches.whnfCoreC[e]? = none) (x : EIdx) (a₁ : AState)
    (hb : (whnfCoreBody mode (coreKnot mode fe id F) fe false d e).run a = .ok (x, a₁)) :
    ((coreKnot mode fe id (F + 1)).whnfCore false d e).run a =
      .ok (x, { a₁ with caches := { a₁.caches with
        whnfCoreC := a₁.caches.whnfCoreC.insert e x } }) := by
  simp [coreKnot, h, hm, StateT.run_bind, hb, except_ok_bind, whnfCoreSet]; rfl

end twin


/-! ## The slot refines the twin's slot -/

theorem callW_zero (p : Prog) (f : FnName) (vs : List Word) (m : Mem) : callW p 0 f vs m = none := by
  simp only [callW, invoke, lookupFn]
  cases p.lookup f with
  | none => rfl
  | some fd => rfl


theorem KeptAll.wk {M M' : ModeMaps} {G g : Word} (h : KeptAll M M' G g) (k : EIdx) (v : EIdx) :
    KeptAll M { M' with wk := M'.wk.insert (k, g) v } G g :=
  ⟨h.1, Kept.insert' h.2.1 k v, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem KeptAll.wc {M M' : ModeMaps} {G g : Word} (h : KeptAll M M' G g) (k : EIdx) (v : EIdx) :
    KeptAll M { M' with wc := M'.wc.insert (k, g) v } G g :=
  ⟨Kept.insert' h.1 k v, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

section slot
variable (p : Prog) (hp : WhnfCoreProg p)

include hp in
/-- **The knot's `whnfCore` slot, one level up**: given the knot at every fuel up to `n` (for
the body's callees), `whnf_core` at `n + 1` refines the slot of `coreKnot mode fe id F`,
`F ≥ n + 1`. The body's own refinement is `whnfCoreBody_refines`. -/
theorem whnfCoreSlot_step (n : Nat) (hk : KnotUpTo p n) : WhnfCoreSlot p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM G g mode cheap d e hF hn hs he
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (whnfCore_spec p hp n s₀ mode cheap vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hB := hS.core.bank
  have h115 : rdW (s.mem.arr64 CTL) 115 <<< 32 = genW 0 g := by rw [bank_gen hB, genW_zero']
  by_cases hst : e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0
  · rw [whnfCoreW_stuck _ _ _ _ _ _ _ _ hst] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have ht : whnfCoreStuckTag (decE e) = true := by rw [stuck_iff e he]; simpa using hst
    obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _ (knot_whnfCore_stuck _ fe F' (cheap != 0) d.toNat _ a₀ ht)
    refine ⟨hok, ?_, by rw [hres, decH, ← hr]⟩
    rw [hst', ← hm]; exact ⟨MM, G, hS, KeptAll.refl _ _ _, StackKept.refl _, UInt64.le_refl _⟩
  have ht : whnfCoreStuckTag (decE e) = false := by rw [stuck_iff e he]; simpa using hst
  by_cases hc : cheap ≠ 0
  · rw [whnfCoreW_cheap _ _ _ _ _ _ _ _ hst hc] at hW
    have hcb : (cheap != 0) = true := by simpa using hc
    rw [hcb]
    unfold memoSlotW at hW
    rw [h115] at hW
    by_cases h0 : mfindG wkSch s.mem e (genW 0 g) = []
    · simp [h0] at hW
    rw [if_neg h0] at hW
    have hf := hS.core.wk.findE hB e he h0
    by_cases h1 : (mfindG wkSch s.mem e (genW 0 g)).headD 0 ≠ 0
    · rw [if_pos h1] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr, hm⟩ := hW
      obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _
        (knot_whnfCore_hitK _ fe F' d.toNat _ a₀ ht _ (hf.1 h1))
      refine ⟨hok, ?_, by rw [hres, decH, ← hr]⟩
      rw [hst', ← hm]; exact ⟨MM, G, hS, KeptAll.refl _ _ _, StackKept.refl _, UInt64.le_refl _⟩
    rw [if_neg h1] at hW
    have hmiss := hf.2 (by simpa using h1)
    cases hcall : callW p n "whnf_core_loop" [mode, 1, vis, d, e] s.mem with
    | none => simp [hcall] at hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    simp only [hcall] at hW
    cases n with
    | zero => simp [callW_zero] at hcall
    | succ n' =>
    have hbody := whnfCoreBody_refines p n' (hk.mono (by omega)) F' (by omega) (by omega) s a₀ dn vis
      fe MM G g mode 1 d e hs he
    obtain ⟨hok, ⟨M', G', hS₁, hK₁, hSt₁, hG₁⟩, hres⟩ := CoreSpec.of_callW hbody hcall
    rw [bank_gen hS₁.core.bank, ← genW_zero'] at hW
    cases hset : msetG wkSch m₁ e (genW 0 g) (r₁.headD 0) with
    | none => rw [hset] at hW; cases hW
    | some m₂ =>
    rw [hset] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨hS₂, hSt₂⟩ := hS₁.set_wk e (r₁.headD 0) he hset
    have hb1 : ((1 : Word) != 0) = true := rfl
    rw [hb1] at hok hres
    have hrun := knot_whnfCore_missK _ fe F' d.toNat _ a₀ ht hmiss _ _ (AM.run_of_ok _ _ hok)
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨hok', ?_, by rw [hres', hres]; simp only [decH, hr]⟩
    rw [hst', ← hm, hres]
    exact ⟨_, G', hS₂, hK₁.wk _ _, hSt₁.trans hSt₂, hG₁⟩
  · have hc0 : cheap = 0 := by simpa using hc
    rw [whnfCoreW_full _ _ _ _ _ _ _ _ hst hc0] at hW
    have hcb : (cheap != 0) = false := by simp [hc0]
    rw [hcb]
    unfold memoSlotW at hW
    rw [h115] at hW
    by_cases h0 : mfindG wcSch s.mem e (genW 0 g) = []
    · simp [h0] at hW
    rw [if_neg h0] at hW
    have hf := hS.core.wc.findE hB e he h0
    by_cases h1 : (mfindG wcSch s.mem e (genW 0 g)).headD 0 ≠ 0
    · rw [if_pos h1] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr, hm⟩ := hW
      obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _
        (knot_whnfCore_hitF _ fe F' d.toNat _ a₀ ht _ (hf.1 h1))
      refine ⟨hok, ?_, by rw [hres, decH, ← hr]⟩
      rw [hst', ← hm]; exact ⟨MM, G, hS, KeptAll.refl _ _ _, StackKept.refl _, UInt64.le_refl _⟩
    rw [if_neg h1] at hW
    have hmiss := hf.2 (by simpa using h1)
    cases hcall : callW p n "whnf_core_loop" [mode, 0, vis, d, e] s.mem with
    | none => simp [hcall] at hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    simp only [hcall] at hW
    cases n with
    | zero => simp [callW_zero] at hcall
    | succ n' =>
    have hbody := whnfCoreBody_refines p n' (hk.mono (by omega)) F' (by omega) (by omega) s a₀ dn vis
      fe MM G g mode 0 d e hs he
    obtain ⟨hok, ⟨M', G', hS₁, hK₁, hSt₁, hG₁⟩, hres⟩ := CoreSpec.of_callW hbody hcall
    rw [bank_gen hS₁.core.bank, ← genW_zero'] at hW
    cases hset : msetG wcSch m₁ e (genW 0 g) (r₁.headD 0) with
    | none => rw [hset] at hW; cases hW
    | some m₂ =>
    rw [hset] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨hS₂, hSt₂⟩ := hS₁.set_wc e (r₁.headD 0) he hset
    have hb0 : ((0 : Word) != 0) = false := rfl
    rw [hb0] at hok hres
    have hrun := knot_whnfCore_missF _ fe F' d.toNat _ a₀ ht hmiss _ _ (AM.run_of_ok _ _ hok)
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨hok', ?_, by rw [hres', hres]; simp only [decH, hr]⟩
    rw [hst', ← hm, hres]
    exact ⟨_, G', hS₂, hK₁.wc _ _, hSt₁.trans hSt₂, hG₁⟩

end slot

end L.Arena
