import ConAgua.Arena.Knot
import ConAgua.Arena.WhnfDeltaSlot

/-!
# The knot's `infer`, `infer_io`, `defeq`, `defeq_e` slots one level up (lane `defeq`)

`infer(mode, vis, d, e)` (`Knot.lean`) refines the `infer` slot of `coreKnot mode fe id (F + 1)`:
a memo hit (`inferC`, array 99, at the mode's eager bit) answers the entry, a miss runs
`infer_body` (the body, `inferBody (coreKnot … F)`), records it and answers it. The same for
`infer_io` (`inferIOC`, array 100, the body at the io view) and `defeq` (`defeqC`, array 101, key
`(a, b ∣ eb << 32)`, `Bool` values). The pattern of `WhnfDeltaSlot.lean`'s `whnf`, without the
stuck tags: a word-level model (`memoSlotW`, `memoSlotD`), the L spec by `vcgen` + `finish`, the
refinement from the body's spec (`InferBodySpec`, …, hypotheses) and the memo lemmas.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- What the slot specs need of a program: the four slots and their memos' `find`/`put`. -/
structure KnotProg (p : Prog) : Prop where
  infer : p.lookup "infer" = some inferSlotL
  inferIO : p.lookup "infer_io" = some inferIOSlotL
  defeq : p.lookup "defeq" = some defeqSlotL
  defeqE : p.lookup "defeq_e" = some defeqESlotL
  inFind : p.lookup "in_find" = some (memoFindG inSch)
  inPut : p.lookup "in_put" = some (memoPutG inSch)
  ioFind : p.lookup "io_find" = some (memoFindG ioSch)
  ioPut : p.lookup "io_put" = some (memoPutG ioSch)
  deFind : p.lookup "de_find" = some (memoFindG deSch)
  dePut : p.lookup "de_put" = some (memoPutG deSch)

/-! ## The models -/

/-- A `Bool` memo around a body (`defeq`): as `memoSlotW`, but a hit answers the verdict word
`u64(v != 0)`. -/
def memoSlotD (S : MemoSch) (m : Mem) (e k : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  if mfindG S m e k = [] then none
  else if (mfindG S m e k).headD 0 ≠ 0 then
    some (Cmp.evalW .ne (mvG S m ((mfindG S m e k).tail.headD 0)) 0, m)
  else match res with
    | none => none
    | some (r, m₁) =>
      match msetG S m₁ e k (r.headD 0) with
      | none => none
      | some m₂ => some (r.headD 0, m₂)

section arms
variable (S : MemoSch) (m m₁ m₂ : Mem) (e k : Word) (r : List Word)

theorem memoSlotD_hit (res : Option (List Word × Mem)) (h0 : mfindG S m e k ≠ [])
    (h1 : (mfindG S m e k).headD 0 ≠ 0) :
    memoSlotD S m e k res = some (Cmp.evalW .ne (mvG S m ((mfindG S m e k).tail.headD 0)) 0, m) := by
  unfold memoSlotD; simp only [h0, h1, if_false, if_true, ne_eq, not_false_eq_true]

theorem memoSlotD_miss (h0 : mfindG S m e k ≠ []) (h1 : (mfindG S m e k).headD 0 = 0)
    (h2 : msetG S m₁ e k (r.headD 0) = some m₂) :
    memoSlotD S m e k (some (r, m₁)) = some (r.headD 0, m₂) := by
  unfold memoSlotD
  rw [if_neg h0, if_neg (by simp only [ne_eq, Decidable.not_not]; exact h1)]
  simp only [h2]

end arms

/-- **The model of `defeq_e`**: the `defeq` slot's run at the eager mode word. -/
def defeqEW (p : Prog) (n : Nat) (m : Mem) (mode vis d a b : Word) : Option (Word × Mem) :=
  match callW p n "defeq" [mode ||| 2, vis, d, a, b] m with
  | none => none
  | some (r, m') => some (r.headD 0, m')

theorem defeqEW_some (p : Prog) (n : Nat) (m m' : Mem) (mode vis d a b : Word) (r : List Word)
    (h : callW p n "defeq" [mode ||| 2, vis, d, a, b] m = some (r, m')) :
    defeqEW p n m mode vis d a b = some (r.headD 0, m') := by
  simp only [defeqEW, h]

/-! ## The L specs -/

section spec
variable (p : Prog) (hp : KnotProg p)

include hp in
theorem infer_spec (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ memoSlotW inSch s₀.mem e (ebKey mode)
      (callW p n "infer_body" [mode, vis, d, e] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.infer]
  simp only [callFn, inferSlotL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec inSch p _ hp.inFind n, memoPutG_spec inSch p _ hp.inPut n,
      callW_spec p n "infer_body"] <;>
    finish [memoSlotW_hit, memoSlotW_miss, mvG, ebKey]

include hp in
theorem inferIO_spec (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_io" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ memoSlotW ioSch s₀.mem e (ebKey mode)
      (callW p n "infer_body_io" [mode, vis, d, e] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.inferIO]
  simp only [callFn, inferIOSlotL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec ioSch p _ hp.ioFind n, memoPutG_spec ioSch p _ hp.ioPut n,
      callW_spec p n "infer_body_io"] <;>
    finish [memoSlotW_hit, memoSlotW_miss, mvG, ebKey]

include hp in
theorem defeq_spec (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ memoSlotD deSch s₀.mem a (b ||| ebKey mode)
      (callW p n "defeq_body" [mode, vis, d, a, b] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.defeq]
  simp only [callFn, defeqSlotL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec deSch p _ hp.deFind n, memoPutG_spec deSch p _ hp.dePut n,
      callW_spec p n "defeq_body"] <;>
    finish [memoSlotD_hit, memoSlotD_miss, mvG, ebKey]

include hp in
theorem defeqE_spec (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_e" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ defeqEW p n s₀.mem mode vis d a b = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.defeqE]
  simp only [callFn, defeqESlotL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "defeq"] <;>
    finish [defeqEW_some]

end spec


/-! ## `defeqC`'s `find; put` at the eager bit -/

/-- `dKeyG`'s decoding at two handle words and an eager bit. -/
theorem dKeyG_dk (a b eb : Word) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) (heb : eb ≤ 1) :
    dKeyG.dk a (genW b eb) = ((decE a, decE b), eb) := by
  have hg : eb.toNat < 2 ^ 32 := by rw [UInt64.le_iff_toNat_le] at heb; simp at heb; omega
  show (pairKey.dk a (genW b eb &&& 0xFFFFFFFF), genW b eb >>> 32) = _
  rw [genW_lo b eb hb, genW_hi b eb hb hg]; rfl

/-- **A `find; put` of `defeqC`** at the eager bit `eb` is the twin field's insert (the `Bool`
twin of `ModeR.setE`). -/
theorem ModeR.setD {S : MemoSch} {m : Mem} {M : Std.HashMap ((EIdx × EIdx) × Word) Bool} {eb : Word}
    {t te : Std.HashMap (EIdx × EIdx) Bool} (hS : S.WF) (h : ModeR S dKeyG VB m M eb t te)
    (heb : eb ≤ 1) (a b r : Word) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) (m' : Mem)
    (hs : msetG S m a (genW b eb) r = some m') :
    ModeR S dKeyG VB m' (M.insert ((decE a, decE b), eb) (decB r)) eb
      (t.insert (decE a, decE b) (decB r)) te := by
  have hok : dKeyG.ok a (genW b eb) := by
    show (pairKey (k₁ := .expr) (k₂ := .expr)).ok a (genW b eb &&& 0xFFFFFFFF); rw [genW_lo b eb hb]; exact ⟨ha, hb⟩
  have hR := memoRV_set S hS dKeyG VB (fun _ _ _ _ _ h => h) m M h.memo a (genW b eb) r hok
    (decB r) rfl m' hs
  rw [dKeyG_dk a b eb ha hb heb] at hR
  refine ⟨hR, bank_set M eb t h.cur _ _, fun h0 => ?_, h.empty⟩
  exact bank_other M eb 1 te (h.stored h0) (by rw [h0]; decide) _ _

/-! ## The relation across the slots' memo `find; put` -/

/-- `inferC` gains an entry (copy of `CoreS.set_wh`, at `inSch`: array 99, `CTL` 102/103). -/
theorem CoreS.set_in {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (e x : Word)
    (he : HW e) (hx : HW x) (hs : msetG inSch m e (genW 0 eb) x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        inferC := a.caches.inferC.insert (decE e) (decE x) } } vis fe
      { M with inf := M.inf.insert (decE e, eb) (decE x) } eb ∧ StackKept m m' := by
  have hf : MemFrame [99] [103] m m' := msetG_frame inSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  have hq := hS.core.inf.setE (coreSch_wf _ _ (by decide) (by decide)) hS.core.eb1 e x he hx m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ 99 → S.cs ≠ 103 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [99] [103] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {VR : Mem → Word → ν → Prop} {M₀ : Std.HashMap (κ × Word) ν} {t te : Std.HashMap κ ν}, S.WF →
      VConst VR → S.arr ≠ 99 → S.cs ≠ 103 → ModeR S K VR m M₀ eb t te →
      ModeR S K VR m' M₀ eb t te :=
    fun hS' hV h1 h2 h => h.frame hS' hV (by simpa using h1) (by simpa using h2) hf
  have frv : ∀ {κ : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ)
      (mp : Std.HashMap κ EIdx), S.WF → S.arr ≠ 99 → S.cs ≠ 103 → MemoRV S K VH m mp →
      MemoRV S K VH m' mp :=
    fun S K mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [99] [103] (by simpa using h1) (by simpa using h2) m m' hf
        (vh_const m m') mp hR
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [99] [103] (by simp) (by simp) m m' hf a
        hS.arena.1), DerR.of_store _ _ _ (DerR.frameM [99] [103] m m' hf (by simp) a hS.arena.2) rfl⟩,
      ⟨mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wc,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wk,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wh,
        hq,
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
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn⟩,
    by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩

/-- `inferIOC` gains an entry (copy of `CoreS.set_wh`, at `ioSch`: array 100, `CTL` 104/105). -/
theorem CoreS.set_io {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (e x : Word)
    (he : HW e) (hx : HW x) (hs : msetG ioSch m e (genW 0 eb) x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        inferIOC := a.caches.inferIOC.insert (decE e) (decE x) } } vis fe
      { M with io := M.io.insert (decE e, eb) (decE x) } eb ∧ StackKept m m' := by
  have hf : MemFrame [100] [105] m m' := msetG_frame ioSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  have hq := hS.core.io.setE (coreSch_wf _ _ (by decide) (by decide)) hS.core.eb1 e x he hx m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ 100 → S.cs ≠ 105 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [100] [105] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {VR : Mem → Word → ν → Prop} {M₀ : Std.HashMap (κ × Word) ν} {t te : Std.HashMap κ ν}, S.WF →
      VConst VR → S.arr ≠ 100 → S.cs ≠ 105 → ModeR S K VR m M₀ eb t te →
      ModeR S K VR m' M₀ eb t te :=
    fun hS' hV h1 h2 h => h.frame hS' hV (by simpa using h1) (by simpa using h2) hf
  have frv : ∀ {κ : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ)
      (mp : Std.HashMap κ EIdx), S.WF → S.arr ≠ 100 → S.cs ≠ 105 → MemoRV S K VH m mp →
      MemoRV S K VH m' mp :=
    fun S K mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [100] [105] (by simpa using h1) (by simpa using h2) m m' hf
        (vh_const m m') mp hR
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [100] [105] (by simp) (by simp) m m' hf a
        hS.arena.1), DerR.of_store _ _ _ (DerR.frameM [100] [105] m m' hf (by simp) a hS.arena.2) rfl⟩,
      ⟨mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wc,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wk,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wh,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.inf,
        hq,
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
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn⟩,
    by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩

/-- `defeqC` gains a verdict (copy of `CoreS.set_wh`, at `deSch`: array 101, `CTL` 106/107, key
`(a, genW b eb)`). -/
theorem CoreS.set_de {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (x y r : Word)
    (hx : HW x) (hy : HW y) (hs : msetG deSch m x (genW y eb) r = some m') :
    CoreS dn m' { a with caches := { a.caches with
        defeqC := a.caches.defeqC.insert (decE x, decE y) (decB r) } } vis fe
      { M with de := M.de.insert ((decE x, decE y), eb) (decB r) } eb ∧ StackKept m m' := by
  have hf : MemFrame [101] [107] m m' := msetG_frame deSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ r hs
  have hq := hS.core.de.setD (coreSch_wf _ _ (by decide) (by decide)) hS.core.eb1 x y r hx hy m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ 101 → S.cs ≠ 107 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [101] [107] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {VR : Mem → Word → ν → Prop} {M₀ : Std.HashMap (κ × Word) ν} {t te : Std.HashMap κ ν}, S.WF →
      VConst VR → S.arr ≠ 101 → S.cs ≠ 107 → ModeR S K VR m M₀ eb t te →
      ModeR S K VR m' M₀ eb t te :=
    fun hS' hV h1 h2 h => h.frame hS' hV (by simpa using h1) (by simpa using h2) hf
  have frv : ∀ {κ : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ)
      (mp : Std.HashMap κ EIdx), S.WF → S.arr ≠ 101 → S.cs ≠ 107 → MemoRV S K VH m mp →
      MemoRV S K VH m' mp :=
    fun S K mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [101] [107] (by simpa using h1) (by simpa using h2) m m' hf
        (vh_const m m') mp hR
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [101] [107] (by simp) (by simp) m m' hf a
        hS.arena.1), DerR.of_store _ _ _ (DerR.frameM [101] [107] m m' hf (by simp) a hS.arena.2) rfl⟩,
      ⟨mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wc,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wk,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wh,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.inf,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.io,
        hq,
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
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn⟩,
    by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩

/-- `KeptAll` across a `infer` memo insert (copy of `KeptAll.wh`). -/
theorem KeptAll.inf {M M' : ModeMaps} {eb : Word} (h : KeptAll M M' eb) (k : EIdx) (v : EIdx) :
    KeptAll M { M' with inf := M'.inf.insert (k, eb) v } eb := fun h0 => by
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := h h0
  refine ⟨a1, b1, c1, fun k' => ?_, e1, f1⟩
  rw [Std.HashMap.getElem?_insert]
  have : ¬ ((k, eb) == (k', (0 : Word))) = true := by simp [h0]
  simp only [this, Bool.false_eq_true, ↓reduceIte]; exact d1 k'

/-- `KeptAll` across a `infer_io` memo insert (copy of `KeptAll.wh`). -/
theorem KeptAll.io {M M' : ModeMaps} {eb : Word} (h : KeptAll M M' eb) (k : EIdx) (v : EIdx) :
    KeptAll M { M' with io := M'.io.insert (k, eb) v } eb := fun h0 => by
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := h h0
  refine ⟨a1, b1, c1, d1, fun k' => ?_, f1⟩
  rw [Std.HashMap.getElem?_insert]
  have : ¬ ((k, eb) == (k', (0 : Word))) = true := by simp [h0]
  simp only [this, Bool.false_eq_true, ↓reduceIte]; exact e1 k'

/-- `KeptAll` across a `defeq` memo insert (copy of `KeptAll.wh`). -/
theorem KeptAll.de {M M' : ModeMaps} {eb : Word} (h : KeptAll M M' eb) (k : EIdx × EIdx) (v : Bool) :
    KeptAll M { M' with de := M'.de.insert (k, eb) v } eb := fun h0 => by
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := h h0
  refine ⟨a1, b1, c1, d1, e1, fun k' => ?_⟩
  rw [Std.HashMap.getElem?_insert]
  have : ¬ ((k, eb) == (k', (0 : Word))) = true := by simp [h0]
  simp only [this, Bool.false_eq_true, ↓reduceIte]; exact f1 k'


/-! ## The twin's slots -/

section twin
variable (mode : ConLeche.CheckMode) (fe : IFEnv) (F : Nat) (d : Nat) (e x y : EIdx) (a : AState)

theorem knot_infer_hit (v : EIdx) (hm : a.caches.inferC[e]? = some v) :
    ((coreKnot mode fe id (F + 1)).infer d e).run a = .ok (v, a) := by
  simp [coreKnot, hm]; rfl

theorem knot_infer_miss (hm : a.caches.inferC[e]? = none) (v : EIdx) (a₁ : AState)
    (hb : (inferBody (coreKnot mode fe id F) fe d e).run a = .ok (v, a₁)) :
    ((coreKnot mode fe id (F + 1)).infer d e).run a =
      .ok (v, { a₁ with caches := { a₁.caches with inferC := a₁.caches.inferC.insert e v } }) := by
  simp [coreKnot, hm, StateT.run_bind, hb, inferSet]; rfl

theorem knot_inferIO_hit (v : EIdx) (hm : a.caches.inferIOC[e]? = some v) :
    ((coreKnot mode fe id (F + 1)).inferIO d e).run a = .ok (v, a) := by
  simp [coreKnot, hm]; rfl

theorem knot_inferIO_miss (hm : a.caches.inferIOC[e]? = none) (v : EIdx) (a₁ : AState)
    (hb : (inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id F)) fe d e).run a = .ok (v, a₁)) :
    ((coreKnot mode fe id (F + 1)).inferIO d e).run a =
      .ok (v, { a₁ with caches := { a₁.caches with
        inferIOC := a₁.caches.inferIOC.insert e v } }) := by
  simp [coreKnot, hm, StateT.run_bind, hb, inferIOSet]; rfl

theorem knot_defeq_hit (v : Bool) (hm : a.caches.defeqC[(x, y)]? = some v) :
    ((coreKnot mode fe id (F + 1)).defeq d x y).run a = .ok (v, a) := by
  simp [coreKnot, hm]; rfl

theorem knot_defeq_miss (hm : a.caches.defeqC[(x, y)]? = none) (v : Bool) (a₁ : AState)
    (hb : (defeqBody mode (coreKnot mode fe id F) fe d x y).run a = .ok (v, a₁)) :
    ((coreKnot mode fe id (F + 1)).defeq d x y).run a =
      .ok (v, { a₁ with caches := { a₁.caches with
        defeqC := a₁.caches.defeqC.insert (x, y) v } }) := by
  simp [coreKnot, hm, StateT.run_bind, hb, defeqSet]; rfl

end twin

/-! ## The bodies' specs (hypotheses of the slot theorems) -/

/-- `infer_body(mode, vis, d, e)` refines `inferBody` at the knot one level down, at every
`F ≥ n` (the shape of `WhnfLoopSpec`). -/
def InferBodySpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → SlotPre s₀ a₀ dn vis fe MM eb mode → HW e →
    KnotUpTo p n →
    CoreSpec p n "infer_body" [mode, vis, d, e]
      (inferBody (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decH s₀ a₀ dn vis fe MM eb

/-- `infer_body_io(mode, vis, d, e)` refines `inferBodyIO` at the io view of the knot one level
down. -/
def InferIOBodySpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → SlotPre s₀ a₀ dn vis fe MM eb mode → HW e →
    KnotUpTo p n →
    CoreSpec p n "infer_body_io" [mode, vis, d, e]
      (inferBodyIO (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE e)) decH
      s₀ a₀ dn vis fe MM eb

/-- `defeq_body(mode, vis, d, a, b)` refines `defeqBody` at the knot one level down. -/
def DefeqBodySpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d x y : Word), n ≤ F → SlotPre s₀ a₀ dn vis fe MM eb mode → HW x →
    HW y → KnotUpTo p n →
    CoreSpec p n "defeq_body" [mode, vis, d, x, y]
      (defeqBody (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE x) (decE y))
      decBool s₀ a₀ dn vis fe MM eb

/-! ## The slots refine the knot's slots -/

section slots
variable (p : Prog) (hp : KnotProg p)

include hp in
/-- **`infer` refines the knot's `infer` slot**: `InferSlot p (n + 1)` from `infer_body`'s spec
at L-fuel `n` and `KnotUpTo p n`. -/
@[refines_part ConRon.Arena.coreKnot "infer"]
theorem infer_refines (n : Nat) (hk : KnotUpTo p n) (hb : InferBodySpec p n) :
    InferSlot p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hs he
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (infer_spec p hp n s₀ mode vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  rw [ebKey_eq mode eb hs.eb_mode] at hW
  unfold memoSlotW at hW
  by_cases h0 : mfindG inSch s.mem e (genW 0 eb) = []
  · simp [h0] at hW
  rw [if_neg h0] at hW
  have hf := hS.core.inf.findE hS.core.eb1 e he h0
  by_cases h1 : (mfindG inSch s.mem e (genW 0 eb)).headD 0 ≠ 0
  · rw [if_pos h1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _
      (knot_infer_hit _ fe F' d.toNat _ a₀ _ (hf.1 h1).1)
    refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact (hf.1 h1).2⟩
    rw [hst', ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
  rw [if_neg h1] at hW
  have hmiss := hf.2 (by simpa using h1)
  cases hcall : callW p n "infer_body" [mode, vis, d, e] s.mem with
  | none => simp [hcall] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  simp only [hcall] at hW
  have hbody := hb F' s a₀ dn vis fe MM eb mode d e (by omega) hs he hk
  obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW hbody hcall
  cases hset : msetG inSch m₁ e (genW 0 eb) (r₁.headD 0) with
  | none => rw [hset] at hW; cases hW
  | some m₂ =>
  rw [hset] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  obtain ⟨hS₂, hSt₂⟩ := hS₁.set_in e (r₁.headD 0) he hrw hset
  have hrun := knot_infer_miss _ fe F' d.toNat _ a₀ hmiss _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok', ?_, by rw [hres', hres]; simp only [decH, hr],
    by unfold ResH; rw [← hr]; exact hrw⟩
  rw [hst', ← hm, hres]
  exact ⟨_, hS₂, hK₁.inf _ _, hSt₁.trans hSt₂⟩

end slots

end L.Arena
