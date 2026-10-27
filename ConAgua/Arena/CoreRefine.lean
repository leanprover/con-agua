import ConAgua.Arena.ScratchRefine
import ConAgua.Census.Attr
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The core tier's primitives under `CoreR`

`Tiers.lean`'s `CoreRM m c M G g` relates the nine L caches (`CoreCaches.lean`) to the twin's
`Caches`. This file has what the core's L code needs of it:

* `flush_caches()` refines `flushCaches` under `CheckR` (`flushCaches_refinesC`);
* a probe of a mode memo at the eager bit is the twin's lookup (`ModeR.findE`, `ModeR.findD`), a
  `find; put` is its insert and keeps the other bank (`ModeR.setE`);
* the same for the three constant caches (`MemoRV … VH` directly: `memoRV_findP`, `findR`);
* the whole tier across one memo's `find; put` (`CoreRM.set_wc`, …): the other eight memos and the
  bank words by their frames.

The second key word at eager bit `eb` is `genW k2 eb = k2 ||| eb << 32`; for a one-handle key it
is `eb << 32` (`genW_zero`), which is what the L code computes from the mode word,
`((mode >> 1) & 1) << 32`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `flush_caches()` refines `flushCaches` -/

/-- The store and memo tiers do not read the caches. -/
theorem ArenaR.caches_irrel {m : Mem} {a : AState} (c : Caches) (hR : ArenaR m a) :
    ArenaR m { a with caches := c } :=
  ⟨hR.lit, hR.app, hR.sort, hR.const, hR.letE, hR.bvar, hR.fvar, hR.lam, hR.forallE, hR.proj,
    hR.zero, hR.succ, hR.max, hR.imax, hR.param, hR.ls, hR.nanon, hR.nstr, hR.nnum, hR.memos,
    hR.zeroHp, hR.paramHp, hR.succHp, hR.maxHp, hR.imaxHp, hR.lsHp, hR.sortLp, hR.constLp, hR.fvarLp⟩

theorem ArenaD.caches_irrel {m : Mem} {a : AState} (c : Caches) (hD : ArenaD m a) :
    ArenaD m { a with caches := c } :=
  ⟨hD.1.caches_irrel c, DerR.of_store _ _ _ hD.2 rfl⟩

theorem flushCaches_run (a : AState) :
    flushCaches.run a = .ok ((), { a with caches := Caches.empty }) := rfl

/-- **`flush_caches()` refines `flushCaches`** under `CheckR`. -/
@[refines ConRon.Arena.flushCaches]
theorem flushCaches_refinesC (p : Prog) (hp : FlushProg p) (a₀ : AState) (n : Nat) (s₀ : St)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (hC : CheckR dn s₀.mem a₀ vis fe) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "flush_caches" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok flushCaches a₀ ∧
      CheckR dn s'.mem (AM.st flushCaches a₀) vis fe; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun (flushCaches_spec p hp n s₀)
  subst hs
  obtain ⟨hok', hst, -⟩ := AM.of_run_ok _ _ _ _ (flushCaches_run a₀)
  refine ⟨hloc, hok', ?_⟩
  rw [hst, hm]
  have hf := flushMem_frame s.mem
  exact ⟨ArenaD.caches_irrel _ ⟨ArenaR.frame_ext [] _ (by simp) flushCtl_ge _ _ hf _ hC.arena.1,
      DerR.frameM [] _ _ _ hf (by simp) _ hC.arena.2⟩,
    hC.core.flush hok,
    hC.pins.frame (.of_lt (k := 0) (by simp) (by decide)) hf,
    hC.env.frame (.of_lt (k := 0) (by simp) (by decide)) (.of_lt flushCtl_lt (by decide)) hf,
    hC.mode.frame hf (by simp [flushCtl]) (by simp [flushCtl])⟩

/-! ## The mode memos: probe and insert at the current generation -/

theorem genW_zero (g : Word) : genW 0 g = g <<< 32 := by simp [genW]

section modeE
variable {S : MemoSch} {m : Mem} {M : Std.HashMap (EIdx × Word) EIdx} {eb : Word}
  {t te : Std.HashMap EIdx EIdx}

/-- **A probe of a one-handle mode memo** at the eager bit `eb`: a hit is the twin field's entry
(a handle word), a miss its absence. -/
theorem ModeR.findE (h : ModeR S eKeyG VH m M eb t te) (heb : eb ≤ 1) (e : Word)
    (he : e.toNat < 2 ^ 32) (hr : mfindG S m e (genW 0 eb) ≠ []) :
    ((mfindG S m e (genW 0 eb)).headD 0 ≠ 0 →
      t[decE e]? = some (decE (mvG S m ((mfindG S m e (genW 0 eb)).tail.headD 0))) ∧
      (mvG S m ((mfindG S m e (genW 0 eb)).tail.headD 0)).toNat < 2 ^ 32) ∧
    ((mfindG S m e (genW 0 eb)).headD 0 = 0 → t[decE e]? = none) := by
  have hg : eb.toNat < 2 ^ 32 := by rw [UInt64.le_iff_toNat_le] at heb; simp at heb; omega
  have := bank_find S bmKey _ VH m M h.memo eb hg t h.cur e 0 ⟨he, rfl⟩ hr
  refine ⟨fun hh => ?_, this.2⟩
  obtain ⟨v, h1, h2, h3⟩ := this.1 hh
  exact ⟨h1.trans (congrArg some h2), h3⟩

/-- `genKey`'s decoding at a handle word and an eager bit. -/
theorem eKeyG_dk (e eb : Word) (_he : e.toNat < 2 ^ 32) (heb : eb ≤ 1) :
    eKeyG.dk e (genW 0 eb) = (decE e, eb) := by
  have hg : eb.toNat < 2 ^ 32 := by rw [UInt64.le_iff_toNat_le] at heb; simp at heb; omega
  show (bmKey.dk e (genW 0 eb &&& 0xFFFFFFFF), genW 0 eb >>> 32) = _
  rw [genW_lo 0 eb (by decide), genW_hi 0 eb (by decide) hg]; rfl

/-- **A `find; put` of a one-handle mode memo** at the eager bit `eb` is the twin field's insert;
the stored eager table is another bank and stays. -/
theorem ModeR.setE (hS : S.WF) (h : ModeR S eKeyG VH m M eb t te) (heb : eb ≤ 1) (e r : Word)
    (he : e.toNat < 2 ^ 32) (hr : r.toNat < 2 ^ 32) (m' : Mem)
    (hs : msetG S m e (genW 0 eb) r = some m') :
    ModeR S eKeyG VH m' (M.insert (decE e, eb) (decE r)) eb (t.insert (decE e) (decE r)) te := by
  have hok : eKeyG.ok e (genW 0 eb) := by
    show bmKey.ok e (genW 0 eb &&& 0xFFFFFFFF); rw [genW_lo 0 eb (by decide)]; exact ⟨he, rfl⟩
  have hR := memoRV_set S hS eKeyG VH (fun _ _ _ _ _ h => h) m M h.memo e (genW 0 eb) r hok
    (decE r) ⟨rfl, hr⟩ m' hs
  rw [eKeyG_dk e eb he heb] at hR
  refine ⟨hR, bank_set M eb t h.cur _ _, fun h0 => ?_, h.empty⟩
  exact bank_other M eb 1 te (h.stored h0) (by rw [h0]; decide) _ _

end modeE

section modeD
variable {S : MemoSch} {m : Mem} {M : Std.HashMap ((EIdx × EIdx) × Word) Bool} {eb : Word}
  {t te : Std.HashMap (EIdx × EIdx) Bool}

/-- A probe of `defeqC` at the eager bit. -/
theorem ModeR.findD (h : ModeR S dKeyG VB m M eb t te) (heb : eb ≤ 1) (a b : Word)
    (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) (hr : mfindG S m a (genW b eb) ≠ []) :
    ((mfindG S m a (genW b eb)).headD 0 ≠ 0 →
      t[(decE a, decE b)]? = some (decB (mvG S m ((mfindG S m a (genW b eb)).tail.headD 0)))) ∧
    ((mfindG S m a (genW b eb)).headD 0 = 0 → t[(decE a, decE b)]? = none) := by
  have hg : eb.toNat < 2 ^ 32 := by rw [UInt64.le_iff_toNat_le] at heb; simp at heb; omega
  have := bank_find S pairKey _ VB m M h.memo eb hg t h.cur a b ⟨ha, hb⟩ hr
  refine ⟨fun hh => ?_, this.2⟩
  obtain ⟨v, h1, h2⟩ := this.1 hh
  exact h1.trans (congrArg some h2)

end modeD

/-! ## The constant caches -/

/-- A probe of a pair-keyed constant cache (`constTyC`, `constValC`). -/
theorem memoRV_findP {k₁ k₂ : IdxKind} {S : MemoSch} {m : Mem}
    {t : Std.HashMap (Idx k₁ × Idx k₂) EIdx} (h : MemoRV S pairKey VH m t) (x y : Word)
    (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) (hr : mfindG S m x y ≠ []) :
    ((mfindG S m x y).headD 0 ≠ 0 →
      t[((decI x : Idx k₁), (decI y : Idx k₂))]? = some (decE (mvG S m ((mfindG S m x y).tail.headD 0))) ∧
      (mvG S m ((mfindG S m x y).tail.headD 0)).toNat < 2 ^ 32) ∧
    ((mfindG S m x y).headD 0 = 0 → t[((decI x : Idx k₁), (decI y : Idx k₂))]? = none) := by
  refine ⟨fun hh => ?_, fun hh => memoRV_miss S pairKey VH m t h x y ⟨hx, hy⟩ hr hh⟩
  obtain ⟨v, h1, h2, h3⟩ := memoRV_hit S pairKey VH m t h x y hr hh ⟨hx, hy⟩
  exact ⟨h1.trans (congrArg some h2), h3⟩

/-- A probe of `ruleRhsC`. -/
theorem memoRV_findR {S : MemoSch} {m : Mem} {t : Std.HashMap (NIdx × NIdx × LsIdx) EIdx}
    (h : MemoRV S rrKey VH m t) (x y : Word) (hx : x.toNat < 2 ^ 32)
    (hr : mfindG S m x y ≠ []) :
    ((mfindG S m x y).headD 0 ≠ 0 →
      t[rrKey.dk x y]? = some (decE (mvG S m ((mfindG S m x y).tail.headD 0))) ∧
      (mvG S m ((mfindG S m x y).tail.headD 0)).toNat < 2 ^ 32) ∧
    ((mfindG S m x y).headD 0 = 0 → t[rrKey.dk x y]? = none) := by
  refine ⟨fun hh => ?_, fun hh => memoRV_miss S rrKey VH m t h x y hx hr hh⟩
  obtain ⟨v, h1, h2, h3⟩ := memoRV_hit S rrKey VH m t h x y hr hh hx
  exact ⟨h1.trans (congrArg some h2), h3⟩

/-- `rrKey`'s second word for a constructor and a level list. -/
theorem rrKey_dk (r c u : Word) (hc : c.toNat < 2 ^ 32) (hu : u.toNat < 2 ^ 32) :
    rrKey.dk r (c ||| (u <<< 32)) = ((decI r : NIdx), (decI c : NIdx), (decI u : LsIdx)) := by
  simp only [rrKey]
  rw [show c ||| (u <<< 32) = genW c u from rfl, genW_lo c u hc, genW_hi c u hc hu]

end L.Arena
