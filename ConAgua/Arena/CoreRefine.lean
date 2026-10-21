import ConAgua.Arena.Tiers
import ConAgua.Arena.ScratchRefine
import ConRon.Arena.Core
import ConAgua.Census.Attr

/-!
# The core tier's primitives under `CoreR`

`Tiers.lean`'s `CoreRM m c M G g` relates the nine L caches (`CoreCaches.lean`) to the twin's
`Caches`. This file has what the core's L code needs of it:

* `flush_caches()` refines `flushCaches` under `CheckR` (`flushCaches_refinesC`);
* a probe of a mode memo at the current generation is the twin's lookup (`ModeR.findE`,
  `ModeR.findD`), a `find; put` is its insert and keeps the other generations' banks
  (`ModeR.setE`, `ModeR.setD`, `Kept`);
* the same for the three constant caches (`MemoRG` directly: `ct`, `cv`, `rr`);
* the whole tier across one memo's `find; put` (`CoreRM.set_wc`, …): the other eight memos and the
  bank words by their frames.

The second key word at generation `g` is `genW k2 g = k2 ||| g << 32`; for a one-handle key it is
`g << 32` (`genW_zero`), which is what the L code computes from `CTL[115]`.
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
    hR.zero, hR.succ, hR.max, hR.imax, hR.param, hR.ls, hR.nanon, hR.nstr, hR.nnum, hR.memos⟩

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
    hC.env.frame (.of_lt (k := 0) (by simp) (by decide)) (.of_lt flushCtl_lt (by decide)) hf⟩

/-! ## The mode memos: probe and insert at the current generation -/

theorem genW_zero (g : Word) : genW 0 g = g <<< 32 := by simp [genW]

/-- The other generations' banks are kept: an insert at `g` (or a run that only inserts at `g`
and above `G`) leaves every generation `g' ≤ G`, `g' ≠ g` alone. -/
def Kept {κ ν : Type} [BEq κ] [Hashable κ] (M M' : Std.HashMap (κ × Word) ν) (G g : Word) : Prop :=
  ∀ (k : κ) (g' : Word), g' ≤ G → g' ≠ g → M'[(k, g')]? = M[(k, g')]?

theorem Kept.refl {κ ν : Type} [BEq κ] [Hashable κ] (M : Std.HashMap (κ × Word) ν) (G g : Word) :
    Kept M M G g := fun _ _ _ _ => rfl

theorem Kept.trans {κ ν : Type} [BEq κ] [Hashable κ] {M₁ M₂ M₃ : Std.HashMap (κ × Word) ν}
    {G g : Word} (h₁ : Kept M₁ M₂ G g) (h₂ : Kept M₂ M₃ G g) : Kept M₁ M₃ G g :=
  fun k g' h1 h2 => (h₂ k g' h1 h2).trans (h₁ k g' h1 h2)

theorem Kept.insert {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] (M : Std.HashMap (κ × Word) ν)
    (G g : Word) (k : κ) (v : ν) : Kept M (M.insert (k, g) v) G g := by
  intro k' g' _ hne
  rw [Std.HashMap.getElem?_insert]
  have : ¬ ((k, g) == (k', g')) = true := by simp [Ne.symm hne]
  simp [this]

section modeE
variable {S : MemoSch} {m : Mem} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word}
  {t : Std.HashMap EIdx EIdx}

/-- **A probe of a one-handle mode memo** at the current generation: a hit is the twin table's
entry, a miss its absence. -/
theorem ModeR.findE (h : ModeR S eKeyG decEV m M G g t) (hB : BankW BANKC m G g) (e : Word)
    (he : e.toNat < 2 ^ 32) (hr : mfindG S m e (genW 0 g) ≠ []) :
    ((mfindG S m e (genW 0 g)).headD 0 ≠ 0 →
      t[decE e]? = some (decE (mvG S m ((mfindG S m e (genW 0 g)).tail.headD 0)))) ∧
    ((mfindG S m e (genW 0 g)).headD 0 = 0 → t[decE e]? = none) := by
  have hg : g.toNat < 2 ^ 32 := by
    obtain ⟨-, -, hgG, hGl, -⟩ := hB; rw [UInt64.le_iff_toNat_le] at hgG; omega
  have := bank_find S bmKey _ (fun _ w v => v = decEV w) m M h.memo g hg t h.bank e 0 ⟨he, rfl⟩ hr
  refine ⟨fun hh => ?_, this.2⟩
  obtain ⟨v, h1, h2⟩ := this.1 hh
  exact h1.trans (congrArg some h2)

/-- **A `find; put` of a one-handle mode memo** at the current generation is the twin table's
insert; the map grows by one entry at `g`. -/
theorem ModeR.setE (hS : S.WF) (hc : S.cs + 1 ≠ BANKC ∧ S.cs + 1 ≠ BANKC + 1)
    (h : ModeR S eKeyG decEV m M G g t) (hB : BankW BANKC m G g) (e r : Word)
    (he : e.toNat < 2 ^ 32) (m' : Mem) (hs : msetG S m e (genW 0 g) r = some m') :
    ModeR S eKeyG decEV m' (M.insert (decE e, g) (decE r)) G g (t.insert (decE e) (decE r)) ∧
      BankW BANKC m' G g := by
  have := bank_put S hS bmKey _ (fun _ w v => v = decEV w) (vstable_eq S decEV) BANKC hc m M
    h.memo G g hB h.fresh t h.bank e 0 r ⟨he, rfl⟩ (decE r) rfl m' hs
  exact ⟨⟨this.1, this.2.1, this.2.2.1⟩, this.2.2.2⟩

end modeE

section modeD
variable {S : MemoSch} {m : Mem} {M : Std.HashMap ((EIdx × EIdx) × Word) Bool} {G g : Word}
  {t : Std.HashMap (EIdx × EIdx) Bool}

/-- A probe of `defeqC` at the current generation. -/
theorem ModeR.findD (h : ModeR S dKeyG decB m M G g t) (hB : BankW BANKC m G g) (a b : Word)
    (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) (hr : mfindG S m a (genW b g) ≠ []) :
    ((mfindG S m a (genW b g)).headD 0 ≠ 0 →
      t[(decE a, decE b)]? = some (decB (mvG S m ((mfindG S m a (genW b g)).tail.headD 0)))) ∧
    ((mfindG S m a (genW b g)).headD 0 = 0 → t[(decE a, decE b)]? = none) := by
  have hg : g.toNat < 2 ^ 32 := by
    obtain ⟨-, -, hgG, hGl, -⟩ := hB; rw [UInt64.le_iff_toNat_le] at hgG; omega
  have := bank_find S pairKey _ (fun _ w v => v = decB w) m M h.memo g hg t h.bank a b ⟨ha, hb⟩ hr
  refine ⟨fun hh => ?_, this.2⟩
  obtain ⟨v, h1, h2⟩ := this.1 hh
  exact h1.trans (congrArg some h2)

/-- A `find; put` of `defeqC` at the current generation. -/
theorem ModeR.setD (hS : S.WF) (hc : S.cs + 1 ≠ BANKC ∧ S.cs + 1 ≠ BANKC + 1)
    (h : ModeR S dKeyG decB m M G g t) (hB : BankW BANKC m G g) (a b r : Word)
    (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) (m' : Mem)
    (hs : msetG S m a (genW b g) r = some m') :
    ModeR S dKeyG decB m' (M.insert ((decE a, decE b), g) (decB r)) G g
        (t.insert (decE a, decE b) (decB r)) ∧ BankW BANKC m' G g := by
  have := bank_put S hS pairKey _ (fun _ w v => v = decB w) (vstable_eq S decB) BANKC hc m M
    h.memo G g hB h.fresh t h.bank a b r ⟨ha, hb⟩ (decB r) rfl m' hs
  exact ⟨⟨this.1, this.2.1, this.2.2.1⟩, this.2.2.2⟩

end modeD

/-! ## The constant caches -/

/-- A probe of a pair-keyed constant cache (`constTyC`, `constValC`). -/
theorem memoRG_findP {k₁ k₂ : IdxKind} {S : MemoSch} {m : Mem}
    {t : Std.HashMap (Idx k₁ × Idx k₂) EIdx} (h : MemoRG S pairKey decEV m t) (x y : Word)
    (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) (hr : mfindG S m x y ≠ []) :
    ((mfindG S m x y).headD 0 ≠ 0 →
      t[((decI x : Idx k₁), (decI y : Idx k₂))]? = some (decE (mvG S m ((mfindG S m x y).tail.headD 0)))) ∧
    ((mfindG S m x y).headD 0 = 0 → t[((decI x : Idx k₁), (decI y : Idx k₂))]? = none) :=
  ⟨fun hh => memoRG_hit S pairKey decEV m t h x y hr hh ⟨hx, hy⟩,
    fun hh => memoRG_miss S pairKey decEV m t h x y ⟨hx, hy⟩ hr hh⟩

/-- A probe of `ruleRhsC`. -/
theorem memoRG_findR {S : MemoSch} {m : Mem} {t : Std.HashMap (NIdx × NIdx × LsIdx) EIdx}
    (h : MemoRG S rrKey decEV m t) (x y : Word) (hx : x.toNat < 2 ^ 32)
    (hr : mfindG S m x y ≠ []) :
    ((mfindG S m x y).headD 0 ≠ 0 →
      t[rrKey.dk x y]? = some (decE (mvG S m ((mfindG S m x y).tail.headD 0)))) ∧
    ((mfindG S m x y).headD 0 = 0 → t[rrKey.dk x y]? = none) :=
  ⟨fun hh => memoRG_hit S rrKey decEV m t h x y hr hh hx,
    fun hh => memoRG_miss S rrKey decEV m t h x y hx hr hh⟩

/-- `rrKey`'s second word for a constructor and a level list. -/
theorem rrKey_dk (r c u : Word) (hc : c.toNat < 2 ^ 32) (hu : u.toNat < 2 ^ 32) :
    rrKey.dk r (c ||| (u <<< 32)) = ((decI r : NIdx), (decI c : NIdx), (decI u : LsIdx)) := by
  simp only [rrKey]
  rw [show c ||| (u <<< 32) = genW c u from rfl, genW_lo c u hc, genW_hi c u hc hu]

end L.Arena
