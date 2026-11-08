module

public import ConAgua.Arena.WhnfDeltaRefine
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.DerRel
import ConAgua.Arena.PinsNatOp
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.L.LocNF
import ConAgua.L.ModelGen
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.StoreDenIntern
import all ConAgua.Arena.WhnfDelta
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.NatAdd
import all ConAgua.Arena.Refine
import all ConAgua.Arena.Store

@[expose] public section

/-!
# δ and `Nat` literals: proofs of `WhnfDelta.lean`'s specs, part 2 (`raw_nat_lit` … `unfold_definition`)

Split from `WhnfDeltaRefine.lean`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `raw_nat_lit` -/

/-- The model of `raw_nat_lit`: `(flag, off, cnt, memory)`. -/
l_model rawNatLit_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.rawNatLit ↦ rawNatLitW tuple]
  specs [callW_spec p n "pin_at", callW_spec p n "pin_word"]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] gen 30


theorem rdW_ctl_top' (m : Mem) : rdW (m.arr64 CTL) 0 = m.top := by
  simp [rdW, Mem.top]

/-- **A `lit` node past the view checks**: the kind word `0` says `natVal`, with the record's
slice; any other kind says `strVal`. -/
theorem view_lit_nat (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h LIT) (hg : tagW h = 8) :
    (tfld m LIT (tierW h) (idxW h) 0 = 0 →
      ∃ N, a.store.view (decE h) = some (.lit (.natVal N)) ∧ NatRec m (tierW h) (idxW h) N) ∧
    (tfld m LIT (tierW h) (idxW h) 0 ≠ 0 →
      ∃ s, a.store.view (decE h) = some (.lit (.strVal s))) := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h litCS RecRel (·.lits) _ hR.lit.2 hv.2
  have hview : ∀ l, k = ⟨l⟩ → a.store.view (decE h) = some (.lit l) := by
    intro l hl
    rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk, hl]
    rfl
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · simp only [RecRel_natVal] at hkr
    exact ⟨fun _ => ⟨N, hview _ rfl, hkr⟩, fun hne => absurd hkr.1 hne⟩
  · simp only [RecRel_strVal, StrRec] at hkr
    exact ⟨fun h0 => absurd (hkr.1.symm.trans h0) (by decide), fun _ => ⟨s, hview _ rfl⟩⟩

/-- The result of a `raw_nat_lit` word triple, as the twin's option. -/
def rawDec (m : Mem) (r : List Word) : Option Nat :=
  if r.headD 0 = 0 then none
  else some (pv (vpool m) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat)

/-- The postcondition of a `raw_nat_lit` run. -/
def RawOut (m : Mem) (a₀ : AState) (h : Word) (r : List Word) : Prop :=
  (rawNatLit? (decE h)).run a₀ = .ok (rawDec m r, a₀) ∧ ResH r ∧
  (r.headD 0 ≠ 0 → SliceOK m (r.tail.headD 0) (r.tail.tail.headD 0) ∧
    Norm (vpool m) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat)

theorem RawOut.none {m : Mem} {a₀ : AState} {h : Word} {r : List Word}
    (hrun : (rawNatLit? (decE h)).run a₀ = .ok (none, a₀)) (hr0 : r.headD 0 = 0) :
    RawOut m a₀ h r :=
  ⟨by unfold rawDec; rw [ite_eq_left hr0]; exact hrun, by unfold ResH HW; rw [hr0]; decide,
         fun hne => absurd hr0 hne⟩

theorem rawNatLit_run_other {a : AState} {h : EIdx} {v : ENodeView} (hv : a.store.view h = some v)
    (hl : ∀ N, v ≠ .lit (.natVal N)) (hc : ∀ c us, v ≠ .const c us) :
    (rawNatLit? h).run a = .ok (none, a) := by
  simp only [rawNatLit?, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  cases v with
  | lit l =>
    cases l with
    | natVal N => exact absurd rfl (hl N)
    | strVal s => rfl
  | const c us => exact absurd rfl (hc c us)
  | _ => rfl

theorem rawNatLit_run_lit {a : AState} {h : EIdx} {N : Nat}
    (hv : a.store.view h = some (.lit (.natVal N))) :
    (rawNatLit? h).run a = .ok (some N, a) := by
  simp only [rawNatLit?, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; rfl

theorem rawNatLit_run_const {m : Mem} {a : AState} {h : EIdx} {c : NIdx} {us : LsIdx}
    (hP : PinsFull m a.pins) (hv : a.store.view h = some (.const c us)) :
    (rawNatLit? h).run a = .ok (if c == decI (pinW m 3) && us == decI (pinW m 52) then some 0
      else none, a) := by
  simp only [rawNatLit?, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, emptyLevels,
    pinEmptyLevels_run hP, pinNatZero_run hP]; rfl


theorem view_other (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (c : TRec) (hv : viewOK m h c)
    (hcg : (tagW h = 0 ∧ c = BVAR) ∨ (tagW h = 1 ∧ c = FVAR) ∨ (tagW h = 2 ∧ c = SORT) ∨
      (tagW h = 5 ∧ c = LAM) ∨ (tagW h = 6 ∧ c = FORALL) ∨
      (tagW h = 7 ∧ c = LET) ∨ (tagW h = 9 ∧ c = PROJ)) :
    ∃ v, a.store.view (decE h) = some v ∧ (∀ N, v ≠ .lit (.natVal N)) ∧
      (∀ c us, v ≠ .const c us) := by
  rcases hcg with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact ⟨_, view_bvar m a hR h hh hv g, fun N => nofun, fun c us => nofun⟩
  · obtain ⟨i, ty, hw⟩ := view_fvar m a hR h hh hv g
    exact ⟨_, hw, fun N => nofun, fun c us => nofun⟩
  · obtain ⟨u, hw⟩ := view_sort m a hR h hh hv g
    exact ⟨_, hw, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_lam m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_forall m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_let m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_proj m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩

theorem rawSimple {dn : NIdx → Option ConLeche.Name} {m : Mem} {a₀ : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a₀ vis fe M eb) {h : Word} (hh : HW h)
    (c : TRec) (hsc : ¬(tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hb : ¬ tcnt m c (tierW h) ≤ idxW h)
    (hcg : (tagW h = 0 ∧ c = BVAR) ∨ (tagW h = 1 ∧ c = FVAR) ∨ (tagW h = 2 ∧ c = SORT) ∨
      (tagW h = 5 ∧ c = LAM) ∨ (tagW h = 6 ∧ c = FORALL) ∨
      (tagW h = 7 ∧ c = LET) ∨ (tagW h = 9 ∧ c = PROJ))
    (r : List Word) (hr : r.headD 0 = 0) : RawOut m a₀ h r := by
  obtain ⟨v, hv, hl, hc⟩ := view_other m a₀ hS.arena.base h hh c ⟨hsc, by simpa using hb⟩ hcg
  exact RawOut.none (rawNatLit_run_other hv hl hc) hr

/-- `rawSimple` at an `app` handle (its index is the wide one). -/
theorem rawSimpleA {dn : NIdx → Option ConLeche.Name} {m : Mem} {a₀ : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a₀ vis fe M eb) {h : Word} (hh : HW h)
    (hsc : ¬(tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hb : ¬ tcnt m APP (tierW h) ≤ idxA h) (g : tagW h = 4)
    (r : List Word) (hr : r.headD 0 = 0) : RawOut m a₀ h r :=
  RawOut.none (rawNatLit_run_other
    (view_app m a₀ hS.arena.base h hh ⟨hsc, by simpa using hb⟩ g).1 (fun N => nofun)
    (fun c us => nofun)) hr

section refs9
variable (p : Prog)

theorem callW_rawNatLit (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb h : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hh : HW h) (r : List Word) (m' : Mem)
    (hcall : callW p n "raw_nat_lit" [h] s₀.mem = some (r, m')) :
    m' = s₀.mem ∧ RawOut s₀.mem a₀ h r := by
  cases n with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (rawNatLit_spec p hp.toWhnfDeltaProg (n + 1) s₀ h) hcall
  rw [rawNatLitW.eq_2] at hW
  by_cases hsc : tierW h ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left hsc] at hW; cases hW
  rw [ite_eq_right hsc] at hW
  -- the tags whose arm only checks the bound
  have simple : ∀ (c : TRec) (g : Prop) [Decidable g], g →
      (g → (tagW h = 0 ∧ c = BVAR) ∨ (tagW h = 1 ∧ c = FVAR) ∨ (tagW h = 2 ∧ c = SORT) ∨
        (tagW h = 5 ∧ c = LAM) ∨ (tagW h = 6 ∧ c = FORALL) ∨
        (tagW h = 7 ∧ c = LET) ∨ (tagW h = 9 ∧ c = PROJ)) →
      (if tcnt s₀.mem c (tierW h) ≤ idxW h then none else
        some ((0 : Word), (0 : Word), (0 : Word), s₀.mem)) =
        some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem) →
      s'.mem = s₀.mem ∧ RawOut s₀.mem a₀ h r := by
    intro c g _ hg hcg hW'
    by_cases hb : tcnt s₀.mem c (tierW h) ≤ idxW h
    · rw [ite_eq_left hb] at hW'; cases hW'
    rw [ite_eq_right hb] at hW'
    simp only [Option.some.injEq, Prod.mk.injEq] at hW'
    obtain ⟨hf, -, -, hm⟩ := hW'
    exact ⟨hm.symm, rawSimple hC hh c hsc hb (hcg hg) r hf.symm⟩
  by_cases g0 : tagW h = 0
  · rw [ite_eq_left g0] at hW
    obtain ⟨h1, h2⟩ := simple BVAR _ g0 (fun _ => Or.inl ⟨g0, rfl⟩) hW
    exact ⟨h1, h2⟩
  rw [ite_eq_right g0] at hW
  by_cases g1 : tagW h = 1
  · rw [ite_eq_left g1] at hW
    obtain ⟨h1, h2⟩ := simple FVAR _ g1 (fun _ => Or.inr (Or.inl ⟨g1, rfl⟩)) hW
    exact ⟨h1, h2⟩
  rw [ite_eq_right g1] at hW
  by_cases g2 : tagW h = 2
  · rw [ite_eq_left g2] at hW
    obtain ⟨h1, h2⟩ := simple SORT _ g2 (fun _ => Or.inr (Or.inr (Or.inl ⟨g2, rfl⟩))) hW
    exact ⟨h1, h2⟩
  rw [ite_eq_right g2] at hW
  by_cases g3 : tagW h = 3
  · rw [ite_eq_left g3] at hW
    by_cases hb : tcnt s₀.mem CONST (tierW h) ≤ idxW h
    · rw [ite_eq_left hb] at hW; cases hW
    rw [ite_eq_right hb] at hW
    cases h1 : callW p n "pin_at" [2] s₀.mem with
    | none => rw [h1, rawNatLitW.k_pin_at.none] at hW; cases hW
    | some q₁ =>
    obtain ⟨r₁, m₁⟩ := q₁
    rw [h1, rawNatLitW.k_pin_at.arm1] at hW
    obtain ⟨hm1, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n s₀.mem 2 r₁ m₁ h1
    subst m₁
    cases h2 : callW p n "pin_word" [52] s₀.mem with
    | none => rw [h2, rawNatLitW.k_pin_word.none] at hW; cases hW
    | some q₂ =>
    obtain ⟨r₂, m₂⟩ := q₂
    rw [h2] at hW
    obtain ⟨hm2, -, hr₂⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₂ m₂ h2
    subst m₂
    simp only [show (2 : Word).toNat = 2 from rfl, show (52 : Word).toNat = 52 from rfl] at hr₁ hr₂
    have hvOK : viewOK s₀.mem h CONST := ⟨hsc, by simpa using hb⟩
    obtain ⟨n_, us_, hview, hn, hu, hnl, hul⟩ := view_const_words s₀.mem a₀ hC.arena.base h hh hvOK g3
    have hrun := rawNatLit_run_const hC.pins hview
    rw [hn, hu] at hrun
    have hbool : ((decI (tfld s₀.mem CONST (tierW h) (idxW h) 0) : NIdx) ==
            decI (pinW s₀.mem 3) &&
            (decI (tfld s₀.mem CONST (tierW h) (idxW h) 1) : LsIdx) ==
              decI (pinW s₀.mem 52)) =
        decide (tfld s₀.mem CONST (tierW h) (idxW h) 0 = r₁.headD 0 ∧
          tfld s₀.mem CONST (tierW h) (idxW h) 1 = r₂.headD 0) := by
      rw [decI_beq _ _ hnl (hC.pins.names_lt 2 (by decide)), decI_beq _ _ hul hC.pins.lv_lt.1,
        Bool.decide_and, hr₁, hr₂]
    rw [hbool] at hrun
    by_cases hcond : tfld s₀.mem CONST (tierW h) (idxW h) 0 = r₁.headD 0 ∧
        tfld s₀.mem CONST (tierW h) (idxW h) 1 = r₂.headD 0
    · rw [rawNatLitW.k_pin_word.arm1 _ _ _ _ _ _ hcond] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hf, ho, hcn, hm⟩ := hW
      have hpv : pv (vpool s₀.mem) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = 0 := by
        rw [← hcn]; rfl
      refine ⟨hm.symm, ?_, ?_, ?_⟩
      · unfold rawDec
        rw [ite_eq_right (by rw [← hf]; decide), hpv]
        simpa [hcond] using hrun
      · unfold ResH HW; rw [← hf]; decide
      · intro _
        refine ⟨?_, ?_⟩
        · rw [← ho, ← hcn, rdW_ctl_top']; exact SliceOK.top0 rfl
        · intro hpos; rw [← hcn] at hpos; simp at hpos
    · rw [rawNatLitW.k_pin_word.arm2 _ _ _ _ _ _ hcond] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hf, ho, hcn, hm⟩ := hW
      refine ⟨hm.symm, RawOut.none ?_ hf.symm⟩
      rw [decide_eq_false hcond] at hrun
      simpa only [Bool.false_eq_true, ↓reduceIte] using hrun
  rw [ite_eq_right g3] at hW
  by_cases g4 : tagW h = 4
  · rw [ite_eq_left g4] at hW
    by_cases hb : tcnt s₀.mem APP (tierW h) ≤ idxA h
    · rw [ite_eq_left hb] at hW; cases hW
    rw [ite_eq_right hb] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hf, -, -, hm⟩ := hW
    exact ⟨hm.symm, rawSimpleA hC hh hsc hb g4 r hf.symm⟩
  rw [ite_eq_right g4] at hW
  by_cases g5 : tagW h = 5
  · rw [ite_eq_left g5] at hW
    obtain ⟨h1, h2⟩ := simple LAM _ g5
      (fun _ => Or.inr (Or.inr (Or.inr (Or.inl ⟨g5, rfl⟩)))) hW
    exact ⟨h1, h2⟩
  rw [ite_eq_right g5] at hW
  by_cases g6 : tagW h = 6
  · rw [ite_eq_left g6] at hW
    obtain ⟨h1, h2⟩ := simple FORALL _ g6
      (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g6, rfl⟩))))) hW
    exact ⟨h1, h2⟩
  rw [ite_eq_right g6] at hW
  by_cases g7 : tagW h = 7
  · rw [ite_eq_left g7] at hW
    obtain ⟨h1, h2⟩ := simple LET _ g7
      (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g7, rfl⟩)))))) hW
    exact ⟨h1, h2⟩
  rw [ite_eq_right g7] at hW
  by_cases g8 : tagW h = 8
  · rw [ite_eq_left g8] at hW
    by_cases hb : tcnt s₀.mem LIT (tierW h) ≤ idxW h
    · rw [ite_eq_left hb] at hW; cases hW
    rw [ite_eq_right hb] at hW
    have hvOK : viewOK s₀.mem h LIT := ⟨hsc, by simpa using hb⟩
    obtain ⟨hk0, hk1⟩ := view_lit_nat s₀.mem a₀ hC.arena.base h hh hvOK g8
    by_cases hk : tfld s₀.mem LIT (tierW h) (idxW h) 0 = 0
    · rw [ite_eq_left hk] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hf, ho, hcn, hm⟩ := hW
      obtain ⟨N, hview, hnat⟩ := hk0 hk
      obtain ⟨-, hsl, hnorm, hpv, -⟩ := hnat
      refine ⟨hm.symm, ?_, ?_, ?_⟩
      · unfold rawDec
        rw [ite_eq_right (by rw [← hf]; decide), ← ho, ← hcn, hpv]
        exact rawNatLit_run_lit hview
      · unfold ResH HW; rw [← hf]; decide
      · intro _
        refine ⟨?_, ?_⟩
        · rw [← ho, ← hcn]; exact hsl.1
        · rw [← ho, ← hcn]; exact hnorm
    · rw [ite_eq_right hk] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hf, ho, hcn, hm⟩ := hW
      obtain ⟨s, hview⟩ := hk1 hk
      exact ⟨hm.symm, RawOut.none (rawNatLit_run_other hview (fun N => nofun) (fun c us => nofun))
        hf.symm⟩
  rw [ite_eq_right g8] at hW
  by_cases g9 : tagW h ≠ 9
  · rw [ite_eq_left g9] at hW; cases hW
  rw [ite_eq_right g9] at hW
  have g9' : tagW h = 9 := by simpa using g9
  obtain ⟨h1, h2⟩ := simple PROJ _ g9'
    (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨g9', rfl⟩)))))) hW
  exact ⟨h1, h2⟩

/-- **`raw_nat_lit` refines `rawNatLit?`**: the result is a flag and the literal's POOL slice
(`pv`), read-only. -/
@[refines ConRon.Arena.rawNatLit?]
theorem rawNatLit_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb h : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hh : HW h) :
    CoreSpec p n "raw_nat_lit" [h] (rawNatLit? (decE h))
      (fun r => if r.headD 0 = 0 then none
        else some (pv (vpool s₀.mem) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat))
      s₀ a₀ dn vis fe MM eb := by
  apply CoreSpec.of_call
  intro r m' hcall
  obtain ⟨rfl, hrun, hres, -⟩ := callW_rawNatLit p hp n s₀ a₀ dn vis fe MM eb h hC hh r m' hcall
  exact CRef.core (m' := s₀.mem) (CRef.pure hC _ hrun rfl hres)

end refs9


/-! ## `nat_lit_to_ctor` -/


/-- The model of `nat_lit_to_ctor`. -/
l_model natLitToCtor_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.natLitToCtor ↦ natLitToCtorW ]
  specs [callW_spec p n "pin_at", callW_spec p n "const_e", callW_spec p n "nat_pred_lit", callW_spec p n "mk_app"]
  grind [arena_grind] fold [tierW, idxW]
  finish [tierW, idxW] gen 30


/-! ## Frames of the `Nat` functions -/

theorem CoreS.of_nat {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (hD : ArenaD m' a') (hcpl : cpl a' = cpl a) (hf : MemFrame natA natC m m')
    (hv : ∀ x w, IsSC w → a'.store.view x = some w → a.store.view x = some w) (hP : PoolGrew m m') :
    CoreS dn m' a' vis fe M eb :=
  have hk : a'.caches = a.caches ∧ a'.pins = a.pins ∧ a'.store.lss = a.store.lss := by
    simpa only [cpl, Prod.mk.injEq] using hcpl
  hS.arena_frameD hD hcpl hf
    (fun b hb => by
      simp only [natA, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by decide)
    (fun b hb => by
      simp only [natA, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [natC, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [natC, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
    (hS.den.of_views hk.1 hk.2.1 hk.2.2 (hf.arr EREC (by simp [tier1, natA, POOL, POOL1, REC, SLOT, CREC, CSLOT, CLP, EREC]) (by decide))
      hv) (hmode := hS.mode.poolGrew hP)

theorem StackKept.of_nat_frame {m m' : Mem} (hf : MemFrame natA natC m m') (hP : PoolGrew m m') :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.arr SPN (by simp [tier1, natA, POOL, POOL1, REC, SLOT, CREC, CSLOT, CLP, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.ctl 136 (by simp [natC])
  exact ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn],
    BKept.of_frame hf (by decide) (by decide), hP⟩

theorem keeps_cpl_natPredArm (a : Nat) : Keeps cpl (natPredArm a) := by
  unfold natPredArm
  exact Keeps.bind (keeps_cpl_internLit _) (fun _ => Keeps.pure _)

section refs10
variable (p : Prog)

theorem callW_natFrame (hc : closedA p natA natC natFns = true) (f : FnName) (hf : f ∈ natFns)
    (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem)
    (h : callW p n f vs m = some (r, m')) : MemFrame natA natC m m' := by
  obtain ⟨s', rfl, hfr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (invoke_memFrame hc n hf vs ⟨m, Locals.init []⟩) h
  exact hfr.1

theorem natPredLit_inst (hp : WhnfDeltaProg' p) : InternSpec p ArenaD :=
  fun a₀ n s₀ o l hA hq hn hq0 => internLit_refinesD p hp.litHash' hp.limbsEq' hp.litMatch' hp.litFind'
    hp.litPush' hp.internLit a₀ n s₀ o l hA hq hn hq0

/-- The functions of `intern_lit`: they write the `lit` table only, never the pool. -/
def litFns : List FnName := ["intern_lit", "lit_hash", "limbs_eq", "lit_match", "lit_find", "lit_push"]

theorem litFns_closed : closedA storeProg [REC, tier1 REC, SLOT, tier1 SLOT] [2, 3] litFns = true := by decide +kernel

theorem WhnfDeltaProg'.litClosed (hp : WhnfDeltaProg' p) : closedA p [REC, tier1 REC, SLOT, tier1 SLOT] [2, 3] litFns = true :=
  closedW_of_agree litFns_closed (by
    intro f hf
    simp only [litFns, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp.internLit]; rfl
    · rw [hp.litHash']; rfl
    · rw [hp.limbsEq']; rfl
    · rw [hp.litMatch']; rfl
    · rw [hp.litFind']; rfl
    · rw [hp.litPush']; rfl)

/-- `intern_lit` under `ArenaD` and "the pool only grew since `m₀`". -/
theorem natPredLit_instP (hp : WhnfDeltaProg' p) (m₀ : Mem) :
    InternSpec p (fun m a => ArenaD m a ∧ PoolGrew m₀ m) := by
  intro a₀ n s₀ o l ⟨hA, hP⟩ hq hn hq0
  apply L.M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hD, hres⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun (natPredLit_inst p hp a₀ n s₀ o l hA hq hn hq0)
  obtain ⟨hfr, -⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_memFrame hp.litClosed n (f := "intern_lit") (by decide) [o, l] s₀)
  subst hs
  exact ⟨hloc, hok, ⟨hD, hP.trans (PoolGrew.of_frame hfr (by decide) (by decide))⟩, hres⟩

theorem callW_natPredLit (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb o cnt : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hs : SliceOK s₀.mem o cnt) (r : List Word) (m' : Mem)
    (h : callW p n "nat_pred_lit" [o, cnt] s₀.mem = some (r, m')) :
    AM.ok (natPredArm (pv (vpool s₀.mem) o.toNat cnt.toNat)) a₀ ∧
    CoreS dn m' (AM.st (natPredArm (pv (vpool s₀.mem) o.toNat cnt.toNat)) a₀) vis fe MM eb ∧
    AM.res (natPredArm (pv (vpool s₀.mem) o.toNat cnt.toNat)) a₀ = some (decE (r.headD 0)) ∧
    MemFrame natA natC s₀.mem m' ∧ PoolGrew s₀.mem m' := by
  obtain ⟨s', rfl, -, hok, ⟨hD, hP⟩, hres⟩ := triple_of_callW
    (natPredLit_refines p (fun m a => ArenaD m a ∧ PoolGrew s₀.mem m) (fun _ _ h => h.1.1.lit.1)
      (fun m m' a hA hg => ⟨ArenaD.grow m m' hg a hA.1, hA.2.trans (PoolGrew.of_grows hg)⟩)
      (natPredLit_instP p hp s₀.mem) hp.natLimb' hp.subBorrow'
      hp.natTrim' hp.natSub hp.predLit n s₀ a₀ ⟨hC.arena, PoolGrew.refl _⟩ o cnt hs hC.mode) h
  have hfr := callW_natFrame p hp.natClosed "nat_pred_lit" (by decide +kernel) n _ _ _ _ h
  exact ⟨hok, hC.of_nat hD (Keeps.run (keeps_cpl_natPredArm _) (AM.run_of_ok _ _ hok)) hfr
    (internE_pure_views (by rintro (⟨_, h⟩ | ⟨_, _, h⟩) <;> cases h) rfl _ (AM.run_of_ok _ _ hok)) hP,
    hres, hfr,
    hP⟩

end refs10


theorem natLitToConstructor_zero_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    (natLitToConstructor 0).run a = (constE (decI (pinW m 3))).run a := by
  simp only [natLitToConstructor, StateT.run_bind, pinNatZero_run h, except_ok_bind]

theorem natLitToConstructor_succ_run {m : Mem} {a a₁ a₂ a₃ : AState} (h : PinsFull m a.pins)
    (k : Nat) (sc l f : EIdx)
    (h1 : (constE (decI (pinW m 4))).run a = .ok (sc, a₁))
    (h2 : (internE (.lit (.natVal k))).run a₁ = .ok (l, a₂))
    (h3 : (internE (.app sc l)).run a₂ = .ok (f, a₃)) :
    (natLitToConstructor (k + 1)).run a = .ok (f, a₃) := by
  simp only [natLitToConstructor, StateT.run_bind, pinNatSucc_run h, except_ok_bind, h1, h2, h3]

theorem natPredArm_succ_run {a₁ a₂ : AState} {k : Nat} {x : EIdx}
    (h : (natPredArm (k + 1)).run a₁ = .ok (some x, a₂)) :
    (internE (.lit (.natVal k))).run a₁ = .ok (x, a₂) := by
  have e : (natPredArm (k + 1)).run a₁ =
      Except.map (fun q => (some q.1, q.2)) ((internE (.lit (.natVal k))).run a₁) := by
    simp only [natPredArm, Nat.add_sub_cancel, StateT.run_bind]
    cases (internE (.lit (.natVal k))).run a₁ <;> rfl
  rw [e] at h
  cases hh : (internE (.lit (.natVal k))).run a₁ with
  | error e => rw [hh] at h; cases h
  | ok q =>
    rw [hh] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨x', a'⟩ := q
    simp only at h1 h2
    rw [h1, h2]

section refs11
variable (p : Prog)

@[refines ConRon.Arena.natLitToConstructor]
theorem natLitToCtor_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb o cnt : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hs : SliceOK s₀.mem o cnt)
    (hnorm : Norm (vpool s₀.mem) o.toNat cnt.toNat) :
    CoreSpec p n "nat_lit_to_ctor" [o, cnt]
      (natLitToConstructor (pv (vpool s₀.mem) o.toNat cnt.toNat)) decH s₀ a₀ dn vis fe MM eb := by
  apply CoreSpec.of_call
  intro r m' hcall
  cases n with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (natLitToCtor_spec p hp.toWhnfDeltaProg (n + 1) s₀ o cnt) hcall
  by_cases hc0 : cnt = 0
  · rw [natLitToCtorW.arm1 _ _ _ _ _ hc0] at hW
    cases h1 : callW p n "pin_at" [2] s₀.mem with
    | none => rw [h1, natLitToCtorW.k_pin_at.none] at hW; cases hW
    | some q₁ =>
    obtain ⟨r₁, m₁⟩ := q₁
    rw [h1, natLitToCtorW.k_pin_at.arm1] at hW
    obtain ⟨hm1, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n s₀.mem 2 r₁ m₁ h1
    subst m₁
    have hnt : HW (r₁.headD 0) := by rw [hr₁]; exact hC.pins.names_lt 2 (by decide)
    cases h2 : callW p n "const_e" [r₁.headD 0] s₀.mem with
    | none => rw [h2, natLitToCtorW.k_const_e.none] at hW; cases hW
    | some q₂ =>
    obtain ⟨r₂, m₂⟩ := q₂
    rw [h2, natLitToCtorW.k_const_e.arm1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨hok, hS, hres, hfr, hhw⟩ := callW_constE p hp n s₀ a₀ dn vis fe MM eb _ hC hnt r₂ m₂ h2
    have hr₁' : r₁.headD 0 = pinW s₀.mem 3 := by
      simp only [show (2 : Word).toNat = 2 from rfl] at hr₁; exact hr₁
    rw [hr₁'] at hok hS hres
    have hpv : pv (vpool s₀.mem) o.toNat cnt.toNat = 0 := by subst hc0; rfl
    rw [hpv]
    rw [← hm]
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨hok', -, -⟩ := AM.of_run_ok _ _ _ _ ((natLitToConstructor_zero_run hC.pins).trans
        (AM.run_of_ok _ _ hok)); exact hok'
    · obtain ⟨-, hst', -⟩ := AM.of_run_ok _ _ _ _ ((natLitToConstructor_zero_run hC.pins).trans
        (AM.run_of_ok _ _ hok))
      rw [hst']; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.of_const_frame hfr⟩
    · obtain ⟨-, -, hres'⟩ := AM.of_run_ok _ _ _ _ ((natLitToConstructor_zero_run hC.pins).trans
        (AM.run_of_ok _ _ hok))
      rw [hres', hres]; simp only [decH, ← hr]
    · unfold ResH; rw [← hr]; exact hhw
  rw [natLitToCtorW.arm2 _ _ _ _ _ hc0] at hW
  have hpos : 0 < cnt.toNat := by
    rcases Nat.eq_zero_or_pos cnt.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hc0
    · exact h0
  obtain ⟨k, hk⟩ : ∃ k, pv (vpool s₀.mem) o.toNat cnt.toNat = k + 1 :=
    ⟨pv (vpool s₀.mem) o.toNat cnt.toNat - 1, by have := pv_pos_of_norm _ _ _ hnorm hpos; omega⟩
  rw [hk]
  cases h1 : callW p n "pin_at" [3] s₀.mem with
  | none => rw [h1, natLitToCtorW.k_pin_at_2.none] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1, natLitToCtorW.k_pin_at_2.arm1] at hW
  obtain ⟨hm1, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n s₀.mem 3 r₁ m₁ h1
  subst m₁
  have hnt : HW (r₁.headD 0) := by rw [hr₁]; exact hC.pins.names_lt 3 (by decide)
  cases h2 : callW p n "const_e" [r₁.headD 0] s₀.mem with
  | none => rw [h2, natLitToCtorW.k_const_e_2.none] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2, natLitToCtorW.k_const_e_2.arm1] at hW
  obtain ⟨hok, hS, hres, hfr, hhw⟩ := callW_constE p hp n s₀ a₀ dn vis fe MM eb _ hC hnt r₂ m₂ h2
  have hr₁' : r₁.headD 0 = pinW s₀.mem 4 := by
    simp only [show (3 : Word).toNat = 3 from rfl] at hr₁; exact hr₁
  rw [hr₁'] at hok hS hres
  have hPool : m₂.arr64 POOL = s₀.mem.arr64 POOL :=
    hfr.arr_eq POOL (by simp [tier1, CREC, CSLOT, CLP, POOL]) (by decide)
  have hPool1 : m₂.arr64 POOL1 = s₀.mem.arr64 POOL1 :=
    hfr.arr_eq POOL1 (by simp [tier1, CREC, CSLOT, CLP, POOL1]) (by decide)
  have hPt : m₂.ptop0 = s₀.mem.ptop0 :=
    ptop0_congr (hfr.arr_eq PT0 (by simp [tier1, CREC, CSLOT, CLP, PT0]) (by decide))
  have hPoolv := vpool_congr hPool hPool1
  have hPoolc := pcap_congr' hPool hPool1
  have hTop : m₂.top = s₀.mem.top := by
    rw [← rdW_ctl_top', ← rdW_ctl_top']; exact hfr.ctl 0 (by simp)
  have hs₂ : SliceOK m₂ o cnt := (SliceOK_congr _ _ hTop hPt).mpr hs
  cases h3 : callW p n "nat_pred_lit" [o, cnt] m₂ with
  | none => rw [h3, natLitToCtorW.k_nat_pred_lit.none] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3, natLitToCtorW.k_nat_pred_lit.arm1] at hW
  obtain ⟨hok3, hS3, hres3, hfr3, hP3⟩ := callW_natPredLit p hp n ⟨m₂, Locals.init []⟩ _ dn vis fe MM eb o cnt
    hS hs₂ r₃ m₃ h3
  rw [hPoolv, hk] at hok3 hS3 hres3
  cases h4 : callW p n "mk_app" [r₂.headD 0, r₃.headD 0] m₃ with
  | none => rw [h4, natLitToCtorW.k_const_e.none] at hW; cases hW
  | some q₄ =>
  obtain ⟨r₄, m₄⟩ := q₄
  rw [h4, natLitToCtorW.k_const_e.arm1] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  obtain ⟨hok4, hD4, hres4, hfr4, hhw4⟩ := callW_mkApp p hp.spine n ⟨m₃, Locals.init []⟩ _ hS3.arena
    (r₂.headD 0) (r₃.headD 0) r₄ m₄ h4
  -- the twin runs
  have e1 : (constE (decI (pinW s₀.mem 4))).run a₀ =
      .ok (decE (r₂.headD 0), AM.st (constE (decI (pinW s₀.mem 4))) a₀) := by
    rw [AM.run_of_ok _ _ hok, hres]; rfl
  have e2 : (internE (.lit (.natVal k))).run (AM.st (constE (decI (pinW s₀.mem 4))) a₀) =
      .ok (decE (r₃.headD 0), AM.st (natPredArm (k + 1)) (AM.st (constE (decI (pinW s₀.mem 4))) a₀)) :=
    natPredArm_succ_run (by rw [AM.run_of_ok _ _ hok3, hres3])
  have e3 : (internE (.app (decE (r₂.headD 0)) (decE (r₃.headD 0)))).run
      (AM.st (natPredArm (k + 1)) (AM.st (constE (decI (pinW s₀.mem 4))) a₀)) =
      .ok (decE (r₄.headD 0), AM.st (internE (.app (decE (r₂.headD 0)) (decE (r₃.headD 0))))
        (AM.st (natPredArm (k + 1)) (AM.st (constE (decI (pinW s₀.mem 4))) a₀))) := by
    rw [AM.run_of_ok _ _ hok4, hres4]
  have hz := natLitToConstructor_succ_run hC.pins k _ _ _ e1 e2 e3
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst', ← hm]
    refine ⟨MM, hS3.of_app hD4 (Keeps.run (keeps_cpl_internApp _ _) (AM.run_of_ok _ _ hok4)) hfr4,
      KeptAll.refl _ _, ?_⟩
    exact ((StackKept.of_const_frame hfr).trans (StackKept.of_nat_frame hfr3 hP3)).trans
      (StackKept.of_app_frame hfr4)
  · rw [hres', decH, ← hr]
  · unfold ResH; rw [← hr]; exact hhw4

end refs11


/-! ## `lit_to_ctor_if_nat` -/


/-- The model of `lit_to_ctor_if_nat`. -/
l_model litToCtorIfNat_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.litToCtorIfNat ↦ litToCtorIfNatW ]
  specs [callW_spec p n "nat_lit_stored", callW_spec p n "nat_lit_to_ctor"]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] gen 30


theorem litToCtor_run_notlit (fe : IFEnv) (a : AState) (h : Word) (hh : HW h) (hg : tagW h ≠ 8) :
    (litToCtorIfNat fe (decE h)).run a = .ok (decE h, a) := by
  have ht : ((decE h).tag == ETag.lit) = false := by rw [decE_lit_tag h hh]; simp [hg]
  simp [litToCtorIfNat, ht, StateT.run_pure]
  rfl

theorem litToCtor_run_str (fe : IFEnv) (a : AState) (h : Word) (hh : HW h) (hg : tagW h = 8)
    (s : String) (hv : a.store.view (decE h) = some (.lit (.strVal s))) :
    (litToCtorIfNat fe (decE h)).run a = .ok (decE h, a) := by
  have ht : ((decE h).tag == ETag.lit) = true := by rw [decE_lit_tag h hh]; simp [hg]
  simp [litToCtorIfNat, ht, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  rfl

theorem litToCtor_run_unsup (fe : IFEnv) (a a₁ : AState) (h : Word) (hh : HW h)
    (hg : tagW h = 8) (N : Nat) (hv : a.store.view (decE h) = some (.lit (.natVal N)))
    (hs : (natLitSupported fe).run a = .ok (false, a₁)) :
    (litToCtorIfNat fe (decE h)).run a = .ok (decE h, a₁) := by
  sorry

theorem litToCtor_run_sup (fe : IFEnv) (a a₁ a₂ : AState) (h : Word) (hh : HW h)
    (hg : tagW h = 8) (N : Nat) (hv : a.store.view (decE h) = some (.lit (.natVal N)))
    (hs : (natLitSupported fe).run a = .ok (true, a₁)) (x : EIdx)
    (hc : (natLitToConstructor N).run a₁ = .ok (x, a₂)) :
    (litToCtorIfNat fe (decE h)).run a = .ok (x, a₂) := by
  sorry

section refs12
variable (p : Prog)

@[refines ConRon.Arena.litToCtorIfNat]
theorem litToCtorIfNat_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb h : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hh : HW h) :
    CoreSpec p n "lit_to_ctor_if_nat" [vis, h] (litToCtorIfNat fe (decE h)) decH s₀ a₀ dn vis fe MM
      eb := by
  sorry

end refs12


/-! ## `const_val_at` -/

/-- `constValC` gains an entry (copy of `CoreS.set_wh`, at `cvSch`: array 103, `CTL` 110/111). -/
theorem CoreS.set_cv {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (nm us x : Word)
    (hn : HW nm) (hu : HW us) (hx : HW x) (hs : msetG cvSch m nm us x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        constValC := a.caches.constValC.insert (decI nm, decI us) (decE x) } } vis fe M eb ∧
      StackKept m m' := by
  have hf : MemFrame [(CV : TieredArray)] [111] m m' :=
    msetG_frame cvSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  have hq := memoRV_set cvSch (coreSch_wf _ _ (by decide) (by decide)) pairKey VH
    (fun _ _ _ _ _ h => h) m a.caches.constValC hS.core.cv nm us x ⟨hn, hu⟩ (decE x) ⟨rfl, hx⟩ m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ CV → S.cs ≠ 111 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [(CV : TieredArray)] [111] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {VR : Mem → Word → ν → Prop} {M₀ : Std.HashMap (κ × Word) ν} {t te : Std.HashMap κ ν}, S.WF →
      VConst VR → S.arr ≠ CV → S.cs ≠ 111 → ModeR S K VR m M₀ eb t te →
      ModeR S K VR m' M₀ eb t te :=
    fun hS' hV h1 h2 h => h.frame hS' hV (by simpa using h1) (by simpa using h2) hf
  have frv : ∀ {κ : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ)
      (mp : Std.HashMap κ EIdx), S.WF → S.arr ≠ CV → S.cs ≠ 111 → MemoRV S K VH m mp →
      MemoRV S K VH m' mp :=
    fun S K mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [(CV : TieredArray)] [111] (by simpa using h1) (by simpa using h2) m m' hf
        (vh_const m m') mp hR
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.arr SPN (by decide) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.ctl 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [(CV : TieredArray)] [111] (by decide) (by simp) m m' hf a
        hS.arena.base), DerR.of_store _ _ _ (DerR.frameM [(CV : TieredArray)] [111] m m' hf (by decide) a hS.arena.der) rfl⟩,
      ⟨mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wc,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wk,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wh,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.inf,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.io,
        mr (coreSch_wf _ _ (by decide) (by decide)) vb_const (by decide) (by decide) hS.core.de,
        hS.core.eb1,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.ct,
        hq,
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


/-- The model of `const_val_at`. -/
l_model constValAt_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.constValAt ↦ constValAtW]
  specs [memoFindG_spec cvSch p _ hp.cvFind n, memoPutG_spec cvSch p _ hp.cvPut n,
    callW_spec p n "inst_lp"]
  grind [arena_grind]


theorem constValAt_run_hit (a : AState) (n : NIdx) (lps : List NIdx) (value : EIdx) (us : LsIdx)
    (r : EIdx) (hm : a.caches.constValC[(n, us)]? = some r) :
    (constValAt n lps value us).run a = .ok (r, a) := by
  simp only [constValAt, StateT.run_bind, StateT.run_get, pure_bind, hm]; rfl

theorem constValAt_run_miss (a a₁ : AState) (n : NIdx) (lps : List NIdx) (value : EIdx) (us : LsIdx)
    (r : EIdx) (hm : a.caches.constValC[(n, us)]? = none)
    (hI : (instLPFast coreWalkFuel lps us value).run a = .ok (r, a₁)) :
    (constValAt n lps value us).run a = .ok (r, { a₁ with caches := { a₁.caches with
      constValC := a₁.caches.constValC.insert (n, us) r } }) := by
  simp only [constValAt, StateT.run_bind, StateT.run_get, pure_bind, hm, hI, except_ok_bind]; rfl

section refs13
variable (p : Prog)

theorem callW_constValAt (hp : WhnfDeltaProg p) (hlp : InstLPOK p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb nm po pl value us : Word) (lps : List NIdx) (hC : CoreS dn s₀.mem a₀ vis fe MM eb)
    (hnm : HW nm) (hv : HW value) (hu : HW us)
    (hlps : hslice? (erecP s₀.mem) po.toNat pl.toNat = some lps) (r : List Word) (m' : Mem)
    (h : callW p n "const_val_at" [nm, po, pl, value, us] s₀.mem = some (r, m')) :
    CoreRef (constValAt (decI nm) lps (decE value) (decI us)) a₀ decH dn s₀.mem vis fe MM eb r m'
      ResH := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (constValAt_spec p hp (n + 1) s₀ nm po pl value us) h
  rw [constValAtW.eq_2] at hW
  by_cases h0 : mfindG cvSch s₀.mem nm us = []
  · rw [ite_eq_left h0] at hW; cases hW
  rw [ite_eq_right h0] at hW
  have hf := memoRV_findP (k₁ := .name) (k₂ := .levels) hC.core.cv nm us hnm hu h0
  by_cases h1 : (mfindG cvSch s₀.mem nm us).headD 0 ≠ 0
  · rw [ite_eq_left h1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    obtain ⟨hhit, hbd⟩ := hf.1 h1
    refine (CRef.pure hC _ (constValAt_run_hit a₀ _ _ _ _ _ hhit) ?_ ?_).core
    · simp only [decH, ← hr]; rfl
    · unfold ResH; rw [← hr]; exact hbd
  rw [ite_eq_right h1] at hW
  have hmiss := hf.2 (by simpa using h1)
  cases hcall : callW p n "inst_lp" [po, pl, us, value] s₀.mem with
  | none => rw [hcall, constValAtW.k_inst_lp.none] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [hcall, constValAtW.k_inst_lp.eq_2] at hW
  obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ :=
    CoreSpec.of_callW (hlp n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb po pl us value lps hC hv
      hu hlps) hcall
  by_cases hf1 : mfindG cvSch m₁ nm us = []
  · rw [ite_eq_left hf1] at hW; cases hW
  rw [ite_eq_right hf1] at hW
  cases hput : mputG cvSch m₁ nm us (r₁.headD 0) ((mfindG cvSch m₁ nm us).headD 0)
      ((mfindG cvSch m₁ nm us).tail.headD 0) with
  | none => rw [hput, constValAtW.k_cv_put.none] at hW; cases hW
  | some m₂ =>
  rw [hput, constValAtW.k_cv_put.arm1] at hW
  have hset : msetG cvSch m₁ nm us (r₁.headD 0) = some m₂ := by
    unfold msetG; rw [ite_eq_right hf1]; exact hput
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  have hrun := AM.run_of_ok _ _ hok
  rw [hres] at hrun
  have hz := constValAt_run_miss a₀ _ (decI nm) lps (decE value) (decI us) _ hmiss hrun
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  obtain ⟨hS₂, hSt₂⟩ := hS₁.set_cv nm us (r₁.headD 0) hnm hu hrw hset
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst', ← hm]
    exact ⟨M', hS₂, hK₁, hSt₁.trans hSt₂⟩
  · rw [hres']; simp only [decH, ← hr]
  · unfold ResH; rw [← hr]; exact hrw

theorem constValAt_refines' (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb nm po pl value us : Word) (lps : List NIdx)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hnm : HW nm) (hv : HW value) (hu : HW us)
    (hlp : InstLPOK p) (hlps : hslice? (erecP s₀.mem) po.toNat pl.toNat = some lps) :
    CoreSpec p n "const_val_at" [nm, po, pl, value, us]
      (constValAt (decI nm) lps (decE value) (decI us)) decH s₀ a₀ dn vis fe MM eb :=
  CoreSpec.of_call fun r m' h => callW_constValAt p hp hlp n s₀ a₀ dn vis fe MM eb nm po pl value us lps
    hC hnm hv hu hlps r m' h

end refs13


/-! ## `unfold_definition` -/

/-- The model of `unfold_defn_at`: `(flag, result, memory)`. -/
def unfoldDefnAtW (p : Prog) (n : Nat) (m : Mem) (e nw usw q : Word) : Option (Word × Word × Mem) :=
  if tagW usw ≠ 0 then none
  else if tierW usw ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m LVLS (tierW usw) ≤ idxW usw then none
  else if tfld m LVLS (tierW usw) (idxW usw) 1 ≠ rdW (m.arr64 EREC) (q + 3) then
    some (0, 0, m)
  else
  match callW p n "const_val_at" [nw, rdW (m.arr64 EREC) (q + 2), rdW (m.arr64 EREC) (q + 3),
      rdW (m.arr64 EREC) (q + 5), usw] m with
  | none => none
  | some (r₃, m₃) =>
  match callW p n "get_app_args" [e] m₃ with
  | none => none
  | some (r₄, m₄) =>
  match callW p n "mk_app_n" [r₃.headD 0, r₄.headD 0, r₄.tail.headD 0] m₄ with
  | none => none
  | some (r₅, m₅) => some (1, r₅.headD 0, m₅.set64 CTL 136 (rdW (m₃.arr64 CTL) 136))

theorem unfoldDefnAt_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (e nw usw q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "unfold_defn_at" [e, nw, usw, q]
    ⦃fun r s' => LocEq s' s₀ ∧
      unfoldDefnAtW p n s₀.mem e nw usw q = some (r.headD 0, r.tail.headD 0, s'.mem) ∧
      ((r.headD 0 ≠ 0) → (136 : Word).toNat < (s'.mem.arr64 CTL).size); ⊤⦄ := by
  sorry

/-- The model of `unfold_definition`: `(flag, result, memory)`. -/
l_model unfoldDefinition_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.unfoldDefinition ↦ unfoldDefinitionW tuple]
  specs [callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "unfold_defn_at"]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] gen 30


/-- The twin's tail of `unfoldDefinition`, once the head is a `defnInfo` constant. -/
def unfoldTailT (n : NIdx) (us : LsIdx) (cv : IConstantVal) (value e : EIdx) : AM (Option EIdx) := do
  let usl ← viewLs us
  if usl.length = cv.levelParams.length then do
    let v ← constValAt n cv.levelParams value us
    let args ← getAppArgs coreWalkFuel e
    let r ← mkAppN v args
    pure (some r)
  else pure none

theorem LsStore.viewLen_eq_map (st : LsStore) (i : LsIdx) :
    st.viewLen i = (st.view i).map List.length := by
  simp only [LsStore.viewLen, LsStore.view, LsStore.persGetLen, LsTables.getLen, LsTables.get]
  split
  · split <;> simp [Option.map_map, Function.comp_def]
  · split
    · split <;> simp [Option.map_map, Function.comp_def]
    · rfl

theorem whnf_viewLs_run {a : AState} {h : LsIdx} {l : LsNodeView} (hv : a.store.lss.view h = some l) :
    (viewLs h).run a = .ok (l, a) := by
  simp [viewLs, StateT.run_bind, StateT.run_get, hv]; rfl

theorem unfoldTail_run_ne {a : AState} {n : NIdx} {us : LsIdx} {cv : IConstantVal} {value e : EIdx}
    {l : LsNodeView} (hv : a.store.lss.view us = some l) (hne : l.length ≠ cv.levelParams.length) :
    (unfoldTailT n us cv value e).run a = .ok (none, a) := by
  simp only [unfoldTailT, StateT.run_bind, whnf_viewLs_run hv, except_ok_bind, hne, ↓reduceIte]; rfl

theorem unfoldTail_run_ok {a a₁ a₂ : AState} {n : NIdx} {us : LsIdx} {cv : IConstantVal}
    {value e v r : EIdx} {args : List EIdx} {l : LsNodeView} (hv : a.store.lss.view us = some l)
    (heq : l.length = cv.levelParams.length)
    (hc : (constValAt n cv.levelParams value us).run a = .ok (v, a₁))
    (hargs : (getAppArgs coreWalkFuel e).run a₁ = .ok (args, a₁))
    (hmk : (mkAppN v args).run a₁ = .ok (r, a₂)) :
    (unfoldTailT n us cv value e).run a = .ok (some r, a₂) := by
  simp only [unfoldTailT, StateT.run_bind, whnf_viewLs_run hv, except_ok_bind, heq, ↓reduceIte, hc,
    hargs, hmk]; rfl

section refs14
variable (p : Prog)

/-- **`mk_app_n` as a run**: the twin's `mkAppN`, `ArenaD` after it, only the `app` tables written,
and the result a handle word. -/
theorem callW_mkAppN (hp : SpineProg p) (n : Nat) (s₀ : St) (a₀ : AState) (hD : ArenaD s₀.mem a₀)
    (f o k : Word) (xs : Array EIdx) (hf : HW f) (hx : SpineR s₀.mem o k xs) (r : List Word)
    (m' : Mem) (h : callW p n "mk_app_n" [f, o, k] s₀.mem = some (r, m')) :
    AM.ok (mkAppN (decE f) xs.toList) a₀ ∧ ArenaD m' (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
    AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧
    MemFrame [AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] [4, 5] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hok, hD', hres, hfr⟩ := triple_of_callW (Q := fun r s' =>
      LocEq s' s₀ ∧ AM.ok (mkAppN (decE f) xs.toList) a₀ ∧
        ArenaD s'.mem (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
        AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧
        MemFrame [AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] [4, 5] s₀.mem s'.mem)
    (mkAppN_refines p hp n s₀ a₀ hD f o k xs hf hx) h
  obtain ⟨s'', hm⟩ := triple_of_callW (mkAppNL_spec p hp.derb hp.appf hp.appp hp.appi hp.mkapp hp.mkn
    n s₀ f o k) h
  exact ⟨hok, hD', hres, hfr, mkAppNFromW_hw k.toNat s₀.mem a₀ f o k 0 (by simp) hD hf _ _ hm.2.2⟩

end refs14


section refs15
variable (p : Prog)

theorem callW_unfoldDefnAt (hp : WhnfDeltaProg' p) (hlp : InstLPOK p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb e nw usw q : Word) (cv : IConstantVal) (value : EIdx) (hint : ConLeche.ReducibilityHint)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) (hnw : HW nw) (hus : HW usw)
    (hci : decCI (erecP s₀.mem) q.toNat = some (.defnInfo cv value hint))
    (hk1 : rdW (s₀.mem.arr64 EREC) q = 1) (r : List Word) (m' : Mem)
    (h : callW p n "unfold_defn_at" [e, nw, usw, q] s₀.mem = some (r, m')) :
    CoreRef (unfoldTailT (decI nw) (decI usw) cv value (decE e)) a₀ decOptR dn s₀.mem vis fe MM eb r
      m' ResW := by
  sorry

end refs15


theorem unfoldDef_run_notconst (fe : IFEnv) (e hh : EIdx) (a : AState)
    (hgf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = false) :
    (unfoldDefinition fe e).run a = .ok (none, a) := by
  simp only [unfoldDefinition, StateT.run_bind, hgf, except_ok_bind, ht]; rfl

theorem unfoldDef_run_nodefn (fe : IFEnv) (e hh : EIdx) (a : AState) (n : NIdx) (us : LsIdx)
    (hgf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = true)
    (hv : a.store.view hh = some (.const n us))
    (hfind : ∀ cv v hint, fe.find? n ≠ some (.defnInfo cv v hint)) :
    (unfoldDefinition fe e).run a = .ok (none, a) := by
  simp only [unfoldDefinition, StateT.run_bind, hgf, except_ok_bind, ht, ↓reduceIte,
    view_run _ _ _ hv]
  cases hf : fe.find? n with
  | none => rfl
  | some ci =>
    cases ci with
    | defnInfo cv v hint => exact absurd hf (hfind cv v hint)
    | _ => rfl

theorem unfoldDef_run_tail (fe : IFEnv) (e hh : EIdx) (a : AState) (n : NIdx) (us : LsIdx)
    (cv : IConstantVal) (value : EIdx) (hint : ConLeche.ReducibilityHint)
    (hgf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = true)
    (hv : a.store.view hh = some (.const n us)) (hfind : fe.find? n = some (.defnInfo cv value hint)) :
    (unfoldDefinition fe e).run a = (unfoldTailT n us cv value e).run a := by
  simp only [unfoldDefinition, StateT.run_bind, hgf, except_ok_bind, ht, ↓reduceIte,
    view_run _ _ _ hv, hfind, unfoldTailT]

section refs16
variable (p : Prog)

theorem callW_unfoldDefinition (hp : WhnfDeltaProg' p) (hlp : InstLPOK p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb e : Word) (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) (r : List Word) (m' : Mem)
    (h : callW p n "unfold_definition" [vis, e] s₀.mem = some (r, m')) :
    CoreRef (unfoldDefinition fe (decE e)) a₀ decOptR dn s₀.mem vis fe MM eb r m' ResW := by
  sorry

/-- **`unfold_definition` refines `unfoldDefinition`**, given the stub `inst_lp`'s spec. -/
theorem unfoldDefinition_refines' (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb e : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) (hlp : InstLPOK p) :
    CoreSpec p n "unfold_definition" [vis, e] (unfoldDefinition fe (decE e)) decOptR s₀ a₀ dn vis fe
      MM eb ResW :=
  CoreSpec.of_call fun r m' h => callW_unfoldDefinition p hp hlp n s₀ a₀ dn vis fe MM eb e hC he r m' h

end refs16

end L.Arena
