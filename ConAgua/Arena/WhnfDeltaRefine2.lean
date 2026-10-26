import ConAgua.Arena.WhnfDeltaRefine

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
def rawNatLitW (p : Prog) (n : Nat) (m : Mem) (h : Word) : Option (Word × Word × Word × Mem) :=
  if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if h >>> 28 = 0 then
    (if tcnt m BVAR (tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 1 then
    (if tcnt m FVAR (tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 2 then
    (if tcnt m SORT (tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 3 then
    (if tcnt m CONST (tierW h) ≤ idxW h then none else
      match callW p n "pin_at" [2] m with
      | none => none
      | some (r₁, m₁) =>
        match callW p n "pin_word" [52] m₁ with
        | none => none
        | some (r₂, m₂) =>
          if tfld m₂ CONST (tierW h) (idxW h) 0 = r₁.headD 0 ∧
              tfld m₂ CONST (tierW h) (idxW h) 1 = r₂.headD 0 then
            some (1, rdW (m₂.arr64 CTL) 0, 0, m₂)
          else some (0, 0, 0, m₂))
  else if h >>> 28 = 4 then
    (if tcnt m APP (tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 5 then
    (if tcnt m LAM (tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 6 then
    (if tcnt m FORALL (tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 7 then
    (if tcnt m LET (tierW h) ≤ idxW h then none else some (0, 0, 0, m))
  else if h >>> 28 = 8 then
    (if tcnt m LIT (tierW h) ≤ idxW h then none
      else if tfld m LIT (tierW h) (idxW h) 0 = 0 then
        some (1, tfld m LIT (tierW h) (idxW h) 1,
          tfld m LIT (tierW h) (idxW h) 2, m)
      else some (0, 0, 0, m))
  else if h >>> 28 ≠ 9 then none
  else if tcnt m PROJ (tierW h) ≤ idxW h then none else some (0, 0, 0, m)

theorem rawNatLit_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "raw_nat_lit" [h]
    ⦃fun r s' => LocEq s' s₀ ∧
      rawNatLitW p n s₀.mem h = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.rawNatLit]
  simp only [callFn, rawNatLitL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "pin_at", callW_spec p n "pin_word"] <;>
    finish (gen := 30) [rawNatLitW, tierW, idxW]


theorem rdW_ctl_top' (m : Mem) : rdW (m.arr64 CTL) 0 = m.top := by
  simp [rdW, Mem.top]

/-- **A `lit` node past the view checks**: the kind word `0` says `natVal`, with the record's
slice; any other kind says `strVal`. -/
theorem view_lit_nat (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h LIT) (hg : h >>> 28 = 8) :
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
    (hcg : (h >>> 28 = 0 ∧ c = BVAR) ∨ (h >>> 28 = 1 ∧ c = FVAR) ∨ (h >>> 28 = 2 ∧ c = SORT) ∨
      (h >>> 28 = 4 ∧ c = APP) ∨ (h >>> 28 = 5 ∧ c = LAM) ∨ (h >>> 28 = 6 ∧ c = FORALL) ∨
      (h >>> 28 = 7 ∧ c = LET) ∨ (h >>> 28 = 9 ∧ c = PROJ)) :
    ∃ v, a.store.view (decE h) = some v ∧ (∀ N, v ≠ .lit (.natVal N)) ∧
      (∀ c us, v ≠ .const c us) := by
  rcases hcg with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact ⟨_, view_bvar m a hR h hh hv g, fun N => nofun, fun c us => nofun⟩
  · obtain ⟨i, ty, hw⟩ := view_fvar m a hR h hh hv g
    exact ⟨_, hw, fun N => nofun, fun c us => nofun⟩
  · obtain ⟨u, hw⟩ := view_sort m a hR h hh hv g
    exact ⟨_, hw, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_app m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_lam m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_forall m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_let m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_proj m a hR h hh hv g).1, fun N => nofun, fun c us => nofun⟩

theorem rawSimple {dn : NIdx → Option ConLeche.Name} {m : Mem} {a₀ : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a₀ vis fe M eb) {h : Word} (hh : HW h)
    (c : TRec) (hsc : ¬(tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hb : ¬ tcnt m c (tierW h) ≤ idxW h)
    (hcg : (h >>> 28 = 0 ∧ c = BVAR) ∨ (h >>> 28 = 1 ∧ c = FVAR) ∨ (h >>> 28 = 2 ∧ c = SORT) ∨
      (h >>> 28 = 4 ∧ c = APP) ∨ (h >>> 28 = 5 ∧ c = LAM) ∨ (h >>> 28 = 6 ∧ c = FORALL) ∨
      (h >>> 28 = 7 ∧ c = LET) ∨ (h >>> 28 = 9 ∧ c = PROJ))
    (r : List Word) (hr : r.headD 0 = 0) : RawOut m a₀ h r := by
  obtain ⟨v, hv, hl, hc⟩ := view_other m a₀ hS.arena.1 h hh c ⟨hsc, by simpa using hb⟩ hcg
  exact RawOut.none (rawNatLit_run_other hv hl hc) hr

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
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (rawNatLit_spec p hp.toWhnfDeltaProg n s₀ h) hcall
  unfold rawNatLitW at hW
  by_cases hsc : tierW h ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left hsc] at hW; cases hW
  rw [ite_eq_right hsc] at hW
  -- the tags whose arm only checks the bound
  have simple : ∀ (c : TRec) (g : Prop) [Decidable g], g →
      (g → (h >>> 28 = 0 ∧ c = BVAR) ∨ (h >>> 28 = 1 ∧ c = FVAR) ∨ (h >>> 28 = 2 ∧ c = SORT) ∨
        (h >>> 28 = 4 ∧ c = APP) ∨ (h >>> 28 = 5 ∧ c = LAM) ∨ (h >>> 28 = 6 ∧ c = FORALL) ∨
        (h >>> 28 = 7 ∧ c = LET) ∨ (h >>> 28 = 9 ∧ c = PROJ)) →
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
  by_cases g0 : h >>> 28 = 0
  · rw [ite_eq_left g0] at hW
    obtain ⟨h1, h2⟩ := simple BVAR _ g0 (fun _ => Or.inl ⟨g0, rfl⟩) hW
    exact ⟨h1, h2⟩
  rw [ite_eq_right g0] at hW
  by_cases g1 : h >>> 28 = 1
  · rw [ite_eq_left g1] at hW
    obtain ⟨h1, h2⟩ := simple FVAR _ g1 (fun _ => Or.inr (Or.inl ⟨g1, rfl⟩)) hW
    exact ⟨h1, h2⟩
  rw [ite_eq_right g1] at hW
  by_cases g2 : h >>> 28 = 2
  · rw [ite_eq_left g2] at hW
    obtain ⟨h1, h2⟩ := simple SORT _ g2 (fun _ => Or.inr (Or.inr (Or.inl ⟨g2, rfl⟩))) hW
    exact ⟨h1, h2⟩
  rw [ite_eq_right g2] at hW
  by_cases g3 : h >>> 28 = 3
  · rw [ite_eq_left g3] at hW
    by_cases hb : tcnt s₀.mem CONST (tierW h) ≤ idxW h
    · rw [ite_eq_left hb] at hW; cases hW
    rw [ite_eq_right hb] at hW
    cases h1 : callW p n "pin_at" [2] s₀.mem with
    | none => rw [h1] at hW; cases hW
    | some q₁ =>
    obtain ⟨r₁, m₁⟩ := q₁
    rw [h1] at hW
    obtain ⟨hm1, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n s₀.mem 2 r₁ m₁ h1
    subst m₁
    dsimp only at hW
    cases h2 : callW p n "pin_word" [52] s₀.mem with
    | none => rw [h2] at hW; cases hW
    | some q₂ =>
    obtain ⟨r₂, m₂⟩ := q₂
    rw [h2] at hW
    obtain ⟨hm2, -, hr₂⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₂ m₂ h2
    subst m₂
    dsimp only at hW
    simp only [show (2 : Word).toNat = 2 from rfl, show (52 : Word).toNat = 52 from rfl] at hr₁ hr₂
    have hvOK : viewOK s₀.mem h CONST := ⟨hsc, by simpa using hb⟩
    obtain ⟨n_, us_, hview, hn, hu, hnl, hul⟩ := view_const_words s₀.mem a₀ hC.arena.1 h hh hvOK g3
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
    · rw [ite_eq_left hcond] at hW
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
    · rw [ite_eq_right hcond] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hf, ho, hcn, hm⟩ := hW
      refine ⟨hm.symm, RawOut.none ?_ hf.symm⟩
      rw [decide_eq_false hcond] at hrun
      simpa only [Bool.false_eq_true, ↓reduceIte] using hrun
  rw [ite_eq_right g3] at hW
  by_cases g4 : h >>> 28 = 4
  · rw [ite_eq_left g4] at hW
    obtain ⟨h1, h2⟩ := simple APP _ g4 (fun _ => Or.inr (Or.inr (Or.inr (Or.inl ⟨g4, rfl⟩)))) hW
    exact ⟨h1, h2⟩
  rw [ite_eq_right g4] at hW
  by_cases g5 : h >>> 28 = 5
  · rw [ite_eq_left g5] at hW
    obtain ⟨h1, h2⟩ := simple LAM _ g5
      (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g5, rfl⟩))))) hW
    exact ⟨h1, h2⟩
  rw [ite_eq_right g5] at hW
  by_cases g6 : h >>> 28 = 6
  · rw [ite_eq_left g6] at hW
    obtain ⟨h1, h2⟩ := simple FORALL _ g6
      (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g6, rfl⟩)))))) hW
    exact ⟨h1, h2⟩
  rw [ite_eq_right g6] at hW
  by_cases g7 : h >>> 28 = 7
  · rw [ite_eq_left g7] at hW
    obtain ⟨h1, h2⟩ := simple LET _ g7
      (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g7, rfl⟩))))))) hW
    exact ⟨h1, h2⟩
  rw [ite_eq_right g7] at hW
  by_cases g8 : h >>> 28 = 8
  · rw [ite_eq_left g8] at hW
    by_cases hb : tcnt s₀.mem LIT (tierW h) ≤ idxW h
    · rw [ite_eq_left hb] at hW; cases hW
    rw [ite_eq_right hb] at hW
    have hvOK : viewOK s₀.mem h LIT := ⟨hsc, by simpa using hb⟩
    obtain ⟨hk0, hk1⟩ := view_lit_nat s₀.mem a₀ hC.arena.1 h hh hvOK g8
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
  by_cases g9 : h >>> 28 ≠ 9
  · rw [ite_eq_left g9] at hW; cases hW
  rw [ite_eq_right g9] at hW
  have g9' : h >>> 28 = 9 := by simpa using g9
  obtain ⟨h1, h2⟩ := simple PROJ _ g9'
    (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨g9', rfl⟩))))))) hW
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
def natLitToCtorW (p : Prog) (n : Nat) (m : Mem) (o cnt : Word) : Option (Word × Mem) :=
  if cnt = 0 then
    match callW p n "pin_at" [2] m with
    | none => none
    | some (r₁, m₁) =>
      match callW p n "const_e" [r₁.headD 0] m₁ with
      | none => none
      | some (r₂, m₂) => some (r₂.headD 0, m₂)
  else
    match callW p n "pin_at" [3] m with
    | none => none
    | some (r₁, m₁) =>
      match callW p n "const_e" [r₁.headD 0] m₁ with
      | none => none
      | some (r₂, m₂) =>
        match callW p n "nat_pred_lit" [o, cnt] m₂ with
        | none => none
        | some (r₃, m₃) =>
          match callW p n "mk_app" [r₂.headD 0, r₃.headD 0] m₃ with
          | none => none
          | some (r₄, m₄) => some (r₄.headD 0, m₄)

theorem natLitToCtor_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (o cnt : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_lit_to_ctor" [o, cnt]
    ⦃fun r s' => LocEq s' s₀ ∧ natLitToCtorW p n s₀.mem o cnt = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.natLitToCtor]
  simp only [callFn, natLitToCtorL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pin_at", callW_spec p n "const_e", callW_spec p n "nat_pred_lit",
      callW_spec p n "mk_app"] <;>
    finish (gen := 30) [natLitToCtorW]


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
    (by simp [natA, POOL, POOL1, CREC, CSLOT, CLP])
    (fun b hb => by
      simp only [natA, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [natC, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [natC, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
    (hS.den.of_views hk.1 hk.2.1 hk.2.2 (hf.1 EREC (by simp [natA, POOL, POOL1, CREC, CSLOT, CLP, EREC]) (by decide))
      hv) (hmode := hS.mode.poolGrew hP)

theorem StackKept.of_nat_frame {m m' : Mem} (hf : MemFrame natA natC m m') (hP : PoolGrew m m') :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (by simp [natA, POOL, POOL1, CREC, CSLOT, CLP, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp [natC])
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

theorem litFns_closed : closedA storeProg [REC, REC + 256, SLOT, SLOT + 256] [2, 3] litFns = true := by decide +kernel

theorem WhnfDeltaProg'.litClosed (hp : WhnfDeltaProg' p) : closedA p [REC, REC + 256, SLOT, SLOT + 256] [2, 3] litFns = true :=
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
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (natLitToCtor_spec p hp.toWhnfDeltaProg n s₀ o cnt) hcall
  unfold natLitToCtorW at hW
  by_cases hc0 : cnt = 0
  · rw [ite_eq_left hc0] at hW
    cases h1 : callW p n "pin_at" [2] s₀.mem with
    | none => rw [h1] at hW; cases hW
    | some q₁ =>
    obtain ⟨r₁, m₁⟩ := q₁
    rw [h1] at hW
    obtain ⟨hm1, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n s₀.mem 2 r₁ m₁ h1
    subst m₁
    dsimp only at hW
    have hnt : HW (r₁.headD 0) := by rw [hr₁]; exact hC.pins.names_lt 2 (by decide)
    cases h2 : callW p n "const_e" [r₁.headD 0] s₀.mem with
    | none => rw [h2] at hW; cases hW
    | some q₂ =>
    obtain ⟨r₂, m₂⟩ := q₂
    rw [h2] at hW
    dsimp only at hW
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
  rw [ite_eq_right hc0] at hW
  have hpos : 0 < cnt.toNat := by
    rcases Nat.eq_zero_or_pos cnt.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hc0
    · exact h0
  obtain ⟨k, hk⟩ : ∃ k, pv (vpool s₀.mem) o.toNat cnt.toNat = k + 1 :=
    ⟨pv (vpool s₀.mem) o.toNat cnt.toNat - 1, by have := pv_pos_of_norm _ _ _ hnorm hpos; omega⟩
  rw [hk]
  cases h1 : callW p n "pin_at" [3] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  obtain ⟨hm1, -, -, hr₁⟩ := callW_pinAt p hp.pinAt n s₀.mem 3 r₁ m₁ h1
  subst m₁
  dsimp only at hW
  have hnt : HW (r₁.headD 0) := by rw [hr₁]; exact hC.pins.names_lt 3 (by decide)
  cases h2 : callW p n "const_e" [r₁.headD 0] s₀.mem with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  obtain ⟨hok, hS, hres, hfr, hhw⟩ := callW_constE p hp n s₀ a₀ dn vis fe MM eb _ hC hnt r₂ m₂ h2
  have hr₁' : r₁.headD 0 = pinW s₀.mem 4 := by
    simp only [show (3 : Word).toNat = 3 from rfl] at hr₁; exact hr₁
  rw [hr₁'] at hok hS hres
  have hPool : m₂.arr64 POOL = s₀.mem.arr64 POOL :=
    hfr.arr_eq POOL (by simp [CREC, CSLOT, CLP, POOL]) (by decide)
  have hPool1 : m₂.arr64 POOL1 = s₀.mem.arr64 POOL1 :=
    hfr.arr_eq POOL1 (by simp [CREC, CSLOT, CLP, POOL1]) (by decide)
  have hPt : m₂.ptop0 = s₀.mem.ptop0 :=
    ptop0_congr (hfr.arr_eq PT0 (by simp [CREC, CSLOT, CLP, PT0]) (by decide))
  have hPoolv := vpool_congr hPool hPool1
  have hPoolc := pcap_congr' hPool hPool1
  have hTop : m₂.top = s₀.mem.top := by
    rw [← rdW_ctl_top', ← rdW_ctl_top']; exact hfr.2.1 0 (by simp)
  have hs₂ : SliceOK m₂ o cnt := (SliceOK_congr _ _ hTop hPt).mpr hs
  cases h3 : callW p n "nat_pred_lit" [o, cnt] m₂ with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  dsimp only at hW
  obtain ⟨hok3, hS3, hres3, hfr3, hP3⟩ := callW_natPredLit p hp n ⟨m₂, Locals.init []⟩ _ dn vis fe MM eb o cnt
    hS hs₂ r₃ m₃ h3
  rw [hPoolv, hk] at hok3 hS3 hres3
  cases h4 : callW p n "mk_app" [r₂.headD 0, r₃.headD 0] m₃ with
  | none => rw [h4] at hW; cases hW
  | some q₄ =>
  obtain ⟨r₄, m₄⟩ := q₄
  rw [h4] at hW
  dsimp only at hW
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
def litToCtorIfNatW (p : Prog) (n : Nat) (m : Mem) (vis h : Word) : Option (Word × Mem) :=
  if h >>> 28 ≠ 8 then some (h, m)
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m LIT (tierW h) ≤ idxW h then none
  else if tfld m LIT (tierW h) (idxW h) 0 ≠ 0 then some (h, m)
  else match callW p n "nat_lit_supported" [vis] m with
    | none => none
    | some (r₁, m₁) =>
      if r₁.headD 0 = 0 then some (h, m₁)
      else match callW p n "nat_lit_to_ctor" [tfld m₁ LIT (tierW h) (idxW h) 1,
          tfld m₁ LIT (tierW h) (idxW h) 2] m₁ with
        | none => none
        | some (r₂, m₂) => some (r₂.headD 0, m₂)

theorem litToCtorIfNat_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (vis h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lit_to_ctor_if_nat" [vis, h]
    ⦃fun r s' => LocEq s' s₀ ∧ litToCtorIfNatW p n s₀.mem vis h = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.litToCtorIfNat]
  simp only [callFn, litToCtorIfNatL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "nat_lit_supported", callW_spec p n "nat_lit_to_ctor"] <;>
    finish (gen := 30) [litToCtorIfNatW, tierW, idxW]


theorem litToCtor_run_notlit (fe : IFEnv) (a : AState) (h : Word) (hh : HW h) (hg : h >>> 28 ≠ 8) :
    (litToCtorIfNat fe (decE h)).run a = .ok (decE h, a) := by
  have ht : ((decE h).tag == ETag.lit) = false := by rw [decE_lit_tag h hh]; simp [hg]
  simp [litToCtorIfNat, ht, StateT.run_pure]
  rfl

theorem litToCtor_run_str (fe : IFEnv) (a : AState) (h : Word) (hh : HW h) (hg : h >>> 28 = 8)
    (s : String) (hv : a.store.view (decE h) = some (.lit (.strVal s))) :
    (litToCtorIfNat fe (decE h)).run a = .ok (decE h, a) := by
  have ht : ((decE h).tag == ETag.lit) = true := by rw [decE_lit_tag h hh]; simp [hg]
  simp [litToCtorIfNat, ht, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  rfl

theorem litToCtor_run_unsup (fe : IFEnv) (a a₁ : AState) (h : Word) (hh : HW h)
    (hg : h >>> 28 = 8) (N : Nat) (hv : a.store.view (decE h) = some (.lit (.natVal N)))
    (hs : (natLitSupported fe).run a = .ok (false, a₁)) :
    (litToCtorIfNat fe (decE h)).run a = .ok (decE h, a₁) := by
  have ht : ((decE h).tag == ETag.lit) = true := by rw [decE_lit_tag h hh]; simp [hg]
  simp [litToCtorIfNat, ht, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hs]
  rfl

theorem litToCtor_run_sup (fe : IFEnv) (a a₁ a₂ : AState) (h : Word) (hh : HW h)
    (hg : h >>> 28 = 8) (N : Nat) (hv : a.store.view (decE h) = some (.lit (.natVal N)))
    (hs : (natLitSupported fe).run a = .ok (true, a₁)) (x : EIdx)
    (hc : (natLitToConstructor N).run a₁ = .ok (x, a₂)) :
    (litToCtorIfNat fe (decE h)).run a = .ok (x, a₂) := by
  have ht : ((decE h).tag == ETag.lit) = true := by rw [decE_lit_tag h hh]; simp [hg]
  simp [litToCtorIfNat, ht, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hs, hc]

section refs12
variable (p : Prog)

@[refines ConRon.Arena.litToCtorIfNat]
theorem litToCtorIfNat_refines (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb h : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hh : HW h) :
    CoreSpec p n "lit_to_ctor_if_nat" [vis, h] (litToCtorIfNat fe (decE h)) decH s₀ a₀ dn vis fe MM
      eb := by
  apply CoreSpec.of_call
  intro r m' hcall
  cases n with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (litToCtorIfNat_spec p hp.toWhnfDeltaProg n s₀ vis h) hcall
  unfold litToCtorIfNatW at hW
  by_cases hg : h >>> 28 ≠ 8
  · rw [ite_eq_left hg] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    exact (CRef.pure hC _ (litToCtor_run_notlit fe a₀ h hh hg) (by simp only [decH, ← hr]) (by
      unfold ResH; rw [← hr]; exact hh)).core
  rw [ite_eq_right hg] at hW
  have hg8 : h >>> 28 = 8 := by simpa using hg
  by_cases hsc : tierW h ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left hsc] at hW; cases hW
  rw [ite_eq_right hsc] at hW
  by_cases hbd : tcnt s₀.mem LIT (tierW h) ≤ idxW h
  · rw [ite_eq_left hbd] at hW; cases hW
  rw [ite_eq_right hbd] at hW
  have hvOK : viewOK s₀.mem h LIT := ⟨hsc, by simpa using hbd⟩
  obtain ⟨hk0, hk1⟩ := view_lit_nat s₀.mem a₀ hC.arena.1 h hh hvOK hg8
  by_cases hk : tfld s₀.mem LIT (tierW h) (idxW h) 0 ≠ 0
  · rw [ite_eq_left hk] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    obtain ⟨s, hv⟩ := hk1 hk
    exact (CRef.pure hC _ (litToCtor_run_str fe a₀ h hh hg8 s hv) (by simp only [decH, ← hr]) (by
      unfold ResH; rw [← hr]; exact hh)).core
  rw [ite_eq_right hk] at hW
  have hk' : tfld s₀.mem LIT (tierW h) (idxW h) 0 = 0 := by simpa using hk
  obtain ⟨N, hview, hnat⟩ := hk0 hk'
  obtain ⟨-, hsl, hnorm, hpv, -⟩ := hnat
  cases h1 : callW p n "nat_lit_supported" [vis] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  obtain ⟨hok1, hS1, hres1, hfr1, hrh1⟩ := callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r₁ m₁ h1
  by_cases hs0 : r₁.headD 0 = 0
  · rw [ite_eq_left hs0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    have hsup : (natLitSupported fe).run a₀ = .ok (false, AM.st (natLitSupported fe) a₀) := by
      have := AM.run_of_ok _ _ hok1
      rw [hres1] at this
      have hdb : decBool r₁ = false := by simp only [decBool, hs0]; rfl
      rwa [hdb] at this
    have hz := litToCtor_run_unsup fe a₀ _ h hh hg8 N hview hsup
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine CRef.core (m' := m₁) ⟨hok', by rw [hst']; exact hS1, ?_, hfr1, ?_⟩
    · rw [hres']; simp only [decH, ← hr]
    · unfold ResH; rw [← hr]; exact hh
  rw [ite_eq_right hs0] at hW
  have hsup : (natLitSupported fe).run a₀ = .ok (true, AM.st (natLitSupported fe) a₀) := by
    have := AM.run_of_ok _ _ hok1
    rw [hres1] at this
    have hdb : decBool r₁ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hs0
    rwa [hdb] at this
  have hE : m₁.arr64 REC = s₀.mem.arr64 REC :=
    hfr1.arr_eq REC (by simp [CREC, CSLOT, CLP, REC]) (by decide)
  have hE' : m₁.arr64 (REC + 256) = s₀.mem.arr64 (REC + 256) :=
    hfr1.arr_eq (REC + 256) (by simp [CREC, CSLOT, CLP, REC]) (by decide)
  have hPool : m₁.arr64 POOL = s₀.mem.arr64 POOL :=
    hfr1.arr_eq POOL (by simp [CREC, CSLOT, CLP, POOL]) (by decide)
  have hPool1 : m₁.arr64 POOL1 = s₀.mem.arr64 POOL1 :=
    hfr1.arr_eq POOL1 (by simp [CREC, CSLOT, CLP, POOL1]) (by decide)
  have hPt : m₁.ptop0 = s₀.mem.ptop0 :=
    ptop0_congr (hfr1.arr_eq PT0 (by simp [CREC, CSLOT, CLP, PT0]) (by decide))
  have hPoolv := vpool_congr hPool hPool1
  have hPoolc := pcap_congr' hPool hPool1
  have hTop : m₁.top = s₀.mem.top := by
    rw [← rdW_ctl_top', ← rdW_ctl_top']; exact hfr1.2.1 0 (by simp)
  simp only [tfld_arr_eq (R := LIT) hE hE'] at hW
  cases h2 : callW p n "nat_lit_to_ctor" [tfld s₀.mem LIT (tierW h) (idxW h) 1,
      tfld s₀.mem LIT (tierW h) (idxW h) 2] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  have hs₁ : SliceOK m₁ (tfld s₀.mem LIT (tierW h) (idxW h) 1)
      (tfld s₀.mem LIT (tierW h) (idxW h) 2) := by
    exact (SliceOK_congr _ _ hTop hPt).mpr hsl.1
  have hn₁ : Norm (vpool m₁) (tfld s₀.mem LIT (tierW h) (idxW h) 1).toNat
      (tfld s₀.mem LIT (tierW h) (idxW h) 2).toNat := by rw [hPoolv]; exact hnorm
  have hctor := natLitToCtor_refines p hp n ⟨m₁, Locals.init []⟩ _ dn vis fe MM eb _ _ hS1 hs₁ hn₁
  obtain ⟨hok2, hA2, hres2, hrw2⟩ := CoreSpec.of_callW hctor h2
  have hc2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hc2
  dsimp only at hc2 hA2 hrw2
  rw [hPoolv, hpv] at hc2
  rw [hPoolv, hpv] at hA2
  have hz := litToCtor_run_sup fe a₀ _ _ h hh hg8 N hview hsup _ hc2
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst', ← hm]
    exact CoreAfter.comp (KeptAll.refl _ _) (StackKept.of_const_frame hfr1) hA2
  · rw [hres']; simp only [decH, ← hr]
  · unfold ResH; rw [← hr]; exact hrw2

end refs12


/-! ## `const_val_at` -/

/-- `constValC` gains an entry (copy of `CoreS.set_wh`, at `cvSch`: array 103, `CTL` 110/111). -/
theorem CoreS.set_cv {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (nm us x : Word)
    (hn : HW nm) (hu : HW us) (hx : HW x) (hs : msetG cvSch m nm us x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        constValC := a.caches.constValC.insert (decI nm, decI us) (decE x) } } vis fe M eb ∧
      StackKept m m' := by
  have hf : MemFrame [103] [111] m m' :=
    msetG_frame cvSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  have hq := memoRV_set cvSch (coreSch_wf _ _ (by decide) (by decide)) pairKey VH
    (fun _ _ _ _ _ h => h) m a.caches.constValC hS.core.cv nm us x ⟨hn, hu⟩ (decE x) ⟨rfl, hx⟩ m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ 103 → S.cs ≠ 111 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [103] [111] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {VR : Mem → Word → ν → Prop} {M₀ : Std.HashMap (κ × Word) ν} {t te : Std.HashMap κ ν}, S.WF →
      VConst VR → S.arr ≠ 103 → S.cs ≠ 111 → ModeR S K VR m M₀ eb t te →
      ModeR S K VR m' M₀ eb t te :=
    fun hS' hV h1 h2 h => h.frame hS' hV (by simpa using h1) (by simpa using h2) hf
  have frv : ∀ {κ : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ)
      (mp : Std.HashMap κ EIdx), S.WF → S.arr ≠ 103 → S.cs ≠ 111 → MemoRV S K VH m mp →
      MemoRV S K VH m' mp :=
    fun S K mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [103] [111] (by simpa using h1) (by simpa using h2) m m' hf
        (vh_const m m') mp hR
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [103] [111] (by simp) (by simp) m m' hf a
        hS.arena.1), DerR.of_store _ _ _ (DerR.frameM [103] [111] m m' hf (by simp) a hS.arena.2) rfl⟩,
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
      hS.pins.congr (hf.1 PINS (by simp [PINS]) (by decide)),
      hS.env.frame (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; decide) hf,
      fun h l e => hS.readL h l e, fun h l e => hS.readLs h l e, hS.nwf,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn, hS.memos.frame hf (by decide) (by decide), hf.2.2.1 145 ▸ hS.bstk,
      (hS.den.frameE (hf.1 EREC (by simp [EREC]) (by decide))).caches rfl rfl rfl,
      hS.mode.frame hf (by simp) (by simp)⟩,
    StackKept.of_frame hf⟩


/-- The model of `const_val_at`. -/
def constValAtW (p : Prog) (n : Nat) (m : Mem) (nm po pl value us : Word) : Option (Word × Mem) :=
  memoSlotW cvSch m nm us (callW p n "inst_lp" [po, pl, us, value] m)

theorem constValAt_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St)
    (nm po pl value us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "const_val_at" [nm, po, pl, value, us]
    ⦃fun r s' => LocEq s' s₀ ∧ constValAtW p n s₀.mem nm po pl value us = some (r.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp.constValAt]
  simp only [callFn, constValAtL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec cvSch p _ hp.cvFind n, memoPutG_spec cvSch p _ hp.cvPut n,
      callW_spec p n "inst_lp"] <;>
    finish [constValAtW, memoSlotW_hit, memoSlotW_miss, mvG]


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
    (hlps : hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps) (r : List Word) (m' : Mem)
    (h : callW p n "const_val_at" [nm, po, pl, value, us] s₀.mem = some (r, m')) :
    CoreRef (constValAt (decI nm) lps (decE value) (decI us)) a₀ decH dn s₀.mem vis fe MM eb r m'
      ResH := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (constValAt_spec p hp n s₀ nm po pl value us) h
  unfold constValAtW memoSlotW at hW
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
    · simp only [decH, ← hr]
    · unfold ResH; rw [← hr]; exact hbd
  rw [ite_eq_right h1] at hW
  have hmiss := hf.2 (by simpa using h1)
  cases hcall : callW p n "inst_lp" [po, pl, us, value] s₀.mem with
  | none => rw [hcall] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [hcall] at hW
  dsimp only at hW
  obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ :=
    CoreSpec.of_callW (hlp n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb po pl us value lps hC hv
      hu hlps) hcall
  cases hset : msetG cvSch m₁ nm us (r₁.headD 0) with
  | none => rw [hset] at hW; cases hW
  | some m₂ =>
  rw [hset] at hW
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
    (hlp : InstLPOK p) (hlps : hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps) :
    CoreSpec p n "const_val_at" [nm, po, pl, value, us]
      (constValAt (decI nm) lps (decE value) (decI us)) decH s₀ a₀ dn vis fe MM eb :=
  CoreSpec.of_call fun r m' h => callW_constValAt p hp hlp n s₀ a₀ dn vis fe MM eb nm po pl value us lps
    hC hnm hv hu hlps r m' h

end refs13


/-! ## `unfold_definition` -/

/-- The model of `unfold_defn_at`: `(flag, result, memory)`. -/
def unfoldDefnAtW (p : Prog) (n : Nat) (m : Mem) (e nw usw q : Word) : Option (Word × Word × Mem) :=
  if usw >>> 28 ≠ 0 then none
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
  rw [invoke_eq _ hp.unfoldDefnAt]
  simp only [callFn, unfoldDefnAtL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE, st64,
      callW_spec p n "const_val_at", callW_spec p n "get_app_args",
      callW_spec p n "mk_app_n"] <;>
    finish (gen := 30) [unfoldDefnAtW, tierW, idxW]

/-- The model of `unfold_definition`: `(flag, result, memory)`. -/
def unfoldDefinitionW (p : Prog) (n : Nat) (m : Mem) (vis e : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "get_app_fn" [e] m with
  | none => none
  | some (r₁, m₁) =>
  if r₁.headD 0 >>> 28 ≠ 3 then some (0, 0, m₁)
  else if tierW (r₁.headD 0) ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0 then none
  else if tcnt m₁ CONST (tierW (r₁.headD 0)) ≤ idxW (r₁.headD 0) then none
  else
  match callW p n "env_find" [tfld m₁ CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 0,
      vis] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if r₂.headD 0 = 0 then some (0, 0, m₂)
  else if rdW (m₂.arr64 EREC) (r₂.tail.headD 0) ≠ 1 then some (0, 0, m₂)
  else
  match callW p n "unfold_defn_at" [e,
      tfld m₁ CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 0,
      tfld m₁ CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 1,
      r₂.tail.headD 0] m₂ with
  | none => none
  | some (r₃, m₃) => some (r₃.headD 0, r₃.tail.headD 0, m₃)

theorem unfoldDefinition_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (vis e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "unfold_definition" [vis, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      unfoldDefinitionW p n s₀.mem vis e = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.unfoldDefinition]
  simp only [callFn, unfoldDefinitionL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "unfold_defn_at"] <;>
    finish (gen := 30) [unfoldDefinitionW, tierW, idxW]


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
    MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hok, hD', hres, hfr⟩ := triple_of_callW (Q := fun r s' =>
      LocEq s' s₀ ∧ AM.ok (mkAppN (decE f) xs.toList) a₀ ∧
        ArenaD s'.mem (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
        AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧
        MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] s₀.mem s'.mem)
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
    (hci : decCI (erecP s₀.mem) dn q.toNat = some (.defnInfo cv value hint))
    (hk1 : rdW (s₀.mem.arr64 EREC) q = 1) (r : List Word) (m' : Mem)
    (h : callW p n "unfold_defn_at" [e, nw, usw, q] s₀.mem = some (r, m')) :
    CoreRef (unfoldTailT (decI nw) (decI usw) cv value (decE e)) a₀ decOptR dn s₀.mem vis fe MM eb r
      m' ResW := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW, h136⟩ := triple_of_callW (unfoldDefnAt_spec p hp.toWhnfDeltaProg n s₀ e nw usw q) h
  obtain ⟨hdefn, -, -, -, -, -⟩ := decCI_split hci (erecP_ext _) hC.erec
  obtain ⟨cv', v', hint', hci_eq, hcv, hv', hvl⟩ := hdefn hk1
  injection hci_eq with hcv_eq hv_eq hh_eq
  subst hcv_eq hv_eq
  obtain ⟨hslice, hlen, -, -⟩ := decCV_rd (erecP_ext s₀.mem) hC.erec hcv
  unfold unfoldDefnAtW at hW
  by_cases g1 : usw >>> 28 ≠ 0
  · rw [ite_eq_left g1] at hW; cases hW
  rw [ite_eq_right g1] at hW
  have g1' : usw >>> 28 = 0 := by simpa using g1
  by_cases g2 : tierW usw ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left g2] at hW; cases hW
  rw [ite_eq_right g2] at hW
  by_cases g3 : tcnt s₀.mem LVLS (tierW usw) ≤ idxW usw
  · rw [ite_eq_left g3] at hW; cases hW
  rw [ite_eq_right g3] at hW
  -- the level list's view
  have hls : lsNodeW s₀.mem usw = [tfld s₀.mem LVLS (tierW usw) (idxW usw) 0,
      tfld s₀.mem LVLS (tierW usw) (idxW usw) 1] := by
    unfold lsNodeW
    rw [ite_eq_right (by simpa using g1'), ite_eq_right g2, ite_eq_right g3]
  have hvl' := lsNodeW_viewLen hC.arena.1 hus hls
  rw [LsStore.viewLen_eq_map] at hvl'
  obtain ⟨l, hview, hllen⟩ : ∃ l, a₀.store.lss.view (decI usw) = some l ∧
      l.length = (tfld s₀.mem LVLS (tierW usw) (idxW usw) 1).toNat := by
    cases hv : a₀.store.lss.view (decI usw) with
    | none => rw [hv] at hvl'; cases hvl'
    | some l => rw [hv] at hvl'; exact ⟨l, rfl, Option.some.inj hvl'⟩
  by_cases g4 : tfld s₀.mem LVLS (tierW usw) (idxW usw) 1 ≠
      rdW (s₀.mem.arr64 EREC) (q + 3)
  · rw [ite_eq_left g4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    refine (CRef.pure hC _ (unfoldTail_run_ne hview ?_) ?_ ?_).core
    · intro hc
      apply g4
      apply UInt64.toNat_inj.mp
      rw [← hllen, hc, hlen]
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [ite_eq_right g4] at hW
  have g4' : tfld s₀.mem LVLS (tierW usw) (idxW usw) 1 =
      rdW (s₀.mem.arr64 EREC) (q + 3) := by simpa using g4
  have hleneq : l.length = cv.levelParams.length := by rw [hllen, hlen, g4']
  -- const_val_at
  cases h1 : callW p n "const_val_at" [nw, rdW (s₀.mem.arr64 EREC) (q + 2),
      rdW (s₀.mem.arr64 EREC) (q + 3), rdW (s₀.mem.arr64 EREC) (q + 5), usw] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₃, m₃⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  obtain ⟨hok1, ⟨M', hS₃, hK₃, hSt₃⟩, hres1, hrh1⟩ := callW_constValAt p hp.toWhnfDeltaProg hlp n s₀ a₀ dn vis
    fe MM eb nw _ _ _ usw cv.levelParams hC hnw hvl hus hslice r₃ m₃ h1
  have hv'' : value = decE (rdW (s₀.mem.arr64 EREC) (q + 5)) := hv'
  rw [← hv''] at hok1 hS₃ hres1
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  -- get_app_args
  cases h2 : callW p n "get_app_args" [e] m₃ with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₄, m₄⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  obtain ⟨t₂, ht₂, -, hfr₂, hgrew, -, -, xs, hxrun, hsp⟩ := triple_of_callW
    (getAppArgs_refines p hp.spine n ⟨m₃, Locals.init []⟩ _ hS₃.arena.1 e he hS₃.spn) h2
  subst ht₂
  have hS₄ : CoreS dn t₂.mem _ vis fe M' eb :=
    hS₃.frame_stk hfr₂ (fun b hb => by simpa using hb) (fun x hx => by simpa using hx)
  -- mk_app_n
  cases h3 : callW p n "mk_app_n" [r₃.headD 0, r₄.headD 0, r₄.tail.headD 0] t₂.mem with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₅, m₅⟩ := q₃
  rw [h3] at hW
  dsimp only at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  obtain ⟨hok3, hD3, hres3, hfr3, hhw3⟩ := callW_mkAppN p hp.spine n ⟨t₂.mem, Locals.init []⟩ _
    hS₄.arena (r₃.headD 0) (r₄.headD 0) (r₄.tail.headD 0) xs.toArray hrh1 hsp r₅ m₅ h3
  rw [List.toList_toArray] at hok3 hD3 hres3
  have e0 : (constValAt (decI nw) cv.levelParams value (decI usw)).run a₀ =
      .ok (decE (r₃.headD 0), AM.st (constValAt (decI nw) cv.levelParams value (decI usw)) a₀) := by
    rw [hrun1]; rfl
  have e2 : (mkAppN (decE (r₃.headD 0)) xs).run
      (AM.st (constValAt (decI nw) cv.levelParams value (decI usw)) a₀) =
      .ok (decE (r₅.headD 0), AM.st (mkAppN (decE (r₃.headD 0)) xs)
        (AM.st (constValAt (decI nw) cv.levelParams value (decI usw)) a₀)) := by
    rw [AM.run_of_ok _ _ hok3, hres3]
  have hz := unfoldTail_run_ok hview hleneq e0 hxrun e2
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  have hcpl : cpl (AM.st (mkAppN (decE (r₃.headD 0)) xs)
      (AM.st (constValAt (decI nw) cv.levelParams value (decI usw)) a₀)) =
      cpl (AM.st (constValAt (decI nw) cv.levelParams value (decI usw)) a₀) := by
    have := Keeps.run (keeps_cpl_mkAppNFrom (decE (r₃.headD 0)) xs.toArray 0)
      (a := AM.st (constValAt (decI nw) cv.levelParams value (decI usw)) a₀)
      (by rw [mkAppNFrom_eq_mkAppN, List.toList_toArray]; exact AM.run_of_ok _ _ hok3)
    simpa using this
  have hS₅ := hS₄.of_app hD3 hcpl hfr3
  have hspn5 : m₅.arr64 SPN = t₂.mem.arr64 SPN :=
    hfr3.1 SPN (by simp [AREC, ASLOT, ADER, SPN]) (by decide)
  have hfr6 : MemFrame [SPN] [136] m₅ (m₅.set64 CTL 136 (rdW (m₃.arr64 CTL) 136)) :=
    (MemFrame.setCtl m₅ 136 _).mono (by simp) (by simp)
  have hS₆ : CoreS dn (m₅.set64 CTL 136 (rdW (m₃.arr64 CTL) 136)) _ vis fe M' eb :=
    hS₅.frame_stk hfr6 (fun b hb => by simpa using hb) (fun x hx => by simpa using hx)
  have h136' : (136 : Word).toNat < (m₅.arr64 CTL).size := by
    have := h136 (by rw [← hr0]; decide)
    rw [← hm, size_set64] at this; exact this
  have hStK : StackKept m₃ (m₅.set64 CTL 136 (rdW (m₃.arr64 CTL) 136)) := by
    apply StackKept.restore _ (by rw [hspn5, hgrew.size])
      (hgrew.bstk.trans (BKept.of_frame hfr3 (by decide) (by decide)))
      (hgrew.pool.trans (PoolGrew.of_frame hfr3 (by decide) (by decide))) h136'
    intro i hi
    simp only [spW, hspn5]
    exact hgrew.below i hi
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst', ← hm]
    exact ⟨M', hS₆, hK₃, hSt₃.trans hStK⟩
  · rw [hres']
    simp only [decOptR, decOpt, ← hr0, ← hr1]
    simp
  · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, hhw3⟩

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
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (unfoldDefinition_spec p hp.toWhnfDeltaProg n s₀ vis e) h
  unfold unfoldDefinitionW at hW
  cases h1 : callW p n "get_app_fn" [e] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  obtain ⟨t₁, ht₁, hm₁, -, hhw1, hgf⟩ := triple_of_callW
    (getAppFn_refines p hp.spine n s₀ a₀ hC.arena.1 e he) h1
  have hm1 : m₁ = s₀.mem := by rw [← ht₁, hm₁]
  subst hm1
  dsimp only at hW
  by_cases g0 : r₁.headD 0 >>> 28 ≠ 3
  · rw [ite_eq_left g0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have ht : ((decE (r₁.headD 0)).tag == ETag.const) = false := by
      rw [decE_const_tag _ hhw1]; exact beq_eq_false_iff_ne.mpr g0
    refine (CRef.pure hC _ (unfoldDef_run_notconst fe _ _ a₀ hgf ht) ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [ite_eq_right g0] at hW
  have g0' : r₁.headD 0 >>> 28 = 3 := by simpa using g0
  have ht : ((decE (r₁.headD 0)).tag == ETag.const) = true := by
    rw [decE_const_tag _ hhw1]; exact beq_iff_eq.mpr g0'
  by_cases g1 : tierW (r₁.headD 0) ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left g1] at hW; cases hW
  rw [ite_eq_right g1] at hW
  by_cases g2 : tcnt s₀.mem CONST (tierW (r₁.headD 0)) ≤ idxW (r₁.headD 0)
  · rw [ite_eq_left g2] at hW; cases hW
  rw [ite_eq_right g2] at hW
  have hvOK : viewOK s₀.mem (r₁.headD 0) CONST := ⟨g1, by simpa using g2⟩
  obtain ⟨n_, us_, hview, hn, hu, hnl, hul⟩ :=
    view_const_words s₀.mem a₀ hC.arena.1 (r₁.headD 0) hhw1 hvOK g0'
  cases h2 : callW p n "env_find" [tfld s₀.mem CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 0, vis] s₀.mem with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  obtain ⟨hm2, hfind, hdec⟩ := callW_envFind p hp n ⟨s₀.mem, Locals.init []⟩ vis _ hC.env hnl r₂ m₂ h2
  subst hm2
  dsimp only at hW
  by_cases g3 : r₂.headD 0 = 0
  · rw [ite_eq_left g3] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hnone : fe.find? n_ = none := by
      rw [hn, hfind]; simp only [decFound, g3, ↓reduceIte]
    refine (CRef.pure hC _ (unfoldDef_run_nodefn fe _ _ a₀ n_ us_ hgf ht hview
      (fun cv v hint hh => by rw [hnone] at hh; cases hh)) ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [ite_eq_right g3] at hW
  obtain ⟨ci, hci⟩ := hdec g3
  have hfind' : fe.find? n_ = some ci := by
    rw [hn, hfind]; simp only [decFound, g3, ↓reduceIte]; exact hci
  obtain ⟨hdefn, hndefn, -, -, -, -⟩ := decCI_split hci (erecP_ext _) hC.erec
  by_cases g4 : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0) ≠ 1
  · rw [ite_eq_left g4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    refine (CRef.pure hC _ (unfoldDef_run_nodefn fe _ _ a₀ n_ us_ hgf ht hview
      (fun cv v hint hh => hndefn g4 cv v hint (by rw [hfind'] at hh; exact Option.some.inj hh))) ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [ite_eq_right g4] at hW
  have g4' : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0) = 1 := by simpa using g4
  obtain ⟨cv, value, hint, rfl, hcv, hv', hvl⟩ := hdefn g4'
  cases h3 : callW p n "unfold_defn_at" [e, tfld s₀.mem CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 0, tfld s₀.mem CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 1, r₂.tail.headD 0] s₀.mem with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  rw [← hm]
  have hci' : decCI (erecP s₀.mem) dn (r₂.tail.headD 0).toNat = some (.defnInfo cv value hint) := hci
  have hcore := callW_unfoldDefnAt p hp hlp n s₀ a₀ dn vis fe MM eb e _ _ (r₂.tail.headD 0) cv value hint
    hC he hnl hul hci' g4' r₃ m₃ h3
  have hrun := unfoldDef_run_tail fe (decE e) (decE (r₁.headD 0)) a₀ n_ us_ cv value hint hgf ht hview
    hfind'
  rw [hn, hu] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.congr_run hrun
  obtain ⟨hok', hA, hres', hrw⟩ := hcore
  have hf : fe.find? n_ = some (.defnInfo cv value hint) := hfind'
  refine ⟨by rw [hok]; exact hok', ?_, ?_, ?_⟩
  · rw [hst]; exact hA
  · rw [hres, hres']; simp only [decOptR, ← hr0, ← hr1]
  · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw

/-- **`unfold_definition` refines `unfoldDefinition`**, given the stub `inst_lp`'s spec. -/
theorem unfoldDefinition_refines' (hp : WhnfDeltaProg' p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb e : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) (hlp : InstLPOK p) :
    CoreSpec p n "unfold_definition" [vis, e] (unfoldDefinition fe (decE e)) decOptR s₀ a₀ dn vis fe
      MM eb ResW :=
  CoreSpec.of_call fun r m' h => callW_unfoldDefinition p hp hlp n s₀ a₀ dn vis fe MM eb e hC he r m' h

end refs16

end L.Arena
