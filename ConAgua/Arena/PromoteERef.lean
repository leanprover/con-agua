import ConAgua.Arena.PromoteE
import ConAgua.Arena.PromoteLsRef
import ConAgua.Arena.PromotePiE
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `promote_e` refines `promoteE`

`pe_rel` by induction on L's fuel, for `promote_e`, `pe_arm` and the recursive arms
(`pe_app`, `pe_lam`, `pe_forall`, `pe_let`, `pe_proj`) together; `pe_const` (names and level
lists only) and `pe_lit` (no children) by themselves. The twin side: the arms named
(`promoteE_succ`), `e_view`'s words denote the twin's view (`IndView.lean`'s `eViewW_ok`), a
literal's record (`promote_lit_rec`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

open L.Ind (eViewW eViewW_ok ViewR)

/-! ## The twin, with the arms named -/

def peConstT (m : PMemo) (fuel : Nat) (n : NIdx) (us : LsIdx) : AM (PMemo × EIdx) := do
  let (m, n) ← promoteN m fuel n
  let (m, us) ← promoteLs m fuel us
  pure (m, ← internPersistentE (.const n us))

def peAppT (m : PMemo) (fuel : Nat) (f a : EIdx) : AM (PMemo × EIdx) := do
  let (m, f) ← promoteE m fuel f
  let (m, a) ← promoteE m fuel a
  pure (m, ← internPersistentE (.app f a))

def peLamT (m : PMemo) (fuel : Nat) (ty body : EIdx) : AM (PMemo × EIdx) := do
  let (m, ty) ← promoteE m fuel ty
  let (m, body) ← promoteE m fuel body
  pure (m, ← internPersistentE (.lam ty body))

def peForallT (m : PMemo) (fuel : Nat) (ty body : EIdx) : AM (PMemo × EIdx) := do
  let (m, ty) ← promoteE m fuel ty
  let (m, body) ← promoteE m fuel body
  pure (m, ← internPersistentE (.forallE ty body))

def peLetT (m : PMemo) (fuel : Nat) (ty val body : EIdx) : AM (PMemo × EIdx) := do
  let (m, ty) ← promoteE m fuel ty
  let (m, val) ← promoteE m fuel val
  let (m, body) ← promoteE m fuel body
  pure (m, ← internPersistentE (.letE ty val body))

def peProjT (m : PMemo) (fuel : Nat) (n : NIdx) (i : Nat) (e : EIdx) : AM (PMemo × EIdx) := do
  let (m, n) ← promoteN m fuel n
  let (m, e) ← promoteE m fuel e
  pure (m, ← internPersistentE (.proj n i e))

def peArmT (m : PMemo) (fuel : Nat) (h : EIdx) : AM (PMemo × EIdx) := do
  match ← view h with
  | .bvar i => do pure (m, ← internPersistentE (.bvar i))
  | .fvar idx ty => do
    let (m, ty) ← promoteE m fuel ty
    pure (m, ← internPersistentE (.fvar idx ty))
  | .sort u => do
    let (m, u) ← promoteL m fuel u
    pure (m, ← internPersistentE (.sort u))
  | .const n us => peConstT m fuel n us
  | .app f a => peAppT m fuel f a
  | .lam ty body => peLamT m fuel ty body
  | .forallE ty body => peForallT m fuel ty body
  | .letE ty val body => peLetT m fuel ty val body
  | .lit l => do pure (m, ← internPersistentE (.lit l))
  | .proj n i e => peProjT m fuel n i e

def peStepT (m : PMemo) (fuel : Nat) (h : EIdx) : AM (PMemo × EIdx) :=
  if h.isPersistent then pure (m, h)
  else match m.eM[h]? with
    | some r => pure (m, r)
    | none => do
      let (m, r) ← peArmT m fuel h
      pure ({ m with eM := m.eM.insert h r }, r)

theorem promoteE_succ (m : PMemo) (fuel : Nat) (h : EIdx) :
    promoteE m (fuel + 1) h = peStepT m fuel h := by
  rw [promoteE, peStepT]
  by_cases hp : h.isPersistent
  · simp only [hp, ↓reduceIte]
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    cases hm : m.eM[h]? with
    | some r => rfl
    | none =>
      simp only [peArmT, peConstT, peAppT, peLamT, peForallT, peLetT, peProjT, bind_assoc]
      apply bind_congr; intro v
      cases v <;> simp

/-! ## The view's words -/

theorem pmGetD1 (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
theorem pmGetD2 (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
theorem pmGetD3 (r : List Word) : r.getD 3 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl

/-- `e_view`'s tag `8`: the checks of a literal handle. -/
theorem eViewW_lit {m : Mem} {h : Word} (h8 : (eViewW m h).headD 0 = 8) :
    h.toNat < 2 ^ 32 ∧ viewOK m h LIT ∧ h >>> 28 = 8 := by
  unfold eViewW at h8
  by_cases c1 : 4294967295 < h
  · simp [c1] at h8
  have hh : h.toNat < 2 ^ 32 := by
    have : ¬ (4294967295 : Nat) < h.toNat := c1
    omega
  by_cases c2 : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [c1, c2] at h8
  simp only [c1, c2, ite_false] at h8
  by_cases g8 : h >>> 28 = 8
  · simp only [g8] at h8
    simp (config := { decide := true }) only [↓reduceIte] at h8
    by_cases c : tcnt m LIT (tierW h) ≤ idxW h
    · simp [c] at h8
    exact ⟨hh, ⟨c2, by simpa using c⟩, g8⟩
  exfalso
  simp only [apply_ite (fun l : List Word => l.headD 0), List.headD_cons, List.headD_nil] at h8
  repeat' split at h8
  all_goals first | (simp at h8; done) | exact absurd ‹h >>> 28 = 8› g8

/-- A literal handle's record: kind word, pool slice, the literal it holds. -/
theorem promote_lit_rec {m : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h LIT) (hg : h >>> 28 = 8) :
    ∃ k : LitNode, a.store.view (decE h) = some (.lit k.l) ∧ RecRel m (tierW h) (idxW h) k := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h litCS RecRel (·.lits) _ hR.lit.2 hv.2
  refine ⟨k, ?_, hkr⟩
  rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk]; rfl

/-! ## The relation for expressions -/

/-- The arrays and `CTL` words an expression promotion writes. -/
abbrev eArrs : List ArrId :=
  lsArrs ++ [REC, tier1 REC, SLOT, tier1 SLOT, AREC, tier1 AREC, ASLOT, tier1 ASLOT, SOREC, tier1 SOREC,
    SOSLOT, tier1 SOSLOT, CREC, tier1 CREC, CSLOT, tier1 CSLOT, LEREC, tier1 LEREC, LESLOT,
    tier1 LESLOT, BREC, tier1 BREC, BSLOT, tier1 BSLOT, FVREC, tier1 FVREC, FVSLOT, tier1 FVSLOT,
    LAREC, tier1 LAREC, LASLOT, tier1 LASLOT, FAREC, tier1 FAREC, FASLOT, tier1 FASLOT, PJREC, tier1 PJREC,
    PJSLOT, tier1 PJSLOT, ADER, tier1 ADER, LADER, tier1 LADER, FADER, tier1 FADER, LEDER,
    tier1 LEDER, PJDER, tier1 PJDER, PEM, SOLP, tier1 SOLP, CLP, tier1 CLP, FVLP, tier1 FVLP]
abbrev eCtl : List Word :=
  lsCtl ++ [2, 3, 4, 5, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27, 28, 29, 30, 31, 32, 33, 147]

/-- **What a successful run of an expression promotion gives.** -/
def PEOk (op : AM (PMemo × EIdx)) (m : Mem) (a : AState) (_pm : PMemo) (r : Word) (m' : Mem) :
    Prop :=
  ∃ a' pm', op.run a = .ok ((pm', decE r), a') ∧ ArenaD m' a' ∧ PMemoR m' pm' ∧ PW r ∧
    cp a' = cp a ∧ MemFrame eArrs eCtl m m' ∧ TierKeep m m'

theorem peSch_wf : peSch.WF := ⟨by decide, by decide⟩

/-- The expression memo gains an entry. -/
theorem PMemoR.setE {m m' : Mem} {pm : PMemo} (hP : PMemoR m pm) (h r : Word)
    (hh : h.toNat < 2 ^ 32) (hr : PW r) (hs : msetG peSch m h 0 r = some m') :
    PMemoR m' { pm with eM := pm.eM.insert (decI h) (decI r) } := by
  have hf := msetG_frame peSch peSch_wf m m' h 0 r hs
  exact ⟨memoRV_frame pnSch pnSch_wf _ _ _ _ (by decide) (by decide) m m' hf
      (fun _ _ h => h) _ hP.n,
    memoRV_frame plSch plSch_wf _ _ _ _ (by decide) (by decide) m m' hf
      (fun _ _ h => h) _ hP.l,
    memoRV_frame plsSch plsSch_wf _ _ _ _ (by decide) (by decide) m m' hf
      (fun _ _ h => h) _ hP.ls,
    memoRV_set peSch peSch_wf (hKey .expr) (VP .expr) (vp_stable _ _) m pm.eM hP.e h 0 r
      ⟨hh, rfl⟩ (decI r) ⟨rfl, hr.1, hr.2⟩ m' hs⟩

/-- **The end of a chain into `PEOk`.** -/
theorem PEOk.of_sim {op : AM (PMemo × EIdx)} {m : Mem} {a : AState} {pm : PMemo}
    {mo : Option (Word × Mem)} (h : Sim mo op a fun r x m' a' => x.2 = decE r ∧ ArenaD m' a' ∧
      PMemoR m' x.1 ∧ PW r ∧ cp a' = cp a ∧ MemFrame eArrs eCtl m m' ∧ TierKeep m m')
    {r : Word} {m' : Mem} (hm : mo = some (r, m')) : PEOk op m a pm r m' := by
  obtain ⟨⟨pm', y⟩, a', h1, e, h2⟩ := h r m' hm
  subst e; exact ⟨a', pm', h1, h2⟩

/-- **A callee in `PEOk` form, its first result word**, as a `Sim`. -/
theorem PEOk.sim1 {op : AM (PMemo × EIdx)} {m : Mem} {a : AState} {pm : PMemo}
    {mo : Option (List Word × Mem)} (h : ∀ r m', mo = some (r, m') → PEOk op m a pm (r.headD 0) m') :
    Sim (hd1 mo) op a fun r x m' a' => x.2 = decE r ∧ ArenaD m' a' ∧
      PMemoR m' x.1 ∧ PW r ∧ cp a' = cp a ∧ MemFrame eArrs eCtl m m' ∧ TierKeep m m' := by
  intro r m' e
  match mo, e with
  | some (r₁, m₁), e =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨a', pm', h1, h2⟩ := h r₁ m₁ rfl
    exact ⟨_, a', h1, rfl, h2⟩

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`pe_lit` refines the literal arm** (`internPersistentE (.lit l)`, the memo untouched). -/
theorem peLit_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (h : Word) (r : List Word)
    (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm) (hh : h.toNat < 2 ^ 32) (hv : viewOK m h LIT)
    (hg : h >>> 28 = 8) (l : ConLeche.Literal) (hl : a.store.view (decE h) = some (.lit l))
    (hc : callW p n "pe_lit" [h] m = some (r, m')) :
    PEOk (do pure (pm, ← internPersistentE (.lit l))) m a pm (r.headD 0) m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (peLit_spec p hp n ⟨m, Locals.init []⟩ h) hc
  simp only at hW
  obtain ⟨k, hk, hkr⟩ := promote_lit_rec hD.1 hh hv hg
  rw [hk] at hl
  cases hl
  obtain ⟨⟨N⟩ | ⟨st⟩⟩ := k
  · simp only [RecRel_natVal, NatRec] at hkr
    obtain ⟨hk0, hsl, hn, hpv, -⟩ := hkr
    rw [peLitW, ite_eq_right (by rw [ltK, hk0]; decide)] at hW
    refine PEOk.of_sim ((Sim.hd1 ((sim_piG _ (fun n s₀ => piLit_spec p hp n s₀ _ _) fun n _ _ h =>
      piLit_rel p hp n m a hD _ _ hsl.1 hn _ _ h).congr (by rw [hpv]))).mono ?_) hW
    rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₁, hpw, hcp, hfr, -⟩
    exact ⟨rfl, hD₁, hP.frameLo (by simp [tier1, tierOff, POOL, PT0, REC, SLOT]) (by simp) hfr, hpw, hcp,
      hfr.mono (by simp) (by simp), TierKeep.of_frame hfr (by decide)⟩
  · simp only [RecRel_strVal, StrRec] at hkr
    obtain ⟨hk1, hsl, hks, -⟩ := hkr
    rw [peLitW, ite_eq_left (by rw [ltK, hk1])] at hW
    refine PEOk.of_sim ((Sim.hd1 (sim_piG _ (fun n s₀ => piLitStr_spec p hp n s₀ _ _) fun n _ _ h =>
      piLitStr_rel p hp n m a hD _ _ hsl.1 st hks _ _ h)).mono ?_) hW
    rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₁, hpw, hcp, hfr, -⟩
    exact ⟨rfl, hD₁, hP.frameLo (by simp [tier1, tierOff, POOL, PT0, REC, SLOT]) (by simp) hfr, hpw, hcp,
      hfr.mono (by simp) (by simp), TierKeep.of_frame hfr (by decide)⟩

/-- **`pe_const` refines the `const` arm.** -/
theorem peConst_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f x us : Word) (r : List Word)
    (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm) (hx : x.toNat < 2 ^ 32)
    (hus : us.toNat < 2 ^ 32) (hc : callW p n "pe_const" [f, x, us] m = some (r, m')) :
    PEOk (peConstT pm f.toNat (decI x) (decI us)) m a pm (r.headD 0) m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (peConst_spec p hp n ⟨m, Locals.init []⟩ f x us) hc
  refine PEOk.of_sim ?_ hW
  unfold pe2W peConstT
  refine Sim.bindK rfl (fun _ _ => rfl) (Sim.ofP ((pn_rel p hp n).1 m a pm f x · · hD hP hx)) ?_
  rintro r₁ ⟨pm₁, _⟩ m₁ a₁ ⟨rfl, hD₁, hP₁, hpw₁, hcp₁, hfr₁, -, -, -⟩
  dsimp only [pe2K]
  refine Sim.bindK rfl (fun _ _ => rfl) (Sim.ofP (pls_rel p hp n m₁ a₁ pm₁ f us · · hD₁ hP₁ hus)) ?_
  rintro r₂ ⟨pm₂, _⟩ m₂ a₂ ⟨rfl, hD₂, hP₂, hpw₂, hcp₂, hfr₂, -, tk₂⟩
  dsimp only [pl2K.pl2K₂]
  refine (Sim.hd1 (sim_pi (fun n s₀ => piConst_spec p hp n s₀ _ _) fun n _ _ h =>
    piConst_rel p hp n m₂ a₂ hD₂ _ _ hpw₁ hpw₂ _ _ h)).mono ?_
  rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₃, hpw₃, hcp₃, hfr₃⟩
  exact ⟨rfl, hD₃, hP₂.frameLo (by simp [tier1, tierOff, CREC, CSLOT, CLP]) (by simp) hfr₃, hpw₃,
    hcp₃.trans (hcp₂.trans hcp₁), ((hfr₁.mono (by simp) (by simp)).trans (hfr₂.mono (by simp) (by simp))).trans
      (hfr₃.mono (by simp) (by simp)),
    ((TierKeep.of_frame hfr₁ (by decide)).trans tk₂).trans (TierKeep.of_frame hfr₃ (by decide))⟩

omit hp in
/-- **The two-child arms** `pe_app`, `pe_lam`, `pe_forall`: both children by `promote_e`, then
the interning `g` (its spec `hs`, its relation `hrel`). -/
theorem pe_two (n : Nat) (ihE : ∀ (m : Mem) (a : AState) (pm : PMemo) (f h : Word) (r : List Word) (m' : Mem),
      ArenaD m a → PMemoR m pm → h.toNat < 2 ^ 32 → callW p n "promote_e" [f, h] m = some (r, m') →
      PEOk (promoteE pm f.toNat (decE h)) m a pm (r.headD 0) m')
    {g mk : FnName} {C : EIdx → EIdx → ENodeView} {A : List ArrId} {Cs : List Word}
    (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) (hC : ∀ x ∈ Cs, x.toNat < 64) (hAe : ∀ b ∈ A, b ∈ eArrs)
    (hCe : ∀ x ∈ Cs, x ∈ eCtl) (h0 : (0 : Word) ∉ Cs)
    (hs : ∀ n s₀ x y, ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) g [x, y]
      ⦃fun r s' => LocEq s' s₀ ∧ piW p n mk [x, y] s₀.mem = some (r.headD 0, s'.mem); ⊤⦄)
    (hrel : ∀ n m a, ArenaD m a → ∀ x y, PW x → PW y → ∀ r m', piW p n mk [x, y] m = some (r, m') →
      ∃ a', (internPersistentE (C (decE x) (decE y))).run a = .ok (decE r, a') ∧ ArenaD m' a' ∧ PW r ∧
        cp a' = cp a ∧ MemFrame A Cs m m')
    (m : Mem) (a : AState) (pm : PMemo) (f x y : Word) (r : Word) (m' : Mem) (hD : ArenaD m a)
    (hP : PMemoR m pm) (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32)
    (hW : pe2W p n m "promote_e" "promote_e" g f x y = some (r, m')) :
    PEOk (do
      let (q, u) ← promoteE pm f.toNat (decE x)
      let (q, v) ← promoteE q f.toNat (decE y)
      pure (q, ← internPersistentE (C u v))) m a pm r m' := by
  refine PEOk.of_sim ?_ hW
  unfold pe2W
  refine Sim.bindK rfl (fun _ _ => rfl) (Sim.ofP (ihE m a pm f x · · hD hP hx)) ?_
  rintro r₁ ⟨pm₁, _⟩ m₁ a₁ ⟨rfl, hD₁, hP₁, hpw₁, hcp₁, hfr₁, tk₁⟩
  dsimp only [pe2K]
  refine Sim.bindK rfl (fun _ _ => rfl) (Sim.ofP (ihE m₁ a₁ pm₁ f y · · hD₁ hP₁ hy)) ?_
  rintro r₂ ⟨pm₂, _⟩ m₂ a₂ ⟨rfl, hD₂, hP₂, hpw₂, hcp₂, hfr₂, tk₂⟩
  dsimp only [pl2K.pl2K₂]
  refine (Sim.hd1 (sim_pi (hs · · _ _) fun n _ _ h => hrel n m₂ a₂ hD₂ _ _ hpw₁ hpw₂ _ _ h)).mono ?_
  rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₃, hpw₃, hcp₃, hfr₃⟩
  exact ⟨rfl, hD₃, hP₂.frameLo hA hC hfr₃, hpw₃, hcp₃.trans (hcp₂.trans hcp₁),
    (hfr₁.trans hfr₂).trans (hfr₃.mono hAe hCe), (tk₁.trans tk₂).trans (TierKeep.of_frame hfr₃ h0)⟩

/-- The seven functions' statements at L fuel `n`. -/
def PESpec (n : Nat) : Prop :=
  (∀ (m : Mem) (a : AState) (pm : PMemo) (f h : Word) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → h.toNat < 2 ^ 32 → callW p n "promote_e" [f, h] m = some (r, m') →
    PEOk (promoteE pm f.toNat (decE h)) m a pm (r.headD 0) m') ∧
  (∀ (m : Mem) (a : AState) (pm : PMemo) (f h : Word) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → h.toNat < 2 ^ 32 → callW p n "pe_arm" [f, h] m = some (r, m') →
    PEOk (peArmT pm f.toNat (decE h)) m a pm (r.headD 0) m') ∧
  (∀ (m : Mem) (a : AState) (pm : PMemo) (f x y : Word) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → x.toNat < 2 ^ 32 → y.toNat < 2 ^ 32 →
    callW p n "pe_app" [f, x, y] m = some (r, m') →
    PEOk (peAppT pm f.toNat (decE x) (decE y)) m a pm (r.headD 0) m') ∧
  (∀ (m : Mem) (a : AState) (pm : PMemo) (f x y : Word) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → x.toNat < 2 ^ 32 → y.toNat < 2 ^ 32 →
    callW p n "pe_lam" [f, x, y] m = some (r, m') →
    PEOk (peLamT pm f.toNat (decE x) (decE y)) m a pm (r.headD 0) m') ∧
  (∀ (m : Mem) (a : AState) (pm : PMemo) (f x y : Word) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → x.toNat < 2 ^ 32 → y.toNat < 2 ^ 32 →
    callW p n "pe_forall" [f, x, y] m = some (r, m') →
    PEOk (peForallT pm f.toNat (decE x) (decE y)) m a pm (r.headD 0) m') ∧
  (∀ (m : Mem) (a : AState) (pm : PMemo) (f x y z : Word) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → x.toNat < 2 ^ 32 → y.toNat < 2 ^ 32 → z.toNat < 2 ^ 32 →
    callW p n "pe_let" [f, x, y, z] m = some (r, m') →
    PEOk (peLetT pm f.toNat (decE x) (decE y) (decE z)) m a pm (r.headD 0) m') ∧
  (∀ (m : Mem) (a : AState) (pm : PMemo) (f nm i e : Word) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → nm.toNat < 2 ^ 32 → e.toNat < 2 ^ 32 →
    callW p n "pe_proj" [f, nm, i, e] m = some (r, m') →
    PEOk (peProjT pm f.toNat (decI nm) i.toNat (decE e)) m a pm (r.headD 0) m')

/-- **`promote_e`, `pe_arm` and the recursive arms refine the twin's**, at every L fuel. -/
theorem pe_rel : ∀ n : Nat, PESpec p n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [callW_zero']
  | succ n ih =>
  obtain ⟨ihE, ihA, ihApp, ihLam, ihFa, ihLet, ihPj⟩ := ih
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `promote_e`
    intro m a pm f h r m' hD hP hh hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (promoteE_spec p hp n ⟨m, Locals.init []⟩ f h) hc
    simp only at hW
    by_cases hf : f = 0
    · simp [peW, hf] at hW
    rw [toNat_pred f hf, promoteE_succ]
    unfold peStepT
    by_cases ht : tierW h = 0
    · rw [peW_pers p n m f h hf ht] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hpers : (decE h).isPersistent = true := PW.pers ⟨hh, ht⟩
      rw [ite_eq_left hpers, ← hr]
      exact ⟨a, pm, rfl, hD, hP, ⟨hh, ht⟩, rfl, MemFrame.refl _ _ _, TierKeep.refl _⟩
    have hnp : (decE h).isPersistent = false := by
      rw [isPersistent_decE h hh]; exact beq_eq_false_iff_ne.mpr ht
    rw [ite_eq_right (by simp [hnp])]
    have hk : (hKey .expr).ok h 0 := ⟨hh, rfl⟩
    by_cases h0 : mfindG peSch m h 0 = []
    · simp [peW, hf, ht, h0] at hW
    by_cases h1 : (mfindG peSch m h 0).headD 0 ≠ 0
    · obtain ⟨v, hv, hvr⟩ := memoRV_hit peSch (hKey .expr) (VP .expr) m pm.eM hP.e h 0 h0 h1 hk
      rw [peW_hit p n m f h hf ht h0 h1] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hv' : pm.eM[decE h]? = some v := hv
      rw [hv']
      obtain ⟨rfl, hw1, hw2⟩ := hvr
      rw [← hr]
      exact ⟨_, pm, rfl, hD, hP, ⟨hw1, hw2⟩, rfl, MemFrame.refl _ _ _, TierKeep.refl _⟩
    have h1' : (mfindG peSch m h 0).headD 0 = 0 := by simpa using h1
    rw [peW_miss p n m f h hf ht h0 h1'] at hW
    have hmiss : pm.eM[decE h]? = none :=
      memoRV_miss peSch (hKey .expr) (VP .expr) m pm.eM hP.e h 0 hk h0 h1'
    rw [hmiss]
    cases hca : callW p n "pe_arm" [f - 1, h] m with
    | none => rw [hca] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hca] at hW
    cases hs : msetG peSch m₁ h 0 (r₁.headD 0) with
    | none => simp only [memoK, hs] at hW; cases hW
    | some m₂ =>
    rw [memoK_some _ _ _ _ _ hs] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨a₁, pm₁, hrun, hD₁, hP₁, hpw, hcp, hfr, tk⟩ := ihA m a pm (f - 1) h r₁ m₁ hD hP hh hca
    refine ⟨a₁, { pm₁ with eM := pm₁.eM.insert (decE h) (decE (r₁.headD 0)) }, ?_,
      hD₁.memo peSch peSch_wf (by decide) (by decide) (by decide) h _ hs,
      hP₁.setE h _ hh hpw hs, by rw [← hr]; exact hpw, hcp, ?_,
      tk.trans (TierKeep.of_frame (msetG_frame peSch peSch_wf _ _ _ _ _ hs) (by decide))⟩
    · rw [run_bind_ok hrun, ← hr]; rfl
    · exact hfr.trans ((msetG_frame peSch peSch_wf _ _ _ _ _ hs).mono (by simp) (by simp))
  · -- `pe_arm`
    intro m a pm f h r m' hD hP hh hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (peArm_spec p hp n ⟨m, Locals.init []⟩ f h) hc
    simp only at hW
    by_cases hne : eViewW m h = []
    · simp [peArmW, hne] at hW
    rw [peArmW_eq p n m f h hne] at hW
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hD.1 h hne
    have hv0 := view_run (decE h) a v hv
    unfold peArmT
    cases v with
    | bvar i =>
      obtain ⟨hg, hi⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      refine PEOk.of_sim (Sim.bind_twin hv0 ((Sim.hd1 ((sim_pi (fun n s₀ => piBVar_spec p hp n s₀ _)
        fun n _ _ h => piBVar_rel p hp n m a hD _ _ _ h).congr (by rw [← pmGetD1, hi]))).mono ?_)) hW
      rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₁, hpw, hcp, hfr⟩
      exact ⟨rfl, hD₁, hP.frameLo (by simp [tier1, tierOff, BREC, BSLOT]) (by simp) hfr, hpw, hcp,
        hfr.mono (by simp) (by simp), TierKeep.of_frame hfr (by decide)⟩
    | fvar i ty =>
      obtain ⟨hg, hi, hty, hty'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hi
      rw [pmGetD2] at hty hty'
      refine PEOk.of_sim (Sim.bind_twin hv0 ?_) hW
      refine Sim.bindK rfl (fun _ _ => rfl) ((Sim.ofP (ihE m a pm f _ · · hD hP hty)).congr
        (by rw [hty'])) ?_
      rintro r₁ ⟨pm₁, _⟩ m₁ a₁ ⟨rfl, hD₁, hP₁, hpw₁, hcp₁, hfr₁, tk₁⟩
      dsimp only [peFvK]
      refine (Sim.hd1 ((sim_pi (fun n s₀ => piFVar_spec p hp n s₀ _ _) fun n _ _ h =>
        piFVar_rel p hp n m₁ a₁ hD₁ _ _ hpw₁ _ _ h).congr (by rw [hi]))).mono ?_
      rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₂, hpw₂, hcp₂, hfr₂⟩
      exact ⟨rfl, hD₂, hP₁.frameLo (by simp [tier1, tierOff, FVREC, FVSLOT, FVLP]) (by simp) hfr₂, hpw₂,
        hcp₂.trans hcp₁, hfr₁.trans (hfr₂.mono (by simp) (by simp)),
        tk₁.trans (TierKeep.of_frame hfr₂ (by decide))⟩
    | sort u =>
      obtain ⟨hg, hu, hu'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hu hu'
      refine PEOk.of_sim (Sim.bind_twin hv0 ?_) hW
      refine Sim.bindK rfl (fun _ _ => rfl) ((Sim.ofP ((pl_rel p hp n).1 m a pm f _ · · hD hP hu)).congr
        (by rw [hu'])) ?_
      rintro r₁ ⟨pm₁, _⟩ m₁ a₁ ⟨rfl, hD₁, hP₁, hpw₁, hcp₁, hfr₁, -, -⟩
      dsimp only [pl1K]
      refine (Sim.hd1 (sim_pi (fun n s₀ => piSort_spec p hp n s₀ _) fun n _ _ h =>
        piSort_rel p hp n m₁ a₁ hD₁ _ hpw₁ _ _ h)).mono ?_
      rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₂, hpw₂, hcp₂, hfr₂⟩
      exact ⟨rfl, hD₂, hP₁.frameLo (by simp [tier1, tierOff, SOREC, SOSLOT, SOLP]) (by simp) hfr₂, hpw₂,
        hcp₂.trans hcp₁, (hfr₁.mono (by simp) (by simp)).trans (hfr₂.mono (by simp [tier1, tierOff]) (by simp)),
        (TierKeep.of_frame hfr₁ (by decide)).trans (TierKeep.of_frame hfr₂ (by decide))⟩
    | const x us =>
      obtain ⟨hg, hx, hx', hus, hus'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hx hx'
      rw [pmGetD2] at hus hus'
      subst hx' hus'
      exact PEOk.of_sim (Sim.bind_twin hv0 (PEOk.sim1 (peConst_rel p hp n m a pm f _ _ · · hD hP hx hus))) hW
    | app u w =>
      obtain ⟨hg, hx, hx', hy, hy'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hx hx'
      rw [pmGetD2] at hy hy'
      subst hx' hy'
      exact PEOk.of_sim (Sim.bind_twin hv0 (PEOk.sim1 (ihApp m a pm f _ _ · · hD hP hx hy))) hW
    | lam u w =>
      obtain ⟨hg, hx, hx', hy, hy'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hx hx'
      rw [pmGetD2] at hy hy'
      subst hx' hy'
      exact PEOk.of_sim (Sim.bind_twin hv0 (PEOk.sim1 (ihLam m a pm f _ _ · · hD hP hx hy))) hW
    | forallE u w =>
      obtain ⟨hg, hx, hx', hy, hy'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hx hx'
      rw [pmGetD2] at hy hy'
      subst hx' hy'
      exact PEOk.of_sim (Sim.bind_twin hv0 (PEOk.sim1 (ihFa m a pm f _ _ · · hD hP hx hy))) hW
    | letE t x b =>
      obtain ⟨hg, ht, ht', hx, hx', hb, hb'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at ht ht'
      rw [pmGetD2] at hx hx'
      rw [pmGetD3] at hb hb'
      subst ht' hx' hb'
      exact PEOk.of_sim (Sim.bind_twin hv0 (PEOk.sim1 (ihLet m a pm f _ _ _ · · hD hP ht hx hb))) hW
    | lit l =>
      have hg : (eViewW m h).headD 0 = 8 := hvr
      obtain ⟨-, hvk, hg8⟩ := eViewW_lit hg
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      exact PEOk.of_sim (Sim.bind_twin hv0 (PEOk.sim1 (peLit_rel p hp n m a pm h · · hD hP hh hvk hg8 l hv ·))) hW
    | proj x i e =>
      obtain ⟨hg, hx, hx', hi, he, he'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hx hx'
      rw [pmGetD2] at hi
      rw [pmGetD3] at he he'
      subst hx' hi he'
      exact PEOk.of_sim (Sim.bind_twin hv0 (PEOk.sim1 (ihPj m a pm f _ _ _ · · hD hP hx he))) hW
  · -- `pe_app`
    intro m a pm f x y r m' hD hP hx hy hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (peApp_spec p hp n ⟨m, Locals.init []⟩ f x y) hc
    exact pe_two p n ihE (C := .app) (by simp [tier1, tierOff, ADER, AREC, ASLOT]) (by simp) (by simp) (by simp) (by decide)
      (fun n s₀ x y => piApp_spec p hp n s₀ x y) (fun n m a hD x y hx hy => piApp_rel p hp n m a hD x y hx hy)
      m a pm f x y _ _ hD hP hx hy hW
  · -- `pe_lam`
    intro m a pm f x y r m' hD hP hx hy hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (peLam_spec p hp n ⟨m, Locals.init []⟩ f x y) hc
    exact pe_two p n ihE (C := .lam) (by simp [tier1, tierOff, LADER, LAREC, LASLOT]) (by simp) (by simp) (by simp) (by decide)
      (fun n s₀ x y => piLam_spec p hp n s₀ x y) (fun n m a hD x y hx hy => piLam_rel p hp n m a hD x y hx hy)
      m a pm f x y _ _ hD hP hx hy hW
  · -- `pe_forall`
    intro m a pm f x y r m' hD hP hx hy hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (peForall_spec p hp n ⟨m, Locals.init []⟩ f x y) hc
    exact pe_two p n ihE (C := .forallE) (by simp [tier1, tierOff, FADER, FAREC, FASLOT]) (by simp) (by simp) (by simp) (by decide)
      (fun n s₀ x y => piForall_spec p hp n s₀ x y) (fun n m a hD x y hx hy => piForall_rel p hp n m a hD x y hx hy)
      m a pm f x y _ _ hD hP hx hy hW
  · -- `pe_let`
    intro m a pm f x y z r m' hD hP hx hy hz hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (peLet_spec p hp n ⟨m, Locals.init []⟩ f x y z) hc
    refine PEOk.of_sim ?_ hW
    unfold peLetW peLetT
    refine Sim.bindK rfl (fun _ _ => rfl) (Sim.ofP (ihE m a pm f x · · hD hP hx)) ?_
    rintro r₁ ⟨pm₁, _⟩ m₁ a₁ ⟨rfl, hD₁, hP₁, hpw₁, hcp₁, hfr₁, tk₁⟩
    dsimp only [pe3K]
    refine Sim.bindK rfl (fun _ _ => rfl) (Sim.ofP (ihE m₁ a₁ pm₁ f y · · hD₁ hP₁ hy)) ?_
    rintro r₂ ⟨pm₂, _⟩ m₂ a₂ ⟨rfl, hD₂, hP₂, hpw₂, hcp₂, hfr₂, tk₂⟩
    dsimp only [pe3K.pe3K₂]
    refine Sim.bindK rfl (fun _ _ => rfl) (Sim.ofP (ihE m₂ a₂ pm₂ f z · · hD₂ hP₂ hz)) ?_
    rintro r₃ ⟨pm₃, _⟩ m₃ a₃ ⟨rfl, hD₃, hP₃, hpw₃, hcp₃, hfr₃, tk₃⟩
    dsimp only [pe3K.pe3K₃]
    refine (Sim.hd1 (sim_pi (fun n s₀ => piLet_spec p hp n s₀ _ _ _) fun n _ _ h =>
      piLet_rel p hp n m₃ a₃ hD₃ _ _ _ hpw₁ hpw₂ hpw₃ _ _ h)).mono ?_
    rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₄, hpw₄, hcp₄, hfr₄⟩
    exact ⟨rfl, hD₄, hP₃.frameLo (by simp [tier1, tierOff, LEDER, LEREC, LESLOT]) (by simp) hfr₄, hpw₄,
      hcp₄.trans (hcp₃.trans (hcp₂.trans hcp₁)),
      ((hfr₁.trans hfr₂).trans hfr₃).trans (hfr₄.mono (by simp) (by simp)),
      ((tk₁.trans tk₂).trans tk₃).trans (TierKeep.of_frame hfr₄ (by decide))⟩
  · -- `pe_proj`
    intro m a pm f nm i e r m' hD hP hnm he hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (peProj_spec p hp n ⟨m, Locals.init []⟩ f nm i e) hc
    refine PEOk.of_sim ?_ hW
    unfold peProjW peProjT
    refine Sim.bindK rfl (fun _ _ => rfl) (Sim.ofP ((pn_rel p hp n).1 m a pm f nm · · hD hP hnm)) ?_
    rintro r₁ ⟨pm₁, _⟩ m₁ a₁ ⟨rfl, hD₁, hP₁, hpw₁, hcp₁, hfr₁, -, -, -⟩
    dsimp only [pePjK]
    refine Sim.bindK rfl (fun _ _ => rfl) (Sim.ofP (ihE m₁ a₁ pm₁ f e · · hD₁ hP₁ he)) ?_
    rintro r₂ ⟨pm₂, _⟩ m₂ a₂ ⟨rfl, hD₂, hP₂, hpw₂, hcp₂, hfr₂, tk₂⟩
    dsimp only [pePjK.pePjK₂]
    refine (Sim.hd1 (sim_pi (fun n s₀ => piProj_spec p hp n s₀ _ _ _) fun n _ _ h =>
      piProj_rel p hp n m₂ a₂ hD₂ _ i _ hpw₁ hpw₂ _ _ h)).mono ?_
    rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₃, hpw₃, hcp₃, hfr₃⟩
    exact ⟨rfl, hD₃, hP₂.frameLo (by simp [tier1, tierOff, PJDER, PJREC, PJSLOT]) (by simp) hfr₃, hpw₃,
      hcp₃.trans (hcp₂.trans hcp₁),
      ((hfr₁.mono (by simp) (by simp)).trans hfr₂).trans (hfr₃.mono (by simp [tier1, tierOff]) (by simp)),
      ((TierKeep.of_frame hfr₁ (by decide)).trans tk₂).trans (TierKeep.of_frame hfr₃ (by decide))⟩

/-- **`promote_e` refines `promoteE`** (`PEOk`). -/
@[refines ConRon.Arena.promoteE]
theorem promoteE_refines (n : Nat) (s₀ : St) (a₀ : AState) (pm : PMemo) (f h : Word)
    (hD : ArenaD s₀.mem a₀) (hP : PMemoR s₀.mem pm) (hh : h.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "promote_e" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      PEOk (promoteE pm f.toNat (decE h)) s₀.mem a₀ pm (r.headD 0) s'.mem; ⊤⦄ :=
  triple_post (callW_spec p n "promote_e" [f, h] s₀) fun _ _ ⟨hl, hc⟩ =>
    ⟨hl, (pe_rel p hp n).1 _ _ _ _ _ _ _ hD hP hh hc⟩

end rel

end L.Arena
