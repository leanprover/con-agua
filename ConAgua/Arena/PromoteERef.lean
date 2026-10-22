import ConAgua.Arena.PromoteE
import ConAgua.Arena.PromoteLsRef
import ConAgua.Arena.PromotePiE
import ConAgua.Census.Attr

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

set_option linter.unusedSimpArgs false

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
    h.toNat < 2 ^ 32 ∧ viewOK m h 2 ∧ h >>> 28 = 8 := by
  unfold eViewW at h8
  by_cases c1 : 4294967295 < h
  · simp [c1] at h8
  have hh : h.toNat < 2 ^ 32 := by
    have : ¬ (4294967295 : Nat) < h.toNat := c1
    omega
  by_cases c2 : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [c1, c2] at h8
  simp only [c1, c2, if_false] at h8
  by_cases g8 : h >>> 28 = 8
  · simp only [g8] at h8
    simp (config := { decide := true }) only [↓reduceIte] at h8
    by_cases c : rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h
    · simp [c] at h8
    exact ⟨hh, ⟨c2, by simpa using c⟩, g8⟩
  exfalso
  by_cases g0 : h >>> 28 = 0
  · simp (config := { decide := true }) only [g0, ↓reduceIte] at h8; split at h8 <;> simp at h8
  simp only [g0, if_false] at h8
  by_cases g1 : h >>> 28 = 1
  · simp (config := { decide := true }) only [g1, ↓reduceIte] at h8; split at h8 <;> simp at h8
  simp only [g1, if_false] at h8
  by_cases g2 : h >>> 28 = 2
  · simp (config := { decide := true }) only [g2, ↓reduceIte] at h8; split at h8 <;> simp at h8
  simp only [g2, if_false] at h8
  by_cases g3 : h >>> 28 = 3
  · simp (config := { decide := true }) only [g3, ↓reduceIte] at h8; split at h8 <;> simp at h8
  simp only [g3, if_false] at h8
  by_cases g4 : h >>> 28 = 4
  · simp (config := { decide := true }) only [g4, ↓reduceIte] at h8; split at h8 <;> simp at h8
  simp only [g4, if_false] at h8
  by_cases g5 : h >>> 28 = 5
  · simp (config := { decide := true }) only [g5, ↓reduceIte] at h8; split at h8 <;> simp at h8
  simp only [g5, if_false] at h8
  by_cases g6 : h >>> 28 = 6
  · simp (config := { decide := true }) only [g6, ↓reduceIte] at h8; split at h8 <;> simp at h8
  simp only [g6, if_false] at h8
  by_cases g7 : h >>> 28 = 7
  · simp (config := { decide := true }) only [g7, ↓reduceIte] at h8; split at h8 <;> simp at h8
  simp only [g7, if_false] at h8
  by_cases g9 : h >>> 28 = 9
  · simp (config := { decide := true }) only [g9, ↓reduceIte] at h8; split at h8 <;> simp at h8
  simp only [g9, if_false] at h8
  simp [g8] at h8

/-- A literal handle's record: kind word, pool slice, the literal it holds. -/
theorem promote_lit_rec {m : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h 2) (hg : h >>> 28 = 8) :
    ∃ k : LitNode, a.store.view (decE h) = some (.lit k.l) ∧ RecRel m (tierW h) (idxW h) k := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h litSch RecRel litH (·.lits) _ hR.lit.2 hv.2
  refine ⟨k, ?_, hkr⟩
  rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk]; rfl

/-! ## The relation for expressions -/

/-- The arrays and `CTL` words an expression promotion writes. -/
abbrev eArrs : List ArrId :=
  lsArrs ++ [REC, SLOT, AREC, ASLOT, SOREC, SOSLOT, CREC, CSLOT, LEREC, LESLOT, BREC, BSLOT,
    FVREC, FVSLOT, LAREC, LASLOT, FAREC, FASLOT, PJREC, PJSLOT, ADER, LADER, FADER, LEDER, PJDER,
    PEM]
abbrev eCtl : List Word :=
  lsCtl ++ [2, 3, 4, 5, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27, 28, 29, 30, 31, 32, 33, 147]

/-- **What a successful run of an expression promotion gives.** -/
def PEOk (op : AM (PMemo × EIdx)) (m : Mem) (a : AState) (pm : PMemo) (r : Word) (m' : Mem) :
    Prop :=
  ∃ a' pm', op.run a = .ok ((pm', decE r), a') ∧ ArenaD m' a' ∧ PMemoR m' pm' ∧ PW r ∧
    cp a' = cp a ∧ MemFrame eArrs eCtl m m'

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

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`pe_lit` refines the literal arm** (`internPersistentE (.lit l)`, the memo untouched). -/
theorem peLit_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (h : Word) (r : List Word)
    (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm) (hh : h.toNat < 2 ^ 32) (hv : viewOK m h 2)
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
    rw [peLitW, if_neg (by rw [ltK, hk0]; decide)] at hW
    cases n with
    | zero => rw [callW_zero', hd1] at hW; cases hW
    | succ n =>
    cases hca : callW p (n + 1) "pi_lit" [ltO m h, ltL m h] m with
    | none => rw [hca] at hW; cases hW
    | some x =>
    obtain ⟨r₁, m₁⟩ := x
    rw [hca, hd1_some] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s₁, hs₁, -, hW₁⟩ := callW_triple (piLit_spec p hp n ⟨m, Locals.init []⟩ _ _) hca
    rw [hs₁, hm] at hW₁
    obtain ⟨a₁, hrun, hD₁, hpw, hcp, hfr⟩ := piLit_rel p hp n m a hD _ _ hsl hn _ _ hW₁
    rw [hpv] at hrun
    refine ⟨a₁, pm, ?_, hD₁, hP.frameLo (by simp [REC, SLOT]) (by simp) hfr, hr ▸ hpw, hcp,
      hfr.mono (by simp) (by simp)⟩
    rw [run_bind_ok hrun, ← hr]; rfl
  · simp only [RecRel_strVal, StrRec] at hkr
    obtain ⟨hk1, hsl, hks, -⟩ := hkr
    rw [peLitW, if_pos (by rw [ltK, hk1])] at hW
    cases n with
    | zero => rw [callW_zero', hd1] at hW; cases hW
    | succ n =>
    cases hca : callW p (n + 1) "pi_lit_str" [ltO m h, ltL m h] m with
    | none => rw [hca] at hW; cases hW
    | some x =>
    obtain ⟨r₁, m₁⟩ := x
    rw [hca, hd1_some] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s₁, hs₁, -, hW₁⟩ := callW_triple (piLitStr_spec p hp n ⟨m, Locals.init []⟩ _ _) hca
    rw [hs₁, hm] at hW₁
    obtain ⟨a₁, hrun, hD₁, hpw, hcp, hfr⟩ := piLitStr_rel p hp n m a hD _ _ hsl st hks _ _ hW₁
    refine ⟨a₁, pm, ?_, hD₁, hP.frameLo (by simp [REC, SLOT]) (by simp) hfr, hr ▸ hpw, hcp,
      hfr.mono (by simp) (by simp)⟩
    rw [run_bind_ok hrun, ← hr]; rfl

/-- **`pe_const` refines the `const` arm.** -/
theorem peConst_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f x us : Word) (r : List Word)
    (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm) (hx : x.toNat < 2 ^ 32)
    (hus : us.toNat < 2 ^ 32) (hc : callW p n "pe_const" [f, x, us] m = some (r, m')) :
    PEOk (peConstT pm f.toNat (decI x) (decI us)) m a pm (r.headD 0) m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (peConst_spec p hp n ⟨m, Locals.init []⟩ f x us) hc
  simp only [pe2W] at hW
  cases hca : callW p n "promote_n" [f, x] m with
  | none => rw [hca] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hca, pe2K_some] at hW
  obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁, -, -, -⟩ :=
    (pn_rel p hp n).1 m a pm f x r₁ m₁ hD hP hx hca
  cases hcb : callW p n "promote_ls" [f, us] m₁ with
  | none => rw [hcb] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hcb, pl2K₂_some] at hW
  obtain ⟨a₂, pm₂, hrun₂, hD₂, hP₂, hpw₂, hcp₂, hfr₂, -⟩ :=
    pls_rel p hp n m₁ a₁ pm₁ f us r₂ m₂ hD₁ hP₁ hus hcb
  cases n with
  | zero => rw [callW_zero', hd1] at hW; cases hW
  | succ n =>
  cases hcc : callW p (n + 1) "pi_const" [r₁.headD 0, r₂.headD 0] m₂ with
  | none => rw [hcc] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [hcc, hd1_some] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨s₃, hs₃, -, hW₃⟩ := callW_triple (piConst_spec p hp n ⟨m₂, Locals.init []⟩ _ _) hcc
  rw [hs₃] at hW₃
  obtain ⟨a₃, hrun₃, hD₃, hpw₃, hcp₃, hfr₃⟩ := piConst_rel p hp n m₂ a₂ hD₂ _ _ hpw₁ hpw₂ _ _ hW₃
  rw [← hm]
  refine ⟨a₃, pm₂, ?_, hD₃, hP₂.frameLo (by simp [CREC, CSLOT]) (by simp) hfr₃, hr ▸ hpw₃,
    hcp₃.trans (hcp₂.trans hcp₁), ?_⟩
  · unfold peConstT
    rw [run_bind_ok hrun₁]
    simp only
    rw [run_bind_ok hrun₂]
    simp only
    rw [run_bind_ok hrun₃, ← hr]; rfl
  · exact ((hfr₁.mono (by simp) (by simp)).trans (hfr₂.mono (by simp) (by simp))).trans
      (hfr₃.mono (by simp) (by simp))

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
      rw [if_pos hpers, ← hr]
      exact ⟨a, pm, rfl, hD, hP, ⟨hh, ht⟩, rfl, MemFrame.refl _ _ _⟩
    have hnp : (decE h).isPersistent = false := by
      rw [isPersistent_decE h hh]; exact beq_eq_false_iff_ne.mpr ht
    rw [if_neg (by simp [hnp])]
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
      exact ⟨_, pm, rfl, hD, hP, ⟨hw1, hw2⟩, rfl, MemFrame.refl _ _ _⟩
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
    obtain ⟨a₁, pm₁, hrun, hD₁, hP₁, hpw, hcp, hfr⟩ := ihA m a pm (f - 1) h r₁ m₁ hD hP hh hca
    refine ⟨a₁, { pm₁ with eM := pm₁.eM.insert (decE h) (decE (r₁.headD 0)) }, ?_,
      hD₁.memo peSch peSch_wf (by decide) (by decide) h _ hs,
      hP₁.setE h _ hh hpw hs, by rw [← hr]; exact hpw, hcp, ?_⟩
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
      cases n with
      | zero => rw [callW_zero', hd1] at hW; cases hW
      | succ n =>
      cases hca : callW p (n + 1) "pi_bvar" [(eViewW m h).tail.headD 0] m with
      | none => rw [hca] at hW; cases hW
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [hca, hd1_some] at hW
      obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨s₁, hs₁, -, hW₁⟩ := callW_triple (piBVar_spec p hp n ⟨m, Locals.init []⟩ _) hca
      rw [hs₁, hm] at hW₁
      obtain ⟨a₁, hrun, hD₁, hpw, hcp, hfr⟩ := piBVar_rel p hp n m a hD _ _ _ hW₁
      rw [← pmGetD1, hi] at hrun
      refine ⟨a₁, pm, ?_, hD₁, hP.frameLo (by simp [BREC, BSLOT]) (by simp) hfr, hr ▸ hpw, hcp,
        hfr.mono (by simp) (by simp)⟩
      rw [run_bind_ok hv0]
      simp only [run_bind_ok hrun, ← hr]; rfl
    | fvar i ty =>
      obtain ⟨hg, hi, hty, hty'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hi
      rw [pmGetD2] at hty hty'
      cases hca : callW p n "promote_e" [f, (eViewW m h).tail.tail.headD 0] m with
      | none => rw [hca] at hW; cases hW
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [hca, peFvK_some] at hW
      obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁⟩ := ihE m a pm f _ r₁ m₁ hD hP hty hca
      rw [hty'] at hrun₁
      cases n with
      | zero => rw [callW_zero', hd1] at hW; cases hW
      | succ n =>
      cases hcb : callW p (n + 1) "pi_fvar" [(eViewW m h).tail.headD 0, r₁.headD 0] m₁ with
      | none => rw [hcb] at hW; cases hW
      | some q =>
      obtain ⟨r₂, m₂⟩ := q
      rw [hcb, hd1_some] at hW
      obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨s₂, hs₂, -, hW₂⟩ := callW_triple (piFVar_spec p hp n ⟨m₁, Locals.init []⟩ _ _) hcb
      rw [hs₂] at hW₂
      obtain ⟨a₂, hrun₂, hD₂, hpw₂, hcp₂, hfr₂⟩ := piFVar_rel p hp n m₁ a₁ hD₁ _ _ hpw₁ _ _ hW₂
      rw [hi] at hrun₂
      rw [← hm]
      refine ⟨a₂, pm₁, ?_, hD₂, hP₁.frameLo (by simp [FVREC, FVSLOT]) (by simp) hfr₂, hr ▸ hpw₂,
        hcp₂.trans hcp₁, hfr₁.trans (hfr₂.mono (by simp) (by simp))⟩
      rw [run_bind_ok hv0]
      simp only
      rw [run_bind_ok hrun₁]
      simp only
      rw [run_bind_ok hrun₂, ← hr]; rfl
    | sort u =>
      obtain ⟨hg, hu, hu'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hu hu'
      cases hca : callW p n "promote_l" [f, (eViewW m h).tail.headD 0] m with
      | none => rw [hca] at hW; cases hW
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [hca, pl1K_some] at hW
      obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁, -, -⟩ :=
        (pl_rel p hp n).1 m a pm f _ r₁ m₁ hD hP hu hca
      rw [hu'] at hrun₁
      cases n with
      | zero => rw [callW_zero', hd1] at hW; cases hW
      | succ n =>
      cases hcb : callW p (n + 1) "pi_sort" [r₁.headD 0] m₁ with
      | none => rw [hcb] at hW; cases hW
      | some q =>
      obtain ⟨r₂, m₂⟩ := q
      rw [hcb, hd1_some] at hW
      obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨s₂, hs₂, -, hW₂⟩ := callW_triple (piSort_spec p hp n ⟨m₁, Locals.init []⟩ _) hcb
      rw [hs₂] at hW₂
      obtain ⟨a₂, hrun₂, hD₂, hpw₂, hcp₂, hfr₂⟩ := piSort_rel p hp n m₁ a₁ hD₁ _ hpw₁ _ _ hW₂
      rw [← hm]
      refine ⟨a₂, pm₁, ?_, hD₂, hP₁.frameLo (by simp [SOREC, SOSLOT]) (by simp) hfr₂, hr ▸ hpw₂,
        hcp₂.trans hcp₁, (hfr₁.mono (by simp) (by simp)).trans (hfr₂.mono (by simp) (by simp))⟩
      rw [run_bind_ok hv0]
      simp only
      rw [run_bind_ok hrun₁]
      simp only
      rw [run_bind_ok hrun₂, ← hr]; rfl
    | const x us =>
      obtain ⟨hg, hx, hx', hus, hus'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hx hx'
      rw [pmGetD2] at hus hus'
      cases hca : callW p n "pe_const" [f, (eViewW m h).tail.headD 0, (eViewW m h).tail.tail.headD 0] m with
      | none => rw [hca] at hW; cases hW
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [hca, hd1_some] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨a₁, pm₁, hrun, hD₁, hP₁, hpw, hcp, hfr⟩ := peConst_rel p hp n m a pm f _ _ r₁ _ hD hP hx hus hca
      rw [hx', hus'] at hrun
      refine ⟨a₁, pm₁, ?_, hD₁, hP₁, hr ▸ hpw, hcp, hfr⟩
      rw [run_bind_ok hv0]
      simp only
      rw [hrun, hr]
    | app u w =>
      obtain ⟨hg, hx, hx', hy, hy'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hx hx'
      rw [pmGetD2] at hy hy'
      cases hca : callW p n "pe_app" [f, (eViewW m h).tail.headD 0, (eViewW m h).tail.tail.headD 0] m with
      | none => rw [hca] at hW; cases hW
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [hca, hd1_some] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨a₁, pm₁, hrun, hD₁, hP₁, hpw, hcp, hfr⟩ := ihApp m a pm f _ _ r₁ _ hD hP hx hy hca
      rw [hx', hy'] at hrun
      refine ⟨a₁, pm₁, ?_, hD₁, hP₁, hr ▸ hpw, hcp, hfr⟩
      rw [run_bind_ok hv0]
      simp only
      rw [hrun, hr]
    | lam u w =>
      obtain ⟨hg, hx, hx', hy, hy'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hx hx'
      rw [pmGetD2] at hy hy'
      cases hca : callW p n "pe_lam" [f, (eViewW m h).tail.headD 0, (eViewW m h).tail.tail.headD 0] m with
      | none => rw [hca] at hW; cases hW
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [hca, hd1_some] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨a₁, pm₁, hrun, hD₁, hP₁, hpw, hcp, hfr⟩ := ihLam m a pm f _ _ r₁ _ hD hP hx hy hca
      rw [hx', hy'] at hrun
      refine ⟨a₁, pm₁, ?_, hD₁, hP₁, hr ▸ hpw, hcp, hfr⟩
      rw [run_bind_ok hv0]
      simp only
      rw [hrun, hr]
    | forallE u w =>
      obtain ⟨hg, hx, hx', hy, hy'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hx hx'
      rw [pmGetD2] at hy hy'
      cases hca : callW p n "pe_forall" [f, (eViewW m h).tail.headD 0, (eViewW m h).tail.tail.headD 0] m with
      | none => rw [hca] at hW; cases hW
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [hca, hd1_some] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨a₁, pm₁, hrun, hD₁, hP₁, hpw, hcp, hfr⟩ := ihFa m a pm f _ _ r₁ _ hD hP hx hy hca
      rw [hx', hy'] at hrun
      refine ⟨a₁, pm₁, ?_, hD₁, hP₁, hr ▸ hpw, hcp, hfr⟩
      rw [run_bind_ok hv0]
      simp only
      rw [hrun, hr]
    | letE t x b =>
      obtain ⟨hg, ht, ht', hx, hx', hb, hb'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at ht ht'
      rw [pmGetD2] at hx hx'
      rw [pmGetD3] at hb hb'
      cases hca : callW p n "pe_let" [f, (eViewW m h).tail.headD 0, (eViewW m h).tail.tail.headD 0,
          (eViewW m h).tail.tail.tail.headD 0] m with
      | none => rw [hca] at hW; cases hW
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [hca, hd1_some] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨a₁, pm₁, hrun, hD₁, hP₁, hpw, hcp, hfr⟩ := ihLet m a pm f _ _ _ r₁ _ hD hP ht hx hb hca
      rw [ht', hx', hb'] at hrun
      refine ⟨a₁, pm₁, ?_, hD₁, hP₁, hr ▸ hpw, hcp, hfr⟩
      rw [run_bind_ok hv0]
      simp only
      rw [hrun, hr]
    | lit l =>
      have hg : (eViewW m h).headD 0 = 8 := hvr
      obtain ⟨-, hvk, hg8⟩ := eViewW_lit hg
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      cases hca : callW p n "pe_lit" [h] m with
      | none => rw [hca] at hW; cases hW
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [hca, hd1_some] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨a₁, pm₁, hrun, hD₁, hP₁, hpw, hcp, hfr⟩ :=
        peLit_rel p hp n m a pm h r₁ _ hD hP hh hvk hg8 l hv hca
      refine ⟨a₁, pm₁, ?_, hD₁, hP₁, hr ▸ hpw, hcp, hfr⟩
      rw [run_bind_ok hv0]
      simp only
      rw [hrun, hr]
    | proj x i e =>
      obtain ⟨hg, hx, hx', hi, he, he'⟩ := hvr
      simp (config := { decide := true }) only [peK, hg, ↓reduceIte] at hW
      rw [pmGetD1] at hx hx'
      rw [pmGetD2] at hi
      rw [pmGetD3] at he he'
      cases hca : callW p n "pe_proj" [f, (eViewW m h).tail.headD 0, (eViewW m h).tail.tail.headD 0,
          (eViewW m h).tail.tail.tail.headD 0] m with
      | none => rw [hca] at hW; cases hW
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [hca, hd1_some] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨a₁, pm₁, hrun, hD₁, hP₁, hpw, hcp, hfr⟩ := ihPj m a pm f _ _ _ r₁ _ hD hP hx he hca
      rw [hx', hi, he'] at hrun
      refine ⟨a₁, pm₁, ?_, hD₁, hP₁, hr ▸ hpw, hcp, hfr⟩
      rw [run_bind_ok hv0]
      simp only
      rw [hrun, hr]
  · -- `pe_app`
    intro m a pm f x y r m' hD hP hx hy hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (peApp_spec p hp n ⟨m, Locals.init []⟩ f x y) hc
    simp only [pe2W] at hW
    cases hca : callW p n "promote_e" [f, x] m with
    | none => rw [hca] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hca, pe2K_some] at hW
    obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁⟩ := ihE m a pm f x r₁ m₁ hD hP hx hca
    cases hcb : callW p n "promote_e" [f, y] m₁ with
    | none => rw [hcb] at hW; cases hW
    | some q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [hcb, pl2K₂_some] at hW
    obtain ⟨a₂, pm₂, hrun₂, hD₂, hP₂, hpw₂, hcp₂, hfr₂⟩ := ihE m₁ a₁ pm₁ f y r₂ m₂ hD₁ hP₁ hy hcb
    cases n with
    | zero => rw [callW_zero', hd1] at hW; cases hW
    | succ n =>
    cases hcc : callW p (n + 1) "pi_app" [r₁.headD 0, r₂.headD 0] m₂ with
    | none => rw [hcc] at hW; cases hW
    | some q₃ =>
    obtain ⟨r₃, m₃⟩ := q₃
    rw [hcc, hd1_some] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s₃, hs₃, -, hW₃⟩ := callW_triple (piApp_spec p hp n ⟨m₂, Locals.init []⟩ _ _) hcc
    rw [hs₃] at hW₃
    obtain ⟨a₃, hrun₃, hD₃, hpw₃, hcp₃, hfr₃⟩ := piApp_rel p hp n m₂ a₂ hD₂ _ _ hpw₁ hpw₂ _ _ hW₃
    rw [← hm]
    refine ⟨a₃, pm₂, ?_, hD₃, hP₂.frameLo (by simp [ADER, AREC, ASLOT]) (by simp) hfr₃, hr ▸ hpw₃,
      hcp₃.trans (hcp₂.trans hcp₁), (hfr₁.trans hfr₂).trans (hfr₃.mono (by simp) (by simp))⟩
    unfold peAppT
    rw [run_bind_ok hrun₁]
    simp only
    rw [run_bind_ok hrun₂]
    simp only
    rw [run_bind_ok hrun₃, ← hr]; rfl
  · -- `pe_lam`
    intro m a pm f x y r m' hD hP hx hy hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (peLam_spec p hp n ⟨m, Locals.init []⟩ f x y) hc
    simp only [pe2W] at hW
    cases hca : callW p n "promote_e" [f, x] m with
    | none => rw [hca] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hca, pe2K_some] at hW
    obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁⟩ := ihE m a pm f x r₁ m₁ hD hP hx hca
    cases hcb : callW p n "promote_e" [f, y] m₁ with
    | none => rw [hcb] at hW; cases hW
    | some q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [hcb, pl2K₂_some] at hW
    obtain ⟨a₂, pm₂, hrun₂, hD₂, hP₂, hpw₂, hcp₂, hfr₂⟩ := ihE m₁ a₁ pm₁ f y r₂ m₂ hD₁ hP₁ hy hcb
    cases n with
    | zero => rw [callW_zero', hd1] at hW; cases hW
    | succ n =>
    cases hcc : callW p (n + 1) "pi_lam" [r₁.headD 0, r₂.headD 0] m₂ with
    | none => rw [hcc] at hW; cases hW
    | some q₃ =>
    obtain ⟨r₃, m₃⟩ := q₃
    rw [hcc, hd1_some] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s₃, hs₃, -, hW₃⟩ := callW_triple (piLam_spec p hp n ⟨m₂, Locals.init []⟩ _ _) hcc
    rw [hs₃] at hW₃
    obtain ⟨a₃, hrun₃, hD₃, hpw₃, hcp₃, hfr₃⟩ := piLam_rel p hp n m₂ a₂ hD₂ _ _ hpw₁ hpw₂ _ _ hW₃
    rw [← hm]
    refine ⟨a₃, pm₂, ?_, hD₃, hP₂.frameLo (by simp [LADER, LAREC, LASLOT]) (by simp) hfr₃, hr ▸ hpw₃,
      hcp₃.trans (hcp₂.trans hcp₁), (hfr₁.trans hfr₂).trans (hfr₃.mono (by simp) (by simp))⟩
    unfold peLamT
    rw [run_bind_ok hrun₁]
    simp only
    rw [run_bind_ok hrun₂]
    simp only
    rw [run_bind_ok hrun₃, ← hr]; rfl
  · -- `pe_forall`
    intro m a pm f x y r m' hD hP hx hy hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (peForall_spec p hp n ⟨m, Locals.init []⟩ f x y) hc
    simp only [pe2W] at hW
    cases hca : callW p n "promote_e" [f, x] m with
    | none => rw [hca] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hca, pe2K_some] at hW
    obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁⟩ := ihE m a pm f x r₁ m₁ hD hP hx hca
    cases hcb : callW p n "promote_e" [f, y] m₁ with
    | none => rw [hcb] at hW; cases hW
    | some q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [hcb, pl2K₂_some] at hW
    obtain ⟨a₂, pm₂, hrun₂, hD₂, hP₂, hpw₂, hcp₂, hfr₂⟩ := ihE m₁ a₁ pm₁ f y r₂ m₂ hD₁ hP₁ hy hcb
    cases n with
    | zero => rw [callW_zero', hd1] at hW; cases hW
    | succ n =>
    cases hcc : callW p (n + 1) "pi_forall" [r₁.headD 0, r₂.headD 0] m₂ with
    | none => rw [hcc] at hW; cases hW
    | some q₃ =>
    obtain ⟨r₃, m₃⟩ := q₃
    rw [hcc, hd1_some] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s₃, hs₃, -, hW₃⟩ := callW_triple (piForall_spec p hp n ⟨m₂, Locals.init []⟩ _ _) hcc
    rw [hs₃] at hW₃
    obtain ⟨a₃, hrun₃, hD₃, hpw₃, hcp₃, hfr₃⟩ := piForall_rel p hp n m₂ a₂ hD₂ _ _ hpw₁ hpw₂ _ _ hW₃
    rw [← hm]
    refine ⟨a₃, pm₂, ?_, hD₃, hP₂.frameLo (by simp [FADER, FAREC, FASLOT]) (by simp) hfr₃, hr ▸ hpw₃,
      hcp₃.trans (hcp₂.trans hcp₁), (hfr₁.trans hfr₂).trans (hfr₃.mono (by simp) (by simp))⟩
    unfold peForallT
    rw [run_bind_ok hrun₁]
    simp only
    rw [run_bind_ok hrun₂]
    simp only
    rw [run_bind_ok hrun₃, ← hr]; rfl

  · -- `pe_let`
    intro m a pm f x y z r m' hD hP hx hy hz hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (peLet_spec p hp n ⟨m, Locals.init []⟩ f x y z) hc
    simp only [peLetW] at hW
    cases hca : callW p n "promote_e" [f, x] m with
    | none => rw [hca] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hca, pe3K_some] at hW
    obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁⟩ := ihE m a pm f x r₁ m₁ hD hP hx hca
    cases hcb : callW p n "promote_e" [f, y] m₁ with
    | none => rw [hcb] at hW; cases hW
    | some q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [hcb, pe3K₂_some] at hW
    obtain ⟨a₂, pm₂, hrun₂, hD₂, hP₂, hpw₂, hcp₂, hfr₂⟩ := ihE m₁ a₁ pm₁ f y r₂ m₂ hD₁ hP₁ hy hcb
    cases hcc : callW p n "promote_e" [f, z] m₂ with
    | none => rw [hcc] at hW; cases hW
    | some q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [hcc, pe3K₃_some] at hW
    obtain ⟨a₃, pm₃, hrun₃, hD₃, hP₃, hpw₃, hcp₃, hfr₃⟩ := ihE m₂ a₂ pm₂ f z r₃ m₃ hD₂ hP₂ hz hcc
    cases n with
    | zero => rw [callW_zero', hd1] at hW; cases hW
    | succ n =>
    cases hcd : callW p (n + 1) "pi_let" [r₁.headD 0, r₂.headD 0, r₃.headD 0] m₃ with
    | none => rw [hcd] at hW; cases hW
    | some q₄ =>
    obtain ⟨r₄, m₄⟩ := q₄
    rw [hcd, hd1_some] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s₄, hs₄, -, hW₄⟩ := callW_triple (piLet_spec p hp n ⟨m₃, Locals.init []⟩ _ _ _) hcd
    rw [hs₄] at hW₄
    obtain ⟨a₄, hrun₄, hD₄, hpw₄, hcp₄, hfr₄⟩ :=
      piLet_rel p hp n m₃ a₃ hD₃ _ _ _ hpw₁ hpw₂ hpw₃ _ _ hW₄
    rw [← hm]
    refine ⟨a₄, pm₃, ?_, hD₄, hP₃.frameLo (by simp [LEDER, LEREC, LESLOT]) (by simp) hfr₄,
      hr ▸ hpw₄, hcp₄.trans (hcp₃.trans (hcp₂.trans hcp₁)),
      ((hfr₁.trans hfr₂).trans hfr₃).trans (hfr₄.mono (by simp) (by simp))⟩
    unfold peLetT
    rw [run_bind_ok hrun₁]
    simp only
    rw [run_bind_ok hrun₂]
    simp only
    rw [run_bind_ok hrun₃]
    simp only
    rw [run_bind_ok hrun₄, ← hr]; rfl
  · -- `pe_proj`
    intro m a pm f nm i e r m' hD hP hnm he hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (peProj_spec p hp n ⟨m, Locals.init []⟩ f nm i e) hc
    simp only [peProjW] at hW
    cases hca : callW p n "promote_n" [f, nm] m with
    | none => rw [hca] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hca, pePjK_some] at hW
    obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁, -, -, -⟩ :=
      (pn_rel p hp n).1 m a pm f nm r₁ m₁ hD hP hnm hca
    cases hcb : callW p n "promote_e" [f, e] m₁ with
    | none => rw [hcb] at hW; cases hW
    | some q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [hcb, pePjK₂_some] at hW
    obtain ⟨a₂, pm₂, hrun₂, hD₂, hP₂, hpw₂, hcp₂, hfr₂⟩ := ihE m₁ a₁ pm₁ f e r₂ m₂ hD₁ hP₁ he hcb
    cases n with
    | zero => rw [callW_zero', hd1] at hW; cases hW
    | succ n =>
    cases hcc : callW p (n + 1) "pi_proj" [r₁.headD 0, i, r₂.headD 0] m₂ with
    | none => rw [hcc] at hW; cases hW
    | some q₃ =>
    obtain ⟨r₃, m₃⟩ := q₃
    rw [hcc, hd1_some] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s₃, hs₃, -, hW₃⟩ := callW_triple (piProj_spec p hp n ⟨m₂, Locals.init []⟩ _ _ _) hcc
    rw [hs₃] at hW₃
    obtain ⟨a₃, hrun₃, hD₃, hpw₃, hcp₃, hfr₃⟩ := piProj_rel p hp n m₂ a₂ hD₂ _ i _ hpw₁ hpw₂ _ _ hW₃
    rw [← hm]
    refine ⟨a₃, pm₂, ?_, hD₃, hP₂.frameLo (by simp [PJDER, PJREC, PJSLOT]) (by simp) hfr₃,
      hr ▸ hpw₃, hcp₃.trans (hcp₂.trans hcp₁),
      ((hfr₁.mono (by simp) (by simp)).trans hfr₂).trans (hfr₃.mono (by simp) (by simp))⟩
    unfold peProjT
    rw [run_bind_ok hrun₁]
    simp only
    rw [run_bind_ok hrun₂]
    simp only
    rw [run_bind_ok hrun₃, ← hr]; rfl

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
