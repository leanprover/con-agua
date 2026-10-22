import ConAgua.Arena.DefEqMidLoops

/-!
# The batched ∀ descent: `defeq_peel` and `defeq_binders` (lane `defeq`)

The descent's loop is split for the proofs (`DefEq.lean`): `peel_leaf` (the twin's
`defeqPeelLeaf`), `peel_dom` (one level's domains), `peel_step` (the two binders' views, then the
domains), `peel_push` (the fresh free variable, pushed at the stack top), and the loop
`defeqPeelLoop` calling them. `fvs` is the stack slice `(fo, k)` with the top at `fo + k`; a
push grows it (`SpineR.push`), so the loop's post is `GrowRefP` (the stack below the old top kept,
the top grown); `defeq_binders` puts the top back.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- The lookups of this file. -/
structure PeelProg (p : Prog) : Prop where
  leaf : p.lookup "peel_leaf" = some peelLeafL
  dom : p.lookup "peel_dom" = some peelDomL
  step : p.lookup "peel_step" = some peelStepL
  push : p.lookup "peel_push" = some peelPushL
  step2 : p.lookup "peel_step2" = some peelStep2L
  peel : p.lookup "defeq_peel" = some defeqPeelL
  binders : p.lookup "defeq_binders" = some defeqBindersL
  eview : p.lookup "e_view" = some L.Ind.eView
  fvf : p.lookup "fvar_find" = some fvarFind
  fvp : p.lookup "fvar_push" = some fvarPush
  fvi : p.lookup "intern_fvar" = some internFVar

/-! ## `intern_fvar` under `CoreS` -/

theorem fvinternW_hw (m : Mem) (a : AState) (hR : FVarR m a) (u ty w : Word) (m' : Mem)
    (hI : fvinternW m u ty = some (w, m')) : HW w := by
  rw [fvinternW_eq] at hI
  exact internM_hw fvarSch FVRecRel fvhash fvarSch_wf m _ _ _ hR (fvMt m u ty) _ _ _ _
    (probe_homeG fvarSch m 0 _ _ (fvprobeW_arm m u ty 0) _)
    (probe_homeG fvarSch m 1 _ _ (fvprobeW_arm m u ty 1) _) _ (fvpushOK_room m) _ _ w m' hI

theorem fvinternW_frame (m : Mem) (u ty w : Word) (m' : Mem) (hI : fvinternW m u ty = some (w, m')) :
    MemFrame [FVREC, FVSLOT] [26, 27] m m' := by
  rw [fvinternW_eq] at hI
  exact internM_frame fvarSch fvarSch_wf _ _ _ _ _ _ _ _ hI

theorem keeps_cpl_internFVar (u : Nat) (ty : EIdx) : Keeps cpl (internE (.fvar u ty)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

/-- **`intern_fvar` as a run under `CoreS`**: the twin's `internE (.fvar u ty)`, the relation at
the same maps, the stack and `CTL[136]` untouched, a handle word. -/
theorem internFVar_core {p : Prog} (hp : PeelProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn m a vis fe M eb) (u ty : Word) (hty : HW ty) (r : List Word)
    (hc : callW p n "intern_fvar" [u, ty] m = some (r, m')) :
    CoreRef (internE (.fvar u.toNat (decE ty))) a decH dn m vis fe M eb r m' ∧
      MemFrame [FVREC, FVSLOT] [26, 27] m m' := by
  obtain ⟨s', rfl, -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internFVar_spec p hp.fvf hp.fvp hp.fvi n ⟨m, Locals.init []⟩ u ty) hc
  obtain ⟨hok, hD, hres⟩ := internFVar_D m a hS.arena u ty _ hty _ hI
  have hf := fvinternW_frame _ _ _ _ _ hI
  have hrun := AM.run_of_ok _ _ hok
  have hS' : CoreS dn s'.mem _ vis fe M eb :=
    hS.arena_frame hD (Keeps.run (keeps_cpl_internFVar _ _) hrun) hf
      (fun b hb => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl <;> decide)
      (by simp [FVREC, FVSLOT])
      (fun b hb => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl <;> decide)
      (fun x hx => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl <;> decide)
      (fun x hx => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl <;> decide)
  have hspn : s'.mem.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [FVREC, FVSLOT, SPN]) (by decide)
  have h136 : rdW (s'.mem.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  exact ⟨⟨hok, ⟨M, hS', KeptAll.refl _ _,
      ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩⟩,
    by rw [hres]; rfl, fvinternW_hw m a hS.arena.1.fvar u ty _ _ hI⟩, hf⟩

/-! ## Growing runs

`WhnfCoreProj.lean`'s `GrowRefP` with its lemmas, restated here (that file and `DefEqLeaves.lean`
both define `lsNodeW_viewLen`, so they cannot be imported together). -/

theorem StackGrew.trans' {m₁ m₂ m₃ : Mem} (h₁ : StackGrew m₁ m₂) (h₂ : StackGrew m₂ m₃) :
    StackGrew m₁ m₃ :=
  ⟨UInt64.le_trans h₁.1 h₂.1, h₂.2.1.trans h₁.2.1,
    fun i hi => (h₂.2.2 i (UInt64.lt_of_lt_of_le hi h₁.1)).trans (h₁.2.2 i hi)⟩

theorem StackKept.toGrew' {m₁ m₂ : Mem} (h : StackKept m₁ m₂) : StackGrew m₁ m₂ :=
  ⟨h.1 ▸ UInt64.le_refl _, h.2.1, h.2.2⟩

/-- `CoreRef` with the stack grown (`StackGrew`) instead of kept. -/
def GrowRefP {α : Type} [Inhabited α] (T : AM α) (a₀ : AState) (dec : List Word → α)
    (dn : NIdx → Option ConLeche.Name) (m₀ : Mem) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb : Word) (r : List Word) (m : Mem) (ok : List Word → Prop := ResH) : Prop :=
  AM.ok T a₀ ∧ (∃ M', CoreS dn m (AM.st T a₀) vis fe M' eb ∧ KeptAll M M' eb ∧ StackGrew m₀ m) ∧
    AM.res T a₀ = dec r ∧ ok r

theorem GrowRefP.of_core {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop}
    (h : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok) : GrowRefP T a₀ dec dn m₀ vis fe M eb r m ok :=
  let ⟨M', hS, hK, hSt⟩ := h.2.1
  ⟨h.1, ⟨M', hS, hK, hSt.toGrew'⟩, h.2.2.1, h.2.2.2⟩

/-- **A run, then a growing rest**. -/
theorem growRef_bind {α β : Type} [Inhabited α] [Inhabited β] {T₁ : AM α} {f : α → AM β}
    {a₀ : AState} {dec₁ : List Word → α} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name}
    {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ r : List Word}
    {ok₁ ok : List Word → Prop}
    (h₁ : GrowRefP T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb → StackGrew m₀ m₁ →
      GrowRefP (f (dec₁ r₁)) (AM.st T₁ a₀) dec dn m₁ vis fe M' eb r m ok) :
    GrowRefP (T₁ >>= f) a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨M', hS, hK, hSt⟩ := h₁.2.1
  obtain ⟨hok2, ⟨M'', hS'', hK'', hSt''⟩, hres2, hrw2⟩ := h₂ M' hS hSt
  have hT : (T₁ >>= f).run a₀ = (f (dec₁ r₁)).run (AM.st T₁ a₀) := by
    rw [StateT.run_bind, AM.run_of_ok _ _ h₁.1, h₁.2.2.1]; rfl
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (hT.trans (AM.run_of_ok _ _ hok2))
  exact ⟨hok, hst ▸ ⟨M'', hS'', hK.trans hK'', hSt.trans' hSt''⟩, hres.trans hres2, hrw2⟩

theorem growRef_ret {α : Type} [Inhabited α] {a : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {v : α} {ok : List Word → Prop} (hS : CoreS dn m a vis fe M eb)
    (hv : v = dec r) (hr : ok r) : GrowRefP (pure v) a dec dn m vis fe M eb r m ok :=
  GrowRefP.of_core (coreRef_ret hS hv hr)

/-! ## `peel_leaf` -/

section plK
variable (p : Prog) (n : Nat) (mode vis d b k fo : Word)

def plK2 (o₁ : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => call1W p n "defeq" [mode, vis, d + k, o₁, r.headD 0] m

def plK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => plK2 p n mode vis d k (r.headD 0) (callW p n "inst_list" [b, fo, k, 0] m)

variable (r : List Word) (m : Mem) (o₁ : Word)
theorem plK2_s : plK2 p n mode vis d k o₁ (some (r, m)) =
    call1W p n "defeq" [mode, vis, d + k, o₁, r.headD 0] m := rfl
theorem plK1_s : plK1 p n mode vis d b k fo (some (r, m)) =
    plK2 p n mode vis d k (r.headD 0) (callW p n "inst_list" [b, fo, k, 0] m) := rfl
end plK

theorem peelLeaf_spec (p : Prog) (hp : PeelProg p) (n : Nat) (s₀ : St) (mode vis d a b k fo : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "peel_leaf" [mode, vis, d, a, b, k, fo]
    ⦃fun r s' => LocEq s' s₀ ∧ plK1 p n mode vis d b k fo
      (callW p n "inst_list" [a, fo, k, 0] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.leaf]
  simp only [callFn, peelLeafL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "inst_list",
      callW_spec p n "defeq"] <;>
    finish [plK1_s, plK2_s, call1W_some]

/-- The common hypotheses on the slice `fvs = (fo, k)` at the top of the stack. -/
structure FvsR (m : Mem) (fo k : Word) (fvs : Array EIdx) : Prop where
  spine : SpineR m fo k fvs
  top : spTop m = fo + k
  fit : fo.toNat + k.toNat < 2 ^ 63

theorem FvsR.le_top {m : Mem} {fo k : Word} {fvs : Array EIdx} (h : FvsR m fo k fvs) :
    fo.toNat + k.toNat ≤ (spTop m).toNat := by
  rw [h.top, UInt64.toNat_add]; have := h.fit; omega

theorem FvsR.kept {m m' : Mem} {fo k : Word} {fvs : Array EIdx} (h : FvsR m fo k fvs)
    (hk : StackKept m m') (hspn : (m.arr64 SPN).size < 2 ^ 63) : FvsR m' fo k fvs :=
  ⟨h.spine.keep hk.2.1 hk.2.2 h.le_top hspn, hk.1.trans h.top, h.fit⟩

theorem word_add_toNat (d k : Word) (h : d.toNat + k.toNat < 2 ^ 64) : (d + k).toNat = d.toNat + k.toNat := by
  rw [UInt64.toNat_add]; omega

theorem toNat_zero_w : (0 : Word).toNat = 0 := rfl

/-- **`peel_leaf` refines `defeqPeelLeaf`** at the knot, from `inst_list`'s spec. -/
@[refines ConRon.Arena.defeqPeelLeaf]
theorem peelLeaf_refines (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs) (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpec p (n + 1) "peel_leaf" [mode, vis, d, a, b, k, fo]
      (defeqPeelLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs)
      decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (peelLeaf_spec p hp n s₀ mode vis d a b k fo)
  subst hs0
  refine ⟨hloc, ?_⟩
  unfold defeqPeelLeaf
  cases hc1 : callW p n "inst_list" [a, fo, k, 0] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1, plK1_s] at hW
  have e₁ := CoreSpec.of_callW (hil n s a₀ dn vis fe M eb a fo k 0 fvs hs.rel ha hx.spine hx.le_top) hc1
  rw [toNat_zero_w] at e₁
  refine coreRef_bindS e₁ (fun M₁ hS₁ hst₁ => ?_)
  have hx₁ := hx.kept hst₁ hs.rel.spn
  cases hc2 : callW p n "inst_list" [b, fo, k, 0] m₁ with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2, plK2_s] at hW
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (hil n _ _ dn vis fe M₁ eb b fo k 0 fvs hS₁ hb hx₁.spine hx₁.le_top) hc2
  rw [toNat_zero_w] at e₂
  refine coreRef_bind e₂ (fun M₂ hS₂ => ?_)
  have e₃ := CoreSpec.of_call1W (s₀ := ⟨m₂, Locals.init []⟩)
    ((hk n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode (d + k) _ _ hF hn
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₁.2.2.2 e₂.2.2.2) (fun r r' h => by simp only [decBool, h]) hW
  rw [word_add_toNat d k hdk] at e₃
  exact e₃

/-! ## `peel_dom` -/

/-- One peeled level's domains, as the twin computes them inside `defeqPeel`. -/
def peelDomT (r : CoreFnsA) (d : Nat) (da db : EIdx) (k : Nat) (fvs : Array EIdx) :
    AM (Bool × EIdx) := do
  let t1 ← instantiateListFast coreWalkFuel da fvs 0
  let t2 ← if da == db then pure t1 else instantiateListFast coreWalkFuel db fvs 0
  let dq ← if da == db then pure true else r.defeq (d + k) t1 t2
  pure (dq, t2)

/-- `(dq, t2)`. -/
def decDom (r : List Word) : Bool × EIdx := (r.headD 0 != 0, decE (r.tail.headD 0))

section pdK
variable (p : Prog) (n : Nat) (mode vis d da db k fo : Word)

def pdK3 (t₂ : Word) (res : Option (List Word × Mem)) : Option (Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => some (r.headD 0, t₂, m)

def pdK2 (t₁ : Word) (res : Option (List Word × Mem)) : Option (Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => pdK3 (r.headD 0) (callW p n "defeq" [mode, vis, d + k, t₁, r.headD 0] m)

def pdK1 (res : Option (List Word × Mem)) : Option (Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if da = db then some (1, r.headD 0, m)
    else pdK2 p n mode vis d k (r.headD 0) (callW p n "inst_list" [db, fo, k, 0] m)

variable (r : List Word) (m : Mem) (t₁ t₂ : Word)
theorem pdK3_s : pdK3 t₂ (some (r, m)) = some (r.headD 0, t₂, m) := rfl
theorem pdK2_s : pdK2 p n mode vis d k t₁ (some (r, m)) =
    pdK3 (r.headD 0) (callW p n "defeq" [mode, vis, d + k, t₁, r.headD 0] m) := rfl
theorem pdK1_eq (h : da = db) : pdK1 p n mode vis d da db k fo (some (r, m)) = some (1, r.headD 0, m) := by
  simp only [pdK1, h, ↓reduceIte]
theorem pdK1_ne (h : da ≠ db) : pdK1 p n mode vis d da db k fo (some (r, m)) =
    pdK2 p n mode vis d k (r.headD 0) (callW p n "inst_list" [db, fo, k, 0] m) := by
  simp only [pdK1, h, ↓reduceIte]
end pdK

theorem peelDom_spec (p : Prog) (hp : PeelProg p) (n : Nat) (s₀ : St) (mode vis d da db k fo : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "peel_dom" [mode, vis, d, da, db, k, fo]
    ⦃fun r s' => LocEq s' s₀ ∧ pdK1 p n mode vis d da db k fo
      (callW p n "inst_list" [da, fo, k, 0] s₀.mem) = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.dom]
  simp only [callFn, peelDomL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "inst_list",
      callW_spec p n "defeq"] <;>
    finish [pdK1_eq, pdK1_ne, pdK2_s, pdK3_s]

/-- **`peel_dom` refines `peelDomT`** (one level's domains) at the knot. -/
theorem peelDom_refines (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d da db k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW da) (hb : HW db)
    (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs) (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpec p (n + 1) "peel_dom" [mode, vis, d, da, db, k, fo]
      (peelDomT (coreKnot (decMode mode) fe id F) d.toNat (decE da) (decE db) k.toNat fvs)
      decDom s₀ a₀ dn vis fe M eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (peelDom_spec p hp n s₀ mode vis d da db k fo)
  subst hs0
  refine ⟨hloc, ?_⟩
  unfold peelDomT
  cases hc1 : callW p n "inst_list" [da, fo, k, 0] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  have e₁ := CoreSpec.of_callW (hil n s a₀ dn vis fe M eb da fo k 0 fvs hs.rel ha hx.spine hx.le_top) hc1
  rw [toNat_zero_w] at e₁
  refine coreRef_bindS e₁ (fun M₁ hS₁ hst₁ => ?_)
  by_cases he : da = db
  · rw [pdK1_eq (h := he), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
    obtain ⟨h1, h2, hm⟩ := hW
    have hbq : (decE da == decE db) = true := by rw [he]; exact beq_self_eq_true _
    simp only [hbq, ↓reduceIte, pure_bind, ← hm]
    exact coreRef_ret hS₁ (by simp only [decDom, decH, ← h1, ← h2]; rfl)
      ⟨h1 ▸ hw1, h2 ▸ e₁.2.2.2⟩
  rw [pdK1_ne (h := he)] at hW
  have hbq : (decE da == decE db) = false := by
    rw [decE_beq_eq _ _ ha hb]; simp [he]
  simp only [hbq, Bool.false_eq_true, ↓reduceIte]
  have hx₁ := hx.kept hst₁ hs.rel.spn
  cases hc2 : callW p n "inst_list" [db, fo, k, 0] m₁ with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2, pdK2_s] at hW
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (hil n _ _ dn vis fe M₁ eb db fo k 0 fvs hS₁ hb hx₁.spine hx₁.le_top) hc2
  rw [toNat_zero_w] at e₂
  refine coreRef_bind e₂ (fun M₂ hS₂ => ?_)
  cases hc3 : callW p n "defeq" [mode, vis, d + k, r₁.headD 0, r₂.headD 0] m₂ with
  | none => rw [hc3] at hW; cases hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [hc3, pdK3_s, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
  obtain ⟨h1, h2, hm⟩ := hW
  have e₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    ((hk n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode (d + k) _ _ hF hn
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₁.2.2.2 e₂.2.2.2) hc3
  rw [word_add_toNat d k hdk] at e₃
  refine coreRef_bind e₃ (fun M₃ hS₃ => ?_)
  rw [← hm]
  exact coreRef_ret hS₃ (by simp only [decDom, decBool, decH, ← h1, ← h2])
    ⟨h1 ▸ e₃.2.2.2, h2 ▸ e₂.2.2.2⟩

/-! ## `e_view` runs -/

theorem eViewW_lam (m : Mem) (h : Word) (hg : h >>> 28 = 5) (hne : L.Ind.eViewW m h ≠ []) :
    viewOK m h 28 ∧ L.Ind.eViewW m h = [5, rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2),
      rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1), 0] := by
  unfold L.Ind.eViewW at hne ⊢
  have h1 : ¬ (4294967295 : Word) < h := fun c => by simp [c] at hne
  simp only [h1, ite_false] at hne ⊢
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, ite_false] at hne ⊢
  have n0 : ¬ h >>> 28 = 0 := by rw [hg]; decide
  have n1 : ¬ h >>> 28 = 1 := by rw [hg]; decide
  have n2 : ¬ h >>> 28 = 2 := by rw [hg]; decide
  have n3 : ¬ h >>> 28 = 3 := by rw [hg]; decide
  have n4 : ¬ h >>> 28 = 4 := by rw [hg]; decide
  simp only [n0, n1, n2, n3, n4, hg, ite_false, ite_true] at hne ⊢
  by_cases c : rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h
  · simp [c] at hne
  simp only [c, ite_false]
  exact ⟨⟨hs, by simpa using c⟩, rfl⟩

/-- **A run of `e_view` at a `∀`**: the memory kept, the binder's two words, the twin's
`viewBind`. -/
theorem eView_forall_callW {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : HW h) (hg : h >>> 28 = 6)
    {r : List Word} (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ r.tail.headD 0 = rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2) ∧
      r.tail.tail.headD 0 = rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1) ∧
      HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) ∧
      a.store.viewBind (decE h) = some (decE (r.tail.headD 0), decE (r.tail.tail.headD 0)) := by
  obtain ⟨s', hm, rfl, hne, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Ind.eView_spec p hp n ⟨m, Locals.init []⟩ h) hc
  obtain ⟨hv, hw⟩ := L.Ind.eViewW_forall m h hg (hr ▸ hne)
  rw [hw] at hr
  subst hr
  obtain ⟨-, h1, h2⟩ := view_forall m a hR h hh hv hg
  exact ⟨hm.symm, rfl, rfl, h1, h2, viewBind_forall m a hR h hh hv hg⟩

/-- **A run of `e_view` at a `λ`**. -/
theorem eView_lam_callW {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : HW h) (hg : h >>> 28 = 5)
    {r : List Word} (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) ∧
      a.store.viewBind (decE h) = some (decE (r.tail.headD 0), decE (r.tail.tail.headD 0)) := by
  obtain ⟨s', hm, rfl, hne, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Ind.eView_spec p hp n ⟨m, Locals.init []⟩ h) hc
  obtain ⟨hv, hw⟩ := eViewW_lam m h hg (hr ▸ hne)
  rw [hw] at hr
  subst hr
  obtain ⟨-, h1, h2⟩ := view_lam m a hR h hh hv hg
  exact ⟨hm.symm, h1, h2, viewBind_lam m a hR h hh hv hg⟩

/-! ## `peel_step2`, `peel_step` -/

/-- The second binder and the domains, as the twin computes them inside `defeqPeel`. -/
def peelStep2T (r : CoreFnsA) (d : Nat) (da b : EIdx) (k : Nat) (fvs : Array EIdx) :
    AM (Bool × EIdx × EIdx) := do
  match ← viewBind b with
  | none => failDanglingE
  | some (db, bb) => do
    let x ← peelDomT r d da db k fvs
    pure (x.1, x.2, bb)

/-- One peeled level, as the twin computes it inside `defeqPeel`: the two binders, the domains. -/
def peelStepT (r : CoreFnsA) (d : Nat) (a b : EIdx) (k : Nat) (fvs : Array EIdx) :
    AM (Bool × EIdx × EIdx × EIdx) := do
  match ← viewBind a with
  | none => failDanglingE
  | some (da, ba) => do
    let y ← peelStep2T r d da b k fvs
    pure (y.1, y.2.1, ba, y.2.2)

/-- `(dq, t2, bb)`. -/
def decPS2 (r : List Word) : Bool × EIdx × EIdx :=
  (r.headD 0 != 0, decE (r.tail.headD 0), decE (r.tail.tail.headD 0))

/-- `(dq, t2, ba, bb)`. -/
def decPS (r : List Word) : Bool × EIdx × EIdx × EIdx :=
  (r.headD 0 != 0, decE (r.tail.headD 0), decE (r.tail.tail.headD 0),
    decE (r.tail.tail.tail.headD 0))

/-- Three result words below `2^32`. -/
def Res3' (r : List Word) : Prop := HW (r.headD 0) ∧ HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0)

/-- Four result words below `2^32`. -/
def Res4 (r : List Word) : Prop :=
  HW (r.headD 0) ∧ HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) ∧ HW (r.tail.tail.tail.headD 0)

section ps2K
variable (p : Prog) (n : Nat) (mode vis d da b k fo : Word)

def ps2K2 (rb : List Word) (res : Option (List Word × Mem)) : Option (Word × Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => some (r.headD 0, r.tail.headD 0, rb.tail.tail.headD 0, m)

def ps2K1 (res : Option (List Word × Mem)) : Option (Word × Word × Word × Mem) :=
  match res with
  | none => none
  | some (rb, m) => ps2K2 rb (callW p n "peel_dom" [mode, vis, d, da, rb.tail.headD 0, k, fo] m)

def psK2 (ra : List Word) (res : Option (List Word × Mem)) :
    Option (Word × Word × Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => some (r.headD 0, r.tail.headD 0, ra.tail.tail.headD 0, r.tail.tail.headD 0, m)

def psK1 (res : Option (List Word × Mem)) : Option (Word × Word × Word × Word × Mem) :=
  match res with
  | none => none
  | some (ra, m) => psK2 ra (callW p n "peel_step2" [mode, vis, d, ra.tail.headD 0, b, k, fo] m)

variable (r ra rb : List Word) (m : Mem)
theorem ps2K2_s : ps2K2 rb (some (r, m)) = some (r.headD 0, r.tail.headD 0, rb.tail.tail.headD 0, m) := rfl
theorem ps2K1_s : ps2K1 p n mode vis d da k fo (some (rb, m)) =
    ps2K2 rb (callW p n "peel_dom" [mode, vis, d, da, rb.tail.headD 0, k, fo] m) := rfl
theorem psK2_s : psK2 ra (some (r, m)) =
    some (r.headD 0, r.tail.headD 0, ra.tail.tail.headD 0, r.tail.tail.headD 0, m) := rfl
theorem psK1_s : psK1 p n mode vis d b k fo (some (ra, m)) =
    psK2 ra (callW p n "peel_step2" [mode, vis, d, ra.tail.headD 0, b, k, fo] m) := rfl
end ps2K

theorem peelStep2_spec (p : Prog) (hp : PeelProg p) (n : Nat) (s₀ : St) (mode vis d da b k fo : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "peel_step2" [mode, vis, d, da, b, k, fo]
    ⦃fun r s' => LocEq s' s₀ ∧ ps2K1 p n mode vis d da k fo (callW p n "e_view" [b] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.step2]
  simp only [callFn, peelStep2L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "e_view",
      callW_spec p n "peel_dom"] <;>
    finish (gen := 50) [ps2K1_s, ps2K2_s, St.setLocs_mem']

theorem peelStep_spec (p : Prog) (hp : PeelProg p) (n : Nat) (s₀ : St) (mode vis d a b k fo : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "peel_step" [mode, vis, d, a, b, k, fo]
    ⦃fun r s' => LocEq s' s₀ ∧ psK1 p n mode vis d b k fo (callW p n "e_view" [a] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.step]
  simp only [callFn, peelStepL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "e_view",
      callW_spec p n "peel_step2"] <;>
    finish (gen := 50) [psK1_s, psK2_s, St.setLocs_mem']

/-- **`peel_step2` refines `peelStep2T`** at a `∀` handle `b`. -/
theorem peelStep2_refines (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d da b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hda : HW da) (hb : HW b)
    (hg : b >>> 28 = 6) (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs)
    (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpec p (n + 1) "peel_step2" [mode, vis, d, da, b, k, fo]
      (peelStep2T (coreKnot (decMode mode) fe id F) d.toNat (decE da) (decE b) k.toNat fvs)
      decPS2 s₀ a₀ dn vis fe M eb Res3' := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (peelStep2_spec p hp n s₀ mode vis d da b k fo)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc1 : callW p n "e_view" [b] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1, ps2K1_s] at hW
  obtain ⟨rfl, -, -, hw1, hw2, hvb⟩ := eView_forall_callW (a := a₀) hp.eview hs.rel.arena.1 hb hg hc1
  have hT : (peelStep2T (coreKnot (decMode mode) fe id F) d.toNat (decE da) (decE b) k.toNat fvs).run a₀ =
      (peelDomT (coreKnot (decMode mode) fe id F) d.toNat (decE da) (decE (r₁.tail.headD 0)) k.toNat fvs
        >>= fun x => pure (x.1, x.2, decE (r₁.tail.tail.headD 0))).run a₀ := by
    simp only [peelStep2T, StateT.run_bind, viewBind_run', hvb, except_ok_bind]
  refine coreRef_congr hT ?_
  cases hc2 : callW p n "peel_dom" [mode, vis, d, da, r₁.tail.headD 0, k, fo] s.mem with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2, ps2K2_s, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
  obtain ⟨h1, h2, h3, hm⟩ := hW
  obtain ⟨n', rfl⟩ := callW_succ hc2
  have e₂ := CoreSpec.of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
    (peelDom_refines p hp hil n' (hk.mono (by omega)) F (by omega) (by omega) ⟨s.mem, Locals.init []⟩ a₀ dn vis fe M eb
      mode d da _ k fo ⟨hs.rel, hs.mode4, hs.eb_mode⟩ hda hw1 fvs hx hdk) hc2
  refine coreRef_bind e₂ (fun M₂ hS₂ => ?_)
  rw [← hm]
  exact coreRef_ret hS₂ (by simp only [decPS2, decDom, ← h1, ← h2, ← h3])
    ⟨h1 ▸ e₂.2.2.2.1, h2 ▸ e₂.2.2.2.2, h3 ▸ hw2⟩

/-- **`peel_step` refines `peelStepT`** at two `∀` handles. -/
theorem peelStep_refines (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (hga : a >>> 28 = 6) (hgb : b >>> 28 = 6) (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs)
    (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpec p (n + 1) "peel_step" [mode, vis, d, a, b, k, fo]
      (peelStepT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs)
      decPS s₀ a₀ dn vis fe M eb Res4 := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (peelStep_spec p hp n s₀ mode vis d a b k fo)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc1 : callW p n "e_view" [a] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1, psK1_s] at hW
  obtain ⟨rfl, -, -, hw1, hw2, hvb⟩ := eView_forall_callW (a := a₀) hp.eview hs.rel.arena.1 ha hga hc1
  have hT : (peelStepT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs).run a₀ =
      (peelStep2T (coreKnot (decMode mode) fe id F) d.toNat (decE (r₁.tail.headD 0)) (decE b) k.toNat fvs
        >>= fun y => pure (y.1, y.2.1, decE (r₁.tail.tail.headD 0), y.2.2)).run a₀ := by
    simp only [peelStepT, StateT.run_bind, viewBind_run', hvb, except_ok_bind]
  refine coreRef_congr hT ?_
  cases hc2 : callW p n "peel_step2" [mode, vis, d, r₁.tail.headD 0, b, k, fo] s.mem with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2, psK2_s, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq,
    Prod.mk.injEq] at hW
  obtain ⟨h1, h2, h3, h4, hm⟩ := hW
  obtain ⟨n', rfl⟩ := callW_succ hc2
  have e₂ := CoreSpec.of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
    (peelStep2_refines p hp hil n' (hk.mono (by omega)) F (by omega) (by omega) ⟨s.mem, Locals.init []⟩ a₀ dn vis fe M eb
      mode d _ b k fo ⟨hs.rel, hs.mode4, hs.eb_mode⟩ hw1 hb hgb fvs hx hdk) hc2
  refine coreRef_bind e₂ (fun M₂ hS₂ => ?_)
  rw [← hm]
  exact coreRef_ret hS₂ (by simp only [decPS, decPS2, ← h1, ← h2, ← h3, ← h4])
    ⟨h1 ▸ e₂.2.2.2.1, h2 ▸ e₂.2.2.2.2.1, h3 ▸ hw2, h4 ▸ e₂.2.2.2.2.2⟩

end L.Arena
