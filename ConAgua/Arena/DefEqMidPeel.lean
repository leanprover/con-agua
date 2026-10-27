import ConAgua.Arena.DefEqMidLoops
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

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
  exact consInternM_lt fvarCS_wf hR hI

theorem peel_keeps_cpl_internFVar (u : Nat) (ty : EIdx) : Keeps cpl (internE (.fvar u ty)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

/-- **`intern_fvar` as a run under `CoreS`**: the twin's `internE (.fvar u ty)`, the relation at
the same maps, the stack and `CTL[136]` untouched, a handle word. -/
theorem peel_internFVar_core {p : Prog} (hp : PeelProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn m a vis fe M eb) (u ty : Word) (hty : HW ty) (r : List Word)
    (hc : callW p n "intern_fvar" [u, ty] m = some (r, m')) :
    CoreRef (internE (.fvar u.toNat (decE ty))) a decH dn m vis fe M eb r m' ∧
      MemFrame [FVREC, FVREC + 256, FVSLOT, FVSLOT + 256, FVLP, FVLP + 256] [26, 27] m m' := by
  obtain ⟨s', rfl, -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internFVar_spec p hp.fvf hp.fvp hp.fvi n ⟨m, Locals.init []⟩ u ty) hc
  obtain ⟨hok, hD, hres⟩ := internFVar_D m a hS.arena u ty _ hty _ hI
  have hf := fvinternW_frame _ _ _ _ _ hI
  have hrun := AM.run_of_ok _ _ hok
  have hS' : CoreS dn s'.mem _ vis fe M eb :=
    hS.arena_frame hD (Keeps.run (peel_keeps_cpl_internFVar _ _) hrun) hf
      (fun b hb => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp [FVREC, FVSLOT, FVLP])
      (fun b hb => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (fun x hx => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl <;> decide)
      (fun x hx => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl <;> decide)
  have hspn : s'.mem.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [FVREC, FVSLOT, FVLP, SPN]) (by decide)
  have h136 : rdW (s'.mem.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  exact ⟨⟨hok, ⟨M, hS', KeptAll.refl _ _,
      StackKept.of_frame hf⟩,
    by rw [hres]; rfl, fvinternW_hw m a hS.arena.1.fvar u ty _ _ hI⟩, hf⟩

/-! ## Growing runs

`WhnfCoreProj.lean`'s `GrowRefP` with its lemmas, restated here (that file and `DefEqLeaves.lean`
both defined `lsNodeW_viewLen`, so they could not be imported together; DefEqLeaves' copy is now `defeq_lsNodeW_viewLen`). -/

theorem StackGrew.trans' {m₁ m₂ m₃ : Mem} (h₁ : StackGrew m₁ m₂) (h₂ : StackGrew m₂ m₃) :
    StackGrew m₁ m₃ :=
  h₁.trans h₂

theorem StackKept.toGrew' {m₁ m₂ : Mem} (h : StackKept m₁ m₂) : StackGrew m₁ m₂ :=
  h.toGrew

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
  ⟨h.spine.keep hk.size hk.below h.le_top hspn, hk.1.trans h.top, h.fit⟩

theorem peel_word_add_toNat (d k : Word) (h : d.toNat + k.toNat < 2 ^ 64) : (d + k).toNat = d.toNat + k.toNat := by
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
  rw [peel_word_add_toNat d k hdk] at e₃
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
  rw [peel_word_add_toNat d k hdk] at e₃
  refine coreRef_bind e₃ (fun M₃ hS₃ => ?_)
  rw [← hm]
  exact coreRef_ret hS₃ (by simp only [decDom, decBool, decH, ← h1, ← h2])
    ⟨h1 ▸ e₃.2.2.2, h2 ▸ e₂.2.2.2⟩

/-! ## `e_view` runs -/

theorem eViewW_lam (m : Mem) (h : Word) (hg : h >>> 28 = 5) (hne : L.Ind.eViewW m h ≠ []) :
    viewOK m h LAM ∧ L.Ind.eViewW m h = [5, tfld m LAM (tierW h) (idxW h) 0,
      tfld m LAM (tierW h) (idxW h) 1, 0] := by
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
  simp only [hg, ite_true] at hne ⊢
  by_cases c : tcnt m LAM (tierW h) ≤ idxW h
  · simp [c] at hne
  simp only [c, ite_false]
  exact ⟨⟨hs, by simpa using c⟩, rfl⟩

/-- **A run of `e_view` at a `∀`**: the memory kept, the binder's two words, the twin's
`viewBind`. -/
theorem eView_forall_callW {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : HW h) (hg : h >>> 28 = 6)
    {r : List Word} (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ r.tail.headD 0 = tfld m FORALL (tierW h) (idxW h) 0 ∧
      r.tail.tail.headD 0 = tfld m FORALL (tierW h) (idxW h) 1 ∧
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

/-! ## `peel_push` -/

/-- A slice survives a change that leaves the stack array alone. -/
theorem SpineR.of_spnP {m m' : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (hs : m'.arr64 SPN = m.arr64 SPN) : SpineR m' off cnt xs := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, by rw [hs]; exact h2, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [spW, hs] at h3 ⊢; exact h3 i hi
  · simp only [spW, hs] at h4 ⊢; exact h4 i hi

/-- The model of `peel_push` past `intern_fvar`'s run: the word at `fo + k`, the top at
`fo + k + 1`. -/
def peelPushK (fo k : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if (fo + k).toNat < (m.arr64 144).size ∧ 136 < (m.arr64 1).size then
      some (r.headD 0, (m.set64 144 (fo + k) (r.headD 0)).set64 1 136 (fo + k + 1))
    else none

theorem pushK_ok (fo k : Word) (r : List Word) (m : Mem) (h1 : (fo + k).toNat < (m.arr64 144).size)
    (h2 : 136 < (m.arr64 1).size) :
    peelPushK fo k (some (r, m)) = some (r.headD 0, (m.set64 144 (fo + k) (r.headD 0)).set64 1 136 (fo + k + 1)) := by
  simp only [peelPushK, h1, h2, and_self, ↓reduceIte]

theorem peelPush_spec (p : Prog) (hp : PeelProg p) (n : Nat) (s₀ : St) (d k fo t2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "peel_push" [d, k, fo, t2]
    ⦃fun r s' => LocEq s' s₀ ∧ peelPushK fo k (callW p n "intern_fvar" [d + k, t2] s₀.mem) =
      some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.push]
  simp only [callFn, peelPushL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, callW_spec p n "intern_fvar"] <;>
    finish [pushK_ok]

/-- **A run of `peel_push`**: the twin's `internFVarE (d + k) t2`, the slice `fvs` grown by the
new free variable, the top at `fo + k + 1`. -/
theorem peelPush_run {p : Prog} (hp : PeelProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn m a vis fe M eb) (d k fo t2 : Word) (ht : HW t2) (fvs : Array EIdx)
    (hx : FvsR m fo k fvs)
    (hdk : d.toNat + k.toNat < 2 ^ 64) (r : List Word)
    (hc : callW p (n + 1) "peel_push" [d, k, fo, t2] m = some (r, m')) :
    GrowRefP (internFVarE (d.toNat + k.toNat) (decE t2)) a decH dn m vis fe M eb r m' ∧
      FvsR m' fo (k + 1) (fvs.push (decE (r.headD 0))) := by
  unfold internFVarE
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (peelPush_spec p hp n ⟨m, Locals.init []⟩ d k fo t2) hc
  cases hc1 : callW p n "intern_fvar" [d + k, t2] m with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  simp only [peelPushK] at hW
  split at hW
  · rename_i hb
    obtain ⟨hb1, hb2⟩ := hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨e₁, hf₁⟩ := peel_internFVar_core hp hS (d + k) t2 ht r₁ hc1
    rw [peel_word_add_toNat d k hdk] at e₁
    obtain ⟨hok, ⟨M₁, hS₁, hK₁, hst₁⟩, hres, hw⟩ := e₁
    have hfvs₁ := hx.kept hst₁ hS.spn
    have hfoK : (fo + k).toNat = fo.toNat + k.toNat := by
      rw [UInt64.toNat_add]; have := hx.fit; omega
    have hk1 : fo.toNat + k.toNat + 1 < 2 ^ 63 := by
      have e : (m₁.arr64 144).size = (m.arr64 SPN).size := hf₁.2.2.1 SPN
      have := hS.spn; omega
    have hpush := hfvs₁.spine.push (hf₁.2.2.1 SPN ▸ hS.spn) (by rw [← hfoK]; exact hb1) _ hw
    -- the two writes
    have hfr : MemFrame [SPN] [136] m₁ s'.mem := by
      rw [← hm]
      exact (MemFrame.set64 m₁ 144 (by decide) _ _).mono (by simp) (by simp) |>.trans
        ((MemFrame.setCtl _ 136 _).mono (by simp) (by simp))
    have hS₂ := hS₁.frame_stk hfr (by simp) (by simp)
    have hspn' : s'.mem.arr64 SPN = (m₁.set64 144 (fo + k) (r₁.headD 0)).arr64 SPN := by
      rw [← hm]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have htop : spTop s'.mem = fo + k + 1 := by
      rw [← hm]; unfold spTop
      rw [rdW_set64L, ite_eq_left ⟨rfl, rfl, by rw [size_set64L]; exact hb2⟩]
    have hk1' : (k + 1).toNat = k.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; have := hx.fit; omega
    refine ⟨⟨hok, ⟨M₁, hS₂, hK₁, ?_⟩, by rw [hres, decH, hr]; rfl, by unfold ResH; rw [← hr]; exact hw⟩,
      ⟨by rw [← hr]; exact hpush.of_spnP hspn', by rw [htop, UInt64.add_assoc], by rw [hk1']; omega⟩⟩
    -- the stack grew
    have hsz : (s'.mem.arr64 SPN).size = (m.arr64 SPN).size := by
      rw [hspn', size_set64L]; exact hst₁.size
    refine ⟨?_, hsz, fun i hi => ?_, hst₁.bstk.trans (BKept.of_frame hfr (by decide) (by decide)),
      hst₁.pool.trans (PoolGrew.of_frame hfr (by decide) (by decide))⟩
    · rw [htop, hx.top, UInt64.le_iff_toNat_le]
      simp only [UInt64.toNat_add, UInt64.toNat_one]
      have := hx.fit; omega
    · have hi' : i ≠ fo + k := fun h => by rw [h, ← hx.top] at hi; exact absurd hi (by simp)
      unfold spW
      rw [hspn', show (144 : ArrId) = SPN from rfl, rdW_set64L, ite_eq_right (fun h => hi' h.2.1.symm)]
      exact hst₁.below i hi
  · cases hW

/-! ## The twin's descent, one level at a time -/

theorem viewBind_bind_run {β : Type} (h : EIdx) (f : Option (EIdx × EIdx) → AM β) (s : AState) :
    (viewBind h >>= f).run s = (f (s.store.viewBind h)).run s := by
  simp only [StateT.run_bind, viewBind_run', except_ok_bind]

/-- One level of the twin's `defeqPeel`, verbatim, the recursive call abstracted as `cont` (the
equation compiler cannot produce `defeqPeel`'s unfolding lemma in its heartbeat budget; con-ron's
`Bridge/Core/Arms/DefeqPeel.lean` states the two unfoldings the same way, by `delta` and `rfl`). -/
def peelLvl (r : CoreFnsA) (d : Nat) (peel : Nat)
    (cont : EIdx → EIdx → Nat → Array EIdx → AM Bool)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) : AM Bool := do
  if a == b then pure true
  else if peel = 0 || a.tag != ETag.forallE || b.tag != ETag.forallE then
    defeqPeelLeaf r d a b k fvs
  else
    match ← viewBind a with
    | none => failDanglingE
    | some (da, ba) =>
      match ← viewBind b with
      | none => failDanglingE
      | some (db, bb) => do
        let sameDom := da == db
        let t1 ← instantiateListFast coreWalkFuel da fvs 0
        let t2 ← if sameDom then pure t1
                 else instantiateListFast coreWalkFuel db fvs 0
        let dq ← if sameDom then pure true else r.defeq (d + k) t1 t2
        if !dq then pure false
        else do
          let fv ← internFVarE (d + k) t2
          cont ba bb (k + 1) (fvs.push fv)

theorem defeqPeel_succ_eq (r : CoreFnsA) (d p : Nat) (a b : EIdx) (k : Nat) (fvs : Array EIdx) :
    defeqPeel r d (p + 1) a b k fvs = peelLvl r d (p + 1) (defeqPeel r d p) a b k fvs := by
  delta defeqPeel peelLvl
  exact rfl

theorem defeqPeel_zero_eq (r : CoreFnsA) (d : Nat) (a b : EIdx) (k : Nat) (fvs : Array EIdx) :
    defeqPeel r d 0 a b k fvs = peelLvl r d 0 (defeqPeelLeaf r d) a b k fvs := by
  delta defeqPeel peelLvl
  exact rfl

theorem peelLvl_eq_run (r : CoreFnsA) (d peel : Nat) (cont : EIdx → EIdx → Nat → Array EIdx → AM Bool)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) (s : AState) (h : (a == b) = true) :
    (peelLvl r d peel cont a b k fvs).run s = .ok (true, s) := by
  simp only [peelLvl, h, ↓reduceIte]; rfl

theorem peelLvl_leaf_run (r : CoreFnsA) (d peel : Nat) (cont : EIdx → EIdx → Nat → Array EIdx → AM Bool)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) (s : AState) (h : (a == b) = false)
    (hl : (decide (peel = 0) || a.tag != ETag.forallE || b.tag != ETag.forallE) = true) :
    (peelLvl r d peel cont a b k fvs).run s = (defeqPeelLeaf r d a b k fvs).run s := by
  simp only [peelLvl, h, hl, Bool.false_eq_true, ↓reduceIte]

theorem peelLvl_step_run (r : CoreFnsA) (d peel : Nat) (cont : EIdx → EIdx → Nat → Array EIdx → AM Bool)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) (s : AState) (h : (a == b) = false)
    (hl : (decide (peel = 0) || a.tag != ETag.forallE || b.tag != ETag.forallE) = false) :
    (peelLvl r d peel cont a b k fvs).run s = (peelStepT r d a b k fvs >>= fun x =>
      if !x.1 then pure false else do
        let fv ← internFVarE (d + k) x.2.1
        cont x.2.2.1 x.2.2.2 (k + 1) (fvs.push fv)).run s := by
  simp only [peelLvl, h, hl, Bool.false_eq_true, ↓reduceIte, peelStepT, bind_assoc]
  rw [viewBind_bind_run, viewBind_bind_run]
  cases s.store.viewBind a with
  | none => rfl
  | some x =>
  obtain ⟨da, ba⟩ := x
  simp only [peelStep2T, bind_assoc, pure_bind]
  rw [viewBind_bind_run, viewBind_bind_run]
  cases s.store.viewBind b with
  | none => rfl
  | some y =>
  obtain ⟨db, bb⟩ := y
  simp only [peelDomT, bind_assoc, pure_bind]
  cases hdd : (da == db) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind, Bool.not_true]

/-! ## `defeq_peel`: the loop -/

/-- **The model of `defeq_peel`'s loop** at L fuel `j`. -/
def peelW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | j + 1, m, mode, vis, d, peel, a, b, k, fo =>
    if a = b then some (1, m)
    else if peel = 0 ∨ a >>> 28 ≠ 6 ∨ b >>> 28 ≠ 6 then
      call1W p j "peel_leaf" [mode, vis, d, a, b, k, fo] m
    else match callW p j "peel_step" [mode, vis, d, a, b, k, fo] m with
      | none => none
      | some (r, m₁) =>
        if r.headD 0 = 0 then some (0, m₁)
        else match callW p j "peel_push" [d, k, fo, r.tail.headD 0] m₁ with
          | none => none
          | some (_, m₂) => peelW p j m₂ mode vis d (peel - 1) (r.tail.tail.headD 0)
              (r.tail.tail.tail.headD 0) (k + 1) fo

section peelArms
variable (p : Prog) (j : Nat) (m m₁ m₂ : Mem) (mode vis d peel a b k fo : Word) (r r₂ : List Word)

theorem peelW_eq (h : a = b) : peelW p (j + 1) m mode vis d peel a b k fo = some (1, m) := by
  simp only [peelW, h, ↓reduceIte]
theorem peelW_leaf (h : ¬ a = b) (hl : peel = 0 ∨ a >>> 28 ≠ 6 ∨ b >>> 28 ≠ 6) :
    peelW p (j + 1) m mode vis d peel a b k fo = call1W p j "peel_leaf" [mode, vis, d, a, b, k, fo] m := by
  simp only [peelW, h, hl, ↓reduceIte]
theorem peelW_n1 (h : ¬ a = b) (hl : ¬ (peel = 0 ∨ a >>> 28 ≠ 6 ∨ b >>> 28 ≠ 6))
    (hc : callW p j "peel_step" [mode, vis, d, a, b, k, fo] m = none) :
    peelW p (j + 1) m mode vis d peel a b k fo = none := by
  simp only [peelW, h, hl, hc, ↓reduceIte]
theorem peelW_stop (h : ¬ a = b) (hl : ¬ (peel = 0 ∨ a >>> 28 ≠ 6 ∨ b >>> 28 ≠ 6))
    (hc : callW p j "peel_step" [mode, vis, d, a, b, k, fo] m = some (r, m₁)) (h0 : r.headD 0 = 0) :
    peelW p (j + 1) m mode vis d peel a b k fo = some (0, m₁) := by
  simp only [peelW, h, hl, hc, h0, ↓reduceIte]
theorem peelW_n2 (h : ¬ a = b) (hl : ¬ (peel = 0 ∨ a >>> 28 ≠ 6 ∨ b >>> 28 ≠ 6))
    (hc : callW p j "peel_step" [mode, vis, d, a, b, k, fo] m = some (r, m₁)) (h0 : ¬ r.headD 0 = 0)
    (hc2 : callW p j "peel_push" [d, k, fo, r.tail.headD 0] m₁ = none) :
    peelW p (j + 1) m mode vis d peel a b k fo = none := by
  simp only [peelW, h, hl, hc, h0, hc2, ↓reduceIte]
theorem peelW_cont (h : ¬ a = b) (hl : ¬ (peel = 0 ∨ a >>> 28 ≠ 6 ∨ b >>> 28 ≠ 6))
    (hc : callW p j "peel_step" [mode, vis, d, a, b, k, fo] m = some (r, m₁)) (h0 : ¬ r.headD 0 = 0)
    (hc2 : callW p j "peel_push" [d, k, fo, r.tail.headD 0] m₁ = some (r₂, m₂)) :
    peelW p (j + 1) m mode vis d peel a b k fo = peelW p j m₂ mode vis d (peel - 1)
      (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) (k + 1) fo := by
  simp only [peelW, h, hl, hc, h0, hc2, ↓reduceIte]

end peelArms

theorem defeqPeelLoop_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n defeqPeelLoop
    ⦃fun r s' => r ≠ .brk ∧
      peelW p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)
        (s₀.loc 6) (s₀.loc 7) = some ((r.retOr [0]).headD 0, s'.mem) ∧ r ≠ .normal; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := defeqPeelLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih, callW_spec p n "peel_leaf",
        callW_spec p n "peel_step", callW_spec p n "peel_push"] <;>
      finish (gen := 50) [peelW_eq, peelW_leaf, peelW_n1, peelW_stop, peelW_n2, peelW_cont, call1W_some,
        St.setLocs_mem']

theorem defeqPeel_spec (p : Prog) (hp : PeelProg p) (n : Nat) (s₀ : St)
    (mode vis d peel a b k fo : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_peel" [mode, vis, d, peel, a, b, k, fo]
    ⦃fun r s' => LocEq s' s₀ ∧ peelW p (n + 1) s₀.mem mode vis d peel a b k fo =
      some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.peel]
  simp only [callFn, defeqPeelL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (defeqPeelLoop_spec p (n + 1) s)] <;>
    finish

/-! ## The loop refines `defeqPeel` -/

theorem growRef_congr {α : Type} [Inhabited α] {T T' : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (h : T.run a₀ = T'.run a₀)
    (h' : GrowRefP T' a₀ dec dn m₀ vis fe M eb r m ok) : GrowRefP T a₀ dec dn m₀ vis fe M eb r m ok := by
  unfold GrowRefP AM.ok AM.st AM.res at *; rw [h]; exact h'

/-- **A kept-stack run, then a growing rest.** -/
theorem growRef_bindK {α β : Type} [Inhabited α] [Inhabited β] {T₁ : AM α} {f : α → AM β}
    {a₀ : AState} {dec₁ : List Word → α} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name}
    {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ r : List Word}
    {ok₁ ok : List Word → Prop}
    (h₁ : CoreRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb → StackKept m₀ m₁ →
      GrowRefP (f (dec₁ r₁)) (AM.st T₁ a₀) dec dn m₁ vis fe M' eb r m ok) :
    GrowRefP (T₁ >>= f) a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨M', hS, hK, hSt⟩ := h₁.2.1
  obtain ⟨hok2, ⟨M'', hS'', hK'', hSt''⟩, hres2, hrw2⟩ := h₂ M' hS hSt
  have hT : (T₁ >>= f).run a₀ = (f (dec₁ r₁)).run (AM.st T₁ a₀) := by
    rw [StateT.run_bind, AM.run_of_ok _ _ h₁.1, h₁.2.2.1]; rfl
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (hT.trans (AM.run_of_ok _ _ hok2))
  exact ⟨hok, hst ▸ ⟨M'', hS'', hK.trans hK'', hSt.toGrew'.trans' hSt''⟩, hres.trans hres2, hrw2⟩

theorem defeqPeel_eq_run (r : CoreFnsA) (d peel : Nat) (a b : EIdx) (k : Nat) (fvs : Array EIdx)
    (s : AState) (h : (a == b) = true) : (defeqPeel r d peel a b k fvs).run s = .ok (true, s) := by
  cases peel with
  | zero => rw [defeqPeel_zero_eq]; exact peelLvl_eq_run _ _ _ _ _ _ _ _ _ h
  | succ p => rw [defeqPeel_succ_eq]; exact peelLvl_eq_run _ _ _ _ _ _ _ _ _ h

theorem defeqPeel_leaf_run (r : CoreFnsA) (d peel : Nat) (a b : EIdx) (k : Nat) (fvs : Array EIdx)
    (s : AState) (h : (a == b) = false)
    (hl : (decide (peel = 0) || a.tag != ETag.forallE || b.tag != ETag.forallE) = true) :
    (defeqPeel r d peel a b k fvs).run s = (defeqPeelLeaf r d a b k fvs).run s := by
  cases peel with
  | zero => rw [defeqPeel_zero_eq]; exact peelLvl_leaf_run _ _ _ _ _ _ _ _ _ h hl
  | succ p => rw [defeqPeel_succ_eq]; exact peelLvl_leaf_run _ _ _ _ _ _ _ _ _ h hl

theorem tag_forall_beq (h : Word) (hh : HW h) : ((decE h).tag == ETag.forallE) = decide (h >>> 28 = 6) :=
  tag_beq_w h hh 6 (by decide) _ rfl 6 rfl

theorem word_toNat_zero_iff (w : Word) : w.toNat = 0 ↔ w = 0 :=
  ⟨fun h => UInt64.toNat_inj.mp (by simpa using h), fun h => by rw [h]; rfl⟩

section loopRef
variable (p : Prog) (hp : PeelProg p) (hil : InstListOK p)

include hp hil in
/-- **The loop's model refines `defeqPeel`** at the knot. -/
theorem peelW_ok (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d fo : Word)
    (hmode : mode < 4) :
    ∀ j, j ≤ n + 1 → ∀ (peel a b k : Word) (m m' : Mem) (s : AState) (M : ModeMaps) (eb v : Word)
      (fvs : Array EIdx), CoreS dn m s vis fe M eb → eb = (mode >>> 1) &&& 1 → HW a → HW b →
      FvsR m fo k fvs → d.toNat + k.toNat + peel.toNat < 2 ^ 64 →
      peelW p j m mode vis d peel a b k fo = some (v, m') →
      GrowRefP (defeqPeel (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE a) (decE b)
        k.toNat fvs) s decBool dn m vis fe M eb [v] m' := by
  intro j
  induction j with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [peelW] at h
  | succ j ih =>
    intro hjn peel a b k m m' s M eb v fvs hS heb ha hb hx hdk h
    have hab : (decE a == decE b) = decide (a = b) := decE_beq_eq _ _ ha hb
    by_cases he : a = b
    · rw [peelW_eq (h := he), Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hr := defeqPeel_eq_run (coreKnot (decMode mode) fe id F) d.toNat peel.toNat _ _ k.toNat
        fvs s (by rw [hab]; simp [he])
      exact growRef_congr (T' := pure true) (by rw [hr]; rfl) (growRef_ret hS rfl resH_one)
    have hab' : (decE a == decE b) = false := by rw [hab]; simp [he]
    have hlw : (decide (peel.toNat = 0) || (decE a).tag != ETag.forallE ||
        (decE b).tag != ETag.forallE) = decide (peel = 0 ∨ a >>> 28 ≠ 6 ∨ b >>> 28 ≠ 6) := by
      simp only [bne, tag_forall_beq a ha, tag_forall_beq b hb, word_toNat_zero_iff]
      by_cases h1 : peel = 0 <;> by_cases h2 : a >>> 28 = 6 <;> by_cases h3 : b >>> 28 = 6 <;>
        simp [h1, h2, h3]
    by_cases hl : peel = 0 ∨ a >>> 28 ≠ 6 ∨ b >>> 28 ≠ 6
    · rw [peelW_leaf (h := he) (hl := hl)] at h
      obtain ⟨j', rfl⟩ := call1W_succ h
      have hr := defeqPeel_leaf_run (coreKnot (decMode mode) fe id F) d.toNat peel.toNat _ _ k.toNat
        fvs s hab' (by rw [hlw]; simp [hl])
      refine growRef_congr hr (GrowRefP.of_core ?_)
      exact CoreSpec.of_call1W (s₀ := ⟨m, Locals.init []⟩)
        (peelLeaf_refines p hp hil j' (hk.mono (by omega)) F (by omega) (by omega) _ s dn vis fe M eb
          mode d a b k fo ⟨hS, hmode, heb⟩ ha hb fvs hx (by omega))
        (fun r r' h => by simp only [decBool, h]) h
    have hp0 : peel ≠ 0 := fun h0 => hl (.inl h0)
    have hga : a >>> 28 = 6 := Classical.byContradiction fun h' => hl (.inr (.inl h'))
    have hgb : b >>> 28 = 6 := Classical.byContradiction fun h' => hl (.inr (.inr h'))
    obtain ⟨q, hq⟩ : ∃ q, peel.toNat = q + 1 :=
      ⟨peel.toNat - 1, by have : peel.toNat ≠ 0 := fun h0' => hp0 ((word_toNat_zero_iff peel).mp h0'); omega⟩
    have hq1 : (peel - 1).toNat = q := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hk1 : (k + 1).toNat = k.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
    cases hc : callW p j "peel_step" [mode, vis, d, a, b, k, fo] m with
    | none => rw [peelW_n1 (h := he) (hl := hl) (hc := hc)] at h; cases h
    | some w =>
    obtain ⟨r₁, m₁⟩ := w
    obtain ⟨j', rfl⟩ := callW_succ hc
    have e₁ := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
      (peelStep_refines p hp hil j' (hk.mono (by omega)) F (by omega) (by omega) _ s dn vis fe M eb
        mode d a b k fo ⟨hS, hmode, heb⟩ ha hb hga hgb fvs hx (by omega)) hc
    have hr := defeqPeel_succ_eq (coreKnot (decMode mode) fe id F) d.toNat q (decE a) (decE b)
      k.toNat fvs
    have hl' : (decide (q + 1 = 0) || (decE a).tag != ETag.forallE ||
        (decE b).tag != ETag.forallE) = false := by rw [← hq, hlw]; simp [hl]
    rw [hq]
    refine growRef_congr ((congrArg (fun T => StateT.run T s) hr).trans
      (peelLvl_step_run _ _ _ _ _ _ _ _ _ hab' hl')) ?_
    refine growRef_bindK e₁ (fun M₁ hS₁ hst₁ => ?_)
    obtain ⟨hw0, hw1, hw2, hw3⟩ := e₁.2.2.2
    by_cases h0 : r₁.headD 0 = 0
    · rw [peelW_stop (h := he) (hl := hl) (hc := hc) (h0 := h0), Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [decPS, h0, bne_self_eq_false, Bool.not_false, ↓reduceIte]
      exact growRef_ret hS₁ rfl resH_zero
    have hnz : (r₁.headD 0 != 0) = true := by simpa using h0
    simp only [decPS, hnz, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hc2 : callW p (j' + 1) "peel_push" [d, k, fo, r₁.tail.headD 0] m₁ with
    | none => rw [peelW_n2 (h := he) (hl := hl) (hc := hc) (h0 := h0) (hc2 := hc2)] at h; cases h
    | some w =>
    obtain ⟨r₂, m₂⟩ := w
    rw [peelW_cont (h := he) (hl := hl) (hc := hc) (h0 := h0) (hc2 := hc2)] at h
    obtain ⟨e₂, hx₂⟩ := peelPush_run hp hS₁ d k fo _ hw1 fvs (hx.kept hst₁ hS.spn)
      (by omega) r₂ hc2
    refine growRef_bind e₂ (fun M₂ hS₂ _ => ?_)
    have := ih (by omega) (peel - 1) _ _ (k + 1) m₂ m' _ M₂ eb v _ hS₂ heb hw2 hw3 hx₂
      (by rw [hq1, hk1]; omega) h
    rw [hq1, hk1] at this
    exact this

end loopRef

/-- **`defeq_peel` refines `defeqPeel`** at the knot: the slice `fvs = (fo, k)` at the top of the
stack, the result's stack grown. -/
@[refines ConRon.Arena.defeqPeel]
theorem defeqPeel_refines (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs) (hdk : d.toNat + k.toNat + peel.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_peel" [mode, vis, d, peel, a, b, k, fo]
    ⦃fun r s' => LocEq s' s₀ ∧ GrowRefP (defeqPeel (coreKnot (decMode mode) fe id F) d.toNat
      peel.toNat (decE a) (decE b) k.toNat fvs) a₀ decBool dn s₀.mem vis fe M eb r s'.mem; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqPeel_spec p hp n s₀ mode vis d peel a b k fo)
  subst hs0
  refine ⟨hloc, ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := peelW_ok p hp hil n hk F hF hn dn vis fe mode d fo hs.mode4 (n + 1)
    (Nat.le_refl _) peel a b k s.mem s'.mem a₀ M eb (r.headD 0) fvs hs.rel hs.eb_mode ha hb hx hdk hW
  exact ⟨h1, h2, h3.trans (by simp [decBool]), h4⟩

/-! ## `defeq_binders` -/

/-- **A growing run whose caller puts the top back**: writing the old top to `CTL[136]` gives a
kept-stack refinement. -/
theorem GrowRefP.reset {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₁ m₃ : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop}
    (h : GrowRefP T a₀ dec dn m₁ vis fe M eb r m₃ ok) (h136 : 136 < (m₃.arr64 1).size) :
    CoreRef T a₀ dec dn m₁ vis fe M eb r (m₃.set64 1 136 (spTop m₁)) ok := by
  obtain ⟨hok, ⟨M', hS, hK, hg⟩, hres, hr⟩ := h
  have hfr : MemFrame [SPN] [136] m₃ (m₃.set64 1 136 (spTop m₁)) :=
    (MemFrame.setCtl _ 136 _).mono (by simp) (by simp)
  have hspn : (m₃.set64 1 136 (spTop m₁)).arr64 SPN = m₃.arr64 SPN :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  exact ⟨hok, ⟨M', hS.frame_stk hfr (by simp) (by simp), hK, StackKept.restoreG hg h136⟩, hres, hr⟩

section bK
variable (p : Prog) (n : Nat) (mode vis d body1 ty2 body2 : Word)

def bK3 (so : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => if 136 < (m.arr64 1).size then some (r.headD 0, m.set64 1 136 so) else none

def bK2 (so : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (_, m) => bK3 so (callW p n "defeq_peel" [mode, vis, d, 16777216, body1, body2, 1, so] m)

def bK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, m)
    else bK2 p n mode vis d body1 body2 (rdW (m.arr64 1) 136)
      (callW p n "peel_push" [d, 0, rdW (m.arr64 1) 136, ty2] m)

variable (r : List Word) (m : Mem) (so x : Word)
theorem bK3_ok (h : 136 < (m.arr64 1).size) : bK3 so (some (r, m)) = some (r.headD 0, m.set64 1 136 so) := by
  simp only [bK3, h, ↓reduceIte]
theorem bK2_s : bK2 p n mode vis d body1 body2 so (some (r, m)) =
    bK3 so (callW p n "defeq_peel" [mode, vis, d, 16777216, body1, body2, 1, so] m) := rfl
theorem bK1_z (h : r.headD 0 = 0) : bK1 p n mode vis d body1 ty2 body2 (some (r, m)) = some (0, m) := by
  simp only [bK1, h, ↓reduceIte]
theorem bK1_nz (h : r.headD 0 ≠ 0) :
    bK1 p n mode vis d body1 ty2 body2 (some (r, m)) =
      bK2 p n mode vis d body1 body2 (rdW (m.arr64 1) 136)
        (callW p n "peel_push" [d, 0, rdW (m.arr64 1) 136, ty2] m) := by
  simp only [bK1, h, ↓reduceIte]
end bK

theorem defeqBinders_spec (p : Prog) (hp : PeelProg p) (n : Nat) (s₀ : St)
    (mode vis d ty1 body1 ty2 body2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_binders" [mode, vis, d, ty1, body1, ty2, body2]
    ⦃fun r s' => LocEq s' s₀ ∧ bK1 p n mode vis d body1 ty2 body2
      (callW p n "defeq" [mode, vis, d, ty1, ty2] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.binders]
  simp only [callFn, defeqBindersL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, callW_spec p n "defeq",
      callW_spec p n "peel_push", callW_spec p n "defeq_peel"] <;>
    finish (gen := 50) (instances := 5000) [bK1_z, bK1_nz, bK2_s, bK3_ok, St.setLocs_mem', rdW_eq]

/-- A run of `peel_push` wrote inside the stack array. -/
theorem peelPush_bound {p : Prog} (hp : PeelProg p) {n : Nat} {m m' : Mem} (d k fo t2 : Word)
    {r : List Word} (hc : callW p (n + 1) "peel_push" [d, k, fo, t2] m = some (r, m')) :
    (fo + k).toNat < (m.arr64 SPN).size := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (peelPush_spec p hp n ⟨m, Locals.init []⟩ d k fo t2) hc
  cases hc1 : callW p n "intern_fvar" [d + k, t2] m with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  obtain ⟨s'', rfl, -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internFVar_spec p hp.fvf hp.fvp hp.fvi n ⟨m, Locals.init []⟩ (d + k) t2) hc1
  have hsz : (s''.mem.arr64 SPN).size = (m.arr64 SPN).size :=
    (fvinternW_frame _ _ _ _ _ hI).2.2.1 SPN
  simp only [peelPushK] at hW
  split at hW
  · rename_i hb; rw [← hsz]; exact hb.1
  · cases hW

theorem fvsR_empty {m : Mem} {so : Word} (htop : spTop m = so) (hb : so.toNat < (m.arr64 SPN).size)
    (hspn : (m.arr64 SPN).size < 2 ^ 63) : FvsR m so 0 #[] :=
  ⟨⟨rfl, by simp; omega, fun i hi => by simp at hi, fun i hi => by simp at hi⟩,
    by rw [htop]; simp, by simp; omega⟩

/-- **`defeq_binders` refines `defeqBinders`** at the knot (the depth leaves room for the peel's
budget). -/
@[refines ConRon.Arena.defeqBinders]
theorem defeqBinders_refines (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty1 body1 ty2 body2 : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (h1 : HW ty1) (hb1 : HW body1) (h2 : HW ty2) (hb2 : HW body2)
    (hd : d.toNat + 1 + peelFuel < 2 ^ 64) :
    CoreSpec p (n + 1) "defeq_binders" [mode, vis, d, ty1, body1, ty2, body2]
      (defeqBinders (coreKnot (decMode mode) fe id F) d.toNat (decE ty1) (decE body1) (decE ty2)
        (decE body2)) decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqBinders_spec p hp n s₀ mode vis d ty1 body1 ty2 body2)
  subst hs0
  refine ⟨hloc, ?_⟩
  unfold defeqBinders
  cases hc1 : callW p n "defeq" [mode, vis, d, ty1, ty2] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  have e₁ := CoreSpec.of_callW
    ((hk n (Nat.le_refl _)).defeq F s a₀ dn vis fe M eb mode d ty1 ty2 hF hn hs h1 h2) hc1
  refine coreRef_bindS e₁ (fun M₁ hS₁ hst₁ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [bK1_z (h := h0), Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [decBool_f h0, ← hm]
    exact coreRef_ret hS₁ (by rw [decBool, ← hr]; rfl) (by unfold ResH; rw [← hr]; exact hw0)
  rw [bK1_nz (h := h0)] at hW
  rw [decBool_t h0]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hso : rdW (m₁.arr64 1) 136 = spTop m₁ := rfl
  rw [hso] at hW
  cases hc2 : callW p n "peel_push" [d, 0, spTop m₁, ty2] m₁ with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2, bK2_s] at hW
  obtain ⟨n', rfl⟩ := callW_succ hc2
  have hbnd := peelPush_bound hp d 0 (spTop m₁) ty2 hc2
  rw [UInt64.add_zero] at hbnd
  obtain ⟨e₂, hx₂⟩ := peelPush_run hp hS₁ d 0 (spTop m₁) ty2 h2 #[]
    (fvsR_empty rfl hbnd hS₁.spn) (by rw [toNat_zero_w, Nat.add_zero]; omega) r₂ hc2
  cases hc3 : callW p (n' + 1) "defeq_peel"
      [mode, vis, d, 16777216, body1, body2, 1, spTop m₁] m₂ with
  | none => rw [hc3] at hW; cases hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [hc3] at hW
  simp only [bK3] at hW
  split at hW
  · rename_i h136
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have e0 : d.toNat + (0 : Word).toNat = d.toNat := rfl
    rw [e0] at e₂
    rw [UInt64.zero_add] at hx₂
    rw [← hm]
    refine GrowRefP.reset (growRef_bind e₂ (fun M₂ hS₂ _ => ?_)) h136
    have e1 : (16777216 : Word).toNat = peelFuel := by simp [peelFuel]
    generalize hw : (16777216 : Word) = w at hc3
    have hwf : w.toNat = peelFuel := by rw [← hw]; exact e1
    have hdk' : d.toNat + (1 : Word).toNat + w.toNat < 2 ^ 64 := by
      rw [hwf, show (1 : Word).toNat = 1 from rfl]; exact hd
    obtain ⟨t, ht, -, hP⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
      (defeqPeel_refines p hp hil n' (hk.mono (by omega)) F (by omega) (by omega) ⟨m₂, Locals.init []⟩
        _ dn vis fe M₂ eb mode d w body1 body2 1 (spTop m₁) ⟨hS₂, hs.mode4, hs.eb_mode⟩ hb1 hb2
        _ hx₂ hdk') hc3
    rw [ht, hwf] at hP
    have e2 : (1 : Word).toNat = 1 := rfl
    have e3 : (#[] : Array EIdx).push (decE (r₂.headD 0)) = #[decE (r₂.headD 0)] := rfl
    rw [e2, e3] at hP
    obtain ⟨g1, g2, g3, g4⟩ := hP
    exact ⟨g1, g2, g3.trans (by unfold decBool; rw [hr]), by unfold ResH; rw [← hr]; exact g4⟩
  · cases hW

end L.Arena
