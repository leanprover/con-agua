module

public import ConAgua.Arena.DefEqMid
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DerRel
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StripTeleSpec
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Checker.NoVerdictTree
import ConAgua.Front.Preserve
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndView
import all ConAgua.Arena.DefEq
import ConAgua.L.WordOff
import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.Inst1Refine

@[expose] public section

/-!
# The binder-telescope congruence: `defeq_binders` (lane `defeq`)

`defeq_binders` (`DefEq.lean`) is the twin's `defeqBinders`: per level `inst_list` of the right
domain over the variable slice, `defeq_domain`, the fresh variable pushed at the stack top, then
`binder_pair` and the next level, or `defeq_binders_inner` at the innermost one. `fvs` is the stack
slice `(fo, k)` with the top at `fo + k` (`FvsR`); a push grows it, so the post is `GrowPost`
(the stack below the old top kept, the top grown); `quick_binders` puts the top back.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- The lookups of this file. -/
structure PeelProg (p : Prog) : Prop where
  domain : p.lookup "defeq_domain" = some defeqDomainL
  inner : p.lookup "defeq_binders_inner" = some defeqBindersInnerL
  pair : p.lookup "binder_pair" = some binderPairL
  binders : p.lookup "defeq_binders" = some defeqBindersL
  eview : p.lookup "e_view" = some L.Ind.eView
  fvf : p.lookup "fvar_find" = some fvarFind
  fvp : p.lookup "fvar_push" = some fvarPush
  fvi : p.lookup "intern_fvar" = some internFVar

/-! ## `intern_fvar` under `CoreS` -/

theorem fvinternW_hw (m : Mem) (a : AState) (hR : FVarR m a) (u ty w : Word) (m' : Mem)
    (hI : fvinternW m u ty = some (w, m')) : HW w := by
  exact consInternM_lt fvarCS_wf hR hI

/-- **`intern_fvar` as a run under `CoreS`**: the twin's `internE (.fvar u ty)`, the relation at
the same maps, the stack and `CTL[136]` untouched, a handle word. -/
theorem peel_internFVar_core {p : Prog} (hp : PeelProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn m a vis fe M eb) (u ty : Word) (hty : HW ty) (r : List Word)
    (hc : callW p n "intern_fvar" [u, ty] m = some (r, m')) :
    CoreRef (internE (.fvar u.toNat (decE ty))) a decH dn m vis fe M eb r m' ∧
      MemFrame [FVREC, tier1 FVREC, FVSLOT, tier1 FVSLOT, FVLP, tier1 FVLP] [26, 27] m m' := by
  obtain ⟨s', rfl, -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internFVar_spec p hp.fvf hp.fvp hp.fvi n ⟨m, Locals.init []⟩ u ty) hc
  obtain ⟨hok, hD, hres⟩ := internFVar_D m a hS.arena u ty _ hty _ hI
  have hf := fvinternW_frame _ _ _ _ _ hI
  have hrun := AM.run_of_ok _ _ hok
  have hS' : CoreS dn s'.mem _ vis fe M eb :=
    hS.arena_frame hD (Keeps.run (L.Arena.keeps_cpl_internFVar _ _) hrun) hf
      (fun b hb => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by decide)
      (fun b hb => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (fun x hx => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl <;> decide)
      (fun x hx => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl <;> decide)
  have hspn : s'.mem.arr64 SPN = m.arr64 SPN := hf.arr SPN (by simp [tier1, FVREC, FVSLOT, FVLP, SPN]) (by decide)
  have h136 : rdW (s'.mem.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.ctl 136 (by simp)
  exact ⟨⟨hok, ⟨M, hS', KeptAll.refl _ _,
      StackKept.of_frame hf⟩,
    by rw [hres]; rfl, fvinternW_hw m a hS.arena.base.fvar u ty _ _ hI⟩, hf⟩

/-! ## Growing runs

`WhnfCoreProj.lean`'s `GrowRefP` with its lemmas, restated here (that file and `DefEqLeaves.lean`
both defined `lsNodeW_viewLen`, so they could not be imported together; DefEqLeaves' copy is now `defeq_lsNodeW_viewLen`). -/

/-- `CoreRef` with the stack grown (`StackGrew`) instead of kept. -/
def GrowRefP {α : Type} [Inhabited α] (T : AM α) (a₀ : AState) (dec : List Word → α)
    (dn : NIdx → Option ConLeche.Name) (m₀ : Mem) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb : Word) (r : List Word) (m : Mem) (ok : List Word → Prop := ResH) : Prop :=
  AM.ok T a₀ ∧ (∃ M', CoreS dn m (AM.st T a₀) vis fe M' eb ∧ KeptAll M M' eb ∧ StackGrew m₀ m) ∧
    AM.res T a₀ = dec r ∧ ok r

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
  exact ⟨hok, hst ▸ ⟨M'', hS'', hK.trans hK'', hSt.trans hSt''⟩, hres.trans hres2, hrw2⟩

/-! ## The variable slice -/

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

theorem toNat_zero_w : (0 : Word).toNat = 0 := rfl

/-! ## `e_view` runs -/

/-- **A run of `e_view` at a `∀`**: the memory kept, the binder's two words, the twin's
`viewBind`. -/
theorem eView_forall_callW {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : HW h) (hg : tagW h = 6)
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
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : HW h) (hg : tagW h = 5)
    {r : List Word} (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) ∧
      a.store.viewBind (decE h) = some (decE (r.tail.headD 0), decE (r.tail.tail.headD 0)) := by
  obtain ⟨s', hm, rfl, hne, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Ind.eView_spec p hp n ⟨m, Locals.init []⟩ h) hc
  obtain ⟨hv, hw⟩ := L.Ind.eViewW_lam m h hg (hr ▸ hne)
  rw [hw] at hr
  subst hr
  obtain ⟨-, h1, h2⟩ := view_lam m a hR h hh hv hg
  exact ⟨hm.symm, h1, h2, viewBind_lam m a hR h hh hv hg⟩

theorem viewBind_bind_run {β : Type} (h : EIdx) (f : Option (EIdx × EIdx) → AM β) (s : AState) :
    (viewBind h >>= f).run s = (f (s.store.viewBind h)).run s := by
  simp only [StateT.run_bind, L.Arena.viewBind_run, except_ok_bind]


/-- A twin run that keeps the state, as a `CoreRef` with any validity. -/
theorem coreRef_pure' {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {r : List Word} {v : α} {ok : List Word → Prop} (hS : CoreS dn m a₀ vis fe M eb)
    (hrun : T.run a₀ = .ok (v, a₀)) (hv : v = dec r) (hr : ok r) :
    CoreRef T a₀ dec dn m vis fe M eb r m ok := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok, ?_, by rw [hres, hv], hr⟩
  rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩

/-! ## `binder_pair` -/

/-- **`binder_pair` is its model `bpairW`** (generated). -/
l_model bpair_spec (p : Prog) (hp : PeelProg p)
  fns [hp.pair ↦ bpairW tuple]
  specs [callW_spec p n "e_view"]
  grind [arena_grind]

/-- `(f, ty1, body1, ty2, body2)`. -/
def decBP (r : List Word) : Option (EIdx × EIdx × EIdx × EIdx) :=
  if r.headD 0 = 0 then none
  else some (decE (r.tail.headD 0), decE (r.tail.tail.headD 0), decE (r.tail.tail.tail.headD 0),
    decE (r.tail.tail.tail.tail.headD 0))

/-- Five result words below `2^32`. -/
def Res5 (r : List Word) : Prop :=
  HW (r.headD 0) ∧ HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) ∧ HW (r.tail.tail.tail.headD 0) ∧
    HW (r.tail.tail.tail.tail.headD 0)

/-- A run of `e_view` at a binder of the pair's kind (`5`, a `λ`; `6`, a `∀`). -/
theorem eView_binder_callW {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h t : Word} (hh : HW h) (ht : t = 5 ∨ t = 6)
    (hg : tagW h = t) {r : List Word} (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) ∧
      a.store.viewBind (decE h) = some (decE (r.tail.headD 0), decE (r.tail.tail.headD 0)) := by
  rcases ht with rfl | rfl
  · exact eView_lam_callW hp hR hh hg hc
  · obtain ⟨e1, -, -, e2, e3, e4⟩ := eView_forall_callW hp hR hh hg hc
    exact ⟨e1, e2, e3, e4⟩

/-- **`binder_pair` refines `binderPair?`.** -/
@[refines ConRon.Arena.binderPair?]
theorem binderPair_refines (p : Prog) (hp : PeelProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb lam a b : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "binder_pair" [lam, a, b] (binderPair? (lam != 0) (decE a) (decE b)) decBP
      s₀ a₀ dn vis fe M eb Res5 := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (bpair_spec p hp (n + 1) s₀ lam a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have core : ∀ (t : Word) (tt : UInt32), (t = 5 ∨ t = 6) →
      (∀ e : Word, HW e → ((decE e).tag == tt) = decide (tagW e = t)) →
      bpairW.j1 p n a b t s.mem = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0,
        r.tail.tail.tail.headD 0, r.tail.tail.tail.tail.headD 0, s'.mem) →
      CoreRef (do
        if (decE a).tag == tt && (decE b).tag == tt then
          match ← viewBind (decE a) with
          | none => failDanglingE
          | some (ty₁, body₁) =>
            match ← viewBind (decE b) with
            | none => failDanglingE
            | some (ty₂, body₂) => pure (some (ty₁, body₁, ty₂, body₂))
        else pure none : AM (Option (EIdx × EIdx × EIdx × EIdx))) a₀ decBP dn s.mem vis fe M eb r s'.mem
        Res5 := by
    intro t tt ht htt hW
    simp only [bpairW.j1] at hW
    rw [htt a ha, htt b hb]
    by_cases hno : tagW a ≠ t ∨ tagW b ≠ t
    · rw [ite_eq_left hno, Option.some.injEq] at hW
      simp only [Prod.mk.injEq] at hW
      obtain ⟨g1, g2, g3, g4, g5, hm⟩ := hW
      have hc : ¬ (tagW a = t ∧ tagW b = t) := fun h => hno.elim (fun h' => h' h.1) (fun h' => h' h.2)
      rw [ite_eq_right (by simpa using hc), ← hm]
      exact coreRef_ret hS (by simp only [decBP, ← g1, ↓reduceIte])
        ⟨g1 ▸ hw0, g2 ▸ hw0, g3 ▸ hw0, g4 ▸ hw0, g5 ▸ hw0⟩
    rw [ite_eq_right hno] at hW
    have hta : tagW a = t := Classical.byContradiction fun h => hno (.inl h)
    have htb : tagW b = t := Classical.byContradiction fun h => hno (.inr h)
    rw [ite_eq_left (by simp [hta, htb])]
    cases hc1 : callW p n "e_view" [a] s.mem with
    | none => rw [hc1] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hc1] at hW
    simp only [bpairW.k_e_view] at hW
    obtain ⟨rfl, ha1, ha2, hva⟩ := eView_binder_callW hp.eview hS.arena.base ha ht hta hc1
    cases hc2 : callW p n "e_view" [b] s.mem with
    | none => rw [hc2] at hW; cases hW
    | some q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [hc2] at hW
    simp only [bpairW.k_e_view_2, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨g1, g2, g3, g4, g5, hm⟩ := hW
    obtain ⟨rfl, hb1, hb2, hvb⟩ := eView_binder_callW hp.eview hS.arena.base hb ht htb hc2
    have hrun : (do
        match ← viewBind (decE a) with
        | none => failDanglingE
        | some (ty₁, body₁) =>
          match ← viewBind (decE b) with
          | none => failDanglingE
          | some (ty₂, body₂) => pure (some (ty₁, body₁, ty₂, body₂)) :
          AM (Option (EIdx × EIdx × EIdx × EIdx))).run a₀ =
        .ok (some (decE (r₁.tail.headD 0), decE (r₁.tail.tail.headD 0), decE (r₂.tail.headD 0),
          decE (r₂.tail.tail.headD 0)), a₀) := by
      rw [viewBind_bind_run, hva]
      simp only [viewBind_bind_run, hvb]
      rfl
    rw [← hm]
    refine coreRef_pure' hS hrun ?_ ⟨g1 ▸ hw1, g2 ▸ ha1, g3 ▸ ha2, g4 ▸ hb1, g5 ▸ hb2⟩
    simp only [decBP, ← g1, ← g2, ← g3, ← g4, ← g5]; rfl
  simp only [bpairW] at hW
  unfold binderPair?
  by_cases hl : lam = 0
  · rw [ite_eq_right (by simpa using hl)] at hW
    simp only [hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact core 6 ETag.forallE (.inr rfl) (fun e he => decE_tag_beq e he 6 (by decide)) hW
  · rw [ite_eq_left hl] at hW
    simp only [bne_iff_ne, ne_eq, hl, not_false_eq_true, ↓reduceIte]
    exact core 5 ETag.lam (.inl rfl) (fun e he => decE_tag_beq e he 5 (by decide)) hW

/-! ## `defeq_domain`, `binder_pair`, `defeq_binders` -/

/-- **`defeq_domain`'s model, both outcomes** (generated; `inst_list` lifted, the `defeq` slot
through its run). -/
l_model ddE_spec (p : Prog) (hf : p.lookup "defeq_domain" = some defeqDomainL)
  fns [hf ↦ ddE list]
  specs [callW_spec p n "inst_list"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`defeq_domain` refines `defeqDomain`, both outcomes** (the variable slice `fvs` below the
stack top): the errors are `inst_list`'s and the `defeq` slot's. -/
theorem dd_ref (p : Prog) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d fo k ty1 ty2 dom2 : Word) (fvs : Array EIdx)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hx : FvsR s₀.mem fo k fvs)
    (h1 : HW ty1) (h2 : HW ty2) (hd2 : HW dom2) :
    RefE (KnotNvG p n) (ddE p (n + 1) s₀.mem mode vis d fo k ty1 ty2 dom2)
      (defeqDomain (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat fvs (decE ty1) (decE ty2)
        (decE dom2)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have K := hk n (Nat.le_refl _)
  have hS := hs.rel
  unfold defeqDomain
  simp only [ddE]
  rw [decE_beq_eq _ _ h1 h2]
  by_cases he : ty1 = ty2
  · rw [ite_eq_left he, ite_eq_left (by simp [he])]
    exact RefE.ret rfl (CorePost.ret hS rfl resH_one)
  rw [ite_eq_right he, ite_eq_right (by simp [he])]
  have hil' := hil n s₀ a₀ dn vis fe M eb ty1 fo k 0 fvs hS h1 hx.spine hx.le_top
  rw [toNat_zero_w] at hil'
  refine RefE.bind_callW (fun _ => rfl) hil' fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [ddE.k_inst_list]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  rw [← bind_pure (CoreFnsA.defeq _ _ _ _)]
  refine RefE.bind_callE (fun _ => rfl) (K.defeq F _ _ dn vis fe M₁ eb mode d _ dom2 hF hn hs₁ h₁.resOk hd2)
    (fun (hG : KnotNvG p n) => (hG.knot n (Nat.le_refl _)).defeq F _ _ dn vis fe M₁ eb mode d _ dom2 hF hn
      hs₁ h₁.resOk hd2) fun _ _ _ e => ?_
  exact RefE.ret rfl ⟨e.after, rfl, e.resOk⟩

/-- **`defeq_domain` refines `defeqDomain`** at the knot (`dd_ref`'s ok half). -/
@[refines ConRon.Arena.defeqDomain]
theorem defeqDomain_refines (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d fo k ty1 ty2 dom2 : Word) (fvs : Array EIdx)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hx : FvsR s₀.mem fo k fvs)
    (h1 : HW ty1) (h2 : HW ty2) (hd2 : HW dom2) :
    CoreSpec p (n + 1) "defeq_domain" [mode, vis, d, fo, k, ty1, ty2, dom2]
      (defeqDomain (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat fvs (decE ty1) (decE ty2)
        (decE dom2)) decBool s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (ddE_spec p hp.domain (n + 1) s₀ mode vis d fo k ty1 ty2 dom2)
    (dd_ref p hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d fo k ty1 ty2 dom2 fvs hs hx h1 h2 hd2)

/-- **`defeq_binders`' model, both outcomes** (generated; recursive; `inst_list`, `intern_fvar`,
`binder_pair` lifted, `defeq_domain` and `defeq_binders_inner` by their models). -/
l_model dbE_spec (p : Prog) (hp : PeelProg p)
  fns [hp.binders ↦ dbE list]
  specs [callW_spec p n "inst_list", ddE_spec p hp.domain n, callW_spec p n "intern_fvar",
    callW_spec p n "binder_pair", liE_spec p hp.inner n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The variable pushed at the stack top** (`defeq_binders`' write): the relation kept, the
stack grown, the slice one longer. -/
theorem fvPush_ok {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {fo k fv : Word}
    {fvs : Array EIdx} (hx : FvsR m fo k fvs) (hfv : HW fv) (hb : ¬ m.len64 SPN ≤ fo + k) :
    CoreS dn ((m.set64 SPN (fo + k) fv).set64 CTL 136 (fo + k + 1)) a vis fe M eb ∧
      StackGrew m ((m.set64 SPN (fo + k) fv).set64 CTL 136 (fo + k + 1)) ∧
      FvsR ((m.set64 SPN (fo + k) fv).set64 CTL 136 (fo + k + 1)) fo (k + 1) (fvs.push (decE fv)) := by
  have hspn := hS.spn
  have hc := hS.ctl136
  have hfit := hx.fit
  simp only [Mem.len64, UInt64.not_le] at hb
  have e1 : (UInt64.ofNat (m.arr64 SPN).size).toNat = (m.arr64 SPN).size :=
    UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
  have hb' := UInt64.lt_iff_toNat_lt.mp hb
  rw [e1] at hb'
  have ht : (fo + k).toNat = fo.toNat + k.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  rw [ht] at hb'
  have h1 : (k + 1).toNat = k.toNat + 1 := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]; rfl
  have h3 : (fo + k + 1).toNat = fo.toNat + k.toNat + 1 := by
    rw [UInt64.toNat_add, ht, Nat.mod_eq_of_lt (by simp; omega)]; rfl
  have sp1 := hx.spine.push hspn hb' fv hfv
  have sp2 := sp1.setCtl 136 (fo + k + 1)
  have hf : MemFrame [SPN] [136] m ((m.set64 SPN (fo + k) fv).set64 CTL 136 (fo + k + 1)) :=
    ((MemFrame.set64 m SPN (by decide) _ _).mono (by simp) (by simp)).trans
      ((MemFrame.setCtl _ 136 _).mono (by simp) (by simp))
  have e : spTop ((m.set64 SPN (fo + k) fv).set64 CTL 136 (fo + k + 1)) = fo + k + 1 := by
    unfold spTop; rw [rdW_set64, ite_eq_left ⟨rfl, rfl, by simpa [L.Mem.size64_set64] using hc⟩]
  refine ⟨hS.frame_stk hf (by simp) (by simp), ⟨?_, ?_, fun i hi => ?_,
    BKept.of_frame hf (by decide) (by decide), PoolGrew.of_frame hf (by decide) (by decide)⟩,
    ⟨sp2, by rw [e, UInt64.add_assoc], by rw [h1]; omega⟩⟩
  · rw [e, hx.top, UInt64.le_iff_toNat_le, h3, ht]; omega
  · rw [L.Mem.size64_set64, L.Mem.size64_set64]
  · rw [hx.top, UInt64.lt_iff_toNat_lt, ht] at hi
    rw [spW_setCtl, spW_set64_ne _ _ _ _ (fun e => by rw [← e, ht] at hi; omega)]

/-- A kept-stack callee's ok run (`callW`), then a growing rest, both outcomes. -/
theorem RefE.bind_callWG {α β γ : Type} [Inhabited γ] {G : Prop} {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {s₀ : St} {x : Except Err (List Word × Mem) → Except Err α}
    (hx : ∀ e, x (.error e) = .error e) {T : AM γ} {k : γ → AM β} {a : AState}
    {dec : List Word → γ} {dec' : List Word → β} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {ok ok' : List Word → Prop} {w : α → List Word × Mem}
    (hok : CoreSpec p n f args T dec s₀ a dn vis fe M eb ok)
    (h : ∀ r m', callW p n f args s₀.mem = some (r, m') → CoreRef T a dec dn s₀.mem vis fe M eb r m' ok →
      ∀ M', CoreS dn m' (AM.st T a) vis fe M' eb → StackKept s₀.mem m' →
      RefE G (x (.ok (r, m'))) (k (dec r)) (AM.st T a)
        (fun v y a' => GrowPost dec' dn m' vis fe M' eb ok' (w v) y a')) :
    RefE G (x (liftE (callW p n f args s₀.mem))) (T >>= k) a
      (fun v y a' => GrowPost dec' dn s₀.mem vis fe M eb ok' (w v) y a') := by
  rcases c : callW p n f args s₀.mem with _ | ⟨r, m'⟩
  · rw [liftE_none, hx]; exact RefE.of_cls0 (by simp)
  have h1 := CoreSpec.of_callW hok c
  rw [liftE_some]
  exact RefE.bind_growK h1 (fun M' hS hSt => h r m' c h1 M' hS hSt)

/-- A unified callee with `CorePost` (the stack kept), then a growing rest, both outcomes. -/
theorem RefE.bind_coreEG {α β γ : Type} [Inhabited γ] {G G' : Prop}
    {x : Except Err (List Word × Mem)} {K : Except Err (List Word × Mem) → Except Err α}
    (hK : ∀ e, K (.error e) = .error e) {T₁ : AM γ} {f : γ → AM β} {a₀ : AState}
    {dec₁ : List Word → γ} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name} {m₀ : Mem}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {ok₁ ok : List Word → Prop}
    {w : α → List Word × Mem} (hG : G → G')
    (h₁ : RefE G' x T₁ a₀ (CorePost dec₁ dn m₀ vis fe M eb ok₁))
    (h₂ : ∀ r₁ m₁, x = .ok (r₁, m₁) → CoreRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁ →
      ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb → StackKept m₀ m₁ →
      RefE G (K (.ok (r₁, m₁))) (f (dec₁ r₁)) (AM.st T₁ a₀)
        (fun v y a' => GrowPost dec dn m₁ vis fe M' eb ok (w v) y a')) :
    RefE G (K x) (T₁ >>= f) a₀ (fun v y a' => GrowPost dec dn m₀ vis fe M eb ok (w v) y a') := by
  rcases hx : x with e | ⟨r₁, m₁⟩
  · rw [hK]; rw [hx] at h₁; exact RefE.bind_left fun hg => h₁ (hG hg)
  rw [hx] at h₁
  obtain ⟨y, a', hrun, hP⟩ := h₁
  have hc := hP.coreRef hrun
  exact RefE.bind_growK hc (fun M' hS hSt => h₂ r₁ m₁ hx hc M' hS hSt)

/-- A stronger context (`G → G'`) for an error claim under `G'`. -/
theorem RefE.weakG {α β : Type} {G G' : Prop} {x : Except Err α} {T : AM β} {a : AState}
    {R : α → β → AState → Prop} (hG : G → G') (h : RefE G' x T a R) : RefE G x T a R := by
  cases x with
  | ok v => exact h
  | error e => exact fun g => h (hG g)

/-- An L-only step that grew the stack (`m₀` to `m₁`): the post moves back to `m₀`. -/
theorem RefE.after_grow {α β : Type} {G : Prop} {x : Except Err α} {T : AM β} {a : AState}
    {dec : List Word → β} {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} {ok : List Word → Prop} {w : α → List Word × Mem}
    (hg : StackGrew m₀ m₁)
    (h : RefE G x T a (fun v y a' => GrowPost dec dn m₁ vis fe M eb ok (w v) y a')) :
    RefE G x T a (fun v y a' => GrowPost dec dn m₀ vis fe M eb ok (w v) y a') :=
  h.mono fun _ _ _ h => ⟨CoreAfterG.compK (KeptAll.refl _ _) hg h.after, h.res, h.valid⟩

/-- **`defeq_binders`' innermost level** (its join point `j1`): both bodies opened over the slice
`(fo, k + 1)`, then `defeq_binders_inner`; the errors are `inst_list`'s and the slots'. -/
theorem dbJ1_ref (p : Prog) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode lam d fo k body1 body2 : Word) (fvs : Array EIdx)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hx : FvsR s₀.mem fo (k + 1) fvs)
    (hb1 : HW body1) (hb2 : HW body2) (hd : d.toNat + 1 < 2 ^ 64) :
    RefE (KnotNvG p n) (dbE.j1 p (n + 1) mode vis lam d fo k body1 body2 s₀.mem)
      (do
        let b₁ ← instantiateListFast coreWalkFuel (decE body1) fvs
        let b₂ ← instantiateListFast coreWalkFuel (decE body2) fvs
        defeqBindersInner (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) (lam != 0)
          d.toNat b₁ b₂) a₀
      (GrowPost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hspn := hS.spn
  simp only [dbE.j1]
  have hil1 := hil (n + 1) s₀ a₀ dn vis fe M eb body1 fo (k + 1) 0 fvs hS hb1 hx.spine hx.le_top
  rw [toNat_zero_w] at hil1
  refine RefE.bind_callWG (w := id) (fun _ => rfl) hil1 fun r₁ m₁ _ h₁ M₁ hS₁ hK₁ => ?_
  simp only [dbE.k_inst_list_2]
  have hx₁ := hx.kept hK₁ hspn
  have hil2 := hil (n + 1) ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb body2 fo (k + 1) 0 fvs hS₁ hb2 hx₁.spine
    hx₁.le_top
  rw [toNat_zero_w] at hil2
  refine RefE.bind_callWG (w := id) (fun _ => rfl) hil2 fun r₂ m₂ _ h₂ M₂ hS₂ hK₂ => ?_
  simp only [dbE.k_inst_list_3]
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  exact RefE.lastE (K := dbE.k_defeq_binders_inner p) (f := fun v => ([v.1.headD 0], v.2))
    (fun _ => rfl) (fun _ => rfl) (fun hG => KnotNvG.knot hG)
    (li_ref p n hk F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode lam d _ _ hF hn hs₂ hd h₁.resOk h₂.resOk)
    fun v y a₁ _ hQ => ⟨CoreAfterG.compK (KeptAll.refl _ _) (StackGrew.refl _) hQ.after.toG, hQ.res, hQ.valid⟩

/-- **`defeq_binders` refines `defeqBinders`, both outcomes** (the variable slice `fvs` at the stack
top; the depth leaves room for the budget): the errors are the slots' and `inst_list`'s. -/
@[refines ConRon.Arena.defeqBinders]
theorem db_ref (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode lam fuel d fo k ty1 body1 ty2 body2 : Word) (fvs : Array EIdx)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hx : FvsR s₀.mem fo k fvs)
    (h1 : HW ty1) (hb1 : HW body1) (h2 : HW ty2) (hb2 : HW body2)
    (hd : d.toNat + fuel.toNat + 1 < 2 ^ 64) :
    RefE (KnotNvG p n) (dbE p (n + 1) s₀.mem mode vis lam fuel d fo k ty1 body1 ty2 body2)
      (defeqBinders (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) (lam != 0)
        fuel.toNat d.toNat fvs (decE ty1) (decE body1) (decE ty2) (decE body2)) a₀
      (GrowPost decBool dn s₀.mem vis fe M eb ResH) := by
  induction n generalizing s₀ a₀ M fuel d k ty1 body1 ty2 body2 fvs with
  | zero => rw [dbE.arm1, callW_zero, liftE_none, dbE.k_inst_list.none]; exact RefE.of_cls0 (by simp)
  | succ n ih =>
  have hS := hs.rel
  have hspn := hS.spn
  rw [dbE.arm1]
  unfold defeqBinders
  have hil0 := hil (n + 1) s₀ a₀ dn vis fe M eb ty2 fo k 0 fvs hS h2 hx.spine hx.le_top
  rw [toNat_zero_w] at hil0
  refine RefE.bind_callWG (w := id) (fun _ => dbE.k_inst_list.none ..) hil0 fun r₁ m₁ _ h₁ M₁ hS₁ hK₁ => ?_
  rw [dbE.k_inst_list.arm1]
  have hx₁ := hx.kept hK₁ hspn
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_coreEG (w := id) (fun _ => dbE.k_defeq_domain.none ..) (fun hG => hG.mono (by omega))
    (dd_ref p hil n (hk.mono (by omega)) F (by omega) (by omega) ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d
      fo k ty1 ty2 (r₁.headD 0) fvs hs₁ hx₁ h1 h2 h₁.resOk) fun r₂ m₂ _ h₂ M₂ hS₂ hK₂ => ?_
  by_cases h0 : r₂.headD 0 = 0
  · rw [dbE.k_defeq_domain.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0, L.Arena.decBool_false_of h0]
    simp only [Bool.not_false, ↓reduceIte]
    exact RefE.ret rfl ⟨⟨M₂, hS₂, KeptAll.refl _ _, StackGrew.refl _⟩, rfl, resH_zero⟩
  rw [dbE.k_defeq_domain.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0, L.Arena.decBool_true_of h0]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine RefE.onlySim (fun _ => dbE.k_intern_fvar.none ..) (fun _ _ h => h) fun r₃ m₃ c₃ => ?_
  obtain ⟨h₃, -⟩ := peel_internFVar_core hp hS₂ d (r₁.headD 0) h₁.resOk r₃ c₃
  refine RefE.bind_growK (w := id) h₃ fun M₃ hS₃ hK₃ => ?_
  by_cases hb : m₃.len64 SPN ≤ fo + k
  · rw [dbE.k_intern_fvar.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ hb]; exact RefE.of_cls0 (by simp)
  have hx₃ := (hx₁.kept hK₂ hS₁.spn).kept hK₃ hS₂.spn
  obtain ⟨hSp, hgp, hxp⟩ := fvPush_ok hS₃ hx₃ h₃.resOk hb
  refine RefE.after_grow hgp ?_
  by_cases hf0 : fuel = 0
  · rw [dbE.k_intern_fvar.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ hb hf0]
    rw [show fuel.toNat = 0 by rw [hf0]; rfl]
    have hsp : SlotPre ⟨_, Locals.init []⟩ _ dn vis fe M₃ eb mode := ⟨hSp, hs.mode4, hs.eb_mode⟩
    exact (dbJ1_ref p hil n (hk.mono (by omega)) F (by omega) (by omega) ⟨_, Locals.init []⟩ _ dn vis fe M₃
      eb mode lam d fo k body1 body2 _ hsp hxp hb1 hb2 (by omega)).weakG (fun hG => hG.mono (by omega))
  rw [dbE.k_intern_fvar.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ hb hf0]
  have hfn : fuel.toNat = (fuel - 1).toNat + 1 := by
    have : fuel.toNat ≠ 0 := fun e => hf0 (UInt64.toNat_inj.mp (by simpa using e))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_one]; omega)),
      UInt64.toNat_one]; omega
  rw [hfn]
  dsimp only
  refine RefE.bind_callWG (w := id) (fun _ => dbE.k_binder_pair.none ..)
    (binderPair_refines p hp n ⟨_, Locals.init []⟩ _ dn vis fe M₃ eb lam body1 body2 hSp hb1 hb2)
    fun r₄ m₄ _ h₄ M₄ hS₄ hK₄ => ?_
  have hx₄ := hxp.kept hK₄ hSp.spn
  have hs₄ : SlotPre ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode := ⟨hS₄, hs.mode4, hs.eb_mode⟩
  by_cases hbp : r₄.headD 0 = 0
  · rw [dbE.k_binder_pair.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ hbp,
      show decBP r₄ = none by simp only [decBP, hbp, ↓reduceIte]]
    dsimp only
    exact (dbJ1_ref p hil n (hk.mono (by omega)) F (by omega) (by omega) ⟨m₄, Locals.init []⟩ _ dn vis fe M₄
      eb mode lam d fo k body1 body2 _ hs₄ hx₄ hb1 hb2 (by omega)).weakG (fun hG => hG.mono (by omega))
  have hd1 : d + 1 ≠ 0 := by
    intro e; have := congrArg UInt64.toNat e; rw [UInt64.toNat_add] at this; simp at this; omega
  rw [dbE.k_binder_pair.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ hbp hd1,
    show decBP r₄ = some (decE (r₄.tail.headD 0), decE (r₄.tail.tail.headD 0),
      decE (r₄.tail.tail.tail.headD 0), decE (r₄.tail.tail.tail.tail.headD 0)) by
      simp only [decBP, hbp, ↓reduceIte]]
  dsimp only
  have hdd : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
  rw [← hdd]
  obtain ⟨-, q1, q2, q3, q4⟩ := h₄.resOk
  exact RefE.lastE (K := dbE.k_defeq_binders_inner p) (f := fun v => ([v.1.headD 0], v.2))
    (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (by omega))
    (ih (hk.mono (by omega)) (by omega) (by omega) ⟨m₄, Locals.init []⟩ _ M₄ (fuel - 1) (d + 1) (k + 1)
      _ _ _ _ _ hs₄ hx₄ q1 q2 q3 q4 (by rw [hdd]; omega))
    fun v y a₁ _ hQ => ⟨hQ.after, hQ.res, hQ.valid⟩

