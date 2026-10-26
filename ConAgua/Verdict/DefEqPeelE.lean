import ConAgua.Verdict.DefEqQuickE

/-!
# The batched ∀ descent's error claims: `peel_*`, `defeq_peel`, `defeq_binders` (lane `verdicts-b`,
helper `k3`)

The error halves of `DefEqMidPeel.lean`. A failure is a `defeq` slot call's (`peel_leaf`,
`peel_dom`, `defeq_binders`' domains) or a callee's of this file; `inst_list`, `e_view`,
`peel_push`, `intern_fvar` are outside the verdict closure. The descent grows the stack
(`GrowRefP`): its ok steps are threaded by `ErrClaim.bind_grow`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **The error claim past a growing ok run** (the error twin of `growRef_bind`). -/
theorem ErrClaim.bind_grow {α β : Type} [Inhabited α] {T₁ : AM α} {f : α → AM β} {a₀ : AState}
    {dec₁ : List Word → α} {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ : List Word} {ok₁ : List Word → Prop} {e : Err}
    (h₁ : GrowRefP T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb → StackGrew m₀ m₁ →
      ErrClaim (f (dec₁ r₁)) (AM.st T₁ a₀) e) :
    ErrClaim (T₁ >>= f) a₀ e := by
  obtain ⟨M', hS, -, hSt⟩ := h₁.2.1
  exact ErrClaim.bind_right (by rw [AM.run_of_ok _ _ h₁.1, h₁.2.2.1]) (h₂ M' hS hSt)

/-! ## `peel_leaf`, `peel_dom` -/

l_model peelLeaf_specE (p : Prog) (hf : p.lookup "peel_leaf" = some peelLeafL)
  fns [hf ↦ peelLeafE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`peel_leaf`'s error claim** (the error half of `peelLeaf_refines`). -/
theorem peelLeaf_refinesE (p : Prog) (hp : PeelProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs) (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpecE p (n + 1) "peel_leaf" [mode, vis, d, a, b, k, fo]
      (defeqPeelLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (peelLeaf_specE p hp.leaf (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b k fo) hc0 (Err.code_ne_of_cls hkc)
  simp only [peelLeafE] at hW
  unfold defeqPeelLeaf
  cases hc1 : callE p n "inst_list" [a, fo, k, 0] s₀.mem with
  | error e =>
    rw [hc1, peelLeafE.k_inst_list.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  simp only [peelLeafE.k_inst_list] at hW
  have e₁ := CoreSpec.of_callW (hil n s₀ a₀ dn vis fe M eb a fo k 0 fvs hs.rel ha hx.spine hx.le_top)
    (callW_of_callE hc1)
  rw [toNat_zero_w] at e₁
  refine ErrClaim.bind_coreS e₁ (fun M₁ hS₁ hst₁ => ?_)
  have hx₁ := hx.kept hst₁ hs.rel.spn
  cases hc2 : callE p n "inst_list" [b, fo, k, 0] m₁ with
  | error e =>
    rw [hc2, peelLeafE.k_inst_list_2.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW
  simp only [peelLeafE.k_inst_list_2] at hW
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (hil n _ _ dn vis fe M₁ eb b fo k 0 fvs hS₁ hb hx₁.spine hx₁.le_top) (callW_of_callE hc2)
  rw [toNat_zero_w] at e₂
  refine ErrClaim.bind_core e₂ (fun M₂ hS₂ => ?_)
  have h3 := tailE (peelLeafE.k_defeq.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  have := CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
    ((hkE n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode (d + k) _ _ hF hn
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₁.2.2.2 e₂.2.2.2) h3
  rw [peel_word_add_toNat d k hdk] at this
  exact this

l_model peelDom_specE (p : Prog) (hf : p.lookup "peel_dom" = some peelDomL)
  fns [hf ↦ peelDomE tuple] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`peel_dom`'s error claim** (the error half of `peelDom_refines`). -/
theorem peelDom_refinesE (p : Prog) (hp : PeelProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d da db k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW da) (hb : HW db)
    (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs) (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpecE p (n + 1) "peel_dom" [mode, vis, d, da, db, k, fo]
      (peelDomT (coreKnot (decMode mode) fe id F) d.toNat (decE da) (decE db) k.toNat fvs) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (peelDom_specE p hp.dom (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d da db k fo) hc0 (Err.code_ne_of_cls hkc)
  simp only [peelDomE] at hW
  unfold peelDomT
  cases hc1 : callE p n "inst_list" [da, fo, k, 0] s₀.mem with
  | error e =>
    rw [hc1, peelDomE.k_inst_list.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  simp only [peelDomE.k_inst_list] at hW
  have e₁ := CoreSpec.of_callW (hil n s₀ a₀ dn vis fe M eb da fo k 0 fvs hs.rel ha hx.spine hx.le_top)
    (callW_of_callE hc1)
  rw [toNat_zero_w] at e₁
  refine ErrClaim.bind_coreS e₁ (fun M₁ hS₁ hst₁ => ?_)
  by_cases he : da = db
  · rw [ite_eq_left he] at hW; cases hW
  rw [ite_eq_right he] at hW
  have hbq : (decE da == decE db) = false := by
    rw [decE_beq_eq _ _ ha hb]; simp [he]
  simp only [hbq, Bool.false_eq_true, ↓reduceIte]
  have hx₁ := hx.kept hst₁ hs.rel.spn
  cases hc2 : callE p n "inst_list" [db, fo, k, 0] m₁ with
  | error e =>
    rw [hc2, peelDomE.k_inst_list_2.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW
  simp only [peelDomE.k_inst_list_2] at hW
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (hil n _ _ dn vis fe M₁ eb db fo k 0 fvs hS₁ hb hx₁.spine hx₁.le_top) (callW_of_callE hc2)
  rw [toNat_zero_w] at e₂
  refine ErrClaim.bind_core e₂ (fun M₂ hS₂ => ?_)
  have h3 := tailE (peelDomE.k_defeq.none p _) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  have := CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
    ((hkE n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode (d + k) _ _ hF hn
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₁.2.2.2 e₂.2.2.2) h3
  rw [peel_word_add_toNat d k hdk] at this
  exact ErrClaim.bind_left this

/-! ## `peel_step2`, `peel_step` -/

l_model peelStep2_specE (p : Prog) (hf : p.lookup "peel_step2" = some peelStep2L)
  fns [hf ↦ peelStep2E tuple] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`peel_step2`'s error claim** (the error half of `peelStep2_refines`). -/
theorem peelStep2_refinesE (p : Prog) (hp : PeelProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d da b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hda : HW da) (hb : HW b)
    (hg : b >>> 28 = 6) (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs)
    (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpecE p (n + 1) "peel_step2" [mode, vis, d, da, b, k, fo]
      (peelStep2T (coreKnot (decMode mode) fe id F) d.toNat (decE da) (decE b) k.toNat fvs) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (peelStep2_specE p hp.step2 (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d da b k fo) hc0 (Err.code_ne_of_cls hkc)
  simp only [peelStep2E] at hW
  cases hc1 : callE p n "e_view" [b] s₀.mem with
  | error e =>
    rw [hc1, peelStep2E.k_e_view.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  simp only [peelStep2E.k_e_view] at hW
  obtain ⟨rfl, -, -, hw1, hw2, hvb⟩ := eView_forall_callW (a := a₀) hp.eview hs.rel.arena.1 hb hg
    (callW_of_callE hc1)
  have hT : (peelStep2T (coreKnot (decMode mode) fe id F) d.toNat (decE da) (decE b) k.toNat fvs).run a₀ =
      (peelDomT (coreKnot (decMode mode) fe id F) d.toNat (decE da) (decE (r₁.tail.headD 0)) k.toNat fvs
        >>= fun x => pure (x.1, x.2, decE (r₁.tail.tail.headD 0))).run a₀ := by
    simp only [peelStep2T, StateT.run_bind, viewBind_run', hvb, except_ok_bind]
  refine ErrClaim.congr_run hT (ErrClaim.bind_left ?_)
  have h2 := tailE (peelStep2E.k_peel_dom.none p _) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  refine ErrClaim.of_callE_succ h2 fun n' hn' h' => ?_
  subst hn'
  exact CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (peelDom_refinesE p hp hil hnv n' (hkE.mono (by omega)) F (by omega)
      (by omega) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb mode d da _ k fo
      ⟨hs.rel, hs.mode4, hs.eb_mode⟩ hda hw1 fvs hx hdk) h'

l_model peelStep_specE (p : Prog) (hf : p.lookup "peel_step" = some peelStepL)
  fns [hf ↦ peelStepE tuple] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`peel_step`'s error claim** (the error half of `peelStep_refines`). -/
theorem peelStep_refinesE (p : Prog) (hp : PeelProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (hga : a >>> 28 = 6) (hgb : b >>> 28 = 6) (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs)
    (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpecE p (n + 1) "peel_step" [mode, vis, d, a, b, k, fo]
      (peelStepT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (peelStep_specE p hp.step (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b k fo) hc0 (Err.code_ne_of_cls hkc)
  simp only [peelStepE] at hW
  cases hc1 : callE p n "e_view" [a] s₀.mem with
  | error e =>
    rw [hc1, peelStepE.k_e_view.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  simp only [peelStepE.k_e_view] at hW
  obtain ⟨rfl, -, -, hw1, hw2, hvb⟩ := eView_forall_callW (a := a₀) hp.eview hs.rel.arena.1 ha hga
    (callW_of_callE hc1)
  have hT : (peelStepT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs).run a₀ =
      (peelStep2T (coreKnot (decMode mode) fe id F) d.toNat (decE (r₁.tail.headD 0)) (decE b) k.toNat fvs
        >>= fun y => pure (y.1, y.2.1, decE (r₁.tail.tail.headD 0), y.2.2)).run a₀ := by
    simp only [peelStepT, StateT.run_bind, viewBind_run', hvb, except_ok_bind]
  refine ErrClaim.congr_run hT (ErrClaim.bind_left ?_)
  have h2 := tailE (peelStepE.k_peel_step2.none p _) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  refine ErrClaim.of_callE_succ h2 fun n' hn' h' => ?_
  subst hn'
  exact CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (peelStep2_refinesE p hp hil hnv n' (hkE.mono (by omega)) F (by omega)
      (by omega) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb mode d _ b k fo
      ⟨hs.rel, hs.mode4, hs.eb_mode⟩ hw1 hb hgb fvs hx hdk) h'

end L.Arena

/-! ## `defeq_peel`: the loop -/

namespace L.Arena

l_model defeqPeel_specE (p : Prog) (hf : p.lookup "defeq_peel" = some defeqPeelL)
  fns [hf ↦ peelE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

theorem peelE_loop1_zero (p : Prog) (m : Mem) (mode vis d peel a b k fo : Word) :
    peelE.loop1 p 0 m mode vis d peel a b k fo = .error .outOfFuel := by
  unfold peelE.loop1; rfl

/-- **The descent loop's error claim** (the error half of `peelW_ok`). -/
theorem peelE_ok (p : Prog) (hp : PeelProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n)
    (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (mode d fo : Word) (hmode : mode < 4) :
    ∀ j, j ≤ n + 1 → ∀ (peel a b k : Word) (m : Mem) (s : AState) (M : ModeMaps) (eb : Word)
      (er : Err) (fvs : Array EIdx), CoreS dn m s vis fe M eb → eb = (mode >>> 1) &&& 1 → HW a →
      HW b → FvsR m fo k fvs → d.toNat + k.toNat + peel.toNat < 2 ^ 64 →
      peelE.loop1 p j m mode vis d peel a b k fo = .error er →
      ErrClaim (defeqPeel (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE a) (decE b)
        k.toNat fvs) s er := by
  intro j
  induction j with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
    rw [peelE_loop1_zero] at h; cases h
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ j ih =>
    intro hjn peel a b k m s M eb er fvs hS heb ha hb hx hdk h
    have hab : (decE a == decE b) = decide (a = b) := decE_beq_eq _ _ ha hb
    by_cases he : a = b
    · rw [peelE.loop1.arm1 (hc1 := rfl) (hc2 := he)] at h; cases h
    have hab' : (decE a == decE b) = false := by rw [hab]; simp [he]
    have hlw : (decide (peel.toNat = 0) || (decE a).tag != ETag.forallE ||
        (decE b).tag != ETag.forallE) = decide (peel = 0 ∨ a >>> 28 ≠ 6 ∨ b >>> 28 ≠ 6) := by
      simp only [bne, tag_forall_beq a ha, tag_forall_beq b hb, word_toNat_zero_iff]
      by_cases h1 : peel = 0 <;> by_cases h2 : a >>> 28 = 6 <;> by_cases h3 : b >>> 28 = 6 <;>
        simp [h1, h2, h3]
    by_cases hl : peel = 0 ∨ a >>> 28 ≠ 6 ∨ b >>> 28 ≠ 6
    · rw [peelE.loop1.arm2 (hc1 := rfl) (hc2 := he) (hc3 := hl)] at h
      have h1 := tailE (peelE.k_peel_leaf.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) h
      have hr := defeqPeel_leaf_run (coreKnot (decMode mode) fe id F) d.toNat peel.toNat _ _ k.toNat
        fvs s hab' (by rw [hlw]; simp [hl])
      refine ErrClaim.congr_run hr (ErrClaim.of_callE_succ h1 fun j' hj h' => ?_)
      subst hj
      exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
        (peelLeaf_refinesE p hp hil hnv j' (hkE.mono (by omega)) F (by omega) (by omega) _ s dn
          vis fe M eb mode d a b k fo ⟨hS, hmode, heb⟩ ha hb fvs hx (by omega)) h'
    have hp0 : peel ≠ 0 := fun h0 => hl (.inl h0)
    have hga : a >>> 28 = 6 := Classical.byContradiction fun h' => hl (.inr (.inl h'))
    have hgb : b >>> 28 = 6 := Classical.byContradiction fun h' => hl (.inr (.inr h'))
    obtain ⟨q, hq⟩ : ∃ q, peel.toNat = q + 1 :=
      ⟨peel.toNat - 1, by have : peel.toNat ≠ 0 := fun h0' => hp0 ((word_toNat_zero_iff peel).mp h0'); omega⟩
    have hq1 : (peel - 1).toNat = q := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hk1 : (k + 1).toNat = k.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
    rw [peelE.loop1.arm3 (hc1 := rfl) (hc2 := he) (hc3 := hl)] at h
    have hr := defeqPeel_succ_eq (coreKnot (decMode mode) fe id F) d.toNat q (decE a) (decE b)
      k.toNat fvs
    have hl' : (decide (q + 1 = 0) || (decE a).tag != ETag.forallE ||
        (decE b).tag != ETag.forallE) = false := by rw [← hq, hlw]; simp [hl]
    rw [hq]
    refine ErrClaim.congr_run ((congrArg (fun T => StateT.run T s) hr).trans
      (peelLvl_step_run _ _ _ _ _ _ _ _ _ hab' hl')) ?_
    cases hc : callE p j "peel_step" [mode, vis, d, a, b, k, fo] m with
    | error e =>
      rw [hc, peelE.k_peel_step.none] at h; cases h
      refine ErrClaim.bind_left (ErrClaim.of_callE_succ hc fun j' hj h' => ?_)
      subst hj
      exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
        (peelStep_refinesE p hp hil hnv j' (hkE.mono (by omega)) F (by omega) (by omega) _ s dn vis
          fe M eb mode d a b k fo ⟨hS, hmode, heb⟩ ha hb hga hgb fvs hx (by omega)) h'
    | ok w =>
    obtain ⟨r₁, m₁⟩ := w
    rw [hc] at h
    obtain ⟨j', rfl⟩ := callE_succ hc
    have e₁ := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
      (peelStep_refines p hp hil j' (hk.mono (by omega)) F (by omega) (by omega) _ s dn vis fe M eb
        mode d a b k fo ⟨hS, hmode, heb⟩ ha hb hga hgb fvs hx (by omega)) (callW_of_callE hc)
    refine ErrClaim.bind_coreS e₁ (fun M₁ hS₁ hst₁ => ?_)
    obtain ⟨hw0, hw1, hw2, hw3⟩ := e₁.2.2.2
    by_cases h0 : r₁.headD 0 = 0
    · rw [peelE.k_peel_step.arm1 (hc1 := h0)] at h; cases h
    rw [peelE.k_peel_step.arm2 (hc1 := h0)] at h
    have hnz : (r₁.headD 0 != 0) = true := by simpa using h0
    simp only [decPS, hnz, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hc2 : callE p (j' + 1) "peel_push" [d, k, fo, r₁.tail.headD 0] m₁ with
    | error e =>
      rw [hc2, peelE.k_peel_push.none] at h; cases h
      exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc2
    | ok w =>
    obtain ⟨r₂, m₂⟩ := w
    rw [hc2, peelE.k_peel_push.arm1] at h
    obtain ⟨e₂, hx₂⟩ := peelPush_run hp hS₁ d k fo _ hw1 fvs (hx.kept hst₁ hS.spn)
      (by omega) r₂ (callW_of_callE hc2)
    refine ErrClaim.bind_grow e₂ (fun M₂ hS₂ _ => ?_)
    have := ih (by omega) (peel - 1) _ _ (k + 1) m₂ _ M₂ eb er _ hS₂ heb hw2 hw3 hx₂
      (by rw [hq1, hk1]; omega) h
    rw [hq1, hk1] at this
    exact this

/-- **`defeq_peel`'s error claim** (the error half of `defeqPeel_refines`). -/
theorem defeqPeel_refinesE (p : Prog) (hp : PeelProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n)
    (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs) (hdk : d.toNat + k.toNat + peel.toNat < 2 ^ 64) :
    CoreSpecE p (n + 1) "defeq_peel" [mode, vis, d, peel, a, b, k, fo]
      (defeqPeel (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE a) (decE b) k.toNat fvs)
      s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (defeqPeel_specE p hp.peel (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d peel a b k fo) hc0 (Err.code_ne_of_cls hkc)
  rw [peelE.arm1] at hW
  exact peelE_ok p hp hil hnv n hk hkE F hF hn dn vis fe mode d fo hs.mode4 (n + 1) (Nat.le_refl _)
    peel a b k _ a₀ M eb er fvs hs.rel hs.eb_mode ha hb hx hdk hW

/-! ## `defeq_binders` -/

l_model defeqBinders_specE (p : Prog) (hf : p.lookup "defeq_binders" = some defeqBindersL)
  fns [hf ↦ defeqBindersE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`defeq_binders`' error claim** (`DefeqBindersE`, the error half of `defeqBinders_refines`). -/
theorem defeqBinders_refinesE (p : Prog) (hp : PeelProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) : DefeqBindersE p := by
  intro n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d ty1 body1 ty2 body2 hs h1 hb1 h2 hb2 hd
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (defeqBinders_specE p hp.binders (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d ty1 body1 ty2 body2) hc0 (Err.code_ne_of_cls hkc)
  rw [defeqBindersE.arm1] at hW
  unfold defeqBinders
  cases hc1 : callE p n "defeq" [mode, vis, d, ty1, ty2] s₀.mem with
  | error e =>
    rw [hc1, defeqBindersE.k_defeq.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE
      ((hkE n (Nat.le_refl _)).defeq F s₀ a₀ dn vis fe M eb mode d ty1 ty2 hF hn hs h1 h2) hc1)
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  simp only [defeqBindersE.k_defeq] at hW
  have e₁ := CoreSpec.of_callW
    ((hk n (Nat.le_refl _)).defeq F s₀ a₀ dn vis fe M eb mode d ty1 ty2 hF hn hs h1 h2)
    (callW_of_callE hc1)
  refine ErrClaim.bind_coreS e₁ (fun M₁ hS₁ hst₁ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0] at hW; cases hW
  rw [ite_eq_right h0] at hW
  rw [decBool_t h0]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hso : rdW (m₁.arr64 CTL) 136 = spTop m₁ := rfl
  rw [hso] at hW
  cases hc2 : callE p n "peel_push" [d, 0, spTop m₁, ty2] m₁ with
  | error e =>
    rw [hc2, defeqBindersE.k_peel_push.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2, defeqBindersE.k_peel_push.arm1] at hW
  obtain ⟨n', rfl⟩ := callE_succ hc2
  have hbnd := peelPush_bound hp d 0 (spTop m₁) ty2 (callW_of_callE hc2)
  rw [UInt64.add_zero] at hbnd
  obtain ⟨e₂, hx₂⟩ := peelPush_run hp hS₁ d 0 (spTop m₁) ty2 h2 #[]
    (fvsR_empty rfl hbnd hS₁.spn) (by rw [toNat_zero_w, Nat.add_zero]; omega) r₂ (callW_of_callE hc2)
  have e0 : d.toNat + (0 : Word).toNat = d.toNat := rfl
  rw [e0] at e₂
  rw [UInt64.zero_add] at hx₂
  refine ErrClaim.bind_grow e₂ (fun M₂ hS₂ _ => ?_)
  have h3 := tailE (defeqBindersE.k_defeq_peel.none p _) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  have e1 : (16777216 : Word).toNat = peelFuel := by simp [peelFuel]
  generalize hw : (16777216 : Word) = w at h3
  have hwf : w.toNat = peelFuel := by rw [← hw]; exact e1
  have hdk' : d.toNat + (1 : Word).toNat + w.toNat < 2 ^ 64 := by
    rw [hwf, show (1 : Word).toNat = 1 from rfl]; exact hd
  have := CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
    (defeqPeel_refinesE p hp hil hnv n' (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega)
      (by omega) ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d w body1 body2 1 (spTop m₁)
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ hb1 hb2 _ hx₂ hdk') h3
  rw [hwf] at this
  have e2 : (1 : Word).toNat = 1 := rfl
  have e3 : (#[] : Array EIdx).push (decE (r₂.headD 0)) = #[decE (r₂.headD 0)] := rfl
  rw [e2, e3] at this
  exact this

end L.Arena
