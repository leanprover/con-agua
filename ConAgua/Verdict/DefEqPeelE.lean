import ConAgua.Verdict.DefEqQuickE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

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

/-- **`defeq_peel`'s error claim** (`defeqPeel_ref`'s error half). -/
theorem defeqPeel_refinesE (p : Prog) (hp : PeelProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n)
    (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs) (hdk : d.toNat + k.toNat + peel.toNat < 2 ^ 64) :
    CoreSpecE p (n + 1) "defeq_peel" [mode, vis, d, peel, a, b, k, fo]
      (defeqPeel (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE a) (decE b) k.toNat fvs)
      s₀ a₀ :=
  RefE.coreSpecE (defeqPeel_specE p hp.peel (n + 1) s₀ mode vis d peel a b k fo) trivial
    ⟨fun j hj F hF hn s₀ a₀ dn vis fe M eb mode d a b k fo hs ha hb fvs hx hdk =>
      peelLeaf_refinesE p hp hil hnv j (hkE.mono hj) F hF hn s₀ a₀ dn vis fe M eb mode d a b k fo hs ha
        hb fvs hx hdk,
     fun j hj F hF hn s₀ a₀ dn vis fe M eb mode d a b k fo hs ha hb hga hgb fvs hx hdk =>
      peelStep_refinesE p hp hil hnv j (hkE.mono hj) F hF hn s₀ a₀ dn vis fe M eb mode d a b k fo hs ha
        hb hga hgb fvs hx hdk,
     fun k args m _ h => callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) k args m h⟩
    (defeqPeel_ref p hp hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d peel a b k fo hs ha hb fvs hx hdk)

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
