import ConAgua.Arena.DefEqStuckIrrel

/-!
# `stuck_str` refines `defeqStuck`'s string-literal arms (lane `defeq`, helper `defeq-top`)

A string literal against an application headed by `String.ofList` at the empty levels:
`strLitToConstructor`, then the knot's `defeq`; every other case `stuckIrrel` (`stuckStrT`). The model `strE` is in
`DefEqModels.lean`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin's arms -/

/-- **`defeqStuck`'s string-literal arm**, `side` `false` for the literal on the left. -/
def stuckStrT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) (side : Bool)
    (l : ConLeche.Literal) (fo : EIdx) : AM Bool :=
  match l with
  | .strVal st =>
    if fo.tag == ETag.const then
      view fo >>= fun v => match v with
        | .const cO usO => do
          let el ← emptyLevels
          let sl ← pinStringOfList
          if cO = sl ∧ usO = el ∧ (← strLitSupported fe) then do
            let c ← strLitToConstructor st
            if side then r.defeq depth a c else r.defeq depth c b
          else stuckIrrel r fe depth a b
        | _ => stuckIrrel r fe depth a b
    else stuckIrrel r fe depth a b
  | _ => stuckIrrel r fe depth a b

/-- The arm past the head's view and the pins. -/
theorem stuckStrT_run (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) (side : Bool)
    (st : String) (fo : EIdx) (s : AState) (m : Mem) (hP : PinsFull m s.pins) (cO : NIdx) (usO : LsIdx)
    (ht : (fo.tag == ETag.const) = true) (hv : s.store.view fo = some (.const cO usO)) :
    (stuckStrT r fe depth a b side (.strVal st) fo).run s =
      (strLitSupported fe >>= fun x =>
        if cO = decI (pinW m (1 + 6)) ∧ usO = decI (pinW m 52) ∧ x = true then do
          let c ← strLitToConstructor st
          if side then r.defeq depth a c else r.defeq depth c b
        else stuckIrrel r fe depth a b).run s := by
  simp only [stuckStrT, ht, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind,
    emptyLevels, pinEmptyLevels_run hP, pinStringOfList, PIN_STRING_OF_LIST, pinAt_run hP 6 (by decide)]

/-- A `stuck_irrel` tail, both outcomes (`si_ref`, its answer re-listed). -/
theorem si_tail {p : Prog} (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    {K : Except Err (List Word × Mem) → Except Err (List Word × Mem)}
    (hK1 : ∀ e, K (.error e) = .error e)
    (hK2 : ∀ v : List Word × Mem, K (.ok v) = .ok ([v.1.headD 0], v.2))
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (m : Mem) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hS : CoreS dn m a₀ vis fe M eb) (hmode : mode < 4) (heb : eb = (mode >>> 1) &&& 1)
    (ha : HW a) (hb : HW b) :
    RefE (StuckG p n) (K (siE p n m mode vis d a b))
      (stuckIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn m vis fe M eb ResH) := by
  cases n with
  | zero => rw [show siE p 0 m mode vis d a b = .error .outOfFuel from rfl, hK1]; exact RefE.of_cls0 rfl
  | succ k =>
  exact RefE.tail_relist1 hK1 hK2 (fun hG => hG.mono (by omega))
    (si_ref p hq hi hc k (hk.mono (by omega)) F ⟨m, Locals.init []⟩ a₀ dn vis fe M eb mode d a b
      (by omega) (by omega) ⟨hS, hmode, heb⟩ ha hb)

/-- **`stuck_str` refines `stuckStrT`, both outcomes** (`lt` a literal handle, `side` the
literal's side): the errors are the `defeq` slot's and `stuck_irrel`'s. -/
theorem str_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b side lt fo : Word) (l : ConLeche.Literal) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hlt : HW lt) (hfo : HW fo)
    (hg : lt >>> 28 = 8) (hl : a₀.store.view (decE lt) = some (.lit l)) :
    RefE (StuckG p n) (strE p (n + 1) s₀.mem mode vis d a b side lt fo)
      (stuckStrT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (side != 0) l
        (decE fo)) a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hR := hS.arena.1
  have hirr : ∀ (st : AState) (m : Mem) (M' : ModeMaps), CoreS dn m st vis fe M' eb →
      RefE (StuckG p n) (strE.j1 p n mode vis d a b m)
        (stuckIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) st
        (CorePost decBool dn m vis fe M' eb ResH) := fun st m M' hS' =>
    si_tail hq hi hc (fun _ => rfl) (fun _ => rfl) n hk F hF hn m st dn vis fe M' eb mode d a b hS'
      hs.mode4 hs.eb_mode ha hb
  have hdef : ∀ (st : AState) (m : Mem) (M' : ModeMaps) (x y : Word), CoreS dn m st vis fe M' eb →
      HW x → HW y →
      RefE (StuckG p n) (strE.k_defeq p (callE p n "defeq" [mode, vis, d, x, y] m))
        ((coreKnot (decMode mode) fe id F).defeq d.toNat (decE x) (decE y)) st
        (CorePost decBool dn m vis fe M' eb ResH) := by
    intro st m M' x y hS' hx hy
    rcases c : callE p n "defeq" [mode, vis, d, x, y] m with e | ⟨r, m'⟩
    · exact fun hG => CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
        ((hG.knot n (Nat.le_refl _)).defeq F _ st dn vis fe M' eb mode d x y hF hn
          ⟨hS', hs.mode4, hs.eb_mode⟩ hx hy) c
    obtain ⟨hrun, hP⟩ := (CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
      ((hk n (Nat.le_refl _)).defeq F _ st dn vis fe M' eb mode d x y hF hn
        ⟨hS', hs.mode4, hs.eb_mode⟩ hx hy) (callW_of_callE c)).post
    exact RefE.ret hrun ⟨hP.after, hP.res.trans (by simp only [decBool, List.headD_cons]), hP.valid⟩
  simp only [strE]
  by_cases h1 : tierW lt ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left h1]; exact RefE.of_cls0 rfl
  rw [ite_eq_right h1]
  by_cases h2 : tcnt s₀.mem LIT (tierW lt) ≤ idxW lt
  · rw [ite_eq_left h2]; exact RefE.of_cls0 rfl
  rw [ite_eq_right h2]
  obtain ⟨kn, hkv, hrec⟩ := view_lit_f s₀.mem a₀ hR lt hlt ⟨h1, by simpa using h2⟩ hg
  rw [hl] at hkv
  have hkl : kn.l = l := by cases hkv; rfl
  obtain ⟨kl⟩ := kn
  simp only at hkl
  subst hkl
  cases kl with
  | natVal N =>
    have h0 : tfld s₀.mem LIT (tierW lt) (idxW lt) 0 = 0 := hrec.1
    rw [ite_eq_right (fun h => absurd (h0 ▸ h.1) (by decide))]
    exact hirr a₀ s₀.mem M hS
  | strVal st =>
    have h0 : tfld s₀.mem LIT (tierW lt) (idxW lt) 0 = 1 := hrec.1
    rcases (Classical.em (fo >>> 28 = 3)).symm with h3 | h3
    · rw [ite_eq_right (fun h => h3 h.2)]
      unfold stuckStrT
      rw [decE_tag_const_beq _ hfo]
      simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hirr a₀ s₀.mem M hS
    rw [ite_eq_left ⟨h0, h3⟩]
    by_cases h4 : tierW fo ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
    · rw [ite_eq_left h4]; exact RefE.of_cls0 rfl
    rw [ite_eq_right h4]
    by_cases h5 : tcnt s₀.mem CONST (tierW fo) ≤ idxW fo
    · rw [ite_eq_left h5]; exact RefE.of_cls0 rfl
    rw [ite_eq_right h5]
    obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s₀.mem a₀ hR fo hfo ⟨h4, by simpa using h5⟩ h3
    have hct : ((decE fo).tag == ETag.const) = true := by rw [decE_tag_const_beq _ hfo]; simp [h3]
    generalize tfld s₀.mem CONST (tierW fo) (idxW fo) 0 = co at hnw hv ⊢
    generalize tfld s₀.mem CONST (tierW fo) (idxW fo) 1 = uo at huw hv ⊢
    -- the pins
    rcases hp1 : callW p n "pin_word" [52] s₀.mem with _ | ⟨r₁, m₁⟩
    · rw [liftE_none, strE.k_pin_word.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]; simp only [strE.k_pin_word]
    obtain ⟨t₁, ht₁, hm₁, -, hr₁⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (pinWord_rd p hq.leaf.pinword n ⟨s₀.mem, Locals.init []⟩ 52) hp1
    have em₁ : m₁ = s₀.mem := by rw [← ht₁]; exact hm₁
    subst em₁
    rcases hp2 : callW p n "pin_at" [6] s₀.mem with _ | ⟨r₂, m₂⟩
    · rw [liftE_none, strE.k_pin_at.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]; simp only [strE.k_pin_at]
    obtain ⟨t₂, ht₂, hm₂, -, -, hr₂⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (pinAt_rd p hq.leaf.pinat n ⟨s₀.mem, Locals.init []⟩ 6) hp2
    have em₂ : m₂ = s₀.mem := by rw [← ht₂]; exact hm₂
    subst em₂
    -- `str_lit_supported`
    refine RefE.of_run_eq (stuckStrT_run _ fe _ _ _ _ st _ a₀ s₀.mem hS.pins _ _ hct hv) ?_
    rcases hp3 : callW p n "str_lit_supported" [vis] s₀.mem with _ | ⟨r₃, m₃⟩
    · rw [liftE_none, strE.k_str_lit_supported.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]; simp only [strE.k_str_lit_supported]
    have h₃ := CoreSpec.of_callW (hc.strLitSupported n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb hS) hp3
    refine RefE.bind_core (w := id) h₃ (fun M₃ hS₃ _ => ?_)
    have hsl : HW (rdW (s₀.mem.arr64 PINS) (1 + 6)) := by
      have := hS.pins.names_lt 6 (by decide); rwa [pinW_rdW s₀.mem (1 + 6) (1 + 6) rfl] at this
    have hel : HW (rdW (s₀.mem.arr64 PINS) 52) := by
      have := hS.pins.lv_lt.1; rwa [pinW_rdW s₀.mem 52 52 rfl] at this
    simp only [pinW_rdW s₀.mem (1 + 6) (1 + 6) rfl, pinW_rdW s₀.mem 52 52 rfl, decI_inj_iff hnw hsl,
      decI_inj_iff huw hel]
    rw [hr₁, hr₂]
    by_cases hcond : co = rdW (s₀.mem.arr64 PINS) (1 + 6) ∧ uo = rdW (s₀.mem.arr64 PINS) 52 ∧
        r₃.headD 0 ≠ 0
    · rw [ite_eq_left hcond]
      obtain ⟨hc₁, hc₂, hc₃⟩ := hcond
      rw [ite_eq_left ⟨hc₁, hc₂, decBool_true_of hc₃⟩]
      rcases hp4 : callW p n "str_lit_ctor" [lt] m₃ with _ | ⟨r₄, m₄⟩
      · rw [liftE_none, strE.k_str_lit_ctor.none]; exact RefE.of_cls0 (by simp)
      rw [liftE_some]; simp only [strE.k_str_lit_ctor]
      have hv₃ := hc.supKeep fe a₀ (decE lt) _ hl
      have h₄ := CoreSpec.of_callW (hc.strLitCtor n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb lt st hS₃
        hlt hv₃) hp4
      refine RefE.bind_core (w := id) h₄ (fun M₄ hS₄ _ => ?_)
      by_cases hsd : side = 0
      · rw [ite_eq_left hsd]
        simp only [hsd, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact hdef _ m₄ M₄ _ _ hS₄ h₄.2.2.2 hb
      · rw [ite_eq_right hsd]
        have : (side != 0) = true := by simpa using hsd
        simp only [this, ↓reduceIte]
        exact hdef _ m₄ M₄ _ _ hS₄ ha h₄.2.2.2
    · rw [ite_eq_right hcond]
      rw [ite_eq_right (fun h => hcond ⟨h.1, h.2.1, fun e => by
              have := h.2.2; rw [decBool_false_of e] at this; cases this⟩)]
      exact hirr _ m₃ M₃ hS₃

/-- **`stuck_str` refines `stuckStrT`** at the knot (`str_ref`'s ok half). -/
@[refines_part ConRon.Arena.defeqStuck "the string-literal arms (stuckStrT)"]
theorem stuckStr_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b side lt fo : Word) (l : ConLeche.Literal) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hlt : HW lt) (hfo : HW fo)
    (hg : lt >>> 28 = 8) (hl : a₀.store.view (decE lt) = some (.lit l)) :
    CoreSpec p (n + 1) "stuck_str" [mode, vis, d, a, b, side, lt, fo]
      (stuckStrT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (side != 0) l
        (decE fo)) decBool s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (strE_spec p hq.stuckStr hq.stuckIrrel hq.setCert hq.setWith hq.setWtb hq.setGo
    hq.setTail hq.sunit hq.suHead hq.suTail (n + 1) s₀ mode vis d a b side lt fo)
    (str_ref p hq hi hc n hk F s₀ a₀ dn vis fe M eb mode d a b side lt fo l hF hn hs ha hb hlt hfo hg hl)

end L.Arena
