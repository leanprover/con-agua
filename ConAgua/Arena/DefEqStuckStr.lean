import ConAgua.Arena.DefEqStuckIrrel

/-!
# `stuck_str` refines `defeqStuck`'s string-literal arms (lane `defeq`, helper `defeq-top`)

A string literal against an application headed by `String.ofList` at the empty levels:
`strLitToConstructor`, then the knot's `defeq`; every other case `stuckIrrel` (`stuckStrT`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

theorem stuckIrrel_at (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d a b : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      HW a → HW b →
      CoreSpec p n "stuck_irrel" [mode, vis, d, a, b]
        (stuckIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
        s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, b, hF, hn, hs, h1, h2 =>
      stuckIrrel_refines p hq hi hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b
        (by omega) (by omega) hs h1 h2

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

/-! ## The model of `stuck_str` -/

section strK
variable (p : Prog) (n : Nat) (mode vis d a b side lt : Word)

def strK4 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if side = 0 then call1W p n "defeq" [mode, vis, d, r.headD 0, b] m
    else call1W p n "defeq" [mode, vis, d, a, r.headD 0] m

def strK3 (co uo el sl : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if co ≠ sl then call1W p n "stuck_irrel" [mode, vis, d, a, b] m
    else if uo ≠ el then call1W p n "stuck_irrel" [mode, vis, d, a, b] m
    else if r.headD 0 = 0 then call1W p n "stuck_irrel" [mode, vis, d, a, b] m
    else strK4 p n mode vis d a b side (callW p n "str_lit_ctor" [lt] m)

def strK2 (co uo el : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => strK3 p n mode vis d a b side lt co uo el (r.headD 0)
      (callW p n "str_lit_supported" [vis] m)

def strK1 (co uo : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => strK2 p n mode vis d a b side lt co uo (r.headD 0) (callW p n "pin_at" [6] m)

/-- **The model of `stuck_str`.** -/
def strK (fo : Word) (m : Mem) : Option (Word × Mem) :=
  if tierW lt ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m LIT (tierW lt) ≤ idxW lt then none
  else if tfld m LIT (tierW lt) (idxW lt) 0 ≠ 1 then
    call1W p n "stuck_irrel" [mode, vis, d, a, b] m
  else if fo >>> 28 ≠ 3 then call1W p n "stuck_irrel" [mode, vis, d, a, b] m
  else if tierW fo ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m CONST (tierW fo) ≤ idxW fo then none
  else strK1 p n mode vis d a b side lt (tfld m CONST (tierW fo) (idxW fo) 0)
    (tfld m CONST (tierW fo) (idxW fo) 1) (callW p n "pin_word" [52] m)

end strK

-- raised: six calls and two node reads on the paths (about 20 s)
set_option maxHeartbeats 1000000 in
theorem stuckStr_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St)
    (mode vis d a b side lt fo : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "stuck_str" [mode, vis, d, a, b, side, lt, fo]
    ⦃fun r s' => LocEq s' s₀ ∧ strK p n mode vis d a b side lt fo s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.stuckStr]
  simp only [callFn, stuckStrL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, evalE_tld, tld,
    evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "pin_word", callW_spec p n "pin_at", callW_spec p n "str_lit_supported",
      callW_spec p n "str_lit_ctor", callW_spec p n "defeq", callW_spec p n "stuck_irrel"] <;>
  simp_all [strK, strK1, strK2, strK3, strK4, call1W, tierW, idxW, LocEq,
    BinOp.eval, St.setLocs_cons,
    CTL, Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

theorem decI_eq_iff' {k : IdxKind} {v w : Word} (hv : HW v) (hw : HW w) :
    (decI v : Idx k) = decI w ↔ v = w :=
  ⟨fun h => decI_inj hv hw h, fun h => by rw [h]⟩

/-- **`stuck_str` refines `stuckStrT`** at the knot (`lt` a literal handle, `side` the literal's
side). -/
@[refines_part ConRon.Arena.defeqStuck "the string-literal arms (stuckStrT)"]
theorem stuckStr_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b side lt fo : Word) (l : ConLeche.Literal) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hlt : HW lt) (hfo : HW fo)
    (hg : lt >>> 28 = 8) (hl : a₀.store.view (decE lt) = some (.lit l)) :
    CoreSpec p (n + 1) "stuck_str" [mode, vis, d, a, b, side, lt, fo]
      (stuckStrT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (side != 0) l
        (decE fo)) decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (stuckStr_spec p hq n s₀ mode vis d a b side lt fo)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hR := hS.arena.1
  have hK := hk n (Nat.le_refl _)
  have hirr : ∀ (st : AState) (m : Mem) (M' : ModeMaps), CoreS dn m st vis fe M' eb →
      call1W p n "stuck_irrel" [mode, vis, d, a, b] m = some (r.headD 0, s'.mem) →
      CoreRef (stuckIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) st decBool
        dn m vis fe M' eb r s'.mem := fun st m M' hS' hc' =>
    CoreSpec.of_call1W (s₀ := ⟨m, Locals.init []⟩)
      (stuckIrrel_at p hq hi hc n hk F _ st dn vis fe M' eb mode d a b hF hn
        ⟨hS', hs.mode4, hs.eb_mode⟩ ha hb) (fun r r' h => by simp only [decBool, h]) hc'
  simp only [strK] at hW
  obtain ⟨h1, hW⟩ := of_ite_none hW
  obtain ⟨h2, hW⟩ := of_ite_none hW
  obtain ⟨kn, hkv, hrec⟩ := view_lit_f s.mem a₀ hR lt hlt ⟨h1, by simpa using h2⟩ hg
  rw [hl] at hkv
  have hkl : kn.l = l := by cases hkv; rfl
  obtain ⟨kl⟩ := kn
  simp only at hkl
  subst hkl
  cases kl with
  | natVal N =>
    have h0 : tfld s.mem LIT (tierW lt) (idxW lt) 0 = 0 := hrec.1
    simp only [h0, ne_eq, show ¬ ((0 : Word) = 1) by decide, not_false_eq_true, ↓reduceIte] at hW
    exact hirr a₀ s.mem M hS hW
  | strVal st =>
    have h0 : tfld s.mem LIT (tierW lt) (idxW lt) 0 = 1 := hrec.1
    simp only [h0, ne_eq, not_true_eq_false, ↓reduceIte] at hW
    rcases (Classical.em (fo >>> 28 = 3)).symm with h3 | h3
    · simp only [h3, not_false_eq_true, ↓reduceIte] at hW
      unfold stuckStrT
      rw [tag_beq_const _ hfo]
      simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hirr a₀ s.mem M hS hW
    simp only [h3, not_true_eq_false, ↓reduceIte] at hW
    obtain ⟨h4, hW⟩ := of_ite_none hW
    obtain ⟨h5, hW⟩ := of_ite_none hW
    obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s.mem a₀ hR fo hfo ⟨h4, by simpa using h5⟩ h3
    have hct : ((decE fo).tag == ETag.const) = true := by rw [tag_beq_const _ hfo]; simp [h3]
    generalize tfld s.mem CONST (tierW fo) (idxW fo) 0 = co at hnw hW hv
    generalize tfld s.mem CONST (tierW fo) (idxW fo) 1 = uo at huw hW hv
    -- the pins
    obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
    obtain ⟨t₁, ht₁, hm₁, -, hr₁⟩ := triple_of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
      (pinWord_rd p hq.leaf.pinword n ⟨s.mem, Locals.init []⟩ 52) hc1
    have em₁ : m₁ = s.mem := by rw [← ht₁]; exact hm₁
    subst em₁
    simp only [strK1] at hW1
    obtain ⟨r₂, m₂, hc2, hW2⟩ := callW_cases rfl hW1
    obtain ⟨t₂, ht₂, hm₂, -, -, hr₂⟩ := triple_of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
      (pinAt_rd p hq.leaf.pinat n ⟨s.mem, Locals.init []⟩ 6) hc2
    have em₂ : m₂ = s.mem := by rw [← ht₂]; exact hm₂
    subst em₂
    simp only [strK2] at hW2
    -- `str_lit_supported`
    obtain ⟨r₃, m₃, hc3, hW3⟩ := callW_cases rfl hW2
    have h₃ := CoreSpec.of_callW (hc.strLitSupported n ⟨s.mem, Locals.init []⟩ a₀ dn vis fe M eb hS) hc3
    refine coreRef_congr (stuckStrT_run _ fe _ _ _ _ st _ a₀ s.mem hS.pins _ _ hct hv) ?_
    refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
    have hsl : HW (rdW (s.mem.arr64 PINS) (1 + 6)) := by
      have := hS.pins.names_lt 6 (by decide); rwa [pinW_rdW s.mem (1 + 6) (1 + 6) rfl] at this
    have hel : HW (rdW (s.mem.arr64 PINS) 52) := by
      have := hS.pins.lv_lt.1; rwa [pinW_rdW s.mem 52 52 rfl] at this
    simp only [pinW_rdW s.mem (1 + 6) (1 + 6) rfl, pinW_rdW s.mem 52 52 rfl, decI_eq_iff' hnw hsl,
      decI_eq_iff' huw hel]
    simp only [strK3, hr₁, hr₂] at hW3
    by_cases hcond : co = rdW (s.mem.arr64 PINS) (1 + 6) ∧ uo = rdW (s.mem.arr64 PINS) 52 ∧
        r₃.headD 0 ≠ 0
    · obtain ⟨hc₁, hc₂, hc₃⟩ := hcond
      simp only [hc₁, hc₂, hc₃, ne_eq, not_true_eq_false, ↓reduceIte] at hW3
      rw [ite_eq_left ⟨hc₁, hc₂, decBool_true_of hc₃⟩]
      obtain ⟨r₄, m₄, hc4, hW4⟩ := callW_cases rfl hW3
      have hv₃ := hc.supKeep fe a₀ (decE lt) _ hl
      have h₄ := CoreSpec.of_callW (hc.strLitCtor n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb lt st hS₃
        hlt hv₃) hc4
      refine coreRef_bind h₄ (fun M₄ hS₄ => ?_)
      simp only [strK4] at hW4
      by_cases hsd : side = 0
      · simp only [hsd, ↓reduceIte] at hW4
        simp only [hsd, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact CoreSpec.of_call1W (s₀ := ⟨m₄, Locals.init []⟩)
          (hK.defeq F _ _ dn vis fe M₄ eb mode d (r₄.headD 0) b hF hn ⟨hS₄, hs.mode4, hs.eb_mode⟩
            h₄.2.2.2 hb) (fun r r' h => by simp only [decBool, h]) hW4
      · simp only [hsd, ↓reduceIte] at hW4
        have : (side != 0) = true := by simpa using hsd
        simp only [this, ↓reduceIte]
        exact CoreSpec.of_call1W (s₀ := ⟨m₄, Locals.init []⟩)
          (hK.defeq F _ _ dn vis fe M₄ eb mode d a (r₄.headD 0) hF hn ⟨hS₄, hs.mode4, hs.eb_mode⟩
            ha h₄.2.2.2) (fun r r' h => by simp only [decBool, h]) hW4
    · have hW3' : call1W p n "stuck_irrel" [mode, vis, d, a, b] m₃ = some (r.headD 0, s'.mem) := by
        by_cases e1 : co = rdW (s.mem.arr64 PINS) (1 + 6)
        · by_cases e2 : uo = rdW (s.mem.arr64 PINS) 52
          · have e3 : r₃.headD 0 = 0 := Classical.byContradiction fun e3 => hcond ⟨e1, e2, e3⟩
            rwa [ite_eq_right ((fun h => h e1)), ite_eq_right ((fun h => h e2)), ite_eq_left e3] at hW3
          · rwa [ite_eq_right ((fun h => h e1)), ite_eq_left e2] at hW3
        · rwa [ite_eq_left e1] at hW3
      rw [ite_eq_right (fun h => hcond ⟨h.1, h.2.1, fun e => by
              have := h.2.2; rw [decBool_false_of e] at this; cases this⟩)]
      exact hirr _ m₃ M₃ hS₃ hW3'

end L.Arena
