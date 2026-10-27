import ConAgua.Arena.RecCheckSpec.PtrNamesWDec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

/-!
# TargetMajorAt2: `ConRon.Arena.targetMajorAt`

The refinement theorems `targetMajorAt_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `target_major_default` at every fuel -/

theorem targetMajorDefault_specF (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hpw : p.lookup "pin_word" = some pinWordL) (hm : p.lookup "mk_target_major" = some mkTargetMajor)
    (hp : p.lookup "target_major_default" = some targetMajorDefault) (hna : NaF p) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_default" []
    ⦃fun r s' => LocEq s' s₀ ∧ fuelW n (tmdW s₀.mem) = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact targetMajorDefault_spec p ha hpw hm hp hna n s₀

theorem tmdW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (hS : StageR dn vis fe m a) :
    RSim (fuelW n (tmdW m)) ConRon.Arena.targetMajorDefault a
      (KP dn vis fe m (fun m' r x => decTM m' (r.headD 0).toNat = some x)) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
    rintro ⟨r, m'⟩ h
    obtain ⟨tm, a', hrun, hS', hg, hd⟩ := tmdW_ok dn vis fe m m' a r h hS
    exact ⟨tm, a', hrun, hS', hg, hd⟩

/-! ## `target_major_at` -/

/-- After `target_major_default`. -/
def tmaK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m') => some ([r.headD 0], m')

/-- **The model of `target_major_at`.** -/
def tmaW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, mo, ml, c =>
    if c < ml then some ([rdW (m.arr64 IW) (mo + c)], m) else tmaK (fuelW n (tmdW m))

section arms
variable (n : Nat) (m m' : Mem) (mo ml c : Word) (r : List Word)
theorem tmaW_hit (h : c < ml) : tmaW (n + 1) m mo ml c = some ([rdW (m.arr64 IW) (mo + c)], m) := by
  simp [tmaW, h]
theorem tmaW_miss (h : ¬ c < ml) : tmaW (n + 1) m mo ml c = tmaK (fuelW n (tmdW m)) := by
  simp [tmaW, h]
theorem tmaK_some : tmaK (some (r, m')) = some ([r.headD 0], m') := rfl
end arms

grind_pattern [ind_grind] tmaW_hit => tmaW (n + 1) m mo ml c
grind_pattern [ind_grind] tmaW_miss => tmaW (n + 1) m mo ml c
grind_pattern [ind_grind] tmaK_some => tmaK (some (r, m'))

theorem targetMajorAt_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hpw : p.lookup "pin_word" = some pinWordL) (hm : p.lookup "mk_target_major" = some mkTargetMajor)
    (hd : p.lookup "target_major_default" = some targetMajorDefault)
    (hp : p.lookup "target_major_at" = some targetMajorAt) (hna : NaF p) (n : Nat) (s₀ : St) (mo ml c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_at" [mo, ml, c]
    ⦃fun r s' => LocEq s' s₀ ∧ tmaW n s₀.mem mo ml c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetMajorAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        targetMajorDefault_specF p ha hpw hm hd hna n] <;>
      finish (gen := 20) [rdW_eq]

/-- The decoded result of `target_major_at`. -/
def decTM0 (m' : Mem) (r : List Word) (x : TargetMajor) : Prop := decTM m' (r.headD 0).toNat = some x

theorem tmaW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (mo ml c : Word) (ms : List TargetMajor) (hS : StageR dn vis fe m a)
    (hms : decPL m (decTM m) mo.toNat ml.toNat = some ms) (_hb : mo.toNat + ml.toNat < 2 ^ 64) :
    RSim (tmaW n m mo ml c) (ConRon.Arena.targetMajorAt ms c.toNat) a (KP dn vis fe m decTM0) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
    by_cases hc : c < ml
    · rw [tmaW_hit n m mo ml c hc]
      have hc' : c.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hc
      obtain ⟨v, hv, hdec⟩ := decPL_getH m hms c.toNat hc'
      have hlen := decPL_length m hms
      have hrd := iwN_rdW_at (w := mo) (k := c.toNat) hv hS.2.2.2.1
      have hcw : mo + UInt64.ofNat c.toNat = mo + c := by simp
      rw [hcw] at hrd
      have hop : ConRon.Arena.targetMajorAt ms c.toNat = pure (ms[c.toNat]'(by omega)) := by
        simp [ConRon.Arena.targetMajorAt, List.getElem?_eq_getElem (by omega : c.toNat < ms.length)]
      rw [hop]
      refine RSim.pure_some ⟨hS, IWGrow.refl m, ?_⟩
      show decTM m (rdW (m.arr64 IW) (mo + c)).toNat = _
      rw [hrd.1, UInt64.toNat_ofNat_of_lt' hrd.2]; exact hdec
    · rw [tmaW_miss n m mo ml c hc]
      have hc' : ¬ c.toNat < ml.toNat := fun h => hc (UInt64.lt_iff_toNat_lt.mpr h)
      have hlen := decPL_length m hms
      have hop : ConRon.Arena.targetMajorAt ms c.toNat = ConRon.Arena.targetMajorDefault := by
        simp [ConRon.Arena.targetMajorAt, List.getElem?_eq_none (by omega : ms.length ≤ c.toNat)]
      rw [hop]
      refine RSim.mono (tmdW_sim dn vis fe n m a hS |> fun h => ?_) (fun _ _ _ _ h => h)
      intro b _hb
      cases ho : fuelW n (tmdW m) with
      | none => rw [ho] at _hb; cases _hb
      | some b0 =>
        obtain ⟨r0, m0⟩ := b0
        rw [ho, tmaK_some] at _hb; cases _hb
        obtain ⟨x, a', hr, hq⟩ := h _ ho
        exact ⟨x, a', hr, hq⟩

/-- **`target_major_at` refines `targetMajorAt`** (the hit arm a read, the miss arm
`target_major_default`). -/
@[refines ConRon.Arena.targetMajorAt]
theorem targetMajorAt_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hpw : p.lookup "pin_word" = some pinWordL) (hm : p.lookup "mk_target_major" = some mkTargetMajor)
    (hd : p.lookup "target_major_default" = some targetMajorDefault)
    (hp : p.lookup "target_major_at" = some targetMajorAt) (hna : NaF p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mo ml c : Word)
    (ms : List TargetMajor) (hS : StageR dn vis fe s₀.mem a₀)
    (hms : decPL s₀.mem (decTM s₀.mem) mo.toNat ml.toNat = some ms) (hb : mo.toNat + ml.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_at" [mo, ml, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetMajorAt ms c.toNat) a₀ ∧
      KP dn vis fe s₀.mem decTM0 (r, s'.mem) (AM.st (ConRon.Arena.targetMajorAt ms c.toNat) a₀)
        (AM.res (ConRon.Arena.targetMajorAt ms c.toNat) a₀); ⊤⦄ :=
  triple_post (targetMajorAt_spec p ha hpw hm hd hp hna n s₀ mo ml c) fun _ _ ⟨hl, hw⟩ =>
    ⟨hl, (tmaW_sim dn vis fe n _ a₀ mo ml c ms hS hms hb).am hw⟩

end L.Ind

end
