import ConAgua.Arena.IndSumSpec.Row
import ConAgua.Arena.IndSumSpec.SpgK3
import ConAgua.Arena.IndSumSpec.StructUsedLater
import ConAgua.Arena.IndSim
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# StructProjGuards: `ConRon.Arena.structProjGuards`

The refinement theorems `structProjGuards_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- After `pin_word(53)`: clear `hb`, then the used-later list. -/
def spgK1 (n : Nat) (m : Mem) (cty nP nF so sl : Word) : Option Word → Option (List Word × Mem)
  | none => none
  | some z =>
    if rdW (m.arr64 CTL) hbSch.cs + 2 = 0 then none
    else spgK2 n so sl z nF (ulW n (mclearG hbSch m) cty nP nF 0)

/-- **The model of `struct_proj_guards(cty, nP, nF, so, sl)`** at callee fuel `n`. -/
def spgW (n : Nat) (m : Mem) (cty nP nF so sl : Word) : Option (List Word × Mem) :=
  spgK1 n m cty nP nF so sl (pinWordV m 53)

section arms
variable (n : Nat) (m m1 : Mem) (cty nP nF so sl z : Word) (r u : List Word)
theorem spgK1_some_zero (h : rdW (m.arr64 CTL) hbSch.cs + 2 = 0) :
    spgK1 n m cty nP nF so sl (some z) = none := by simp [spgK1, h]
theorem spgK1_some (h : rdW (m.arr64 CTL) hbSch.cs + 2 ≠ 0) :
    spgK1 n m cty nP nF so sl (some z) =
      spgK2 n so sl z nF (ulW n (mclearG hbSch m) cty nP nF 0) := by simp [spgK1, h]
end arms
attribute [ind_grind] spgK1_some_zero spgK1_some

/-! ## The spec -/

section spec
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p) (hst : StripProg p)
  (hsg : p.lookup "struct_used_later_go" = some structUsedLaterGoL)
  (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hul : p.lookup "struct_used_later_list" = some structUsedLaterListL)
  (hgd : p.lookup "sl_getd" = some slGetD)
  (hmf : p.lookup "max_find" = some maxFind) (hmp : p.lookup "max_push" = some maxPush)
  (him : p.lookup "intern_max" = some internMax)
  (hcol : p.lookup "struct_proj_guards_col" = some structProjGuardsColL)
  (hrow : p.lookup "struct_proj_guards_row" = some structProjGuardsRowL)
  (hpw : p.lookup "pin_word" = some pinWordL) (hcl : p.lookup "hb_clear" = some (memoClearG hbSch))
  (hp : p.lookup "struct_proj_guards" = some structProjGuardsL)

include hv hf hput hins hgo hbp hst hsg ha hc hsc hul hgd hmf hmp him hcol hrow hpw hcl hp in
theorem spg_spec (n : Nat) (s₀ : St) (cty nP nF so sl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_proj_guards" [cty, nP, nF, so, sl]
    ⦃fun r s' => LocEq s' s₀ ∧ spgW n s₀.mem cty nP nF so sl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structProjGuardsL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinWord_specV p hpw n,
      memoClearG_spec hbSch p _ hcl n, ulW_spec p hv hf hput hins hgo hbp hst hsg ha hc hsc hul n,
      rowW_spec p hgd hmf hmp him hcol ha hc hsc hrow n] <;>
    finish (gen := 20) [spgW]

end spec

/-! ## The relation to the twin -/

theorem iwB_of_iwN {m : Mem} {i : Nat} {b : Bool} (h : iwN m i = some (if b then 1 else 0)) :
    iwB m i = some b := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, hv⟩ := h
  simp only [iwB, bool?, hw, Option.map_some, Option.some.injEq]
  cases b <;> simp at hv
  · exact (bne_eq_false_iff_eq).mpr (UInt64.toNat_inj.mp (by simpa using hv))
  · simp only [bne_iff_ne, ne_eq]; intro e; rw [e] at hv; simp at hv

theorem mapM_iwB_of_bnums {m : Mem} {o : Nat} : ∀ (js : List Nat) (bs : List Bool),
    js.mapM (fun j => iwN m (o + j)) = some (bnums bs) → js.mapM (fun j => iwB m (o + j)) = some bs
  | [], bs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h ⊢
    cases bs with | nil => rfl | cons _ _ => simp [bnums] at h
  | j :: js, bs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨y, hy, ys, hys, e⟩ := h
    cases bs with
    | nil => simp [bnums] at e
    | cons b bt =>
      simp only [bnums, List.map_cons, List.cons.injEq] at e
      obtain ⟨rfl, e2⟩ := e
      exact ⟨b, iwB_of_iwN hy, bt, mapM_iwB_of_bnums js bt (by rw [hys, e2]; rfl), rfl⟩

/-- The used-later flags as numbers `0`/`1` are the flags as `Bool`s. -/
theorem decBL_of_bnums {m : Mem} {o l : Nat} {bs : List Bool}
    (h : decNL m o l = some (bnums bs)) : decBL m o l = some bs :=
  mapM_iwB_of_bnums _ _ h

/-- **`struct_proj_guards`' model refines `structProjGuards`** from the stage relation and a related
`hb` memo, for a sorts slice below the pool's top. -/
theorem spgW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat)
    (m : Mem) (a : AState) (cty nP nF so sl : Word) (sorts : List LIdx)
    (mp : Std.HashMap (EIdx × Nat) Bool) (hc' : H cty)
    (hb : nP.toNat + nF.toNat + 1 < 2 ^ 64) (hS : StageR dn vis fe m a) (hM : hbMR m mp)
    (hs : decHL m so.toNat sl.toNat = some sorts) (hst : so.toNat + sl.toNat ≤ iwTop m) :
    Sim (spgW n m cty nP nF so sl) (structProjGuards (decI cty) nP.toNat nF.toNat sorts) a
      (fun r gs m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some gs ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m') := by
  unfold spgW
  simp only [structProjGuards]
  cases hz' : pinWordV m 53 with
  | none => exact fun _ _ e => by simp [spgK1] at e
  | some z =>
  obtain ⟨hrun0, hz⟩ := pinZero_stage hS hz'
  refine Sim.bind_twin hrun0 ?_
  by_cases h0 : rdW (m.arr64 CTL) hbSch.cs + 2 = 0
  · intro r m' e; rw [spgK1_some_zero n m cty nP nF so sl z h0] at e; cases e
  rw [spgK1_some n m cty nP nF so sl z h0]
  have hf0 := mclearG_frame hbSch m
  have hM0 := memoRV_clear hbSch hbSch_wf lfKey hbVR m mp hM h0
  obtain ⟨hS0, hg0⟩ := StageR.frame_hi hS hf0 (by simp) (by
      intro x hx; simp [hbSch] at hx; rcases hx with rfl | rfl <;> decide) (by simp) (by simp [hbSch])
  refine Sim.bindK rfl (fun _ _ => rfl)
    (Q := fun u bs m2 a2 => decNL m2 (u.headD 0).toNat (u.tail.headD 0).toNat = some (bnums bs) ∧
      u.tail.headD 0 = nF ∧ (u.headD 0).toNat + nF.toNat = iwTop m2 ∧ StageR dn vis fe m2 a2 ∧
      IWGrow m m2) ?_ fun u bs m2 a2 ⟨hd, hl, ht, hS2, hg2⟩ => ?_
  · intro u m2 e
    obtain ⟨bs, mp', a', hrun, hdec, hlen, htop, -, hS', hg⟩ :=
      ulW_ok n _ _ a cty nP nF 0 u ∅ (by simpa using hb) hc' hS0 hM0 e
    exact ⟨bs, a', by simpa using hrun, hdec, hlen, htop, hS', hg0.trans hg⟩
  have hu := decBL_of_bnums hd
  rw [hl] at hu
  intro r m' e
  rw [spgK2_some] at e
  rcases hr : rowW n m2 (u.headD 0) nF so sl z 0 nF with _ | ⟨rr, m3⟩
  · rw [hl, hr] at e; cases e
  rw [hl, hr, spgK3_some] at e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
  have hst2 : so.toNat + sl.toNat ≤ iwTop m2 := Nat.le_trans hst hg2.1
  obtain ⟨gs, a3, hrun, hS3, hg3, hd3, ht3⟩ := rowW_ok dn vis fe n m2 m3 a2 _ _ so sl z 0 nF rr bs sorts
    hr hS2 hu (by rw [decHL_grow hg2 hst]; exact hs) (hS2.lt64 (by omega)) (hS2.lt64 hst2) (by omega)
    hst2 hz (by simpa using hS2.lt64 (x := nF.toNat) (by omega))
  exact ⟨gs, a3, by simpa using hrun, hS3, hg2.trans hg3, by simpa using hd3, by simpa using ht3⟩

/-! ## The census theorem -/

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p) (hst : StripProg p)
  (hsg : p.lookup "struct_used_later_go" = some structUsedLaterGoL)
  (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hul : p.lookup "struct_used_later_list" = some structUsedLaterListL)
  (hgd : p.lookup "sl_getd" = some slGetD)
  (hmf : p.lookup "max_find" = some maxFind) (hmp : p.lookup "max_push" = some maxPush)
  (him : p.lookup "intern_max" = some internMax)
  (hcol : p.lookup "struct_proj_guards_col" = some structProjGuardsColL)
  (hrow : p.lookup "struct_proj_guards_row" = some structProjGuardsRowL)
  (hpw : p.lookup "pin_word" = some pinWordL) (hcl : p.lookup "hb_clear" = some (memoClearG hbSch))
  (hp : p.lookup "struct_proj_guards" = some structProjGuardsL)

include hv hf hput hins hgo hbp hst hsg ha hc hsc hul hgd hmf hmp him hcol hrow hpw hcl hp in
/-- **`struct_proj_guards` refines `structProjGuards`** from the stage relation and a related `hb`
memo (any well-formed one: the walk clears it). -/
@[refines ConRon.Arena.structProjGuards]
theorem structProjGuards_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis cty nP nF so sl : Word) (sorts : List LIdx) (mp : Std.HashMap (EIdx × Nat) Bool)
    (hc' : H cty) (hb : nP.toNat + nF.toNat + 1 < 2 ^ 64)
    (hS : StageR dn vis fe s₀.mem a₀) (hM : hbMR s₀.mem mp)
    (hs : decHL s₀.mem so.toNat sl.toNat = some sorts) (hsbd : so.toNat + sl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_proj_guards" [cty, nP, nF, so, sl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structProjGuards (decI cty) nP.toNat nF.toNat sorts) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (structProjGuards (decI cty) nP.toNat nF.toNat sorts) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (structProjGuards (decI cty) nP.toNat nF.toNat sorts) a₀); ⊤⦄ := by
  refine triple_post (spg_spec p hv hf hput hins hgo hbp hst hsg ha hc hsc hul hgd hmf hmp him hcol hrow
    hpw hcl hp n s₀ cty nP nF so sl) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hok, hS', hg, hd, -⟩ := (spgW_ok n _ a₀ cty nP nF so sl sorts mp hc' hb hS hM hs hsbd).run hm
  exact ⟨hl, hok, hS', hg, hd⟩

end census

end L.Ind

end
