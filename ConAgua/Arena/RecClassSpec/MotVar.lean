import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Census.Attr

/-!
# MotVar: `ConRon.Arena.ClassGen.ihParts`, `ConRon.Arena.ClassGen.motVar`, `ConRon.Arena.ClassGen.slotVar`, `ConRon.Arena.ClassRead.motiveSlot`, `ConRon.Arena.classRecOf`

The refinement theorems `classRecOf_refines`, `classReadMotiveSlot_refines`, `classGenSlotVar_refines`, `classGenMotVar_refines`, `classGenIhParts_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`class_rec_of` refines `classRecOf`**: `(1, name)` for `some name`, `(0, 0)` for `none`; the
memory is unchanged. -/
@[refines ConRon.Arena.classRecOf]
theorem classRecOf_refines (p : Prog) (hp : p.lookup "class_rec_of" = some classRecOf) (n : Nat)
    (s₀ : St) (rco rcl cgo cgl t : Word) (rc : List Nat) (cs : List IConstantVal)
    (hrc : decNL s₀.mem rco.toNat rcl.toNat = some rc)
    (hcs : decPL s₀.mem (decCVp s₀.mem) cgo.toNat cgl.toNat = some cs)
    (hb1 : rco.toNat + rcl.toNat < 2 ^ 64) (hb2 : cgo.toNat + cgl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_of" [rco, rcl, cgo, cgl, t]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      (match ConRon.Arena.classRecOf rc cs t.toNat with
        | none => r = [0, 0]
        | some nm => r.headD 0 = 1 ∧ (r.tail.headD 0).toNat < 2 ^ 32 ∧ decI (r.tail.headD 0) = nm);
      ⊤⦄ := by
  refine triple_post (classRecOf_spec p hp n s₀ rco rcl cgo cgl t) ?_
  rintro r s' ⟨hl, hm, hw⟩
  obtain ⟨g1, g2⟩ := classRecOfW_ok n _ rco rcl cgo cgl t r rc cs hw hrc hcs hb1 hb2
  refine ⟨hl, hm, ?_⟩
  have e := crOf_eq t.toNat cs rc
  simp only [ConRon.Arena.classRecOf] at *
  rw [e]
  cases hc : crOf t.toNat rc cs with
  | none => exact g1 hc
  | some nm => exact g2 nm hc

/-- **`class_read_motive_slot` refines `ClassRead.motiveSlot`**: `(1, i)` for `some i`, `(0, 0)` for
`none`; memory unchanged. -/
@[refines ConRon.Arena.ClassRead.motiveSlot]
theorem classReadMotiveSlot_refines (p : Prog)
    (hp : p.lookup "class_read_motive_slot" = some classReadMotiveSlot) (n : Nat) (s₀ : St)
    (so sl c : Word) (sls : List ClassSlot) (hdec : decPL s₀.mem (decCS s₀.mem) so.toNat sl.toNat = some sls)
    (hb : so.toNat + sl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_motive_slot" [so, sl, c]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r = msRes (ConRon.Arena.ClassRead.motiveSlot sls c.toNat); ⊤⦄ := by
  refine triple_post (classReadMotiveSlot_spec p hp n s₀ so sl c) ?_
  rintro r s' ⟨hl, hm, hw⟩
  refine ⟨hl, hm, ?_⟩
  rw [msW_ok n _ so sl c r sls hw hdec hb]
  have := motIdx_eq 0 sls
  simp only [Nat.zero_add, List.map_id'] at this
  simp only [ConRon.Arena.ClassRead.motiveSlot]
  erw [this]

/-- **`class_gen_slot_var` refines `ClassGen.slotVar`** (through `pin_word` and master's interning). -/
@[refines ConRon.Arena.ClassGen.slotVar]
theorem classGenSlotVar_refines (p : Prog) (hpin : p.lookup "pin_word" = some pinWordL)
    (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
    (his : p.lookup "intern_sort" = some internSort)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hp : p.lookup "class_gen_slot_var" = some classGenSlotVar) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g s : Word) (G : ClassGen)
    (hS : StageR dn vis fe s₀.mem a₀) (hg : iwN s₀.mem g.toNat = some G.nP)
    (hgt : g.toNat < iwTop s₀.mem) (hns : G.nP + s.toNat < 2 ^ 64) :
    ⦃fun s_ => s_ = s₀⦄ invoke p (exec p n) "class_gen_slot_var" [g, s]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.slotVar G s.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.ClassGen.slotVar G s.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.ClassGen.slotVar G s.toNat) a₀; ⊤⦄ := by
  refine triple_post (slotVar_spec p hpin hsf hsp his hff hfp hif hp n s₀ g s) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hgr, h1, h2⟩ := slotVarW_ok dn vis fe _ _ a₀ g s G r hS hg hgt hns hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.ClassGen.slotVar G s.toNat) a₀ a' x hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hgr, h1, by rw [hres]; exact h2⟩

/-- **`class_gen_mot_var` refines `ClassGen.motVar`**. -/
@[refines ConRon.Arena.ClassGen.motVar]
theorem classGenMotVar_refines (p : Prog) (hpin : p.lookup "pin_word" = some pinWordL)
    (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
    (his : p.lookup "intern_sort" = some internSort)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hsv : p.lookup "class_gen_slot_var" = some classGenSlotVar)
    (hms : p.lookup "class_read_motive_slot" = some classReadMotiveSlot)
    (hp : p.lookup "class_gen_mot_var" = some classGenMotVar) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g c : Word) (G : ClassGen)
    (hS : StageR dn vis fe s₀.mem a₀) (hg : iwN s₀.mem g.toNat = some G.nP)
    (hgt : g.toNat < iwTop s₀.mem)
    (hsl : decAt s₀.mem (decPL s₀.mem (decCS s₀.mem)) (g.toNat + 7) = some G.slots)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hgb : g.toNat + 9 < 2 ^ 64)
    (hsz : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) :
    ⦃fun s_ => s_ = s₀⦄ invoke p (exec p (n + 1)) "class_gen_mot_var" [g, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.motVar G c.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.ClassGen.motVar G c.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.ClassGen.motVar G c.toNat) a₀; ⊤⦄ := by
  refine triple_post (motVar_spec p hpin hsf hsp his hff hfp hif hsv hms hp n s₀ g c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hgr, h1, h2⟩ := motVarW_ok dn vis fe n _ _ a₀ g c G r hS hg hgt hsl hns hgb (by omega) hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.ClassGen.motVar G c.toNat) a₀ a' x hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hgr, h1, by rw [hres]; exact h2⟩

/-- **`class_gen_ih_parts` refines `ClassGen.ihParts`** (through `open_pis_at_fvars_f`'s real
refinement, under the walk memos, and `get_app_args`). -/
@[refines ConRon.Arena.ClassGen.ihParts]
theorem classGenIhParts_refines (p : Prog) (hp : p.lookup "class_gen_ih_parts" = some classGenIhParts)
    (had : AdF p) (hopf : OpfF p) (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv)
    (g t tele w d : Word) (G : ClassGen) (hS : StageR dn vis fe s₀.mem a₀) (hw : H w)
    (hcls : decAt s₀.mem (decPL s₀.mem (decTM s₀.mem)) (g.toNat + 3) = some G.cls)
    (hsz : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_gen_ih_parts" [g, t, tele, w, d]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      IhRes s'.mem r (AM.res (ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat) a₀) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (classGenIhParts_spec p hp had hopf n s₀ g t tele w d) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨res, a', hrun, hS', hg, hres, hA'⟩ := ihW_ok dn vis fe _ _ a₀ g t tele w d G r hS hw hcls (by omega) hA hm
  obtain ⟨hok, hst, hrs⟩ := AM.of_run_ok (ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat) a₀ a' res hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hrs]; exact hres, hA'⟩

end L.Ind

end
