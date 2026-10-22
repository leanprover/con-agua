import ConAgua.Arena.IndSumSpec5
import ConAgua.Arena.RecClassSpec

/-!
# Refinements of `IndSum`, seventh file (lane `indproofs`, helper `memo`)

`struct_used_later_go`, `struct_used_later` and `struct_used_later_list` (the `hb` memo walks of
`IndSumSpec5.lean` behind `strip_pis`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `struct_used_later_go`, `struct_used_later`: the word models -/

/-- After `strip_pis`: `0` if it failed, else the walk of the body from index `0`. -/
def usgK1 (n : Nat) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (rs, m1) => if rs.headD 0 = 0 then some (0, m1) else hbGoW n m1 0 (rs.tail.tail.tail.headD 0)

def usgW (n : Nat) (m : Mem) (cty nP j : Word) : Option (Word × Mem) :=
  usgK1 n (stubM "strip_pis" m [nP + j + 1, cty])

/-- Same, with the fresh-memo `has_loose_b_var_b_fast`. -/
def ustK1 (n : Nat) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (rs, m1) => if rs.headD 0 = 0 then some (0, m1) else hbFastW n m1 0 (rs.tail.tail.tail.headD 0)

def ustW (n : Nat) (m : Mem) (cty nP j : Word) : Option (Word × Mem) :=
  ustK1 n (stubM "strip_pis" m [nP + j + 1, cty])

theorem usgK1_some_zero {n : Nat} {rs : List Word} {m1 : Mem} (h : rs.headD 0 = 0) :
    usgK1 n (some (rs, m1)) = some (0, m1) := by simp only [usgK1, if_pos h]
theorem usgK1_some_ne {n : Nat} {rs : List Word} {m1 : Mem} (h : ¬ rs.headD 0 = 0) :
    usgK1 n (some (rs, m1)) = hbGoW n m1 0 (rs.tail.tail.tail.headD 0) := by simp only [usgK1, if_neg h]
theorem ustK1_some_zero {n : Nat} {rs : List Word} {m1 : Mem} (h : rs.headD 0 = 0) :
    ustK1 n (some (rs, m1)) = some (0, m1) := by simp only [ustK1, if_pos h]
theorem ustK1_some_ne {n : Nat} {rs : List Word} {m1 : Mem} (h : ¬ rs.headD 0 = 0) :
    ustK1 n (some (rs, m1)) = hbFastW n m1 0 (rs.tail.tail.tail.headD 0) := by simp only [ustK1, if_neg h]
attribute [ind_grind] usgK1_some_zero usgK1_some_ne ustK1_some_zero ustK1_some_ne

section spec
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL)

include hv hf hput hins hgo in
theorem structUsedLaterGo_spec (hp : p.lookup "struct_used_later_go" = some structUsedLaterGoL)
    (n : Nat) (s₀ : St) (cty nP j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_used_later_go" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧ usgW n s₀.mem cty nP j = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := hbGo_spec p hv hf hput hins hgo n
  unfold HbGoSpec at ih
  rw [invoke_eq _ hp]
  simp only [callFn, structUsedLaterGoL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, stubM_spec p "strip_pis" n, ih] <;>
    finish [usgW]

include hv hf hput hins hgo in
theorem structUsedLater_spec (hcl : p.lookup "hb_clear" = some (memoClearG hbSch))
    (hfast : p.lookup "has_loose_b_var_b_fast" = some hasLooseBVarBFastL)
    (hp : p.lookup "struct_used_later" = some structUsedLaterL)
    (n : Nat) (s₀ : St) (cty nP j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "struct_used_later" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧ ustW n s₀.mem cty nP j = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structUsedLaterL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, stubM_spec p "strip_pis" (n + 1),
      hbFast_spec p hv hf hput hins hgo hcl hfast n] <;>
    finish [ustW]

end spec

/-! ## The relation to the twin -/

theorem usDrop3_eq (rs : List Word) : rs.drop 3 = rs.tail.tail.tail := by
  rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> rfl

theorem add3_toNat {nP j : Word} (h : nP.toNat + j.toNat + 1 < 2 ^ 64) :
    (nP + j + 1).toNat = nP.toNat + j.toNat + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_add]; simp; omega

theorem usgW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat)
    (m m' : Mem) (a : AState) (cty nP j r : Word) (mp : Std.HashMap (EIdx × Nat) Bool)
    (hn : 2 ^ 31 + n ≤ coreWalkFuel) (hsum : nP.toNat + j.toNat + 1 < 2 ^ 64) (hc : H cty)
    (hS : StageR dn vis fe m a) (hM : hbMR m mp) (h : usgW n m cty nP j = some (r, m')) :
    ∃ b mp' a', (structUsedLaterGo mp (decI cty) nP.toNat j.toNat).run a = .ok ((b, mp'), a') ∧
      r = (if b then 1 else 0) ∧ hbMR m' mp' ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  simp only [usgW] at h
  cases hst : stubM "strip_pis" m [nP + j + 1, cty] with
  | none => rw [hst] at h; simp [usgK1] at h
  | some pr =>
    obtain ⟨rs, m1⟩ := pr
    rw [hst] at h
    obtain ⟨x, a1, hrun, hS1, hg1, hdec⟩ := stripPis_spec dn vis fe (nP + j + 1) cty hc m m1 a rs hst hS
    obtain ⟨A, C, hA, hC, hfr⟩ := stubHbFrame "strip_pis" (Or.inr rfl) m m1 _ rs hst
    have hM1 : hbMR m1 mp :=
      memoRV_frame hbSch hbSch_wf lfKey hbVR A C hA hC m m1 hfr (fun _ _ h => h) mp hM
    rw [add3_toNat hsum] at hrun
    cases x with
    | none =>
      have hz : rs.headD 0 = 0 := hdec
      rw [usgK1_some_zero hz] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨false, mp, a1, ?_, rfl, hM1, hS1, hg1⟩
      simp only [structUsedLaterGo, StateT.run_bind]
      rw [hrun]
      rfl
    | some le =>
      obtain ⟨l, e⟩ := le
      obtain ⟨h1, -, hb32, hbe⟩ := hdec
      rw [usgK1_some_ne (by rw [h1]; decide)] at h
      rw [usDrop3_eq] at hb32 hbe
      have hbH : H (rs.tail.tail.tail.headD 0) := hb32
      obtain ⟨b, mp', a', hr2, hb, hM2, hS2, hg2⟩ :=
        hbGoOK n m1 m' a1 0 (rs.tail.tail.tail.headD 0) r mp coreWalkFuel hn (Nat.le_refl _) h hS1 hbH hM1
      refine ⟨b, mp', a', ?_, hb, hM2, hS2, hg1.trans hg2⟩
      rw [show (0 : Word).toNat = 0 from rfl, decE_eq, hbe] at hr2
      simp only [structUsedLaterGo, StateT.run_bind]
      rw [hrun]
      simp only [except_ok_bind]
      exact hr2

theorem ustW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat)
    (m m' : Mem) (a : AState) (cty nP j r : Word) (mp : Std.HashMap (EIdx × Nat) Bool)
    (hn : 2 ^ 31 + n ≤ coreWalkFuel) (hsum : nP.toNat + j.toNat + 1 < 2 ^ 64) (hc : H cty)
    (hS : StageR dn vis fe m a) (hM : hbMR m mp) (h : ustW n m cty nP j = some (r, m')) :
    ∃ b a', (structUsedLater (decI cty) nP.toNat j.toNat).run a = .ok (b, a') ∧
      r = (if b then 1 else 0) ∧ (∃ mp1, hbMR m' mp1) ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  simp only [ustW] at h
  cases hst : stubM "strip_pis" m [nP + j + 1, cty] with
  | none => rw [hst] at h; simp [ustK1] at h
  | some pr =>
    obtain ⟨rs, m1⟩ := pr
    rw [hst] at h
    obtain ⟨x, a1, hrun, hS1, hg1, hdec⟩ := stripPis_spec dn vis fe (nP + j + 1) cty hc m m1 a rs hst hS
    obtain ⟨A, C, hA, hC, hfr⟩ := stubHbFrame "strip_pis" (Or.inr rfl) m m1 _ rs hst
    have hM1 : hbMR m1 mp :=
      memoRV_frame hbSch hbSch_wf lfKey hbVR A C hA hC m m1 hfr (fun _ _ h => h) mp hM
    rw [add3_toNat hsum] at hrun
    cases x with
    | none =>
      have hz : rs.headD 0 = 0 := hdec
      rw [ustK1_some_zero hz] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨false, a1, ?_, rfl, ⟨mp, hM1⟩, hS1, hg1⟩
      simp only [structUsedLater, StateT.run_bind]
      rw [hrun]
      rfl
    | some le =>
      obtain ⟨l, e⟩ := le
      obtain ⟨h1, -, hb32, hbe⟩ := hdec
      rw [ustK1_some_ne (by rw [h1]; decide)] at h
      rw [usDrop3_eq] at hb32 hbe
      have hbH : H (rs.tail.tail.tail.headD 0) := hb32
      obtain ⟨b, a', hr2, hb, hM2, hS2, hg2⟩ :=
        hbFastW_ok n m1 m' a1 0 (rs.tail.tail.tail.headD 0) r mp hn hbH hS1 hM1 h
      refine ⟨b, a', ?_, hb, hM2, hS2, hg1.trans hg2⟩
      rw [show (0 : Word).toNat = 0 from rfl, decE_eq, hbe] at hr2
      simp only [structUsedLater, StateT.run_bind]
      rw [hrun]
      simp only [except_ok_bind]
      exact hr2

/-! ## The census theorems -/

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL)

include hv hf hput hins hgo in
/-- **`struct_used_later_go` refines `structUsedLaterGo`** (through the stubs `strip_pis`, `bvar_b`),
sharing the caller's `hb` memo. -/
@[refines ConRon.Arena.structUsedLaterGo]
theorem structUsedLaterGo_refines (hp : p.lookup "struct_used_later_go" = some structUsedLaterGoL)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis cty nP j : Word)
    (mp : Std.HashMap (EIdx × Nat) Bool) (hn : 2 ^ 31 + n ≤ coreWalkFuel)
    (hsum : nP.toNat + j.toNat + 1 < 2 ^ 64) (hc : H cty) (hS : StageR dn vis fe s₀.mem a₀)
    (hM : hbMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_used_later_go" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (structUsedLaterGo mp (decI cty) nP.toNat j.toNat) a₀ ∧
      r.headD 0 = (if (AM.res (structUsedLaterGo mp (decI cty) nP.toNat j.toNat) a₀).1 then 1 else 0) ∧
      hbMR s'.mem (AM.res (structUsedLaterGo mp (decI cty) nP.toNat j.toNat) a₀).2 ∧
      StageR dn vis fe s'.mem (AM.st (structUsedLaterGo mp (decI cty) nP.toNat j.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (structUsedLaterGo_spec p hv hf hput hins hgo hp n s₀ cty nP j) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, mp', a', hrun, hb, hM', hS', hg⟩ := usgW_ok n _ _ a₀ cty nP j _ mp hn hsum hc hS hM hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hb, by rw [hres]; exact hM', by rw [hst]; exact hS', hg⟩

include hv hf hput hins hgo in
/-- **`struct_used_later` refines `structUsedLater`** (through `strip_pis`, `bvar_b`): clears the `hb`
memo and walks. -/
@[refines ConRon.Arena.structUsedLater]
theorem structUsedLater_refines (hcl : p.lookup "hb_clear" = some (memoClearG hbSch))
    (hfast : p.lookup "has_loose_b_var_b_fast" = some hasLooseBVarBFastL)
    (hp : p.lookup "struct_used_later" = some structUsedLaterL)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis cty nP j : Word)
    (mp : Std.HashMap (EIdx × Nat) Bool) (hn : 2 ^ 31 + n ≤ coreWalkFuel)
    (hsum : nP.toNat + j.toNat + 1 < 2 ^ 64) (hc : H cty) (hS : StageR dn vis fe s₀.mem a₀)
    (hM : hbMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "struct_used_later" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (structUsedLater (decI cty) nP.toNat j.toNat) a₀ ∧
      r.headD 0 = (if AM.res (structUsedLater (decI cty) nP.toNat j.toNat) a₀ then 1 else 0) ∧
      (∃ mp1, hbMR s'.mem mp1) ∧
      StageR dn vis fe s'.mem (AM.st (structUsedLater (decI cty) nP.toNat j.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (structUsedLater_spec p hv hf hput hins hgo hcl hfast hp n s₀ cty nP j) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hb, hM', hS', hg⟩ := ustW_ok n _ _ a₀ cty nP j _ mp hn hsum hc hS hM hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hb, hM', by rw [hst]; exact hS', hg⟩

end census
