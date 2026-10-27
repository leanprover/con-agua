import ConAgua.Arena.IndSumSpec.Bnums
import ConAgua.Arena.IndSumSpec.McGoStep
import ConAgua.Arena.IndSumSpec.StructProjArgP
import ConAgua.Arena.RecClassSpec.Classes
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

/-!
# StructUsedLater: `ConRon.Arena.structUsedLaterGo`, `ConRon.Arena.structUsedLaterList`, `ConRon.Arena.structUsedLater`

The refinement theorems `structUsedLaterGo_refines`, `structUsedLater_refines`, `structUsedLaterList_refines` and the lemmas only they use.
-/

noncomputable section

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
  | some (rs, m1) => if rs.headD 0 = 0 then some (0, m1) else hbGoW n m1 CWF 0 (rs.tail.tail.tail.headD 0)

def usgW (n : Nat) (m : Mem) (cty nP j : Word) : Option (Word × Mem) :=
  usgK1 n (stripF 6 m [nP + j + 1, cty])

/-- Same, with the fresh-memo `has_loose_b_var_b_fast`. -/
def ustK1 (n : Nat) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (rs, m1) => if rs.headD 0 = 0 then some (0, m1) else hbFastW n m1 0 (rs.tail.tail.tail.headD 0)

def ustW (n : Nat) (m : Mem) (cty nP j : Word) : Option (Word × Mem) :=
  ustK1 n (stripF 6 m [nP + j + 1, cty])

theorem usgK1_some_zero {n : Nat} {rs : List Word} {m1 : Mem} (h : rs.headD 0 = 0) :
    usgK1 n (some (rs, m1)) = some (0, m1) := by simp only [usgK1, ite_eq_left h]
theorem usgK1_some_ne {n : Nat} {rs : List Word} {m1 : Mem} (h : ¬ rs.headD 0 = 0) :
    usgK1 n (some (rs, m1)) = hbGoW n m1 CWF 0 (rs.tail.tail.tail.headD 0) := by simp only [usgK1, ite_eq_right h]
theorem ustK1_some_zero {n : Nat} {rs : List Word} {m1 : Mem} (h : rs.headD 0 = 0) :
    ustK1 n (some (rs, m1)) = some (0, m1) := by simp only [ustK1, ite_eq_left h]
theorem ustK1_some_ne {n : Nat} {rs : List Word} {m1 : Mem} (h : ¬ rs.headD 0 = 0) :
    ustK1 n (some (rs, m1)) = hbFastW n m1 0 (rs.tail.tail.tail.headD 0) := by simp only [ustK1, ite_eq_right h]
attribute [ind_grind] usgK1_some_zero usgK1_some_ne ustK1_some_zero ustK1_some_ne

section spec
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p) (hst : StripProg p)

include hv hf hput hins hgo hbp hst in
theorem structUsedLaterGo_spec (hp : p.lookup "struct_used_later_go" = some structUsedLaterGoL)
    (n : Nat) (s₀ : St) (cty nP j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_used_later_go" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧ usgW n s₀.mem cty nP j = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := hbGo_spec p hv hf hput hins hgo hbp n
  unfold HbGoSpec at ih
  rw [invoke_eq _ hp]
  simp only [callFn, structUsedLaterGoL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, stripPis_specF p hst n, ih] <;>
    finish [usgW]

include hv hf hput hins hgo hbp hst in
theorem structUsedLater_spec (hcl : p.lookup "hb_clear" = some (memoClearG hbSch))
    (hfast : p.lookup "has_loose_b_var_b_fast" = some hasLooseBVarBFastL)
    (hp : p.lookup "struct_used_later" = some structUsedLaterL)
    (n : Nat) (s₀ : St) (cty nP j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "struct_used_later" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧ ustW n s₀.mem cty nP j = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structUsedLaterL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, stripPis_specF p hst (n + 1),
      hbFast_spec p hv hf hput hins hgo hbp hcl hfast n] <;>
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
    (hsum : nP.toNat + j.toNat + 1 < 2 ^ 64) (hc : H cty)
    (hS : StageR dn vis fe m a) (hM : hbMR m mp) (h : usgW n m cty nP j = some (r, m')) :
    ∃ b mp' a', (structUsedLaterGo mp (decI cty) nP.toNat j.toNat).run a = .ok ((b, mp'), a') ∧
      r = (if b then 1 else 0) ∧ hbMR m' mp' ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  simp only [usgW] at h
  obtain ⟨rs, m1, hst, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  obtain ⟨x, a1, hrun, hS1, hg1, hdec⟩ := stripF_pis_ok dn vis fe (nP + j + 1) cty hc m m1 a rs hst hS
  have hM1 : hbMR m1 mp := memoRV_frame hbSch hbSch_wf lfKey hbVR [IW] [200] (by simp [hbSch, HBM, IW])
    (by simp [hbSch]) m m1 (stripF_frame hst) (fun _ _ h => h) mp hM
  rw [add3_toNat hsum] at hrun
  cases x with
  | none =>
    have hz : rs.headD 0 = 0 := hdec
    rw [usgK1_some_zero hz] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
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
    obtain ⟨⟨b, mp'⟩, a', hr2, hb, hM2, hS2, hg2⟩ :=
      hbGoOK n m1 a1 CWF 0 (rs.tail.tail.tail.headD 0) mp hS1 hbH hM1 _ _ h
    refine ⟨b, mp', a', ?_, hb, hM2, hS2, hg1.trans hg2⟩
    rw [show (0 : Word).toNat = 0 from rfl, decE_eq, hbe, CWF_eq] at hr2
    simp only [structUsedLaterGo, StateT.run_bind, hrun, except_ok_bind]
    exact hr2

theorem ustW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat)
    (m m' : Mem) (a : AState) (cty nP j r : Word) (mp : Std.HashMap (EIdx × Nat) Bool)
    (hsum : nP.toNat + j.toNat + 1 < 2 ^ 64) (hc : H cty)
    (hS : StageR dn vis fe m a) (hM : hbMR m mp) (h : ustW n m cty nP j = some (r, m')) :
    ∃ b a', (structUsedLater (decI cty) nP.toNat j.toNat).run a = .ok (b, a') ∧
      r = (if b then 1 else 0) ∧ (∃ mp1, hbMR m' mp1) ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  simp only [ustW] at h
  obtain ⟨rs, m1, hst, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  obtain ⟨x, a1, hrun, hS1, hg1, hdec⟩ := stripF_pis_ok dn vis fe (nP + j + 1) cty hc m m1 a rs hst hS
  have hM1 : hbMR m1 mp := memoRV_frame hbSch hbSch_wf lfKey hbVR [IW] [200] (by simp [hbSch, HBM, IW])
    (by simp [hbSch]) m m1 (stripF_frame hst) (fun _ _ h => h) mp hM
  rw [add3_toNat hsum] at hrun
  cases x with
  | none =>
    have hz : rs.headD 0 = 0 := hdec
    rw [ustK1_some_zero hz] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
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
      hbFastW_ok n m1 m' a1 0 (rs.tail.tail.tail.headD 0) r mp hbH hS1 hM1 h
    refine ⟨b, a', ?_, hb, hM2, hS2, hg1.trans hg2⟩
    rw [show (0 : Word).toNat = 0 from rfl, decE_eq, hbe] at hr2
    simp only [structUsedLater, StateT.run_bind, hrun, except_ok_bind]
    exact hr2

/-! ## The census theorems -/

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p) (hst : StripProg p)

include hv hf hput hins hgo hbp hst in
/-- **`struct_used_later_go` refines `structUsedLaterGo`** (through the stubs `strip_pis`, `bvar_b`),
sharing the caller's `hb` memo. -/
@[refines ConRon.Arena.structUsedLaterGo]
theorem structUsedLaterGo_refines (hp : p.lookup "struct_used_later_go" = some structUsedLaterGoL)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis cty nP j : Word)
    (mp : Std.HashMap (EIdx × Nat) Bool)
    (hsum : nP.toNat + j.toNat + 1 < 2 ^ 64) (hc : H cty) (hS : StageR dn vis fe s₀.mem a₀)
    (hM : hbMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_used_later_go" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (structUsedLaterGo mp (decI cty) nP.toNat j.toNat) a₀ ∧
      r.headD 0 = (if (AM.res (structUsedLaterGo mp (decI cty) nP.toNat j.toNat) a₀).1 then 1 else 0) ∧
      hbMR s'.mem (AM.res (structUsedLaterGo mp (decI cty) nP.toNat j.toNat) a₀).2 ∧
      StageR dn vis fe s'.mem (AM.st (structUsedLaterGo mp (decI cty) nP.toNat j.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (structUsedLaterGo_spec p hv hf hput hins hgo hbp hst hp n s₀ cty nP j) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, mp', a', hrun, hb, hM', hS', hg⟩ := usgW_ok n _ _ a₀ cty nP j _ mp hsum hc hS hM hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hb, by rw [hres]; exact hM', by rw [hst]; exact hS', hg⟩

include hv hf hput hins hgo hbp hst in
/-- **`struct_used_later` refines `structUsedLater`** (through `strip_pis`, `bvar_b`): clears the `hb`
memo and walks. -/
@[refines ConRon.Arena.structUsedLater]
theorem structUsedLater_refines (hcl : p.lookup "hb_clear" = some (memoClearG hbSch))
    (hfast : p.lookup "has_loose_b_var_b_fast" = some hasLooseBVarBFastL)
    (hp : p.lookup "struct_used_later" = some structUsedLaterL)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis cty nP j : Word)
    (mp : Std.HashMap (EIdx × Nat) Bool)
    (hsum : nP.toNat + j.toNat + 1 < 2 ^ 64) (hc : H cty) (hS : StageR dn vis fe s₀.mem a₀)
    (hM : hbMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "struct_used_later" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (structUsedLater (decI cty) nP.toNat j.toNat) a₀ ∧
      r.headD 0 = (if AM.res (structUsedLater (decI cty) nP.toNat j.toNat) a₀ then 1 else 0) ∧
      (∃ mp1, hbMR s'.mem mp1) ∧
      StageR dn vis fe s'.mem (AM.st (structUsedLater (decI cty) nP.toNat j.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (structUsedLater_spec p hv hf hput hins hgo hbp hst hcl hfast hp n s₀ cty nP j) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hb, hM', hS', hg⟩ := ustW_ok n _ _ a₀ cty nP j _ mp hsum hc hS hM hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hb, hM', by rw [hst]; exact hS', hg⟩

end census

/-! ## `struct_used_later_list`: the word model -/

/-- `usgW` at the callee's own exec fuel (zero: the call cannot return). -/
def usg0 : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, cty, nP, j => usgW n m cty nP j

/-- The empty slice. -/
def ulK0 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m1) => some ([q, 0], m1)
/-- After the cons. -/
def ulK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m3) => some ([rc.headD 0, rc.tail.headD 0], m3)
/-- After the recursion: the cons. -/
def ulK2 (k : Nat) (r : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m2) => ulK3 (consW k m2 r (rr.headD 0) (rr.tail.headD 0))

mutual
def ulW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, cty, nP, n, base =>
    if n = 0 then ulK0 (allocW m 0) else ulK1 k cty nP n base (usg0 k m cty nP base)
/-- After `struct_used_later_go`: the recursion. -/
def ulK1 (k : Nat) (cty nP n base : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => ulK2 k r (ulW k m1 cty nP (n - 1) (base + 1))
end

section ulArms
variable (k : Nat) (m m1 m2 : Mem) (cty nP n base r q : Word) (rr : List Word)
theorem ulW_zero (hn : n = 0) : ulW (k + 1) m cty nP n base = ulK0 (allocW m 0) := by simp [ulW, hn]
theorem ulW_succ (hn : n ≠ 0) :
    ulW (k + 1) m cty nP n base = ulK1 k cty nP n base (usg0 k m cty nP base) := by simp [ulW, hn]
theorem ulK0_some : ulK0 (some (q, m1)) = some ([q, 0], m1) := rfl
theorem ulK1_some : ulK1 k cty nP n base (some (r, m1)) = ulK2 k r (ulW k m1 cty nP (n - 1) (base + 1)) := by
  rw [ulK1]
theorem ulK2_some : ulK2 k r (some (rr, m2)) = ulK3 (consW k m2 r (rr.headD 0) (rr.tail.headD 0)) := rfl
theorem ulK3_some (rc : List Word) : ulK3 (some (rc, m2)) = some ([rc.headD 0, rc.tail.headD 0], m2) := rfl
end ulArms

grind_pattern [ind_grind] ulW_zero => ulW (k + 1) m cty nP n base
grind_pattern [ind_grind] ulW_succ => ulW (k + 1) m cty nP n base
grind_pattern [ind_grind] ulK0_some => ulK0 (some (q, m1))
grind_pattern [ind_grind] ulK1_some => ulK1 k cty nP n base (some (r, m1))
grind_pattern [ind_grind] ulK2_some => ulK2 k r (some (rr, m2))
grind_pattern [ind_grind] ulK3_some => ulK3 (some (rc, m2))

section ulspec
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p) (hst : StripProg p)
  (hsg : p.lookup "struct_used_later_go" = some structUsedLaterGoL)
  (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hp : p.lookup "struct_used_later_list" = some structUsedLaterListL)

include hv hf hput hins hgo hbp hst hsg in
theorem structUsedLaterGo_spec0 (n : Nat) (s₀ : St) (cty nP j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_used_later_go" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧ usg0 n s₀.mem cty nP j = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases n with
  | zero =>
    rw [invoke_eq _ hsg]; simp only [callFn, structUsedLaterGoL]; vcgen [exec] <;> grind
  | succ n => exact structUsedLaterGo_spec p hv hf hput hins hgo hbp hst hsg n s₀ cty nP j

include hv hf hput hins hgo hbp hst hsg ha hc hsc hp in
theorem ulW_spec (n : Nat) : ∀ (s₀ : St) (cty nP m base : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_used_later_list" [cty, nP, m, base]
    ⦃fun r s' => LocEq s' s₀ ∧ ulW n s₀.mem cty nP m base = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ cty nP m base; rw [invoke_eq _ hp]; simp only [callFn, structUsedLaterListL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ cty nP m base
    rw [invoke_eq _ hp]
    simp only [callFn, structUsedLaterListL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        structUsedLaterGo_spec0 p hv hf hput hins hgo hbp hst hsg n, iwAlloc_specW p ha n,
        slCons_specW p ha hc hsc n, ih] <;> finish (gen := 20)

end ulspec

theorem ulW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (cty nP n base : Word) (r : List Word)
      (mp : Std.HashMap (EIdx × Nat) Bool),
    nP.toNat + base.toNat + n.toNat + 1 < 2 ^ 64 → H cty →
    StageR dn vis fe m a → hbMR m mp → ulW k m cty nP n base = some (r, m') →
    ∃ bs mp' a', (structUsedLaterList (decI cty) nP.toNat mp n.toNat base.toNat).run a = .ok (bs, a') ∧
      decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (bnums bs) ∧ r.tail.headD 0 = n ∧
      (r.headD 0).toNat + n.toNat = iwTop m' ∧ hbMR m' mp' ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  induction k with
  | zero => intro m m' a cty nP n base r mp _ _ _ _ h; simp [ulW] at h
  | succ k ih =>
    intro m m' a cty nP n base r mp hb hc hS hM h
    by_cases hn0 : n = 0
    · rw [ulW_zero k m cty nP n base hn0] at h
      obtain ⟨q, m1, hal, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [ulK0_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS1, hg1, hq, htop⟩ := allocW_stage hal hS
      obtain ⟨hI1, hE1, hsz, hEs, hc200⟩ := hS.2
      obtain ⟨rfl, rfl, -⟩ := allocW_facts hal hsz
      have hM1 : hbMR (allocMem m 0) mp :=
        memoRV_frame hbSch hbSch_wf lfKey hbVR [IW] [200] (by simp [IW, HBM, hbSch]) (by simp [hbSch])
          m _ (allocMem_frame m 0) (fun _ _ h => h) mp hM
      subst hn0
      refine ⟨[], mp, a, ?_, ?_, rfl, ?_, hM1, hS1, hg1⟩
      · simp [structUsedLaterList]; rfl
      · simp [decNL, bnums]
      · simp only [List.headD_cons]; rw [htop, ← hq]
    · rw [ulW_succ k m cty nP n base hn0] at h
      have hn1 : (n - 1).toNat = n.toNat - 1 := by
        have : 1 ≤ n.toNat := by
          rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
          · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hn0
          · omega
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using this))]; simp
      have hb1 : (base + 1).toNat = base.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hnn : n.toNat = (n.toNat - 1) + 1 := by
        have : n.toNat ≠ 0 := fun h0 => hn0 (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      cases k with
      | zero => simp [usg0, ulK1] at h
      | succ k' =>
        have hu : usg0 (k' + 1) m cty nP base = usgW k' m cty nP base := rfl
        rw [hu] at h
        obtain ⟨rg, m1, hg, h⟩ := kSome_inv h (by simp [ulK1]) (fun _ _ => rfl)
        rw [ulK1_some] at h
        obtain ⟨b, mp1, a1, hrun1, hrg, hM1, hS1, hg1⟩ :=
          usgW_ok k' m m1 a cty nP base rg mp (by omega) hc hS hM hg
        obtain ⟨rr, m2, hl, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
        rw [ulK2_some] at h
        obtain ⟨bs, mp2, a2, hrun2, hdec, hlen, htop, hM2, hS2, hg2⟩ :=
          ih m1 m2 a1 cty nP (n - 1) (base + 1) rr mp1 (by rw [hn1, hb1]; omega) hc hS1 hM1 hl
        obtain ⟨rc, m3, hcw, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
        rw [ulK3_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hI2, hE2, hsz2, hEs2, hc2⟩ := hS2.2
        have hlen' : (rr.tail.headD 0).toNat = n.toNat - 1 := by rw [hlen, hn1]
        have hsrc : (rr.headD 0).toNat + (rr.tail.headD 0).toNat ≤ iwTop m2 := by
          rw [hlen', ← hn1]; exact Nat.le_of_eq htop
        rw [hn1, hb1] at hrun2
        obtain ⟨hrc, -, -, hfr3, -, -⟩ := consW_decN hcw hsz2 hc2 hsrc hdec
        obtain ⟨hS3, hg3, hdec3, htop3⟩ := consW_stageN hcw hS2 hsrc hdec
        have hM3 : hbMR m3 mp2 :=
          memoRV_frame hbSch hbSch_wf lfKey hbVR [IW] [200] (by simp [IW, HBM, hbSch]) (by simp [hbSch])
            m2 m3 hfr3 (fun _ _ h => h) mp2 hM2
        have hlen3 : rc.tail.headD 0 = n := by
          rw [hrc]; simp only [List.tail_cons, List.headD_cons]
          rw [hlen]; simp
        refine ⟨b :: bs, mp2, a2, ?_, ?_, ?_, ?_, hM3, hS3, hg1.trans (hg2.trans hg3)⟩
        · rw [hnn, structUsedLaterList.eq_2]
          simp only [StateT.run_bind, hrun1, except_ok_bind, hrun2]
          rfl
        · have hrt : rg.toNat = (if b then 1 else 0) := by rw [hrg]; cases b <;> rfl
          simp only [List.headD_cons, List.tail_cons]
          rw [hdec3, hrt]; rfl
        · simp only [List.headD_cons, List.tail_cons]; exact hlen3
        · rw [hlen3] at htop3; simpa only [List.headD_cons, List.tail_cons] using htop3

section ulCensus
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "hb_find" = some (memoFindG hbSch)) (hput : p.lookup "hb_put" = some (memoPutG hbSch))
  (hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL)
  (hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL) (hbp : BvbProg p) (hst : StripProg p)
  (hsg : p.lookup "struct_used_later_go" = some structUsedLaterGoL)
  (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hp : p.lookup "struct_used_later_list" = some structUsedLaterListL)
include hv hf hput hins hgo hbp hst hsg ha hc hsc hp

/-- **`struct_used_later_list` refines `structUsedLaterList`** (through `strip_pis`, `bvar_b`): the answers
as the `0`/`1` numbers of an `IW` slice, all through the caller's shared `hb` memo. -/
@[refines ConRon.Arena.structUsedLaterList]
theorem structUsedLaterList_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis cty nP cnt base : Word) (mp : Std.HashMap (EIdx × Nat) Bool)
    (hb : nP.toNat + base.toNat + cnt.toNat + 1 < 2 ^ 64) (hc' : H cty)
    (hS : StageR dn vis fe s₀.mem a₀) (hM : hbMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_used_later_list" [cty, nP, cnt, base]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (structUsedLaterList (decI cty) nP.toNat mp cnt.toNat base.toNat) a₀ ∧
      decNL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (bnums (AM.res (structUsedLaterList (decI cty) nP.toNat mp cnt.toNat base.toNat) a₀)) ∧
      r.tail.headD 0 = cnt ∧ (r.headD 0).toNat + cnt.toNat = iwTop s'.mem ∧
      (∃ mp1, hbMR s'.mem mp1) ∧
      StageR dn vis fe s'.mem (AM.st (structUsedLaterList (decI cty) nP.toNat mp cnt.toNat base.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (ulW_spec p hv hf hput hins hgo hbp hst hsg ha hc hsc hp n s₀ cty nP cnt base) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨bs, mp', a', hrun, hdec, hlen, htop, hM', hS', hg⟩ :=
    ulW_ok n _ _ a₀ cty nP cnt base r mp hb hc' hS hM hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hdec, hlen, htop, ⟨mp', hM'⟩, by rw [hst]; exact hS', hg⟩

end ulCensus

end L.Ind
end
