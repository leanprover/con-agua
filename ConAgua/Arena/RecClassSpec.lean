import ConAgua.Arena.IndSumSpec
import ConAgua.Arena.RecClass
import ConAgua.Arena.IndInstallSpec

/-!
# Refinements of `RecClass` (lane `induct`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem decNL_succ (m : Mem) (off n : Nat) :
    decNL m off (n + 1) = (do
      let x ← iwN m off
      let xs ← decNL m (off + 1) n
      pure (x :: xs)) := by
  simp only [decNL, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range n))
  funext j
  simp only [Function.comp]
  congr 1
  omega

/-- **A decoding `IW` number slice is an `SlR` slice** of the numbers' words. -/
theorem slR_of_decNL (m : Mem) : ∀ (n off : Nat) (ns : List Nat),
    decNL m off n = some ns → off + n < 2 ^ 64 →
    ∃ ws, SlR m (UInt64.ofNat off) (UInt64.ofNat n) ws ∧ ns = ws.map UInt64.toNat := by
  intro n
  induction n with
  | zero =>
    intro off ns h _
    simp [decNL] at h
    exact ⟨[], by simpa using (SlR.nil (m := m) (o := UInt64.ofNat off)), by simp [h]⟩
  | succ n ih =>
    intro off ns h hb
    rw [decNL_succ] at h
    cases hx : iwN m off with
    | none => simp [hx] at h
    | some x =>
      cases hxs : decNL m (off + 1) n with
      | none => simp [hx, hxs] at h
      | some xs =>
        simp [hx, hxs] at h
        subst h
        obtain ⟨ws, hws, rfl⟩ := ih (off + 1) xs hxs (by omega)
        obtain ⟨e1, -⟩ := iwN_rdW hx (by omega)
        refine ⟨UInt64.ofNat x :: ws, ?_, ?_⟩
        · have e2 : UInt64.ofNat off + 1 = UInt64.ofNat (off + 1) := by simp [UInt64.ofNat_add]
          have e3 : UInt64.ofNat (n + 1) - 1 = UInt64.ofNat n := by simp [UInt64.ofNat_add]
          have hne : UInt64.ofNat (n + 1) ≠ 0 := by
            intro h0; have := congrArg UInt64.toNat h0; simp at this; omega
          rw [← e1]
          exact SlR.cons hne (by rw [e2, e3]; exact hws)
        · have := (iwN_rdW hx (by omega)).2
          simp; omega

/-! ## `class_of_motive_var` -/

theorem findIdx_toNat (ws : List Word) (x : Word) :
    (ws.map UInt64.toNat).findIdx? (· == x.toNat) = ws.findIdx? (· == x) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.findIdx?_cons, beq_iff_eq]
    have : (w.toNat = x.toNat) ↔ w = x := ⟨fun h => UInt64.toNat_inj.mp h, fun h => h ▸ rfl⟩
    by_cases h : w = x
    · simp [h]
    · simp [h, this, ih]

/-- **`class_of_motive_var` refines `classOfMotiveVar`**: `(1, i)` for `some i`, `(0, 0)` for
`none`; memory unchanged. -/
@[refines ConRon.Arena.classOfMotiveVar]
theorem classOfMotiveVar_refines (p : Prog) (hf : p.lookup "sl_find" = some slFind)
    (hp : p.lookup "class_of_motive_var" = some classOfMotiveVar) (n : Nat) (s₀ : St)
    (nP o l pv : Word) (ns : List Nat) (hd : decNL s₀.mem o.toNat l.toNat = some ns)
    (hb : o.toNat + l.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_of_motive_var" [nP, o, l, pv]
    ⦃fun r s' => s'.mem = s₀.mem ∧
      r = match ConRon.Arena.classOfMotiveVar nP.toNat ns pv.toNat with
        | some i => [1, UInt64.ofNat i]
        | none => [0, 0]; ⊤⦄ := by
  obtain ⟨ws, hws, rfl⟩ := slR_of_decNL s₀.mem _ _ _ hd hb
  simp only [UInt64.ofNat_toNat] at hws
  have hlen : ws.length < 2 ^ 64 := by
    have := decNL_length s₀.mem hd; simp at this; omega
  have key : ∀ r, findW n s₀.mem o l (pv - nP) = some r → nP ≤ pv →
      r = match ConRon.Arena.classOfMotiveVar nP.toNat (ws.map UInt64.toNat) pv.toNat with
        | some i => [1, UInt64.ofNat i]
        | none => [0, 0] := by
    intro r hr hle
    have hle' : nP.toNat ≤ pv.toNat := UInt64.le_iff_toNat_le.mp hle
    have hsub : (pv - nP).toNat = pv.toNat - nP.toNat := UInt64.toNat_sub_of_le _ _ hle
    rw [findW_ok n _ _ _ _ _ _ hws hr hlen]
    simp only [ConRon.Arena.classOfMotiveVar, hle', if_true, ← hsub, findIdx_toNat]
    cases List.findIdx? (fun x => x == pv - nP) ws <;> rfl
  have key2 : pv < nP →
      ConRon.Arena.classOfMotiveVar nP.toNat (ws.map UInt64.toNat) pv.toNat = none := by
    intro h
    have : ¬ nP.toNat ≤ pv.toNat := by have := UInt64.lt_iff_toNat_lt.mp h; omega
    simp [ConRon.Arena.classOfMotiveVar, this]
  rw [invoke_eq _ hp]
  simp only [callFn, classOfMotiveVar]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, slFind_spec p hf n] <;>
    finish


/-! ## `class_binder`, `class_gen_binder`: one `fvar_type_d` call (through the stub) -/

/-- The word model of a one-call wrapper of `fvar_type_d`. -/
def fvarTypeDW1 (m : Mem) (x : Word) : Option (List Word × Mem) :=
  match stubM "fvar_type_d" m [x] with
  | none => none
  | some (r, m') => some ([r.headD 0], m')

theorem classBinder_spec (p : Prog) (hp : p.lookup "class_binder" = some classBinder) (n : Nat)
    (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_binder" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ fvarTypeDW1 s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classBinder]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, stubM_spec p "fvar_type_d" n] <;>
    finish [fvarTypeDW1]

theorem classGenBinder_spec (p : Prog) (hp : p.lookup "class_gen_binder" = some classGenBinder)
    (n : Nat) (s₀ : St) (g x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_gen_binder" [g, x]
    ⦃fun r s' => LocEq s' s₀ ∧ fvarTypeDW1 s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classGenBinder]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, stubM_spec p "fvar_type_d" n] <;>
    finish [fvarTypeDW1]

/-- The relational lemma of `fvarTypeDW1`. -/
theorem fvarTypeDW1_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (x : Word) (hx : H x) (r : List Word) (h : fvarTypeDW1 m x = some (r, m'))
    (hS : StageR dn vis fe m a) :
    ∃ t a', (fvarTypeD (decI x)).run a = .ok (t, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = t := by
  simp only [fvarTypeDW1] at h
  cases hs : stubM "fvar_type_d" m [x] with
  | none => rw [hs] at h; simp at h
  | some rm =>
    obtain ⟨r1, m1⟩ := rm
    rw [hs] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨t, a', hrun, hS', hg, hd1, hd2⟩ := fvarTypeD_spec dn vis fe x hx m m1 a r1 hs hS
    exact ⟨t, a', hrun, hS', hg, hd1, by simpa using hd2⟩

/-- **`class_binder` refines `classBinder`** (through the `fvar_type_d` stub). -/
@[refines ConRon.Arena.classBinder]
theorem classBinder_refines (p : Prog) (hp : p.lookup "class_binder" = some classBinder) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (x : Word)
    (hx : H x) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_binder" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classBinder (decI x)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classBinder (decI x)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = AM.res (ConRon.Arena.classBinder (decI x)) a₀; ⊤⦄ := by
  refine triple_post (classBinder_spec p hp n s₀ x) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨t, a', hrun, hS', hg, h1, h2⟩ := fvarTypeDW1_ok dn vis fe _ _ a₀ x hx r hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.classBinder (decI x)) a₀ a' t hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, h1, by rw [hres]; exact h2⟩

/-- **`class_gen_binder` refines `ClassGen.binder`** (through the `fvar_type_d` stub). -/
@[refines ConRon.Arena.ClassGen.binder]
theorem classGenBinder_refines (p : Prog) (hp : p.lookup "class_gen_binder" = some classGenBinder)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (G : ClassGen) (g x : Word) (hx : H x) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_gen_binder" [g, x]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.binder G (decI x)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.ClassGen.binder G (decI x)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = AM.res (ConRon.Arena.ClassGen.binder G (decI x)) a₀; ⊤⦄ := by
  refine triple_post (classGenBinder_spec p hp n s₀ g x) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨t, a', hrun, hS', hg, h1, h2⟩ := fvarTypeDW1_ok dn vis fe _ _ a₀ x hx r hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.ClassGen.binder G (decI x)) a₀ a' t hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, h1, by rw [hres]; exact h2⟩


/-! ## `expr_get_d` -/

/-- The word model of `expr_get_d`. -/
def exprGetDW (m : Mem) (o l i : Word) : Option (List Word × Mem) :=
  if i < l then
    (if (o + i).toNat < (m.arr64 IW).size then some ([rdW (m.arr64 IW) (o + i)], m) else none)
  else
    match stubM "intern_bvar" m [0] with
    | none => none
    | some (r, m') => some ([r.headD 0], m')

theorem exprGetD_spec (p : Prog) (hp : p.lookup "expr_get_d" = some exprGetD) (n : Nat) (s₀ : St)
    (o l i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "expr_get_d" [o, l, i]
    ⦃fun r s' => LocEq s' s₀ ∧ exprGetDW s₀.mem o l i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, exprGetD]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      stubM_spec p "intern_bvar" n] <;>
    finish [exprGetDW]

theorem exprGetDW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (o l i : Word) (xs : List EIdx) (r : List Word)
    (h : exprGetDW m o l i = some (r, m')) (hS : StageR dn vis fe m a)
    (hxs : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat < 2 ^ 64) :
    ∃ x a', (ConRon.Arena.exprGetD xs i.toNat).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = x := by
  simp only [exprGetDW] at h
  by_cases hi : i < l
  · simp only [hi, if_true] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hit : i.toNat < l.toNat := UInt64.lt_iff_toNat_lt.mp hi
      obtain ⟨w, hw1, hw2, hw3⟩ := decHL_get' hxs i.toNat hit hb
      have hoi : o + i = UInt64.ofNat (o.toNat + i.toNat) := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
      refine ⟨xs[i.toNat]'(by rw [decHL_length m hxs]; exact hit), a, ?_, hS, IWGrow.refl m, ?_, ?_⟩
      · simp [ConRon.Arena.exprGetD, hit, decHL_length m hxs]; rfl
      · simp only [List.headD_cons]; rw [hoi, hw1]; exact hw2
      · simp only [List.headD_cons]; rw [hoi, hw1]; exact hw3.symm
    · simp at h
  · simp only [hi, if_false] at h
    cases hs : stubM "intern_bvar" m [0] with
    | none => rw [hs] at h; simp at h
    | some rm =>
      obtain ⟨r1, m1⟩ := rm
      rw [hs] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨x, a', hrun, hS', hg, hd1, hd2⟩ := recInternBVar_spec dn vis fe 0 m m1 a r1 hs hS
      have hge : l.toNat ≤ i.toNat := by
        have : ¬ i.toNat < l.toNat := fun h => hi (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      refine ⟨x, a', ?_, hS', hg, hd1, by simpa using hd2⟩
      have hn : xs[i.toNat]? = none := by
        rw [List.getElem?_eq_none_iff, decHL_length m hxs]; exact hge
      simp only [ConRon.Arena.exprGetD, hn]
      exact hrun

/-- **`expr_get_d` refines `exprGetD`** (through the `intern_bvar` master stub). -/
@[refines ConRon.Arena.exprGetD]
theorem exprGetD_refines (p : Prog) (hp : p.lookup "expr_get_d" = some exprGetD) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (o l i : Word) (xs : List EIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hxs : decHL s₀.mem o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "expr_get_d" [o, l, i]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.exprGetD xs i.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.exprGetD xs i.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = AM.res (ConRon.Arena.exprGetD xs i.toNat) a₀; ⊤⦄ := by
  refine triple_post (exprGetD_spec p hp n s₀ o l i) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, h1, h2⟩ := exprGetDW_ok dn vis fe _ _ a₀ o l i xs r hm hS hxs hb
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.exprGetD xs i.toNat) a₀ a' x hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, h1, by rw [hres]; exact h2⟩

end L.Ind
