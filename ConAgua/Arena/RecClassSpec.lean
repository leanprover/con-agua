import ConAgua.Arena.IndSumSpec
import ConAgua.Arena.RecClass
import ConAgua.Arena.IndInstallSpec
import ConAgua.Arena.IndView

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
    simp only [ConRon.Arena.classOfMotiveVar, hle', ite_true, ← hsub, findIdx_toNat]
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
  · simp only [hi, ite_true] at h
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
  · simp only [hi, ite_false] at h
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

theorem ETables.getFVarIdx_of_get (t : ETables) (i : EIdx) (k : Nat) (ty : EIdx)
    (h : t.get i = some (.fvar k ty)) : t.getFVarIdx i = some k := by
  unfold ETables.get at h
  unfold ETables.getFVarIdx
  split at h
  · simp at h
  split at h
  · cases hn : t.fvars.node? i.idxNat <;> simp [hn] at h ⊢
    exact h.1
  all_goals (repeat' (first | (simp at h; done) | split at h))

theorem EStore.viewFVarIdx_of_view (st : EStore) (i : EIdx) (k : Nat) (ty : EIdx)
    (h : st.view i = some (.fvar k ty)) : st.viewFVarIdx i = some k := by
  unfold EStore.view at h
  unfold EStore.viewFVarIdx EStore.persGetFVarIdx
  split at h
  · simp only [*, ite_true]; exact ETables.getFVarIdx_of_get _ _ _ _ h
  · split at h
    · simp only [*, ite_true]; split <;> simp_all [ETables.getFVarIdx_of_get _ _ _ _ h]
    · simp at h

/-! ## `fvar_head` -/

/-- The word model of `fvar_head`. -/
def fvarHeadW (m : Mem) (e : Word) : Option (List Word × Mem) :=
  match stubM "get_app_fn" m [CWF, e] with
  | none => none
  | some (r, m1) =>
    if r.headD 0 >>> 28 = 1 then
      (if eViewW m1 (r.headD 0) = [] then none
       else some ([1, (eViewW m1 (r.headD 0)).tail.headD 0], m1))
    else some ([0, 0], m1)

theorem fvarHead_spec (p : Prog) (hp : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "fvar_head" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ fvarHeadW s₀.mem e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, fvarHead]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      stubM_spec p "get_app_fn" n, eView_spec p hv n] <;>
    finish [fvarHeadW]


theorem viewFVarIdx_run' (h : EIdx) (a : AState) :
    (ConRon.Arena.viewFVarIdx h).run a = .ok (a.store.viewFVarIdx h, a) := rfl

theorem eViewW_head1 (m : Mem) (w : Word) (hne : eViewW m w ≠ []) (hg : w >>> 28 = 1) :
    (eViewW m w).headD 0 = 1 := by
  unfold eViewW at hne ⊢
  simp (config := {decide := true}) only [hg, ite_true, ite_false] at hne ⊢
  by_cases c1 : 4294967295 < w
  · simp [c1] at hne
  by_cases c2 : tierW w ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [c1, c2] at hne
  by_cases c3 : rdW (m.arr64 CTL) (26 + tierW w) ≤ idxW w
  · simp [c1, c2, c3] at hne
  simp [c1, c2, c3]

theorem fvarHeadW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (e : Word) (he : H e) (r : List Word) (h : fvarHeadW m e = some (r, m'))
    (hS : StageR dn vis fe m a) :
    ∃ x a', (ConRon.Arena.fvarHead (decI e)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ r = (match x with | some i => [1, UInt64.ofNat i] | none => [0, 0]) := by
  simp only [fvarHeadW] at h
  cases hs : stubM "get_app_fn" m [CWF, e] with
  | none => rw [hs] at h; simp at h
  | some rm =>
    obtain ⟨r1, m1⟩ := rm
    rw [hs] at h
    simp only at h
    obtain ⟨t, a1, hrun1, hS1, hg1, hd1, hd2⟩ := getAppFn_spec dn vis fe CWF e he m m1 a r1 hs hS
    rw [CWF_eq] at hrun1
    generalize r1.headD 0 = w at hd1 hd2 h
    by_cases hf : w >>> 28 = 1
    · rw [if_pos hf] at h
      by_cases hne : eViewW m1 w = []
      · rw [if_pos hne] at h; simp at h
      rw [if_neg hne] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨v, hv, hR⟩ := eViewW_ok m1 a1 hS1.1.arena.1 w hne
      have htag : (decE w).tag = ETag.fvar := by
        rw [decE_tag w hd1, hf]; rfl
      cases v with
      | fvar k ty =>
        simp only [ViewR] at hR
        have hk := EStore.viewFVarIdx_of_view _ _ _ _ hv
        refine ⟨some k, a1, ?_, hS1, hg1, ?_⟩
        · simp only [ConRon.Arena.fvarHead]
          rw [StateT.run_bind, hrun1]
          simp only [bind, Except.bind]
          rw [← hd2]
          have : (decI w : EIdx) = decE w := rfl
          rw [this]
          simp only [htag, beq_self_eq_true, ite_true]
          have e1 : (ConRon.Arena.viewFVarIdx (decE w)).run a1 = .ok (some k, a1) := by
            rw [viewFVarIdx_run', hk]
          simp only [StateT.run] at e1 ⊢
          simp only [StateT.bind, e1, bind, Except.bind]
          rfl
        · have e2 : (eViewW m1 w).tail.headD 0 = (eViewW m1 w).getD 1 0 := by
            cases eViewW m1 w with
            | nil => simp
            | cons x xs => cases xs <;> simp
          simp only [e2, ← hR.2.1, UInt64.ofNat_toNat]
      | bvar i => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | sort u => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | const n us => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | app f x => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | lam f x => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | forallE f x => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | letE f x y => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | lit l => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | proj f x y => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
    · rw [if_neg hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have htag : ¬ (decE w).tag = ETag.fvar := by
        rw [decE_tag w hd1]
        intro hc
        apply hf
        have := congrArg UInt32.toNat hc
        simp [ETag.fvar] at this
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_shiftRight]
        simp
        omega
      refine ⟨none, a1, ?_, hS1, hg1, rfl⟩
      simp only [ConRon.Arena.fvarHead]
      rw [StateT.run_bind, hrun1]
      simp only [bind, Except.bind]
      rw [← hd2]
      have : (decI w : EIdx) = decE w := rfl
      rw [this]
      have htag' : ((decE w).tag == ETag.fvar) = false := by simpa using htag
      simp only [htag', Bool.false_eq_true, ite_false]
      rfl


/-- **`fvar_head` refines `fvarHead`** (through the `get_app_fn` stub and `e_view`). -/
@[refines ConRon.Arena.fvarHead]
theorem fvarHead_refines (p : Prog) (hp : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (e : Word) (he : H e)
    (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "fvar_head" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.fvarHead (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.fvarHead (decI e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      r = (match AM.res (ConRon.Arena.fvarHead (decI e)) a₀ with
        | some i => [1, UInt64.ofNat i] | none => [0, 0]); ⊤⦄ := by
  refine triple_post (fvarHead_spec p hp hv n s₀ e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hr⟩ := fvarHeadW_ok dn vis fe _ _ a₀ e he r hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.fvarHead (decI e)) a₀ a' x hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hr⟩


/-! ## `close_lams` -/

mutual
/-- **The model of `close_lams`.** -/
def closeLamsW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, bo, bl, i, body =>
    if bl = 0 then some ([body], m)
    else clK1 bo i (closeLamsW n m (bo + 1) (bl - 1) (i + 1) body)

/-- After the recursive call: `abstract1_fast`. -/
def clK1 (bo i : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => clK2 bo (stubM "abstract1_fast" m1 [CWF, r.headD 0, i, 0])

/-- After `abstract1_fast`: read the binder domain, `mk_lam`. -/
def clK2 (bo : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m2) =>
    if bo.toNat < (m2.arr64 IW).size then
      clK3 (stubM "mk_lam" m2 [rdW (m2.arr64 IW) bo, ra.headD 0])
    else none

/-- After `mk_lam`. -/
def clK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m3) => some ([rb.headD 0], m3)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (bo bl i body : Word) (r ra rb : List Word)
theorem closeLamsW_nil (h : bl = 0) : closeLamsW (n + 1) m bo bl i body = some ([body], m) := by
  simp [closeLamsW, h]
theorem closeLamsW_cons (h : bl ≠ 0) : closeLamsW (n + 1) m bo bl i body =
    clK1 bo i (closeLamsW n m (bo + 1) (bl - 1) (i + 1) body) := by
  simp [closeLamsW, h]
theorem clK1_some : clK1 bo i (some (r, m1)) =
    clK2 bo (stubM "abstract1_fast" m1 [CWF, r.headD 0, i, 0]) := rfl
theorem clK2_oob (h : ¬ bo.toNat < (m2.arr64 IW).size) : clK2 bo (some (ra, m2)) = none := by
  simp [clK2, h]
theorem clK2_ok (h : bo.toNat < (m2.arr64 IW).size) : clK2 bo (some (ra, m2)) =
    clK3 (stubM "mk_lam" m2 [rdW (m2.arr64 IW) bo, ra.headD 0]) := by
  simp [clK2, h]
theorem clK3_some : clK3 (some (rb, m3)) = some ([rb.headD 0], m3) := rfl
end arms

grind_pattern [ind_grind] closeLamsW_nil => closeLamsW (n + 1) m bo bl i body
grind_pattern [ind_grind] closeLamsW_cons => closeLamsW (n + 1) m bo bl i body
grind_pattern [ind_grind] clK1_some => clK1 bo i (some (r, m1))
grind_pattern [ind_grind] clK2_oob => clK2 bo (some (ra, m2))
grind_pattern [ind_grind] clK2_ok => clK2 bo (some (ra, m2))
grind_pattern [ind_grind] clK3_some => clK3 (some (rb, m3))

theorem closeLams_spec (p : Prog) (hp : p.lookup "close_lams" = some closeLams) (n : Nat) :
    ∀ (s₀ : St) (bo bl i body : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "close_lams" [bo, bl, i, body]
    ⦃fun r s' => LocEq s' s₀ ∧ closeLamsW n s₀.mem bo bl i body = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ bo bl i body; rw [invoke_eq _ hp]; simp only [callFn, closeLams]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ bo bl i body
    rw [invoke_eq _ hp]
    simp only [callFn, closeLams]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "abstract1_fast" n, stubM_spec p "mk_lam" n, ih] <;>
      finish (gen := 20)


theorem decHL_cons {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL m o (l + 1) = some xs) :
    ∃ x ys, xs = x :: ys ∧ decHL m (o + 1) l = some ys ∧ iwH m o = some x := by
  simp only [decHL, hslice?_succ] at h
  cases hx : (hd? (iwA m) o : Option (Idx k)) with
  | none => simp [hx] at h
  | some x =>
    cases hxs : (hslice? (iwA m) (o + 1) l : Option (List (Idx k))) with
    | none => simp [hx, hxs] at h
    | some ys =>
      simp [hx, hxs] at h
      exact ⟨x, ys, h.symm, hxs, hx⟩

theorem closeLamsW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (bo bl i body : Word) (bs : List EIdx) (r : List Word),
    closeLamsW n m bo bl i body = some (r, m') → StageR dn vis fe m a → H body →
    decHL m bo.toNat bl.toNat = some bs → bo.toNat + bl.toNat < 2 ^ 64 →
    bo.toNat + bl.toNat ≤ iwTop m → i.toNat + bl.toNat < 2 ^ 64 →
    ∃ x a', (ConRon.Arena.closeLams bs i.toNat (decI body)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = x := by
  induction n with
  | zero => intro m m' a bo bl i body bs r h; simp [closeLamsW] at h
  | succ n ih =>
    intro m m' a bo bl i body bs r h hS hb hbs hbo hbt hib
    by_cases hbl : bl = 0
    · rw [closeLamsW_nil n m bo bl i body hbl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hl0 : bl.toNat = 0 := by rw [hbl]; rfl
      rw [hl0] at hbs
      simp [decHL, hslice?] at hbs
      subst hbs
      exact ⟨decI body, a, rfl, hS, IWGrow.refl m, by simpa using hb, rfl⟩
    · rw [closeLamsW_cons n m bo bl i body hbl] at h
      have hlpos : 1 ≤ bl.toNat := by
        rcases Nat.eq_zero_or_pos bl.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hbl
        · omega
      obtain ⟨l1, hl1⟩ : ∃ l1, bl.toNat = l1 + 1 := ⟨bl.toNat - 1, by omega⟩
      rw [hl1] at hbs
      obtain ⟨dom, rest, rfl, hrest, hdom⟩ := decHL_cons hbs
      have hbl1 : (bl - 1).toNat = l1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hlpos))]; simp; omega
      have hbo1 : (bo + 1).toNat = bo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      cases hr : closeLamsW n m (bo + 1) (bl - 1) (i + 1) body with
      | none => rw [hr] at h; simp [clK1] at h
      | some rm =>
        obtain ⟨r1, m1⟩ := rm
        rw [hr, clK1_some] at h
        obtain ⟨x1, a1, hrun1, hS1, hg1, hd11, hd12⟩ := ih m m1 a (bo + 1) (bl - 1) (i + 1) body rest r1 hr hS hb
          (by rw [hbo1, hbl1]; exact hrest) (by omega) (by omega) (by omega)
        cases ha : stubM "abstract1_fast" m1 [CWF, r1.headD 0, i, 0] with
        | none => rw [ha] at h; simp [clK2] at h
        | some ram =>
          obtain ⟨ra, m2⟩ := ram
          rw [ha] at h
          obtain ⟨x2, a2, hrun2, hS2, hg2, hd21, hd22⟩ :=
            abstract1Fast_spec dn vis fe CWF (r1.headD 0) i 0 hd11 m1 m2 a1 ra ha hS1
          by_cases hoob : bo.toNat < (m2.arr64 IW).size
          · rw [clK2_ok m2 bo ra hoob] at h
            obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW hdom (by omega)
            rw [UInt64.ofNat_toNat] at hw1
            have hrd : rdW (m2.arr64 IW) bo = w := by
              have hg := hg1.trans hg2
              have := hg.2.2.1 bo.toNat (by omega)
              simp only [rdW] at this hw1 ⊢
              have e : (m2.arr64 IW)[bo.toNat]? = (m.arr64 IW)[bo.toNat]? := this
              rw [e]; exact hw1
            rw [hrd] at h
            cases hm : stubM "mk_lam" m2 [w, ra.headD 0] with
            | none => rw [hm] at h; simp [clK3] at h
            | some rbm =>
              obtain ⟨rb, m3⟩ := rbm
              rw [hm, clK3_some] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨x3, a3, hrun3, hS3, hg3, hd31, hd32⟩ :=
                recMkLam_spec dn vis fe w (ra.headD 0) hw2 hd21 m2 m3 a2 rb hm hS2
              refine ⟨x3, a3, ?_, hS3, (hg1.trans hg2).trans hg3, by simpa using hd31, by simpa using hd32⟩
              rw [CWF_eq] at hrun2
              have hz : (0 : Word).toNat = 0 := rfl
              rw [hz] at hrun2
              rw [hi1] at hrun1
              simp only [ConRon.Arena.closeLams, StateT.run_bind]
              rw [hrun1]
              simp only [bind, Except.bind]
              rw [← hd12, hrun2]
              simp only [bind, Except.bind]
              rw [← hw3, ← hd22]
              exact hrun3
          · rw [clK2_oob m2 bo ra hoob] at h; simp at h


/-- **`close_lams` refines `closeLams`** (through the `abstract1_fast` and `mk_lam` stubs). -/
@[refines ConRon.Arena.closeLams]
theorem closeLams_refines (p : Prog) (hp : p.lookup "close_lams" = some closeLams) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (bo bl i body : Word) (bs : List EIdx) (hS : StageR dn vis fe s₀.mem a₀) (hb : H body)
    (hbs : decHL s₀.mem bo.toNat bl.toNat = some bs) (hbo : bo.toNat + bl.toNat < 2 ^ 64)
    (hbt : bo.toNat + bl.toNat ≤ iwTop s₀.mem) (hib : i.toNat + bl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "close_lams" [bo, bl, i, body]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.closeLams bs i.toNat (decI body)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.closeLams bs i.toNat (decI body)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = AM.res (ConRon.Arena.closeLams bs i.toNat (decI body)) a₀; ⊤⦄ := by
  refine triple_post (closeLams_spec p hp n s₀ bo bl i body) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, h1, h2⟩ := closeLamsW_ok dn vis fe n _ _ a₀ bo bl i body bs r hm hS hb
    hbs hbo hbt hib
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.closeLams bs i.toNat (decI body)) a₀ a' x hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, h1, by rw [hres]; exact h2⟩

end L.Ind
