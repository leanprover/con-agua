import ConAgua.Arena.RecCheckSpec3
import ConAgua.Arena.IndPosSpec2A
import ConAgua.Arena.IndSim
import ConAgua.Arena.RecClassSpecD

/-!
# `RecClass`: `ClassGen.major` (lane `indproofs2`, helper `rec2`)

The class generator `g` is taken decoded below the tops (`DecB` of `decCG`), so every field and
every slice it names is stable across the callees. A slice decoded below the tops may still be
empty at an offset above the top; `rec2InstW_ok` and `rec2AppendW_norm` handle that case (an empty
slice's offset is never read).
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Reading below the tops -/

theorem rec2IwN_trunc {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) :
    i < iwTop m ∧ iwN m i = some v := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨hi, by simp [iwN, nat?, hw']⟩

theorem rec2IwH_trunc {k : IdxKind} {m : Mem} {i : Nat} {x : Idx k} (h : iwH (truncM m) i = some x) :
    i < iwTop m ∧ iwH m i = some x := by
  obtain ⟨w, hw, hl, hx⟩ := hd?_some h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  refine ⟨hi, ?_⟩
  simp only [iwH, hd?, iwA] at hw' ⊢
  simp [hw', hl, hx]

/-- A non-empty handle slice decoded below the tops lies below the top. -/
theorem rec2DecB_HL_top {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : DecB (fun m => (decHL m o l : Option (List (Idx k)))) m xs) (hl : l ≠ 0) : o + l ≤ iwTop m := by
  have := decHL_getI h (l - 1) (by omega)
  have := (rec2IwH_trunc this).1
  omega

theorem rec2DecB_HL_stab {k : IdxKind} {m m' : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : DecB (fun m => (decHL m o l : Option (List (Idx k)))) m xs) (hg : IWGrow m m') :
    decHL m' o l = some xs :=
  h.stab (OMono.decHL o l) m' hg

/-- The fields of a class generator decoded below the tops. -/
theorem rec2CG_parts {m : Mem} {g : Nat} {G : ClassGen} (h : DecB (fun m => decCG m g) m G) :
    iwN m g = some G.nP ∧ g + 13 < iwTop m ∧
    (∃ o l, iwN m (g + 3) = some o ∧ iwN m (g + 4) = some l ∧
      DecB (fun m => decPL m (decTM m) o l) m G.cls) ∧
    (∃ o l, iwN m (g + 5) = some o ∧ iwN m (g + 6) = some l ∧
      DecB (fun m => (decHL m o l : Option (List EIdx))) m G.formerTys) ∧
    iwH m (g + 11) = some G.elim ∧
    (∃ o l, iwN m (g + 12) = some o ∧ iwN m (g + 13) = some l ∧
      DecB (fun m => (decHL m o l : Option (List EIdx))) m G.pre) := by
  have h' : decCG (truncM m) g = some G := h
  simp only [decCG, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h'
  obtain ⟨nP, hnP, ps, hps, cls, hcls, ft, hft, sl, hsl, cts, hcts, el, hel, pre, hpre, rfl⟩ := h'
  obtain ⟨o3, l3, h3, h4, hc⟩ := decAt_some hcls
  obtain ⟨o5, l5, h5, h6, hf⟩ := decAt_some hft
  obtain ⟨o12, l12, h12, h13, hp⟩ := decAt_some hpre
  refine ⟨(rec2IwN_trunc hnP).2, (rec2IwN_trunc h13).1, ⟨o3, l3, (rec2IwN_trunc h3).2,
    (rec2IwN_trunc h4).2, hc⟩, ⟨o5, l5, (rec2IwN_trunc h5).2, (rec2IwN_trunc h6).2, hf⟩,
    (rec2IwH_trunc hel).2, ⟨o12, l12, (rec2IwN_trunc h12).2, (rec2IwN_trunc h13).2, hp⟩⟩

theorem rec2DecTM_parts {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    iwH m p = some M.ind ∧ iwH m (p + 1) = some M.lvls ∧
    (∃ o l, iwN m (p + 2) = some o ∧ iwN m (p + 3) = some l ∧ decHL m o l = some M.ds) ∧
    iwN m (p + 4) = some M.nPc ∧ iwN m (p + 5) = some M.nIdx := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨w5, h5, a1, ha1, ds, hds, w4, h4, w3, h3, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h
  exact ⟨h5, ha1, decAt_some hds, h4, h3⟩

/-! ## `target_major_at`, its `ds` slice decoded below the tops -/

theorem rec2TMD_ds {a a' : AState} {tm : TargetMajor}
    (h : ConRon.Arena.targetMajorDefault.run a = .ok (tm, a')) : tm.ds = [] := by
  simp only [ConRon.Arena.targetMajorDefault, StateT.run_bind] at h
  cases h1 : (internNNode .anonymous).run a with
  | error e => rw [h1] at h; cases h
  | ok p =>
    rw [h1, except_ok_bind] at h
    cases h2 : StateT.run pinEmptyLevels p.snd with
    | error e => rw [h2] at h; cases h
    | ok q =>
      rw [h2, except_ok_bind] at h
      injection h with h'
      injection h' with e1 e2
      rw [← e1]

/-- `target_major_at`'s record: decoded, its `ds` slice decoded below the tops. -/
def TMR (m' : Mem) (q : Nat) (tm : TargetMajor) : Prop :=
  decTM m' q = some tm ∧
    ∀ o l, iwN m' (q + 2) = some o → iwN m' (q + 3) = some l →
      DecB (fun m => (decHL m o l : Option (List EIdx))) m' tm.ds

theorem rec2SimTMA (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (mo ml c : Word) (ms : List TargetMajor) (hS : StageR dn vis fe m a)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hb : mo.toNat + ml.toNat < 2 ^ 64) :
    RSim (tmaW n m mo ml c) (ConRon.Arena.targetMajorAt ms c.toNat) a
      (fun b a' tm => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ TMR b.2 (b.1.headD 0).toNat tm) := by
  have hms0 : decPL m (decTM m) mo.toNat ml.toNat = some ms :=
    hms.get (OMono.decPL (fun q => decTM_mono q) _ _)
  intro b hb'
  obtain ⟨tm, a', hrun, hS', hg, hd⟩ := tmaW_sim dn vis fe n m a mo ml c ms hS hms0 hb b hb'
  refine ⟨tm, a', hrun, hS', hg, hd, fun o l ho hl => ?_⟩
  rcases hc : ms[c.toNat]? with _ | x
  · have hrun' : ConRon.Arena.targetMajorDefault.run a = .ok (tm, a') := by
      simpa [ConRon.Arena.targetMajorAt, hc] using hrun
    rw [rec2TMD_ds hrun']
    obtain ⟨-, -, ⟨o', l', ho', hl', hds⟩, -⟩ := rec2DecTM_parts hd
    rw [ho] at ho'; rw [hl] at hl'; cases ho'; cases hl'
    rw [rec2TMD_ds hrun'] at hds
    have : l = 0 := by have := decHL_length _ hds; simp at this; omega
    subst this
    show decHL (truncM b.2) o 0 = some []
    simp [decHL, hslice?]
  have hrun' : (pure x : AM TargetMajor).run a = .ok (tm, a') := by
    simpa [ConRon.Arena.targetMajorAt, hc] using hrun
  have hx : x = tm := by injection hrun' with e; injection e
  subst hx
  have hct : c.toNat < ms.length := (List.getElem?_eq_some_iff.mp hc).1
  have hlen := decPL_length m hms0
  obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m) hms c.toNat (by omega)
  obtain ⟨hvt, hv'⟩ := rec2IwN_trunc hv
  have hxe : ms[c.toNat] = x := (List.getElem?_eq_some_iff.mp hc).2
  rw [hxe] at hdv
  obtain ⟨-, -, ⟨o', l', ho', hl', hds⟩, -⟩ := rec2DecTM_parts hdv
  -- the record pointer is the one the model returns
  have hq : (b.1.headD 0).toNat = v := by
    have := hdv; have hd0 := hd
    by_cases hcl : c < ml
    · cases n with
      | zero => simp [tmaW] at hb'
      | succ n =>
        rw [tmaW_hit n m mo ml c hcl] at hb'
        cases hb'
        have hrd := iwN_rdW_at (w := mo) (k := c.toNat) hv' hS.2.2.2.1
        have hcw : mo + UInt64.ofNat c.toNat = mo + c := by simp
        rw [hcw] at hrd
        simp only [List.headD_cons]; rw [hrd.1, UInt64.toNat_ofNat_of_lt' hrd.2]
    · exfalso; apply hcl; apply UInt64.lt_iff_toNat_lt.mpr; omega
  rw [hq] at ho hl
  have e1 : iwN b.2 (v + 2) = some o' := by
    rw [iwN_grow hg (rec2IwN_trunc ho').1]; exact (rec2IwN_trunc ho').2
  have e2 : iwN b.2 (v + 3) = some l' := by
    rw [iwN_grow hg (rec2IwN_trunc hl').1]; exact (rec2IwN_trunc hl').2
  rw [e1] at ho; rw [e2] at hl
  simp only [Option.some.injEq] at ho hl
  subst ho hl
  exact (show DecB (fun m => (decHL m o' l' : Option (List EIdx))) m x.ds from hds).grow
    (OMono.decHL _ _) hg

/-! ## Empty slices at any offset -/

/-- A slice that is empty or below the top. -/
theorem rec2DecB_HL_bound {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : DecB (fun m => (decHL m o l : Option (List (Idx k)))) m xs) (hS : (m.arr64 IW).size < 2 ^ 64)
    (ht : iwTop m ≤ (m.arr64 IW).size) (ho : o < 2 ^ 64) : o + l < 2 ^ 64 := by
  by_cases hl : l = 0
  · omega
  · have := rec2DecB_HL_top h hl; omega

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}

/-- `inst_pis_with` on a slice decoded below the tops (possibly empty, at any offset). -/
theorem rec2SimInstW (n : Nat) (hS : StageR dn vis fe m a) {ao al e : Word} (he : H e) {args : List EIdx}
    (hd : DecB (fun m => (decHL m ao.toNat al.toNat : Option (List EIdx))) m args) :
    RSim (instW n m ao al e) (ConRon.Arena.instPisWith args (decI e)) a (KP dn vis fe m decOE) := by
  rintro ⟨r, m'⟩ h
  have hd0 : decHL m ao.toNat al.toNat = some args := hd.get (OMono.decHL _ _)
  by_cases hal : al = 0
  · cases n with
    | zero => simp [instW] at h
    | succ n =>
    rw [instW_nil n m ao al e hal] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : args = [] := by
      have h0 : al.toNat = 0 := by rw [hal]; rfl
      rw [h0] at hd0; simpa [decHL, hslice?] using hd0.symm
    subst this
    exact ⟨some (decI e), a, rfl, hS, IWGrow.refl _, rfl, he, rfl⟩
  · have hl : al.toNat ≠ 0 := fun h0 => hal (UInt64.toNat_inj.mp (by simpa using h0))
    have ht := rec2DecB_HL_top hd hl
    obtain ⟨x, a', hrun, hS', hg, hout⟩ := instW_ok n dn fe vis m m' a ao al e args r h hS he hd0
      (hS.lt64 ht) ht
    exact ⟨x, a', hrun, hS', hg, hout⟩

end sims

theorem rec2AppendW_norm (n : Nat) (m : Mem) (o1 o2 l2 : Word) :
    appendW n m o1 0 o2 l2 = appendW n m 0 0 o2 l2 := by
  have hc : ∀ k m1 q (s : Word), copyW k m1 q s 0 = copyW k m1 q 0 0 := by
    intro k; cases k <;> simp [copyW]
  simp only [appendW, hc]

/-- `sl_append` of a slice decoded below the tops (possibly empty, at any offset) and a slice
below the top. -/
theorem rec2AppendW_dec {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o1 l1 o2 l2 : Word} {r : List Word} {xs ys : List EIdx}
    (h : appendW n m o1 l1 o2 l2 = some (r, m')) (hS : StageR dn vis fe m a)
    (h1 : DecB (fun m => (decHL m o1.toNat l1.toNat : Option (List EIdx))) m xs)
    (h2 : decHL m o2.toNat l2.toNat = some ys) (hb2 : o2.toNat + l2.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (xs ++ ys) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  have hx0 : decHL m o1.toNat l1.toNat = some xs := h1.get (OMono.decHL _ _)
  have key : ∀ o1' : Word, appendW n m o1' l1 o2 l2 = some (r, m') →
      decHL m o1'.toNat l1.toNat = some xs → o1'.toNat + l1.toNat ≤ iwTop m → _ := fun o1' h' hx hb1 => by
    obtain ⟨hr, hd, -, -, -, htop⟩ := appendW_dec h' hS.2.2.2.1 hS.2.2.2.2.2 hb1 hb2 hx h2
    obtain ⟨hS', hg, -⟩ := appendW_stage h' hS hb1 hb2
    exact (⟨hS', hg, by rw [hr]; exact hd, by rw [hr]; simp only [List.headD_cons, List.tail_cons]; omega⟩ :
      StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (xs ++ ys) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m')
  by_cases hl : l1 = 0
  · subst hl
    rw [rec2AppendW_norm] at h
    exact key 0 h (by simpa [decHL, hslice?] using hx0) (by simp)
  · have hl' : l1.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
    exact key o1 h hx0 (rec2DecB_HL_top h1 hl')

/-! ## `expr_get_d` at every fuel -/

theorem rec2ExprGetD_specF (p : Prog) (hpf : p.lookup "bvar_find" = some bvarFind)
    (hpp : p.lookup "bvar_push" = some bvarPush) (hib : p.lookup "intern_bvar" = some internBVar)
    (hp : p.lookup "expr_get_d" = some exprGetD) (n : Nat) (s₀ : St) (o l i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "expr_get_d" [o, l, i]
    ⦃fun r s' => LocEq s' s₀ ∧ fuelW n (exprGetDW s₀.mem o l i) = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact exprGetD_spec p hpf hpp hib hp n s₀ o l i

theorem rec2SimExprGetD {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (n : Nat) (hS : StageR dn vis fe m a) {o l i : Word} {xs : List EIdx}
    (hxs : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat < 2 ^ 64) :
    RSim (fuelW n (exprGetDW m o l i)) (ConRon.Arena.exprGetD xs i.toNat) a (KP dn vis fe m decW0E) := by
  rcases n with _ | n
  · exact RSim.none
  rintro ⟨r, m'⟩ h
  obtain ⟨x, a', hrun, hS', hg, h1, h2⟩ := exprGetDW_ok dn vis fe m m' a o l i xs r h hS hxs hb
  exact ⟨x, a', hrun, hS', hg, h1, h2⟩

/-! ## `class_gen_major`: the model -/

/-- The lookups `class_gen_major` needs. -/
structure MjProg (p : Prog) : Prop where
  ad : AdF p
  hi1 : I1Prog p
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  app : p.lookup "sl_append" = some slAppend
  pw : p.lookup "pin_word" = some pinWordL
  mtm : p.lookup "mk_target_major" = some mkTargetMajor
  tmd : p.lookup "target_major_default" = some targetMajorDefault
  tma : p.lookup "target_major_at" = some targetMajorAt
  na : NaF p
  bf : p.lookup "bvar_find" = some bvarFind
  bp : p.lookup "bvar_push" = some bvarPush
  ib : p.lookup "intern_bvar" = some internBVar
  egd : p.lookup "expr_get_d" = some exprGetD
  ev : p.lookup "e_view" = some eView
  ipw : p.lookup "inst_pis_with" = some instPisWith
  cf : p.lookup "const_find" = some constFind
  cp : p.lookup "const_push" = some constPush
  ic : p.lookup "intern_const" = some internConst
  mjt : p.lookup "class_gen_major_tail" = some classGenMajorTail
  mci : p.lookup "class_gen_major_ci" = some classGenMajorCi
  mjo : p.lookup "class_gen_major_open" = some classGenMajorOpen
  mj : p.lookup "class_gen_major" = some classGenMajor
  opf : OpfF p

l_model classGenMajorTail_spec (p : Prog) (h : MjProg p)
  fns [h.mjt ↦ mjtW list]
  specs [internConst_spec p h.cf h.cp h.ic n, slAppend_specW p h.alloc h.copy h.app n, mknF_spec p h.ad n]
  grind [arena_grind] simp []

l_model classGenMajorOpen_spec (p : Prog) (h : MjProg p)
  fns [h.mjo ↦ mjoW list]
  specs [opfF_spec p h.opf n, classGenMajorTail_spec p h n]
  grind [arena_grind] simp []

theorem classGenMajorCi_spec (p : Prog) (h : MjProg p) (n : Nat) (s₀ : St) (ci : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_major_ci" [ci]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = rdW (s₀.mem.arr64 IW) ci ∧ r.tail.headD 0 = rdW (s₀.mem.arr64 IW) (ci + 1) ∧
      r.tail.tail.headD 0 = rdW (s₀.mem.arr64 IW) (ci + 2) ∧
      r.tail.tail.tail.headD 0 = rdW (s₀.mem.arr64 IW) (ci + 3) ∧
      r.tail.tail.tail.tail.headD 0 = rdW (s₀.mem.arr64 IW) (ci + 5); ⊤⦄ := by
  rw [invoke_eq _ h.mci]
  simp only [callFn, classGenMajorCi]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
    finish (gen := 20) [rdW_eq]

l_model classGenMajor_spec (p : Prog) (h : MjProg p)
  fns [h.mj ↦ mjW list]
  specs [targetMajorAt_spec p h.alloc h.pw h.mtm h.tmd h.tma h.na n,
    rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, instPisWith_spec p h.ev h.ipw h.hi1 n,
    classGenMajorOpen_spec p h n, classGenMajorCi_spec p h n]
  grind [arena_grind] finish [rdW_eq] gen 20

/-! ## `class_gen_major` refines `ClassGen.major` -/

/-- The twin's `ClassGen.major` after the index telescope is opened. -/
def rec2MajTail (ind : NIdx) (lvls : LsIdx) (ds ifs : List EIdx) : AM (Option (List EIdx × EIdx)) := do
  let hd ← internE (.const ind lvls)
  let maj ← mkAppN hd (ds ++ ifs)
  pure (some (ifs, maj))

/-- The twin's `ClassGen.major` after the parameters are instantiated. -/
def rec2MajOpen (ind : NIdx) (lvls : LsIdx) (ds : List EIdx) (nIdx : Nat) (ty : EIdx) (d : Nat) :
    AM (Option (List EIdx × EIdx)) := do
  match ← openPisAtFvarsF nIdx ty d with
  | none => pure none
  | some (ifs, _) => rec2MajTail ind lvls ds ifs

theorem rec2Major_eq (g : ClassGen) (c d : Nat) : ConRon.Arena.ClassGen.major g c d = (do
    let ci ← ConRon.Arena.targetMajorAt g.cls c
    let fty ← ConRon.Arena.exprGetD g.formerTys c
    match ← ConRon.Arena.instPisWith ci.ds fty with
    | none => pure none
    | some ty => rec2MajOpen ci.ind ci.lvls ci.ds ci.nIdx ty d) := rfl

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem mjtW_sim (n : Nat) (m : Mem) (a : AState) (ind lvls ds0 dl0 fo fl : Word) (I : NIdx) (U : LsIdx)
    (ds ifs : List EIdx) (hS : StageR dn vis fe m a) (hI : ind.toNat < 2 ^ 32 ∧ decI ind = I)
    (hU : lvls.toNat < 2 ^ 32 ∧ decI lvls = U)
    (hds : DecB (fun m => (decHL m ds0.toNat dl0.toNat : Option (List EIdx))) m ds)
    (hifs : decHL m fo.toNat fl.toNat = some ifs) (hfb : fo.toNat + fl.toNat ≤ iwTop m) :
    RSim (mjtW n m ind lvls ds0 dl0 fo fl) (rec2MajTail I U ds ifs) a (KP dn vis fe m decOLE) := by
  rcases n with _ | n
  · exact RSim.none
  rw [mjtW.arm1]
  obtain ⟨hI1, rfl⟩ := hI
  obtain ⟨hU1, rfl⟩ := hU
  refine RSim.bind (K := mjtW.k_intern_const n ds0 dl0 fo fl) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧
    IWGrow m b.2 ∧ x = decE b.1) ?_ ?_
  · rintro ⟨hd, m1⟩ h1
    obtain ⟨a', hrun, hS', hg⟩ := internConst_stage hS ind lvls hI1 hU1 h1
    exact ⟨decE hd, a', hrun, hS', hg, rfl⟩
  rintro ⟨hd, m1⟩ x a1 - ⟨hS1, hg1, rfl⟩
  by_cases hbig : 4294967296 ≤ hd
  · rw [mjtW.k_intern_const.abort1 (hc1 := hbig)]; exact RSim.none
  rw [mjtW.k_intern_const.arm1 (hc1 := hbig)]
  have hH : H hd := by
    have : ¬ (4294967296 : Word).toNat ≤ hd.toNat := fun x => hbig (UInt64.le_iff_toNat_le.mpr x)
    simp at this; exact this
  refine RSim.lstep (K := mjtW.k_sl_append fo fl hd) rfl fun ⟨r2, m2⟩ h2 => ?_
  obtain ⟨hS2, hg2, hd2, hb2⟩ := rec2AppendW_dec h2 hS1 (hds.grow (OMono.decHL _ _) hg1)
    (by rw [decHL_grow hg1 hfb]; exact hifs) (Nat.le_trans hfb hg1.1)
  rw [mjtW.k_sl_append.arm1]
  refine RSim.bind (K := mjtW.k_mk_app_n_f fo fl) rfl
    ((mknF_ok dn vis fe hd (r2.headD 0) (r2.tail.headD 0) hH (ds ++ ifs)).sim ⟨hS2, hd2⟩) ?_
  rintro ⟨r3, m3⟩ maj a3 - ⟨hS3, hg3, hmaj⟩
  rw [mjtW.k_mk_app_n_f.arm1]
  have hg := hg1.trans (hg2.trans hg3)
  refine RSim.pure_some ⟨hS3, hg, rfl, ⟨?_, ?_⟩, ?_⟩
  · show decHL m3 fo.toNat fl.toNat = some ifs
    rw [decHL_grow hg hfb]; exact hifs
  · show fo.toNat + fl.toNat ≤ iwTop m3
    exact Nat.le_trans hfb hg.1
  · exact hmaj

/-! ## The `abstract1` memo across `class_gen_major` -/

theorem exprGetDW_afr {m m' : Mem} {o l i : Word} {r : List Word} (h : exprGetDW m o l i = some (r, m')) :
    AFr m m' := by
  unfold exprGetDW at h
  afr_auto h [binternW_afr]

theorem mkTMW_afr {m m' : Mem} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word} {r : List Word}
    (h : mkTMW m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = some (r, m')) : AFr m m' := by
  simp only [mkTMW] at h
  split at h; · cases h
  rename_i q m1 h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (allocW_afr h1).trans (by simp only [tmWr]; afr_set)

theorem tmdW_afr {m m' : Mem} {r : List Word} (h : tmdW m = some (r, m')) : AFr m m' := by
  simp only [tmdW, tmdK1.eq_def, tmdK2.eq_def, tmdK3.eq_def] at h
  afr_auto h [naF_afr, mkTMW_afr]

theorem tmaW_afr {n : Nat} {m m' : Mem} {mo ml c : Word} {r : List Word} (h : tmaW n m mo ml c = some (r, m')) :
    AFr m m' := by
  rcases n with _ | n
  · simp [tmaW] at h
  simp only [tmaW, tmaK.eq_def] at h
  cases n <;> simp only [fuelW] at h <;> afr_auto h [tmdW_afr]

theorem mjtW_afr {n : Nat} {m m' : Mem} {ind lvls ds0 dl0 fo fl : Word} {r : List Word}
    (h : mjtW n m ind lvls ds0 dl0 fo fl = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [mjtW] at h
  simp only [mjtW, mjtW.k_intern_const.eq_def, mjtW.k_sl_append.eq_def, mjtW.k_mk_app_n_f.eq_def] at h
  afr_auto h [ceinternW_afr, appendW_afr, mknF_afr]

theorem exprGetDF_afr {n : Nat} {m m' : Mem} {o l i : Word} {r : List Word}
    (h : fuelW n (exprGetDW m o l i) = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [fuelW] at h
  | succ n => exact exprGetDW_afr h

theorem mjoW_sim (n : Nat) (m : Mem) (a : AState) (ind lvls ds0 dl0 nIdx ty d : Word) (I : NIdx) (U : LsIdx)
    (ds : List EIdx) (hS : StageR dn vis fe m a) (hI : ind.toNat < 2 ^ 32 ∧ decI ind = I)
    (hU : lvls.toNat < 2 ^ 32 ∧ decI lvls = U)
    (hds : DecB (fun m => (decHL m ds0.toNat dl0.toNat : Option (List EIdx))) m ds) (hty : H ty)
    (hA : AbsOK m) :
    RSim (mjoW n m ind lvls ds0 dl0 nIdx ty d) (rec2MajOpen I U ds nIdx.toNat (decI ty) d.toNat) a
      (fun b a' x => KP dn vis fe m decOLE b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [mjoW.arm1]
  refine RSim.bind (K := mjoW.k_open_pis_at_fvars_f n ind lvls ds0 dl0) rfl (simOpenPisF hS hA hty) ?_
  rintro ⟨r4, m4⟩ o a4 - ⟨⟨hS4, hg4, ho⟩, hA4⟩
  rcases o with _ | p4
  · rw [mjoW.k_open_pis_at_fvars_f.arm1 (hc1 := ho)]; exact RSim.pure_some ⟨⟨hS4, hg4, rfl⟩, hA4⟩
  obtain ⟨ifs, body⟩ := p4
  obtain ⟨h41, ⟨hifs, hfb⟩, -⟩ := ho
  simp only [getD_one, getD_two, Nat.reduceAdd] at hifs hfb
  rw [mjoW.k_open_pis_at_fvars_f.arm2 (hc1 := by rw [h41]; decide)]
  refine RSim.bindPure (K := mjoW.k_class_gen_major_tail) rfl (RSim.withF (mjtW_sim n m4 a4 ind lvls ds0 dl0 _ _ I U ds ifs hS4 hI hU
    (hds.grow (OMono.decHL _ _) hg4) hifs hfb) (fun _ hb => mjtW_afr hb)) ?_
  rintro ⟨r5, m5⟩ x a5 - ⟨⟨hS5, hg5, hx⟩, hf5⟩
  rw [mjoW.k_class_gen_major_tail.arm1]
  refine RSim.pure_some ⟨⟨hS5, hg4.trans hg5, ?_⟩, hf5 hA4⟩
  rcases x with _ | p
  · exact hx
  obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hx
  refine ⟨by simpa using h1, ⟨by simpa [getD_one, getD_two] using h2, by simpa [getD_one, getD_two] using h3⟩, ?_⟩
  simpa [decW0E, drop3_headD] using h4

end sims

theorem rec2DecB_PL_top {α : Type} {f : Mem → Nat → Option α} {m : Mem} {o l : Nat} {xs : List α}
    (h : DecB (fun m => decPL m (f m) o l) m xs) (hl : l ≠ 0) : o + l ≤ iwTop m := by
  obtain ⟨v, hv, -⟩ := decPL_getH (truncM m) h (l - 1) (by omega)
  have := (rec2IwN_trunc hv).1
  omega

/-- A word read at a decoded record field. -/
theorem rec2RdN {m : Mem} {w : Word} {k v : Nat} (h : iwN m (w.toNat + k) = some v)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    rdW (m.arr64 IW) (w + UInt64.ofNat k) = UInt64.ofNat v ∧ (UInt64.ofNat v : Word).toNat = v := by
  have := iwN_rdW_at h hsz
  exact ⟨this.1, UInt64.toNat_ofNat_of_lt' this.2⟩

theorem mjW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (g c d : Word) (G : ClassGen) (hS : StageR dn vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hA : AbsOK m) :
    RSim (mjW n m g c d) (ConRon.Arena.ClassGen.major G c.toNat d.toNat) a
      (fun b a' x => KP dn vis fe m decOLE b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [mjW.arm1, rec2Major_eq]
  have hsz := hS.2.2.2.1
  have htop := hS.2.1
  obtain ⟨-, hgt, ⟨o3, l3, h3, h4, hcls⟩, ⟨o5, l5, h5, h6, hft⟩, -, -⟩ := rec2CG_parts hG
  obtain ⟨e3, t3⟩ := rec2RdN (w := g) (k := 3) h3 hsz
  obtain ⟨e4, t4⟩ := rec2RdN (w := g) (k := 4) h4 hsz
  simp only [show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at e3 e4
  rw [e3, e4]
  have hb3 : o3 + l3 < 2 ^ 64 := by
    by_cases hl : l3 = 0
    · have := iwN_rdW h3 (by omega); omega
    · have := rec2DecB_PL_top hcls hl; omega
  refine RSim.bind (K := mjW.k_target_major_at n g c d) rfl (RSim.withF (rec2SimTMA dn vis fe n m a _ _ c G.cls hS
    (by rw [t3, t4]; exact hcls) (by rw [t3, t4]; exact hb3)) (fun _ hb => tmaW_afr hb)) ?_
  rintro ⟨r1, m1⟩ tm a1 - ⟨⟨hS1, hg1, hTM, hds⟩, hf1⟩
  dsimp only at hS1 hg1 hTM hds
  rw [mjW.k_target_major_at.arm1]
  have hsz1 := hS1.2.2.2.1
  obtain ⟨hind, hlv, ⟨o, l, ho, hl, -⟩, -, hni⟩ := rec2DecTM_parts hTM
  have hds1 := hds o l ho hl
  obtain ⟨vi, evi, hvi, dvi⟩ := iwH_rdW_at (w := r1.headD 0) (k := 0) (by simpa using hind) hsz1
  obtain ⟨vl, evl, hvl, dvl⟩ := iwH_rdW_at (w := r1.headD 0) (k := 1) hlv hsz1
  obtain ⟨eo, to⟩ := rec2RdN (w := r1.headD 0) (k := 2) ho hsz1
  obtain ⟨el, tl⟩ := rec2RdN (w := r1.headD 0) (k := 3) hl hsz1
  obtain ⟨en, tn⟩ := rec2RdN (w := r1.headD 0) (k := 5) hni hsz1
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero, show UInt64.ofNat 1 = (1 : Word) from rfl,
    show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl,
    show UInt64.ofNat 5 = (5 : Word) from rfl] at evi evl eo el en
  rw [evi, evl, eo, el, en]
  -- the former types, at `m1`
  have e5' : iwN m1 (g.toNat + 5) = some o5 := by rw [iwN_grow hg1 (by omega)]; exact h5
  have e6' : iwN m1 (g.toNat + 6) = some l5 := by rw [iwN_grow hg1 (by omega)]; exact h6
  obtain ⟨e5, t5⟩ := rec2RdN (w := g) (k := 5) e5' hsz1
  obtain ⟨e6, t6⟩ := rec2RdN (w := g) (k := 6) e6' hsz1
  simp only [show UInt64.ofNat 5 = (5 : Word) from rfl, show UInt64.ofNat 6 = (6 : Word) from rfl] at e5 e6
  rw [e5, e6]
  have hb5 : o5 + l5 < 2 ^ 64 := by
    by_cases hl5 : l5 = 0
    · have := iwN_rdW h5 (by omega); omega
    · have := rec2DecB_HL_top hft hl5; omega
  refine RSim.bind (K := mjW.k_expr_get_d n d _ _ _ _ _) rfl (RSim.withF (rec2SimExprGetD n hS1
    (by rw [t5, t6]; exact rec2DecB_HL_stab hft hg1) (by rw [t5, t6]; exact hb5)) (fun _ hb => exprGetDF_afr hb)) ?_
  rintro ⟨r2, m2⟩ fty a2 - ⟨⟨hS2, hg2, hfH, hfd⟩, hf2⟩
  dsimp only at hS2 hg2 hfH hfd
  subst hfd
  rw [mjW.k_expr_get_d.arm1]
  have hds2 := hds1.grow (OMono.decHL _ _) hg2
  rw [← to, ← tl] at hds2
  refine RSim.bind (K := mjW.k_inst_pis_with n d _ _ _ _ _) rfl (RSim.withF (rec2SimInstW n hS2 hfH hds2)
    (fun _ hb => instW_afr _ _ _ _ _ _ _ hb)) ?_
  rintro ⟨r3, m3⟩ oty a3 - ⟨⟨hS3, hg3, ho3⟩, hf3⟩
  have hA3 : AbsOK m3 := hf3 (hf2 (hf1 hA))
  dsimp only at hS3 hg3 ho3
  rcases oty with _ | ty
  · rw [mjW.k_inst_pis_with.arm1 (hc1 := ho3)]; exact RSim.pure_some ⟨⟨hS3, hg1.trans (hg2.trans hg3), rfl⟩, hA3⟩
  obtain ⟨h31, htyH, htyd⟩ := ho3
  rw [mjW.k_inst_pis_with.arm2 (hc1 := by rw [h31]; decide)]
  have hm := mjoW_sim (dn := dn) (vis := vis) (fe := fe) n m3 a3 vi vl _ _ (UInt64.ofNat tm.nIdx)
    (r3.tail.headD 0) d tm.ind tm.lvls tm.ds hS3 ⟨hvi, dvi⟩ ⟨hvl, dvl⟩ (hds2.grow (OMono.decHL _ _) hg3) htyH hA3
  rw [tn, htyd] at hm
  refine RSim.bindPure (K := mjW.k_class_gen_major_open) rfl hm ?_
  rintro ⟨r5, m5⟩ x a5 - ⟨⟨hS5, hg5, hx⟩, hA5⟩
  rw [mjW.k_class_gen_major_open.arm1]
  refine RSim.pure_some ⟨⟨hS5, hg1.trans (hg2.trans (hg3.trans hg5)), ?_⟩, hA5⟩
  rcases x with _ | p
  · exact hx
  obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hx
  refine ⟨by simpa using h1, ⟨by simpa [getD_one, getD_two] using h2, by simpa [getD_one, getD_two] using h3⟩, ?_⟩
  simpa [decW0E, drop3_headD] using h4

/-- **`class_gen_major` refines `ClassGen.major`** (through `open_pis_at_fvars_f`'s real
refinement, under the walk memos, kept after; the class generator decoded below the tops). -/
@[refines ConRon.Arena.ClassGen.major]
theorem classGenMajor_refines (p : Prog) (hp : MjProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g c d : Word) (G : ClassGen)
    (hS : StageR dn vis fe s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_major" [g, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.major G c.toNat d.toNat) a₀ ∧
      KP dn vis fe s₀.mem decOLE (r, s'.mem) (AM.st (ConRon.Arena.ClassGen.major G c.toNat d.toNat) a₀)
        (AM.res (ConRon.Arena.ClassGen.major G c.toNat d.toNat) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classGenMajor_spec p hp n s₀ g c d) fun _ _ ⟨hl, hw⟩ =>
    ⟨hl, (mjW_sim dn vis fe n _ a₀ g c d G hS hG hA).am hw⟩

/-! ## `class_gen_motive_ty` -/

theorem rec2MapM_classBinder : ∀ xs : List EIdx, xs.mapM ConRon.Arena.classBinder = fvarTypeDs xs
  | [] => rfl
  | x :: xs => by
    simp only [List.mapM_cons, fvarTypeDs, ConRon.Arena.classBinder, rec2MapM_classBinder xs]

theorem rec2MapM_genBinder (g : ClassGen) : ∀ xs : List EIdx, xs.mapM g.binder = fvarTypeDs xs
  | [] => rfl
  | x :: xs => by
    simp only [List.mapM_cons, fvarTypeDs, ConRon.Arena.ClassGen.binder, rec2MapM_genBinder g xs]

/-- The lookups `class_gen_motive_ty` needs. -/
structure MtProg (p : Prog) : Prop extends MjProg p where
  sf : p.lookup "sort_find" = some sortFind
  sp : p.lookup "sort_push" = some sortPush
  isort : p.lookup "intern_sort" = some internSort
  db : p.lookup "der_b" = some derB
  ff : p.lookup "forall_find" = some forallFind
  fp : p.lookup "forall_push" = some forallPush
  ifa : p.lookup "intern_forall" = some internForallL
  mkf : p.lookup "mk_forall" = some mkForall
  ct : p.lookup "close_telescope" = some closeTelescope
  ab : AbF p
  mot : p.lookup "class_gen_motive_ty" = some classGenMotiveTy

l_model classGenMotiveTy_spec (p : Prog) (h : MtProg p)
  fns [h.mot ↦ motW list]
  specs [classGenMajor_spec p h.toMjProg n, internSort_spec p h.sf h.sp h.isort n,
    mkForall_spec p h.db h.ff h.fp h.ifa h.mkf n, ftdsF_spec p h.ad n,
    closeTelescope_spec p h.db h.ff h.fp h.ifa h.mkf h.ct h.ab n]
  grind [arena_grind] simp [rdW_eq]

/-- The decoded result of an `Option EIdx` producer. -/
theorem motW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (g c d : Word) (G : ClassGen) (hS : StageR dn vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hA : AbsOK m) :
    RSim (motW n m g c d) (ConRon.Arena.ClassGen.motiveTy G c.toNat d.toNat) a
      (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [motW.arm1]
  unfold ConRon.Arena.ClassGen.motiveTy
  refine RSim.bind (K := motW.k_class_gen_major n g d) rfl
    (mjW_sim dn vis fe n m a g c d G hS hG hA) ?_
  rintro ⟨r1, m1⟩ o1 a1 - ⟨⟨hS1, hg1, ho1⟩, hA1⟩
  dsimp only at hS1 hg1 ho1
  rcases o1 with _ | p1
  · rw [motW.k_class_gen_major.arm1 (hc1 := ho1)]; exact RSim.pure_some ⟨⟨hS1, hg1, rfl⟩, hA1⟩
  obtain ⟨ifs, maj⟩ := p1
  obtain ⟨h11, ⟨hifs, hfb⟩, hmH, hmd⟩ := ho1
  simp only [getD_one, getD_two, Nat.reduceAdd] at hifs hfb
  simp only [drop3_headD] at hmH hmd
  rw [motW.k_class_gen_major.arm2 (hc1 := by rw [h11]; decide)]
  obtain ⟨-, hgt, -, -, hel, -⟩ := rec2CG_parts hG
  obtain ⟨ve, eve, hve, dve⟩ := iwH_rdW_at (w := g) (k := 11) (by rw [iwH_grow hg1 (show g.toNat + 11 < iwTop m by omega)]; exact hel) hS1.2.2.2.1
  simp only [show UInt64.ofNat 11 = (11 : Word) from rfl] at eve
  rw [eve]
  refine RSim.bind (K := motW.k_intern_sort n d _ _ _) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧
    IWGrow m1 b.2 ∧ x = decE b.1 ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨srt, m2⟩ h2
    obtain ⟨a', hrun, hS', hg⟩ := internSort_stage hS1 ve hve h2
    rw [dve] at hrun
    exact ⟨decE srt, a', hrun, hS', hg, rfl, sointernW_afr h2 hA1⟩
  rintro ⟨srt, m2⟩ x a2 - ⟨hS2, hg2, rfl, hA2⟩
  by_cases hbig : 4294967296 ≤ srt
  · rw [motW.k_intern_sort.abort1 (hc1 := hbig)]; exact RSim.none
  rw [motW.k_intern_sort.arm1 (hc1 := hbig)]
  refine RSim.bind (K := motW.k_mk_forall n d _ _) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧
    IWGrow m2 b.2 ∧ x = decE b.1 ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨b, m3⟩ h3
    obtain ⟨a', hrun, hS', hg⟩ := mkForall_stage hS2 _ srt h3
    exact ⟨decE b, a', by rw [← hmd]; exact hrun, hS', hg, rfl, mkForallW_afr h3 hA2⟩
  rintro ⟨b, m3⟩ x a3 - ⟨hS3, hg3, rfl, hA3⟩
  by_cases hbig3 : 4294967296 ≤ b
  · rw [motW.k_mk_forall.abort1 (hc1 := hbig3)]; exact RSim.none
  rw [motW.k_mk_forall.arm1 (hc1 := hbig3)]
  have hbH : H b := by
    have : ¬ (4294967296 : Word).toNat ≤ b.toNat := fun x => hbig3 (UInt64.le_iff_toNat_le.mpr x)
    simp at this; exact this
  have hg13 := hg1.trans (hg2.trans hg3)
  rw [rec2MapM_classBinder]
  refine RSim.bind (K := motW.k_fvar_type_ds n d b) rfl (RSim.withF ((ftdsF_ok dn vis fe _ _ ifs).sim
      ⟨hS3, by rw [decHL_grow (hg2.trans hg3) hfb]; exact hifs, fun _ => Nat.le_trans hfb (hg2.trans hg3).1⟩) (fun _ hb => ftdsF_afr hb)) ?_
  rintro ⟨r4, m4⟩ bs a4 - ⟨⟨hS4, hg4, hbs, hbb⟩, hf4⟩
  dsimp only at hS4 hg4 hbs hbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hbs hbb
  by_cases hov : d + r4.tail.headD 0 < d
  · rw [motW.k_fvar_type_ds.abort1 (hc1 := hov)]; exact RSim.none
  rw [motW.k_fvar_type_ds.arm1 (hc1 := hov)]
  have hdl : d.toNat + (r4.tail.headD 0).toNat < 2 ^ 64 := by
    have := nctAddNowrap (a := r4.tail.headD 0) (b := d) (by rwa [UInt64.add_comm]); omega
  refine RSim.bind (K := motW.k_close_telescope) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m4 b.2 ∧
    decW0E b.2 b.1 x ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨r5, m5⟩ h5
    obtain ⟨x, a', hrun, hS', hg, hx, hA5⟩ := closeW_ok n dn fe vis m4 m5 a4 _ _ d b bs r5 h5 hS4 hbH hbs
      (hS4.lt64 hbb) hbb hdl (hf4 hA3)
    exact ⟨x, a', hrun, hS', hg, hx, hA5⟩
  rintro ⟨r5, m5⟩ x a5 - ⟨hS5, hg5, hx, hA5⟩
  rw [motW.k_close_telescope.arm1]
  exact RSim.pure_some ⟨⟨hS5, hg13.trans (hg4.trans hg5), rfl, by simpa [decW0E] using hx⟩, hA5⟩

/-- **`class_gen_motive_ty` refines `ClassGen.motiveTy`** (through the stubs of `class_gen_major`,
`fvar_type_ds` and `close_telescope`'s `abstract1_fast`). -/
@[refines ConRon.Arena.ClassGen.motiveTy]
theorem classGenMotiveTy_refines (p : Prog) (hp : MtProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g c d : Word) (G : ClassGen)
    (hS : StageR dn vis fe s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_motive_ty" [g, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.motiveTy G c.toNat d.toNat) a₀ ∧
      KP dn vis fe s₀.mem decOE (r, s'.mem) (AM.st (ConRon.Arena.ClassGen.motiveTy G c.toNat d.toNat) a₀)
        (AM.res (ConRon.Arena.ClassGen.motiveTy G c.toNat d.toNat) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classGenMotiveTy_spec p hp n s₀ g c d) fun _ _ ⟨hl, hw⟩ =>
    let h := (motW_sim dn vis fe n _ a₀ g c d G hS hG hA).am hw
    ⟨hl, h.1, h.2.1, h.2.2⟩

end L.Ind
