import ConAgua.Arena.RecGenSpec6
import ConAgua.Arena.RecCheckSpec3

/-!
# `RecClass`: `ClassGen.major` (lane `indproofs2`, helper `rec2`)

The class generator `g` is taken decoded below the tops (`DecB` of `decCG`), so every field and
every slice it names is stable across the callees. A slice decoded below the tops may still be
empty at an offset above the top; `rec2InstW_ok` and `rec2AppendW_norm` handle that case (an empty
slice's offset is never read).
-/

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
  cases hc : ms[c.toNat]? with
  | none =>
    have hrun' : ConRon.Arena.targetMajorDefault.run a = .ok (tm, a') := by
      simpa [ConRon.Arena.targetMajorAt, hc] using hrun
    rw [rec2TMD_ds hrun']
    obtain ⟨-, -, ⟨o', l', ho', hl', hds⟩, -⟩ := rec2DecTM_parts hd
    rw [ho] at ho'; rw [hl] at hl'; cases ho'; cases hl'
    rw [rec2TMD_ds hrun'] at hds
    have : l = 0 := by have := decHL_length _ hds; simp at this; omega
    subst this
    show decHL (truncM b.2) o 0 = some []
    simp [decHL, hslice?]
  | some x =>
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
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
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
  cases n with
  | zero => exact RSim.none
  | succ n =>
    rintro ⟨r, m'⟩ h
    obtain ⟨x, a', hrun, hS', hg, h1, h2⟩ := exprGetDW_ok dn vis fe m m' a o l i xs r h hS hxs hb
    exact ⟨x, a', hrun, hS', hg, h1, h2⟩

/-! ## `class_gen_major`: the model -/

def mjtK3 (fo fl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([1, fo, fl, r3.headD 0], m3)

def mjtK2 (hd fo fl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => mjtK3 fo fl (stubM "mk_app_n_f" m2 [hd, r2.headD 0, r2.tail.headD 0])

def mjtK1 (n : Nat) (ds0 dl0 fo fl : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hd, m1) => if 4294967296 ≤ hd then none else mjtK2 hd fo fl (appendW n m1 ds0 dl0 fo fl)

/-- **The model of `class_gen_major_tail`.** -/
def mjtW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, ind, lvls, ds0, dl0, fo, fl => mjtK1 n ds0 dl0 fo fl (ceinternW m ind lvls)

def mjoK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => some ([r5.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0, r5.tail.tail.tail.headD 0], m5)

def mjoK (n : Nat) (ind lvls ds0 dl0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r4.headD 0 = 0 then some ([0, 0, 0, 0], m4)
    else mjoK1 (mjtW n m4 ind lvls ds0 dl0 (r4.tail.headD 0) (r4.tail.tail.headD 0))

/-- **The model of `class_gen_major_open`.** -/
def mjoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, ind, lvls, ds0, dl0, nIdx, ty, d =>
    mjoK n ind lvls ds0 dl0 (stubM "open_pis_at_fvars_f" m [nIdx, ty, d])

def mjK3 (n : Nat) (ind lvls ds0 dl0 nIdx d : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then some ([0, 0, 0, 0], m3)
    else mjoK1 (mjoW n m3 ind lvls ds0 dl0 nIdx (r3.tail.headD 0) d)

def mjK2 (n : Nat) (ind lvls ds0 dl0 nIdx d : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => mjK3 n ind lvls ds0 dl0 nIdx d (instW n m2 ds0 dl0 (r2.headD 0))

def mjK1 (n : Nat) (g c d : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    mjK2 n (rdW (m1.arr64 IW) (r1.headD 0)) (rdW (m1.arr64 IW) (r1.headD 0 + 1))
      (rdW (m1.arr64 IW) (r1.headD 0 + 2)) (rdW (m1.arr64 IW) (r1.headD 0 + 3))
      (rdW (m1.arr64 IW) (r1.headD 0 + 5)) d
      (fuelW n (exprGetDW m1 (rdW (m1.arr64 IW) (g + 5)) (rdW (m1.arr64 IW) (g + 6)) c))

/-- **The model of `class_gen_major`.** -/
def mjW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, g, c, d => mjK1 n g c d (tmaW n m (rdW (m.arr64 IW) (g + 3)) (rdW (m.arr64 IW) (g + 4)) c)

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (g c d ind lvls ds0 dl0 nIdx fo fl hd : Word)
  (r1 r2 r3 r4 r5 : List Word)
theorem mjtW_eq : mjtW (n + 1) m ind lvls ds0 dl0 fo fl = mjtK1 n ds0 dl0 fo fl (ceinternW m ind lvls) := rfl
theorem mjtK1_big (h : 4294967296 ≤ hd) : mjtK1 n ds0 dl0 fo fl (some (hd, m1)) = none := by
  rw [mjtK1, if_pos h]
theorem mjtK1_ok (h : ¬ 4294967296 ≤ hd) : mjtK1 n ds0 dl0 fo fl (some (hd, m1)) =
    mjtK2 hd fo fl (appendW n m1 ds0 dl0 fo fl) := by
  rw [mjtK1, if_neg h]
theorem mjtK2_some : mjtK2 hd fo fl (some (r2, m2)) =
    mjtK3 fo fl (stubM "mk_app_n_f" m2 [hd, r2.headD 0, r2.tail.headD 0]) := rfl
theorem mjtK3_some : mjtK3 fo fl (some (r3, m3)) = some ([1, fo, fl, r3.headD 0], m3) := rfl
theorem mjW_eq : mjW (n + 1) m g c d =
    mjK1 n g c d (tmaW n m (rdW (m.arr64 IW) (g + 3)) (rdW (m.arr64 IW) (g + 4)) c) := rfl
theorem mjK1_some : mjK1 n g c d (some (r1, m1)) =
    mjK2 n (rdW (m1.arr64 IW) (r1.headD 0)) (rdW (m1.arr64 IW) (r1.headD 0 + 1))
      (rdW (m1.arr64 IW) (r1.headD 0 + 2)) (rdW (m1.arr64 IW) (r1.headD 0 + 3))
      (rdW (m1.arr64 IW) (r1.headD 0 + 5)) d
      (fuelW n (exprGetDW m1 (rdW (m1.arr64 IW) (g + 5)) (rdW (m1.arr64 IW) (g + 6)) c)) := rfl
theorem mjK2_some : mjK2 n ind lvls ds0 dl0 nIdx d (some (r2, m2)) =
    mjK3 n ind lvls ds0 dl0 nIdx d (instW n m2 ds0 dl0 (r2.headD 0)) := rfl
theorem mjK3_fail (h : r3.headD 0 = 0) : mjK3 n ind lvls ds0 dl0 nIdx d (some (r3, m3)) = some ([0, 0, 0, 0], m3) := by
  rw [mjK3, if_pos h]
theorem mjK3_ok (h : r3.headD 0 ≠ 0) : mjK3 n ind lvls ds0 dl0 nIdx d (some (r3, m3)) =
    mjoK1 (mjoW n m3 ind lvls ds0 dl0 nIdx (r3.tail.headD 0) d) := by
  rw [mjK3, if_neg h]
theorem mjoW_eq (ty : Word) : mjoW (n + 1) m ind lvls ds0 dl0 nIdx ty d =
    mjoK n ind lvls ds0 dl0 (stubM "open_pis_at_fvars_f" m [nIdx, ty, d]) := rfl
theorem mjoK_fail (h : r4.headD 0 = 0) : mjoK n ind lvls ds0 dl0 (some (r4, m4)) = some ([0, 0, 0, 0], m4) := by
  rw [mjoK, if_pos h]
theorem mjoK_ok (h : r4.headD 0 ≠ 0) : mjoK n ind lvls ds0 dl0 (some (r4, m4)) =
    mjoK1 (mjtW n m4 ind lvls ds0 dl0 (r4.tail.headD 0) (r4.tail.tail.headD 0)) := by
  rw [mjoK, if_neg h]
theorem mjoK1_some : mjoK1 (some (r5, m5)) =
    some ([r5.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0, r5.tail.tail.tail.headD 0], m5) := rfl
end arms

grind_pattern [ind_grind] mjtW_eq => mjtW (n + 1) m ind lvls ds0 dl0 fo fl
grind_pattern [ind_grind] mjtK1_big => mjtK1 n ds0 dl0 fo fl (some (hd, m1))
grind_pattern [ind_grind] mjtK1_ok => mjtK1 n ds0 dl0 fo fl (some (hd, m1))
grind_pattern [ind_grind] mjtK2_some => mjtK2 hd fo fl (some (r2, m2))
grind_pattern [ind_grind] mjtK3_some => mjtK3 fo fl (some (r3, m3))
grind_pattern [ind_grind] mjW_eq => mjW (n + 1) m g c d
grind_pattern [ind_grind] mjK1_some => mjK1 n g c d (some (r1, m1))
grind_pattern [ind_grind] mjK2_some => mjK2 n ind lvls ds0 dl0 nIdx d (some (r2, m2))
grind_pattern [ind_grind] mjK3_fail => mjK3 n ind lvls ds0 dl0 nIdx d (some (r3, m3))
grind_pattern [ind_grind] mjK3_ok => mjK3 n ind lvls ds0 dl0 nIdx d (some (r3, m3))
grind_pattern [ind_grind] mjoW_eq => mjoW (n + 1) m ind lvls ds0 dl0 nIdx ty d
grind_pattern [ind_grind] mjoK_fail => mjoK n ind lvls ds0 dl0 (some (r4, m4))
grind_pattern [ind_grind] mjoK_ok => mjoK n ind lvls ds0 dl0 (some (r4, m4))
grind_pattern [ind_grind] mjoK1_some => mjoK1 (some (r5, m5))

/-- The lookups `class_gen_major` needs. -/
structure MjProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  app : p.lookup "sl_append" = some slAppend
  pw : p.lookup "pin_word" = some pinWordL
  mtm : p.lookup "mk_target_major" = some mkTargetMajor
  tmd : p.lookup "target_major_default" = some targetMajorDefault
  tma : p.lookup "target_major_at" = some targetMajorAt
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

theorem classGenMajorTail_spec (p : Prog) (h : MjProg p) (n : Nat) (s₀ : St) (ind lvls ds0 dl0 fo fl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_major_tail" [ind, lvls, ds0, dl0, fo, fl]
    ⦃fun r s' => LocEq s' s₀ ∧ mjtW n s₀.mem ind lvls ds0 dl0 fo fl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.mjt]
  simp only [callFn, classGenMajorTail]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        internConst_spec p h.cf h.cp h.ic n, slAppend_specW p h.alloc h.copy h.app n,
        stubM_spec p "mk_app_n_f" n] <;>
      finish (gen := 20)

theorem classGenMajorOpen_spec (p : Prog) (h : MjProg p) (n : Nat) (s₀ : St) (ind lvls ds0 dl0 nIdx ty d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_major_open" [ind, lvls, ds0, dl0, nIdx, ty, d]
    ⦃fun r s' => LocEq s' s₀ ∧ mjoW n s₀.mem ind lvls ds0 dl0 nIdx ty d = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.mjo]
  simp only [callFn, classGenMajorOpen]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        stubM_spec p "open_pis_at_fvars_f" n, classGenMajorTail_spec p h n] <;>
      finish (gen := 20) [loc_init4, loc_init5, loc_init6]

theorem classGenMajorCi_spec (p : Prog) (h : MjProg p) (n : Nat) (s₀ : St) (ci : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_major_ci" [ci]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r = [rdW (s₀.mem.arr64 IW) ci, rdW (s₀.mem.arr64 IW) (ci + 1), rdW (s₀.mem.arr64 IW) (ci + 2),
        rdW (s₀.mem.arr64 IW) (ci + 3), rdW (s₀.mem.arr64 IW) (ci + 5)]; ⊤⦄ := by
  rw [invoke_eq _ h.mci]
  simp only [callFn, classGenMajorCi]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish (gen := 20) [rdW_eq]

theorem classGenMajor_spec (p : Prog) (h : MjProg p) (n : Nat) (s₀ : St) (g c d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_major" [g, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ mjW n s₀.mem g c d = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.mj]
  simp only [callFn, classGenMajor]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        targetMajorAt_spec p h.alloc h.pw h.mtm h.tmd h.tma n,
        rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, instPisWith_spec p h.ev h.ipw n,
        classGenMajorOpen_spec p h n, classGenMajorCi_spec p h n] <;>
      finish (gen := 20) [rdW_eq]

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
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [mjtW_eq]
  obtain ⟨hI1, rfl⟩ := hI
  obtain ⟨hU1, rfl⟩ := hU
  refine RSim.bind (K := mjtK1 n ds0 dl0 fo fl) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧
    IWGrow m b.2 ∧ x = decE b.1) ?_ ?_
  · rintro ⟨hd, m1⟩ h1
    obtain ⟨a', hrun, hS', hg⟩ := internConst_stage hS ind lvls hI1 hU1 h1
    exact ⟨decE hd, a', hrun, hS', hg, rfl⟩
  rintro ⟨hd, m1⟩ x a1 - ⟨hS1, hg1, rfl⟩
  by_cases hbig : 4294967296 ≤ hd
  · rw [mjtK1_big (h := hbig)]; exact RSim.none
  rw [mjtK1_ok (h := hbig)]
  have hH : H hd := by
    have : ¬ (4294967296 : Word).toNat ≤ hd.toNat := fun x => hbig (UInt64.le_iff_toNat_le.mpr x)
    simp at this; exact this
  refine RSim.lstep (K := mjtK2 hd fo fl) rfl fun ⟨r2, m2⟩ h2 => ?_
  obtain ⟨hS2, hg2, hd2, hb2⟩ := rec2AppendW_dec h2 hS1 (hds.grow (OMono.decHL _ _) hg1)
    (by rw [decHL_grow hg1 hfb]; exact hifs) (Nat.le_trans hfb hg1.1)
  rw [mjtK2_some]
  refine RSim.bind (K := mjtK3 fo fl) rfl
    ((mkAppN_spec dn vis fe hd (r2.headD 0) (r2.tail.headD 0) hH (ds ++ ifs)).sim ⟨hS2, hd2⟩) ?_
  rintro ⟨r3, m3⟩ maj a3 - ⟨hS3, hg3, hmaj⟩
  rw [mjtK3_some]
  have hg := hg1.trans (hg2.trans hg3)
  refine RSim.pure_some ⟨hS3, hg, rfl, ⟨?_, ?_⟩, ?_⟩
  · show decHL m3 fo.toNat fl.toNat = some ifs
    rw [decHL_grow hg hfb]; exact hifs
  · show fo.toNat + fl.toNat ≤ iwTop m3
    exact Nat.le_trans hfb hg.1
  · exact hmaj

theorem mjoW_sim (n : Nat) (m : Mem) (a : AState) (ind lvls ds0 dl0 nIdx ty d : Word) (I : NIdx) (U : LsIdx)
    (ds : List EIdx) (hS : StageR dn vis fe m a) (hI : ind.toNat < 2 ^ 32 ∧ decI ind = I)
    (hU : lvls.toNat < 2 ^ 32 ∧ decI lvls = U)
    (hds : DecB (fun m => (decHL m ds0.toNat dl0.toNat : Option (List EIdx))) m ds) (hty : H ty) :
    RSim (mjoW n m ind lvls ds0 dl0 nIdx ty d) (rec2MajOpen I U ds nIdx.toNat (decI ty) d.toNat) a
      (KP dn vis fe m decOLE) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [mjoW_eq]
  refine RSim.bind (K := mjoK n ind lvls ds0 dl0) rfl (simOpenPis hS hty) ?_
  rintro ⟨r4, m4⟩ o a4 - ⟨hS4, hg4, ho⟩
  cases o with
  | none =>
    rw [mjoK_fail (h := ho)]
    exact RSim.pure_some ⟨hS4, hg4, rfl⟩
  | some p4 =>
  obtain ⟨ifs, body⟩ := p4
  obtain ⟨h41, ⟨hifs, hfb⟩, -⟩ := ho
  simp only [getD_one, getD_two, Nat.reduceAdd] at hifs hfb
  rw [mjoK_ok (h := by rw [h41]; decide)]
  refine RSim.bindPure (K := mjoK1) rfl (mjtW_sim n m4 a4 ind lvls ds0 dl0 _ _ I U ds ifs hS4 hI hU
    (hds.grow (OMono.decHL _ _) hg4) hifs hfb) ?_
  rintro ⟨r5, m5⟩ x a5 - ⟨hS5, hg5, hx⟩
  rw [mjoK1_some]
  refine RSim.pure_some ⟨hS5, hg4.trans hg5, ?_⟩
  cases x with
  | none => exact hx
  | some p =>
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
    (hG : DecB (fun m => decCG m g.toNat) m G) :
    RSim (mjW n m g c d) (ConRon.Arena.ClassGen.major G c.toNat d.toNat) a (KP dn vis fe m decOLE) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [mjW_eq, rec2Major_eq]
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
  refine RSim.bind (K := mjK1 n g c d) rfl (rec2SimTMA dn vis fe n m a _ _ c G.cls hS
    (by rw [t3, t4]; exact hcls) (by rw [t3, t4]; exact hb3)) ?_
  rintro ⟨r1, m1⟩ tm a1 - ⟨hS1, hg1, hTM, hds⟩
  dsimp only at hS1 hg1 hTM hds
  rw [mjK1_some]
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
  refine RSim.bind (K := mjK2 n _ _ _ _ _ d) rfl (rec2SimExprGetD n hS1
    (by rw [t5, t6]; exact rec2DecB_HL_stab hft hg1) (by rw [t5, t6]; exact hb5)) ?_
  rintro ⟨r2, m2⟩ fty a2 - ⟨hS2, hg2, hfH, hfd⟩
  dsimp only at hS2 hg2 hfH hfd
  subst hfd
  rw [mjK2_some]
  have hds2 := hds1.grow (OMono.decHL _ _) hg2
  rw [← to, ← tl] at hds2
  refine RSim.bind (K := mjK3 n _ _ _ _ _ d) rfl (rec2SimInstW n hS2 hfH hds2) ?_
  rintro ⟨r3, m3⟩ oty a3 - ⟨hS3, hg3, ho3⟩
  dsimp only at hS3 hg3 ho3
  cases oty with
  | none =>
    rw [mjK3_fail (h := ho3)]
    exact RSim.pure_some ⟨hS3, hg1.trans (hg2.trans hg3), rfl⟩
  | some ty =>
  obtain ⟨h31, htyH, htyd⟩ := ho3
  rw [mjK3_ok (h := by rw [h31]; decide)]
  have hm := mjoW_sim (dn := dn) (vis := vis) (fe := fe) n m3 a3 vi vl _ _ (UInt64.ofNat tm.nIdx)
    (r3.tail.headD 0) d tm.ind tm.lvls tm.ds hS3 ⟨hvi, dvi⟩ ⟨hvl, dvl⟩ (hds2.grow (OMono.decHL _ _) hg3) htyH
  rw [tn, htyd] at hm
  refine RSim.bindPure (K := mjoK1) rfl hm ?_
  rintro ⟨r5, m5⟩ x a5 - ⟨hS5, hg5, hx⟩
  rw [mjoK1_some]
  refine RSim.pure_some ⟨hS5, hg1.trans (hg2.trans (hg3.trans hg5)), ?_⟩
  cases x with
  | none => exact hx
  | some p =>
    obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hx
    refine ⟨by simpa using h1, ⟨by simpa [getD_one, getD_two] using h2, by simpa [getD_one, getD_two] using h3⟩, ?_⟩
    simpa [decW0E, drop3_headD] using h4

/-- **`class_gen_major` refines `ClassGen.major`** (through the stubs `open_pis_at_fvars_f`,
`mk_app_n_f`, `instantiate1_fast`; the class generator decoded below the tops). -/
@[refines ConRon.Arena.ClassGen.major]
theorem classGenMajor_refines (p : Prog) (hp : MjProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g c d : Word) (G : ClassGen)
    (hS : StageR dn vis fe s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_major" [g, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.major G c.toNat d.toNat) a₀ ∧
      KP dn vis fe s₀.mem decOLE (r, s'.mem) (AM.st (ConRon.Arena.ClassGen.major G c.toNat d.toNat) a₀)
        (AM.res (ConRon.Arena.ClassGen.major G c.toNat d.toNat) a₀); ⊤⦄ :=
  triple_post (classGenMajor_spec p hp n s₀ g c d) fun _ _ ⟨hl, hw⟩ =>
    ⟨hl, (mjW_sim dn vis fe n _ a₀ g c d G hS hG).am hw⟩

/-! ## `class_gen_motive_ty` -/

theorem rec2MapM_classBinder : ∀ xs : List EIdx, xs.mapM ConRon.Arena.classBinder = fvarTypeDs xs
  | [] => rfl
  | x :: xs => by
    simp only [List.mapM_cons, fvarTypeDs, ConRon.Arena.classBinder, rec2MapM_classBinder xs]

theorem rec2MapM_genBinder (g : ClassGen) : ∀ xs : List EIdx, xs.mapM g.binder = fvarTypeDs xs
  | [] => rfl
  | x :: xs => by
    simp only [List.mapM_cons, fvarTypeDs, ConRon.Arena.ClassGen.binder, rec2MapM_genBinder g xs]

def motK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => some ([1, r5.headD 0], m5)

def motK4 (n : Nat) (d b : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if d + r4.tail.headD 0 < d then none
    else motK5 (closeW n m4 (r4.headD 0) (r4.tail.headD 0) d b)

def motK3 (n : Nat) (d fo fl : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (b, m3) => if 4294967296 ≤ b then none else motK4 n d b (stubM "fvar_type_ds" m3 [fo, fl])

def motK2 (n : Nat) (d fo fl maj : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (srt, m2) => if 4294967296 ≤ srt then none else motK3 n d fo fl (mkForallW m2 maj srt)

def motK1 (n : Nat) (g d : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else motK2 n d (r1.tail.headD 0) (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0)
      (sointernW m1 (rdW (m1.arr64 IW) (g + 11)))

/-- **The model of `class_gen_motive_ty`.** -/
def motW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, g, c, d => motK1 n g d (mjW n m g c d)

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (g c d b fo fl maj srt : Word) (r1 r4 r5 : List Word)
theorem motW_eq : motW (n + 1) m g c d = motK1 n g d (mjW n m g c d) := rfl
theorem motK1_fail (h : r1.headD 0 = 0) : motK1 n g d (some (r1, m1)) = some ([0, 0], m1) := by
  rw [motK1, if_pos h]
theorem motK1_ok (h : r1.headD 0 ≠ 0) : motK1 n g d (some (r1, m1)) =
    motK2 n d (r1.tail.headD 0) (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0)
      (sointernW m1 (rdW (m1.arr64 IW) (g + 11))) := by
  rw [motK1, if_neg h]
theorem motK2_big (h : 4294967296 ≤ srt) : motK2 n d fo fl maj (some (srt, m2)) = none := by
  rw [motK2, if_pos h]
theorem motK2_ok (h : ¬ 4294967296 ≤ srt) : motK2 n d fo fl maj (some (srt, m2)) =
    motK3 n d fo fl (mkForallW m2 maj srt) := by
  rw [motK2, if_neg h]
theorem motK3_big (h : 4294967296 ≤ b) : motK3 n d fo fl (some (b, m3)) = none := by
  rw [motK3, if_pos h]
theorem motK3_ok (h : ¬ 4294967296 ≤ b) : motK3 n d fo fl (some (b, m3)) =
    motK4 n d b (stubM "fvar_type_ds" m3 [fo, fl]) := by
  rw [motK3, if_neg h]
theorem motK4_big (h : d + r4.tail.headD 0 < d) : motK4 n d b (some (r4, m4)) = none := by
  rw [motK4, if_pos h]
theorem motK4_ok (h : ¬ d + r4.tail.headD 0 < d) : motK4 n d b (some (r4, m4)) =
    motK5 (closeW n m4 (r4.headD 0) (r4.tail.headD 0) d b) := by
  rw [motK4, if_neg h]
theorem motK5_some : motK5 (some (r5, m5)) = some ([1, r5.headD 0], m5) := rfl
end arms

grind_pattern [ind_grind] motW_eq => motW (n + 1) m g c d
grind_pattern [ind_grind] motK1_fail => motK1 n g d (some (r1, m1))
grind_pattern [ind_grind] motK1_ok => motK1 n g d (some (r1, m1))
grind_pattern [ind_grind] motK2_big => motK2 n d fo fl maj (some (srt, m2))
grind_pattern [ind_grind] motK2_ok => motK2 n d fo fl maj (some (srt, m2))
grind_pattern [ind_grind] motK3_big => motK3 n d fo fl (some (b, m3))
grind_pattern [ind_grind] motK3_ok => motK3 n d fo fl (some (b, m3))
grind_pattern [ind_grind] motK4_big => motK4 n d b (some (r4, m4))
grind_pattern [ind_grind] motK4_ok => motK4 n d b (some (r4, m4))
grind_pattern [ind_grind] motK5_some => motK5 (some (r5, m5))

/-- The lookups `class_gen_motive_ty` needs. -/
structure MtProg (p : Prog) extends MjProg p : Prop where
  sf : p.lookup "sort_find" = some sortFind
  sp : p.lookup "sort_push" = some sortPush
  isort : p.lookup "intern_sort" = some internSort
  db : p.lookup "der_b" = some derB
  ff : p.lookup "forall_find" = some forallFind
  fp : p.lookup "forall_push" = some forallPush
  ifa : p.lookup "intern_forall" = some internForallL
  mkf : p.lookup "mk_forall" = some mkForall
  ct : p.lookup "close_telescope" = some closeTelescope
  mot : p.lookup "class_gen_motive_ty" = some classGenMotiveTy

theorem classGenMotiveTy_spec (p : Prog) (h : MtProg p) (n : Nat) (s₀ : St) (g c d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_motive_ty" [g, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ motW n s₀.mem g c d = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.mot]
  simp only [callFn, classGenMotiveTy]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classGenMajor_spec p h.toMjProg n, internSort_spec p h.sf h.sp h.isort n,
        mkForall_spec p h.db h.ff h.fp h.ifa h.mkf n, stubM_spec p "fvar_type_ds" n,
        closeTelescope_spec p h.db h.ff h.fp h.ifa h.mkf h.ct n] <;>
      finish (gen := 20) [rdW_eq]

/-- The decoded result of an `Option EIdx` producer. -/
theorem motW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (g c d : Word) (G : ClassGen) (hS : StageR dn vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) :
    RSim (motW n m g c d) (ConRon.Arena.ClassGen.motiveTy G c.toNat d.toNat) a (KP dn vis fe m decOE) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [motW_eq]
  unfold ConRon.Arena.ClassGen.motiveTy
  refine RSim.bind (K := motK1 n g d) rfl (mjW_sim dn vis fe n m a g c d G hS hG) ?_
  rintro ⟨r1, m1⟩ o1 a1 - ⟨hS1, hg1, ho1⟩
  dsimp only at hS1 hg1 ho1
  cases o1 with
  | none =>
    rw [motK1_fail (h := ho1)]
    exact RSim.pure_some ⟨hS1, hg1, rfl⟩
  | some p1 =>
  obtain ⟨ifs, maj⟩ := p1
  obtain ⟨h11, ⟨hifs, hfb⟩, hmH, hmd⟩ := ho1
  simp only [getD_one, getD_two, Nat.reduceAdd] at hifs hfb
  simp only [drop3_headD] at hmH hmd
  rw [motK1_ok (h := by rw [h11]; decide)]
  obtain ⟨-, hgt, -, -, hel, -⟩ := rec2CG_parts hG
  obtain ⟨ve, eve, hve, dve⟩ := iwH_rdW_at (w := g) (k := 11) (iwH_grow hg1 (by omega) ▸ hel) hS1.2.2.2.1
  simp only [show UInt64.ofNat 11 = (11 : Word) from rfl] at eve
  rw [eve]
  refine RSim.bind (K := motK2 n d _ _ _) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧
    IWGrow m1 b.2 ∧ x = decE b.1) ?_ ?_
  · rintro ⟨srt, m2⟩ h2
    obtain ⟨a', hrun, hS', hg⟩ := internSort_stage hS1 ve hve h2
    exact ⟨decE srt, a', by rw [← dve]; exact hrun, hS', hg, rfl⟩
  rintro ⟨srt, m2⟩ x a2 - ⟨hS2, hg2, rfl⟩
  by_cases hbig : 4294967296 ≤ srt
  · rw [motK2_big (h := hbig)]; exact RSim.none
  rw [motK2_ok (h := hbig)]
  refine RSim.bind (K := motK3 n d _ _) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧
    IWGrow m2 b.2 ∧ x = decE b.1) ?_ ?_
  · rintro ⟨b, m3⟩ h3
    obtain ⟨a', hrun, hS', hg⟩ := mkForall_stage hS2 _ srt h3
    exact ⟨decE b, a', by rw [← hmd]; exact hrun, hS', hg, rfl⟩
  rintro ⟨b, m3⟩ x a3 - ⟨hS3, hg3, rfl⟩
  by_cases hbig3 : 4294967296 ≤ b
  · rw [motK3_big (h := hbig3)]; exact RSim.none
  rw [motK3_ok (h := hbig3)]
  have hbH : H b := by
    have : ¬ (4294967296 : Word).toNat ≤ b.toNat := fun x => hbig3 (UInt64.le_iff_toNat_le.mpr x)
    simp at this; exact this
  have hg13 := hg1.trans (hg2.trans hg3)
  rw [rec2MapM_classBinder]
  refine RSim.bind (K := motK4 n d b) rfl ((fvarTypeDs_spec dn vis fe _ _ ifs).sim
    ⟨hS3, by rw [decHL_grow (hg2.trans hg3) hfb]; exact hifs⟩) ?_
  rintro ⟨r4, m4⟩ bs a4 - ⟨hS4, hg4, hbs, hbb⟩
  dsimp only at hS4 hg4 hbs hbb
  simp only [getD_zero, getD_one] at hbs hbb
  by_cases hov : d + r4.tail.headD 0 < d
  · rw [motK4_big (h := hov)]; exact RSim.none
  rw [motK4_ok (h := hov)]
  have hdl : d.toNat + (r4.tail.headD 0).toNat < 2 ^ 64 := by
    have : ¬ (d + r4.tail.headD 0).toNat < d.toNat := fun x => hov (UInt64.lt_iff_toNat_lt.mpr x)
    rw [UInt64.toNat_add] at this
    by_contra hc
    have : (d.toNat + (r4.tail.headD 0).toNat) % 2 ^ 64 = d.toNat + (r4.tail.headD 0).toNat - 2 ^ 64 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by have := d.toNat_lt; have := (r4.tail.headD 0).toNat_lt; omega)]
    have := (r4.tail.headD 0).toNat_lt
    simp only [UInt64.size] at *
    omega
  refine RSim.bindPure (K := motK5) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m4 b.2 ∧
    decW0E b.2 b.1 x) ?_ ?_
  · rintro ⟨r5, m5⟩ h5
    obtain ⟨x, a', hrun, hS', hg, hx⟩ := closeW_ok n dn fe vis m4 m5 a4 _ _ d b bs r5 h5 hS4 hbH hbs
      (hS4.lt64 hbb) hbb hdl
    rw [decE_eq] at *
    exact ⟨x, a', hrun, hS', hg, hx⟩
  rintro ⟨r5, m5⟩ x a5 - ⟨hS5, hg5, hx⟩
  rw [motK5_some]
  exact RSim.pure_some ⟨hS5, hg13.trans (hg4.trans hg5), rfl, by simpa [decW0E] using hx⟩

/-- **`class_gen_motive_ty` refines `ClassGen.motiveTy`** (through the stubs of `class_gen_major`,
`fvar_type_ds` and `close_telescope`'s `abstract1_fast`). -/
@[refines ConRon.Arena.ClassGen.motiveTy]
theorem classGenMotiveTy_refines (p : Prog) (hp : MtProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g c d : Word) (G : ClassGen)
    (hS : StageR dn vis fe s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_motive_ty" [g, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.motiveTy G c.toNat d.toNat) a₀ ∧
      KP dn vis fe s₀.mem decOE (r, s'.mem) (AM.st (ConRon.Arena.ClassGen.motiveTy G c.toNat d.toNat) a₀)
        (AM.res (ConRon.Arena.ClassGen.motiveTy G c.toNat d.toNat) a₀); ⊤⦄ :=
  triple_post (classGenMotiveTy_spec p hp n s₀ g c d) fun _ _ ⟨hl, hw⟩ =>
    ⟨hl, (motW_sim dn vis fe n _ a₀ g c d G hS hG).am hw⟩

end L.Ind
