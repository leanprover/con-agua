import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.IlpRd
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

/-!
# TargetMajorAt: `ConRon.Arena.abstractPrefixList`, `ConRon.Arena.abstractPrefix`, `ConRon.Arena.targetHoles`, `ConRon.Arena.targetMajorAt` (hit), `ConRon.Arena.targetPiDomsWith`

The refinement theorems `targetMajorAt_refines_hit`, `abstractPrefix_refines`, `abstractPrefixList_refines`, `targetHoles_refines`, `targetPiDomsWith_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `decPL` read back at one index -/

/-- A trivially `True`-postconditioned triple, for the branch this theorem leaves to the default
arm (round 2's scope is the HIT arm only; the MISS arm interns and is left for a later round). -/
theorem trivialTriple {α : Type} (prog : M α) (P : St → Prop) :
    ⦃P⦄ prog ⦃fun _ _ => True; ⊤⦄ :=
  M.triple_of_run fun _ _ _ _ _ => trivial

/-! ## `target_major_at`'s HIT arm -/

/-- **`target_major_at` HIT arm refines `targetMajorAt`**: at an in-range class index, the
L function reads the stored pointer directly (no allocation), which decodes to the twin's
`ms[c]`, just as the twin's `pure m` does nothing to the state. -/
@[refines_part ConRon.Arena.targetMajorAt "hit"]
theorem targetMajorAt_refines_hit (p : Prog) (hp : p.lookup "target_major_at" = some targetMajorAt)
    (n : Nat) (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (hR : StageR dn vis fe s₀.mem a₀) (mo ml c : Word) (ms : List TargetMajor)
    (bigM : TargetMajor) (hms : decPL s₀.mem (decTM s₀.mem) mo.toNat ml.toNat = some ms)
    (hc : c.toNat < ml.toNat) (hfound : ms[c.toNat]? = some bigM)
    (hbound : mo.toNat + ml.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "target_major_at" [mo, ml, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetMajorAt ms c.toNat) a₀ ∧
      KeepPost dn vis fe (fun m' r (x : TargetMajor) => decTM m' (r.headD 0).toNat = some x)
        s₀.mem s'.mem a₀ r (AM.res (ConRon.Arena.targetMajorAt ms c.toNat) a₀); ⊤⦄ := by
  obtain ⟨v, hv, hdec⟩ := decPL_getH s₀.mem hms c.toNat hc
  have hv' := iwN_rdW hv (by omega)
  have hget : ms[c.toNat]'(by rw [decPL_length s₀.mem hms]; exact hc) = bigM := by
    have heq := List.getElem?_eq_getElem (l := ms) (i := c.toNat)
      (by rw [decPL_length s₀.mem hms]; exact hc)
    rw [hfound] at heq
    exact (Option.some.injEq _ _).mp heq.symm
  have hdecBigM : decTM s₀.mem v = some bigM := hget ▸ hdec
  have hop : ConRon.Arena.targetMajorAt ms c.toNat = pure bigM := by
    simp [ConRon.Arena.targetMajorAt, hfound]
  have hcc : c < ml := UInt64.lt_iff_toNat_lt.mpr hc
  rw [invoke_eq _ hp]
  simp only [callFn, targetMajorAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        trivialTriple (invoke p (exec p n) "target_major_default" []) (fun s => s = s₀)] <;>
      finish [KeepPost, IWGrow.refl]

/-- **`abstract_prefix` refines `abstractPrefix`** (through the `abstract1_fast` stub). -/
@[refines ConRon.Arena.abstractPrefix]
theorem abstractPrefix_refines (p : Prog) (hp : p.lookup "abstract_prefix" = some abstractPrefix)
    (hab : AbF p) (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (k c e : Word) (hS : StageR dn vis fe s₀.mem a₀) (he : H e)
    (hb : c.toNat + k.toNat < 2 ^ 64) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "abstract_prefix" [k, c, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.abstractPrefix k.toNat c.toNat (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.abstractPrefix k.toNat c.toNat (decI e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = AM.res (ConRon.Arena.abstractPrefix k.toNat c.toNat (decI e)) a₀ ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (abstractPrefix_spec p hp hab n s₀ k c e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, h1, h2, hA'⟩ := absPrefW_ok dn vis fe n _ _ a₀ k c e r hm hS he hb hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.abstractPrefix k.toNat c.toNat (decI e)) a₀ a' x hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, h1, by rw [hres]; exact h2, hA'⟩

/-- **`abstract_prefix_list` refines `abstractPrefixList`** (through the `abstract1_fast` stub). -/
@[refines ConRon.Arena.abstractPrefixList]
theorem abstractPrefixList_refines (p : Prog) (hap : p.lookup "abstract_prefix" = some abstractPrefix)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "abstract_prefix_list" = some abstractPrefixList) (hab : AbF p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (rP dso dsl : Word)
    (ds : List EIdx) (hS : StageR dn vis fe s₀.mem a₀) (hds : decHL s₀.mem dso.toNat dsl.toNat = some ds)
    (hb : dso.toNat + dsl.toNat < 2 ^ 64) (hbt : dso.toNat + dsl.toNat ≤ iwTop s₀.mem)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "abstract_prefix_list" [rP, dso, dsl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.abstractPrefixList rP.toNat ds) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.abstractPrefixList rP.toNat ds) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (ConRon.Arena.abstractPrefixList rP.toNat ds) a₀) ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (abstractPrefixList_spec p hap hc ha hsc hp hab n s₀ rP dso dsl) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨xs, a', hrun, hS', hg, hd, -, hA'⟩ := aplW_ok dn vis fe n _ _ a₀ rP dso dsl r ds hm hS hds hb hbt
    rP.toNat_lt hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.abstractPrefixList rP.toNat ds) a₀ a' xs hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hd, hA'⟩

/-- **`target_holes` refines `targetHoles`** (through master's `intern_fvar`). -/
@[refines ConRon.Arena.targetHoles]
theorem targetHoles_refines (p : Prog) (hff : p.lookup "fvar_find" = some fvarFind)
    (hfp : p.lookup "fvar_push" = some fvarPush) (hif : p.lookup "intern_fvar" = some internFVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "target_holes" = some targetHoles) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (tyo tyl base : Word)
    (tys : List EIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (htys : decHL s₀.mem tyo.toNat tyl.toNat = some tys) (hb : tyo.toNat + tyl.toNat < 2 ^ 64)
    (hbt : tyo.toNat + tyl.toNat ≤ iwTop s₀.mem) (hbase : base.toNat + tyl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_holes" [tyo, tyl, base]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetHoles tys base.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetHoles tys base.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (ConRon.Arena.targetHoles tys base.toNat) a₀); ⊤⦄ := by
  refine triple_post (targetHoles_spec p hff hfp hif hc ha hsc hp n s₀ tyo tyl base) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨xs, a', hrun, hS', hg, hd, -⟩ := thW_ok dn vis fe n _ _ a₀ tyo tyl base r tys hm hS htys hb hbt hbase
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.targetHoles tys base.toNat) a₀ a' xs hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hd⟩

local notation "V" => ConLeche.CheckMode.verified

/-- **`target_pi_doms_with` refines `targetPiDomsWith`** (through `e_view`, `instantiate1_fast`
and `sl_cons`). -/
@[refines ConRon.Arena.targetPiDomsWith]
theorem targetPiDomsWith_refines (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "target_pi_doms_with" = some targetPiDomsWith) (hi1 : I1Prog p) (n : Nat) (s₀ : St)
    (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (xo xl e : Word) (xs : List EIdx)
    (hS : StageR dn vis fe s₀.mem a₀) (he : H e) (hxs : decHL s₀.mem xo.toNat xl.toNat = some xs)
    (hb : xo.toNat + xl.toNat < 2 ^ 64) (hbt : xo.toNat + xl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_pi_doms_with" [xo, xl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetPiDomsWith xs (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetPiDomsWith xs (decI e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ PdRes s'.mem r (AM.res (ConRon.Arena.targetPiDomsWith xs (decI e)) a₀);
      ⊤⦄ := by
  refine triple_post (targetPiDomsWith_spec p hv hc ha hsc hp hi1 n s₀ xo xl e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨res, a', hrun, hS', hg, hres⟩ := pdW_ok dn vis fe n _ _ a₀ xo xl e r xs hm hS he hxs hb hbt
  obtain ⟨hok, hst, hrs⟩ := AM.of_run_ok (ConRon.Arena.targetPiDomsWith xs (decI e)) a₀ a' res hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hrs]; exact hres⟩

theorem decTM_fields {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    iwH m (p + 1) = some M.lvls ∧ ∃ w8, iwN m (p + 8) = some w8 ∧ M.member = decON w8 := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨w5, h5, a1, ha1, w4, h4, w3, h3, w2, h2, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h
  exact ⟨ha1, w1, hw1, rfl⟩

theorem targetCtorAt_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
    (hcv : p.lookup "cv_lps" = some cvLps) (hp : p.lookup "target_ctor_at" = some targetCtorAt)
    (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (M c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_ctor_at" [M, c]
    ⦃fun r s' => LocEq s' s₀ ∧ tcW cR n s₀.mem M c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, targetCtorAt]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      cvLps_spec p ha hc he hcv n, hcR n "inst_lp_fast"] <;>
    finish (gen := 20) [tcW, tcK1, tcK2]

theorem tcW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m m' : Mem)
    (a : AState) (Mp c : Word) (bigM : TargetMajor) (cv : IConstantVal) (r : List Word) (cR : CallM)
    (hI : IlpRd cR dn vis fe (IlpBase m a)) (hS : StageR dn vis fe m a) (hM : decTM m Mp.toNat = some bigM) (hcv : decCVp m c.toNat = some cv)
    (hMb : Mp.toNat + 13 < 2 ^ 64) (hcb : c.toNat + 3 < 2 ^ 64)
    (hlpb : (rdW (m.arr64 EREC) (c + 2)).toNat = 0 ∨
      (rdW (m.arr64 EREC) (c + 1)).toNat + (rdW (m.arr64 EREC) (c + 2)).toNat ≤ (m.arr64 EREC).size)
    (h : tcW cR n m Mp c = some (r, m')) :
    ∃ x a', (ConRon.Arena.targetCtorAt bigM cv).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = x ∧ AFr m m' := by
  obtain ⟨hlv, w8, h8, hmem⟩ := decTM_fields hM
  obtain ⟨-, -, htyp⟩ := decCV_some (a := erA m) (q := c.toNat) hcv
  obtain ⟨wt, hwt, hwtlt, hwtd⟩ := erH_rdW htyp (by omega)
  have hwc : UInt64.ofNat (c.toNat + 3) = c + 3 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add]
    simp
  rw [hwc] at hwt
  have e : UInt64.ofNat Mp.toNat = Mp := UInt64.ofNat_toNat
  have h8' := iwN_off (k := 8) h8 (by omega)
  rw [e] at h8'
  simp only [show UInt64.ofNat 8 = 8 from rfl] at h8'
  have hw8b : w8 < 2 ^ 64 := (iwN_rdW h8 (by omega)).2
  simp only [tcW, h8'.2] at h
  by_cases hz : UInt64.ofNat w8 = 0
  · have hw0 : w8 = 0 := by
      have := congrArg UInt64.toNat hz
      rw [UInt64.toNat_ofNat_of_lt' hw8b] at this
      simpa using this
    -- an outside major
    have hnone : bigM.member = none := by rw [hmem, hw0]; simp [decON]
    simp only [hz, ne_eq, not_true_eq_false, ite_false] at h
    obtain ⟨wl, hwl, hwl2, hwl3⟩ : ∃ wl, rdW (m.arr64 IW) (Mp + 1) = wl ∧ wl.toNat < 2 ^ 32 ∧ decI wl = bigM.lvls := by
      have h1 := iwH_off (k := 1) hlv (by omega)
      rw [e] at h1
      simp only [show UInt64.ofNat 1 = 1 from rfl] at h1
      exact h1.2
    rw [hwl] at h
    rcases hcl : cvLpsW n m c with _ | ⟨r1, m1⟩ <;> rw [hcl] at h <;>
      try (simp only [tcK1, reduceCtorEq] at h; done)
    obtain ⟨hS1, hg1, hE, hdec1, hto⟩ := cvLpsW_stage hcl hS hcv hcb hlpb
    simp only [tcK1] at h
    rw [hE, hwt] at h
    rcases hi : cR n "inst_lp_fast" [CWF, r1.headD 0, r1.tail.headD 0, wl, wt] m1 with _ | ⟨r2, m2⟩ <;> rw [hi] at h <;>
      try (simp only [tcK2, reduceCtorEq] at h; done)
    simp only [tcK2, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨x, a2, hrun, ⟨hS2, hg2, hd1, hd2⟩, -, hA2⟩ :=
      hI n CWF (r1.headD 0) (r1.tail.headD 0) wl wt cv.levelParams m1 m2 a r2 hwl2 hwtlt
        ⟨rfl, erToIwW_iwFr hcl⟩ hS1 hdec1 hi
    refine ⟨x, a2, ?_, hS2, hg1.trans hg2, by simpa using hd1, by simpa using hd2,
      (erToIwW_afr hcl).trans hA2⟩
    simp only [ConRon.Arena.targetCtorAt, hnone]
    rw [CWF_eq] at hrun
    rw [← hwl3, ← hwtd]
    exact hrun
  · have hnz : w8 ≠ 0 := fun hh => hz (by rw [hh]; rfl)
    obtain ⟨t0, ht0⟩ : ∃ t0, bigM.member = some t0 := ⟨w8 - 1, by rw [hmem]; simp [decON, hnz]⟩
    simp only [hz, ne_eq, not_false_eq_true, ite_true, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [hwt]
    refine ⟨cv.type, a, ?_, hS, IWGrow.refl m, by simpa using hwtlt, by simpa using hwtd, AFr.refl _⟩
    simp [ConRon.Arena.targetCtorAt, ht0]; rfl

end L.Ind

end
