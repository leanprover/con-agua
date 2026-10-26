import ConAgua.Arena.DefEqStuckEta

/-!
# `eta_ctor_shape` refines `etaCtorShape` (lane `defeq`, helper `defeq-top`)

Reads only: `get_app_fn`, the head's `const` record, `env_find`, the constructor record's counts,
`get_app_args` (its slice dropped: the top put back). Shared helpers for the structure-η side:
`envFind_callW` (a run of `env_find`), `decCI_ctorF` (a constructor record's counts),
`getAppArgs_callW`, `CoreS.restoreTop` (the relation after the top is put back).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Shared helpers -/

/-- **A run of `env_find`**: the memory unchanged, the twin's `find?` decoded, a hit decodes. -/
theorem envFind_callW {p : Prog} (hp : WhnfCoreProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {vis : Word} {fe : IFEnv} (hE : EnvR dn m vis fe) {k : Word} (hk : HW k)
    {r : List Word} (hc : callW p n "env_find" [k, vis] m = some (r, m')) :
    m' = m ∧ fe.find? (decI k) = decFound dn m (r.headD 0) (r.tail.headD 0) ∧
      (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP m) dn (r.tail.headD 0).toNat = some ci) := by
  obtain ⟨t₂, ht₂, hm₂, -, hfind⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_refines p hp.envix hp.envrow hp.envfind n ⟨m, Locals.init []⟩ vis k hE hk) hc
  obtain ⟨t₂', ht₂', hm₂', -, hfound⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_found p hp.envix hp.envrow hp.envfind n ⟨m, Locals.init []⟩ vis k hk) hc
  refine ⟨by rw [← ht₂]; exact hm₂, hfind, fun h0 => ?_⟩
  obtain ⟨htag, hrow, hq⟩ := hfound h0
  obtain ⟨ci, hci⟩ := hE.found_some k hk htag hrow
  exact ⟨ci, by rw [hq]; exact hci⟩

/-- A found record decodes to the twin's constant. -/
theorem find_of_found {dn : NIdx → Option ConLeche.Name} {m : Mem} {fe : IFEnv} {k : Word}
    {r : List Word} (hfind : fe.find? (decI k) = decFound dn m (r.headD 0) (r.tail.headD 0))
    (h0 : r.headD 0 ≠ 0) {ci : IConstantInfo}
    (hci : decCI (erecP m) dn (r.tail.headD 0).toNat = some ci) : fe.find? (decI k) = some ci := by
  rw [hfind]; simp only [decFound, h0, ↓reduceIte]; exact hci

/-- **A constructor record's counts**: kind word `4`, parameters at `q + 5`, fields at `q + 6`. -/
theorem decCI_ctorF {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI a dn q.toNat = some ci) (hab : ArrExt a b)
    (hsz : b.size < 2 ^ 63) :
    (rdW b q = 4 → ∃ cv, ci = .ctorInfo cv (rdW b (q + 5)).toNat (rdW b (q + 6)).toNat) ∧
    (rdW b q ≠ 4 → ∀ cv np nf, ci ≠ .ctorInfo cv np nf) := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  have hrd : rdW b q = w := by
    have := rdW_ext hab hsz (k := 0) (by decide) (by simpa using hq); simpa using this
  rw [hrd]
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  constructor
  · intro hw; subst hw
    simp only [show UInt64.toNat 4 = 4 from rfl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, np, ⟨w5, hw5, rfl⟩, nf, ⟨w6, hw6, rfl⟩, hc⟩ := h
    cases hc
    have h5 : rdW b (q + 5) = w5 := rdW_ext hab hsz (k := 5) (by decide) hw5
    have h6 : rdW b (q + 6) = w6 := rdW_ext hab hsz (k := 6) (by decide) hw6
    exact ⟨cv, by rw [h5, h6]⟩
  · intro hw cv np nf hc
    subst hc
    have hne : w.toNat ≠ 4 := fun e => hw (UInt64.toNat_inj.mp (by rw [e]; rfl))
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h hne; simp [Option.bind_eq_some_iff] at h hne)

/-- **A run of `get_app_args`** from `CoreS`: the twin's arguments as a slice at the old top. -/
theorem getAppArgs_callW {p : Prog} (hp : SpineProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn m a vis fe M eb) {e : Word} (he : HW e) {r : List Word}
    (hc : callW p n "get_app_args" [e] m = some (r, m')) :
    MemFrame [SPN] [136] m m' ∧ StackGrew m m' ∧ r.headD 0 = spTop m ∧
      spTop m' = spTop m + r.tail.headD 0 ∧
      ∃ xs, (getAppArgs coreWalkFuel (decE e)).run a = .ok (xs, a) ∧
        SpineR m' (r.headD 0) (r.tail.headD 0) xs.toArray := by
  obtain ⟨t, ht, -, h1, h2, h3, h4, h5⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (getAppArgs_refines p hp n ⟨m, Locals.init []⟩ a hS.arena.1 e he hS.spn) hc
  subst ht
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **The top put back** after a run that only pushed (`MemFrame [SPN] [136]`, `StackGrew`). -/
theorem CoreS.restoreTop {dn : NIdx → Option ConLeche.Name} {m m₁ : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (hf : MemFrame [SPN] [136] m m₁) (hg : StackGrew m m₁)
    (h136 : (136 : Word).toNat < (m₁.arr64 CTL).size) :
    CoreS dn (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) a vis fe M eb ∧
      StackKept m (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) := by
  have hS₁ := hS.frame_stk hf (by simp) (by simp)
  have hS₂ := hS₁.frame_stk (MemFrame.setCtl m₁ 136 (rdW (m.arr64 CTL) 136)) (by simp) (by simp)
  exact ⟨hS₂, StackKept.restoreG hg h136⟩

/-! ## `eta_ctor_shape` -/

section ecs
variable (p : Prog) (n : Nat) (vis a : Word)

/-- After `get_app_args`: the top put back, the count test. -/
def ecsK3 (top q : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if (136 : Word).toNat < (m.arr64 CTL).size then
      if r.tail.headD 0 < rdW ((m.set64 CTL 136 top).arr64 EREC) (q + 6) then
        some (0, m.set64 CTL 136 top)
      else some (if r.tail.headD 0 - rdW ((m.set64 CTL 136 top).arr64 EREC) (q + 6) =
          rdW ((m.set64 CTL 136 top).arr64 EREC) (q + 5) then 1 else 0, m.set64 CTL 136 top)
    else none

/-- After `env_find`: a constructor record, then the arguments. -/
def ecsK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, m)
    else if rdW (m.arr64 EREC) (r.tail.headD 0) ≠ 4 then some (0, m)
    else ecsK3 (rdW (m.arr64 CTL) 136) (r.tail.headD 0) (callW p n "get_app_args" [a] m)

/-- **The model of `eta_ctor_shape`** past `get_app_fn`'s run. -/
def ecsK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 >>> 28 ≠ 3 then some (0, m)
    else if tierW (r.headD 0) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m CONST (tierW (r.headD 0)) ≤ idxW (r.headD 0) then none
    else ecsK2 p n a (callW p n "env_find"
      [tfld m CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0, vis] m)

end ecs

theorem etaCtorShape_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (vis a : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "eta_ctor_shape" [vis, a]
    ⦃fun r s' => LocEq s' s₀ ∧ ecsK1 p n vis a (callW p n "get_app_fn" [a] s₀.mem) =
      some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.etaCtorShape]
  simp only [callFn, etaCtorShapeL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, evalE_tld, tld,
    evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64_spec,
      callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "get_app_args"] <;>
  simp_all [ecsK1, ecsK2, ecsK3, tierW, idxW, LocEq, BinOp.eval,
    St.setLocs_cons, CTL, EREC, Cmp.eval, Cmp.evalW,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ, size_set64]
  all_goals (intro h; simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *; omega)

/-! ### The twin's runs, by case -/

theorem etaCtorShape_run_nonconst (fe : IFEnv) (e : EIdx) (a : AState) (hh : EIdx)
    (hgaf : (getAppFn coreWalkFuel e).run a = .ok (hh, a)) (ht : (hh.tag == ETag.const) = false) :
    (etaCtorShape fe e).run a = .ok (false, a) := by
  simp only [etaCtorShape, StateT.run_bind, hgaf, except_ok_bind, ht, Bool.false_eq_true,
    ↓reduceIte]
  rfl

theorem etaCtorShape_run_other (fe : IFEnv) (e : EIdx) (a : AState) (hh : EIdx) (c : NIdx)
    (us : LsIdx) (hgaf : (getAppFn coreWalkFuel e).run a = .ok (hh, a))
    (ht : (hh.tag == ETag.const) = true) (hv : a.store.view hh = some (.const c us))
    (hf : ∀ cv np nf, fe.find? c ≠ some (.ctorInfo cv np nf)) :
    (etaCtorShape fe e).run a = .ok (false, a) := by
  simp only [etaCtorShape, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte,
    view_run _ _ _ hv]
  rcases hc : fe.find? c with _ | ⟨_ | _ | _ | _ | ⟨cv, np, nf⟩ | _ | _⟩ <;> try rfl
  all_goals exact absurd hc (hf cv np nf)

theorem etaCtorShape_run_ctor (fe : IFEnv) (e : EIdx) (a : AState) (hh : EIdx) (c : NIdx)
    (us : LsIdx) (hgaf : (getAppFn coreWalkFuel e).run a = .ok (hh, a))
    (ht : (hh.tag == ETag.const) = true) (hv : a.store.view hh = some (.const c us))
    (cv : IConstantVal) (np nf : Nat) (hf : fe.find? c = some (.ctorInfo cv np nf))
    (xs : List EIdx) (hargs : (getAppArgs coreWalkFuel e).run a = .ok (xs, a)) :
    (etaCtorShape fe e).run a = .ok (xs.length == np + nf, a) := by
  simp only [etaCtorShape, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte,
    view_run _ _ _ hv, hf, hargs]
  rfl

/-- The L count test is the twin's: `an - nf = np` on words, past `an < nf`. -/
theorem count_test (an npw nfw : Word) (k : Nat) (hk : k = an.toNat) :
    (if an < nfw then (0 : Word) else if an - nfw = npw then 1 else 0) =
      (if (k == npw.toNat + nfw.toNat) = true then 1 else 0) := by
  subst hk
  by_cases h1 : an < nfw
  · have h1' : an.toNat < nfw.toNat := UInt64.lt_iff_toNat_lt.mp h1
    have : (an.toNat == npw.toNat + nfw.toNat) = false := by simp; omega
    simp only [h1, ↓reduceIte, this]; rfl
  · have h1' : nfw.toNat ≤ an.toNat :=
      Nat.not_lt.mp (fun h => h1 (UInt64.lt_iff_toNat_lt.mpr h))
    have hs : (an - nfw).toNat = an.toNat - nfw.toNat := UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr h1')
    simp only [h1, ↓reduceIte]
    by_cases h2 : an - nfw = npw
    · have : (an.toNat == npw.toNat + nfw.toNat) = true := by
        simp; rw [← h2, hs]; omega
      simp only [h2, ↓reduceIte, this]
    · have : (an.toNat == npw.toNat + nfw.toNat) = false := by
        simp; intro e; apply h2; apply UInt64.toNat_inj.mp; rw [hs]; omega
      simp only [h2, ↓reduceIte, this]; rfl

/-- **`eta_ctor_shape` refines `etaCtorShape`.** -/
@[refines ConRon.Arena.etaCtorShape]
theorem etaCtorShape_refines (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb e : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) :
    CoreSpec p (n + 1) "eta_ctor_shape" [vis, e] (etaCtorShape fe (decE e)) decBool s₀ a₀ dn vis
      fe MM eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (etaCtorShape_spec p hq n s₀ vis e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hR := hS.arena.1
  have hres : ∀ x : Word, some (x, s.mem) = some (r.headD 0, s'.mem) → HW x → ∀ v,
      (etaCtorShape fe (decE e)).run a₀ = .ok (v, a₀) → v = (x != 0) →
      CoreRef (etaCtorShape fe (decE e)) a₀ decBool dn s.mem vis fe MM eb r s'.mem := by
    intro x hxy hx v hv hvx
    obtain ⟨h1, h3⟩ := Prod.mk.inj (Option.some.inj hxy)
    rw [← h3]
    refine coreRef_pure hS hv ?_ ?_
    · rw [hvx, decBool, ← h1]
    · unfold ResH; rw [← h1]; exact hx
  obtain ⟨r₁, m₁, hc, hW⟩ := callW_cases rfl hW
  obtain ⟨rfl, hh, hgaf⟩ := getAppFn_callW hq.leaf hS.arena.1 he hc
  simp only [ecsK1] at hW
  generalize r₁.headD 0 = h at hh hgaf hW
  rcases (Classical.em (h >>> 28 = 3)).symm with h3 | h3
  · simp only [ne_eq, h3, not_false_eq_true, ↓reduceIte] at hW
    exact hres 0 hW hw0 _
      (etaCtorShape_run_nonconst fe _ a₀ _ hgaf (by rw [tag_beq_const _ hh]; simp [h3])) rfl
  have hs : ¬ (tierW h ≠ 0 ∧ rdW (s.mem.arr64 CTL) 1 = 0) := fun hs => by simp [h3, hs] at hW
  have hcc : ¬ tcnt s.mem CONST (tierW h) ≤ idxW h := fun hcc => by simp [h3, hs, hcc] at hW
  simp only [h3, hs, hcc, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  have hvo : viewOK s.mem h CONST := ⟨hs, by simpa using hcc⟩
  obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s.mem a₀ hR h hh hvo h3
  have hct : ((decE h).tag == ETag.const) = true := by rw [tag_beq_const _ hh]; simp [h3]
  generalize tfld s.mem CONST (tierW h) (idxW h) 0 = k at hnw hW hv
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  obtain ⟨rfl, hfind, hfound⟩ := envFind_callW hq.leaf.core hS.env hnw hc2
  simp only [ecsK2] at hW
  by_cases h0 : r₂.headD 0 = 0
  · simp only [h0, ↓reduceIte] at hW
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [decFound, h0, ↓reduceIte]
    exact hres 0 hW hw0 _ (etaCtorShape_run_other fe _ a₀ _ _ _ hgaf hct hv
      (fun cv np nf e => by rw [hnone] at e; cases e)) rfl
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hctor := decCI_ctorF hci (erecP_ext _) hS.erec
  rcases (Classical.em (rdW (s.mem.arr64 EREC) (r₂.tail.headD 0) = 4)).symm with h4 | h4
  · simp only [h0, h4, ne_eq, not_false_eq_true, ↓reduceIte] at hW
    exact hres 0 hW hw0 _ (etaCtorShape_run_other fe _ a₀ _ _ _ hgaf hct hv
      (fun cv np nf e => hctor.2 h4 cv np nf (by rw [hfind'] at e; exact Option.some.inj e))) rfl
  simp only [h0, h4, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  obtain ⟨cv, hci_eq⟩ := hctor.1 h4
  obtain ⟨r₃, m₃, hc3, hW⟩ := callW_cases rfl hW
  obtain ⟨hf3, hg3, -, -, xs, hargs, hsp⟩ := getAppArgs_callW hq.leaf.core.spine hS he hc3
  simp only [ecsK3] at hW
  have h136 : (136 : Word).toNat < (m₃.arr64 CTL).size := by
    by_cases h : (136 : Word).toNat < (m₃.arr64 CTL).size
    · exact h
    · simp only [h, ↓reduceIte] at hW; cases hW
  simp only [h136, ↓reduceIte] at hW
  obtain ⟨hS', hK'⟩ := hS.restoreTop hf3 hg3 h136
  have herec : ((m₃.set64 CTL 136 (rdW (s.mem.arr64 CTL) 136)).arr64 EREC) = s.mem.arr64 EREC := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    exact hf3.1 EREC (by simp [EREC, SPN]) (by decide)
  rw [herec] at hW
  have hrun := etaCtorShape_run_ctor fe _ a₀ _ _ _ hgaf hct hv cv _ _ (by rw [hfind', hci_eq]) xs
    hargs
  have hlen : xs.length = (r₃.tail.headD 0).toNat := by
    have := hsp.size; simpa using this
  have hW' : some ((if r₃.tail.headD 0 < rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 6) then (0 : Word)
      else if r₃.tail.headD 0 - rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 6) =
        rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 5) then 1 else 0),
      m₃.set64 CTL 136 (rdW (s.mem.arr64 CTL) 136)) = some (r.headD 0, s'.mem) := by
    rw [← hW]; split <;> rfl
  rw [count_test _ _ _ xs.length hlen] at hW'
  simp only [Option.some.injEq, Prod.mk.injEq] at hW'
  obtain ⟨hr, hm⟩ := hW'
  obtain ⟨hok, hst, hres'⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok, ?_, ?_, ?_⟩
  · rw [hst, ← hm]; exact ⟨MM, hS', KeptAll.refl _ _, hK'⟩
  · rw [hres', decBool, ← hr]; split <;> simp_all
  · unfold ResH; rw [← hr]; split <;> first | exact hw0 | exact hw1

end L.Arena
