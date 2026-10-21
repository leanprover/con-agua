import ConAgua.Arena.WhnfCoreSlot

/-!
# Refinements of `WhnfCore.lean`'s functions (other than the slot and the loop)

The callW pattern of `WhnfCoreSlot.lean`, one function at a time.

* Environment reads: `env_find`'s flag `≠ 0` means the name has a row (`envFind_found`), and every
  row decodes (`EnvR.found_some`): the L code may read the record's words where the twin matches
  on the decoded constant (`decCI_ctor`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `env_find`: a found row is a row -/

theorem envFind_found (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hp : p.lookup "env_find" = some envFindL)
    (n : Nat) (s₀ : St) (vis w : Word) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_find" [w, vis]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      (r.headD 0 ≠ 0 → rowTag w ≤ 2 ∧ rowC s₀.mem w ≠ 0 ∧ r.tail.headD 0 = rowP s₀.mem w); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, envFindL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, envRowGet_spec p hx hg n] <;>
      finish

/-- **Every row of the index decodes.** -/
theorem EnvR.found_some {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : rowTag w ≤ 2)
    (hc : rowC m w ≠ 0) : ∃ ci, decCI (m.arr64 EREC) dn (rowP m w).toNat = some ci := by
  have hn : (decI w : NIdx).word.toUInt64 = w := (word_decI _ w hw).mpr rfl
  have hk := h.keys (decI w) (by rw [hn]; exact ht)
  have hv := h.vals (decI w) (by rw [hn]; exact ht) (by rw [hn]; exact hc)
  rw [hn] at hk hv
  cases e : fe.idx[(decI w : NIdx)]? with
  | none => simp [e, rowW, hc] at hk
  | some q => rw [e] at hv; exact ⟨q.2, hv.symm⟩

theorem hd?_eq {k : IdxKind} {a : Array Word} {i : Nat} {x : Idx k} (h : hd? a i = some x) :
    ∃ w, a[i]? = some w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  cases e : a[i]? with
  | none => simp [hd?, e] at h
  | some w => simp [hd?, e] at h; exact ⟨w, rfl, h.1, h.2.symm⟩

theorem decCV_type {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    ∃ w, a[q + 3]? = some w ∧ w.toNat < 2 ^ 32 ∧ cv.type = decI w := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨n, -, ls, -, ty, ht, hc⟩ := h
  cases hc
  obtain ⟨w, hw, hl, rfl⟩ := hd?_eq ht
  exact ⟨w, hw, hl, rfl⟩

/-- The kind word of a decoded constant record says whether it is a constructor, and a
constructor's type is the handle at `q + 4`. -/
theorem decCI_ctor {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI a dn q.toNat = some ci) (hsz : a.size < 2 ^ 63) :
    (rdW a q = 4 → ∃ cv np nf, ci = .ctorInfo cv np nf ∧ cv.type = decI (rdW a (q + 4)) ∧
      (rdW a (q + 4)).toNat < 2 ^ 32) ∧
    (rdW a q ≠ 4 → ∀ cv np nf, ci ≠ .ctorInfo cv np nf) := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  have hlt : q.toNat < a.size := by
    rcases Nat.lt_or_ge q.toNat a.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at hq
  have h4 : (q + 4).toNat = q.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have hrd : rdW a q = w := by simp [rdW, hq]
  rw [hrd]
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  constructor
  · intro hw; subst hw
    simp only [show UInt64.toNat 4 = 4 from rfl, Option.bind_eq_some_iff] at h
    obtain ⟨cv, hcv, np, -, nf, -, hc⟩ := h
    cases hc
    obtain ⟨tw, htw, htl, hty⟩ := decCV_type hcv
    have hrd4 : rdW a (q + 4) = tw := by
      simp only [rdW, h4]; rw [show q.toNat + 4 = q.toNat + 1 + 3 by omega, htw]; rfl
    exact ⟨cv, _, _, rfl, by rw [hrd4]; exact hty, by rw [hrd4]; exact htl⟩
  · intro hw cv np nf hc
    subst hc
    have hne : w.toNat ≠ 4 := fun e => hw (UInt64.toNat_inj.mp (by rw [e]; rfl))
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h hne; simp [Option.bind_eq_some_iff] at h hne)

/-! ## Runs of plain triples -/

/-- **A triple applies to a run**: the post holds of the run's result, at a state with the run's
memory and the caller's locals. -/
theorem triple_of_callW {p : Prog} {n : Nat} {f : FnName} {args : List Word} {s₀ : St}
    {Q : List Word → St → Prop}
    (h : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args ⦃fun r s' => Q r s'; ⊤⦄)
    {r : List Word} {m' : Mem} (hc : callW p n f args s₀.mem = some (r, m')) :
    ∃ s', s'.mem = m' ∧ Q r s' := by
  simp only [callW] at hc
  cases hr : (invoke p (exec p n) f args).run { mem := s₀.mem, loc := Locals.init [] } with
  | error e => simp [hr] at hc
  | ok q =>
    simp only [hr, Option.some.injEq] at hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
    have hrun : (invoke p (exec p n) f args).run s₀ = .ok (q.1, { q.2 with loc := s₀.loc }) := by
      rw [invoke_run_loc, hr]; rfl
    exact ⟨{ q.2 with loc := s₀.loc }, rfl, L.M.of_run (P := fun s => s = s₀) rfl hrun h⟩

/-! ## `proj_cert` -/

/-- The model of `proj_cert`, its callees through their runs. -/
def projCertW (p : Prog) (n : Nat) (m : Mem) (vis k ao an : Word) : Option (Word × Mem) :=
  match callW p n "env_find" [k, vis] m with
  | none => none
  | some (r₁, m₁) =>
    if r₁.headD 0 = 0 then some (0, m₁)
    else if rdW (m₁.arr64 EREC) (r₁.tail.headD 0) ≠ 4 then some (0, m₁)
    else match callW p n "peel_pis" [an, rdW (m₁.arr64 EREC) (r₁.tail.headD 0 + 4)] m₁ with
      | none => none
      | some (r₂, m₂) => some (if r₂.headD 0 ≠ 0 then 1 else 0, m₂)

section pc
variable (p : Prog) (n : Nat) (m m₁ m₂ : Mem) (vis k ao an : Word) (r₁ r₂ : List Word)

theorem projCertW_none (h : callW p n "env_find" [k, vis] m = some (r₁, m₁)) (h0 : r₁.headD 0 = 0) :
    projCertW p n m vis k ao an = some (0, m₁) := by
  simp only [projCertW, h, h0, ↓reduceIte]

theorem projCertW_kind (h : callW p n "env_find" [k, vis] m = some (r₁, m₁)) (h0 : ¬ r₁.headD 0 = 0)
    (h4 : rdW (m₁.arr64 EREC) (r₁.tail.headD 0) ≠ 4) :
    projCertW p n m vis k ao an = some (0, m₁) := by
  simp only [projCertW, h, h0, h4, ↓reduceIte, ne_eq, not_false_eq_true]

theorem projCertW_peel (h : callW p n "env_find" [k, vis] m = some (r₁, m₁)) (h0 : ¬ r₁.headD 0 = 0)
    (h4 : ¬ rdW (m₁.arr64 EREC) (r₁.tail.headD 0) ≠ 4)
    (h2 : callW p n "peel_pis" [an, rdW (m₁.arr64 EREC) (r₁.tail.headD 0 + 4)] m₁ = some (r₂, m₂)) :
    projCertW p n m vis k ao an = some (if r₂.headD 0 ≠ 0 then 1 else 0, m₂) := by
  simp only [projCertW, h, h0, h4, h2, ↓reduceIte]

end pc

theorem projCert_spec (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St) (vis k ao an : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proj_cert" [vis, k, ao, an]
    ⦃fun r s' => LocEq s' s₀ ∧ projCertW p n s₀.mem vis k ao an = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.cert]
  simp only [callFn, projCertL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "env_find", callW_spec p n "peel_pis"] <;>
    finish [projCertW_none, projCertW_kind, projCertW_peel]


theorem projCert_run_none (fe : IFEnv) (c : NIdx) (args : List EIdx) (a : AState)
    (h : ∀ cv np nf, fe.find? c ≠ some (.ctorInfo cv np nf)) :
    (projCert fe c args).run a = .ok (false, a) := by
  unfold projCert
  cases e : fe.find? c with
  | none => rfl
  | some ci =>
    cases ci with
    | ctorInfo cv np nf => exact absurd e (h cv np nf)
    | _ => rfl

theorem projCert_run_ctor (fe : IFEnv) (c : NIdx) (args : List EIdx) (a : AState)
    (cv : IConstantVal) (np nf : Nat) (h : fe.find? c = some (.ctorInfo cv np nf)) (o : Option EIdx)
    (hp : (peelPis args.length cv.type).run a = .ok (o, a)) :
    (projCert fe c args).run a = .ok (o.isSome, a) := by
  simp only [projCert, h, teleArityOk, StateT.run_bind, hp, except_ok_bind]; rfl

/-- **`proj_cert` refines `projCert`** (the verified mode's `projCertAt`). -/
@[refines ConRon.Arena.projCert]
theorem projCert_refines (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb k ao an : Word)
    (args : Array EIdx) (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (hk : HW k)
    (har : SpineR s₀.mem ao an args) :
    CoreSpec p (n + 1) "proj_cert" [vis, k, ao, an] (projCert fe (decI k) args.toList) decBool s₀ a₀
      dn vis fe MM eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (projCert_spec p hp n s₀ vis k ao an)
  subst hs0
  refine ⟨hloc, ?_⟩
  simp only [projCertW] at hW
  cases hc : callW p n "env_find" [k, vis] s.mem with
  | none => simp [hc] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  simp only [hc] at hW
  obtain ⟨t₁, ht₁, hm₁, -, hfind⟩ := triple_of_callW
    (envFind_refines p hp.envix hp.envrow hp.envfind n s vis k hS.env hk) hc
  obtain ⟨t₁', ht₁', hm₁', -, hfound⟩ := triple_of_callW
    (envFind_found p hp.envix hp.envrow hp.envfind n s vis k hk) hc
  rw [ht₁] at hm₁
  subst hm₁
  by_cases h0 : r₁.headD 0 = 0
  · rw [if_pos h0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [decFound, h0, ↓reduceIte]
    have hrun' := projCert_run_none fe (decI k) args.toList a₀ (fun cv np nf h => by
      rw [hnone] at h; cases h)
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
    rw [← hm]
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
    · rw [hres]; simp only [decBool]; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg h0] at hW
  obtain ⟨htag, hrow, hq⟩ := hfound h0
  obtain ⟨ci, hci⟩ := hS.env.found_some k hk htag hrow
  have hfind' : fe.find? (decI k) = some ci := by
    rw [hfind]; simp only [decFound, h0, ↓reduceIte, hq]; exact hci
  rw [← hq] at hci
  have hctor := decCI_ctor hci hS.erec
  by_cases h4 : rdW (s.mem.arr64 EREC) (r₁.tail.headD 0) ≠ 4
  · rw [if_pos h4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hrun' := projCert_run_none fe (decI k) args.toList a₀ (fun cv np nf h => by
      rw [hfind'] at h; cases h; exact hctor.2 h4 cv np nf rfl)
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
    rw [← hm]
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
    · rw [hres]; simp only [decBool]; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg h4] at hW
  obtain ⟨cv, np, nf, rfl, hty, htw⟩ := hctor.1 (by simpa using h4)
  cases hc2 : callW p n "peel_pis" [an, rdW (s.mem.arr64 EREC) (r₁.tail.headD 0 + 4)] s.mem with
  | none => rw [hc2] at hW; simp at hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  simp only [hc2, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  obtain ⟨t₂, ht₂, hm₂, -, -, hpeel⟩ := triple_of_callW
    (peelPis_refines p hp.spine n s a₀ hS.arena.1 an _ htw) hc2
  rw [ht₂] at hm₂
  have hlen : args.toList.length = an.toNat := by simp [har.size]
  rw [decE_eq, ← hty, ← hlen] at hpeel
  have hrun' := projCert_run_ctor fe (decI k) args.toList a₀ cv np nf hfind' _ hpeel
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  rw [← hm, hm₂]
  refine ⟨hok, ?_, ?_, ?_⟩
  · rw [hst]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
  · rw [hres]; simp only [decBool]; rw [← hr]; simp only [decOpt]; split <;> simp_all
  · unfold ResH HW; rw [← hr]; split <;> decide

end L.Arena
