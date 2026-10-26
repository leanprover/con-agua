import ConAgua.Arena.PinsNatOp
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
    (hc : rowC m w ≠ 0) : ∃ ci, decCI (erecP m) dn (rowP m w).toNat = some ci := by
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
theorem decCI_ctor {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI a dn q.toNat = some ci) (hab : ArrExt a b)
    (hsz : b.size < 2 ^ 63) :
    (rdW b q = 4 → ∃ cv np nf, ci = .ctorInfo cv np nf ∧ cv.type = decI (rdW b (q + 4)) ∧
      (rdW b (q + 4)).toNat < 2 ^ 32) ∧
    (rdW b q ≠ 4 → ∀ cv np nf, ci ≠ .ctorInfo cv np nf) := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  have hqb := hab _ _ hq
  have hlt : q.toNat < b.size := by
    rcases Nat.lt_or_ge q.toNat b.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at hqb
  have h4 : (q + 4).toNat = q.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have hrd : rdW b q = w := by simp [rdW, hqb]
  rw [hrd]
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  constructor
  · intro hw; subst hw
    simp only [show UInt64.toNat 4 = 4 from rfl, Option.bind_eq_some_iff] at h
    obtain ⟨cv, hcv, np, -, nf, -, hc⟩ := h
    cases hc
    obtain ⟨tw, htw, htl, hty⟩ := decCV_type hcv
    have htwb := hab _ _ htw
    have hrd4 : rdW b (q + 4) = tw := by
      simp only [rdW, h4]; rw [show q.toNat + 4 = q.toNat + 1 + 3 by omega, htwb]; rfl
    exact ⟨cv, _, _, rfl, by rw [hrd4]; exact hty, by rw [hrd4]; exact htl⟩
  · intro hw cv np nf hc
    subst hc
    have hne : w.toNat ≠ 4 := fun e => hw (UInt64.toNat_inj.mp (by rw [e]; rfl))
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h hne; simp [Option.bind_eq_some_iff] at h hne)

/-! ## Runs of plain triples -/

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
  rcases hc : callW p n "env_find" [k, vis] s.mem with _ | ⟨r₁, m₁⟩ <;> simp only [hc, reduceCtorEq] at hW
  obtain ⟨t₁, ht₁, hm₁, -, hfind⟩ := triple_of_callW
    (envFind_refines p hp.envix hp.envrow hp.envfind n s vis k hS.env hk) hc
  obtain ⟨t₁', ht₁', hm₁', -, hfound⟩ := triple_of_callW
    (envFind_found p hp.envix hp.envrow hp.envfind n s vis k hk) hc
  rw [ht₁] at hm₁
  subst hm₁
  by_cases h0 : r₁.headD 0 = 0
  · rw [if_pos h0] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
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
  have hctor := decCI_ctor hci (erecP_ext _) hS.erec
  by_cases h4 : rdW (s.mem.arr64 EREC) (r₁.tail.headD 0) ≠ 4
  · rw [if_pos h4] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
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
  rcases hc2 : callW p n "peel_pis" [an, rdW (s.mem.arr64 EREC) (r₁.tail.headD 0 + 4)] s.mem with _ | ⟨r₂, m₂⟩ <;> simp only [hc2, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hW
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

/-! ## Stack writers keep the relation; slices below the top survive -/

theorem CoreS.frame_stk {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b = SPN)
    (hC : ∀ x ∈ C, x = 136) : CoreS dn m' a vis fe M eb := by
  have aA : ∀ lo hi : Nat, hi ≤ 144 → AvoidA lo hi A := fun lo hi h b hb => by
    have := hA b hb; simp only [SPN, ArrId] at this ⊢; omega
  have aC : ∀ lo hi : Nat, hi ≤ 136 → AvoidC lo hi C := fun lo hi h x hx => by
    have := hA; rw [hC x hx]; right; simpa using h
  exact ⟨⟨ArenaR.frame_ext A C (fun b hb => by rw [hA b hb]; decide)
      (fun x hx => by rw [hC x hx]; decide) m m' hf a hS.arena.1,
      DerR.frameM A C m m' hf (fun b hb => by rw [hA b hb]; decide) a hS.arena.2⟩,
    hS.core.frame (aA 96 128 (by decide)) (aC 96 128 (by decide)) hf,
    hS.pins.congr (hf.1 PINS (fun h => by have := hA _ h; simp [PINS, SPN] at this) (by decide)),
    hS.env.frame (aA 129 144 (by decide)) (aC 128 136 (by decide)) hf
      (fun b hb => by have := hA b hb; simp only [SPN, ArrId] at this ⊢; omega),
    hS.readL, hS.readLs, hS.nwf, hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn,
    hS.memos.frame_hi hf (fun b hb => by rw [hA b hb]; decide) (fun x hx => by rw [hC x hx]; decide)
      (fun b hb => by rw [hA b hb]; decide) (fun x hx => by rw [hC x hx]; decide),
    hf.2.2.1 145 ▸ hS.bstk,
    hS.den.frameE (hf.1 EREC (fun h => by have := hA _ h; simp [EREC, SPN] at this) (by decide)),
    hS.mode.frame hf (fun h => by have := hC _ h; simp at this) (fun h => by have := hC _ h; simp at this)⟩

theorem SpineR.keep {m m' : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (hsz : (m'.arr64 SPN).size = (m.arr64 SPN).size)
    (hk : ∀ i : Word, i < spTop m → spW m' i = spW m i)
    (htop : off.toNat + cnt.toNat ≤ (spTop m).toNat) (hspn : (m.arr64 SPN).size < 2 ^ 63) :
    SpineR m' off cnt xs := by
  have hb := h.bound
  have hlt : ∀ i : Nat, i < cnt.toNat → off + i.toUInt64 < spTop m := by
    intro i hi
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat']
    have : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨h.size, hsz ▸ hb, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hk _ (hlt i hi)]; exact h.lt i hi
  · rw [hk _ (hlt i (h.size ▸ hi))]; exact h.get i hi


/-! ## Stack and word helpers (used by the app arm and `whnf_app`) -/

/-- The top restored after a run that kept everything below the old top. -/
theorem StackKept.restore {m m₁ : Mem} (hk : ∀ i : Word, i < spTop m → spW m₁ i = spW m i)
    (hsz : (m₁.arr64 SPN).size = (m.arr64 SPN).size) (hb : BKept m m₁) (hp : PoolGrew m m₁)
    (h136 : (136 : Word).toNat < (m₁.arr64 CTL).size) :
    StackKept m (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) := by
  have hfs : MemFrame [] [136] m₁ (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) :=
    MemFrame.setCtl m₁ 136 _
  have hspn : (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)).arr64 SPN = m₁.arr64 SPN :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨?_, by rw [hspn, hsz], fun i hi => by simp only [spW, hspn]; exact hk i hi,
    hb.trans (BKept.of_frame hfs (by decide) (by decide)),
    hp.trans (PoolGrew.of_frame hfs (by decide) (by decide))⟩
  simp only [spTop, rdW_set64]
  have : (136 : Word).toNat = 136 := rfl
  simp only [this] at h136
  simp; intro h; omega

/-- The top restored after a run that grew the stack. -/
theorem StackKept.restoreG {m m₁ : Mem} (hg : StackGrew m m₁)
    (h136 : (136 : Word).toNat < (m₁.arr64 CTL).size) :
    StackKept m (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) :=
  StackKept.restore hg.below hg.size hg.bstk hg.pool h136

theorem addW (a b : Word) (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

/-- The twin's second half of the `.app` clause. -/
def whnfCoreApp2T (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (v h : EIdx)
    (args nodes : Array EIdx) : AM WhnfStep := do
  let hv ← headAndArgs v
  whnfApp mode r fe depth v hv.1 hv.2 (v == h) args nodes 0

theorem evalW_eq_ne (v h : Word) (hv : HW v) (hh : HW h) :
    (Cmp.evalW .eq v h != 0) = (decE v == decE h) := by
  rw [decE_eq, decE_eq, decI_beq v h hv hh]
  by_cases e : v = h <;> simp [Cmp.evalW, Cmp.eval, e]

end L.Arena
