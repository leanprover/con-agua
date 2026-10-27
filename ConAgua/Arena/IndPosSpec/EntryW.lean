import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# EntryW

`blk_k3`, `stripW_wrap`, `nestCtorEntryStrip_spec`, `erec_nat`, `erec_hd`, `decCI_kind_cases` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem blk_k3 {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = decFound dn m found q) (h0 : found ≠ 0)
    (hex : ∃ ci, decCI (erecP m) dn q.toNat = some ci) (hk : rdW (m.arr64 EREC) q = 3) :
    hslice? (erA m) (rdW (m.arr64 EREC) (q + 15)).toNat (rdW (m.arr64 EREC) (q + 16)).toNat =
      some (nestBlockOf fe (decI c)) := by
  obtain ⟨ci, hci⟩ := hex
  obtain ⟨k, hkn⟩ : ∃ k, nat? (erecP m) q.toNat = some k := by
    simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hci
    obtain ⟨k, hk, -⟩ := hci
    exact ⟨k, hk⟩
  have hkn' : nat? (erA m) q.toNat = some k := by
    simp only [nat?, Option.map_eq_some_iff] at hkn ⊢
    obtain ⟨w, hw, rfl⟩ := hkn
    exact ⟨w, erecP_get hw, rfl⟩
  have hrd := erN_rdW hkn' q.toNat_lt
  rw [UInt64.ofNat_toNat] at hrd
  have hk3 : k = 3 := by
    have h1 : UInt64.ofNat k = 3 := by rw [← hrd]; exact hk
    have h2 := congrArg UInt64.toNat h1
    rw [UInt64.toNat_ofNat_of_lt' (nat?_lt hkn')] at h2
    simpa using h2
  subst hk3
  obtain ⟨cv, caps, hI, -⟩ := decCI_kind3 hci hkn
  subst hI
  have hb := decCI_indInfo_bound hci
  have hsz := erecP_size_lt m
  have := nestBlockOf_key found q hfound (fun _ => ⟨cv, caps, hci⟩) (fun _ => by omega)
  simpa [h0, hk] using this

section arms
variable (m m1 : Mem) (ciq nPc nF : Word) (r : List Word)
theorem stripW_wrap (h : rdW (m.arr64 EREC) ciq = 4)
    (h2 : rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6) < rdW (m.arr64 EREC) (ciq + 5)) :
    stripW m ciq = none := by
  simp [stripW, h, h2]
end arms
grind_pattern [ind_grind] stripW_wrap => stripW m ciq
theorem nestCtorEntryStrip_spec (p : Prog) (hp : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip)
    (hst : StripProg p) (n : Nat) (s₀ : St) (ciq : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctor_entry_strip" [ciq]
    ⦃fun r s' => LocEq s' s₀ ∧ stripW s₀.mem ciq = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtorEntryStrip]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stripPis_specF p hst n] <;> finish (gen := 20)

theorem erec_nat {m : Mem} {w : Word} {c : Nat} {k : Nat} (h : nat? (erecP m) (w.toNat + c) = some k)
    (hc : c < 2 ^ 64) : rdW (m.arr64 EREC) (w + UInt64.ofNat c) = UInt64.ofNat k ∧ k < 2 ^ 64 := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h
  exact ⟨by rw [erec_rd hv hc]; simp, v.toNat_lt⟩

theorem erec_hd {m : Mem} {w : Word} {c : Nat} {k : IdxKind} {x : Idx k}
    (h : hd? (erecP m) (w.toNat + c) = some x) (hc : c < 2 ^ 64) :
    ∃ v, rdW (m.arr64 EREC) (w + UInt64.ofNat c) = v ∧ v.toNat < 2 ^ 32 ∧ decI v = x := by
  obtain ⟨v, hv, hlt, rfl⟩ := hd?_some h
  exact ⟨v, erec_rd hv hc, hlt, rfl⟩

/-- A record's kind word and, for a constructor, its fields. -/
theorem decCI_kind_cases {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} (h : decCI a dn p = some ci) :
    ∃ k, nat? a p = some k ∧
      ((k = 4 ∧ ∃ cv nPc nF, ci = .ctorInfo cv nPc nF ∧ decCV a (p + 1) = some cv ∧
          nat? a (p + 5) = some nPc ∧ nat? a (p + 6) = some nF) ∨
       (k ≠ 4 ∧ ∀ cv nPc nF, ci ≠ .ctorInfo cv nPc nF)) := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  refine ⟨k, hk, ?_⟩
  match k, h with
  | 0, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 1, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 2, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 3, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 4, h =>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, a1, h1, b1, h2, rfl⟩ := h
    left; exact ⟨rfl, cv, a1, b1, rfl, hcv, h1, h2⟩
  | 5, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 6, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all []
  | (_ + 7), h => simp at h

theorem erecP_ext_grow {m m' : Mem} (hg : IWGrow m m') : ArrExt (erecP m) (erA m') := by
  intro i v hv
  have hlt : i < erTop m := by
    have := (Array.getElem?_eq_some_iff.mp hv).1
    simp only [erecP, Array.size_extract, erecTop] at this
    simp only [erTop]; omega
  rw [erA, hg.2.2.2 i hlt]
  exact erecP_get hv

/-- What `nest_ctor_entry_strip` returns, against the twin's `stripPis` result. -/
def StripOut (m : Mem) (r : List Word) (ciq : Word) (cv : IConstantVal) (nPc nF : Nat) :
    Option (List EIdx × EIdx) → Prop
  | none => r = [0, 0, 0, 0, 0]
  | some (_, b) => ∃ w, r = [1, ciq + 1, UInt64.ofNat nPc, UInt64.ofNat nF, w] ∧ w.toNat < 2 ^ 32 ∧
      decI w = b ∧ decCV (erecP m) (ciq.toNat + 1) = some cv

theorem stripW_ok {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m' : Mem}
    {a : AState} {ciq : Word} {r : List Word} {ci : IConstantInfo}
    (h : stripW m ciq = some (r, m')) (hS : StageR dn vis fe m a)
    (hci : decCI (erecP m) dn ciq.toNat = some ci) :
    (∀ cv nPc nF, ci = .ctorInfo cv nPc nF → nPc + nF < 2 ^ 64 ∧
      ∃ x a', (stripPis (nPc + nF) cv.type).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
        IWGrow m m' ∧ StripOut m r ciq cv nPc nF x) ∧
    ((∀ cv nPc nF, ci ≠ .ctorInfo cv nPc nF) → r = [0, 0, 0, 0, 0] ∧ m' = m) := by
  obtain ⟨k, hk, hcases⟩ := decCI_kind_cases hci
  have hk0 := erec_nat (m := m) (w := ciq) (c := 0) (by simpa using hk) (by decide)
  have e0 : UInt64.ofNat 0 = 0 := rfl
  rw [e0, UInt64.add_zero] at hk0
  rcases hcases with ⟨rfl, cv, nPc, nF, rfl, hcv, hnP, hnF⟩ | ⟨hne, hnc⟩
  · have hker : rdW (m.arr64 EREC) ciq = 4 := by rw [hk0.1]; rfl
    have hP := erec_nat (m := m) (w := ciq) (c := 5) hnP (by decide)
    have hF := erec_nat (m := m) (w := ciq) (c := 6) hnF (by decide)
    have hP' : rdW (m.arr64 EREC) (ciq + 5) = UInt64.ofNat nPc := hP.1
    have hF' : rdW (m.arr64 EREC) (ciq + 6) = UInt64.ofNat nF := hF.1
    by_cases hw : rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6) < rdW (m.arr64 EREC) (ciq + 5)
    · rw [stripW_wrap m ciq hker hw] at h; cases h
    have hsum : nPc + nF < 2 ^ 64 := by
      rw [hP', hF', UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hP.2,
        UInt64.toNat_ofNat_of_lt' hF.2] at hw
      have := hP.2; have := hF.2
      omega
    rw [stripW_ctor m ciq hker hw] at h
    have hty := decCV_type hcv
    rw [Nat.add_assoc] at hty
    obtain ⟨wt, hwt, hwtlt, hwtd⟩ := erec_hd (m := m) (w := ciq) (c := 1 + 3) hty (by decide)
    have e13 : ciq + 1 + 3 = ciq + UInt64.ofNat (1 + 3) := by rw [UInt64.add_assoc]; rfl
    rw [e13, hwt, hP', hF'] at h
    refine ⟨?_, fun hh => absurd rfl (hh cv nPc nF)⟩
    intro cv' nPc' nF' hc
    obtain ⟨rfl, rfl, rfl⟩ : cv = cv' ∧ nPc = nPc' ∧ nF = nF' := by
      simp only [IConstantInfo.ctorInfo.injEq] at hc; exact ⟨hc.1, hc.2.1, hc.2.2⟩
    refine ⟨hsum, ?_⟩
    rcases hs : stripF 6 m [UInt64.ofNat nPc + UInt64.ofNat nF, wt] with _ | ⟨r1, m1⟩ <;> rw [hs] at h; · simp [stripK] at h
    have hk' : (UInt64.ofNat nPc + UInt64.ofNat nF).toNat = nPc + nF := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hP.2, UInt64.toNat_ofNat_of_lt' hF.2]
      exact Nat.mod_eq_of_lt hsum
    obtain ⟨x, a1, hrun, hS1, hg, hdec⟩ :=
      stripF_pis_ok dn vis fe (UInt64.ofNat nPc + UInt64.ofNat nF) wt hwtlt m m1 a r1 hs hS
    rw [hk', hwtd] at hrun
    refine ⟨x, a1, hrun, ?_⟩
    by_cases hz : r1.headD 0 = 0
    · rw [stripK_fail _ _ _ _ _ hz] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      cases x with
      | none => exact ⟨hS1, hg, rfl⟩
      | some xv =>
        obtain ⟨l, e⟩ := xv
        simp only [decOLE] at hdec
        exact absurd hdec.1 (by rw [hz]; decide)
    · rw [stripK_ok _ _ _ _ _ hz] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      cases x with
      | none => simp only [decOLE] at hdec; exact absurd hdec hz
      | some xv =>
        obtain ⟨l, e⟩ := xv
        simp only [decOLE, decW0E] at hdec
        obtain ⟨-, -, hel, hed⟩ := hdec
        refine ⟨hS1, hg, r1.tail.tail.tail.headD 0, rfl, ?_, ?_, ?_⟩
        · rwa [drop3_eq] at hel
        · rwa [drop3_eq] at hed
        · exact hcv
  · have hker : rdW (m.arr64 EREC) ciq ≠ 4 := by
      rw [hk0.1]; intro h4
      have := congrArg UInt64.toNat h4
      rw [UInt64.toNat_ofNat_of_lt' hk0.2] at this
      exact hne (by simpa using this)
    rw [stripW_notctor m ciq hker] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨fun cv nPc nF hc => absurd hc (hnc cv nPc nF), fun _ => ⟨rfl, rfl⟩⟩

theorem nestCtorEntry_spec (p : Prog) (hs : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip)
    (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "nest_ctor_entry" = some nestCtorEntry) (hst : StripProg p) (had : AdF p) (n : Nat) (s₀ : St)
    (C ciq : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctor_entry" [C, ciq]
    ⦃fun r s' => LocEq s' s₀ ∧ entryW s₀.mem C ciq = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtorEntry]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestCtorEntryStrip_spec p hs hst n, gafF_spec p had n, eView_spec p hv n] <;>
      finish (gen := 20) [entryW]

def EntryOut (m' : Mem) (r : List Word) (ciq : Word) : Option (IConstantVal × Nat × Nat) → Prop
  | none => r = [0, 0, 0, 0]
  | some (cv, nPc, nF) => r = [1, ciq + 1, UInt64.ofNat nPc, UInt64.ofNat nF] ∧
      decCVp m' (ciq.toNat + 1) = some cv ∧ nPc + nF < 2 ^ 64

theorem entryW_ok {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m' : Mem}
    {a : AState} {C ciq : Word} {r : List Word} {ci : IConstantInfo} (hC : H C)
    (h : entryW m C ciq = some (r, m')) (hS : StageR dn vis fe m a)
    (hci : decCI (erecP m) dn ciq.toNat = some ci) :
    ∃ x a', (ConRon.Arena.nestCtorEntry (decI C) ci).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ EntryOut m' r ciq x := by
  unfold entryW at h
  rcases h0 : stripW m ciq with _ | ⟨r0, m0⟩ <;> rw [h0] at h; · simp [entryK1] at h
  obtain ⟨hctor, hnon⟩ := stripW_ok h0 hS hci
  by_cases hc : ∃ cv nPc nF, ci = .ctorInfo cv nPc nF
  · obtain ⟨cv, nPc, nF, rfl⟩ := hc
    obtain ⟨hsum, x, a1, hrun1, hS1, hg1, hout⟩ := hctor cv nPc nF rfl
    cases x with
    | none =>
      simp only [StripOut] at hout
      subst hout
      rw [entryK1_fail _ _ _ (by rfl)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨none, a1, ?_, hS1, hg1, rfl⟩
      simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind]
      rw [hrun1]; rfl
    | some xv =>
      obtain ⟨l, b⟩ := xv
      obtain ⟨w, rfl, hwlt, hwd, hcvm0⟩ := hout
      rw [entryK1_ok _ _ _ (by simp)] at h
      simp only [List.tail_cons, List.headD_cons] at h
      rcases hg : gafF m0 [CWF, w] with _ | ⟨r2, m2⟩ <;> rw [hg] at h; · simp [entryK2] at h
      obtain ⟨x2, a2, hrun2, hS2, hg2, hlt2, hdec2⟩ :=
        gafF_ok dn vis fe CWF w hwlt m0 m2 a1 r2 hg hS1
      rw [CWF_eq, hwd] at hrun2
      have htagiff := tag_const_iff (r2.headD 0) hlt2
      rw [hdec2] at htagiff
      by_cases hk : r2.headD 0 >>> 28 ≠ 3
      · rw [entryK2_notconst _ _ _ _ hk] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        refine ⟨none, a2, ?_, hS2, hg1.trans hg2, rfl⟩
        simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind, hrun1, except_ok_bind, hrun2]
        have ht : ¬ (x2.tag == ETag.const) = true := by rw [htagiff]; simpa using hk
        simp only [ht]; rfl
      · rw [entryK2_const _ _ _ _ hk] at h
        have hk3 : r2.headD 0 >>> 28 = 3 := by simpa using hk
        cases hvl : eViewW m2 (r2.headD 0) with
        | nil => rw [hvl] at h; simp [entryK3] at h
        | cons g vt =>
          have hne : eViewW m2 (r2.headD 0) ≠ [] := by rw [hvl]; simp
          rw [hvl] at h
          obtain ⟨v, hv, hvr⟩ := eViewW_ok m2 a2 hS2.1.arena.1 (r2.headD 0) hne
          rw [hvl] at hvr
          have hdE : decE (r2.headD 0) = x2 := hdec2
          have ht : x2.tag = ETag.const := by
            have := htagiff
            rw [show decide (r2.headD 0 >>> 28 = 3) = true by rw [hk3]; decide] at this
            simpa using this
          obtain ⟨n0, us0, rfl⟩ := EStore.view_const a2.store x2 ht v (hdE ▸ hv)
          simp only [ViewR, getD1_eq] at hvr
          obtain ⟨-, hn1, hn2, -, -⟩ := hvr
          simp only [List.tail_cons] at hn1 hn2
          have hview : a2.store.viewConst x2 = some (n0, us0) :=
            EStore.viewConst_of_view _ _ ht n0 us0 (hdE ▸ hv)
          have hbeq : (n0 == decI C) = decide (vt.headD 0 = C) := by
            rw [← hn2]; exact decI_beq' _ _ hn1 hC
          have htwin : (ConRon.Arena.nestCtorEntry (decI C) (.ctorInfo cv nPc nF)).run a =
              .ok (if vt.headD 0 = C then some (cv, nPc, nF) else none, a2) := by
            simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind, hrun1, except_ok_bind, hrun2, ht, beq_self_eq_true, ite_true, viewConst_run, hview, hbeq]
            by_cases hcn : vt.headD 0 = C
            · simp only [hcn, decide_true, ite_true]; rfl
            · simp only [hcn, decide_false]; rfl
          by_cases hcn : vt.headD 0 = C
          · rw [entryK3_hit _ _ _ _ (by simp) (by simpa using hcn)] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
            refine ⟨_, a2, htwin, hS2, hg1.trans hg2, ?_⟩
            simp only [hcn, ite_true, EntryOut]
            exact ⟨rfl, (erecP_ext_grow (hg1.trans hg2)).decCV hcvm0, hsum⟩
          · rw [entryK3_miss _ _ _ _ (by simp) (by simpa using hcn)] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
            refine ⟨_, a2, htwin, hS2, hg1.trans hg2, ?_⟩
            simp only [hcn, ite_false, EntryOut]
  · have hne : ∀ cv nPc nF, ci ≠ .ctorInfo cv nPc nF := fun cv n f hh => hc ⟨cv, n, f, hh⟩
    obtain ⟨rfl, rfl⟩ := hnon hne
    rw [entryK1_fail _ _ _ (by rfl)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
    cases ci with
    | ctorInfo cv n f => exact absurd ⟨cv, n, f, rfl⟩ hc
    | _ => rfl

theorem resHeadK_some (r : List Word) (m1 : Mem) :
    resHeadK (some (r, m1)) = some ([if r.headD 0 >>> 28 = 1 then 1 else 0], m1) := rfl
grind_pattern [ind_grind] resHeadK_some => resHeadK (some (r, m1))

theorem nestResHead_spec (p : Prog) (hg : p.lookup "nest_res_head" = some nestResHeadL) (had : AdF p) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_res_head" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ resHeadW s₀.mem e = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hg, callFn, nestResHeadL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        gafF_spec p had n] <;> finish [resHeadW]

theorem resHeadW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem) (a : AState)
    (e : Word) (r : List Word) (he : H e) (h : resHeadW m e = some (r, m')) (hS : StageR dn vis fe m a) :
    ∃ a', (ConRon.Arena.nestResHead (decI e)).run a = .ok (r.headD 0 != 0, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  unfold resHeadW at h
  rcases hs : gafF m [CWF, e] with _ | ⟨r1, m1⟩ <;> rw [hs] at h; · simp [resHeadK] at h
  simp only [resHeadK, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨x, a1, hrun, hS1, hg, hlt, hdec⟩ := gafF_ok dn vis fe CWF e he m m1 a r1 hs hS
  refine ⟨a1, ?_, hS1, hg⟩
  rw [CWF_eq] at hrun
  have htag : (x.tag == ETag.fvar) = decide (r1.headD 0 >>> 28 = 1) := by
    rw [← hdec]
    have := decE_tag_eq (r1.headD 0) hlt 1 (by decide)
    have e1 : (ETag.fvar : UInt32) = UInt32.ofNat 1 := rfl
    show ((decE (r1.headD 0)).tag == ETag.fvar) = _
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e1, this]
    exact Iff.rfl
  simp only [ConRon.Arena.nestResHead, StateT.run_bind]
  rw [hrun]
  simp only [bind, Except.bind, pure, htag]
  show (StateT.pure (decide (r1.headD 0 >>> 28 = 1))).run a1 = _
  generalize r1.headD 0 = w
  by_cases hc : w >>> 28 = 1 <;> simp [hc, StateT.pure, StateT.run, pure, Except.pure]

end L.Ind

end
