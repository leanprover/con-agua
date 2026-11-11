module

public import ConAgua.Arena.IndPosSpec.NestBlockOfKey
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import ConAgua.L.ModelGen
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2
import ConAgua.L.WordOff
import ConAgua.Arena.IndPartsSpec.RecTW

@[expose] public section

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

theorem blk_k3 {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = envFound m found q) (h0 : found ≠ 0)
    (hex : ∃ ci, decCI (erecP m) q.toNat = some ci) (hk : erRd m q = 3) :
    hslice? (erA m) (erRd m (q + 15)).toNat (erRd m (q + 16)).toNat =
      some (nestBlockOf fe (decI c)) := by
  have := nestBlockOf_key found q hfound (fun _ => hex)
  simpa [h0, hk] using this

l_model nestCtorEntryStrip_spec (p : Prog) (hp : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip)
    (hst : StripProg p)
  fns [hp ↦ stripW list]
  specs [stripPis_specF p hst n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

theorem erec_nat {m : Mem} {w : Word} {c : Nat} {k : Nat} (h : nat? (erecP m) (w.toNat + c) = some k)
    (hc : c < 2 ^ 64) : erRd m (w + UInt64.ofNat c) = UInt64.ofNat k ∧ k < 2 ^ 64 := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h
  exact ⟨by rw [erec_rd hv hc]; simp, v.toNat_lt⟩

theorem erec_hd {m : Mem} {w : Word} {c : Nat} {k : IdxKind} {x : Idx k}
    (h : hd? (erecP m) (w.toNat + c) = some x) (hc : c < 2 ^ 64) :
    ∃ v, erRd m (w + UInt64.ofNat c) = v ∧ v.toNat < 2 ^ 32 ∧ decI v = x := by
  obtain ⟨v, hv, hlt, rfl⟩ := hd?_some h
  exact ⟨v, erec_rd hv hc, hlt, rfl⟩

/-- A record's kind word and, for a constructor, its fields. -/
theorem decCI_kind_cases {a : Nat → Option Word} {p : Nat}
    {ci : IConstantInfo} (h : decCI a p = some ci) :
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

theorem erecP_ext_grow {m m' : Mem} (hg : IWGrow m m') : ArrExt (erecP m) (erA m') := hg.ext

/-- What `nest_ctor_entry_strip` returns, against the twin's `stripPis` result. -/
def StripOut (m : Mem) (r : List Word) (ciq : Word) (cv : IConstantVal) (nPc nF : Nat) :
    Option (List EIdx × EIdx) → Prop
  | none => r = [0, 0, 0, 0, 0]
  | some (_, b) => ∃ w, r = [1, ciq + 1, UInt64.ofNat nPc, UInt64.ofNat nF, w] ∧ w.toNat < 2 ^ 32 ∧
      decI w = b ∧ decCV (erecP m) (ciq.toNat + 1) = some cv

theorem stripW_ok {fe : IFEnv} {vis : Word} {m m' : Mem}
    {a : AState} {ciq : Word} {r : List Word} {ci : IConstantInfo}
    (h : stripW m ciq = some (r, m')) (hS : StageR vis fe m a)
    (hci : decCI (erecP m) ciq.toNat = some ci) :
    (∀ cv nPc nF, ci = .ctorInfo cv nPc nF → nPc + nF < 2 ^ 64 ∧
      ∃ x a', (stripPis (nPc + nF) cv.type).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
        IWGrow m m' ∧ StripOut m r ciq cv nPc nF x) ∧
    ((∀ cv nPc nF, ci ≠ .ctorInfo cv nPc nF) → r = [0, 0, 0, 0, 0] ∧ m' = m) := by
  obtain ⟨k, hk, hcases⟩ := decCI_kind_cases hci
  have hk0 := erec_nat (m := m) (w := ciq) (c := 0) (by simpa using hk) (by decide)
  have e0 : UInt64.ofNat 0 = 0 := rfl
  rw [e0, UInt64.add_zero] at hk0
  rcases hcases with ⟨rfl, cv, nPc, nF, rfl, hcv, hnP, hnF⟩ | ⟨hne, hnc⟩
  · have hker : erRd m ciq = 4 := by rw [hk0.1]; rfl
    have hP := erec_nat (m := m) (w := ciq) (c := 5) hnP (by decide)
    have hF := erec_nat (m := m) (w := ciq) (c := 6) hnF (by decide)
    have hP' : erRd m (ciq + 5) = UInt64.ofNat nPc := hP.1
    have hF' : erRd m (ciq + 6) = UInt64.ofNat nF := hF.1
    by_cases hw : erRd m (ciq + 5) + erRd m (ciq + 6) < erRd m (ciq + 5)
    · rw [stripW.abort1 (hc1 := hker) (hc2 := hw)] at h; cases h
    have hsum : nPc + nF < 2 ^ 64 := by
      rw [hP', hF', UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hP.2,
        UInt64.toNat_ofNat_of_lt' hF.2] at hw
      have := hP.2; have := hF.2
      omega
    rw [stripW.arm2 (hc1 := hker) (hc2 := hw)] at h
    simp only [erRd_foldN] at h
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
    rcases hs : stripF 6 m [UInt64.ofNat nPc + UInt64.ofNat nF, wt] with _ | ⟨r1, m1⟩ <;> rw [hs] at h; · rw [stripW.k_strip_pis.none] at h; cases h
    have hk' : (UInt64.ofNat nPc + UInt64.ofNat nF).toNat = nPc + nF := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hP.2, UInt64.toNat_ofNat_of_lt' hF.2]
      exact Nat.mod_eq_of_lt hsum
    obtain ⟨x, a1, hrun, hS1, hg, hdec⟩ :=
      stripF_pis_ok vis fe (UInt64.ofNat nPc + UInt64.ofNat nF) wt hwtlt m m1 a r1 hs hS
    rw [hk', hwtd] at hrun
    refine ⟨x, a1, hrun, ?_⟩
    by_cases hz : r1.headD 0 = 0
    · rw [stripW.k_strip_pis.arm1 (hc1 := hz)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      cases x with
      | none => exact ⟨hS1, hg, rfl⟩
      | some xv =>
        obtain ⟨l, e⟩ := xv
        simp only [decOLE] at hdec
        exact absurd hdec.1 (by rw [hz]; decide)
    · rw [stripW.k_strip_pis.arm2 (hc1 := hz)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      cases x with
      | none => simp only [decOLE] at hdec; exact absurd hdec hz
      | some xv =>
        obtain ⟨l, e⟩ := xv
        simp only [decOLE, decW0E] at hdec
        obtain ⟨-, -, hel, hed⟩ := hdec
        refine ⟨hS1, hg, r1.tail.tail.tail.headD 0, rfl, ?_, ?_, ?_⟩
        · rwa [L.drop_three] at hel
        · rwa [L.drop_three] at hed
        · exact hcv
  · have hker : erRd m ciq ≠ 4 := by
      rw [hk0.1]; intro h4
      have := congrArg UInt64.toNat h4
      rw [UInt64.toNat_ofNat_of_lt' hk0.2] at this
      exact hne (by simpa using this)
    rw [stripW.arm1 (hc1 := hker)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨fun cv nPc nF hc => absurd hc (hnc cv nPc nF), fun _ => ⟨rfl, rfl⟩⟩

l_model nestCtorEntry_spec (p : Prog) (hs : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip)
    (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "nest_ctor_entry" = some nestCtorEntry) (hst : StripProg p) (had : AdF p)
  fns [hp ↦ entryW list]
  specs [nestCtorEntryStrip_spec p hs hst n, gafF_spec p had n, eView_spec p hv n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

def EntryOut (m' : Mem) (r : List Word) (ciq : Word) : Option (IConstantVal × Nat × Nat) → Prop
  | none => r = [0, 0, 0, 0]
  | some (cv, nPc, nF) => r = [1, ciq + 1, UInt64.ofNat nPc, UInt64.ofNat nF] ∧
      decCVp m' (ciq.toNat + 1) = some cv ∧ nPc + nF < 2 ^ 64

theorem entryW_ok {fe : IFEnv} {vis : Word} {m m' : Mem}
    {a : AState} {C ciq : Word} {r : List Word} {ci : IConstantInfo} (hC : H C)
    (h : entryW m C ciq = some (r, m')) (hS : StageR vis fe m a)
    (hci : decCI (erecP m) ciq.toNat = some ci) :
    ∃ x a', (ConRon.Arena.nestCtorEntry (decI C) ci).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ EntryOut m' r ciq x := by
  rw [entryW.arm1] at h
  rcases h0 : stripW m ciq with _ | ⟨r0, m0⟩ <;> rw [h0] at h
  · rw [entryW.k_nest_ctor_entry_strip.none] at h; cases h
  obtain ⟨hctor, hnon⟩ := stripW_ok h0 hS hci
  by_cases hc : ∃ cv nPc nF, ci = .ctorInfo cv nPc nF
  · obtain ⟨cv, nPc, nF, rfl⟩ := hc
    obtain ⟨hsum, x, a1, hrun1, hS1, hg1, hout⟩ := hctor cv nPc nF rfl
    cases x with
    | none =>
      simp only [StripOut] at hout
      subst hout
      rw [entryW.k_nest_ctor_entry_strip.arm1 (hc1 := rfl)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨none, a1, ?_, hS1, hg1, rfl⟩
      simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind]
      rw [hrun1]; rfl
    | some xv =>
      obtain ⟨l, b⟩ := xv
      obtain ⟨w, rfl, hwlt, hwd, hcvm0⟩ := hout
      rw [entryW.k_nest_ctor_entry_strip.arm2 (hc1 := by simp)] at h
      simp only [List.tail_cons, List.headD_cons] at h
      rcases hg : gafF m0 [CWF, w] with _ | ⟨r2, m2⟩ <;> rw [hg] at h; · rw [entryW.k_get_app_fn_f.none] at h; cases h
      obtain ⟨x2, a2, hrun2, hS2, hg2, hlt2, hdec2⟩ :=
        gafF_ok vis fe CWF w hwlt m0 m2 a1 r2 hg hS1
      rw [CWF_eq, hwd] at hrun2
      have htagiff := decI_tag_const_beq (r2.headD 0) hlt2
      rw [hdec2] at htagiff
      by_cases hk : tagW (r2.headD 0) ≠ 3
      · rw [entryW.k_get_app_fn_f.arm1 (hc1 := hk)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        refine ⟨none, a2, ?_, hS2, hg1.trans hg2, rfl⟩
        simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind, hrun1, except_ok_bind, hrun2]
        have ht : ¬ (x2.tag == ETag.const) = true := by rw [htagiff]; simpa using hk
        simp only [ht]; rfl
      · have hk3 : tagW (r2.headD 0) = 3 := by simpa using hk
        cases hvl : eViewW m2 (r2.headD 0) with
        | nil => rw [entryW.k_get_app_fn_f.abort1 (hc1 := hk3) (hc2 := hvl)] at h; cases h
        | cons g vt =>
          have hne : eViewW m2 (r2.headD 0) ≠ [] := by rw [hvl]; simp
          obtain ⟨v, hv, hvr⟩ := eViewW_ok m2 a2 hS2.check.arena.base (r2.headD 0) hne
          rw [hvl] at hvr
          have hdE : decE (r2.headD 0) = x2 := hdec2
          have ht : x2.tag = ETag.const := by
            have := htagiff
            rw [show decide (tagW (r2.headD 0) = 3) = true by rw [hk3]; decide] at this
            simpa using this
          obtain ⟨n0, us0, rfl⟩ := EStore.view_const a2.store x2 ht v (hdE ▸ hv)
          simp only [ViewR, L.getD_one] at hvr
          obtain ⟨-, hn1, hn2, -, -⟩ := hvr
          simp only [List.tail_cons] at hn1 hn2
          have hview : a2.store.viewConst x2 = some (n0, us0) :=
            EStore.viewConst_of_view _ _ ht n0 us0 (hdE ▸ hv)
          have hbeq : (n0 == decI C) = decide (vt.headD 0 = C) := by
            rw [← hn2]; exact decI_beq _ _ hn1 hC
          have htwin : (ConRon.Arena.nestCtorEntry (decI C) (.ctorInfo cv nPc nF)).run a =
              .ok (if vt.headD 0 = C then some (cv, nPc, nF) else none, a2) := by
            simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind, hrun1, except_ok_bind, hrun2, ht, beq_self_eq_true, ite_true, L.Ind.viewConst_run, hview, hbeq]
            by_cases hcn : vt.headD 0 = C
            · simp only [hcn, decide_true, ite_true]; rfl
            · simp only [hcn, decide_false]; rfl
          by_cases hcn : vt.headD 0 = C
          · rw [entryW.k_get_app_fn_f.arm3 (hc1 := hk3) (hc2 := hne) (hc3 := by rw [hvl]; simpa using hcn)] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
            refine ⟨_, a2, htwin, hS2, hg1.trans hg2, ?_⟩
            simp only [hcn, ite_true, EntryOut]
            exact ⟨by trivial, (erecP_ext_grow (hg1.trans hg2)).decCV hcvm0, hsum⟩
          · rw [entryW.k_get_app_fn_f.arm2 (hc1 := hk3) (hc2 := hne) (hc3 := by rw [hvl]; simpa using hcn)] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
            refine ⟨_, a2, htwin, hS2, hg1.trans hg2, ?_⟩
            simp only [hcn, ite_false, EntryOut]
  · have hne : ∀ cv nPc nF, ci ≠ .ctorInfo cv nPc nF := fun cv n f hh => hc ⟨cv, n, f, hh⟩
    obtain ⟨rfl, rfl⟩ := hnon hne
    rw [entryW.k_nest_ctor_entry_strip.arm1 (hc1 := rfl)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
    cases ci with
    | ctorInfo cv n f => exact absurd ⟨cv, n, f, rfl⟩ hc
    | _ => rfl

l_model nestResHead_spec (p : Prog) (hg : p.lookup "nest_res_head" = some nestResHeadL) (had : AdF p)
  fns [hg ↦ resHeadW list]
  specs [gafF_spec p had n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

theorem resHeadW_ok (_dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem) (a : AState)
    (e : Word) (r : List Word) (he : H e) (h : resHeadW m e = some (r, m')) (hS : StageR vis fe m a) :
    ∃ a', (ConRon.Arena.nestResHead (decI e)).run a = .ok (r.headD 0 != 0, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' := by
  rw [resHeadW.arm1] at h
  rcases hs : gafF m [CWF, e] with _ | ⟨r1, m1⟩ <;> rw [hs] at h; · rw [resHeadW.k_get_app_fn_f.none] at h; cases h
  simp only [resHeadW.k_get_app_fn_f.arm1, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨x, a1, hrun, hS1, hg, hlt, hdec⟩ := gafF_ok vis fe CWF e he m m1 a r1 hs hS
  refine ⟨a1, ?_, hS1, hg⟩
  rw [CWF_eq] at hrun
  have htag : (x.tag == ETag.fvar) = decide (tagW (r1.headD 0) = 1) := by
    rw [← hdec]
    have := decE_tag_eq (r1.headD 0) hlt 1 (by decide)
    have e1 : (ETag.fvar : UInt32) = UInt32.ofNat 1 := rfl
    show ((decE (r1.headD 0)).tag == ETag.fvar) = _
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e1, this]
    exact Iff.rfl
  simp only [ConRon.Arena.nestResHead, StateT.run_bind]
  rw [hrun]
  simp only [bind, Except.bind, pure, htag]
  show (StateT.pure (decide (tagW (r1.headD 0) = 1))).run a1 = _
  generalize r1.headD 0 = w
  by_cases hc : tagW w = 1 <;> simp [hc, StateT.pure, StateT.run, pure, Except.pure]

end L.Ind

end
