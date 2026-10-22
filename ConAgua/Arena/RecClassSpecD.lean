import ConAgua.Arena.RecClassSpecC

/-!
# `RecClass`: `classReadMinor`'s relational lemmas (lane `indproofs2`, helper `rec`)

The callee simulations (`sim*`: a stub's `RelAM`, a translated callee's relational lemma, in
`RSim` form with the twin's own spelling, `coreWalkFuel` for `CWF`), then `RSim` chains.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Callee simulations -/

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}

theorem simFvarTypeD (hS : StageR dn vis fe m a) {e : Word} (he : H e) :
    RSim (stubM "fvar_type_d" m [e]) (fvarTypeD (decI e)) a (KP dn vis fe m decW0E) :=
  (fvarTypeD_spec dn vis fe e he).sim hS

theorem simPiResult (hS : StageR dn vis fe m a) {e : Word} (he : H e) :
    RSim (stubM "pi_result_f" m [CWF, e]) (piResult coreWalkFuel (decI e)) a (KP dn vis fe m decW0E) := by
  have h := (piResult_spec dn vis fe CWF e he).sim hS; rw [CWF_eq] at h; exact h

theorem simGetAppFn (hS : StageR dn vis fe m a) {e : Word} (he : H e) :
    RSim (stubM "get_app_fn_f" m [CWF, e]) (getAppFn coreWalkFuel (decI e)) a (KP dn vis fe m decW0E) := by
  have h := (getAppFn_spec dn vis fe CWF e he).sim hS; rw [CWF_eq] at h; exact h

theorem simGetAppArgs (hS : StageR dn vis fe m a) {e : Word} (he : H e) :
    RSim (stubM "get_app_args_f" m [CWF, e]) (getAppArgs coreWalkFuel (decI e)) a
      (KP dn vis fe m (decRL (fun m => decHL m) 0)) := by
  have h := (getAppArgs_spec dn vis fe CWF e he).sim hS; rw [CWF_eq] at h; exact h

theorem simOpenPis (hS : StageR dn vis fe m a) {k e i : Word} (he : H e) :
    RSim (stubM "open_pis_at_fvars_f" m [k, e, i]) (openPisAtFvarsF k.toNat (decI e) i.toNat) a
      (KP dn vis fe m decOLE) :=
  (openPisAtFvarsF_spec dn vis fe k e i he).sim hS

/-- `fvar_head`'s result. -/
def decFH (r : List Word) : Option Nat → Prop
  | none => r = [0, 0]
  | some i => r = [1, UInt64.ofNat i] ∧ i < 2 ^ 64

theorem simFvarHead (hS : StageR dn vis fe m a) {e : Word} (he : H e) :
    RSim (fvarHeadW m e) (ConRon.Arena.fvarHead (decI e)) a
      (fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ decFH b.1 x) := by
  rintro ⟨r, m'⟩ h
  obtain ⟨x, a', hrun, hS', hg, hr, hb⟩ := fvarHeadW_ok dn vis fe m m' a e he r h hS
  refine ⟨x, a', hrun, hS', hg, ?_⟩
  cases x with
  | none => exact hr
  | some i => exact ⟨hr, hb i rfl⟩

end sims

/-! ## Reading the last element of a decoded slice -/

theorem decHL_last {k : IdxKind} {m : Mem} {wo wl : Word} {xs : List (Idx k)}
    (h : decHL m wo.toNat wl.toNat = some xs) (hl : wl ≠ 0) (hb : wo.toNat + wl.toNat < 2 ^ 64) :
    ∃ w, rdW (m.arr64 IW) (wo + wl - 1) = w ∧ H w ∧ xs.getLast? = some (decI w) := by
  have hl0 : wl.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  have hlen := decHL_length m h
  obtain ⟨w, h1, h2, h3⟩ := decHL_get' h (wl.toNat - 1) (by omega) (by omega)
  have he : UInt64.ofNat (wo.toNat + (wl.toNat - 1)) = wo + wl - 1 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega), UInt64.toNat_sub_of_le _ _ ?_, UInt64.toNat_add]
    · simp; omega
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]; simp; omega
  rw [he] at h1
  refine ⟨w, h1, h2, ?_⟩
  rw [List.getLast?_eq_getElem?, hlen, ← h3]
  exact List.getElem?_eq_getElem _

/-! ## `class_read_minor_ih1` -/

/-- The twin's `filterMapM` body in `classReadMinor`. -/
def ihStep (nP : Nat) (motPos : List Nat) (d : Nat) (x : EIdx) : AM (Option (Nat × Nat)) := do
  let ty ← fvarTypeD x
  let r ← piResult coreWalkFuel ty
  match ← ConRon.Arena.fvarHead r with
  | none => pure none
  | some p2 =>
    match ConRon.Arena.classOfMotiveVar nP motPos p2 with
    | none => pure none
    | some t => do
      let rargs ← getAppArgs coreWalkFuel r
      match rargs.getLast? with
      | none => pure none
      | some a =>
        match ← ConRon.Arena.fvarHead a with
        | none => pure none
        | some f => pure (if d ≤ f then some (f - d, t) else none)

/-- `class_read_minor_ih1`'s result. -/
def decIH (_m : Mem) (r : List Word) : Option (Nat × Nat) → Prop
  | none => r.headD 0 = 0
  | some (f, t) => r = [1, UInt64.ofNat f, UInt64.ofNat t] ∧ f < 2 ^ 64 ∧ t < 2 ^ 64

theorem ofNat_sub_word (f : Nat) (d : Word) (hf : f < 2 ^ 64) (hd : d.toNat ≤ f) :
    UInt64.ofNat f - d = UInt64.ofNat (f - d.toNat) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hf]; exact hd),
    UInt64.toNat_ofNat_of_lt' hf, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]

theorem ih1W_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (nP mo ml d x : Word) (motPos : List Nat) (hS : StageR dn vis fe m a) (hx : H x)
    (hmot : decNL m mo.toNat ml.toNat = some motPos) (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (ih1W n m nP mo ml d x) (ihStep nP.toNat motPos d.toNat (decI x)) a (KP dn vis fe m decIH) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  have hmb : mo.toNat + ml.toNat < 2 ^ 64 := by
    have := hS.2.1; have := hS.2.2.2.1; omega
  refine RSim.bind (K := ih1K1 n nP mo ml d) rfl (simFvarTypeD hS hx) ?_
  rintro ⟨r1, m1⟩ ty a1 - ⟨hS1, hg1, hb1, rfl⟩
  refine RSim.bind (K := ih1K2 n nP mo ml d) rfl (simPiResult hS1 hb1) ?_
  rintro ⟨r2, m2⟩ ty2 a2 - ⟨hS2, hg2, hb2, rfl⟩
  refine RSim.bind (K := ih1K3 n nP mo ml d (r2.headD 0)) rfl (simFvarHead hS2 hb2) ?_
  rintro ⟨r3, m3⟩ x3 a3 - ⟨hS3, hg3, hx3⟩
  have hg13 := (hg1.trans hg2).trans hg3
  cases x3 with
  | none =>
    simp only [decFH] at hx3; subst hx3
    rw [ih1K3_fail (h := rfl)]
    exact RSim.pure_some ⟨hS3, hg13, rfl⟩
  | some p2 =>
    obtain ⟨rfl, hp2⟩ := hx3
    rw [ih1K3_ok (h := by simp)]
    refine RSim.lstep (K := ih1K4 d (r2.headD 0) m3) rfl fun r4 h4 => ?_
    have hmot3 : decNL m3 mo.toNat ml.toNat = some motPos := by rw [decNL_grow hg13 hmt]; exact hmot
    have hc := cmvW_ok (n - 1) m3 nP mo ml _ r4 motPos hmot3 hmb h4
    simp only [List.tail_cons, List.headD_cons, UInt64.toNat_ofNat_of_lt' hp2] at hc
    show RSim _ (match ConRon.Arena.classOfMotiveVar nP.toNat motPos p2 with
      | none => pure none
      | some t => _) a3 _
    cases hcm : ConRon.Arena.classOfMotiveVar nP.toNat motPos p2 with
    | none =>
      rw [hcm] at hc; subst hc
      rw [ih1K4_fail (h := rfl)]
      exact RSim.pure_some ⟨hS3, hg13, rfl⟩
    | some t =>
      rw [hcm] at hc; subst hc
      have ht : t < 2 ^ 64 := by
        have := cmv_lt _ _ _ _ hcm; have := decNL_length m3 hmot3; omega
      rw [ih1K4_ok (h := by simp)]
      simp only [List.tail_cons, List.headD_cons]
      refine RSim.bind (K := ih1K5 d (UInt64.ofNat t)) rfl (simGetAppArgs hS3 hb2) ?_
      rintro ⟨r5, m5⟩ rargs a5 - ⟨hS5, hg5, hd5, ht5⟩
      simp only [Nat.zero_add, getD_zero, getD_one] at hd5 ht5
      have hg15 := hg13.trans hg5
      have hb5 : (r5.headD 0).toNat + (r5.tail.headD 0).toNat < 2 ^ 64 := by
        have h1 : iwTop m5 ≤ (m5.arr64 IW).size := hS5.2.1
        have h2 : (m5.arr64 IW).size < 2 ^ 64 := hS5.2.2.2.1
        omega
      by_cases hz : r5.tail.headD 0 = 0
      · rw [ih1K5_fail (h := hz)]
        have hnil : rargs = [] := by
          have := decHL_length m5 hd5; rw [hz] at this; exact List.eq_nil_of_length_eq_zero this
        subst hnil
        exact RSim.pure_some ⟨hS5, hg15, rfl⟩
      obtain ⟨w, hw, hH, hlast⟩ := decHL_last hd5 hz hb5
      rw [ih1K5_ok (h := hz), hw, hlast]
      refine RSim.bind (K := ih1K6 d (UInt64.ofNat t)) rfl (simFvarHead hS5 hH) ?_
      rintro ⟨r6, m6⟩ x6 a6 - ⟨hS6, hg6, hx6⟩
      have hg16 := hg15.trans hg6
      cases x6 with
      | none =>
        simp only [decFH] at hx6; subst hx6
        rw [ih1K6_fail (h := rfl)]
        exact RSim.pure_some ⟨hS6, hg16, rfl⟩
      | some f =>
        obtain ⟨rfl, hf⟩ := hx6
        by_cases hlt : UInt64.ofNat f < d
        · rw [ih1K6_lt (h := by simp) (h2 := hlt)]
          have hlt' : ¬ d.toNat ≤ f := by
            have := UInt64.lt_iff_toNat_lt.mp hlt; rw [UInt64.toNat_ofNat_of_lt' hf] at this; omega
          refine RSim.pure_some ⟨hS6, hg16, ?_⟩
          rw [ite_cond_eq_false _ _ (eq_false hlt')]; rfl
        · rw [ih1K6_ok (h := by simp) (h2 := hlt)]
          have hle : d.toNat ≤ f := by
            have := (UInt64.not_lt).mp hlt; rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hf] at this
            exact this
          refine RSim.pure_some ⟨hS6, hg16, ?_⟩
          rw [ite_cond_eq_true _ _ (eq_true hle)]
          refine ⟨?_, by omega, ht⟩
          simp only [List.tail_cons, List.headD_cons, ofNat_sub_word f d hf hle]

/-! ## Records under the stage relation -/

/-- **A fresh record keeps the stage relation**: the pointer is the old top, the words are
there, the pool grew. -/
theorem recW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {k : Word} {ws r : List Word} (h : recW m k ws = some (r, m'))
    (hS : StageR dn vis fe m a) (hk : k.toNat = ws.length) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ r = [rdW (m.arr64 CTL) 200] ∧
    (∀ j < ws.length, (m'.arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? = ws[j]?) ∧
    iwTop m' = iwTop m + ws.length := by
  obtain ⟨hr, hget, hg, hf, htop, hroom⟩ := recW_post h hS.2.2.2.2.2 hS.2.2.2.1 hk
  refine ⟨stage_frame_iw hS hf (by omega), hg, hr, hget, htop⟩

/-- A word of a fresh record, read stably. -/
theorem rec_iwN_stab {m m' : Mem} {ws : List Word} {q : Word} (hq : q = rdW (m.arr64 CTL) 200)
    (hget : ∀ j < ws.length, (m'.arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? = ws[j]?)
    (htop : iwTop m' = iwTop m + ws.length) (j : Nat) (hj : j < ws.length) :
    StabD (fun m => iwN m (q.toNat + j)) m' (ws[j]'hj).toNat := by
  subst hq
  have hlt : (rdW (m.arr64 CTL) 200).toNat + j < iwTop m' := by rw [htop]; simp [iwTop]; omega
  refine StabD.of_eq (fun m'' hg => iwN_grow hg hlt) ?_
  simp only [iwN, nat?, iwA, hget j hj, List.getElem?_eq_getElem hj, Option.map_some]

theorem decNN_stab {m : Mem} {q x y : Nat} (h1 : StabD (fun m => iwN m q) m x)
    (h2 : StabD (fun m => iwN m (q + 1)) m y) : StabD (fun m => decNN m q) m (x, y) := by
  intro m' hg
  simp only [decNN, h1 m' hg, h2 m' hg]; rfl

/-- The stable record `[a, b]` built by `rec2`. -/
theorem rec2_decNN {m m' : Mem} {a b q : Word} (hq : q = rdW (m.arr64 CTL) 200)
    (hget : ∀ j < [a, b].length, (m'.arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? = [a, b][j]?)
    (htop : iwTop m' = iwTop m + [a, b].length) :
    StabD (fun m => decNN m q.toNat) m' (a.toNat, b.toNat) :=
  decNN_stab (by simpa using rec_iwN_stab hq hget htop 0 (by simp))
    (by simpa using rec_iwN_stab hq hget htop 1 (by simp))

/-! ## `class_read_minor_ihs` -/

/-- `class_read_minor_ihs`'s result: a stable slice of `[field, class]` records. -/
def decIHS (m' : Mem) (r : List Word) (ihs : List (Nat × Nat)) : Prop :=
  SPL decNN m' (r.headD 0).toNat (r.tail.headD 0).toNat ihs

theorem ihsW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (nP mo ml d : Word)
    (motPos : List Nat) (n : Nat) : ∀ (m : Mem) (a : AState) (fo fl : Word) (fvs : List EIdx),
    StageR dn vis fe m a → decHL m fo.toNat fl.toNat = some fvs → fo.toNat + fl.toNat ≤ iwTop m →
    decNL m mo.toNat ml.toNat = some motPos → mo.toNat + ml.toNat ≤ iwTop m →
    RSim (ihsW n m nP mo ml d fo fl) (fvs.filterMapM (ihStep nP.toNat motPos d.toNat)) a
      (KP dn vis fe m decIHS) := by
  induction n with
  | zero => intro m a fo fl fvs _ _ _ _ _; exact RSim.of_none (by rw [ihsW])
  | succ n ih =>
  intro m a fo fl fvs hS hfvs hft hmot hmt
  have hfb : fo.toNat + fl.toNat < 2 ^ 64 := by
    have h1 : iwTop m ≤ (m.arr64 IW).size := hS.2.1
    have h2 : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
    omega
  by_cases hfl : fl = 0
  · rw [ihsW_nil (h := hfl)]
    have hnil : fvs = [] := by
      have := decHL_length m hfvs; rw [hfl] at this; exact List.eq_nil_of_length_eq_zero this
    subst hnil
    rw [List.filterMapM_nil]
    exact RSim.pure_some ⟨hS, IWGrow.refl m, SPL.nil 0 (Nat.zero_le _)⟩
  obtain ⟨hfo1, hfl1, hfl0⟩ := slice_step hfl hfb
  obtain ⟨k, hk⟩ : ∃ k, fl.toNat = k + 1 := ⟨fl.toNat - 1, by omega⟩
  rw [hk] at hfvs
  obtain ⟨x, xs, rfl, hxs, hx⟩ := decHL_cons_r hfvs
  obtain ⟨w, hw, hH, rfl⟩ := iwH_rdW hx (by omega)
  rw [UInt64.ofNat_toNat] at hw
  rw [ihsW_cons (h := hfl), hw, List.filterMapM_cons]
  refine RSim.bind (K := ihsK1 n nP mo ml d fo fl) (by rw [ihsK1])
    (ih1W_sim dn vis fe n m a nP mo ml d w motPos hS hH hmot hmt) ?_
  rintro ⟨r1, m1⟩ o a1 - ⟨hS1, hg1, ho⟩
  dsimp only at hS1 hg1 ho
  rw [ihsK1_some]
  have hxs1 : decHL m1 (fo + 1).toNat (fl - 1).toNat = some xs := by
    rw [hfo1, hfl1, decHL_grow hg1 (by omega)]; rw [show fl.toNat - 1 = k by omega]; exact hxs
  have hft1 : (fo + 1).toNat + (fl - 1).toNat ≤ iwTop m1 := by have := hg1.1; omega
  have hmot1 : decNL m1 mo.toNat ml.toNat = some motPos := by rw [decNL_grow hg1 hmt]; exact hmot
  have hmt1 : mo.toNat + ml.toNat ≤ iwTop m1 := Nat.le_trans hmt hg1.1
  cases o with
  | none =>
    refine RSim.bindPure (K := ihsK2 n r1) (by rw [ihsK2]) (ih m1 a1 (fo + 1) (fl - 1) xs hS1 hxs1 hft1 hmot1 hmt1) ?_
    rintro ⟨r2, m2⟩ rest a2 - ⟨hS2, hg2, hsp⟩
    have ho' : r1.headD 0 ≠ 1 := by simp only [decIH] at ho; rw [ho]; decide
    rw [ihsK2_miss (h := ho')]
    exact RSim.pure_some ⟨hS2, hg1.trans hg2, hsp⟩
  | some ft =>
    obtain ⟨f, t⟩ := ft
    obtain ⟨rfl, hf, ht⟩ := ho
    refine RSim.bind (K := ihsK2 n [1, UInt64.ofNat f, UInt64.ofNat t]) (by rw [ihsK2])
      (ih m1 a1 (fo + 1) (fl - 1) xs hS1 hxs1 hft1 hmot1 hmt1) ?_
    rintro ⟨r2, m2⟩ rest a2 - ⟨hS2, hg2, hsp⟩
    rw [ihsK2_hit (h := rfl)]
    simp only [List.tail_cons, List.headD_cons]
    refine RSim.lstep (K := ihsK3 n r2) (by rw [ihsK3]) ?_
    rintro ⟨r3, m3⟩ h3
    obtain ⟨hS3, hg3, hr3, hget, htop⟩ := recW_stage h3 hS2 rfl
    rw [ihsK3_some]
    refine RSim.lstep (K := ihsK4) (by rw [ihsK4]) ?_
    rintro ⟨r4, m4⟩ h4
    have hst := rec2_decNN (a := UInt64.ofNat f) (b := UInt64.ofNat t) rfl hget htop
    rw [hr3] at h4
    simp only [List.headD_cons] at h4
    obtain ⟨hS4, hg4, hsp4⟩ := SPL.cons h4 hS3 (hsp.grow hg3) hst
    rw [ihsK4_some]
    refine RSim.pure_some ⟨hS4, ((hg1.trans hg2).trans hg3).trans hg4, ?_⟩
    simp only [decIHS, List.headD_cons, List.tail_cons]
    rwa [UInt64.toNat_ofNat_of_lt' hf, UInt64.toNat_ofNat_of_lt' ht] at hsp4

/-! ## `class_read_minor_finish` -/

/-- A `const` handle's view, through `e_view`'s words. -/
theorem viewConstW {m : Mem} {a : AState} (hR : ArenaR m a) {w : Word} (hne : eViewW m w ≠ [])
    (hg : w >>> 28 = 3) :
    (ConRon.Arena.viewConst (decE w)).run a = .ok (some (decI ((eViewW m w).tail.headD 0),
      decI ((eViewW m w).tail.tail.headD 0)), a) ∧ H ((eViewW m w).tail.headD 0) ∧
      H ((eViewW m w).tail.tail.headD 0) := by
  obtain ⟨v, hv, hR'⟩ := eViewW_ok m a hR w hne
  have hhead := eViewW_head3 m w hne hg
  cases v with
  | const nn us =>
    simp only [ViewR, getD_one, getD_two] at hR'
    obtain ⟨-, hn1, hn2, hu1, hu2⟩ := hR'
    refine ⟨?_, hn1, hu1⟩
    show Except.ok (a.store.viewConst (decE w), a) = _
    rw [EStore.viewConst_of_view_r _ _ _ _ hv, hn2, hu2]
  | bvar i => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | fvar i ty => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | sort u => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | app f x => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | lam f x => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | forallE f x => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | letE f x y => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | lit l => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR') (by decide)
  | proj f x y => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)

/-- A handle word of a fresh record, read stably. -/
theorem rec_iwH_stab {kk : IdxKind} {m m' : Mem} {ws : List Word} {q : Word} (hq : q = rdW (m.arr64 CTL) 200)
    (hget : ∀ j < ws.length, (m'.arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? = ws[j]?)
    (htop : iwTop m' = iwTop m + ws.length) (j : Nat) (hj : j < ws.length) (hw : H (ws[j]'hj)) :
    StabD (fun m => (iwH m (q.toNat + j) : Option (Idx kk))) m' (decI (ws[j]'hj)) := by
  subst hq
  have hlt : (rdW (m.arr64 CTL) 200).toNat + j < iwTop m' := by rw [htop]; simp [iwTop]; omega
  refine StabD.of_eq (fun m'' hg => iwH_grow hg hlt) ?_
  simp [iwH, hd?, iwA, hget j hj, List.getElem?_eq_getElem hj, hw]

theorem decCS_minor_stab {m : Mem} {q c o l : Nat} {cn : NIdx} {ihs : List (Nat × Nat)}
    (h0 : StabD (fun m => iwN m q) m 1) (h1 : StabD (fun m => iwN m (q + 1)) m c)
    (h2 : StabD (fun m => (iwH m (q + 2) : Option NIdx)) m cn)
    (h3 : StabD (fun m => iwN m (q + 3)) m o) (h4 : StabD (fun m => iwN m (q + 4)) m l)
    (hs : SPL decNN m o l ihs) : StabD (fun m => decCS m q) m (.minor c cn ihs) := by
  intro m' hg
  have e4 : iwN m' (q + 3 + 1) = some l := h4 m' hg
  simp [decCS, decAt, h0 m' hg, h1 m' hg, h2 m' hg, h3 m' hg, e4, (hs.grow hg).decPL]

/-- The twin's `classReadMinor` from the conclusion's head on. -/
def minorFin (nP : Nat) (motPos : List Nat) (d c : Nat) (fvs : List EIdx) (hd : EIdx) :
    AM (Option ClassSlot) :=
  if (hd.tag == ETag.const) = true then do
    match ← viewConst hd with
    | none => failDanglingE
    | some (cn, _) => do
      let ihs ← fvs.filterMapM (ihStep nP motPos d)
      pure (some (.minor c cn ihs))
  else pure none

/-- A slot read off a binder: `none`, or a stably decoding slot record. -/
def decSlot (m' : Mem) (r : List Word) : Option ClassSlot → Prop
  | none => r.headD 0 = 0
  | some s => r.headD 0 = 1 ∧ StabD (fun m => decCS m (r.tail.headD 0).toNat) m' s

theorem finW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (nP mo ml d fo fl hd c : Word) (motPos : List Nat) (fvs : List EIdx)
    (hS : StageR dn vis fe m a) (hH : H hd) (hfvs : decHL m fo.toNat fl.toNat = some fvs)
    (hft : fo.toNat + fl.toNat ≤ iwTop m) (hmot : decNL m mo.toNat ml.toNat = some motPos)
    (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (finW n m nP mo ml d fo fl hd c) (minorFin nP.toNat motPos d.toNat c.toNat fvs (decI hd)) a
      (KP dn vis fe m decSlot) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  by_cases hg : hd >>> 28 ≠ 3
  · rw [finW_tag (h := hg)]
    have ht : ¬ (((decI hd : EIdx)).tag == ETag.const) = true := by
      have : ¬ (decE hd).tag = ETag.const := fun h => hg ((decE_tag_const hd hH).mp h)
      simp only [beq_iff_eq]; exact this
    simp only [minorFin]
    rw [if_neg ht]
    exact RSim.pure_some ⟨hS, IWGrow.refl m, rfl⟩
  by_cases hne : eViewW m hd = []
  · rw [finW_nil (h := hg) (h2 := hne)]; exact RSim.none
  rw [finW_ok (h := hg) (h2 := hne)]
  have hg3 : hd >>> 28 = 3 := by simpa using hg
  have ht : (((decI hd : EIdx)).tag == ETag.const) = true := by
    have : (decE hd).tag = ETag.const := (decE_tag_const hd hH).mpr hg3
    simp only [beq_iff_eq]; exact this
  obtain ⟨hvc, hcn, -⟩ := viewConstW hS.1.arena.1 hne hg3
  simp only [minorFin]
  rw [if_pos ht]
  refine RSim.tstep hvc ?_
  refine RSim.bind (K := finK1 c ((eViewW m hd).tail.headD 0)) rfl
    (ihsW_sim dn vis fe nP mo ml d motPos n m a fo fl fvs hS hfvs hft hmot hmt) ?_
  rintro ⟨r1, m1⟩ ihs a1 - ⟨hS1, hg1, hsp⟩
  dsimp only at hS1 hg1 hsp
  refine RSim.lstep (K := finK2) rfl ?_
  rintro ⟨r2, m2⟩ h2
  obtain ⟨hS2, hg2, hr2, hget, htop⟩ := recW_stage h2 hS1 rfl
  rw [finK2_some]
  refine RSim.pure_some ⟨hS2, hg1.trans hg2, rfl, ?_⟩
  rw [hr2]
  simp only [List.headD_cons, List.tail_cons]
  have hq : rdW (m1.arr64 CTL) 200 = rdW (m1.arr64 CTL) 200 := rfl
  have e0 := rec_iwN_stab hq hget htop 0 (by simp)
  have e1 := rec_iwN_stab hq hget htop 1 (by simp)
  have e2 := rec_iwH_stab (kk := IdxKind.name) hq hget htop 2 (by simp) hcn
  have e3 := rec_iwN_stab hq hget htop 3 (by simp)
  have e4 := rec_iwN_stab hq hget htop 4 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4
  exact decCS_minor_stab e0 e1 e2 e3 e4 (hsp.grow hg2)

/-! ## `pi_binders` under the stage relation -/

theorem piBW_room (n : Nat) (m m' : Mem) (a : AState) (fuel h : Word) (rs : List Word)
    (hR : ArenaR m a) (hp : piBW n m fuel h = some (rs, m')) (hh : H h)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hc : 200 < (m.arr64 CTL).size)
    (htop : iwTop m ≤ (m.arr64 IW).size) : iwTop m' ≤ (m'.arr64 IW).size := by
  cases n with
  | zero => simp [piBW] at hp
  | succ n =>
  by_cases hf : fuel = 0
  · rw [piBW_fuel0 n m fuel h hf] at hp; simp at hp
  by_cases hg : h >>> 28 ≠ 6
  · rw [piBW_leaf n m fuel h hf hg] at hp
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp; exact htop
  rw [piBW_node n m fuel h hf hg] at hp
  have hg6 : h >>> 28 = 6 := by simpa using hg
  by_cases hr : eViewW m h = []
  · rw [hr, piBK1_nil] at hp; simp at hp
  obtain ⟨hvok, hew⟩ := eViewW_forall m h hg6 hr
  rw [piBK1_ne n m fuel _ hr] at hp
  cases hrec : piBW n m (fuel - 1) ((eViewW m h).getD 2 0) with
  | none => rw [hrec] at hp; simp [piBK2] at hp
  | some rm =>
    obtain ⟨rs1, m1⟩ := rm
    rw [hrec, piBK2_some] at hp
    cases hcons : consW n m1 ((eViewW m h).getD 1 0) (rs1.headD 0) (rs1.getD 1 0) with
    | none => rw [hcons] at hp; simp [piBK3] at hp
    | some rm2 =>
      obtain ⟨r2, m2⟩ := rm2
      rw [hcons, piBK3_some] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨-, rfl⟩ := hp
      obtain ⟨-, hty, hb⟩ := view_forall m a hR h hh hvok hg6
      have hty2 : ((eViewW m h).getD 1 0).toNat < 2 ^ 32 := by rw [hew]; exact hty
      have hb2 : ((eViewW m h).getD 2 0).toNat < 2 ^ 32 := by rw [hew]; exact hb
      obtain ⟨bs1, e1, -, -, hdec1, -, -, -, hf1, hle1⟩ :=
        piBW_ok n m m1 a (fuel - 1) _ rs1 hR hrec hb2 hsz hc
      have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := by rw [hf1.2.2.1 IW]; exact hsz
      have hc1 : 200 < (m1.arr64 CTL).size := by rw [hf1.2.2.1 CTL]; exact hc
      exact consW_room hcons hsz1 hc1 hle1 hty2 hdec1

/-- `pi_binders` as a simulation: the twin keeps its state, the binders a slice below the top. -/
theorem simPiBinders {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (n : Nat) (hS : StageR dn vis fe m a) {h : Word} (hh : H h) :
    RSim (piBW n m CWF h) (ConRon.Arena.piBinders coreWalkFuel (decI h)) a
      (fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧
        decHL b.2 (b.1.headD 0).toNat (b.1.tail.headD 0).toNat = some x.1 ∧
        (b.1.headD 0).toNat + (b.1.tail.headD 0).toNat ≤ iwTop b.2) := by
  rintro ⟨rs, m'⟩ hp
  obtain ⟨bs, e, hrun, -, hdec, -, -, hg, hf, hle⟩ :=
    piBW_ok n m m' a CWF h rs hS.1.arena.1 hp hh hS.2.2.2.1 hS.2.2.2.2.2
  have hroom := piBW_room n m m' a CWF h rs hS.1.arena.1 hp hh hS.2.2.2.1 hS.2.2.2.2.2 hS.2.1
  refine ⟨(bs, e), a, by rw [← CWF_eq]; exact hrun, stage_frame_iw hS hf (by rw [← hf.2.2.1 IW]; exact hroom),
    hg, by simpa [getD_one] using hdec, by simpa [getD_one] using hle⟩

/-! ## `class_read_minor_tail`, `class_read_minor` -/

/-- The twin's `classReadMinor` from the class on. -/
def minorTail (nP : Nat) (motPos : List Nat) (d c : Nat) (fvs : List EIdx) (concl : EIdx) :
    AM (Option ClassSlot) := do
  let args ← getAppArgs coreWalkFuel concl
  match args.getLast? with
  | none => pure none
  | some last => do
    let hd ← getAppFn coreWalkFuel last
    minorFin nP motPos d c fvs hd

theorem decSlot_pair {m : Mem} {r : List Word} {x : Option ClassSlot} (h : decSlot m r x) :
    decSlot m [r.headD 0, r.tail.headD 0] x := by
  cases x with
  | none => exact h
  | some s => exact h

theorem tailW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (nP mo ml d fo fl concl c : Word) (motPos : List Nat) (fvs : List EIdx)
    (hS : StageR dn vis fe m a) (hH : H concl) (hfvs : decHL m fo.toNat fl.toNat = some fvs)
    (hft : fo.toNat + fl.toNat ≤ iwTop m) (hmot : decNL m mo.toNat ml.toNat = some motPos)
    (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (tailW n m nP mo ml d fo fl concl c)
      (minorTail nP.toNat motPos d.toNat c.toNat fvs (decI concl)) a (KP dn vis fe m decSlot) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [tailW_eq]
  refine RSim.bind (K := tK1 n nP mo ml d fo fl c) rfl (simGetAppArgs hS hH) ?_
  rintro ⟨r5, m5⟩ rargs a5 - ⟨hS5, hg5, hd5, ht5⟩
  dsimp only at hS5 hg5 hd5 ht5
  simp only [Nat.zero_add, getD_zero, getD_one] at hd5 ht5
  have hb5 : (r5.headD 0).toNat + (r5.tail.headD 0).toNat < 2 ^ 64 := by
    have h1 : iwTop m5 ≤ (m5.arr64 IW).size := hS5.2.1
    have h2 : (m5.arr64 IW).size < 2 ^ 64 := hS5.2.2.2.1
    omega
  by_cases hz : r5.tail.headD 0 = 0
  · rw [tK1_fail (h := hz)]
    have hnil : rargs = [] := by
      have := decHL_length m5 hd5; rw [hz] at this; exact List.eq_nil_of_length_eq_zero this
    subst hnil
    exact RSim.pure_some ⟨hS5, hg5, rfl⟩
  obtain ⟨w, hw, hwH, hlast⟩ := decHL_last hd5 hz hb5
  rw [tK1_ok (h := hz), hw, hlast]
  refine RSim.bind (K := tK2 n nP mo ml d fo fl c) rfl (simGetAppFn hS5 hwH) ?_
  rintro ⟨r6, m6⟩ hd a6 - ⟨hS6, hg6, hb6, rfl⟩
  dsimp only at hS6 hg6 hb6
  rw [tK2_some]
  have hg56 := hg5.trans hg6
  refine RSim.bindPure (K := tK3) rfl (finW_sim dn vis fe n m6 a6 nP mo ml d fo fl (r6.headD 0) c motPos
    fvs hS6 hb6 (by rw [decHL_grow hg56 hft]; exact hfvs) (Nat.le_trans hft hg56.1)
    (by rw [decNL_grow hg56 hmt]; exact hmot) (Nat.le_trans hmt hg56.1)) ?_
  rintro ⟨r7, m7⟩ x a7 - ⟨hS7, hg7, hd7⟩
  rw [tK3_some]
  exact RSim.pure_some ⟨hS7, hg56.trans hg7, decSlot_pair hd7⟩

theorem drop3_headD (r : List Word) : (r.drop 3).headD 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

theorem minorW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (nP mo ml d dom : Word) (motPos : List Nat) (hS : StageR dn vis fe m a) (hH : H dom)
    (hmot : decNL m mo.toNat ml.toNat = some motPos) (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (minorW n m nP mo ml d dom) (ConRon.Arena.classReadMinor nP.toNat motPos d.toNat (decI dom)) a
      (KP dn vis fe m decSlot) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  have hmb : mo.toNat + ml.toNat < 2 ^ 64 := by
    have h1 : iwTop m ≤ (m.arr64 IW).size := hS.2.1
    have h2 : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
    omega
  rw [minorW_eq]
  refine RSim.bind (K := mK1 n nP mo ml d dom) rfl (simPiBinders n hS hH) ?_
  rintro ⟨r1, m1⟩ ⟨bs, e⟩ a1 - ⟨hS1, hg1, hd1, ht1⟩
  dsimp only at hS1 hg1 hd1 ht1
  rw [mK1_some]
  have hlen : bs.length = (r1.tail.headD 0).toNat := decHL_length _ hd1
  simp only []
  rw [hlen]
  refine RSim.bind (K := mK2 n nP mo ml d) rfl (simOpenPis hS1 hH) ?_
  rintro ⟨r2, m2⟩ o a2 - ⟨hS2, hg2, ho⟩
  dsimp only at hS2 hg2 ho
  have hg12 := hg1.trans hg2
  cases o with
  | none =>
    rw [mK2_fail (h := ho)]
    exact RSim.pure_some ⟨hS2, hg12, rfl⟩
  | some fc =>
  obtain ⟨fvs, concl⟩ := fc
  obtain ⟨h21, ⟨hfvs, hft⟩, hcH, rfl⟩ := ho
  simp only [getD_one, getD_two, Nat.reduceAdd] at hfvs hft
  rw [drop3_headD] at hcH ⊢
  rw [mK2_ok (h := by rw [h21]; decide)]
  refine RSim.bind (K := mK3 n nP mo ml d (r2.tail.headD 0) (r2.tail.tail.headD 0)
    (r2.tail.tail.tail.headD 0)) rfl (simFvarHead hS2 hcH) ?_
  rintro ⟨r3, m3⟩ x3 a3 - ⟨hS3, hg3, hx3⟩
  dsimp only at hS3 hg3 hx3
  have hg13 := hg12.trans hg3
  cases x3 with
  | none =>
    simp only [decFH] at hx3; subst hx3
    rw [mK3_fail (h := rfl)]
    exact RSim.pure_some ⟨hS3, hg13, rfl⟩
  | some p2 =>
  obtain ⟨rfl, hp2⟩ := hx3
  rw [mK3_ok (h := by simp)]
  refine RSim.lstep (K := mK4 n nP mo ml d (r2.tail.headD 0) (r2.tail.tail.headD 0)
    (r2.tail.tail.tail.headD 0) m3) rfl fun r4 h4 => ?_
  have hmot3 : decNL m3 mo.toNat ml.toNat = some motPos := by rw [decNL_grow hg13 hmt]; exact hmot
  have hc := cmvW_ok (n - 1) m3 nP mo ml _ r4 motPos hmot3 hmb h4
  simp only [List.tail_cons, List.headD_cons, UInt64.toNat_ofNat_of_lt' hp2] at hc
  cases hcm : ConRon.Arena.classOfMotiveVar nP.toNat motPos p2 with
  | none =>
    rw [hcm] at hc; subst hc
    simp only [hcm]
    rw [mK4_fail (h := rfl)]
    exact RSim.pure_some ⟨hS3, hg13, rfl⟩
  | some c =>
  rw [hcm] at hc; subst hc
  simp only [hcm]
  have hc64 : c < 2 ^ 64 := by
    have := cmv_lt _ _ _ _ hcm; have := decNL_length m3 hmot3; omega
  rw [mK4_ok (h := by simp)]
  simp only [List.tail_cons, List.headD_cons]
  have ht := tailW_sim dn vis fe n m3 a3 nP mo ml d (r2.tail.headD 0) (r2.tail.tail.headD 0)
    (r2.tail.tail.tail.headD 0) (UInt64.ofNat c) motPos fvs hS3 hcH
    (by rw [decHL_grow hg3 hft]; exact hfvs) (Nat.le_trans hft hg3.1) hmot3 (Nat.le_trans hmt hg13.1)
  rw [UInt64.toNat_ofNat_of_lt' hc64] at ht
  refine RSim.bindPure (K := mK5) rfl ht ?_
  rintro ⟨r5, m5⟩ x a5 - ⟨hS5, hg5, hd5⟩
  rw [mK5_some]
  exact RSim.pure_some ⟨hS5, hg13.trans hg5, decSlot_pair hd5⟩

/-- **`class_read_minor` refines `classReadMinor`** (through the stubs `open_pis_at_fvars_f`,
`get_app_args`, `get_app_fn`, `fvar_type_d`, `pi_result`): the slot read is a stably decoding
`ClassSlot` record. -/
@[refines ConRon.Arena.classReadMinor]
theorem classReadMinor_refines (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
    (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons) (h2 : p.lookup "rec2" = some rec2)
    (h5 : p.lookup "rec5" = some rec5)
    (hi1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1)
    (his : p.lookup "class_read_minor_ihs" = some classReadMinorIhs)
    (hfin : p.lookup "class_read_minor_finish" = some classReadMinorFinish)
    (hpb : p.lookup "pi_binders" = some piBinders)
    (hmin : p.lookup "class_read_minor" = some classReadMinor)
    (htl : p.lookup "class_read_minor_tail" = some classReadMinorTail)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (nP mo ml d dom : Word) (motPos : List Nat) (hS : StageR dn vis fe s₀.mem a₀) (hH : H dom)
    (hmot : decNL s₀.mem mo.toNat ml.toNat = some motPos) (hmt : mo.toNat + ml.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_minor" [nP, mo, ml, d, dom]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classReadMinor nP.toNat motPos d.toNat (decI dom)) a₀ ∧
      KP dn vis fe s₀.mem decSlot (r, s'.mem)
        (AM.st (ConRon.Arena.classReadMinor nP.toNat motPos d.toNat (decI dom)) a₀)
        (AM.res (ConRon.Arena.classReadMinor nP.toNat motPos d.toNat (decI dom)) a₀); ⊤⦄ :=
  triple_post (classReadMinor_spec p hfh hv hf hcm hc ha hsc h2 h5 hi1 his hfin hpb hmin htl n s₀
    nP mo ml d dom) fun _ _ ⟨hl, hw⟩ =>
    ⟨hl, (minorW_sim dn vis fe n _ a₀ nP mo ml d dom motPos hS hH hmot hmt).am hw⟩

end L.Ind
