import ConAgua.Arena.IndPos2SpecR

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the relational steps,
`nest_fields` and `nest_ctors_walk`. -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A `Π` handle's view: its domain and body, decoded. -/
theorem pos2_forall_view {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    {w : Word} (hS : StageR dn vis fe m a) (hw : H w) (h6 : w >>> 28 = 6) (hne : eViewW m w ≠ []) :
    ∃ d b, eViewW m w = [6, d, b, 0] ∧ H d ∧ H b ∧
      (viewBind (decI w)).run a = .ok (some (decI d, decI b), a) ∧ (decI w : EIdx).tag = ETag.forallE := by
  obtain ⟨hvok, hew⟩ := eViewW_forall m w h6 hne
  obtain ⟨-, hty, hb⟩ := view_forall m a hS.1.arena.1 w hw hvok h6
  have hvb := viewBind_forall m a hS.1.arena.1 w hw hvok h6
  exact ⟨_, _, hew, hty, hb, by rw [viewBind_run']; simp only [← decE_eq]; rw [hvb],
    (decE_tag_forall w hw).mpr h6⟩

theorem pos2_word_add {x y : Word} (h : ¬ x + y < x) : (x + y).toNat = x.toNat + y.toNat := by
  rcases Nat.lt_or_ge (x.toNat + y.toNat) (2 ^ 64) with hl | hl
  · exact word_add_toNat hl
  · exfalso; apply h; apply UInt64.lt_iff_toNat_lt.mpr; rw [UInt64.toNat_add]
    have := x.toNat_lt; have := y.toNat_lt; omega

theorem pos2_word_succ {x : Word} (h : ¬ x + 1 = 0) : (x + 1).toNat = x.toNat + 1 := by
  rcases Nat.lt_or_ge (x.toNat + 1) (2 ^ 64) with hl | hl
  · exact word_add_toNat (by simpa using hl)
  · exfalso; apply h; apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; have := x.toNat_lt; simp; omega

theorem pos2_word_pred {x : Word} (h : x ≠ 0) : (x - 1).toNat = x.toNat - 1 := by
  have : x.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp

section steps
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (hM : PosMemo dn vis fe)
  (hcs : CtorSums fe)

include hM in
theorem fieldsOK_step (n : Nat) (hk : 2 ^ 31 + (n + 1) ≤ coreWalkFuel) (ih : NbOK dn vis fe n) :
    FieldsOK dn vis fe (n + 1) := by
  obtain ⟨hPos, -, -, -, -, -, -, -, -, -, hFields⟩ := ih
  intro m m' a ctx fu po pl base nF j cur ns kO kL dO dL c prog NS ks nds r h hS hW hcur hns hks hkb hnd hndb
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbFieldsW_succ] at h
  by_cases h0 : nF = 0
  · rw [if_pos h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst h0
    refine ⟨(ks, nds, decI cur, NS), a, by rw [ConRon.Arena.nestFields.eq_def]; rfl, hS, IWGrow.refl _, hks, hkb, hnd, hndb,
      hcur, rfl, hns, by simp, by simp, by simp⟩
  rw [if_neg h0] at h
  by_cases h6 : cur >>> 28 ≠ 6
  · rw [if_pos h6] at h; cases h
  rw [if_neg h6] at h
  have h6' : cur >>> 28 = 6 := by simpa using h6
  by_cases hov : base + j < base
  · rw [if_pos hov] at h; cases h
  rw [if_neg hov] at h
  by_cases hov1 : base + j + 1 = 0
  · rw [if_pos hov1] at h; cases h
  rw [if_neg hov1] at h
  by_cases hev : eViewW m cur = []
  · rw [if_pos hev] at h; cases h
  rw [if_neg hev] at h
  obtain ⟨d, b, hv, hd, hb, hvb, htag⟩ := pos2_forall_view hS hcur h6' hev
  rw [hv] at h
  simp only [List.tail_cons, List.headD_cons] at h
  have hbj : (base + j).toNat = base.toNat + j.toNat := pos2_word_add hov
  have hbj1 : (base + j + 1).toNat = base.toNat + j.toNat + 1 := by rw [pos2_word_succ hov1, hbj]
  obtain ⟨nF', hnF'⟩ : ∃ nF', nF.toNat = nF' + 1 := ⟨nF.toNat - 1, by
    have : nF.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  -- the field's domain walked
  cases hp : nbPosW n m vis ctx fu po pl (base + j) 0 d ns with
  | none => rw [hp] at h; simp [nbFieldsK1] at h
  | some pr =>
  obtain ⟨rp, m1⟩ := pr
  rw [hp, nbFieldsK1_some] at h
  simp only [List.tail_cons, List.headD_cons] at h
  obtain ⟨x1, a1, hrun1, hS1, hg1, hk1, hnd1H, hnd1, hns1⟩ := hPos m m1 a ctx fu po pl (base + j) 0 d ns c prog NS rp
    hp hS hW hd hns
  -- the field's variable
  cases hfv : fvinternW m1 (base + j) d with
  | none => rw [hfv] at h; simp [nbFieldsK2] at h
  | some pr2 =>
  obtain ⟨fv, m2⟩ := pr2
  rw [hfv, nbFieldsK2_some] at h
  by_cases hfvb : 4294967296 ≤ fv
  · rw [if_pos hfvb] at h; cases h
  rw [if_neg hfvb] at h
  simp only [List.tail_cons, List.headD_cons] at h
  have hfvH : H fv := by
    have : ¬ (4294967296 : Word).toNat ≤ fv.toNat := fun e => hfvb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 (base + j) d hd hfv
  -- the body opened
  cases hin : stubM "instantiate1_fast" m2 [CWF, b, fv, 0] with
  | none => rw [hin] at h; simp [nbFieldsK3] at h
  | some pr3 =>
  obtain ⟨rb, m3⟩ := pr3
  rw [hin, nbFieldsK3_some] at h
  obtain ⟨b2, a3, hrun3, hS3, hg3, hb2H, hb2d⟩ := instantiate1Fast_spec dn vis fe CWF b fv 0 hb hfvH m2 m3 a2 rb hin hS2
  rw [CWF_eq] at hrun3
  have hg13 := (hg1.trans hg2).trans hg3
  -- the kind and the walked domain appended
  cases hs1 : snocW n m3 kO kL (rp.headD 0) with
  | none => rw [hs1] at h; simp [nbFieldsK4] at h
  | some pr4 =>
  obtain ⟨rk, m4⟩ := pr4
  rw [hs1, nbFieldsK4_some] at h
  obtain ⟨hS4, hg4, hk40, hk41, ht4, hw4, hx4⟩ := snocW_words hs1 hS3 (by have := hg13.1; omega)
  have hks4 : KlB m4 (rk.headD 0).toNat (rk.tail.headD 0).toNat (ks ++ [x1.1]) := by
    rw [hk40, hk41]
    exact KlB.snoc ((hks.grow hg13)) hg4 (by omega) hw4 hx4 hk1
  cases hs2 : snocW n m4 dO dL (rp.tail.headD 0) with
  | none => rw [hs2] at h; simp [nbFieldsK5] at h
  | some pr5 =>
  obtain ⟨rd, m5⟩ := pr5
  rw [hs2, nbFieldsK5_some] at h
  have hg14 := hg13.trans hg4
  obtain ⟨hrd, hnd5, hg5, -, hl5, ht5⟩ := snocW_decK hs2 hS4.2.2.2.1 hS4.2.2.2.2.2 (by have := hg14.1; omega)
    hnd1H (by rw [decHL_agree (RdS.of_grow hg14) (fun i hi => by omega)]; exact hnd)
  have hS5 := snocW_stage hs2 hS4
  have hg15 := hg14.trans hg5
  -- the rest of the fields
  have hj1 : (j + 1).toNat = j.toNat + 1 := word_add_toNat (by have := (base + j + 1).toNat_lt; simp; omega)
  have hnF1 : (nF - 1).toNat = nF' := by rw [pos2_word_pred h0]; omega
  obtain ⟨x, a', hrun, hS', hg', hK', hKb', hD', hDb', hcH', hcd', hns', hl1, hl2, hov'⟩ :=
    hFields m5 m' a3 ctx fu po pl base (nF - 1) (j + 1) (rb.headD 0) (rp.tail.tail.headD 0) (rk.headD 0)
      (rk.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) c prog x1.2.2 (ks ++ [x1.1]) (nds ++ [decI (rp.tail.headD 0)])
      r h hS5 (hW.grow (hg15.trans (IWGrow.refl _))) (by simpa using hb2H)
      ((hns1.grow (hg2.trans hg3) (Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1)).grow (hg4.trans hg5)
        (Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1))
      (hks4.grow hg5) (by rw [hk40, hk41]; have := hg5.1; omega)
      (by rw [hrd]; simpa using hnd5) (by rw [hrd]; simp only [List.headD_cons, List.tail_cons]; omega)
  refine ⟨x, a', ?_, hS', hg15.trans hg', hK', hKb', hD', hDb', hcH', hcd', hns', ?_, ?_, ?_⟩
  · rw [hnF', ConRon.Arena.nestFields.eq_def]
    simp only [htag, beq_self_eq_true, if_true, StateT.run_bind, hvb, except_ok_bind]
    have e1 := hrun1; simp only [hbj, UInt64.toNat_zero] at e1
    have e2 : (internFVarE (base.toNat + j.toNat) (decI d)).run a1 = .ok (decI fv, a2) := by
      simpa [internFVarE, hbj, decE_eq] using hrun2
    have e3 : (instantiate1Fast coreWalkFuel (decI b) (decI fv) 0).run a2 = .ok (b2, a3) := by simpa using hrun3
    rw [e1]; simp only [except_ok_bind]; rw [e2]; simp only [except_ok_bind]; rw [e3]; simp only [except_ok_bind]
    rw [hnF1, hj1, hb2d, hnd1] at hrun
    exact hrun
  · rw [hl1]; simp; omega
  · rw [hl2]; simp; omega
  · right; rcases hov' with h' | h'
    · rw [hnF1] at h'; subst h'; have := (base + j + 1).toNat_lt; omega
    · rw [hj1, hnF1] at h'; omega

include hM in
theorem walkOK_step (n : Nat) (hk : 2 ^ 31 + (n + 1) ≤ coreWalkFuel) (ih : NbOK dn vis fe n) :
    WalkOK dn vis fe (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hFields⟩ := ih
  intro m m' a ctx root fu po pl hi nF crest ns c prog NS r h hS hW hcr hns
  rw [nbWalkW_succ] at h
  -- the fields walked, at the input-derived fuel or the given one
  have hF : ∀ (fu' : Word) (m1 : Mem) (a1 : AState), StageR dn vis fe m1 a1 → IWGrow m m1 →
      nbWalkK2 n hi (nbFieldsW n m1 vis ctx fu' po pl hi nF 0 crest ns 0 0 0 0) = some (r, m') →
      ∃ ks nds cur ns2 closed a',
        (∀ {β : Type} (K : List NestFieldKind → List EIdx → EIdx → NestState → EIdx → AM β),
          (do let (ks, nds, cur, ns2) ← nestFields V fe c fu'.toNat prog hi.toNat nF.toNat 0 (decI crest) NS [] []
              let closed ← ConRon.Arena.closeTelescope nds hi.toNat cur
              K ks nds cur ns2 closed).run a1 = (K ks nds cur ns2 closed).run a') ∧
        StageR dn vis fe m' a' ∧ IWGrow m1 m' ∧ KlB m' (r.headD 0).toNat (r.tail.headD 0).toNat ks ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ ks.length = nF.toNat ∧
        H (r.tail.tail.headD 0) ∧ decI (r.tail.tail.headD 0) = cur ∧
        H (r.tail.tail.tail.headD 0) ∧ decI (r.tail.tail.tail.headD 0) = closed ∧
        NSB m' (r.tail.tail.tail.tail.headD 0) ns2 := by
    intro fu' m1 a1 hS1 hg1 h
    have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
    cases hf : nbFieldsW n m1 vis ctx fu' po pl hi nF 0 crest ns 0 0 0 0 with
    | none => rw [hf] at h; simp [nbWalkK2] at h
    | some pr =>
    obtain ⟨rf, m2⟩ := pr
    rw [hf, nbWalkK2_some] at h
    obtain ⟨x, a2, hrun, hS2, hg2, hK, hKb, hD, hDb, hcH, hcd, hns2, hl1, hl2, hov⟩ :=
      hFields m1 m2 a1 ctx fu' po pl hi nF 0 crest ns 0 0 0 0 c prog NS [] [] rf hf hS1 (hW.grow hg1) hcr
        (hns.grow hg1 (Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1)) (KlB.nil _ _) (by simp)
        (by simp [decHL, hslice?]) (by simp)
    cases hcl : closeW n m2 (rf.tail.tail.headD 0) (rf.tail.tail.tail.headD 0) hi (rf.tail.tail.tail.tail.headD 0) with
    | none => rw [hcl] at h; simp [nbWalkK3] at h
    | some pr2 =>
    obtain ⟨rc, m3⟩ := pr2
    rw [hcl, nbWalkK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.headD_cons, List.tail_cons]
    have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
    have hdl : (rf.tail.tail.tail.headD 0).toNat = x.2.1.length := (decHL_length _ hD).symm
    have hib : hi.toNat + (rf.tail.tail.tail.headD 0).toNat < 2 ^ 64 := by
      rw [hdl, hl2]
      simp only [UInt64.toNat_zero, Nat.add_zero, List.length_nil, Nat.zero_add] at hov ⊢
      rcases hov with h0 | h0
      · rw [h0]; simpa using hi.toNat_lt
      · omega
    obtain ⟨cl, a3, hrun3, hS3, hg3, hclH, hcld⟩ := closeW_ok n dn fe vis m2 m3 a2 _ _ hi _ x.2.1 rc hcl hS2 hcH hD
      (by omega) hDb hib
    refine ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, cl, a3, fun K => ?_, hS3, hg2.trans hg3, hK.grow hg3,
      by have := hg3.1; omega, by simpa using hl1, hcH, hcd, hclH, hcld, hns2.grow hg3 htop2⟩
    rw [hcd] at hrun3
    simp only [UInt64.toNat_zero] at hrun
    simp only [StateT.run_bind, hrun, except_ok_bind, hrun3]
  by_cases hr : root ≠ 0
  · rw [if_pos hr] at h
    have hdec : decide (root ≠ 0) = true := by simpa using hr
    cases n with
    | zero => simp [wfWf, nbWalkK1] at h
    | succ n' =>
    cases n' with
    | zero => simp [wfWf, nbWalkK1] at h
    | succ n'' =>
    simp only [wfWf] at h
    cases hw : wfW n'' m crest with
    | none => rw [hw] at h; simp [nbWalkK1] at h
    | some pr =>
    obtain ⟨wf, m1⟩ := pr
    rw [hw] at h
    simp only [nbWalkK1_some, List.headD_cons] at h
    obtain ⟨mp, hmp⟩ := hM.dp m a hS
    obtain ⟨d, hrunw, hwd, -, hS1, hg1⟩ := wfW_ok n'' dn fe vis m m1 a crest wf mp hw hS hcr hmp
    obtain ⟨ks, nds, cur, ns2, closed, a', hK, rest⟩ := hF wf m1 a hS1 hg1 h
    refine ⟨ks, nds, cur, ns2, closed, a', fun K => ?_, rest.1, hg1.trans rest.2.1, rest.2.2⟩
    rw [← hK K, hwd]
    simp only [walkK, hdec, dite_true, StateT.run_bind, ← decE_eq, hrunw, except_ok_bind]
  · rw [if_neg hr] at h
    have hdec : decide (root ≠ 0) = false := by simpa using hr
    obtain ⟨ks, nds, cur, ns2, closed, a', hK, rest⟩ := hF fu m a hS (IWGrow.refl _) h
    refine ⟨ks, nds, cur, ns2, closed, a', fun K => ?_, rest⟩
    rw [← hK K]
    simp only [walkK, hdec]
    rfl

include hM in
theorem oneOK_step (n : Nat) (hk : 2 ^ 31 + (n + 1) ≤ coreWalkFuel) (ih : NbOK dn vis fe n) :
    OneOK dn vis fe (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hWalk, -⟩ := ih
  intro m m' a ctx root fu po pl hi us dO dL no nl hO hL cv nF ns c prog ds names holes cvv NS r h hS hW hC hcv
    hcv3 hns
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbOneW_succ] at h
  -- the crest, typed
  cases hct : p2ctW n m vis no nl us dO dL hO hL cv hi with
  | none => rw [hct] at h; simp [nbOneK1] at h
  | some pr =>
  obtain ⟨rc, m1⟩ := pr
  rw [hct, nbOneK1_some] at h
  obtain ⟨cty, a1, crest, a2, ty, a3, so, a4, hnod, hrun1, hrun2, hrun3, hrun4, hS1, hg1, hcrH, hcrd⟩ :=
    p2ctW_ok dn vis fe hM hct hS hC.hus hC.hnames hC.hnamesb hC.hnn (hC.hds.get (OMono.decHL _ _)) hC.hdsb
      hC.hholes hC.hholesb ((erecP_ext m).decCV hcv) hcv3
  -- the walk
  cases hwk : nbWalkW n m1 vis ctx root fu po pl hi nF (rc.headD 0) ns with
  | none => rw [hwk] at h; simp [nbOneK2] at h
  | some pr2 =>
  obtain ⟨rw, m2⟩ := pr2
  rw [hwk, nbOneK2_some] at h
  obtain ⟨ks, nds, cur, ns2, closed, a5, hW5, hS2, hg2, hks, hksb, hksl, hcurH, hcurd, hclH, hcld, hns2⟩ :=
    hWalk m1 m2 a4 ctx root fu po pl hi nF (rc.headD 0) ns c prog NS rw hwk hS1 (hW.grow hg1) hcrH
      (hns.grow hg1 htop)
  -- U4
  have hkl : (rw.tail.headD 0).toNat = nF.toNat := by rw [← hks.length, hksl]
  have hksT : decKL (truncM m2) (rw.headD 0).toNat nF.toNat = some ks := by rw [← hkl]; exact hks
  cases hu : u4W n m2 (rw.headD 0) nF (rw.tail.tail.tail.headD 0) 0 with
  | none => rw [hu] at h; simp [nbOneK3] at h
  | some pr3 =>
  obtain ⟨ru, m3⟩ := pr3
  rw [hu, nbOneK3_some] at h
  obtain ⟨bu, a6, hrun6, hS3, hg3, hru⟩ := u4W_ok dn vis fe hM (m0 := m2) _ nF _ ks hclH hksT n m2 m3 a5 0 ru
    (by omega) hu hS2 (IWGrow.refl _) (by simp)
  cases bu with
  | true => rw [if_pos (by rw [hru]; decide)] at h; cases h
  | false =>
  rw [if_neg (by rw [hru]; decide)] at h
  -- the result's head
  have hU3 := (((hW.grow hg1).grow hg2).grow hg3).u
  cases hro : roW n m3 ctx hi (rw.tail.tail.headD 0) with
  | none => rw [hro] at h; simp [nbOneK4] at h
  | some pr4 =>
  obtain ⟨rr, m4⟩ := pr4
  rw [hro, nbOneK4_some] at h
  obtain ⟨bo, a7, hrun7, hS4, hg4, hrr⟩ := roW_ok dn vis fe hM hro hS3 hU3 hcurH
  cases bo with
  | false => rw [if_pos (by rw [hrr]; rfl)] at h; cases h
  | true =>
  rw [if_neg (by rw [hrr]; decide)] at h
  -- the constructor's record
  have hg14 := ((hg1.trans hg2).trans hg3).trans hg4
  have hW4 := hW.grow hg14
  cases n with
  | zero => simp [ncnWf, nbOneK5] at h
  | succ n' =>
  simp only [ncnWf] at h
  cases hnf : ncnW n' m4 ctx po pl us dO dL cv (rw.tail.tail.tail.headD 0) with
  | none => rw [hnf] at h; simp [nbOneK5] at h
  | some pr5 =>
  obtain ⟨nf, m5⟩ := pr5
  rw [hnf] at h
  simp only [nbOneK5_some, List.headD_cons] at h
  obtain ⟨M, G, g, hR⟩ := hM.rf m4 a7 hS4
  have htop4 : iwTop m4 < 2 ^ 64 := Nat.lt_of_le_of_lt hS4.2.1 hS4.2.2.2.1
  obtain ⟨x, a8, hrun8, hnfd, hnfb, M', G', hS5, hg5, -⟩ := ncnW_ok dn fe vis n' m4 m5 a7 ctx po pl us dO dL cv _ nf c prog
    ds cvv M G g hnf hS4 hW4.u.dec hW4.u.inn hW4.hs (by have := hW.hb; simp [NestCtx.hiAt] at this; omega) hC.hus
    ((hC.hds.grow (OMono.decHL _ _) hg14).get (OMono.decHL _ _)) (fun j hj => by have := hC.hdsb; have := hg14.1; omega)
    hclH ((GrowX.of_grow (q := 0) (n := 0) hg14).erecP.decCV hcv) hR
  have htop5 : iwTop m5 < 2 ^ 64 := Nat.lt_of_le_of_lt hS5.2.1 hS5.2.2.2.1
  have hns5 := hns2.grow ((hg3.trans hg4).trans hg5) (Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1)
  obtain ⟨hp6, hk5, ha5, hn5⟩ := nsb_words hns5 htop5
  -- the record appended to the state's constructor list
  cases hsn : snocW (n' + 1) m5 (rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 4))
      (rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 5)) nf with
  | none => rw [hsn] at h; simp [nbOneK6] at h
  | some pr6 =>
  obtain ⟨rs, m6⟩ := pr6
  rw [hsn, nbOneK6_some] at h
  obtain ⟨hS6, hg6, h60, h61, ht6, hw6, hx6⟩ := snocW_words hsn hS5 hns5.b4
  have hnfs6 : NfsB m6 (rs.headD 0).toNat (rs.tail.headD 0).toNat (ns2.ctorNfs.toList ++ [x]) := by
    rw [h60, h61]
    exact pos2_decB_snoc decNCN_mono hn5 hg6 (by omega) hw6 hx6 (DecB.grow (decNCN_mono _) hg6 hnfd)
  have hrd : ∀ i : Word, i.toNat < 4 → rdW (m6.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + i) =
      rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + i) := fun i hi => by
    have e : (rw.tail.tail.tail.tail.headD 0 + i).toNat = (rw.tail.tail.tail.tail.headD 0).toNat + i.toNat :=
      word_add_toNat (by omega)
    simp only [rdW, e]; rw [hg6.2.2.1 _ (by omega)]
  have hrd0 : rdW (m6.arr64 IW) (rw.tail.tail.tail.tail.headD 0) = rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0) := by
    simpa using hrd 0 (by decide)
  rw [hrd0, hrd 1 (by decide), hrd 2 (by decide), hrd 3 (by decide)] at h
  cases hq : posRecW m6 [rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0),
      rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 1), rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 2),
      rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 3), rs.headD 0, rs.tail.headD 0] with
  | none => rw [hq] at h; simp [nbOneK7] at h
  | some pr7 =>
  obtain ⟨q, m7⟩ := pr7
  rw [hq, nbOneK7_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS7, hg7, hqq, ht7, hget7⟩ := posRecW_stage hq hS6 (by simp)
  simp only [List.length_cons, List.length_nil] at ht7
  have hg67 := hg6.trans hg7
  have hNS3 := nsb_rec6 (m' := m7) (q := q) (keys := ns2.keys.toList) (act := ns2.active)
    (nfs := ns2.ctorNfs.toList ++ [x]) (by omega) (Nat.lt_of_le_of_lt hS7.2.1 hS7.2.2.2.1) hget7 (hk5.grow hg67)
    (by have := hns5.b0; have := hg67.1; omega) (ha5.grow hg67) (by have := hns5.b2; have := hg67.1; omega)
    (hnfs6.grow hg7) (by rw [h60, h61]; have := hg7.1; omega)
  have hgall := (hg14.trans hg5).trans hg67
  refine ⟨ks, closed, { ns2 with ctorNfs := ns2.ctorNfs.push x }, a8, fun K => ?_, hS7, hgall,
    ?_, ?_, hclH, hcld, ?_⟩
  · have hr6 : ((List.range nF.toNat).anyM (u4F ks closed)).run a5 = .ok (false, a6) := by
      rw [List.range_eq_range', ← hcld]; simpa using hrun6
    have hr8 : (ConRon.Arena.nestCtorNf c prog (decI us) ds cvv closed).run a7 = .ok (x, a8) := by
      rw [← hcld]; simpa [decE_eq] using hrun8
    rw [hcrd] at hW5
    rw [hcurd] at hrun7
    simp only [oneK, hnod, Bool.not_true, Bool.false_eq_true, ite_false, StateT.run_bind, hrun1, except_ok_bind,
      hrun2, hrun3, hrun4]
    rw [hW5]
    simp only [StateT.run_bind, hr6, except_ok_bind, Bool.false_eq_true, ite_false]
    rw [hrun7]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, StateT.run_bind, hr8, except_ok_bind]
  · simp only [List.headD_cons, List.tail_cons]
    exact hks.grow ((((hg3.trans hg4).trans hg5).trans hg6).trans hg7)
  · simp only [List.headD_cons, List.tail_cons]
    have := hg3.1; have := hg4.1; have := hg5.1; have := hg6.1; have := hg7.1; omega
  · simp only [List.headD_cons, List.tail_cons]
    have e : (ns2.ctorNfs.toList ++ [x]).toArray = ns2.ctorNfs.push x := Array.ext' (by simp)
    simpa [e] using hNS3

theorem ctorsOK_step (n : Nat) (ih : NbOK dn vis fe n) : CtorsOK dn vis fe (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, hCtors, hOne, -, -⟩ := ih
  intro m m' a ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL c prog ds names holes cs NS outs r h hS hW hC
    hcl hcb hcs hns hout houtb
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbCtorsW_succ] at h
  by_cases h0 : cL = 0
  · rw [if_pos h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst h0
    have : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hcl.symm)
    subst this
    exact ⟨(outs, NS), a, by rw [ConRon.Arena.nestCtors.eq_def]; rfl, hS, IWGrow.refl _, hout, houtb, hns⟩
  rw [if_neg h0] at h
  obtain ⟨⟨cvv, nFn⟩, cs', rfl⟩ : ∃ x cs', cs = x :: cs' := by
    cases cs with
    | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hcl)) h0
    | cons x cs' => exact ⟨x, cs', rfl⟩
  simp only [List.length_cons] at hcl hcb
  obtain ⟨w, hw, hcn⟩ := hcs 0 (by simp)
  obtain ⟨hp0, hp1, q, hq, hcvv, hnF⟩ := hcn
  simp only [Nat.add_zero, List.getElem_cons_zero] at hw hcvv hnF
  have hrw : rdW (m.arr64 IW) cO = w := by simp [rdW, hw]
  have hw1 : (w + 1).toNat = w.toNat + 1 := word_add_toNat (by simp; omega)
  have hrq : (rdW (m.arr64 IW) w).toNat = q := by
    have := rd_iwN (m := m) (p := w) (i := 0) (by simpa using hq) (by simp; omega); simpa using this
  have hrn : (rdW (m.arr64 IW) (w + 1)).toNat = nFn := rd_iwN (by simpa using hnF) (by simp; omega)
  rw [hrw] at h
  obtain ⟨-, -, hty⟩ := decCV_some hcvv
  obtain ⟨wt, hwt, -⟩ := hd?_some hty
  have hq3 : q + 3 < 2 ^ 64 := by
    have := (Array.getElem?_eq_some_iff.mp hwt).1; have := erecP_size_lt m; omega
  -- one constructor
  cases ho : nbOneW n m vis ctx root fu po pl hi us dO dL no nl hO hL (rdW (m.arr64 IW) w)
      (rdW (m.arr64 IW) (w + 1)) ns with
  | none => rw [ho] at h; simp [nbCtorsK1] at h
  | some pr =>
  obtain ⟨r1, m1⟩ := pr
  rw [ho, nbCtorsK1_some] at h
  obtain ⟨ks, closed, NS3, a1, hK1, hS1, hg1, hks, hksb, hclH, hcld, hns3⟩ :=
    hOne m m1 a ctx root fu po pl hi us dO dL no nl hO hL _ _ ns c prog ds names holes cvv NS r1 ho hS hW hC
      (by rw [hrq]; exact hcvv) (by rw [hrq]; exact hq3) hns
  rw [hrn] at hK1
  -- its record, appended
  cases hr3 : posRecW m1 [r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0] with
  | none => rw [hr3] at h; simp [nbCtorsK2] at h
  | some pr2 =>
  obtain ⟨rec, m2⟩ := pr2
  rw [hr3, nbCtorsK2_some] at h
  obtain ⟨hS2, hg2, hrq2, ht2, hget2⟩ := posRecW_stage hr3 hS1 (by simp)
  simp only [List.length_cons, List.length_nil] at ht2
  have hke := pos2_ke_rec (by omega) hget2 (hks.grow hg2) hclH hcld
  cases hsn : snocW n m2 oO oL rec with
  | none => rw [hsn] at h; simp [nbCtorsK3] at h
  | some pr3 =>
  obtain ⟨ro, m3⟩ := pr3
  rw [hsn, nbCtorsK3_some] at h
  have hg12 := hg1.trans hg2
  obtain ⟨hS3, hg3, h30, h31, ht3, hw3, hx3⟩ := snocW_words hsn hS2 (by have := hg12.1; omega)
  have hout3 : OutsB m3 (ro.headD 0).toNat (ro.tail.headD 0).toNat (outs ++ [(ks, closed)]) := by
    rw [h30, h31]
    exact pos2_decB_snoc decKE_mono (hout.grow hg12) hg3 (by omega) hw3 hx3 (DecB.grow (decKE_mono _) hg3 hke)
  have hg13 := hg12.trans hg3
  have hcO1 : (cO + 1).toNat = cO.toNat + 1 := word_add_toNat (by simp; omega)
  have hcL1 : (cL - 1).toNat = cs'.length := by rw [pos2_word_pred h0]; omega
  obtain ⟨x, a', hrun, hS', hg', hO', hOb', hns'⟩ := hCtors m3 m' a1 ctx root fu po pl hi us dO dL no nl hO hL
    (cO + 1) (cL - 1) _ _ _ c prog ds names holes cs' NS3 (outs ++ [(ks, closed)]) r h hS3 (hW.grow hg13)
    ⟨hC.hus, hC.hds.grow (OMono.decHL _ _) hg13, by have := hC.hdsb; have := hg13.1; omega,
      by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by have := hC.hnamesb; omega)]; exact hC.hnames,
      by have := hC.hnamesb; have := hg13.1; omega, hC.hnn,
      by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by have := hC.hholesb; omega)]; exact hC.hholes,
      by have := hC.hholesb; have := hg13.1; omega⟩
    hcL1 (by rw [hcO1]; have := hg13.1; omega) (by rw [hcO1]; exact (hcs.grow (by simpa using hcb) hg13).tail)
    ((hns3.grow hg2 (Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1)).grow hg3 (Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1))
    hout3 (by rw [h30, h31]; omega)
  refine ⟨x, a', ?_, hS', hg13.trans hg', hO', hOb', hns'⟩
  rw [nestCtors_cons, hK1]
  exact hrun

end steps

end L.Ind
