import ConAgua.Arena.IndPos2SpecR
import ConAgua.Arena.StageInst1
import ConAgua.Arena.IndRealAbsPos

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the relational steps,
`nest_fields` and `nest_ctors_walk`. -/


noncomputable section

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

theorem pos2_rd_grow {m m' : Mem} (hg : IWGrow m m') {x : Word} (hx : x.toNat < iwTop m) :
    rdW (m'.arr64 IW) x = rdW (m.arr64 IW) x := by simp only [rdW]; rw [hg.2.2.1 _ hx]

/-- The words of a `NestState` record, read after the pool grew. -/
theorem pos2_ns_rd {m m' : Mem} (hg : IWGrow m m') {p : Word} (hp : p.toNat + 6 ≤ iwTop m)
    (htop : iwTop m < 2 ^ 64) (i : Word) (hi : i.toNat < 6) : rdW (m'.arr64 IW) (p + i) = rdW (m.arr64 IW) (p + i) :=
  pos2_rd_grow hg (by rw [word_add_toNat (by omega)]; omega)

/-- A handle slice split at `k`. -/
theorem pos2_decHL_split {k : IdxKind} {m : Mem} {o l n : Nat} {xs : List (Idx k)} (h : decHL m o l = some xs)
    (hn : n ≤ l) : decHL m o n = some (xs.take n) ∧ decHL m (o + n) (l - n) = some (xs.drop n) := by
  obtain ⟨hl, hg⟩ := pos2_hslice_get h
  have get : ∀ j (hj : j < xs.length), iwH m (o + j) = some xs[j] := fun j hj => by
    have := mapM_opt_get (fun j => (hd? (iwA m) (o + j) : Option (Idx k))) (List.range l) xs h j
      (by simp; omega)
    simpa [iwH] using this
  constructor
  · have := decHL_of_get m (xs.take n) o (fun j hj => by
      simp only [List.length_take] at hj; rw [List.getElem_take]; exact get j (by omega))
    simpa [List.length_take, hl, Nat.min_eq_left hn] using this
  · have := decHL_of_get m (xs.drop n) (o + n) (fun j hj => by
      simp only [List.length_drop] at hj; rw [List.getElem_drop, show o + n + j = o + (n + j) by omega]
      exact get (n + j) (by omega))
    simpa [List.length_drop, hl] using this

/-- `aL == nPc + nI` on words is the twin's comparison, `nPc ≤ aL`. -/
theorem pos2_len_eq {aL nPc nI : Word} (h : nPc.toNat ≤ aL.toNat) :
    (aL = nPc + nI) ↔ aL.toNat = nPc.toNat + nI.toNat := by
  constructor
  · intro e
    rcases Nat.lt_or_ge (nPc.toNat + nI.toNat) (2 ^ 64) with hl | hl
    · rw [e, word_add_toNat hl]
    · exfalso
      have := congrArg UInt64.toNat e; rw [UInt64.toNat_add] at this
      have := nI.toNat_lt; have := nPc.toNat_lt
      omega
  · intro e
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, ← e]; exact (Nat.mod_eq_of_lt aL.toNat_lt).symm

theorem pos2_contains_map (ws : List Word) (hw : ∀ w ∈ ws, H w) (x : Word) (hx : H x) :
    (ws.map (decI : Word → NIdx)).contains (decI x) = ws.contains x := by
  rw [Bool.eq_iff_iff]
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨v, hv, e⟩
    rw [decI_inj (hw v hv) hx e] at hv; exact hv
  · intro h; exact ⟨x, h, rfl⟩

theorem pos2_getD2 (vl : List Word) : vl.getD 2 0 = vl.tail.tail.headD 0 := by
  rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> rfl

section steps
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  (hcs : CtorSums fe)

theorem fieldsOK_step (n : Nat) (hk : 2 ^ 31 + (n + 1) ≤ coreWalkFuel) (ih : NbOK dn vis fe n) :
    FieldsOK dn vis fe (n + 1) := by
  obtain ⟨hPos, -, -, -, -, -, -, -, -, -, hFields⟩ := ih
  intro m m' a ctx fu po pl base nF j cur ns kO kL dO dL c prog NS ks nds r h hS hW hcur hns hks hkb hnd hndb hP hA
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbFieldsW_succ] at h
  by_cases h0 : nF = 0
  · rw [if_pos h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst h0
    refine ⟨(ks, nds, decI cur, NS), a, by rw [ConRon.Arena.nestFields.eq_def]; rfl, hS, IWGrow.refl _, hks, hkb, hnd, hndb,
      hcur, rfl, hns, by simp, by simp, by simp, hP, hA⟩
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
  obtain ⟨x1, a1, hrun1, hS1, hg1, hk1, hnd1H, hnd1, hns1, hP1, hA1⟩ := hPos m m1 a ctx fu po pl (base + j) 0 d ns c prog
    NS rp hp hS hW hd hns hP hA
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
  cases hin : i1F m2 [CWF, b, fv, 0] with
  | none => rw [hin] at h; simp [nbFieldsK3] at h
  | some pr3 =>
  obtain ⟨rb, m3⟩ := pr3
  rw [hin, nbFieldsK3_some] at h
  obtain ⟨b2, a3, hrun3, hS3, hg3, hb2H, hb2d⟩ := i1F_ok dn vis fe b fv 0 hb m2 m3 a2 rb hin hS2
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
  obtain ⟨x, a', hrun, hS', hg', hK', hKb', hD', hDb', hcH', hcd', hns', hl1, hl2, hov', hP', hA'⟩ :=
    hFields m5 m' a3 ctx fu po pl base (nF - 1) (j + 1) (rb.headD 0) (rp.tail.tail.headD 0) (rk.headD 0)
      (rk.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) c prog x1.2.2 (ks ++ [x1.1]) (nds ++ [decI (rp.tail.headD 0)])
      r h hS5 (hW.grow (hg15.trans (IWGrow.refl _))) (by simpa using hb2H)
      ((hns1.grow (hg2.trans hg3) (Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1)).grow (hg4.trans hg5)
        (Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1))
      (hks4.grow hg5) (by rw [hk40, hk41]; have := hg5.1; omega)
      (by rw [hrd]; simpa using hnd5) (by rw [hrd]; simp only [List.headD_cons, List.tail_cons]; omega)
      ((((hP1.fr (fvinternW_mfr hfv)).fr (MFr.ofI1F hin)).fr (snocW_mfr hs1)).fr (snocW_mfr hs2))
      (snocW_afr hs2 (snocW_afr hs1 (i1F_afr hin (fvinternW_afr hfv hA1))))
  refine ⟨x, a', ?_, hS', hg15.trans hg', hK', hKb', hD', hDb', hcH', hcd', hns', ?_, ?_, ?_, hP', hA'⟩
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

theorem walkOK_step (n : Nat) (hk : 2 ^ 31 + (n + 1) ≤ coreWalkFuel) (ih : NbOK dn vis fe n) :
    WalkOK dn vis fe (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hFields⟩ := ih
  intro m m' a ctx root fu po pl hi nF crest ns c prog NS r h hS hW hcr hns hP hA
  rw [nbWalkW_succ] at h
  -- the fields walked, at the input-derived fuel or the given one
  have hF : ∀ (fu' : Word) (m1 : Mem) (a1 : AState), StageR dn vis fe m1 a1 → IWGrow m m1 → PosMR m1 → AbsOK m1 →
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
        NSB m' (r.tail.tail.tail.tail.headD 0) ns2 ∧ PosMR m' ∧ AbsOK m' := by
    intro fu' m1 a1 hS1 hg1 hP1 hA1 h
    have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
    cases hf : nbFieldsW n m1 vis ctx fu' po pl hi nF 0 crest ns 0 0 0 0 with
    | none => rw [hf] at h; simp [nbWalkK2] at h
    | some pr =>
    obtain ⟨rf, m2⟩ := pr
    rw [hf, nbWalkK2_some] at h
    obtain ⟨x, a2, hrun, hS2, hg2, hK, hKb, hD, hDb, hcH, hcd, hns2, hl1, hl2, hov, hP2, hA2⟩ :=
      hFields m1 m2 a1 ctx fu' po pl hi nF 0 crest ns 0 0 0 0 c prog NS [] [] rf hf hS1 (hW.grow hg1) hcr
        (hns.grow hg1 (Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1)) (KlB.nil _ _) (by simp)
        (by simp [decHL, hslice?]) (by simp) hP1 hA1
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
    obtain ⟨cl, a3, hrun3, hS3, hg3, ⟨hclH, hcld⟩, hA3⟩ := closeW_ok n dn fe vis m2 m3 a2 _ _ hi _ x.2.1 rc hcl hS2
      hcH hD (by omega) hDb hib hA2
    refine ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, cl, a3, fun K => ?_, hS3, hg2.trans hg3, hK.grow hg3,
      by have := hg3.1; omega, by simpa using hl1, hcH, hcd, hclH, hcld, hns2.grow hg3 htop2,
      hP2.fr (closeW_mfr _ _ _ _ _ _ _ _ hcl), hA3⟩
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
    obtain ⟨mp, hmp⟩ := hP.dp
    obtain ⟨d, hrunw, hwd, hM1, hS1, hg1, hf1⟩ := wfW_ok n'' dn fe vis m m1 a crest wf mp hw hS hcr hmp
    obtain ⟨ks, nds, cur, ns2, closed, a', hK, rest⟩ := hF wf m1 a hS1 hg1 (hP.setDp hf1 ⟨∅, hM1⟩)
      (wfW_afr hw hA) h
    refine ⟨ks, nds, cur, ns2, closed, a', fun K => ?_, rest.1, hg1.trans rest.2.1, rest.2.2⟩
    rw [← hK K, hwd]
    simp only [walkK, hdec, dite_true, StateT.run_bind, ← decE_eq, hrunw, except_ok_bind]
  · rw [if_neg hr] at h
    have hdec : decide (root ≠ 0) = false := by simpa using hr
    obtain ⟨ks, nds, cur, ns2, closed, a', hK, rest⟩ := hF fu m a hS (IWGrow.refl _) hP hA h
    refine ⟨ks, nds, cur, ns2, closed, a', fun K => ?_, rest⟩
    rw [← hK K]
    simp only [walkK, hdec]
    rfl

theorem oneOK_step (n : Nat) (hk : 2 ^ 31 + (n + 1) ≤ coreWalkFuel) (ih : NbOK dn vis fe n) :
    OneOK dn vis fe (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hWalk, -⟩ := ih
  intro m m' a ctx root fu po pl hi us dO dL no nl hO hL cv nF ns c prog ds names holes cvv NS r h hS hW hC hcv
    hcv3 hns hP hA
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbOneW_succ] at h
  -- the crest, typed
  cases hct : p2ctW n m vis no nl us dO dL hO hL cv hi with
  | none => rw [hct] at h; simp [nbOneK1] at h
  | some pr =>
  obtain ⟨rc, m1⟩ := pr
  rw [hct, nbOneK1_some] at h
  obtain ⟨cty, a1, crest, a2, ty, a3, so, a4, hnod, hrun1, hrun2, hrun3, hrun4, hS1, hg1, hcrH, hcrd, hP1⟩ :=
    p2ctW_ok dn vis fe hct hS hC.hus hC.hnames hC.hnamesb hC.hnn (hC.hds.get (OMono.decHL _ _)) hC.hdsb
      hC.hholes hC.hholesb ((erecP_ext m).decCV hcv) hcv3 hP
  have hA1 := p2ctW_afr hct hA
  -- the walk
  cases hwk : nbWalkW n m1 vis ctx root fu po pl hi nF (rc.headD 0) ns with
  | none => rw [hwk] at h; simp [nbOneK2] at h
  | some pr2 =>
  obtain ⟨rw, m2⟩ := pr2
  rw [hwk, nbOneK2_some] at h
  obtain ⟨ks, nds, cur, ns2, closed, a5, hW5, hS2, hg2, hks, hksb, hksl, hcurH, hcurd, hclH, hcld, hns2, hP2, hA2⟩ :=
    hWalk m1 m2 a4 ctx root fu po pl hi nF (rc.headD 0) ns c prog NS rw hwk hS1 (hW.grow hg1) hcrH
      (hns.grow hg1 htop) hP1 hA1
  -- U4
  have hkl : (rw.tail.headD 0).toNat = nF.toNat := by rw [← hks.length, hksl]
  have hksT : decKL (truncM m2) (rw.headD 0).toNat nF.toNat = some ks := by rw [← hkl]; exact hks
  cases hu : u4W n m2 (rw.headD 0) nF (rw.tail.tail.tail.headD 0) 0 with
  | none => rw [hu] at h; simp [nbOneK3] at h
  | some pr3 =>
  obtain ⟨ru, m3⟩ := pr3
  rw [hu, nbOneK3_some] at h
  obtain ⟨bu, a6, hrun6, hS3, hg3, hru, hP3⟩ := u4W_ok dn vis fe (m0 := m2) _ nF _ ks hclH hksT n m2 m3 a5 0 ru
    (by omega) hu hS2 (IWGrow.refl _) (by simp) hP2
  have hA3 := u4W_afr _ _ _ _ _ _ _ _ hu hA2
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
  obtain ⟨bo, a7, hrun7, hS4, hg4, hrr, hP4⟩ := roW_ok dn vis fe hro hS3 hU3 hcurH hP3
  have hA4 := roW_afr hro hA3
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
  obtain ⟨M, G, g, hR⟩ := hP4.rf
  have htop4 : iwTop m4 < 2 ^ 64 := Nat.lt_of_le_of_lt hS4.2.1 hS4.2.2.2.1
  obtain ⟨x, a8, hrun8, hnfd, hnfb, M', G', hS5, hg5, hR5, -⟩ := ncnW_ok dn fe vis n' m4 m5 a7 ctx po pl us dO dL cv _ nf c prog
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
    ?_, ?_, hclH, hcld, ?_, ((hP4.setRf (ncnW_mfr hnf) ⟨M', G', g, hR5⟩).fr (snocW_mfr hsn)).fr (posRecW_mfr hq),
    posRecW_afr hq (snocW_afr hsn (ncnW_afr hnf hA4))⟩
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
    hcl hcb hcs hns hout houtb hP hA
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbCtorsW_succ] at h
  by_cases h0 : cL = 0
  · rw [if_pos h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst h0
    have : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hcl.symm)
    subst this
    exact ⟨(outs, NS), a, by rw [ConRon.Arena.nestCtors.eq_def]; rfl, hS, IWGrow.refl _, hout, houtb, hns, hP, hA⟩
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
  obtain ⟨ks, closed, NS3, a1, hK1, hS1, hg1, hks, hksb, hclH, hcld, hns3, hP1, hA1⟩ :=
    hOne m m1 a ctx root fu po pl hi us dO dL no nl hO hL _ _ ns c prog ds names holes cvv NS r1 ho hS hW hC
      (by rw [hrq]; exact hcvv) (by rw [hrq]; exact hq3) hns hP hA
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
  obtain ⟨x, a', hrun, hS', hg', hO', hOb', hns', hP', hA'⟩ := hCtors m3 m' a1 ctx root fu po pl hi us dO dL no nl hO hL
    (cO + 1) (cL - 1) _ _ _ c prog ds names holes cs' NS3 (outs ++ [(ks, closed)]) r h hS3 (hW.grow hg13)
    ⟨hC.hus, hC.hds.grow (OMono.decHL _ _) hg13, by have := hC.hdsb; have := hg13.1; omega,
      by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by have := hC.hnamesb; omega)]; exact hC.hnames,
      by have := hC.hnamesb; have := hg13.1; omega, hC.hnn,
      by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by have := hC.hholesb; omega)]; exact hC.hholes,
      by have := hC.hholesb; have := hg13.1; omega⟩
    hcL1 (by rw [hcO1]; have := hg13.1; omega) (by rw [hcO1]; exact (hcs.grow (by simpa using hcb) hg13).tail)
    ((hns3.grow hg2 (Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1)).grow hg3 (Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1))
    hout3 (by rw [h30, h31]; omega) ((hP1.fr (posRecW_mfr hr3)).fr (snocW_mfr hsn))
    (snocW_afr hsn (posRecW_afr hr3 hA1))
  refine ⟨x, a', ?_, hS', hg13.trans hg', hO', hOb', hns', hP', hA'⟩
  rw [nestCtors_cons, hK1]
  exact hrun

include hcs in
theorem frameOK_step (n : Nat) (ih : NbOK dn vis fe n) : FrameOK dn vis fe (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, hCtors, -, -, -⟩ := ih
  intro m m' a ctx fu po pl hi us dO dL nPc gO gL ns c prog ds grp NS r h hS hW hhi hus hds hdsb hgl hgb hgrp hns hP hA
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbFrameW_succ] at h
  -- the group's head name
  have hhn : (if gL = 0 then naF m [] else some ([rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m)) =
        none ∨ ∃ (rn : List Word) (m1 : Mem) (a1 : AState),
      (if gL = 0 then naF m [] else some ([rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m)) =
        some (rn, m1) ∧ StageR dn vis fe m1 a1 ∧ IWGrow m m1 ∧ MFr [] [] m m1 ∧ AFr m m1 ∧ H (rn.headD 0) ∧
      (match grp with
        | [] => internNNode .anonymous
        | (c, _) :: _ => pure c : AM NIdx).run a = .ok (decI (rn.headD 0), a1) := by
    by_cases h0 : gL = 0
    · rw [if_pos h0]
      have : grp = [] := List.eq_nil_of_length_eq_zero (by rw [← hgl, h0]; rfl)
      subst this
      cases hst : naF m [] with
      | none => exact Or.inl rfl
      | some pr =>
      obtain ⟨rn, m1⟩ := pr
      obtain ⟨x, a1, hrun, hS1, hg1, hxH, hxd⟩ := naF_ok dn vis fe m m1 a rn hst hS
      exact Or.inr ⟨rn, m1, a1, rfl, hS1, hg1, MFr.of_frame (naF_frame hst) (by simp [NAREC, NASLOT]) (by simp),
        naF_afr hst, hxH, by rw [hxd]; exact hrun⟩
    · rw [if_neg h0]
      obtain ⟨⟨cg, tg⟩, grp', rfl⟩ : ∃ x grp', grp = x :: grp' := by
        cases grp with
        | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hgl)) h0
        | cons x grp' => exact ⟨x, grp', rfl⟩
      simp only [List.length_cons] at hgb
      obtain ⟨w, cw, tw, hrw, hw1, hrc, hcH, hcd, -, -, -⟩ := hgrp.head (by omega) htop
      rw [UInt64.ofNat_toNat] at hrw
      rw [hrw, hrc]
      exact Or.inr ⟨[cw], m, a, rfl, hS, IWGrow.refl _, MFr.refl _ _ _, AFr.refl _, hcH,
        by simp only [List.headD_cons]; rw [hcd]; rfl⟩
  rcases hhn with hnone | ⟨rn, m1, a1, hrn, hS1, hg1, hf1, hfa1, hrnH, hrun1⟩
  · rw [hnone] at h; simp [nbFrameK1] at h
  rw [hrn, nbFrameK1_some] at h
  have hrnb : ¬ 4294967296 ≤ rn.headD 0 := by
    have : ¬ (4294967296 : Word).toNat ≤ (rn.headD 0).toNat := by simpa using hrnH
    exact fun e => this (UInt64.le_iff_toNat_le.mp e)
  rw [if_neg hrnb] at h
  -- the instantiation `hn.{us} ds`, typed
  cases hic : ceinternW m1 (rn.headD 0) us with
  | none => rw [hic] at h; simp [nbFrameK2] at h
  | some pr2 =>
  obtain ⟨hc, m2⟩ := pr2
  rw [hic, nbFrameK2_some] at h
  by_cases hcb : 4294967296 ≤ hc
  · rw [if_pos hcb] at h; cases h
  rw [if_neg hcb] at h
  have hcH : H hc := by
    have : ¬ (4294967296 : Word).toNat ≤ hc.toNat := fun e => hcb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internConst_stage hS1 (rn.headD 0) us hrnH hus hic
  have hg12 := hg1.trans hg2
  cases hma : mknF m2 [hc, dO, dL] with
  | none => rw [hma] at h; simp [nbFrameK3] at h
  | some pr3 =>
  obtain ⟨ra, m3⟩ := pr3
  rw [hma, nbFrameK3_some] at h
  obtain ⟨app, a3, hrun3, hS3, hg3, happH, happd⟩ := mknF_ok dn vis fe hc dO dL hcH ds m2 m3 a2 ra hma
    ⟨hS2, (hds.grow (OMono.decHL _ _) hg12).get (OMono.decHL _ _)⟩
  cases hit : stubM "infer_type_core" m3 [vis, hi, ra.headD 0] with
  | none => rw [hit] at h; simp [nbFrameK4] at h
  | some pr4 =>
  obtain ⟨rt, m4⟩ := pr4
  rw [hit, nbFrameK4_some] at h
  obtain ⟨ty, a4, hrun4, hS4, hg4, -⟩ := inferTypeCore_spec dn vis fe hi _ happH m3 m4 a3 rt hit hS3
  have hg14 := (hg12.trans hg3).trans hg4
  -- the stack grown and the names
  cases hfg : fgW n m4 hi us dO dL gO gL po pl 0 0 with
  | none => rw [hfg] at h; simp [nbFrameK5] at h
  | some pr5 =>
  obtain ⟨rp, m5⟩ := pr5
  rw [hfg, nbFrameK5_some] at h
  obtain ⟨hS5, hg5, hP5, hN5, hNb5⟩ := fgW_ok dn vis fe hi us dO dL ds hus n m4 m5 a4 gO gL po pl 0 0 grp prog [] rp
    hfg hS4 (hds.grow (OMono.decHL _ _) hg14) hgl (by have := hg14.1; omega) (hgrp.grow hgb hg14)
    (hW.hs.grow hg14) (by simp [decHL, hslice?]) (by simp)
  simp only [List.nil_append] at hP5 hN5
  -- the group's constructors
  cases hgc : gcW n m5 vis nPc (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0) 0 0 with
  | none => rw [hgc] at h; simp [nbFrameK6] at h
  | some pr6 =>
  obtain ⟨rc, m6⟩ := pr6
  rw [hgc, nbFrameK6_some] at h
  obtain ⟨ctors, a6, hrun6, hS6, hg6, hcl6, hcb6, hcs6⟩ := gcW_ok dn fe vis nPc hcs n m5 m6 a4 _ _ 0 0 (grp.map (·.1)) []
    rc hgc hS5 hN5 (fun j hj => by omega) (by simp) (by simp) (fun i hi => by simp at hi)
  -- the holes
  have hg46 := hg5.trans hg6
  cases hfh : fhW n m6 hi gO gL 0 0 with
  | none => rw [hfh] at h; simp [nbFrameK7] at h
  | some pr7 =>
  obtain ⟨rh, m7⟩ := pr7
  rw [hfh, nbFrameK7_some] at h
  obtain ⟨holes, a7, hrun7, hS7, hg7, hH7, hHb7⟩ := fhW_ok dn vis fe n m6 m7 a6 hi gO gL 0 0 grp [] rh hfh hS6 hgl
    (by have := (hg14.trans hg46).1; omega) (hgrp.grow hgb (hg14.trans hg46)) (by simp [decHL, hslice?]) (by simp)
  simp only [List.nil_append] at hH7
  by_cases hov : hi + gL < hi
  · rw [if_pos hov] at h; cases h
  rw [if_neg hov] at h
  by_cases hov2 : dL + gL < dL
  · rw [if_pos hov2] at h; cases h
  rw [if_neg hov2] at h
  have hhg : (hi + gL).toNat = hi.toNat + gL.toNat := pos2_word_add hov
  have hdg : (dL + gL).toNat = dL.toNat + gL.toNat := pos2_word_add hov2
  have hg47 := (hg5.trans hg6).trans hg7
  have hg17 := (hg14.trans hg47)
  have htop7 : iwTop m7 < 2 ^ 64 := Nat.lt_of_le_of_lt hS7.2.1 hS7.2.2.2.1
  cases hct : nbCtorsW n m7 vis ctx 0 fu (rp.headD 0) (rp.tail.headD 0) (hi + gL) us dO dL (rp.tail.tail.headD 0)
      (rp.tail.tail.tail.headD 0) (rh.headD 0) (rh.tail.headD 0) (rc.headD 0) (rc.tail.headD 0) ns 0 0 with
  | none => rw [hct] at h; simp [nbFrameK8] at h
  | some pr8 =>
  obtain ⟨r8, m8⟩ := pr8
  rw [hct, nbFrameK8_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hP7 := hP5.grow (hg6.trans hg7)
  have hpl2 : (rp.tail.headD 0).toNat = pl.toNat + gL.toNat := by rw [← hP7.1, List.length_append, hW.len]; simp [hgl]
  obtain ⟨x, a8, hrun8, hS8, hg8, -, -, hns8, hPm8, hA8⟩ := hCtors m7 m8 a7 ctx 0 fu _ _ (hi + gL) us dO dL _ _ _ _ _ _ ns 0 0
    c (prog ++ grp.map fun x => (⟨⟨x.1, decI us, ds⟩, hi.toNat⟩ : NestHole)) ds (grp.map (·.1)) holes ctors NS [] r8
    hct hS7 ⟨hW.u.grow hg17, hP7, by
      have := hW.hb; rw [hW.len] at hhi; simp only [NestCtx.hiAt] at this hhi ⊢; rw [hpl2]
      have := (hi + gL).toNat_lt; omega⟩
    ⟨hus, hds.grow (OMono.decHL _ _) hg17, by have := hg17.1; omega,
      by rw [decHL_agree (RdS.of_grow (hg6.trans hg7)) (fun j hj => by omega)]; exact hN5,
      by have := (hg6.trans hg7).1; omega, by simp only [List.length_map]; rw [← hgl, ← hdg]; exact (dL + gL).toNat_lt,
      hH7, hHb7⟩
    hcl6 (by have := hg7.1; omega) (hcs6.grow hcb6 hg7) (hns.grow hg17 htop) (OutsB.nil _ _) (by simp)
    ((((((hP.fr hf1).fr (ceinternW_mfr hic)).fr (MFr.ofMknF hma)).stub (by decide) hit).fr
      (fgW_mfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfg)).fr (gcW_mfr _ _ _ _ _ _ _ _ _ _ hgc) |>.fr
      (fhW_mfr _ _ _ _ _ _ _ _ _ hfh))
    (fhW_afr _ _ _ _ _ _ _ _ _ hfh (gcW_afr _ _ _ _ _ _ _ _ _ _ hgc (fgW_afr _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfg
      (stub_afr hit (by decide) (mknF_afr hma (ceinternW_afr hic (hfa1 hA)))))))
  refine ⟨x.2, a8, ?_, hS8, hg17.trans hg8, by simpa using hns8, hPm8, hA8⟩
  rw [ConRon.Arena.nestFrame.eq_def]
  have hz : (grp.zipIdx.mapM fun ((_, ty), i) => internFVarE (hi.toNat + i) ty) = pos2FhT hi.toNat grp := by
    simpa using pos2_zipIdx_holes hi.toNat grp 0
  have e2 : (internConstE (decI (rn.headD 0)) (decI us)).run a1 = .ok (decI hc, a2) := hrun2
  rw [happd] at hrun4
  have e8 : (ConRon.Arena.nestCtors V fe c false fu.toNat
      (prog ++ grp.map fun (c, _) => { key := ⟨c, decI us, ds⟩, base := hi.toNat }) (hi.toNat + grp.length)
      (decI us) ds (grp.map (·.1)) holes ctors NS []).run a7 = .ok (x, a8) := by
    rw [hhg, hgl] at hrun8; simpa using hrun8
  cases grp with
  | nil =>
    simp only at hrun1
    simp only [StateT.run_bind, hrun1, except_ok_bind, e2, hrun3, hrun4, hrun6, hz, hrun7, e8]
    rfl
  | cons xg grp' =>
    obtain ⟨cg, tg⟩ := xg
    simp only at hrun1
    simp only [StateT.run_bind, hrun1, except_ok_bind, e2, hrun3, hrun4, hrun6, hz, hrun7, e8]
    rfl



theorem newOK_step (n : Nat) (ih : NbOK dn vis fe n) : NewOK dn vis fe (n + 1) := by
  obtain ⟨-, -, -, -, -, -, hFrame, -, -, -, -⟩ := ih
  intro m m' a ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS r h hS hW hnn hus hds hdsb hcty hns hP hA
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hdsD := hds.get (OMono.decHL _ _)
  have hhi0 : c.hiAt 0 < 2 ^ 64 := by have := hW.hb; simp only [NestCtx.hiAt] at this ⊢; omega
  rw [nbNewW_succ] at h
  -- the walk stack
  cases n with
  | zero => simp [nwsWf, nbNewK1] at h
  | succ n' =>
  simp only [nwsWf] at h
  cases hws : nwsW n' m ctx dO dL po pl with
  | none => rw [hws] at h; simp [nbNewK1] at h
  | some pr =>
  obtain ⟨rw, m1⟩ := pr
  rw [hws, nbNewK1_some] at h
  obtain ⟨wp, a1, hrun1, hS1, hg1, hwp⟩ := nwsW_ok dn fe vis n' m m1 a ctx dO dL po pl c ds prog rw hws hS
    hW.u.dec hW.u.inn hhi0 hdsD (fun j hj => by omega)
  have hWp : WCtx dn vis fe m1 ctx (rw.headD 0) (rw.tail.headD 0) c wp := by
    rcases hwp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hW.u.grow hg1, ⟨rfl, by simp, fun i hi => by simp at hi⟩, by simpa using hhi0⟩
    · exact hW.grow hg1
  -- the mates
  cases hfm : nfmW (n' + 1) m1 vis nn with
  | none => rw [hfm] at h; simp [nbNewK2] at h
  | some pr2 =>
  obtain ⟨rm, m2⟩ := pr2
  rw [hfm, nbNewK2_some] at h
  obtain ⟨hS2, hg2, hmd, hmb⟩ := nfmW_ok hfm hS1 hnn
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have hWp2 := hWp.grow hg2
  have hhw : (nhiW m2 ctx (rw.tail.headD 0)).toNat = c.hiAt wp.length := hWp2.hi htop2
  -- the group, from the instantiation met
  cases hpr : posRecW m2 [nn, cty] with
  | none => rw [hpr] at h; simp [nbNewK3] at h
  | some pr3 =>
  obtain ⟨pw, m3⟩ := pr3
  rw [hpr, nbNewK3_some] at h
  obtain ⟨hS3, hg3, hpq, ht3, hget3⟩ := posRecW_stage hpr hS2 (by simp)
  simp only [List.length_cons, List.length_nil] at ht3
  cases hn1 : new1W m3 pw with
  | none => rw [hn1] at h; simp [nbNewK4] at h
  | some pr4 =>
  obtain ⟨g0, m4⟩ := pr4
  rw [hn1, nbNewK4_some] at h
  obtain ⟨hn1r, hg0⟩ := new1W_rec hn1
  obtain ⟨hS4, hg4, hg0q, ht4, hget4⟩ := posRecW_stage hn1r hS3 (by simp)
  simp only [List.length_cons, List.length_nil] at ht4
  have hgrp0 : GrpAt m4 (g0.headD 0).toNat [(decI nn, decI cty)] := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    have e0 := hget3 0 (by simp); have e1 := hget3 1 (by simp)
    simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ] at e0 e1
    refine ⟨pw, nn, cty, by simpa using hget4 0 (by simp), by omega,
      by rw [hg4.2.2.1 _ (by omega)]; exact e0, hnn, rfl, by rw [hg4.2.2.1 _ (by omega)]; exact e1, hcty, rfl⟩
  rw [hg0] at h
  simp only [List.headD_cons, List.tail_cons] at h
  have hg24 := hg3.trans hg4
  -- grown by the mates
  cases hgg : ggW (n' + 1) m4 vis ctx (nhiW m2 ctx (rw.tail.headD 0)) us dO dL (rm.headD 0) (rm.tail.headD 0)
      (g0.headD 0) 1 with
  | none => rw [hgg] at h; simp [nbNewK5] at h
  | some pr5 =>
  obtain ⟨rg, m5⟩ := pr5
  rw [hgg, nbNewK5_some] at h
  have hg14 := hg1.trans (hg2.trans hg24)
  obtain ⟨grp, a5, hrun5, hS5, hg5, hgl5, hgb5, hgrp5, hP5⟩ := ggW_ok dn fe vis ctx (nhiW m2 ctx (rw.tail.headD 0)) us
    dO dL (c.hiAt wp.length) hhw c ds hus (n' + 1) m4 m5 a1 (rm.headD 0) (rm.tail.headD 0) (g0.headD 0) 1
    (nestFrameMates fe (decI nn)) [(decI nn, decI cty)] rg hgg hS4 (hW.u.grow hg14)
    (by rw [decHL_agree (RdS.of_grow hg14) (fun j hj => by omega)]; exact hdsD) (by have := hg14.1; omega)
    (by rw [decHL_agree (RdS.of_grow hg24) (fun j hj => by omega)]; exact hmd)
    (fun j hj => by have := hg24.1; omega) (by simp) (by simp only [List.length_cons, List.length_nil]; omega) hgrp0
    ((((hP.fr (nwsW_mfr hws)).fr (nfmW_mfr hfm)).fr (posRecW_mfr hpr)).fr (new1W_mfr hn1))
  have hA5 : AbsOK m5 := ggW_afr _ _ _ _ _ _ _ _ _ _ _ _ _ _ hgg
    (new1W_afr hn1 (posRecW_afr hpr (nfmW_afr hfm (nwsW_afr hws hA))))
  have hg15 := hg14.trans hg5
  have htop5 : iwTop m5 < 2 ^ 64 := Nat.lt_of_le_of_lt hS5.2.1 hS5.2.2.2.1
  -- its keys, then the active list
  cases hca : caW (n' + 1) m5 us dO dL (rg.headD 0) (rg.tail.headD 0) 0 0 with
  | none => rw [hca] at h; simp [nbNewK6] at h
  | some pr6 =>
  obtain ⟨ra, m6⟩ := pr6
  rw [hca, nbNewK6_some] at h
  obtain ⟨hS6, hg6, hka, hkab⟩ := caW_ok dn vis fe us dO dL ds hus (n' + 1) m5 m6 a5 _ _ 0 0 grp [] ra hca hS5
    (hds.grow (OMono.decHL _ _) hg15) (by simpa using hgl5) hgb5 hgrp5 (KsB.nil _ _) (by simp)
  simp only [List.nil_append] at hka
  obtain ⟨hp6, hk0, ha0, hn0⟩ := nsb_words hns htop
  have hg16 := hg15.trans hg6
  rw [pos2_ns_rd hg16 hp6 htop 2 (by decide), pos2_ns_rd hg16 hp6 htop 3 (by decide)] at h
  cases hap : appendW (n' + 1) m6 (ra.headD 0) (ra.tail.headD 0) (rdW (m.arr64 IW) (ns + 2))
      (rdW (m.arr64 IW) (ns + 3)) with
  | none => rw [hap] at h; simp [nbNewK7] at h
  | some pr7 =>
  obtain ⟨rap, m7⟩ := pr7
  rw [hap, nbNewK7_some] at h
  obtain ⟨hS7, hg7, h70, h71, ht7, hw71, hw72⟩ := appendW_stage hap hS6 hkab
    (by have := hns.b2; have := hg16.1; omega)
  have hact7 : KsB m7 (rap.headD 0).toNat (rap.tail.headD 0).toNat
      (grp.map (fun x => (⟨x.1, decI us, ds⟩ : NestKey)) ++ NS.active) := by
    rw [h70, h71]
    exact pos2_decB_append decNK_mono hka (ha0.grow hg16) hg7 (by omega) hw71 hw72
  have hg17 := hg16.trans hg7
  rw [pos2_rd_grow hg17 (by omega), pos2_ns_rd hg17 hp6 htop 1 (by decide), pos2_ns_rd hg17 hp6 htop 4 (by decide),
    pos2_ns_rd hg17 hp6 htop 5 (by decide)] at h
  cases hq1 : posRecW m7 [rdW (m.arr64 IW) ns, rdW (m.arr64 IW) (ns + 1), rap.headD 0, rap.tail.headD 0,
      rdW (m.arr64 IW) (ns + 4), rdW (m.arr64 IW) (ns + 5)] with
  | none => rw [hq1] at h; simp [nbNewK8] at h
  | some pr8 =>
  obtain ⟨ns1, m8⟩ := pr8
  rw [hq1, nbNewK8_some] at h
  obtain ⟨hS8, hg8, hq8, ht8, hget8⟩ := posRecW_stage hq1 hS7 (by simp)
  simp only [List.length_cons, List.length_nil] at ht8
  have hg18 := hg17.trans hg8
  have hns1 := nsb_rec6 (m' := m8) (q := ns1) (keys := NS.keys.toList)
    (act := grp.map (fun x => (⟨x.1, decI us, ds⟩ : NestKey)) ++ NS.active) (nfs := NS.ctorNfs.toList) (by omega)
    (Nat.lt_of_le_of_lt hS8.2.1 hS8.2.2.2.1) hget8 (hk0.grow hg18) (by have := hns.b0; have := hg18.1; omega)
    (hact7.grow hg8) (by have := hg8.1; omega) (hn0.grow hg18) (by have := hns.b4; have := hg18.1; omega)
  simp only [Array.toArray_toList] at hns1
  -- the frame
  cases hfr : nbFrameW (n' + 1) m8 vis ctx fu (rw.headD 0) (rw.tail.headD 0) (nhiW m2 ctx (rw.tail.headD 0)) us dO dL
      nPc (rg.headD 0) (rg.tail.headD 0) ns1 with
  | none => rw [hfr] at h; simp [nbNewK9] at h
  | some pr9 =>
  obtain ⟨r9, m9⟩ := pr9
  rw [hfr, nbNewK9_some] at h
  have hg58 := (hg6.trans hg7).trans hg8
  obtain ⟨x9, a9, hrun9, hS9, hg9, hns9, hP9, hA9⟩ := hFrame m8 m9 a5 ctx fu _ _ _ us dO dL nPc _ _ ns1 c wp ds grp _ r9 hfr
    hS8 (hWp2.grow ((hg24.trans hg5).trans hg58)) hhw hus (hds.grow (OMono.decHL _ _) hg18)
    (by have := hg18.1; omega) (by simpa using hgl5) (by have := hg58.1; omega) (hgrp5.grow hgb5 hg58) hns1
    (((hP5.fr (caW_mfr _ _ _ _ _ _ _ _ _ _ _ hca)).fr (appendW_mfr hap)).fr (posRecW_mfr hq1))
    (posRecW_afr hq1 (appendW_afr hap (caW_afr _ _ _ _ _ _ _ _ _ _ _ hca hA5)))
  have hg19 := hg18.trans hg9
  rw [pos2_ns_rd hg19 hp6 htop 2 (by decide), pos2_ns_rd hg19 hp6 htop 3 (by decide)] at h
  cases hcf : cfW (n' + 1) m9 ctx us dO dL (rg.headD 0) (rg.tail.headD 0) (r9.headD 0) (rdW (m.arr64 IW) (ns + 2))
      (rdW (m.arr64 IW) (ns + 3)) kb with
  | none => rw [hcf] at h; simp [nbAppK6] at h
  | some pr10 =>
  obtain ⟨r10, m10⟩ := pr10
  rw [hcf, nbAppK6_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨x, a', hrun10, hS10, hg10, -, hk10, hns10⟩ := cfW_ok dn vis fe hcf hS9 (hW.u.grow hg19) hhi0 hus
    (hds.grow (OMono.decHL _ _) hg19) (by have := hg19.1; omega) (by simpa using hgl5)
    (by have := (hg58.trans hg9).1; omega) (hgrp5.grow hgb5 (hg58.trans hg9)) hns9 (ha0.grow hg19)
    (by have := hns.b2; have := hg19.1; omega)
  refine ⟨x, a', ?_, hS10, hg19.trans hg10, by simpa using hk10, by simpa using hns10, hP9.fr (cfW_mfr hcf),
    cfW_afr hcf hA9⟩
  rw [hhw] at hrun9
  rw [ConRon.Arena.nestContNew.eq_def]
  simp only [StateT.run_bind, hrun1, except_ok_bind, hrun5, hrun9]
  exact hrun10

theorem keyOK_step (n : Nat) (ih : NbOK dn vis fe n) : KeyOK dn vis fe (n + 1) := by
  obtain ⟨-, -, -, -, -, hNew, -, -, -, -, -⟩ := ih
  intro m m' a ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS r h hS hW hnn hus hds hdsb hcty hns hP hA
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hhi0 : c.hiAt 0 < 2 ^ 64 := by have := hW.hb; simp only [NestCtx.hiAt] at this ⊢; omega
  rw [nbKeyW_succ] at h
  cases hk : posRecW m [nn, us, dO, dL] with
  | none => rw [hk] at h; simp [nbKeyK1] at h
  | some pr =>
  obtain ⟨key, m1⟩ := pr
  rw [hk, nbKeyK1_some] at h
  obtain ⟨hS1, hg1, hkq, ht1, hget1⟩ := posRecW_stage hk hS (by simp)
  simp only [List.length_cons, List.length_nil] at ht1
  have hK : DecB (fun m => decNK m key.toNat) m1 ⟨decI nn, decI us, ds⟩ :=
    pos2_key_rec hnn hus (by omega) hget1 (hds.grow (OMono.decHL _ _) hg1)
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨hp6, hk0, ha0, -⟩ := nsb_words hns htop
  rw [pos2_ns_rd hg1 hp6 htop 2 (by decide), pos2_ns_rd hg1 hp6 htop 3 (by decide)] at h
  -- not in progress
  cases hc1 : nkcW n m1 (rdW (m.arr64 IW) (ns + 2)) (rdW (m.arr64 IW) (ns + 3)) key with
  | none => rw [hc1] at h; cases h
  | some b1 =>
  rw [hc1] at h
  simp only at h
  have hb1 := nkcW_ok key _ n m1 _ _ b1 NS.active hc1 (ha0.grow hg1) hK htop1
  by_cases hb1n : b1 ≠ 0
  · rw [if_pos hb1n] at h; cases h
  rw [if_neg hb1n] at h
  have hact : NS.active.contains ⟨decI nn, decI us, ds⟩ = false := by
    cases e : NS.active.contains ⟨decI nn, decI us, ds⟩ with
    | false => rfl
    | true => rw [e] at hb1; simp at hb1n; rw [hb1n] at hb1; exact absurd hb1 (by decide)
  -- closed?
  cases n with
  | zero => simp [dcWf, nbKeyK2] at h
  | succ n' =>
  cases hdc : dcWf (n' + 1) m1 ctx dO dL with
  | none => rw [hdc] at h; simp [nbKeyK2] at h
  | some pr2 =>
  obtain ⟨r2, m2⟩ := pr2
  rw [hdc, nbKeyK2_some] at h
  obtain ⟨bc, a2, hrun2, hS2, hg2, hr2⟩ := dcWf_ok dn fe vis (n' + 1) m1 m2 a ctx dO dL c ds r2 hdc hS1
    (hW.grow hg1).u.dec (hW.grow hg1).u.inn hhi0 ((hds.grow (OMono.decHL _ _) hg1).get (OMono.decHL _ _))
    (fun j hj => by have := hg1.1; omega)
  have hg12 := hg1.trans hg2
  have hP2 : PosMR m2 := (hP.fr (posRecW_mfr hk)).fr (dcWf_mfr hdc)
  have hA2 : AbsOK m2 := dcWf_afr hdc (posRecW_afr hk hA)
  -- the frame, when not cached
  have hnew : ∀ (rr : List Word) (mm : Mem),
      nbAppK6 (nbNewW (n' + 1) m2 vis ctx fu po pl kb nn us dO dL nPc cty ns) = some (rr, mm) →
      ∃ x a', (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a2 =
          .ok (x, a') ∧ StageR dn vis fe mm a' ∧ IWGrow m2 mm ∧ decNFK (rr.headD 0) = some x.1 ∧
        NSB mm (rr.tail.headD 0) x.2 ∧ PosMR mm ∧ AbsOK mm := by
    intro rr mm hh
    cases hn : nbNewW (n' + 1) m2 vis ctx fu po pl kb nn us dO dL nPc cty ns with
    | none => rw [hn] at hh; simp [nbAppK6] at hh
    | some pr3 =>
    obtain ⟨r3, m3⟩ := pr3
    rw [hn, nbAppK6_some] at hh
    simp only [Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    obtain ⟨x, a', hrun, hS3, hg3, hk3, hns3, hP3, hA3⟩ := hNew m2 m3 a2 ctx fu po pl kb nn us dO dL nPc cty ns c
      prog ds NS r3 hn hS2 (hW.grow hg12) hnn hus (hds.grow (OMono.decHL _ _) hg12) (by have := hg12.1; omega) hcty
      (hns.grow hg12 htop) hP2 hA2
    exact ⟨x, a', hrun, hS3, hg3, by simpa using hk3, by simpa using hns3, hP3, hA3⟩
  have hrun2' : (ds.allM fun x => do
      let b ← fvarB coreWalkFuel x
      pure (decide (b ≤ c.hiAt 0))).run a = .ok (bc, a2) := hrun2
  have htwin : (nestContKey V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a =
      (if bc && NS.keys.contains ⟨decI nn, decI us, ds⟩ then pure (NestFieldKind.nested (kb.toNat != 0), NS)
       else nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a2 := by
    rw [ConRon.Arena.nestContKey.eq_def]
    simp only [hact, Bool.false_eq_true, ite_false, StateT.run_bind, hrun2', except_ok_bind]
  by_cases hr2n : r2.headD 0 ≠ 0
  · rw [if_pos hr2n] at h
    have hbc : bc = true := by cases bc <;> simp_all
    subst hbc
    rw [pos2_rd_grow hg12 (by omega), pos2_ns_rd hg12 hp6 htop 1 (by decide)] at h
    cases hc2 : nkcW (n' + 1) m2 (rdW (m.arr64 IW) ns) (rdW (m.arr64 IW) (ns + 1)) key with
    | none => rw [hc2] at h; cases h
    | some b2 =>
    rw [hc2] at h
    simp only at h
    have hb2 := nkcW_ok key _ (n' + 1) m2 _ _ b2 NS.keys.toList hc2 (hk0.grow hg12) (hK.grow (decNK_mono _) hg2)
      (Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1)
    by_cases hb2n : b2 ≠ 0
    · rw [if_pos hb2n] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hin : NS.keys.contains ⟨decI nn, decI us, ds⟩ = true := by
        rw [← Array.contains_toList]
        cases e : NS.keys.toList.contains ⟨decI nn, decI us, ds⟩ with
        | true => rfl
        | false => rw [e] at hb2; exact absurd hb2 (by simpa using hb2n)
      refine ⟨(NestFieldKind.nested (kb.toNat != 0), NS), a2, by rw [htwin]; simp [hin]; rfl, hS2, hg12,
        by simpa using decNFK_nestedW kb, by simpa using hns.grow hg12 htop, hP2, hA2⟩
    · rw [if_neg hb2n] at h
      have hout : NS.keys.contains ⟨decI nn, decI us, ds⟩ = false := by
        rw [← Array.contains_toList]
        cases e : NS.keys.toList.contains ⟨decI nn, decI us, ds⟩ with
        | false => rfl
        | true => rw [e] at hb2; simp at hb2n hb2; rw [hb2n] at hb2; exact absurd hb2 (by decide)
      obtain ⟨x, a', hrun, rest⟩ := hnew r m' h
      exact ⟨x, a', by rw [htwin]; simpa [hout] using hrun, rest.1, hg12.trans rest.2.1, rest.2.2⟩
  · rw [if_neg hr2n] at h
    have hbc : bc = false := by cases bc <;> simp_all
    subst hbc
    obtain ⟨x, a', hrun, rest⟩ := hnew r m' h
    exact ⟨x, a', by rw [htwin]; simpa using hrun, rest.1, hg12.trans rest.2.1, rest.2.2⟩

include hcs in
theorem contOK_step (n : Nat) (hk : 2 ^ 31 + (n + 1) ≤ coreWalkFuel) (ih : NbOK dn vis fe n) :
    ContOK dn vis fe (n + 1) := by
  obtain ⟨-, -, -, -, hKey, -, -, -, -, -, -⟩ := ih
  intro m m' a ctx fu po pl kb nn us aO aL ns c prog args NS r h hS hW hnn hus hargs hab hns hP hA
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbContW_succ] at h
  cases n with
  | zero => simp [ntWf, nbContK1] at h
  | succ n' =>
  simp only [ntWf] at h
  cases hnt : ntW n' m vis nn with
  | none => rw [hnt] at h; simp [nbContK1] at h
  | some pr =>
  obtain ⟨r1, m1⟩ := pr
  rw [hnt, nbContK1_some] at h
  obtain ⟨xc, a1, hrun1, hS1, hg1, hnc⟩ := ntW_ok dn fe vis nn hnn hcs n' m m1 a r1 hnt hS
  cases xc with
  | none => simp only [NcOut] at hnc; rw [if_pos hnc] at h; cases h
  | some pc =>
  obtain ⟨nPc, ctors⟩ := pc
  obtain ⟨hnc0, hnc1, -, -, -⟩ := hnc
  rw [if_neg (by rw [hnc0]; decide)] at h
  have hal := decHL_length m hargs
  by_cases hlt : aL < r1.tail.headD 0
  · rw [if_pos hlt] at h; cases h
  rw [if_neg hlt] at h
  have hle : nPc ≤ args.length := by
    have : ¬ aL.toNat < (r1.tail.headD 0).toNat := fun e => hlt (UInt64.lt_iff_toNat_lt.mpr e)
    omega
  generalize hPw : r1.tail.headD 0 = nPcW at h hnc1
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  have hW1 := hW.grow hg1
  have hhp : (nhiW m1 ctx pl).toNat = c.hiAt prog.length := hW1.hi htop1
  have hargs1 : decHL m1 aO.toNat aL.toNat = some args := by
    rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hargs
  obtain ⟨hds, hidx⟩ := pos2_decHL_split hargs1 (show nPcW.toNat ≤ aL.toNat by omega)
  have hab1 : aO.toNat + aL.toNat ≤ iwTop m1 := by have := hg1.1; omega
  have hPle : nPcW.toNat ≤ aL.toNat := by omega
  have hiO : (aO + nPcW).toNat = aO.toNat + nPcW.toNat := word_add_toNat (by omega)
  have hiL : (aL - nPcW).toNat = aL.toNat - nPcW.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
  -- the checks
  cases hcc : p2ccW (n' + 1) m1 ctx (nhiW m1 ctx pl) nn aO nPcW (aO + nPcW) (aL - nPcW) with
  | none => rw [hcc] at h; simp [nbContK2] at h
  | some pr2 =>
  obtain ⟨r2, m2⟩ := pr2
  rw [hcc, nbContK2_some] at h
  obtain ⟨-, q, a2, hrun2a, hrun2q, hq, hrun2c, -, hS2, hg2, hP2⟩ := p2ccW_ok dn vis fe (by omega) hcc hS1 hW1.u hds
    (fun j hj => by omega) (by rw [hiO, hiL]; exact hidx) (fun j hj => by rw [hiO, hiL] at *; omega) hnn
    (hP.fr (ntWf_mfr (k := n' + 1) (by simpa [ntWf] using hnt)))
  have hA2 : AbsOK m2 := p2ccW_afr hcc (ntWf_afr (k := n' + 1) (by simpa [ntWf] using hnt) hA)
  -- the instantiation's former
  cases hk4 : posRecW m2 [nn, us, aO, nPcW] with
  | none => rw [hk4] at h; simp [nbContK3] at h
  | some pr3 =>
  obtain ⟨key, m3⟩ := pr3
  rw [hk4, nbContK3_some] at h
  obtain ⟨hS3, hg3, hkq, ht3, hget3⟩ := posRecW_stage hk4 hS2 (by simp)
  simp only [List.length_cons, List.length_nil] at ht3
  have hg13 := hg1.trans (hg2.trans hg3)
  have hab3 : aO.toNat + aL.toNat ≤ iwTop m3 := by have := (hg2.trans hg3).1; omega
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  have hdsB : DecB (fun m => (decHL m aO.toNat nPcW.toNat : Option (List EIdx))) m3 (args.take nPcW.toNat) :=
    decHL_decB (by rw [decHL_agree (RdS.of_grow (hg2.trans hg3)) (fun j hj => by omega)]; exact hds)
      (by have := (hg2.trans hg3).1; omega)
  have hK : DecB (fun m => decNK m key.toNat) m3 ⟨decI nn, decI us, args.take nPcW.toNat⟩ :=
    pos2_key_rec hnn hus (by omega) hget3 hdsB
  obtain ⟨hKd, hKin⟩ := pos2_nk_in hK
  simp only [nitWf] at h
  cases hni : nitW n' m3 vis ctx (nhiW m1 ctx pl) key with
  | none => rw [hni] at h; simp [nbContK4] at h
  | some pr4 =>
  obtain ⟨r4, m4⟩ := pr4
  rw [hni, nbContK4_some] at h
  have hksl : NKSl m3 key := by
    unfold NKSl
    rw [pos2_rd_get (by simpa using hget3 2 (by simp)) (by simp; omega),
      pos2_rd_get (by simpa using hget3 3 (by simp)) (by simp; omega)]
    have := (hg2.trans hg3).1; omega
  obtain ⟨xi, a4, hrun4, hS4, hg4, hni0, hctyH, hctyd, hP4⟩ := nitW_ok n' dn fe vis ctx (nhiW m1 ctx pl)
    (c.hiAt prog.length) hhp c m3 m4 a2 key _ r4 hni hS3 ((hW1.grow (hg2.trans hg3)).u) hKd hKin hksl
    (hP2.fr (posRecW_mfr hk4))
  have hA4 : AbsOK m4 := nitW_afr hni (posRecW_afr hk4 hA2)
  by_cases hne : aL ≠ nPcW + r4.headD 0
  · rw [if_pos hne] at h; cases h
  rw [if_neg hne] at h
  have heq : args.length = nPc + xi.1 := by
    have := (pos2_len_eq (nI := r4.headD 0) (show nPcW.toNat ≤ aL.toNat by omega)).mp (by simpa using hne)
    omega
  -- the instantiation met
  cases hky : nbKeyW (n' + 1) m4 vis ctx fu po pl kb nn us aO nPcW nPcW (r4.tail.headD 0) ns with
  | none => rw [hky] at h; simp [nbAppK6] at h
  | some pr5 =>
  obtain ⟨r5, m5⟩ := pr5
  rw [hky, nbAppK6_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hg14 := hg13.trans hg4
  obtain ⟨x, a', hrun5, hS5, hg5, hk5, hns5, hP5, hA5⟩ := hKey m4 m5 a4 ctx fu po pl kb nn us aO nPcW nPcW (r4.tail.headD 0)
    ns c prog (args.take nPcW.toNat) NS r5 hky hS4 (hW.grow hg14) hnn hus (hdsB.grow (OMono.decHL _ _) hg4)
    (by have := hg14.1; omega) hctyH (hns.grow hg14 htop) hP4 hA4
  refine ⟨x, a', ?_, hS5, hg14.trans hg5, by simpa using hk5, by simpa using hns5, hP5, hA5⟩
  rw [hnc1] at hrun2a hrun2c hrun4 hrun5
  rw [hhp] at hrun2a hrun2c
  rw [hctyd] at hrun5
  have hpc : ((args.take nPc).allM fun x => do
      let bb ← bvarB coreWalkFuel x
      if bb != 0 then pure false
      else do
        let fb ← fvarB coreWalkFuel x
        pure (decide (fb ≤ c.hiAt prog.length))).run a1 = .ok (true, a2) := hrun2c
  have hlt' : ¬ args.length < nPc := by omega
  rw [ConRon.Arena.nestCont.eq_def]
  simp only [StateT.run_bind, hrun1, except_ok_bind, hlt', ite_false, hrun2a, Bool.false_eq_true, hrun2q, hq,
    hpc, Bool.not_true, hrun4]
  simp only [heq, bne_self_eq_false, Bool.false_eq_true, ite_false]
  exact hrun5

theorem appOK_step (n : Nat) (ih : NbOK dn vis fe n) : AppOK dn vis fe (n + 1) := by
  obtain ⟨-, -, -, hCont, -, -, -, -, -, -, -⟩ := ih
  intro m m' a ctx fu po pl kb hi w ns c prog NS r h hS hW hhi hw hns hP hA
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbAppW_succ] at h
  cases hga : gaaF m [CWF, w] with
  | none => rw [hga] at h; simp [nbAppK1] at h
  | some pr =>
  obtain ⟨ra, m1⟩ := pr
  rw [hga, nbAppK1_some] at h
  obtain ⟨args, a1, hrun1, hS1, hg1, hargs, hargsb⟩ := gaaF_ok dn vis fe CWF w hw m m1 a ra hga hS
  rw [CWF_eq] at hrun1
  have e0 : ra.getD 0 0 = ra.headD 0 := by cases ra <;> rfl
  rw [e0, getD1_eq] at hargs hargsb
  cases hgf : gafF m1 [CWF, w] with
  | none => rw [hgf] at h; simp [nbAppK2] at h
  | some pr2 =>
  obtain ⟨rh, m2⟩ := pr2
  rw [hgf, nbAppK2_some] at h
  obtain ⟨hd, a2, hrun2, hS2, hg2, hhdH, hhdd⟩ := gafF_ok dn vis fe CWF w hw m1 m2 a1 rh hgf hS1
  rw [CWF_eq] at hrun2
  have hg12 := hg1.trans hg2
  have hP2 : PosMR m2 := (hP.fr (MFr.ofGaaF hga)).fr (MFr.ofGafF hgf)
  have hA2 : AbsOK m2 := gafF_afr hgf (gaaF_afr hga hA)
  by_cases hev : eViewW m2 (rh.headD 0) = []
  · rw [if_pos hev] at h; cases h
  rw [if_neg hev] at h
  obtain ⟨v, hview, hvr⟩ := eViewW_ok m2 a2 hS2.1.arena.1 (rh.headD 0) hev
  have hvrun : (view hd).run a2 = .ok (v, a2) := by rw [← hhdd, ← decE_eq]; exact view_run _ _ _ hview
  have hargs2 : decHL m2 (ra.headD 0).toNat (ra.tail.headD 0).toNat = some args := by
    rw [decHL_agree (RdS.of_grow hg2) (fun j hj => by omega)]; exact hargs
  by_cases h1 : (eViewW m2 (rh.headD 0)).headD 0 = 1
  · rw [if_pos h1] at h
    -- a hole
    obtain ⟨i, ty, rfl⟩ : ∃ i ty, v = .fvar i ty := by
      cases v <;> simp only [ViewR] at hvr <;> (try (rw [h1] at hvr; simp at hvr)) <;> exact ⟨_, _, rfl⟩
    obtain ⟨-, hi1, -, -⟩ := hvr
    rw [getD1_eq] at hi1
    cases hpf : pfW n m2 vis ctx po pl kb hi ((eViewW m2 (rh.headD 0)).tail.headD 0) (ra.headD 0) (ra.tail.headD 0) with
    | none => rw [hpf] at h; simp [nbAppK4] at h
    | some pr3 =>
    obtain ⟨rp, m3⟩ := pr3
    rw [hpf, nbAppK4_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hhi0 : c.hiAt 0 < 2 ^ 64 := by have := hW.hb; simp only [NestCtx.hiAt] at this ⊢; omega
    obtain ⟨k, a3, hK, hS3, hg3, hk, hP3⟩ := pfW_ok dn vis fe hpf hS2 (hW.grow hg12).u (hW.grow hg12).hs hhi0 hargs2
      (by have := hg2.1; omega) hP2
    refine ⟨(k, decI w, NS), a3, ?_, hS3, hg12.trans hg3, by simpa using hk, rfl,
      by simpa using (hns.grow (hg12.trans hg3) htop), hP3, pfW_afr hpf hA2⟩
    rw [hi1] at hK
    simp only [posAppT, StateT.run_bind, hrun1, except_ok_bind, hrun2, hvrun]
    rw [hK]; rfl
  rw [if_neg h1] at h
  have h3 : (eViewW m2 (rh.headD 0)).headD 0 = 3 := by
    by_cases h3 : (eViewW m2 (rh.headD 0)).headD 0 = 3
    · exact h3
    · rw [if_neg h3] at h; cases h
  rw [if_pos h3] at h
  -- a constant: a container
  obtain ⟨nn, us, rfl⟩ : ∃ nn us, v = .const nn us := by
    cases v <;> simp only [ViewR] at hvr <;> (try (rw [h3] at hvr; simp at hvr)) <;> exact ⟨_, _, rfl⟩
  obtain ⟨-, hnH, hnd, husH, husd⟩ := hvr
  rw [getD1_eq] at hnH hnd
  rw [pos2_getD2] at husH husd
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hn2, hnb2, -, -, -, -⟩ := ctx_fields (hW.grow hg12).u.dec (hW.grow hg12).u.inn htop2
  have hne2 := ctx_names_end (hW.grow hg12).u.dec (hW.grow hg12).u.inn (hW.grow hg12).u.sl htop2
  obtain ⟨ws, hws, hwsd, hwsH⟩ := slR_of_decHL m2 _ _ _ hn2 (by omega)
  simp only [UInt64.ofNat_toNat] at hws
  cases hco : containsW n m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1))
      ((eViewW m2 (rh.headD 0)).tail.headD 0) with
  | none => rw [hco] at h; simp [nbAppK5] at h
  | some o =>
  rw [hco, nbAppK5_some] at h
  have ho := containsW_ok n m2 _ _ _ o ws hws hco
  by_cases hon : o ≠ 0
  · rw [if_pos hon] at h; cases h
  rw [if_neg hon] at h
  have hnotin : c.names.contains nn = false := by
    rw [hwsd, ← hnd, pos2_contains_map ws hwsH _ hnH]
    cases e : ws.contains ((eViewW m2 (rh.headD 0)).tail.headD 0) with
    | false => rfl
    | true => rw [e] at ho; simp at hon; rw [hon] at ho; exact absurd ho (by decide)
  cases hct : nbContW n m2 vis ctx fu po pl kb ((eViewW m2 (rh.headD 0)).tail.headD 0)
      ((eViewW m2 (rh.headD 0)).tail.tail.headD 0) (ra.headD 0) (ra.tail.headD 0) ns with
  | none => rw [hct] at h; simp [nbAppK6] at h
  | some pr4 =>
  obtain ⟨rc, m4⟩ := pr4
  rw [hct, nbAppK6_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨x, a4, hrun4, hS4, hg4, hk4, hns4, hP4, hA4⟩ := hCont m2 m4 a2 ctx fu po pl kb _ _ _ _ ns c prog args NS rc
    hct hS2 (hW.grow hg12) hnH husH hargs2 (by have := hg2.1; omega) (hns.grow hg12 htop) hP2 hA2
  rw [hnd, husd] at hrun4
  refine ⟨(x.1, decI w, x.2), a4, ?_, hS4, hg12.trans hg4, by simpa using hk4, rfl, by simpa using hns4, hP4, hA4⟩
  simp only [posAppT, StateT.run_bind, hrun1, except_ok_bind, hrun2, hvrun, hnotin, Bool.false_eq_true, ite_false,
    hrun4]
  rfl

theorem bindOK_step (n : Nat) (ih : NbOK dn vis fe n) : BindOK dn vis fe (n + 1) := by
  obtain ⟨hPos, -, -, -, -, -, -, -, -, -, -⟩ := ih
  intro m m' a ctx fu po pl dep kb w ns c prog NS r h hS hW hw h6 hns hP hA
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbBindW_succ] at h
  by_cases hev : eViewW m w = []
  · rw [if_pos hev] at h; cases h
  rw [if_neg hev] at h
  obtain ⟨d, b, hv, hd, hb, hvb, htag⟩ := pos2_forall_view hS hw h6 hev
  rw [hv] at h
  simp only [List.tail_cons, List.headD_cons] at h
  -- the domain mentions no member and no hole
  obtain ⟨hn0, hnb0, -, -, hnP, -⟩ := ctx_fields hW.u.dec hW.u.inn htop
  have hne0 := ctx_names_end hW.u.dec hW.u.inn hW.u.sl htop
  have hhi := hW.hi htop
  cases hno : noConstWf n m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
      (nhiW m ctx pl) d with
  | none => rw [hno] at h; simp [nbBindK1] at h
  | some pr =>
  obtain ⟨o, m1⟩ := pr
  rw [hno, nbBindK1_some] at h
  obtain ⟨mp, hmp⟩ := hP.no
  obtain ⟨bo, hrun1, hbo, hM1, hS1, hg1, hf1⟩ := noConstWf_ok n dn fe vis m m1 a _ _ _ _ d o c.names mp hno hS hd hn0
    (by omega) hmp
  rw [hnP, hhi, decE_eq] at hrun1
  by_cases ho : o ≠ 0
  · rw [if_pos ho] at h; cases h
  rw [if_neg ho] at h
  have hbo' : bo = false := by rw [← hbo]; simpa using ho
  subst hbo'
  by_cases hd1 : dep + 1 = 0
  · rw [if_pos hd1] at h; cases h
  rw [if_neg hd1] at h
  by_cases hk1 : kb + 1 = 0
  · rw [if_pos hk1] at h; cases h
  rw [if_neg hk1] at h
  simp only [List.tail_cons, List.headD_cons] at h
  -- the variable, the body opened
  cases hfv : fvinternW m1 dep d with
  | none => rw [hfv] at h; simp [nbBindK2] at h
  | some pr2 =>
  obtain ⟨fv, m2⟩ := pr2
  rw [hfv, nbBindK2_some] at h
  by_cases hfvb : 4294967296 ≤ fv
  · rw [if_pos hfvb] at h; cases h
  rw [if_neg hfvb] at h
  simp only [List.tail_cons, List.headD_cons] at h
  have hfvH : H fv := by
    have : ¬ (4294967296 : Word).toNat ≤ fv.toNat := fun e => hfvb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 dep d hd hfv
  cases hin : i1F m2 [CWF, b, fv, 0] with
  | none => rw [hin] at h; simp [nbBindK3] at h
  | some pr3 =>
  obtain ⟨rb, m3⟩ := pr3
  rw [hin, nbBindK3_some] at h
  simp only [List.tail_cons, List.headD_cons] at h
  obtain ⟨b2, a3, hrun3, hS3, hg3, hb2H, hb2d⟩ := i1F_ok dn vis fe b fv 0 hb m2 m3 a2 rb hin hS2
  rw [CWF_eq] at hrun3
  have hg13 := (hg1.trans hg2).trans hg3
  -- the codomain walked
  cases hp : nbPosW n m3 vis ctx fu po pl (dep + 1) (kb + 1) (rb.headD 0) ns with
  | none => rw [hp] at h; simp [nbBindK4] at h
  | some pr4 =>
  obtain ⟨rp, m4⟩ := pr4
  rw [hp, nbBindK4_some] at h
  obtain ⟨x, a4, hrun4, hS4, hg4, hk4, hnbH, hnbd, hns4, hP4, hA4⟩ := hPos m3 m4 a3 ctx fu po pl (dep + 1) (kb + 1)
    (rb.headD 0) ns c prog NS rp hp hS3 (hW.grow hg13) (by simpa using hb2H) (hns.grow hg13 htop)
    (((hP.setNo hf1 ⟨∅, hM1⟩).fr (fvinternW_mfr hfv)).fr (MFr.ofI1F hin))
    (i1F_afr hin (fvinternW_afr hfv (noConstWf_afr hno hA)))
  cases hab : abF m4 [CWF, rp.tail.headD 0, dep, 0] with
  | none => rw [hab] at h; simp [nbBindK5] at h
  | some pr5 =>
  obtain ⟨ra, m5⟩ := pr5
  rw [hab, nbBindK5_some] at h
  obtain ⟨nb2, a5, hrun5, ⟨hS5, hg5, hnb2H, hnb2d⟩, hA5⟩ := abF_ok dn vis fe _ dep 0 hnbH m4 m5 a4 ra hab ⟨hS4, hA4⟩
  rw [CWF_eq] at hrun5
  cases hmf : mkForallW m5 d (ra.headD 0) with
  | none => rw [hmf] at h; simp [nbBindK6] at h
  | some pr6 =>
  obtain ⟨z, m6⟩ := pr6
  rw [hmf, nbBindK6_some] at h
  by_cases hzb : 4294967296 ≤ z
  · rw [if_pos hzb] at h; cases h
  rw [if_neg hzb] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨a6, hrun6, hS6, hg6⟩ := mkForall_stage hS5 d (ra.headD 0) hmf
  have hzH : H z := by
    have : ¬ (4294967296 : Word).toNat ≤ z.toNat := fun e => hzb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  have htop4 : iwTop m4 < 2 ^ 64 := Nat.lt_of_le_of_lt hS4.2.1 hS4.2.2.2.1
  refine ⟨(x.1, decI z, x.2.2), a6, ?_, hS6, ((hg13.trans hg4).trans hg5).trans hg6, by simpa using hk4,
    by simpa using hzH, by simp, by simpa using (hns4.grow (hg5.trans hg6) htop4),
    (hP4.fr (MFr.ofAbF hab)).fr (mkForallW_mfr hmf), mkForallW_afr hmf hA5⟩
  rw [pos2_word_succ hd1, pos2_word_succ hk1, hb2d] at hrun4
  rw [hnbd] at hrun5
  have e2 : (internFVarE dep.toNat (decI d)).run a = .ok (decI fv, a2) := by simpa [internFVarE, decE_eq] using hrun2
  have e3 : (instantiate1Fast coreWalkFuel (decI b) (decI fv) 0).run a2 = .ok (b2, a3) := by simpa using hrun3
  have e5 : (abstract1Fast coreWalkFuel x.2.1 dep.toNat 0).run a4 = .ok (nb2, a5) := by simpa using hrun5
  have e6 : (internForallEE (decI d) nb2).run a5 = .ok (decI z, a6) := by
    rw [← hnb2d]; exact hrun6
  simp only [posBindT, StateT.run_bind, hvb, except_ok_bind, hrun1, Bool.false_eq_true, ite_false, e2, e3, hrun4,
    e5, e6]
  rfl

theorem posOK_step (n : Nat) (ih : NbOK dn vis fe n) : PosOK dn vis fe (n + 1) := by
  obtain ⟨-, hBind, hApp, -, -, -, -, -, -, -, -⟩ := ih
  intro m m' a ctx fu po pl dep kb e ns c prog NS r h hS hW he hns hP hA
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbPosW_succ] at h
  by_cases hf0 : fu = 0
  · rw [if_pos hf0] at h; cases h
  rw [if_neg hf0] at h
  have hfu : fu.toNat = (fu - 1).toNat + 1 := by
    have : fu.toNat ≠ 0 := fun e' => hf0 (UInt64.toNat_inj.mp (by simpa using e'))
    rw [pos2_word_pred hf0]; omega
  have hhi := hW.hi htop
  -- the reduct
  cases hwt : stubM "whnf_top" m [vis, dep, e] with
  | none => rw [hwt] at h; simp [nbPosK1] at h
  | some pr =>
  obtain ⟨rw, m1⟩ := pr
  rw [hwt, nbPosK1_some] at h
  obtain ⟨w, a1, hrun1, hS1, hg1, hwH, hwd⟩ := whnf_spec dn vis fe dep e he m m1 a rw hwt hS
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  have hW1 := hW.grow hg1
  obtain ⟨hn1, -, -, -, hnP1, -⟩ := ctx_fields hW1.u.dec hW1.u.inn htop1
  have hne1 := ctx_names_end hW1.u.dec hW1.u.inn hW1.u.sl htop1
  have hhi1 : (nhiW m ctx pl).toNat = c.hiAt prog.length := hhi
  cases hno : noConstWf n m1 (rdW (m1.arr64 IW) ctx) (rdW (m1.arr64 IW) (ctx + 1)) (rdW (m1.arr64 IW) (ctx + 4))
      (nhiW m ctx pl) (rw.headD 0) with
  | none => rw [hno] at h; simp [nbPosK2] at h
  | some pr2 =>
  obtain ⟨o, m2⟩ := pr2
  rw [hno, nbPosK2_some] at h
  have hP1 : PosMR m1 := hP.stub (by decide) hwt
  have hA1 : AbsOK m1 := stub_afr hwt (by decide) hA
  obtain ⟨mp, hmp⟩ := hP1.no
  obtain ⟨bo, hrun2, hbo, hM2, hS2, hg2, hf2⟩ := noConstWf_ok n dn fe vis m1 m2 a1 _ _ _ _ _ o c.names mp hno hS1 hwH hn1
    (by omega) hmp
  rw [hnP1, hhi1, decE_eq, hwd] at hrun2
  have hg12 := hg1.trans hg2
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have hW2 := hW.grow hg12
  have hns2 := hns.grow hg12 htop
  have hP2 : PosMR m2 := hP1.setNo hf2 ⟨∅, hM2⟩
  have hA2 : AbsOK m2 := noConstWf_afr hno hA1
  have hrun1' : (whnf V fe checkFuel dep.toNat (decI e)).run a = .ok (w, a1) := hrun1
  by_cases ho : o = 0
  · -- no occurrence in the reduct: the original, or the reduct
    rw [if_pos ho] at h
    have hbo' : bo = false := by rw [← hbo]; simp [ho]
    subst hbo'
    obtain ⟨hn2, -, -, -, hnP2, -⟩ := ctx_fields hW2.u.dec hW2.u.inn htop2
    have hne2 := ctx_names_end hW2.u.dec hW2.u.inn hW2.u.sl htop2
    cases hno2 : noConstWf n m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4))
        (nhiW m ctx pl) e with
    | none => rw [hno2] at h; simp [nbPosK3] at h
    | some pr3 =>
    obtain ⟨o2, m3⟩ := pr3
    rw [hno2] at h
    obtain ⟨mp2, hmp2⟩ := hP2.no
    obtain ⟨bo2, hrun3, hbo2, hM3, hS3, hg3, hf3⟩ := noConstWf_ok n dn fe vis m2 m3 a1 _ _ _ _ _ o2 c.names mp2 hno2 hS2
      he hn2 (by omega) hmp2
    rw [hnP2, hhi1, decE_eq] at hrun3
    have hns3 := hns2.grow hg3 htop2
    have hP3 : PosMR m3 := hP2.setNo hf3 ⟨∅, hM3⟩
    have hA3 : AbsOK m3 := noConstWf_afr hno2 hA2
    simp only [nbPosK3] at h
    by_cases ho2 : o2 ≠ 0
    · rw [if_pos ho2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hbo2' : bo2 = true := by rw [← hbo2]; simpa using ho2
      subst hbo2'
      refine ⟨(.ordinary, w, NS), a1, ?_, hS3, hg12.trans hg3, by simp [decNFK], by simpa using hwH,
        by simpa using hwd, by simpa using hns3, hP3, hA3⟩
      rw [hfu, nestPos_succ]
      simp only [StateT.run_bind, hrun1', except_ok_bind, hrun2, Bool.not_false, ite_true, hrun3]
      rfl
    · rw [if_neg ho2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hbo2' : bo2 = false := by rw [← hbo2]; simpa using ho2
      subst hbo2'
      refine ⟨(.ordinary, decI e, NS), a1, ?_, hS3, hg12.trans hg3, by simp [decNFK], by simpa using he,
        by simp, by simpa using hns3, hP3, hA3⟩
      rw [hfu, nestPos_succ]
      simp only [StateT.run_bind, hrun1', except_ok_bind, hrun2, Bool.not_false, ite_true, hrun3]
      rfl
  rw [if_neg ho] at h
  have hbo' : bo = true := by rw [← hbo]; simpa using ho
  subst hbo'
  by_cases h6 : rw.headD 0 >>> 28 = 6
  · -- a binder
    rw [if_pos h6] at h
    cases hb : nbBindW n m2 vis ctx (fu - 1) po pl dep kb (rw.headD 0) ns with
    | none => rw [hb] at h; simp [nbPosK4] at h
    | some pr4 =>
    obtain ⟨rb, m4⟩ := pr4
    rw [hb] at h
    simp only [nbPosK4, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨x, a4, hrun4, hS4, hg4, hk4, hxH, hxd, hns4, hP4, hA4⟩ :=
      hBind m2 m4 a1 ctx (fu - 1) po pl dep kb (rw.headD 0) ns c prog NS rb hb hS2 hW2 hwH h6 hns2 hP2 hA2
    refine ⟨x, a4, ?_, hS4, hg12.trans hg4, by simpa using hk4, by simpa using hxH, by simpa using hxd,
      by simpa using hns4, hP4, hA4⟩
    have htag : w.tag = ETag.forallE := by rw [← hwd]; exact (decE_tag_forall _ hwH).mpr h6
    rw [hwd] at hrun4
    rw [hfu, nestPos_succ]
    simp only [StateT.run_bind, hrun1', except_ok_bind, hrun2, Bool.not_true, htag, beq_iff_eq]
    simpa using hrun4
  · -- an application
    rw [if_neg h6] at h
    cases hp : nbAppW n m2 vis ctx (fu - 1) po pl kb (nhiW m ctx pl) (rw.headD 0) ns with
    | none => rw [hp] at h; simp [nbPosK5] at h
    | some pr4 =>
    obtain ⟨rp, m4⟩ := pr4
    rw [hp] at h
    simp only [nbPosK5, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨x, a4, hrun4, hS4, hg4, hk4, hx1, hns4, hP4, hA4⟩ :=
      hApp m2 m4 a1 ctx (fu - 1) po pl kb (nhiW m ctx pl) (rw.headD 0) ns c prog NS rp hp hS2 hW2 hhi1 hwH hns2 hP2 hA2
    refine ⟨x, a4, ?_, hS4, hg12.trans hg4, by simpa using hk4, by simpa using hwH,
      by simpa [hwd] using hx1.symm, by simpa using hns4, hP4, hA4⟩
    have htag : ¬ w.tag = ETag.forallE := by rw [← hwd]; exact fun e' => h6 ((decE_tag_forall _ hwH).mp e')
    rw [hwd, hhi1] at hrun4
    rw [hfu, nestPos_succ]
    simp only [StateT.run_bind, hrun1', except_ok_bind, hrun2, Bool.not_true, htag, beq_iff_eq]
    simpa using hrun4


theorem nbOK_zero : NbOK dn vis fe 0 := by
  simp only [NbOK, PosOK, BindOK, AppOK, ContOK, KeyOK, NewOK, FrameOK, CtorsOK, OneOK, WalkOK, FieldsOK]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [nbPosW, nbBindW, nbAppW, nbContW, nbKeyW, nbNewW, nbFrameW, nbCtorsW, nbOneW, nbWalkW, nbFieldsW]

include hcs in
/-- The block's relational content at every fuel up to the walk fuel. -/
theorem nbOK_all : ∀ n, 2 ^ 31 + n ≤ coreWalkFuel → NbOK dn vis fe n
  | 0, _ => nbOK_zero dn vis fe
  | n + 1, hk => by
    have ih := nbOK_all n (by omega)
    exact ⟨posOK_step dn vis fe n ih, bindOK_step dn vis fe n ih, appOK_step dn vis fe n ih,
      contOK_step dn vis fe hcs n hk ih, keyOK_step dn vis fe n ih, newOK_step dn vis fe n ih,
      frameOK_step dn vis fe hcs n ih, ctorsOK_step dn vis fe n ih, oneOK_step dn vis fe n hk ih,
      walkOK_step dn vis fe n hk ih, fieldsOK_step dn vis fe n hk ih⟩

end steps

end L.Ind
