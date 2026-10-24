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

theorem fieldsOK_step (n : Nat) (ih : NbOK dn vis fe stubCall n) :
    FieldsOK dn vis fe stubCall (n + 1) := by
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
  cases hp : nbPosW stubCall n m vis ctx fu po pl (base + j) 0 d ns with
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

theorem walkOK_step (n : Nat) (ih : NbOK dn vis fe stubCall n) :
    WalkOK dn vis fe stubCall (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hFields⟩ := ih
  intro m m' a ctx root fu po pl hi nF crest ns c prog NS r h hS hW hcr hns hP hA
  rw [nbWalkW_succ] at h
  -- the fields walked, at the input-derived fuel or the given one
  have hF : ∀ (fu' : Word) (m1 : Mem) (a1 : AState), StageR dn vis fe m1 a1 → IWGrow m m1 → PosMR m1 → AbsOK m1 →
      nbWalkK2 n hi (nbFieldsW stubCall n m1 vis ctx fu' po pl hi nF 0 crest ns 0 0 0 0) = some (r, m') →
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
    cases hf : nbFieldsW stubCall n m1 vis ctx fu' po pl hi nF 0 crest ns 0 0 0 0 with
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

theorem ctorsOK_step (n : Nat) (ih : NbOK dn vis fe stubCall n) : CtorsOK dn vis fe stubCall (n + 1) := by
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
  cases ho : nbOneW stubCall n m vis ctx root fu po pl hi us dO dL no nl hO hL (rdW (m.arr64 IW) w)
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

theorem keyOK_step (n : Nat) (ih : NbOK dn vis fe stubCall n) : KeyOK dn vis fe stubCall (n + 1) := by
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
      nbAppK6 (nbNewW stubCall (n' + 1) m2 vis ctx fu po pl kb nn us dO dL nPc cty ns) = some (rr, mm) →
      ∃ x a', (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a2 =
          .ok (x, a') ∧ StageR dn vis fe mm a' ∧ IWGrow m2 mm ∧ decNFK (rr.headD 0) = some x.1 ∧
        NSB mm (rr.tail.headD 0) x.2 ∧ PosMR mm ∧ AbsOK mm := by
    intro rr mm hh
    cases hn : nbNewW stubCall (n' + 1) m2 vis ctx fu po pl kb nn us dO dL nPc cty ns with
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

theorem appOK_step (n : Nat) (ih : NbOK dn vis fe stubCall n) : AppOK dn vis fe stubCall (n + 1) := by
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
  cases hct : nbContW stubCall n m2 vis ctx fu po pl kb ((eViewW m2 (rh.headD 0)).tail.headD 0)
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

theorem bindOK_step (n : Nat) (ih : NbOK dn vis fe stubCall n) : BindOK dn vis fe stubCall (n + 1) := by
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
  cases hp : nbPosW stubCall n m3 vis ctx fu po pl (dep + 1) (kb + 1) (rb.headD 0) ns with
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

theorem nbOK_zero : NbOK dn vis fe stubCall 0 := by
  simp only [NbOK, PosOK, BindOK, AppOK, ContOK, KeyOK, NewOK, FrameOK, CtorsOK, OneOK, WalkOK, FieldsOK]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [nbPosW, nbBindW, nbAppW, nbContW, nbKeyW, nbNewW, nbFrameW, nbCtorsW, nbOneW, nbWalkW, nbFieldsW]

end steps

end L.Ind
