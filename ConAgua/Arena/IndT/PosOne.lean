import ConAgua.Arena.IndT.PosCrest

/-!
# `nest_ctors_one` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`oneOK_step`'s proof (`IndPosSpec/Pos2DecHLSplit`) with the twin side of con-ron's `nestCtors_spec` (its cons
case): the crest typed (`p2ctW_okC`), the fields walked (the block's `WalkOKC` at `n`), the
later-use check (`anyM_pstep`, `structUsedLater_spec`), the result's head (`nestResHead_spec`,
`nestOcc_spec`), the constructor's normal form (`nestCtorNf_spec`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dOut kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The later-use check (`u4F` over the fields) is a pure step. -/
theorem u4_pstep {ks : List NestFieldKind} {closed : EIdx} {closedP : ConLeche.Expr} (xs : List Nat)
    {s₀ s' : AState} {b : Bool} (hok : ConRon.Bridge.StateOK s₀)
    (hcl : denoteE s₀.store closed = some closedP) (h : (xs.anyM (u4F ks closed)) s₀ = .ok (b, s')) :
    PStep s₀ s' :=
  (ConRon.Bridge.Inductives.anyM_pstep
    (g := fun i => if (ks[i]?.map (· == .ordinary)).getD true then false
      else ConLeche.structUsedLater closedP 0 i)
    (fun _ st => denoteE st closed = some closedP) (fun hx h => ConRon.Bridge.denote_ext h hx)
    (fun i s₀ s' b hok hq hrun => by
      unfold u4F at hrun
      by_cases hc : (ks[i]?.map (· == .ordinary)).getD true = true
      · rw [ite_eq_left hc] at hrun
        obtain ⟨rfl, rfl⟩ := ConRon.Bridge.AM.pure_ok hrun
        exact ⟨PStep.refl hok, by simp [hc]⟩
      · rw [ite_eq_right hc] at hrun
        obtain ⟨p, hb⟩ := ConRon.Bridge.Inductives.structUsedLater_spec closed closedP 0 i s₀ s' b hok hq hrun
        exact ⟨p, by simp only [hc]; exact hb⟩)
    xs s₀ s' b hok (fun _ _ => hcl) h).1

/-- The result-head check (`roK`) is a pure step. -/
theorem roK_pstep {c : NestCtx} {hi : Nat} {cur : EIdx} {curP : ConLeche.Expr}
    {namesP : List ConLeche.Name} {a a' : AState} {b : Bool}
    (h : ∀ {β : Type} (K : Bool → AM β), (roK c hi cur K).run a = (K b).run a')
    (hok : ConRon.Bridge.StateOK a) (hcur : denoteE a.store cur = some curP)
    (hn : Frontend.denoteNList a.store.ns c.names = some namesP) : PStep a a' := by
  have h2 : (roK c hi cur (fun x => (pure x : AM Bool))) a = .ok (b, a') := h _
  simp only [roK] at h2
  obtain ⟨rh, s2, h5, h6⟩ := ConRon.Bridge.AM.bind_ok h2
  obtain ⟨p5, -⟩ := ConRon.Bridge.Inductives.nestResHead_spec cur curP a s2 rh hok hcur h5
  cases rh with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind] at h6
    obtain ⟨-, rfl⟩ := ConRon.Bridge.AM.pure_ok h6
    exact p5
  | true =>
    simp only [↓reduceIte, pure_bind] at h6
    obtain ⟨args, s3, h7, h8⟩ := ConRon.Bridge.AM.bind_ok h6
    obtain ⟨rfl, hargs⟩ := ConRon.Bridge.Inductives.getAppArgs_run p5.ok (ConRon.Bridge.denote_ext hcur p5.ext) h7
    obtain ⟨occ, s4, h9, h10⟩ := ConRon.Bridge.AM.bind_ok h8
    obtain ⟨-, rfl⟩ := ConRon.Bridge.AM.pure_ok h10
    obtain ⟨p9, -⟩ := ConRon.Bridge.Inductives.anyM_E_pstep
      (fun st => Frontend.denoteNList st.ns c.names = some namesP)
      (fun hx h => ConRon.Bridge.denoteNListE_ext hx _ _ h)
      (fun e eP s₀ s' b hok' hq hd hrun' =>
        ConRon.Bridge.Inductives.nestOcc_spec c.names namesP c.nP hi e eP s₀ s' b hok' ⟨hq, hd⟩ hrun')
      args _ s3 _ occ p5.ok (ConRon.Bridge.denoteNListE_ext p5.ext _ _ hn) hargs h9
    exact p5.trans p9

section steps
variable {p : Prog} (hq : KnotStageProg p) (hIlpf : IlpfF p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq hIlpf henv in
theorem oneOKC_step (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (ih : NbOKC p dn vis fe env n) :
    OneOKC p dn vis fe env (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hWalk, -⟩ := ih
  intro m m' a ctx root fu po pl hi us dO dL no nl hO hL cv nF ns c prog ds names holes cvv NS r ctxP progP
    usP dsP namesP holesP cvP nsP h hC hW hCc hcv hcv3 hns hP hA hc hctx hprog hpre hcvP hcl hnsP
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbOneW_succ] at h
  -- the crest, typed
  rcases hct : p2ctW (realCall p) n m vis no nl us dO dL hO hL cv hi with _ | ⟨rc, m1⟩ <;> rw [hct] at h; · simp [nbOneK1] at h
  rw [nbOneK1_some] at h
  obtain ⟨cty, a1, crest, a2, ty, a3, so, a4, hnod, hrun1, hrun2, hrun3, hrun4, hC1, hg1, hcrH, hcrd, hP1, hA1, c1,
      crestP, hcrP, hwc⟩ :=
    p2ctW_okC hq hIlpf dn vis fe henv (by omega) hct hC hCc.hus hCc.hnames hCc.hnamesb hCc.hnn
      (hCc.hds.get (OMono.decHL _ _)) hCc.hdsb hCc.hholes hCc.hholesb ((erecP_ext m).decCV hcv) hcv3 hP hA hpre
      hcvP hcl
  have hS1 := hC1.stage
  -- the walk
  rcases hwk : nbWalkW (realCall p) n m1 vis ctx root fu po pl hi nF (rc.headD 0) ns with _ | ⟨rw, m2⟩ <;> rw [hwk] at h; · simp [nbOneK2] at h
  rw [nbOneK2_some] at h
  obtain ⟨ks, nds, cur, ns2, closed, a5, hW5, hC2, hg2, hks, hksb, hksl, hcurH, hcurd, hclH, hcld, hns2, hP2, hA2,
      c2, ndsP, curP, nsP2, hndsP, hcurP, hns2P, hclP, hwnds, hwcur⟩ :=
    hWalk m1 m2 a4 ctx root fu po pl hi nF (rc.headD 0) ns c prog NS rw ctxP progP crestP nsP hwk hC1 (hW.grow hg1)
      hcrH (hns.grow hg1 htop) hP1 hA1 hc (dCtx_ext _ c1.ext _ _ hctx) (dProg_ext c1.ext _ _ hprog)
      (by rw [hcrd]; exact hcrP) (dState_ext c1.ext _ _ hnsP) hwc
  have hS2 := hC2.stage
  -- U4
  have hkl : (rw.tail.headD 0).toNat = nF.toNat := by rw [← hks.length, hksl]
  have hksT : decKL (truncM m2) (rw.headD 0).toNat nF.toNat = some ks := by rw [← hkl]; exact hks
  rcases hu : u4W n m2 (rw.headD 0) nF (rw.tail.tail.tail.headD 0) 0 with _ | ⟨ru, m3⟩ <;> rw [hu] at h; · simp [nbOneK3] at h
  rw [nbOneK3_some] at h
  obtain ⟨bu, a6, hrun6, hS3, hg3, hru, hP3⟩ := u4W_ok dn vis fe (m0 := m2) _ nF _ ks hclH hksT n m2 m3 a5 0 ru
    hu hS2 (IWGrow.refl _) (by simp) hP2
  have hA3 := u4W_afr _ _ _ _ _ _ _ _ hu hA2
  have p6 : PStep a5 a6 := u4_pstep _ hC2.check.state (by rw [hcld]; exact hclP) hrun6
  cases bu with
  | true => rw [ite_eq_left (by rw [hru]; decide)] at h; cases h
  | false =>
  rw [ite_eq_right (by rw [hru]; decide)] at h
  -- the result's head
  have hU3 := (((hW.grow hg1).grow hg2).grow hg3).u
  rcases hro : roW n m3 ctx hi (rw.tail.tail.headD 0) with _ | ⟨rr, m4⟩ <;> rw [hro] at h; · simp [nbOneK4] at h
  rw [nbOneK4_some] at h
  obtain ⟨bo, a7, hrun7, hS4, hg4, hrr, hP4⟩ := roW_ok dn vis fe hro hS3 hU3 hcurH hP3
  have hA4 := roW_afr hro hA3
  have hx16 := c2.ext.trans p6.ext
  obtain ⟨hcn, -, -, -, -, -⟩ := ConRon.Bridge.Inductives.dCtx_fields (dCtx_ext _ (c1.ext.trans hx16) _ _ hctx)
  have p7 : PStep a6 a7 := roK_pstep hrun7 p6.ok
    (by rw [hcurd]; exact ConRon.Bridge.denote_ext hcurP p6.ext) hcn
  cases bo with
  | false => rw [ite_eq_left (by rw [hrr]; rfl)] at h; cases h
  | true =>
  rw [ite_eq_right (by rw [hrr]; decide)] at h
  -- the constructor's record
  have hg14 := ((hg1.trans hg2).trans hg3).trans hg4
  have hW4 := hW.grow hg14
  cases n with
  | zero => simp [ncnWf, nbOneK5] at h
  | succ n' =>
  simp only [ncnWf] at h
  rcases hnf : ncnW n' m4 ctx po pl us dO dL cv (rw.tail.tail.tail.headD 0) with _ | ⟨nf, m5⟩ <;> rw [hnf] at h; · simp [nbOneK5] at h
  simp only [nbOneK5_some, List.headD_cons] at h
  obtain ⟨M, G, g, hR⟩ := hP4.rf
  have htop4 : iwTop m4 < 2 ^ 64 := Nat.lt_of_le_of_lt hS4.2.1 hS4.2.2.2.1
  obtain ⟨x, a8, hrun8, hnfd, hnfb, M', G', hS5, hg5, hR5, -⟩ := ncnW_ok dn fe vis n' m4 m5 a7 ctx po pl us dO dL cv _ nf c prog
    ds cvv M G g hnf hS4 hW4.u.dec hW4.u.inn hW4.hs (by have := hW.hb; simp [NestCtx.hiAt] at this; omega) hCc.hus
    ((hCc.hds.grow (OMono.decHL _ _) hg14).get (OMono.decHL _ _)) (fun j hj => by have := hCc.hdsb; have := hg14.1; omega)
    hclH ((GrowX.of_grow (q := 0) (n := 0) hg14).erecP.decCV hcv) hR
  have hr8 : (ConRon.Arena.nestCtorNf c prog (decI us) ds cvv closed).run a7 = .ok (x, a8) := by
    rw [← hcld]; simpa [decE_eq] using hrun8
  have hC4 : StageC dn vis fe env m4 a7 := hC2.of_pstep hS4 hA4 (p6.trans p7)
  have hx07 := c1.ext.trans (c2.ext.trans (p6.ext.trans p7.ext))
  obtain ⟨p8, hnfP⟩ := ConRon.Bridge.Inductives.nestCtorNf_spec c prog (decI us) ds cvv closed env.find? ctxP progP
    usP dsP cvP _ a7 a8 x hC4.check.state hC4.check.pins
    ⟨dCtx_ext _ hx07 _ _ hctx, dProg_ext hx07 _ _ hprog, ConRon.Bridge.denoteLs_ext hpre.hus hx07,
      ConRon.Bridge.denoteEList_ext hx07 _ _ hpre.hds, ConRon.Bridge.Inductives.dExt_denoteCV hx07 _ _ hcvP,
      ConRon.Bridge.denote_ext hclP (p6.ext.trans p7.ext)⟩ hr8
  have htop5 : iwTop m5 < 2 ^ 64 := Nat.lt_of_le_of_lt hS5.2.1 hS5.2.2.2.1
  have hns5 := hns2.grow ((hg3.trans hg4).trans hg5) (Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1)
  obtain ⟨hp6, hk5, ha5, hn5⟩ := nsb_words hns5 htop5
  -- the record appended to the state's constructor list
  rcases hsn : snocW (n' + 1) m5 (rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 4))
      (rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 5)) nf with _ | ⟨rs, m6⟩; · rw [hsn] at h; simp [nbOneK6] at h
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
  rcases hq' : posRecW m6 [rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0),
      rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 1), rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 2),
      rdW (m5.arr64 IW) (rw.tail.tail.tail.tail.headD 0 + 3), rs.headD 0, rs.tail.headD 0] with _ | ⟨q, m7⟩; · rw [hq'] at h; simp [nbOneK7] at h
  rw [hq', nbOneK7_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS7, hg7, hqq, ht7, hget7⟩ := posRecW_stage hq' hS6 (by simp)
  simp only [List.length_cons, List.length_nil] at ht7
  have hg67 := hg6.trans hg7
  have hNS3 := nsb_rec6 (m' := m7) (q := q) (keys := ns2.keys.toList) (act := ns2.active)
    (nfs := ns2.ctorNfs.toList ++ [x]) (by omega) (Nat.lt_of_le_of_lt hS7.2.1 hS7.2.2.2.1) hget7 (hk5.grow hg67)
    (by have := hns5.b0; have := hg67.1; omega) (ha5.grow hg67) (by have := hns5.b2; have := hg67.1; omega)
    (hnfs6.grow hg7) (by rw [h60, h61]; have := hg7.1; omega)
  have hgall := (hg14.trans hg5).trans hg67
  have hA7 : AbsOK m7 := posRecW_afr hq' (snocW_afr hsn (ncnW_afr hnf hA4))
  have hx58 := p6.ext.trans (p7.ext.trans p8.ext)
  refine ⟨ks, closed, { ns2 with ctorNfs := ns2.ctorNfs.push x }, a8, fun K => ?_, hC4.of_pstep hS7 hA7 p8, hgall,
    ?_, ?_, hclH, hcld, ?_, ((hP4.setRf (ncnW_mfr hnf) ⟨M', G', g, hR5⟩).fr (snocW_mfr hsn)).fr (posRecW_mfr hq'),
    hA7, (c1.trans c2).trans ((p6.trans (p7.trans p8)).toCore hC2.check),
    ⟨(ks.map kindOf, ConLeche.closeTelescope ndsP hi.toNat curP),
      by simp [dOut, ConRon.Bridge.denote_ext hclP hx58],
      ConLeche.Cached.closeTelescope_wscoped ndsP hi.toNat curP hwnds hwcur⟩,
    ⟨_, ConRon.Bridge.Inductives.dState_push (dState_ext hx58 _ _ hns2P) hnfP⟩⟩
  · have hr6 : ((List.range nF.toNat).anyM (u4F ks closed)).run a5 = .ok (false, a6) := by
      rw [List.range_eq_range', ← hcld]; simpa using hrun6
    rw [hcrd] at hW5
    rw [hcurd] at hrun7
    simp only [oneK, hnod, Bool.not_true, Bool.false_eq_true, ite_false, StateT.run_bind, hrun1, except_ok_bind,
      hrun2, hrun3, hrun4]
    simp only [hW5, StateT.run_bind, hr6, except_ok_bind, Bool.false_eq_true, ite_false, hrun7, Bool.not_true, hr8]
  · simp only [List.headD_cons, List.tail_cons]
    exact hks.grow ((((hg3.trans hg4).trans hg5).trans hg6).trans hg7)
  · simp only [List.headD_cons, List.tail_cons]
    have := hg3.1; have := hg4.1; have := hg5.1; have := hg6.1; have := hg7.1; omega
  · simp only [List.headD_cons, List.tail_cons]
    have e : (ns2.ctorNfs.toList ++ [x]).toArray = ns2.ctorNfs.push x := Array.ext' (by simp)
    simpa [e] using hNS3

end steps

end L.Ind
