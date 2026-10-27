import ConAgua.Arena.IndPosSpec.CfW
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndPosSpec.MapOKStep
import ConAgua.Arena.IndPosSpec.NcnW
import ConAgua.Arena.IndPosSpec.NtyW

/-!
# NestCrest: `ConRon.Arena.nestCanonCrest`, `ConRon.Arena.nestCrest`

The refinement theorems `nestCanonCrest_refines`, `nestCrest_refines` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem RfFr.of_frame {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m') (hA : RFM ∉ A)
    (hC : (208 : Word) ∉ C ∧ (218 : Word) ∉ C ∧ (219 : Word) ∉ C) : RfFr m m' :=
  ⟨A, C, hf, hA, hC.1, hC.2.1, hC.2.2⟩

theorem appendW_mfr {n : Nat} {m m' : Mem} {o1 l1 o2 l2 : Word} {r : List Word}
    (h : appendW n m o1 l1 o2 l2 = some (r, m')) : MFr [] [] m m' := by
  unfold appendW at h
  mfr_auto h [allocW_mfr, fun h => MFr.of_iw (posmemo_copyW_iw _ _ _ _ _ _ h)]

theorem pccW_fr {k : Nat} {m m' : Mem} {no nl us nn cty : Word} {r : List Word}
    (h : pccW k m no nl us nn cty = some (r, m')) : RfFr m m' :=
  RfFr.of_mfr (pccW_mfr h) (by decide) (by decide)

section census3
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (hl : AhLook p) (hk : MkLook p)
  (hng : p.lookup "nest_phs_go" = some nestPhsGo) (hnp : p.lookup "nest_phs" = some nestPhs)
  (hip : p.lookup "inst_pis_with" = some instPisWith)
  (hf : p.lookup "ra_find" = some (memoFindG raSch)) (hput : p.lookup "ra_put" = some (memoPutG raSch))
  (hgo : p.lookup "replace_apps_go" = some replaceAppsGo)
  (hnode : p.lookup "replace_apps_node" = some replaceAppsNode)
  (hcl : p.lookup "ra_clear" = some (memoClearG raSch))
  (hra : p.lookup "replace_apps" = some replaceApps)
  (hp : p.lookup "nest_canon_crest" = some nestCanonCrest)
include ha hl hk hng hnp hip hf hput hgo hnode hcl hra hp

/-- **`nest_canon_crest` refines `nestCanonCrest`**: instantiate the pis with the canonical parameter
variables, then rewrite the applications (result `[1, e]`, or `[0, 0]` for `none`). -/
@[refines ConRon.Arena.nestCanonCrest]
theorem nestCanonCrest_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl us nn cty : Word) (names : List NIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hcty : H cty) (hus : H us) (hdec : decHL s₀.mem no.toNat nl.toNat = some names)
    (hno : no.toNat + nl.toNat < 2 ^ 64) (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem)
    (hnn : nn.toNat + names.length < 2 ^ 64)
    (mp0 : Std.HashMap EIdx EIdx) (hM : rpMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "nest_canon_crest" [no, nl, us, nn, cty]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.nestCanonCrest names (decI us) nn.toNat (decI cty)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestCanonCrest names (decI us) nn.toNat (decI cty)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decOE s'.mem r (AM.res (ConRon.Arena.nestCanonCrest names (decI us) nn.toNat (decI cty)) a₀) ∧
      ∃ mp, rpMR s'.mem mp; ⊤⦄ := by
  refine triple_post (nestCanonCrest_spec p ha hl hk hng hnp hip hf hput hgo hnode hcl hra hp n s₀ no nl us nn cty) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨x, a', hrun, hS', hgr, hout, hM'⟩ := pccW_ok n dn fe vis _ _ a₀ no nl us nn cty names r hm hS hcty hus hdec hno hit
    hnn mp0 hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl', hok, by rw [hst]; exact hS', hgr, by rw [hres]; exact hout, hM'⟩

end census3

theorem rxDsW_mfr {n : Nat} {m m' : Mem} {f o l a b : Word} (h : rxDsW n m f o l = some (a, b, m')) : RxFr m m' :=
  (posmemo_rx_mfr n).2.2.2.1 _ _ _ _ _ _ _ h

end L.Ind

namespace L.Ind

open L.Arena

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem pcrW_ok (k : Nat) (m m' : Mem) (a : AState) (no nl us dO dL hO hL cty : Word) (r : List Word)
    (names : List NIdx) (ds holes : List EIdx) (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word)
    (h : pcrW k m no nl us dO dL hO hL cty = some (r, m')) (hS : StageR dn vis fe m a) (hcty : H cty)
    (hus : H us) (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hnn : dL.toNat + names.length < 2 ^ 64)
    (mp0 : Std.HashMap EIdx EIdx) (hMr : rpMR m mp0)
    (hds : decHL m dO.toNat dL.toNat = some ds) (hdsb : dO.toNat + dL.toNat ≤ iwTop m)
    (hho : decHL m hO.toNat hL.toNat = some holes) (hhob : hO.toNat + hL.toNat ≤ iwTop m)
    (hR : RfInv m M G g) :
    ∃ x a', (ConRon.Arena.nestCrest names (decI us) ds holes (decI cty)).run a = .ok (x, a') ∧
      decOE m' r x ∧ RxPost dn fe vis m m' a' M G g ∧ ∃ mp, rpMR m' mp := by
  unfold pcrW at h
  have hdl := decHL_length m hds
  rcases hpc : pccW k m no nl us dL cty with _ | ⟨r1, m1⟩ <;> rw [hpc] at h; · simp [pcrK1] at h
  obtain ⟨x, a1, hrun1, hS1, hg1, hout1, mp1, hM1⟩ := pccW_ok k dn fe vis m m1 a no nl us dL cty names r1 hpc hS hcty
    hus hdec hno hit hnn mp0 hMr
  have hR1 := hR.frame (pccW_fr hpc)
  cases x with
  | none =>
    have hz : r1.headD 0 = 0 := hout1
    rw [pcrK1_zero (h := hz)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨none, a1, ?_, rfl, hR.post hS1 hg1 (pccW_fr hpc), mp1, hM1⟩
    simp only [ConRon.Arena.nestCrest, StateT.run_bind]
    rw [hdl, hrun1]; rfl
  | some c =>
    obtain ⟨h1, hcH, hcd⟩ := hout1
    rw [pcrK1_ok (h := by rw [h1]; decide)] at h
    rcases hrec : posRecW m1 [1, dO, dL, hO, hL] with _ | ⟨f, m2⟩ <;> rw [hrec] at h; · simp [pcrK2] at h
    rw [pcrK2_some] at h
    obtain ⟨hS2, hg2, hf2, ht2, hget2⟩ := posRecW_stage hrec hS1 (by simp)
    simp only [List.length_cons, List.length_nil] at ht2
    have hg12 := hg1.trans hg2
    have g0 := iwN_of_get (by simpa using hget2 0 (by simp))
    have g1 := iwN_of_get (by simpa using hget2 1 (by simp))
    have g2 := iwN_of_get (by simpa using hget2 2 (by simp))
    have g3 := iwN_of_get (by simpa using hget2 3 (by simp))
    have g4 := iwN_of_get (by simpa using hget2 4 (by simp))
    have hfm : FMOk m2 f.toNat (.keyMap ds holes) :=
      ⟨by simpa using g0, by omega, ⟨dO.toNat, dL.toNat, g1, g2, by rw [decHL_grow hg12 hdsb]; exact hds,
        by have := hg12.1; omega⟩, ⟨hO.toNat, hL.toNat, g3, g4, by rw [decHL_grow hg12 hhob]; exact hho,
        by have := hg12.1; omega⟩⟩
    rcases hrx : rxW (k + 2) m2 f (r1.tail.headD 0) with _ | ⟨rr, m3⟩ <;> rw [hrx] at h; · simp [pcrK3] at h
    rw [pcrK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨a3, hrun3, hH3, hpost3⟩ := (rxOK_all dn fe vis (k + 2)).2.2.2.2.2.2 m2 m3 a1 f _ _ rr M G g hrx hS2 hfm
      hcH (hR1.frame (posRecW_fr hrec))
    refine ⟨some (decE rr), a3, ?_, ⟨rfl, hH3, rfl⟩, RxPost.of_fr hR ((pccW_fr hpc).trans (posRecW_fr hrec)) hg12 hpost3,
      mp1, rpMR_mfr ((posRecW_mfr hrec).up.trans (rxW_mfr hrx)) (by decide) (by decide) hM1⟩
    simp only [ConRon.Arena.nestCrest, StateT.run_bind, hdl, hrun1, except_ok_bind, ← hcd, show (decI (r1.tail.headD 0) : EIdx) = decE (r1.tail.headD 0) from rfl, hrun3]
    rfl

end rel

section census
variable (p : Prog) (L : CrLook p)
include L

/-- **`nest_crest` refines `nestCrest`** (through the stubs below `nest_canon_crest` and `mk_app_n`;
`replace_apps`' memo well formed in the memory at hand, and again after). -/
@[refines ConRon.Arena.nestCrest]
theorem nestCrest_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis no nl us dO dL hO hL cty : Word) (names : List NIdx) (ds holes : List EIdx)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word) (hS : StageR dn vis fe s₀.mem a₀) (hcty : H cty)
    (hus : H us) (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem) (hnn : dL.toNat + names.length < 2 ^ 64)
    (mp0 : Std.HashMap EIdx EIdx) (hMr : rpMR s₀.mem mp0)
    (hds : decHL s₀.mem dO.toNat dL.toNat = some ds) (hdsb : dO.toNat + dL.toNat ≤ iwTop s₀.mem)
    (hho : decHL s₀.mem hO.toNat hL.toNat = some holes) (hhob : hO.toNat + hL.toNat ≤ iwTop s₀.mem)
    (hR : RfInv s₀.mem M G g) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 3)) "nest_crest" [no, nl, us, dO, dL, hO, hL, cty]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestCrest names (decI us) ds holes (decI cty)) a₀ ∧
      decOE s'.mem r (AM.res (ConRon.Arena.nestCrest names (decI us) ds holes (decI cty)) a₀) ∧
      RxPost dn fe vis s₀.mem s'.mem (AM.st (ConRon.Arena.nestCrest names (decI us) ds holes (decI cty)) a₀) M G g ∧
      ∃ mp, rpMR s'.mem mp; ⊤⦄ := by
  refine triple_post (nestCrest_spec p L k s₀ no nl us dO dL hO hL cty) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hout, hpost, hM'⟩ := pcrW_ok dn fe vis k _ _ a₀ no nl us dO dL hO hL cty r names ds holes M G g hm
    hS hcty hus hdec hno hit hnn mp0 hMr hds hdsb hho hhob hR
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hout, by rw [hst]; exact hpost, hM'⟩

end census

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- Across a `has_loose_bvar_b` walk. -/
theorem PosMR.setHb {m m' : Mem} (h : PosMR m) (hf : MFr [HBM] [214, 215] m m')
    (hn : ∃ mp, hbMR m' mp) : PosMR m' := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, -, ⟨M, G, g, hR⟩⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩,
    ⟨c, rpMR_mfr hf (by decide) (by decide) hc⟩, hn, ⟨M, G, g, hR.mfr hf (by decide) (by decide)⟩⟩

/-- Across `has_fvar_fast`. -/
theorem MFr.ofHffF {m m' : Mem} {args r : List Word} (h : hffF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (hffF_frame h)
    (fun b hb => .inl (by simp only [frA, List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb; decide))
    (fun x hx => .inl (by simp only [frC, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide))
/-- Across `loose_bvars_bounded_fast`. -/
theorem MFr.ofLbbF {m m' : Mem} {args r : List Word} (h : lbbF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (lbbF_frame h)
    (fun b hb => .inl (by simp only [walkA, List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb; decide))
    (fun x hx => .inl (by simp only [walkC, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide))
/-- Across `get_app_fn_f` (writes nothing). -/
theorem MFr.ofGafF {m m' : Mem} {args r : List Word} (h : gafF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (gafF_frame h) (by simp) (by simp)
/-- Across `get_app_args_f` (the stack, the pool, their tops). -/
theorem MFr.ofGaaF {m m' : Mem} {args r : List Word} (h : gaaF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (gaaF_frame h)
    (fun b hb => .inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide))
    (fun x hx => .inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide))
/-- Across `strip_pis`/`strip_lams` (their write set, `stripF_frame`). -/
theorem MFr.ofStripF {tg : Word} {m m' : Mem} {args r : List Word} (h : stripF tg m args = some (r, m')) :
    MFr [] [] m m' := MFr.of_iw (stripF_frame h)

theorem mkForallW_mfr {m m' : Mem} {t b r : Word} (h : mkForallW m t b = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low (mkForallW_low h)
theorem ceinternW_mfr {m m' : Mem} {f x r : Word} (h : ceinternW m f x = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low (ceinternW_low h)
/-- Across `abstract1_fast` (its write set, the `abstract1` memo and the store, below 64). -/
theorem MFr.ofAbF {m m' : Mem} {args r : List Word} (h : abF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low ⟨_, _, abF_frame h, lt64A_of_all rfl, lt64_of_all rfl⟩

theorem closeW_mfr : ∀ (n : Nat) (m m' : Mem) (dO dl i body : Word) (r : List Word),
    closeW n m dO dl i body = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, h => by simp [closeW] at h
  | n + 1, m, m', dO, dl, i, body, r, h => by
    unfold closeW closeK1 closeK2 closeK3 at h
    mfr_auto h [closeW_mfr n _ _ _ _ _ _ _, MFr.ofAbF, MFr.ofI1F, mkForallW_mfr]

theorem stripW_mfr {m m' : Mem} {ciq : Word} {r : List Word} (h : stripW m ciq = some (r, m')) : MFr [] [] m m' := by
  unfold stripW stripK at h
  mfr_auto h [MFr.ofStripF]

theorem entryW_mfr {m m' : Mem} {C ciq : Word} {r : List Word} (h : entryW m C ciq = some (r, m')) :
    MFr [] [] m m' := by
  unfold entryW entryK1 entryK2 entryK3 at h
  mfr_auto h [stripW_mfr, MFr.ofStub, MFr.ofI1F, MFr.ofGafF]

theorem ncGoW_mfr : ∀ (k : Nat) (m m' : Mem) (vis C co cl cs ol fp : Word) (r : List Word),
    ncGoW k m vis C co cl cs ol fp = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [ncGoW] at h
  | k + 1, m, m', vis, C, co, cl, cs, ol, fp, r, h => by
    unfold ncGoW ncK1 ncK2 ncK3 at h
    mfr_auto h [ncGoW_mfr k _ _ _ _ _ _ _ _ _ _, envFindW_mfr, entryW_mfr, posRecW_mfr,
      fun h => (MFr.set_iw _ _ _).trans (ncGoW_mfr k _ _ _ _ _ _ _ _ _ _ h)]

theorem ncWf_mfr {k : Nat} {m m' : Mem} {vis C co cl : Word} {r : List Word} (h : ncWf k m vis C co cl = some (r, m')) :
    MFr [] [] m m' := by
  cases k with
  | zero => simp [ncWf] at h
  | succ k =>
  simp only [ncWf] at h
  unfold ncW ncB at h
  mfr_auto h [allocW_mfr, ncGoW_mfr _ _ _ _ _ _ _ _ _ _ _]

theorem ntWf_mfr {k : Nat} {m m' : Mem} {vis C : Word} {r : List Word} (h : ntWf k m vis C = some (r, m')) :
    MFr [] [] m m' := by
  cases k with
  | zero => simp [ntWf] at h
  | succ k =>
  simp only [ntWf] at h
  unfold ntW ntK1 ntK2 at h
  mfr_auto h [envFindW_mfr, ncWf_mfr]

theorem nwsW_mfr {n : Nat} {m m' : Mem} {ctx off l po pl : Word} {r : List Word}
    (h : nwsW n m ctx off l po pl = some (r, m')) : MFr [] [] m m' := by
  unfold nwsW nwsK at h
  mfr_auto h [dcWf_mfr]

theorem gcW_mfr : ∀ (k : Nat) (m m' : Mem) (vis nPc off l oo ol : Word) (r : List Word),
    gcW k m vis nPc off l oo ol = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [gcW] at h
  | k + 1, m, m', vis, nPc, off, l, oo, ol, r, h => by
    unfold gcW gcK1 gcK2 at h
    mfr_auto h [ntWf_mfr, appendW_mfr, gcW_mfr k _ _ _ _ _ _ _ _ _]

theorem rhGoW_mfr : ∀ (k : Nat) (m m' : Mem) (no nl lv po pl nP q j : Word),
    rhGoW k m no nl lv po pl nP q j = some m' → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [rhGoW] at h
  | k + 1, m, m', no, nl, lv, po, pl, nP, q, j, h => by
    unfold rhGoW rhK1 rhK2 at h
    mfr_auto h [posRecW_mfr, fun h => (MFr.set_iw _ _ _).trans (rhGoW_mfr k _ _ _ _ _ _ _ _ _ _ h)]

theorem haW_mfr {k : Nat} {m m' : Mem} {ctx po pl i : Word} {r : List Word}
    (h : haW k m ctx po pl i = some (r, m')) : MFr [] [] m m' := by
  have rh : ∀ {m m' : Mem} {ctx : Word} {r : List Word}, rhWf k m ctx = some (r, m') → MFr [] [] m m' := by
    intro m m' ctx r h
    cases k with
    | zero => simp [rhWf] at h
    | succ k =>
    simp only [rhWf] at h
    unfold rhW rhA rhB at h
    mfr_auto h [allocW_mfr, rhGoW_mfr _ _ _ _ _ _ _ _ _ _ _]
  unfold haW haK1 haK2 at h
  mfr_auto h [rh, appendW_mfr]

theorem naW_mfr {k : Nat} {m m' : Mem} {vis c : Word} {r : List Word} (h : naW k m vis c = some (r, m')) :
    MFr [] [] m m' := by
  unfold naW naK1 naK2 at h
  mfr_auto h [envFindW_mfr, piBW_mfr _ _ _ _ _ _]

theorem resHeadW_mfr {m m' : Mem} {e : Word} {r : List Word} (h : resHeadW m e = some (r, m')) : MFr [] [] m m' := by
  unfold resHeadW resHeadK at h
  mfr_auto h [MFr.ofStub, MFr.ofI1F, MFr.ofGafF]

/-- The `has_loose_bvar_b` walk's write set among the memos. -/
abbrev HbFr (m m' : Mem) : Prop := MFr [HBM] [214, 215] m m'

theorem hbInsW_mfr {m m' : Mem} {e i r x : Word} (h : hbInsW m e i r = some (x, m')) : HbFr m m' := by
  unfold hbInsW at h
  rcases hs : msetG hbSch m e i r with _ | m2 <;> rw [hs] at h; · simp at h
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact ⟨_, _, msetG_frame hbSch hbSch_wf m m2 e i r hs, by simp [hbSch], by simp [hbSch]⟩

theorem hbGoW_mfr : ∀ (n : Nat) (m m' : Mem) (f i h r : Word), hbGoW n m f i h = some (r, m') → HbFr m m'
  | 0, _, _, _, _, _, _, hh => by simp [hbGoW] at hh
  | n + 1, m, m', f, i, h, r, hh => by
    have node : ∀ {m m' : Mem} {f i g x y z r : Word}, hbNodeW n f m i g x y z = some (r, m') → HbFr m m' := by
      intro m m' f i g x y z r h
      unfold hbNodeW hbO1 hbL1 hbL2 at h
      mfr_auto h [hbGoW_mfr n _ _ _ _ _ _]
    unfold hbGoW hbK1 hbK2 hbK3 hbK4 at hh
    mfr_auto hh [bvbW_mfr, node, hbInsW_mfr]

theorem hbFastW_mfr {n : Nat} {m m' : Mem} {i e r : Word} (h : hbFastW n m i e = some (r, m')) : HbFr m m' := by
  unfold hbFastW at h
  split at h
  · simp at h
  exact MFr.trans ⟨_, _, mclearG_frame hbSch m, by simp, by simp [hbSch]⟩ (hbGoW_mfr _ _ _ _ _ _ _ h)

theorem ncnW_mfr {k : Nat} {m m' : Mem} {ctx po pl us dO dL cv closed r : Word}
    (h : ncnW k m ctx po pl us dO dL cv closed = some (r, m')) : RxFr m m' := by
  unfold ncnW ncnK1 ncnK2 ncnK3 at h
  mfr_auto h [posRecW_mfr, rxDsW_mfr, rxW_mfr]

theorem pcrW_mfr {k : Nat} {m m' : Mem} {no nl us dO dL hO hL cty : Word} {r : List Word}
    (h : pcrW k m no nl us dO dL hO hL cty = some (r, m')) : CrFr m m' := by
  unfold pcrW pcrK1 pcrK2 pcrK3 at h
  mfr_auto h [pccW_mfr, posRecW_mfr, rxW_mfr]

/-- Across `nest_crest`. -/
theorem PosMR.setCr {m m' : Mem} (h : PosMR m) (hf : CrFr m m') (hrp : ∃ mp, rpMR m' mp)
    (hrf : ∃ M G g, RfInv m' M G g) : PosMR m' := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, -, ⟨d, hd⟩, -⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩, hrp,
    ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, hrf⟩

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem ustW_mfr {n : Nat} {m m' : Mem} {cty nP j r : Word} (h : ustW n m cty nP j = some (r, m')) : HbFr m m' := by
  unfold ustW ustK1 at h
  mfr_auto h [MFr.ofStripF, hbFastW_mfr]

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem hkW_ok {m : Mem} {ctx kb i r : Word} {c : NestCtx} (h : hkW m ctx kb i = some r)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (htop : iwTop m < 2 ^ 64)
    (hhi : c.hiAt 0 < 2 ^ 64) (hnP : c.nP ≤ i.toNat) :
    decNFK r = some (holeKind c kb.toNat i.toNat) := by
  have hhw := nhiW_toNat (nf := 0) hc hin htop (by simpa using hhi)
  obtain ⟨-, -, -, -, hP, -⟩ := ctx_fields hc hin htop
  simp only [UInt64.toNat_zero] at hhw
  unfold hkW at h
  have ht : (i - rdW (m.arr64 IW) (ctx + 4)).toNat = i.toNat - c.nP := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hP]
  by_cases hlt : i < nhiW m ctx 0
  · rw [ite_eq_left hlt] at h
    have hlt' : i.toNat < c.hiAt 0 := by have := UInt64.lt_iff_toNat_lt.mp hlt; omega
    by_cases hbig : 1152921504606846976 ≤ i - rdW (m.arr64 IW) (ctx + 4)
    · rw [ite_eq_left hbig] at h; cases h
    rw [ite_eq_right hbig] at h
    have hsmall : i.toNat - c.nP < 1152921504606846976 := by
      have : ¬ (1152921504606846976 : Word).toNat ≤ (i - rdW (m.arr64 IW) (ctx + 4)).toNat :=
        fun e => hbig (UInt64.le_iff_toNat_le.mpr e)
      simp at this; omega
    simp only [holeKind, hlt', ite_true]
    by_cases hkb : kb = 0
    · rw [ite_eq_left hkb] at h; cases h; subst hkb
      have e : (1 + 8 * (i - rdW (m.arr64 IW) (ctx + 4))).toNat = 1 + 8 * (i.toNat - c.nP) := by
        rw [UInt64.toNat_add, UInt64.toNat_mul, ht]; simp; omega
      simp only [decNFK, e]
      have h1 : (1 + 8 * (i.toNat - c.nP)) % 8 = 1 := by omega
      have h2 : (1 + 8 * (i.toNat - c.nP)) / 8 = i.toNat - c.nP := by omega
      simp [h1, h2]
    · rw [ite_eq_right hkb] at h; cases h
      have hkb' : (kb.toNat == 0) = false := by
        simp; intro e; exact hkb (UInt64.toNat_inj.mp (by simpa using e))
      have e : (2 + 8 * (i - rdW (m.arr64 IW) (ctx + 4))).toNat = 2 + 8 * (i.toNat - c.nP) := by
        rw [UInt64.toNat_add, UInt64.toNat_mul, ht]; simp; omega
      simp only [decNFK, e, hkb']
      have h1 : (2 + 8 * (i.toNat - c.nP)) % 8 = 2 := by omega
      have h2 : (2 + 8 * (i.toNat - c.nP)) / 8 = i.toNat - c.nP := by omega
      simp [h1, h2]
  · rw [ite_eq_right hlt] at h; cases h
    have : ¬ i.toNat < c.hiAt 0 := fun e => hlt (UInt64.lt_iff_toNat_lt.mpr (by omega))
    simp [holeKind, this, decNFK]

end L.Ind

namespace L.Ind

open L.Arena

theorem nestHoleAt_nP {c : NestCtx} {prog : List NestHole} {i : Nat} {h : NestHole}
    (e : ConRon.Arena.nestHoleAt c prog i = some h) : c.nP ≤ i := by
  unfold ConRon.Arena.nestHoleAt at e; split at e
  · assumption
  · cases e

/-- A hole decoded below the top: its key's name and `ds` length as the words L reads. -/
theorem nh_key_words {m : Mem} {p : Word} {hl : NestHole} (hd : decNH m p.toNat = some hl)
    (hin : NHIn m p.toNat (· < iwTop m)) (htop : iwTop m < 2 ^ 64) :
    H (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) ∧ decI (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) = hl.key.cname ∧
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) p + 3)).toNat = hl.key.ds.length := by
  obtain ⟨k, hk, hK⟩ := decNH_fields hd
  have hkin := hin.2.2 k hk
  have hp0 := hin.1
  have hk0 := hkin.1 0 (by omega)
  have hklt : k < 2 ^ 64 := by omega
  have hk' : (UInt64.ofNat k : Word).toNat = k := UInt64.toNat_ofNat_of_lt' hklt
  have hrd : rdW (m.arr64 IW) p = UInt64.ofNat k := by
    have := rd_iwN (m := m) (p := p) (i := 0) (by simpa using hk) (by simp; omega)
    apply UInt64.toNat_inj.mp; rw [hk']
    simpa using this
  rw [hrd]
  obtain ⟨h0, h1, -, -, h4, -, -⟩ := nk_fields (key := UInt64.ofNat k) (by rw [hk']; exact hK) (by rw [hk']; exact hkin) htop
  exact ⟨h0, h1, by rw [← decHL_length m h4]⟩

theorem pfW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    {k : Nat} {m m' : Mem} {a : AState} {ctx po pl kb hi i aO aL : Word} {c : NestCtx}
    {prog : List NestHole} {args : List EIdx} {r : List Word}
    (h : pfW k m vis ctx po pl kb hi i aO aL = some (r, m')) (hS : StageR dn vis fe m a)
    (hU : UCtx dn vis fe m ctx c) (hpr : HSl m po.toNat pl.toNat prog) (hhi : c.hiAt 0 < 2 ^ 64)
    (hargs : decHL m aO.toNat aL.toNat = some args) (hab : aO.toNat + aL.toNat ≤ iwTop m) (hP : PosMR m) :
    ∃ x a', (∀ {β : Type} (K : NestFieldKind → AM β),
      (pfK fe c prog kb.toNat hi.toNat i.toNat args K).run a = (K x).run a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decNFK (r.headD 0) = some x ∧ PosMR m' := by
  cases k with
  | zero => simp [pfW] at h
  | succ k =>
  simp only [pfW] at h
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  cases k with
  | zero => simp [haWf, p2pfK1] at h
  | succ k =>
  rcases hha : haWf (k + 1) m ctx po pl i with _ | ⟨r1, m1⟩ <;> rw [hha] at h; · simp [p2pfK1] at h
  rw [p2pfK1_eq] at h
  obtain ⟨hS1, hg1, hon⟩ := haW_ok k dn fe vis a m m1 ctx po pl i r1 c prog (by simpa [haWf] using hha) hS hU.dec
    hU.inn hpr
  cases hnh : ConRon.Arena.nestHoleAt c prog i.toNat with
  | none =>
    rw [hnh] at hon; simp only [decONH] at hon
    rw [ite_eq_left hon] at h; cases h
  | some hl =>
  rw [hnh] at hon
  obtain ⟨hon1, hdec, hnin⟩ := hon
  rw [ite_eq_right (by rw [hon1]; decide)] at h
  have hU1 := hU.grow hg1
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨hn1, -, -, -, hnP1, -⟩ := ctx_fields hU1.dec hU1.inn htop1
  have hne1 := ctx_names_end hU1.dec hU1.inn hU1.sl htop1
  rcases hoa : noaW (k + 1) m1 (rdW (m1.arr64 IW) ctx) (rdW (m1.arr64 IW) (ctx + 1)) (rdW (m1.arr64 IW) (ctx + 4))
      hi aO aL with _ | ⟨r2, m2⟩; · rw [hoa] at h; simp [p2pfK2] at h
  rw [hoa, p2pfK2_eq] at h
  obtain ⟨b, hrunoa, hS2, hg2, hr2, hP2⟩ := noaW_ok dn fe vis _ _ _ _ c.names (k + 1) m1 m2 a _ _ args r2 hoa hS1
    hn1 hne1 (by rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hargs)
    (fun j hj => by have := hg1.1; omega) (hP.fr (haW_mfr (by simpa [haWf] using hha)))
  rw [hnP1] at hrunoa
  cases b with
  | true => rw [ite_eq_left (by rw [hr2]; decide)] at h; cases h
  | false =>
  rw [ite_eq_right (by rw [hr2]; decide)] at h
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hd2, hnin2⟩ := hnin.grow hg2
  rw [← hd2] at hdec
  obtain ⟨hcH, hcd, hdl⟩ := nh_key_words hdec hnin2 htop2
  rcases hna : naWf (k + 1) m2 vis (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0))) with _ | ⟨r3, m3⟩ <;> rw [hna] at h; · simp [p2pfK3] at h
  rw [p2pfK3_eq] at h
  obtain ⟨ar, a3, hrun3, hS3, hg3, hr3⟩ := naW_ok dn fe vis _ hcH k m2 m3 a r3 (by simpa [naWf] using hna) hS2
  rw [hcd] at hrun3
  have hal := decHL_length m hargs
  by_cases hov : aL + rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3) < aL
  · rw [ite_eq_left hov] at h; cases h
  rw [ite_eq_right hov] at h
  have hsum : (aL + rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3)).toNat =
      aL.toNat + hl.key.ds.length := by
    rw [← hdl]
    rcases Nat.lt_or_ge (aL.toNat + (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3)).toNat) (2 ^ 64)
      with hl' | hl'
    · exact word_add_toNat hl'
    · exfalso; apply hov; apply UInt64.lt_iff_toNat_lt.mpr; rw [UInt64.toNat_add]
      have := aL.toNat_lt; have := (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3)).toNat_lt; omega
  by_cases hne : aL + rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3) ≠ r3.headD 0
  · rw [ite_eq_left hne] at h; cases h
  rw [ite_eq_right hne] at h
  have heq : args.length + hl.key.ds.length = ar := by
    rw [hal, ← hsum, ← hr3]; simp only [ne_eq, Decidable.not_not] at hne; rw [hne]
  rcases hk : hkWf (k + 1) m3 ctx kb i with _ | w <;> rw [hk] at h; · cases h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hU3 := (hU1.grow hg2).grow hg3
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  have hw := hkW_ok (by simpa [hkWf] using hk) hU3.dec hU3.inn htop3 hhi (nestHoleAt_nP hnh)
  refine ⟨holeKind c kb.toNat i.toNat, a3, fun K => ?_, hS3, (hg1.trans hg2).trans hg3, by simpa using hw,
    hP2.fr (naW_mfr (by simpa [naWf] using hna))⟩
  simp only [pfK, hnh, StateT.run_bind, hrunoa, except_ok_bind, Bool.false_eq_true, ite_false, hrun3, heq,
    beq_self_eq_true, ite_true]

end L.Ind

namespace L.Ind

open L.Arena

theorem decNFK_ordinary {w : Word} {x : NestFieldKind} (h : decNFK w = some x) :
    (x == .ordinary) = (w == 0) := by
  by_cases hw : w = 0
  · subst hw; simp [decNFK] at h; subst h; rfl
  · have hw' : (w == 0) = false := by simpa using hw
    rw [hw']
    simp only [decNFK] at h
    split at h <;> rename_i ht
    · split at h
      · exfalso; apply hw; apply UInt64.toNat_inj.mp; simp; omega
      · cases h
    all_goals first
      | (simp only [Option.some.injEq] at h; subst h; exact beq_eq_false_iff_ne.mpr (by intro e; cases e))
      | (split at h
         · simp only [Option.some.injEq] at h; subst h; exact beq_eq_false_iff_ne.mpr (by intro e; cases e)
         · cases h)
      | (cases h; done)

theorem u4W_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    {m0 : Mem} (ko nF cl : Word) (ks : List NestFieldKind) (hcl : H cl)
    (hks : decKL (truncM m0) ko.toNat nF.toNat = some ks) :
    ∀ (n : Nat) (m m' : Mem) (a : AState) (i : Word) (r : List Word),
    u4W n m ko nF cl i = some (r, m') → StageR dn vis fe m a → IWGrow m0 m → i.toNat ≤ nF.toNat → PosMR m →
    ∃ b a', ((List.range' i.toNat (nF.toNat - i.toNat)).anyM (u4F ks (decI cl))).run a = .ok (b, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) ∧ PosMR m' := by
  intro n
  obtain ⟨hkl, hkw⟩ := decKL_get hks
  induction n with
  | zero => intro m m' a i r h; simp [u4W] at h
  | succ n ih =>
    intro m m' a i r h hS hg0 hi hP
    by_cases hd : nF ≤ i
    · rw [u4W_done (h := hd)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : nF.toNat - i.toNat = 0 := by have := UInt64.le_iff_toNat_le.mp hd; omega
      rw [this]; exact ⟨false, a, rfl, hS, IWGrow.refl _, rfl, hP⟩
    have hlt : i.toNat < nF.toNat := by
      have : ¬ nF.toNat ≤ i.toNat := fun e => hd (UInt64.le_iff_toNat_le.mpr e); omega
    obtain ⟨w, hw, hx⟩ := hkw i.toNat hlt
    obtain ⟨hwi, hw'⟩ := truncM_iw_get hw
    have hrd : rdW (m.arr64 IW) (ko + i) = w := by
      have e : (ko + i).toNat = ko.toNat + i.toNat := word_add_toNat (by
        have := hS.2.1; have := hS.2.2.2.1; have := hg0.1; omega)
      simp only [rdW, e]; simp only [iwA] at hw'; rw [hg0.2.2.1 _ hwi, hw']; rfl
    have hi1 : (i + 1).toNat = i.toNat + 1 := word_add_toNat (by have := nF.toNat_lt; simp; omega)
    have hrange : List.range' i.toNat (nF.toNat - i.toNat) =
        i.toNat :: List.range' (i + 1).toNat (nF.toNat - (i + 1).toNat) := by
      rw [hi1, show nF.toNat - i.toNat = (nF.toNat - (i.toNat + 1)) + 1 by omega, List.range'_succ]
    rw [hrange, List.anyM_cons]
    have hord : ((ks[i.toNat]?.map (· == .ordinary)).getD true) = (w == 0) := by
      rw [List.getElem?_eq_getElem (by omega)] at hx ⊢
      simp only [Option.map_some, Option.getD_some]
      exact decNFK_ordinary hx
    by_cases hk : rdW (m.arr64 IW) (ko + i) ≠ 0
    · rw [u4W_kind (h := hd) (hk := hk)] at h
      have hw0 : (w == 0) = false := by rw [← hrd]; simpa using hk
      cases n with
      | zero => simp [ustWf, u4K] at h
      | succ n =>
      cases n with
      | zero => simp [ustWf, u4K] at h
      | succ n =>
      rcases hu : ustW n m cl 0 i with _ | ⟨su, m1⟩; · simp only [ustWf] at h; rw [hu] at h; simp [u4K] at h
      simp only [ustWf] at h; rw [hu] at h
      obtain ⟨mp, hmp⟩ := hP.hb
      obtain ⟨b1, a1, hrun1, hsu, hM1, hS1, hg1⟩ := ustW_ok n m m1 a cl 0 i su mp
        (by have := nF.toNat_lt; simp; omega) hcl hS hmp hu
      have hP1 := hP.setHb (ustW_mfr hu) hM1
      by_cases hs : su ≠ 0
      · rw [u4K_hit (h := hs)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hb1 : b1 = true := by cases b1 <;> simp_all
        subst hb1
        refine ⟨true, a1, ?_, hS1, hg1, rfl, hP1⟩
        simp only [u4F, hord, hw0, Bool.false_eq_true, ite_false, StateT.run_bind]
        simp only [UInt64.toNat_zero] at hrun1
        rw [hrun1]; rfl
      · rw [u4K_miss (h := hs)] at h
        have hb1 : b1 = false := by cases b1 <;> simp_all
        subst hb1
        obtain ⟨b, a', hrun, hS', hg', hr, hP'⟩ := ih m1 m' a1 (i + 1) r h hS1 (hg0.trans hg1)
          (by rw [hi1]; omega) hP1
        refine ⟨b, a', ?_, hS', hg1.trans hg', hr, hP'⟩
        simp only [u4F, hord, hw0, Bool.false_eq_true, ite_false, StateT.run_bind]
        simp only [UInt64.toNat_zero] at hrun1
        rw [hrun1, except_ok_bind]; simpa using hrun
    · rw [u4W_ord (h := hd) (hk := hk)] at h
      have hw0 : (w == 0) = true := by rw [← hrd]; simpa using hk
      obtain ⟨b, a', hrun, hS', hg', hr, hP'⟩ := ih m m' a (i + 1) r h hS hg0 (by rw [hi1]; omega) hP
      refine ⟨b, a', ?_, hS', hg', hr, hP'⟩
      simp only [u4F, hord, hw0, ite_true, StateT.run_bind]
      simpa using hrun

end L.Ind

namespace L.Ind

open L.Arena

theorem roW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    {k : Nat} {m m' : Mem} {a : AState} {ctx hi cur : Word} {c : NestCtx} {r : List Word}
    (h : roW k m ctx hi cur = some (r, m')) (hS : StageR dn vis fe m a) (hU : UCtx dn vis fe m ctx c)
    (hcur : H cur) (hP : PosMR m) :
    ∃ b a', (∀ {β : Type} (K : Bool → AM β), (roK c hi.toNat (decI cur) K).run a = (K b).run a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) ∧ PosMR m' := by
  cases k with
  | zero => simp [roW] at h
  | succ k =>
  simp only [roW] at h
  rcases hrh : resHeadW m cur with _ | ⟨r1, m1⟩ <;> rw [hrh] at h; · simp [roK0] at h
  rw [roK0_eq] at h
  obtain ⟨a1, hrun1, hS1, hg1⟩ := resHeadW_ok dn fe vis m m1 a cur r1 hcur hrh hS
  by_cases h0 : r1.headD 0 = 0
  · rw [ite_eq_left h0] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨false, a1, fun K => ?_, hS1, hg1, rfl, hP.fr (resHeadW_mfr hrh)⟩
    simp only [roK, StateT.run_bind, hrun1, except_ok_bind, h0, bne_self_eq_false, Bool.false_eq_true, ite_false]
    rfl
  rw [ite_eq_right h0] at h
  have hne : (r1.headD 0 != 0) = true := by simpa using h0
  rcases hga : gaaF m1 [CWF, cur] with _ | ⟨r2, m2⟩ <;> rw [hga] at h; · simp [roK1] at h
  rw [roK1_some] at h
  obtain ⟨args, a2, hrun2, hS2, hg2, hargs⟩ := gaaF_ok dn vis fe CWF cur hcur m1 m2 a1 r2 hga hS1
  rw [CWF_eq] at hrun2
  have hU2 := (hU.grow hg1).grow hg2
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hn2, -, -, -, hnP2, -⟩ := ctx_fields hU2.dec hU2.inn htop2
  have hne2 := ctx_names_end hU2.dec hU2.inn hU2.sl htop2
  obtain ⟨hdA, hbA⟩ := hargs
  have e0 : r2.getD 0 0 = r2.headD 0 := by cases r2 <;> rfl
  have e1 : r2.getD 1 0 = r2.tail.headD 0 := by rcases r2 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  rw [e0, e1] at hdA hbA
  rcases hoa : noaW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi
      (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩; · rw [hoa] at h; simp [roK2] at h
  rw [hoa, roK2_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨b, hrunoa, hS3, hg3, hr3, hP3⟩ := noaW_ok dn fe vis _ _ _ _ c.names k m2 m3 a2 _ _ args r3 hoa hS2
    hn2 hne2 hdA (fun j hj => by omega) ((hP.fr (resHeadW_mfr hrh)).fr (MFr.ofGaaF hga))
  rw [hnP2] at hrunoa
  refine ⟨!b, a2, ?_, hS3, (hg1.trans hg2).trans hg3, ?_, hP3⟩
  · intro β K; simp only [roK, StateT.run_bind, hrun1, except_ok_bind, hne, ite_true, hrun2, hrunoa]; rfl
  · rw [hr3]; cases b <;> rfl

end L.Ind

end

end
