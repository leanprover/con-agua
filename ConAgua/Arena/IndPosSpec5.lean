import ConAgua.Arena.IndPosSpec4

/-! # `nestCrest` (lane `indproofs2`, helper `pos`)

The banked `replaceFVars` memo across `nest_canon_crest`: its pieces leave the memo alone
(`RfFr`): `nest_phs`, `inst_pis_with` (a stub), `replace_apps` (its own memo, `RAM`). -/


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


/-! ## Memo frames of the pieces (lane `indproofs2`, helper `posmemo`)

`MFr S T` (`IndPos2SpecD`): the writers below leave every per-call memo outside `S` alone; the
banked memo's `RfFr` is a corollary (`RfFr.of_mfr`). -/

theorem RfFr.of_mfr {S : List ArrId} {T : List Word} {m m' : Mem} (h : MFr S T m m') (hS : RFM ∉ S)
    (hT : (208 : Word) ∉ T ∧ (218 : Word) ∉ T ∧ (219 : Word) ∉ T) : RfFr m m' := by
  obtain ⟨A, C, f, a, c⟩ := h
  refine ⟨A, C, f, fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · rcases a _ hm with h | h | h
    · simp [RFM] at h
    · simp [RFM] at h
    · exact hS h
  all_goals rcases c _ hm with h | h | h
  all_goals first | (simp at h; done) | skip
  · exact hT.1 h
  · exact hT.2.1 h
  · exact hT.2.2 h

theorem dpMR_mfr {S0 : List ArrId} {T0 : List Word} {m m' : Mem} (hf : MFr S0 T0 m m') (hS : DPM ∉ S0)
    (hT : (206 : Word) ∉ T0) {mp : Std.HashMap EIdx Nat} (h : dpMR m mp) : dpMR m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := hf.memo DPM 206 (by decide) (by decide) hS hT
  exact memoRG_frame dpSch dpSch_wf bmKey (fun w : Word => w.toNat) A C hA hC m m' f mp h

theorem RfInv.mfr {S : List ArrId} {T : List Word} {m m' : Mem} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word}
    (h : RfInv m M G g) (hf : MFr S T m m') (hS : RFM ∉ S)
    (hT : (208 : Word) ∉ T ∧ (218 : Word) ∉ T ∧ (219 : Word) ∉ T) : RfInv m' M G g :=
  h.frame (RfFr.of_mfr hf hS hT)

theorem allocW_mfr {m m' : Mem} {k q : Word} (h : allocW m k = some (q, m')) : MFr [] [] m m' := by
  simp only [allocW] at h
  split at h; · simp at h
  split at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact MFr.of_iw (allocMem_frame m k)

theorem posRecW_mfr {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m')) :
    MFr [] [] m m' := by
  simp only [posRecW] at h
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  exact (allocW_mfr ‹_›).trans (MFr.of_iw (wrIW_frame _ _ _))

theorem posmemo_copyW_iw : ∀ (n : Nat) (m m' : Mem) (d s l : Word), copyW n m d s l = some m' →
    MemFrame [IW] [200] m m'
  | 0, _, _, _, _, _, h => by simp [copyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [copyW_nil n m d s l hl] at h; cases h; exact MemFrame.refl _ _ _
    · rw [copyW_step n m d s l hl] at h
      exact (set64IW_frame _ _ _).trans (posmemo_copyW_iw n _ _ _ _ _ h)

theorem snocW_mfr {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} (h : snocW n m o l x = some (r, m')) :
    MFr [] [] m m' := by
  unfold snocW at h
  mfr_auto h [allocW_mfr, fun h => MFr.of_iw (posmemo_copyW_iw _ _ _ _ _ _ h)]
  simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.set_iw _ _ _

theorem appendW_mfr {n : Nat} {m m' : Mem} {o1 l1 o2 l2 : Word} {r : List Word}
    (h : appendW n m o1 l1 o2 l2 = some (r, m')) : MFr [] [] m m' := by
  unfold appendW at h
  mfr_auto h [allocW_mfr, fun h => MFr.of_iw (posmemo_copyW_iw _ _ _ _ _ _ h)]

theorem phsGoW_mfr (k : Nat) : ∀ (m m' : Mem) (q n i : Word), phsGoW k m q n i = some m' → MFr [] [] m m' := by
  induction k with
  | zero => intro m m' q n i h; simp [phsGoW] at h
  | succ k ih =>
    intro m m' q n i h
    simp only [phsGoW, phsK1.eq_def, phsK2.eq_def, phsK3.eq_def] at h
    mfr_auto h [fun h => MFr.of_low (sointernW_low h), fun h => MFr.of_low (fvinternW_low h),
      fun h => (MFr.set_iw _ _ _).trans (ih _ _ _ _ _ h)]

theorem phsW_mfr {k : Nat} {m m' : Mem} {nn : Word} {r : List Word} (h : phsW k m nn = some (r, m')) : MFr [] [] m m' := by
  simp only [phsW, phsA.eq_def, phsB.eq_def] at h
  mfr_auto h [allocW_mfr, phsGoW_mfr k _ _ _ _ _]

theorem instW_mfr (n : Nat) : ∀ (m m' : Mem) (ao al e : Word) (r : List Word), instW n m ao al e = some (r, m') →
    MFr [] [] m m' := by
  induction n with
  | zero => intro m m' ao al e r h; simp [instW] at h
  | succ n ih =>
    intro m m' ao al e r h
    simp only [instW, instK1, instK2.eq_def, instK3.eq_def] at h
    mfr_auto h [MFr.ofI1F, ih _ _ _ _ _ _]

theorem rpMkW_mfr {m m' : Mem} {g a2 x2 c2 y x r : Word} (h : rpMkW m g a2 x2 c2 y x = some (r, m')) : MFr [] [] m m' := by
  unfold rpMkW at h
  mfr_auto h [fun h => MFr.of_low (mkAppW_low h), fun h => MFr.of_low (mkLamW_low h),
    fun h => MFr.of_low (mkForallW_low h), fun h => MFr.of_low (mkLetW_low h), fun h => MFr.of_low (mkProjW_low h)]

theorem rpGoW_mfr (n : Nat) :
    (∀ (m m' : Mem) (no nl us b nn f h r : Word), rpGoW n m no nl us b nn f h = some (r, m') → MFr [RAM] [210, 211] m m') ∧
    (∀ (m m' : Mem) (no nl us b nn f1 h g x y z r : Word),
      rpNodeW n m no nl us b nn f1 h g x y z = some (r, m') → MFr [RAM] [210, 211] m m') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ _ h => by simp [rpGoW] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [rpNodeW] at h⟩
  | succ j =>
  have ahF : ∀ {m m' : Mem} {no nl us b nn e : Word} {rr : List Word},
      ahWf j m no nl us b nn e = some (rr, m') → MFr [] [] m m' := by
    intro m m' no nl us b nn e rr h
    cases j with
    | zero => simp [ahWf] at h
    | succ i => exact MFr.of_low (ahW_low h)
  have ndF : ∀ {m m' : Mem} {no nl us b nn f1 h g x y z r : Word},
      rpNodeW j m no nl us b nn f1 h g x y z = some (r, m') → MFr [RAM] [210, 211] m m' := by
    intro m m' no nl us b nn f1 h g x y z r hn
    cases j with
    | zero => simp [rpNodeW] at hn
    | succ i => exact (ih (i + 1) (by omega)).2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn
  refine ⟨fun m m' no nl us b nn f h r hg => ?_, fun m m' no nl us b nn f1 h g x y z r hn => ?_⟩
  · simp only [rpGoW] at hg
    split at hg; · cases hg
    simp only [rpG1] at hg
    split at hg; · cases hg
    split at hg; · rw [← (Prod.mk.inj (Option.some.inj hg)).2]; exact MFr.refl _ _ _
    split at hg
    · rcases ha : ahWf j m no nl us b nn h with _ | ⟨rr, m1⟩ <;> rw [ha] at hg; · cases hg
      rw [rpH_some] at hg; rw [← (Prod.mk.inj (Option.some.inj hg)).2]; exact (ahF ha).up
    simp only [rpG3] at hg
    split at hg; · cases hg
    split at hg; · rw [← (Prod.mk.inj (Option.some.inj hg)).2]; exact MFr.refl _ _ _
    simp only [rpG4.eq_def, rpG5.eq_def] at hg
    split at hg; · cases hg
    rename_i hn; split at hg; · cases hg
    rename_i hs; rw [← (Prod.mk.inj (Option.some.inj hg)).2]
    exact (ndF hn).trans ⟨_, _, msetG_frame raSch raSch_wf _ _ _ _ _ hs, by simp [raSch, RAM], by simp [raSch]⟩
  · simp only [rpNodeW, rpA1.eq_def, rpB1.eq_def, rpB2.eq_def, rpL1.eq_def, rpL2.eq_def, rpL3.eq_def,
      rpP1.eq_def] at hn
    have ihG := (ih j (by omega)).1
    mfr_auto hn [ahF, ihG _ _ _ _ _ _ _ _ _ _, rpMkW_mfr]

theorem rpConstW_mfr {n : Nat} {m m' : Mem} {no nl us b nn e r : Word}
    (h : rpConstW n m no nl us b nn e = some (r, m')) : MFr [RAM] [210, 211] m m' := by
  simp only [rpConstW, rpClrK.eq_def] at h
  split at h; · cases h
  split at h; · cases h
  rename_i hg; split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
  exact (MFr.trans ⟨_, _, mclearG_frame raSch m, by simp, by simp [raSch]⟩
    ((rpGoW_mfr n).1 _ _ _ _ _ _ _ _ _ _ hg)).trans ⟨_, _, mclearG_frame raSch _, by simp, by simp [raSch]⟩

theorem pccW_mfr {k : Nat} {m m' : Mem} {no nl us nn cty : Word} {r : List Word}
    (h : pccW k m no nl us nn cty = some (r, m')) : MFr [RAM] [210, 211] m m' := by
  simp only [pccW, pccA.eq_def, pccB.eq_def, pccC.eq_def] at h
  mfr_auto h [phsW_mfr, instW_mfr _ _ _ _ _ _ _, rpConstW_mfr]


theorem rpConstW_fr {n : Nat} {m m' : Mem} {no nl us b nn e r : Word}
    (h : rpConstW n m no nl us b nn e = some (r, m')) : RfFr m m' :=
  RfFr.of_mfr (rpConstW_mfr h) (by decide) (by decide)

theorem pccW_fr {k : Nat} {m m' : Mem} {no nl us nn cty : Word} {r : List Word}
    (h : pccW k m no nl us nn cty = some (r, m')) : RfFr m m' :=
  RfFr.of_mfr (pccW_mfr h) (by decide) (by decide)

theorem pccW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl us nn cty : Word) (names : List NIdx) (r : List Word)
    (h : pccW k m no nl us nn cty = some (r, m')) (hS : StageR dn vis fe m a) (hcty : H cty) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hnn : nn.toNat + names.length < 2 ^ 64)
    (mp0 : Std.HashMap EIdx EIdx) (hM : rpMR m mp0) :
    ∃ x a', (ConRon.Arena.nestCanonCrest names (decI us) nn.toNat (decI cty)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decOE m' r x ∧ ∃ mp, rpMR m' mp := by
  unfold pccW at h
  rcases hph : phsW k m nn with _ | ⟨r1, m1⟩ <;> rw [hph] at h; · simp [pccA] at h
  rw [pccA_some] at h
  obtain ⟨phs, a1, hrun1, hS1, hg1, hdec1, hbd1⟩ := phsW_ok k dn fe vis m m1 a nn r1 hph hS
  have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
    have : iwTop m1 < 2 ^ 64 := (rdW (m1.arr64 CTL) 200).toNat_lt
    omega
  rcases hin : instW (k + 1) m1 (r1.headD 0) (r1.tail.headD 0) cty with _ | ⟨r2, m2⟩ <;> rw [hin] at h; · simp [pccB] at h
  obtain ⟨x, a2, hrun2, hS2, hg2, hout2⟩ := instW_ok (k + 1) dn fe vis m1 m2 a1 (r1.headD 0) (r1.tail.headD 0)
    cty phs r2 hin hS1 hcty hdec1 hb1 hbd1
  have hM2 : rpMR m2 mp0 :=
    rpMR_mfr ((phsW_mfr hph).trans (instW_mfr _ _ _ _ _ _ _ hin)) (by decide) (by decide) hM
  by_cases hz : r2.headD 0 = 0
  · rw [pccB_zero k no nl us nn r2 m2 hz] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    cases x with
    | none =>
      refine ⟨none, a2, ?_, hS2, hg1.trans hg2, rfl, mp0, hM2⟩
      simp only [ConRon.Arena.nestCanonCrest, StateT.run_bind, hrun1, except_ok_bind, hrun2]
      rfl
    | some t => simp only [decOE] at hout2; rw [hz] at hout2; simp at hout2
  · rw [pccB_ok k no nl us nn r2 m2 hz] at h
    cases x with
    | none => exact absurd hout2 hz
    | some t =>
      simp only [decOE, decW0E] at hout2
      obtain ⟨-, htlt, htd⟩ := hout2
      rcases hrc : rpConstW k m2 no nl us 0 nn (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> rw [hrc] at h; · simp [pccC] at h
      by_cases hb3 : 4294967296 ≤ r3
      · rw [pccC_big _ _ _ hb3] at h; simp at h
      rw [pccC_some _ _ _ hb3] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hg12 := hg1.trans hg2
      have hdec2 : decHL m2 no.toNat nl.toNat = some names := by rw [decHL_grow hg12 hit]; exact hdec
      obtain ⟨a3, hrun3, hM3, hS3, hg3⟩ := rpConstW_ok k dn fe vis m2 m3 a2 no nl us 0 nn (r2.tail.headD 0) r3
        nn.toNat names mp0 hrc hS2 htlt hus hdec2 hno (by have := hg12.1; omega) rfl hnn
        (by simp; omega) hM2
      refine ⟨some (decE r3), a3, ?_, hS3, hg12.trans hg3, ?_, ∅, hM3⟩
      · simp only [ConRon.Arena.nestCanonCrest, StateT.run_bind]
        simp only [hrun1, except_ok_bind, StateT.run_bind, hrun2]
        have h3 : StateT.run (ConRon.Arena.replaceApps names (decI us) 0 nn.toNat (decI (r2.tail.headD 0))) a2 = .ok (decE r3, a3) := hrun3
        rw [← htd, h3]
        rfl
      · simp only [decOE, decW0E]
        exact ⟨rfl, lt_of_notbig hb3, rfl⟩


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

/-! ### The banked walk `replace_fvars` writes only its own memo -/

/-- The banked walk's write set among the memos. -/
abbrev RxFr (m m' : Mem) : Prop := MFr [RFM] [208, 209, 218, 219] m m'

theorem posmemo_rpMk_rx {m m' : Mem} {g a2 x2 c2 y x r : Word} (h : rpMkW m g a2 x2 c2 y x = some (r, m')) :
    RxFr m m' := (rpMkW_mfr h).up

theorem posmemo_rx_mfr (n : Nat) :
    (∀ (m m' : Mem) (f i a b : Word), rxMapW n m f i = some (a, b, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (ctx po pl nn i a b : Word), rxImgW n m ctx po pl nn i = some (a, b, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (ctx po pl n1 i a b : Word), rxFrameW n m ctx po pl n1 i = some (a, b, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (f o l a b : Word), rxDsW n m f o l = some (a, b, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (f o l q j : Word), rxDsGoW n m f o l q j = some m' → RxFr m m') ∧
    (∀ (m m' : Mem) (f e r : Word), rxW n m f e = some (r, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (f fu h r : Word), rxGoW n m f fu h = some (r, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (f f1 g x y z r : Word), rxNodeW n m f f1 g x y z = some (r, m') → RxFr m m') := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [rxMapW, rxImgW, rxFrameW, rxDsW, rxDsGoW, rxW, rxGoW, rxNodeW]
  | succ n ih =>
  obtain ⟨iMap, iImg, iFr, iDs, iDsGo, iRx, iGo, iNode⟩ := ih
  have pfr : ∀ (m m' : Mem) (ctx po pl n1 h a b : Word),
      pfrK1 n ctx po pl n1 (some (h, m)) = some (a, b, m') → RxFr m m' := by
    intro m m' ctx po pl n1 h a b hh
    simp only [pfrK1, pfrK2.eq_def, pfrK3.eq_def, frK4.eq_def, frK5.eq_def] at hh
    mfr_auto hh [posRecW_mfr, iDs _ _ _ _ _ _ _, fun h => MFr.of_low (ceinternW_low h), MFr.ofMknF]
    simp only [Option.some.injEq, Prod.mk.injEq] at hh; obtain ⟨-, -, rfl⟩ := hh; exact MFr.refl _ _ _
  refine ⟨fun m m' f i a b hh => ?_, fun m m' ctx po pl nn i a b hh => ?_,
    fun m m' ctx po pl n1 i a b hh => ?_, fun m m' f o l a b hh => ?_, fun m m' f o l q j hh => ?_,
    fun m m' f e r hh => ?_, fun m m' f fu h r hh => ?_, fun m m' f f1 g x y z r hh => ?_⟩
  · simp only [rxMapW, erK1.eq_def, erK2.eq_def, erK3.eq_def] at hh
    split at hh; · exact iImg _ _ _ _ _ _ _ _ _ hh
    split at hh; · obtain ⟨-, -, rfl⟩ := Prod.mk.inj (Option.some.inj hh); exact MFr.refl _ _ _
    split at hh
    · split at hh; · cases hh
      split at hh; · cases hh
      split at hh; · cases hh
      split at hh; · cases hh
      obtain ⟨-, -, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
      exact (MFr.of_low ((sointernW_low ‹_›).trans (fvinternW_low ‹_›))).up
    split at hh <;> obtain ⟨-, -, rfl⟩ := Prod.mk.inj (Option.some.inj hh) <;> exact MFr.refl _ _ _
  · simp only [rxImgW, rxRootW, rtK1.eq_def, rtK2.eq_def] at hh
    mfr_auto hh [iImg _ _ _ _ _ _ _ _ _, iFr _ _ _ _ _ _ _ _ _, fun h => MFr.of_low (ceinternW_low h), MFr.ofMknF]
    all_goals simp only [Option.some.injEq, Prod.mk.injEq] at hh; obtain ⟨-, -, rfl⟩ := hh; exact MFr.refl _ _ _
  · simp only [rxFrameW, frK0.eq_def] at hh
    split at hh; · exact pfr _ _ _ _ _ _ _ _ _ hh
    split at hh; · cases hh
    rename_i h1; rcases h2 : posRecW _ [_, 0] with _ | ⟨k, m2⟩ <;> rw [h2] at hh; · simp [pfrK1] at hh
    exact ((posRecW_mfr h1).trans (posRecW_mfr h2)).up.trans (pfr _ _ _ _ _ _ _ _ _ hh)
  · simp only [rxDsW, dsA.eq_def, dsB.eq_def] at hh
    mfr_auto hh [allocW_mfr, iDsGo _ _ _ _ _ _ _]
    simp only [Option.some.injEq, Prod.mk.injEq] at hh; obtain ⟨-, -, rfl⟩ := hh; exact MFr.refl _ _ _
  · simp only [rxDsGoW, dgK.eq_def] at hh
    mfr_auto hh [iRx _ _ _ _ _, fun h => (MFr.set_iw _ _ _).up.trans (iDsGo _ _ _ _ _ _ _ h)]
  · simp only [rxW, rxK1.eq_def] at hh
    refine (MFr.trans ⟨_, _, benterG_frame 218 m, by simp, by simp⟩ ?_ : RxFr _ _)
    mfr_auto hh [iGo _ _ _ _ _ _]
    simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2]
    exact ⟨_, _, MemFrame.setCtl _ 219 _, by simp, by simp⟩
  · simp only [rxGoW] at hh
    split at hh; · cases hh
    simp only [rxG1] at hh
    split at hh; · cases hh
    split at hh; · rw [← (Prod.mk.inj (Option.some.inj hh)).2]; exact MFr.refl _ _ _
    split at hh
    · rcases hm : rxMapW n m f _ with _ | ⟨ok, r1, m1⟩ <;> rw [hm] at hh; · cases hh
      rw [rxH_some] at hh; rw [← (Prod.mk.inj (Option.some.inj hh)).2]; exact iMap _ _ _ _ _ _ hm
    simp only [rxG3] at hh
    split at hh; · cases hh
    split at hh; · rw [← (Prod.mk.inj (Option.some.inj hh)).2]; exact MFr.refl _ _ _
    simp only [rxG4.eq_def, rxG5.eq_def] at hh
    split at hh; · cases hh
    rename_i hn; split at hh; · cases hh
    rename_i hs; rw [← (Prod.mk.inj (Option.some.inj hh)).2]
    exact (iNode _ _ _ _ _ _ _ _ _ hn).trans ⟨_, _, msetG_frame rfSch rfSch_wf _ _ _ _ _ hs, by simp [rfSch, RFM], by simp [rfSch]⟩
  · simp only [rxNodeW, rxB1.eq_def, rxB2.eq_def, rxL1.eq_def, rxL2.eq_def, rxL3.eq_def, rxP1.eq_def] at hh
    mfr_auto hh [iGo _ _ _ _ _ _, posmemo_rpMk_rx]

theorem rxW_mfr {n : Nat} {m m' : Mem} {f e r : Word} (h : rxW n m f e = some (r, m')) : RxFr m m' :=
  (posmemo_rx_mfr n).2.2.2.2.2.1 _ _ _ _ _ h

theorem rxDsW_mfr {n : Nat} {m m' : Mem} {f o l a b : Word} (h : rxDsW n m f o l = some (a, b, m')) : RxFr m m' :=
  (posmemo_rx_mfr n).2.2.2.1 _ _ _ _ _ _ _ h

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_crest` refines `nestCrest` -/

def pcrK3 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([1, r], m3)
def pcrK2 (k : Nat) (c : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (f, m2) => pcrK3 (rxW (k + 2) m2 f c)
def pcrK1 (k : Nat) (dO dL hO hL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if r1.headD 0 = 0 then some ([0, 0], m1)
      else pcrK2 k (r1.tail.headD 0) (posRecW m1 [1, dO, dL, hO, hL])
/-- The model of `nest_crest` at exec fuel `k + 3`. -/
def pcrW (k : Nat) (m : Mem) (no nl us dO dL hO hL cty : Word) : Option (List Word × Mem) :=
  pcrK1 k dO dL hO hL (pccW k m no nl us dL cty)

section arms
variable (k : Nat) (m1 m2 m3 : Mem) (dO dL hO hL c f r : Word) (r1 : List Word)
theorem pcrK3_some : pcrK3 (some (r, m3)) = some ([1, r], m3) := rfl
theorem pcrK2_some : pcrK2 k c (some (f, m2)) = pcrK3 (rxW (k + 2) m2 f c) := rfl
theorem pcrK1_zero (h : r1.headD 0 = 0) : pcrK1 k dO dL hO hL (some (r1, m1)) = some ([0, 0], m1) := by
  simp only [pcrK1]; rw [ite_eq_left h]
theorem pcrK1_ok (h : ¬ r1.headD 0 = 0) : pcrK1 k dO dL hO hL (some (r1, m1)) =
    pcrK2 k (r1.tail.headD 0) (posRecW m1 [1, dO, dL, hO, hL]) := by simp only [pcrK1]; rw [ite_eq_right h]
end arms
attribute [ind_grind] pcrK3_some pcrK2_some pcrK1_zero pcrK1_ok

/-- The lookups of `nest_crest`. -/
structure CrLook (p : Prog) : Prop where
  rx : RxLook p
  ng : p.lookup "nest_phs_go" = some nestPhsGo
  np : p.lookup "nest_phs" = some nestPhs
  ip : p.lookup "inst_pis_with" = some instPisWith
  raf : p.lookup "ra_find" = some (memoFindG raSch)
  rap : p.lookup "ra_put" = some (memoPutG raSch)
  rgo : p.lookup "replace_apps_go" = some replaceAppsGo
  rnd : p.lookup "replace_apps_node" = some replaceAppsNode
  rcl : p.lookup "ra_clear" = some (memoClearG raSch)
  ra : p.lookup "replace_apps" = some replaceApps
  cc : p.lookup "nest_canon_crest" = some nestCanonCrest
  cr : p.lookup "nest_crest" = some nestCrest

theorem nestCrest_spec (p : Prog) (L : CrLook p) (k : Nat) (s₀ : St) (no nl us dO dL hO hL cty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 3)) "nest_crest" [no, nl, us, dO, dL, hO, hL, cty]
    ⦃fun r s' => LocEq s' s₀ ∧ pcrW k s₀.mem no nl us dO dL hO hL cty = some (r, s'.mem); ⊤⦄ := by
  have R := L.rx
  simp only [invoke_eq _ L.cr, callFn, nestCrest]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      nestCanonCrest_spec p R.ha R.hl R.hk L.ng L.np L.ip L.raf L.rap L.rgo L.rnd L.rcl L.ra L.cc k,
      posRec5_specW p R.ha R.h5 (k + 2), (rxSpec_all p R (k + 2)).2.2.2.2.2.2.2] <;>
    finish (gen := 20) [pcrW]

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
