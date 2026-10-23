import ConAgua.Arena.IndInstallSpec26
import ConAgua.Arena.RecCheckSpec5

/-!
# Refinements of `IndInstall`, part 27 (lane `indproofs3`, helper `tail`): `checkBlockTables`

One structure-like member (`ctoW_sim`) and the walk over the three lists (`ctbW_sim`), then the
census theorem.

**Hypotheses beyond the stage relation and the decodings** (each is the caller's):
* `HbMemo s₀.mem`: the `has_loose_bvar_b` memo well formed in the memory at hand (for
  `struct_proj_guards`); returned for the memory after.
-/

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- One structure-like member's install, as the twin runs it. -/
def tabOne (fe : IFEnv) (bs : BlockShape) (msh : MemberShape) (cA : IConstantVal) (nF : Nat)
    (sorts : List LIdx) : AM IFEnv := do
  let guards ← structProjGuards cA.type bs.nP nF sorts
  checkStructProjTable msh.cvT.name cA.name bs.lps bs.nP nF bs.resSort guards 1 cA fe

theorem cbt_one (bs : BlockShape) (msh : MemberShape) (ms : List MemberShape)
    (css : List (List (IConstantVal × Nat))) (sss : List (List (List LIdx))) (fe : IFEnv)
    (cA : IConstantVal) (nF : Nat) (sorts : List LIdx) (h : msh.nIdx = 0) :
    ConRon.Arena.checkBlockTables bs (msh :: ms) ([(cA, nF)] :: css) ([sorts] :: sss) fe =
      tabOne fe bs msh cA nF sorts >>= fun fe₂ => ConRon.Arena.checkBlockTables bs ms css sss fe₂ := by
  simp [ConRon.Arena.checkBlockTables, h, tabOne, bind_assoc]

theorem cbt_skip (bs : BlockShape) (msh : MemberShape) (ms : List MemberShape)
    (cs : List (IConstantVal × Nat)) (css : List (List (IConstantVal × Nat))) (ss : List (List LIdx))
    (sss : List (List (List LIdx))) (fe : IFEnv) (h : ¬ (cs.length = 1 ∧ ss.length = 1 ∧ msh.nIdx = 0)) :
    ConRon.Arena.checkBlockTables bs (msh :: ms) (cs :: css) (ss :: sss) fe = ConRon.Arena.checkBlockTables bs ms css sss fe := by
  rcases cs with _ | ⟨⟨cA, nF⟩, _ | ⟨c2, cs⟩⟩ <;> rcases ss with _ | ⟨s1, _ | ⟨s2, ss⟩⟩ <;>
    simp_all [ConRon.Arena.checkBlockTables]

theorem cbt_nil (bs : BlockShape) (ms : List MemberShape) (css : List (List (IConstantVal × Nat)))
    (sss : List (List (List LIdx))) (fe : IFEnv) (h : ms = [] ∨ css = [] ∨ sss = []) :
    ConRon.Arena.checkBlockTables bs ms css sss fe = pure fe := by
  rcases ms with _ | ⟨m, ms⟩ <;> rcases css with _ | ⟨c, css⟩ <;> rcases sss with _ | ⟨s, sss⟩ <;>
    simp_all [ConRon.Arena.checkBlockTables]

/-- `struct_proj_guards` at fuel `1` does not return. -/
theorem spgW_zero (m : Mem) (cty nP nF so sl : Word) : spgW 0 m cty nP nF so sl = none := by
  simp only [spgW, spgK1]
  split
  · rfl
  · split
    · rfl
    · simp [ulW, spgK2]

theorem nPnF_bound {x y : Word} (h : ¬ x + y + 1 ≤ x) : x.toNat + y.toNat + 1 < 2 ^ 64 := by
  have h' : x.toNat < (x + y + 1).toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h)
  rw [UInt64.toNat_add, UInt64.toNat_add] at h'
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  simp only [UInt64.toNat_one] at h'
  omega

/-- **`check_block_tables_one`'s model refines one member's install.** -/
theorem ctoW_sim {p : Prog} (hP : TabsProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState} {pp ms co so : Word} {bs : BlockShape} {msh : MemberShape}
    {cA : IConstantVal} {nF : Nat} {sorts : List LIdx}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hms : DecB (fun m => decMS m ms.toNat) m msh) (hcs : PSlR decCN [(cA, nF)] co 1 m)
    (hss : PSlR decIS [sorts] so 1 m) (hM : HbMemo m) :
    Sim (ctoW p n m pp ms co so vis) (tabOne fe bs msh cA nF sorts) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m') := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  -- the constructor `[cv, nF]`
  obtain ⟨pc, y, ys, hy, hw0, hpcb, hdc, -⟩ := partsPSl_cons hcs (by decide)
  simp only [List.cons.injEq] at hy
  obtain ⟨rfl, -⟩ := hy
  obtain ⟨⟨cvp, hcvp, hcv⟩, hnF⟩ := decCN_some (show decCN (truncM m) pc = some (cA, nF) from hdc)
  have hpc' : (UInt64.ofNat pc : Word).toNat = pc := UInt64.toNat_ofNat_of_lt' hpcb
  have hlt1 := partsIwLt hnF
  obtain ⟨hw1, hcvb, -⟩ := partsIwRd hcvp hpc'
  obtain ⟨hw2, hnFb, -⟩ := partsIwRd hnF (w := UInt64.ofNat pc + 1)
    (by rw [UInt64.toNat_add, hpc']; simp; omega)
  -- the sorts `[off, len]`
  obtain ⟨ps, z, zs, hz, hw3, hpsb, hds, -⟩ := partsPSl_cons hss (by decide)
  simp only [List.cons.injEq] at hz
  obtain ⟨rfl, -⟩ := hz
  have hps' : (UInt64.ofNat ps : Word).toNat = ps := UInt64.toNat_ofNat_of_lt' hpsb
  obtain ⟨so', sl', hso, hsl, hdd⟩ := decAt_some (show decIS (truncM m) ps = some sorts from hds)
  have hlt2 := partsIwLt hsl
  obtain ⟨hw4, hsob, -⟩ := partsIwRd hso hps'
  obtain ⟨hw5, hslb, -⟩ := partsIwRd hsl (w := UInt64.ofNat ps + 1)
    (by rw [UInt64.toNat_add, hps']; simp; omega)
  have hso' : (UInt64.ofNat so' : Word).toNat = so' := UInt64.toNat_ofNat_of_lt' hsob
  have hsl' : (UInt64.ofNat sl' : Word).toNat = sl' := UInt64.toNat_ofNat_of_lt' hslb
  have hsorts : decHL m so' sl' = some sorts ∧ (sl' = 0 ∨ so' + sl' ≤ iwTop m) := by
    by_cases h0 : sl' = 0
    · subst h0
      have : sorts = [] := by simpa [decHL, hslice?] using hdd.symm
      subst this; exact ⟨by simp [decHL, hslice?], .inl rfl⟩
    · have hb := decHL_truncM_bound hdd h0
      exact ⟨by rw [← decHL_truncM hb]; exact hdd, .inr hb⟩
  -- the shape's words
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨hnpw, hnpb, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  -- the member's name
  have hmsT : decMS (truncM m) ms.toNat = some msh := hms
  obtain ⟨⟨cvm, hcvm, hcvT⟩, -, -⟩ := decMS_some hmsT
  obtain ⟨hw6, hcvmb, -⟩ := partsIwRd hcvm rfl
  -- the fuel
  match n with
  | 0 =>
    intro r m' e
    simp only [ctoW, callW_zero] at e
    split at e <;> simp [ctoK1] at e
  | 1 =>
    intro r m' e
    have hz0 : ∀ a1 a2 a3 a4 a5 : Word, callW p 1 "struct_proj_guards" [a1, a2, a3, a4, a5] m = none := by
      intro a1 a2 a3 a4 a5
      cases h : callW p 1 "struct_proj_guards" [a1, a2, a3, a4, a5] m with
      | none => rfl
      | some y =>
        obtain ⟨s', -, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
          (spg_spec p hP.tbl.hv hP.hf hP.hput hP.hins hP.hgo hP.hbp hP.hst hP.hsg hP.tbl.ha hP.tbl.hc hP.tbl.hsc
            hP.hul hP.hgd hP.hmf hP.hmp hP.him hP.hcol hP.hrow hP.hpw hP.hcl hP.hspg 0 _ a1 a2 a3 a4 a5) h
        rw [spgW_zero] at hW; cases hW
    simp only [ctoW, hz0] at e
    split at e <;> simp [ctoK1] at e
  | j + 2 =>
  unfold ctoW
  rw [hw0, hw1, hw2, hw3, hw4, hw5, hnpw]
  by_cases hg : UInt64.ofNat bs.nP + UInt64.ofNat nF + 1 ≤ (UInt64.ofNat bs.nP : Word)
  · rw [if_pos hg]; exact Sim.of_none
  rw [if_neg hg]
  have hb := nPnF_bound hg
  rw [UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb] at hb
  obtain ⟨w, hwT, hwl, hwd⟩ := sumTypeWord (q := UInt64.ofNat cvp)
    (by rw [UInt64.toNat_ofNat_of_lt' hcvb]; exact DecB.get (OMono.decCVp _) hcv) hS.2.2.2.2.1
  rw [hwT]
  unfold tabOne
  -- `struct_proj_guards`
  refine Sim.bindK (K := ctoK1 p (j + 2) pp ms (UInt64.ofNat cvp) (UInt64.ofNat nF) vis) rfl (fun _ _ => rfl)
    (by
      have h := tabSimSpg hP (j + 1) w (UInt64.ofNat bs.nP) (UInt64.ofNat nF) (UInt64.ofNat so')
        (UInt64.ofNat sl') sorts hwl
        (by rw [UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb]; exact hb) hS hM
        (by rw [hso', hsl']; exact hsorts.1)
        (by rcases hsorts.2 with h | h
            · left; rw [h]; rfl
            · right; rw [hso', hsl']; exact h)
      rw [hwd, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb] at h
      exact h) ?_
  rintro rg guards m1 a1 ⟨hS1, hg1, hgd1, hgt1, hM1⟩
  rw [ctoK1_some]
  -- `block_shape_lps` (model only)
  refine Sim.mstep (K := ctoK2 p (j + 2) pp ms (UInt64.ofNat cvp) (UInt64.ofNat nF) vis rg) rfl
    (fun _ _ => rfl) fun rl m2 h2 => ?_
  obtain ⟨s2, rfl, -, hW2, -⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (blockShapeLps_spec2 p hP.tbl.ha hP.erCopy hP.erToIw hP.lps (j + 2) _ pp) h2
  obtain ⟨hS2, hg2, hl2, hlb2⟩ := lpsW_ok' hW2 hS1 (hq.grow (decBS_mono _) hg1)
  have hM2 : HbMemo s2.mem := hM1.fr (lpsW_mfrT hW2)
  have hg12 := hg1.trans hg2
  -- `check_struct_proj_table`
  rw [ctoK2_some]
  obtain ⟨hnpw2, -, hrs2, hrse2⟩ := partsShapeWords hg12 hq hq9
  have hms2 : rdW (s2.mem.arr64 IW) ms = UInt64.ofNat cvm := by
    rw [partsRdIW_grow hg12 (by have := partsIwLt hcvm; omega)]; exact hw6
  obtain ⟨hT32, hTn⟩ := partsCVName hg12 hcvT hcvmb
  obtain ⟨hC32, hCn⟩ := partsCVName hg12 hcv hcvb
  rw [hnpw2, hms2]
  refine Sim.post (K := ctoK3) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow s2.mem m' ∧ MFr [] [] s2.mem m')
    (fun r m' e => by
      obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
        (tblW_spec p hP.tbl j _ (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvm))
          (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvp)) (rl.headD 0) (rl.tail.headD 0) (UInt64.ofNat bs.nP)
          (UInt64.ofNat nF) (rdW (s2.mem.arr64 IW) (pp + 6)) (rg.headD 0) (rg.tail.headD 0) 1
          (UInt64.ofNat cvp) vis) e
      have h := tblW_okM (dn := dn) (vis := vis) (fe := fe) p hP.tbl j s2.mem a1
        (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvm)) (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvp))
        (rl.headD 0) (rl.tail.headD 0) (UInt64.ofNat bs.nP) (UInt64.ofNat nF) (rdW (s2.mem.arr64 IW) (pp + 6))
        (rg.headD 0) (rg.tail.headD 0) 1
        (UInt64.ofNat cvp) bs.lps guards cA hS2 hT32 hC32 hrs2
        (by rw [UInt64.toNat_ofNat_of_lt' hnpb]; omega) hl2 hlb2
        (by rw [decHL_grow hg2 (Nat.le_of_eq hgt1)]; exact hgd1) (by rw [hgt1]; exact hg2.1)
        (by rw [UInt64.toNat_ofNat_of_lt' hcvb]; exact DecB.grow (OMono.decCVp _) hg12 hcv)
      rw [hTn, hCn, hrse2, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb] at h
      exact h r s3.mem hW3)
    fun r x m3 a3 h => ⟨h.1, hg12.trans h.2.1, hM2.fr h.2.2⟩

/-- **`check_block_tables`' model refines `checkBlockTables`.** -/
theorem ctbW_sim {p : Prog} (hP : TabsProg p) (dn : NIdx → Option ConLeche.Name) (pp : Word) (bs : BlockShape)
    (n : Nat) :
    ∀ (m : Mem) (a : AState) (vis : Word) (fe : IFEnv) (mo ml co cl so sl : Word) (mss : List MemberShape)
      (css : List (List (IConstantVal × Nat))) (sss : List (List (List LIdx))),
    StageR dn vis fe m a → DecB (fun m => decBS m pp.toNat) m bs →
    ShapeSrc m pp → PSlR decMS mss mo ml m → PSlR decCNS css co cl m → PSlR decISS sss so sl m → HbMemo m →
    Sim (ctbW p n m pp mo ml co cl so sl vis) (ConRon.Arena.checkBlockTables bs mss css sss fe) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m') := by
  induction n with
  | zero => intros; rw [ctbW_zero]; exact Sim.of_none
  | succ n ih =>
  intro m a vis fe mo ml co cl so sl mss css sss hS hq hsrc hmss hcss hsss hM
  by_cases hml : ml = 0
  · subst hml
    rw [ctbW_nil1 p n m pp mo 0 co cl so sl vis rfl, cbt_nil bs mss css sss fe (.inl (partsPSl_nil hmss))]
    exact Sim.ret ⟨hS, IWGrow.refl m, hM⟩
  by_cases hcl : cl = 0
  · subst hcl
    rw [ctbW_nil2 p n m pp mo ml co 0 so sl vis hml rfl,
      cbt_nil bs mss css sss fe (.inr (.inl (partsPSl_nil hcss)))]
    exact Sim.ret ⟨hS, IWGrow.refl m, hM⟩
  by_cases hsl : sl = 0
  · subst hsl
    rw [ctbW_nil3 p n m pp mo ml co cl so 0 vis hml hcl rfl,
      cbt_nil bs mss css sss fe (.inr (.inr (partsPSl_nil hsss)))]
    exact Sim.ret ⟨hS, IWGrow.refl m, hM⟩
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨msp, msh, rest, rfl, hwm, hmsb, hdm, hrest⟩ := partsPSl_cons hmss hml
  obtain ⟨csp, cs, css', rfl, hwc, hcsb, hdc, hcss'⟩ := partsPSl_cons hcss hcl
  obtain ⟨ssp, ss, sss', rfl, hws, hssb, hds, hsss'⟩ := partsPSl_cons hsss hsl
  have hmsp' : (UInt64.ofNat msp : Word).toNat = msp := UInt64.toNat_ofNat_of_lt' hmsb
  have hcsp' : (UInt64.ofNat csp : Word).toNat = csp := UInt64.toNat_ofNat_of_lt' hcsb
  have hssp' : (UInt64.ofNat ssp : Word).toNat = ssp := UInt64.toNat_ofNat_of_lt' hssb
  -- the member's constructors `[off, len]`
  obtain ⟨o1, l1, ho1, hl1, hd1, hb1⟩ := partsAt decCN_mono
    (show decAt (truncM m) (decPL (truncM m) (decCN (truncM m))) csp = some cs from hdc)
  have hlt1 := partsIwLt hl1
  obtain ⟨hwo1, -, -⟩ := partsIwRd ho1 hcsp'
  obtain ⟨hwl1, -, -⟩ := partsIwRd hl1 (w := UInt64.ofNat csp + 1)
    (by rw [UInt64.toNat_add, hcsp']; simp; omega)
  rw [ofNat_toNat_word] at hwo1 hwl1
  have hlen1 : cs.length = l1.toNat := decPL_length _ hd1
  -- the member's sorts `[off, len]`
  obtain ⟨o2, l2, ho2, hl2, hd2, hb2⟩ := partsAt decIS_mono
    (show decAt (truncM m) (fun o l => decPL (truncM m) (decIS (truncM m)) o l) ssp = some ss from hds)
  have hlt2 := partsIwLt hl2
  obtain ⟨hwo2, -, -⟩ := partsIwRd ho2 hssp'
  obtain ⟨hwl2, -, -⟩ := partsIwRd hl2 (w := UInt64.ofNat ssp + 1)
    (by rw [UInt64.toNat_add, hssp']; simp; omega)
  rw [ofNat_toNat_word] at hwo2 hwl2
  have hlen2 : ss.length = l2.toNat := decPL_length _ hd2
  -- the member's index count
  obtain ⟨-, hni, -⟩ := decMS_some (show decMS (truncM m) msp = some msh from hdm)
  have hlt3 := partsIwLt hni
  obtain ⟨hwn, hnib, -⟩ := partsIwRd hni (w := UInt64.ofNat msp + 1)
    (by rw [UInt64.toNat_add, hmsp']; simp; omega)
  have hni0 : (UInt64.ofNat msh.nIdx : Word) = 0 ↔ msh.nIdx = 0 := by
    constructor
    · intro e; have := congrArg UInt64.toNat e; rwa [UInt64.toNat_ofNat_of_lt' hnib] at this
    · intro e; rw [e]; rfl
  have hw1 : ∀ w : Word, w = 1 ↔ w.toNat = 1 := fun w =>
    ⟨fun e => by rw [e]; rfl, fun e => UInt64.toNat_inj.mp (by rw [e]; rfl)⟩
  by_cases hc : l1 = 1 ∧ l2 = 1 ∧ msh.nIdx = 0
  · obtain ⟨e1, e2, e3⟩ := hc
    subst e1 e2
    obtain ⟨⟨cA, nF⟩, rfl⟩ := List.length_eq_one_iff.mp (show cs.length = 1 by rw [hlen1]; rfl)
    obtain ⟨sorts, rfl⟩ := List.length_eq_one_iff.mp (show ss.length = 1 by rw [hlen2]; rfl)
    rw [ctbW_one p n m pp mo ml co cl so sl vis hml hcl hsl (by rw [hwc, hwl1]) (by rw [hws, hwl2])
      (by rw [hwm, hwn, (hni0).mpr e3]), cbt_one bs msh rest css' sss' fe cA nF sorts e3, hwm, hwc, hws, hwo1, hwo2]
    have hcall : Sim (callW p n "check_block_tables_one" [pp, UInt64.ofNat msp, o1, o2, vis] m)
        (tabOne fe bs msh cA nF sorts) a
        (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m') := by
      cases n with
      | zero => rw [callW_zero]; exact Sim.of_none
      | succ k =>
        intro r m' e
        obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
          (cto_spec p hP.one k _ pp (UInt64.ofNat msp) o1 o2 vis) e
        exact ctoW_sim hP k hS hq hsrc (by rw [hmsp']; exact hdm)
          ⟨hd1, hb1.resolve_left (by decide)⟩ ⟨hd2, hb2.resolve_left (by decide)⟩ hM r s'.mem hW
    refine Sim.bindK (K := ctbK1 p n pp mo ml co cl so sl) (by simp [ctbK1.eq_def])
      (fun r m1 => ctbK1_some p n m1 pp mo ml co cl so sl r) hcall ?_
    rintro r fe₂ m1 a1 ⟨hS1, hg1, hM1⟩
    exact Sim.post (K := ctbK2) rfl (fun _ _ => rfl)
      (ih m1 a1 (r.headD 0) fe₂ (mo + 1) (ml - 1) (co + 1) (cl - 1) (so + 1) (sl - 1) rest css' sss'
        hS1 (hq.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc) (hrest.grow decMS_mono hg1)
        (hcss'.grow decCNS_mono hg1) (hsss'.grow decISS_mono hg1) hM1)
      (fun r x m a ⟨h1, h2, h3⟩ => ⟨h1, hg1.trans h2, h3⟩)
  · rw [ctbW_skip p n m pp mo ml co cl so sl vis hml hcl hsl (by
        rw [hwc, hwl1, hws, hwl2, hwm, hwn, hni0]; exact hc),
      cbt_skip bs msh rest cs css' ss sss' fe (by
        rw [hlen1, hlen2, ← hw1, ← hw1]; exact hc)]
    exact Sim.post (K := ctbK2) rfl (fun _ _ => rfl)
      (ih m a vis fe (mo + 1) (ml - 1) (co + 1) (cl - 1) (so + 1) (sl - 1) rest css' sss'
        hS hq hsrc hrest hcss' hsss' hM)
      (fun r x m a ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩)

/-- **`check_block_tables` refines `checkBlockTables`**: from the stage relation at `vis` of `fe`,
the shape record, the members, the stored constructors and their fields' sorts (per member, as
`check_block_ctors` returns them) decoded below the tops, and the walk memos well formed, a
returning run returns the view of the environment with every structure-like member's projection
table pushed; the memos stay well formed. -/
@[refines ConRon.Arena.checkBlockTables]
theorem checkBlockTables_refines (p : Prog) (hP : TabsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (pp mo ml co cl so sl : Word)
    (bs : BlockShape) (mss : List MemberShape) (css : List (List (IConstantVal × Nat)))
    (sss : List (List (List LIdx))) (hS : StageR dn vis fe s₀.mem a₀)
    (hq : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hsrc : ShapeSrc s₀.mem pp)
    (hmss : PSlR decMS mss mo ml s₀.mem) (hcss : PSlR decCNS css co cl s₀.mem)
    (hsss : PSlR decISS sss so sl s₀.mem) (hM : HbMemo s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_tables" [pp, mo, ml, co, cl, so, sl, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockTables bs mss css sss fe) a₀ ∧
      StageR dn (r.headD 0) (AM.res (ConRon.Arena.checkBlockTables bs mss css sss fe) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlockTables bs mss css sss fe) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ HbMemo s'.mem; ⊤⦄ :=
  triple_post (ctb_spec p hP.tabs n s₀ pp mo ml co cl so sl vis) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (ctbW_sim hP dn pp bs n s₀.mem a₀ vis fe mo ml co cl so sl mss css sss hS hq
      hsrc hmss hcss hsss hM) hm
    ⟨hl, hok, hQ⟩

end L.Ind
