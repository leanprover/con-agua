module

public import ConAgua.Arena.QuotRecT
public import ConAgua.Arena.QuotFns
public import ConAgua.Arena.IndPartsSpec.PlW
public import ConAgua.Arena.IndSumSpec.Row
public import ConAgua.Arena.TwinStep
public import ConRon.Bridge.Checker.Basis
public import ConAgua.Arena.DeclCanonEq
public import ConAgua.Arena.DeclCanonSpec
public import ConAgua.Rom.CIReadSpec
import ConAgua.Arena.IlpRd
import ConAgua.Arena.DeclAndPinIndRef
import ConAgua.Arena.IndexLoops
import all ConAgua.Arena.BasisL
import ConAgua.L.WordOff
import ConAgua.Arena.RecCheckSpec.ErToIwWStage
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# A pin at a stream's names: `cv_at_lps`, `ci_at_lps`, `quot_pin_hit`, `quot_at` (lane `ronsync2`, stage 3)

`cv_at_lps(d, c + 1, po, pl)` writes `IConstantVal.atLps cv ps` (`cv` the record `c`'s, `ps` the
`EREC` name slice `(po, pl)`) as the 4 words at `d`, a region its caller allocated: `er_to_iw` and
`param_levels` (`plW_sim`; the twin's `paramLevels` an interning step, `paramLevels_run`, so
`TwinOK` by `TwinOK.of_istep`), `inst_lp` under `CoreS` (`InstLPOK`, `StageT.of_core`), then the
words (`wrER_fresh`: the region above the base state's top, `EnvR` from the base).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- The lookups and program facts the pins at a stream's names need. -/
structure QuotAtProg (p : Prog) : Prop where
  cvAt : p.lookup "cv_at_lps" = some cvAtLps
  iwAlloc : p.lookup "iw_alloc" = some iwAlloc
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  iwCopy : p.lookup "iw_copy" = some iwCopy
  slCons : p.lookup "sl_cons" = some slCons
  slGet : p.lookup "sl_get" = some slGet
  paramFind : p.lookup "param_find" = some paramFind
  paramPush : p.lookup "param_push" = some paramPush
  internParam : p.lookup "intern_param" = some internParam
  plGo : p.lookup "param_levels_go" = some paramLevelsGoL
  pl : p.lookup "param_levels" = some paramLevelsL
  il : IlF p
  erPut : p.lookup "erec_put" = some erecPut
  erAlloc : p.lookup "erec_alloc" = some erecAlloc
  instLP : InstLPOK p
  core : CoreStageClosed p
  coreErec : closedA p coreErecA coreErecC coreFns = true
  quot : QuotClosed p
  plc : PlClosed p
  qph : p.lookup "quot_pin_hit" = some quotPinHitL
  cvLps : p.lookup "cv_lps" = some cvLps
  slContains : p.lookup "sl_contains" = some slContains
  slNodup : p.lookup "sl_nodup" = some slNodup
  canon : CanonProg p
  qat : p.lookup "quot_at" = some L.Ind.quotAt

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`StageT` across `param_levels`**: its `StageR` post, the twin's interning step, the frame
(`plFns` leaves the core memos, the pins and the records alone). -/
theorem StageT.of_pl {m m' : Mem} {a a' : AState} (hT : StageT dn vis fe m a)
    (hS : StageR vis fe m' a') (hs : ConRon.Bridge.Frontend.IStepS a a')
    (hf : MemFrame plA plC m m') : StageT dn vis fe m' a' := by
  have na : ∀ b ∈ plBad, b ∉ plA := fun _ h => plA_not h
  have nc : ∀ x ∈ plBadC, x ∉ plC := fun _ h => plC_not h
  refine ⟨hS, hT.twin.of_istep hs (by rw [hf.size]; exact hT.twin.erec)
    (by rw [hf.size]; exact hT.twin.spn) (by rw [hf.size]; exact hT.twin.bstk)
    (hT.twin.memos.frame hf ⟨na _ (by simp [plBad]), na _ (by simp [plBad])⟩
      ⟨nc _ (by simp [plBadC]), nc _ (by simp [plBadC])⟩
      ⟨na _ (by simp [plBad]), na _ (by simp [plBad]), na _ (by simp [plBad])⟩
      ⟨nc _ (by simp [plBadC]), nc _ (by simp [plBadC]), nc _ (by simp [plBadC])⟩
      ⟨na _ (by simp [plBad]), na _ (by simp [plBad]), na _ (by simp [plBad])⟩
      ⟨nc _ (by simp [plBadC]), nc _ (by simp [plBadC]), nc _ (by simp [plBadC])⟩
      (na _ (by simp [plBad])) (nc _ (by simp [plBadC]))), ?_⟩
  have hP : m'.arr64 PINS = m.arr64 PINS := hf.arr PINS (na _ (by simp [plBad])) (by decide)
  simp only [pinW, hP]; exact hT.flag

/-- **`StageT` across record words** (`wrER`): the `StageR` after it, the twin unchanged. -/
theorem StageT.of_wrER {m : Mem} {a : AState} {d : Word} {ws : List Word}
    (hT : StageT dn vis fe m a) (hS : StageR vis fe (wrER m d ws) a) :
    StageT dn vis fe (wrER m d ws) a := by
  have hf := (wrER_frame ws m d).mono (C' := [129, 130]) (fun _ h => h) (by simp)
  refine ⟨hS, hT.twin.frame hf (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide), ?_⟩
  have hP : (wrER m d ws).arr64 PINS = m.arr64 PINS := hf.arr PINS (by decide) (by decide)
  simp only [pinW, hP]; exact hT.flag

end

/-- A constant value from its four words. -/
theorem decCV_of_words {a : Nat → Option Word} {q : Nat} {w0 w1 w2 w3 : Word} {ps : List NIdx}
    (h0 : a q = some w0) (h0l : w0.toNat < 2 ^ 32) (h1 : a (q + CV.lpsOff.toNat) = some w1)
    (h2 : a (q + CV.lpsLen.toNat) = some w2) (hs : hslice? a w1.toNat w2.toNat = some ps)
    (h3 : a (q + CV.type.toNat) = some w3) (h3l : w3.toNat < 2 ^ 32) :
    decCV a q = some ⟨decI w0, ps, decI w3⟩ := by
  have h2' : a (q + CV.lpsOff.toNat + 1) = some w2 := by
    rw [Nat.add_assoc, ← CV.lpsLen_toNat]; exact h2
  refine decCV_of (by simp [hd?, h0, h0l]) ?_ (by simp [hd?, h3, h3l])
  simp only [hlist?, nat?, h1, h2', hs, Option.map_some, bind, Option.bind_some]

/-- A constant value from its four words, as `wrER` leaves them. -/
theorem decCV_of_wr4 {a : Nat → Option Word} {q : Nat} {w0 w1 w2 w3 : Word} {ps : List NIdx}
    (hrd : ∀ j < [w0, w1, w2, w3].length, a (q + j) = [w0, w1, w2, w3][j]?) (h0l : w0.toNat < 2 ^ 32)
    (hs : hslice? a w1.toNat w2.toNat = some ps) (h3l : w3.toNat < 2 ^ 32) :
    decCV a q = some ⟨decI w0, ps, decI w3⟩ :=
  decCV_of_words (by simpa using hrd 0 (by simp)) h0l (by simpa [rec_unfold] using hrd 1 (by simp))
    (by simpa [rec_unfold] using hrd 2 (by simp)) hs (by simpa [rec_unfold] using hrd 3 (by simp)) h3l

theorem word_add12 (c : Word) : c + 1 + 2 = c + 3 := by rw [UInt64.add_assoc]; rfl
theorem word_add13 (c : Word) : c + 1 + 3 = c + 4 := by rw [UInt64.add_assoc]; rfl

/-- `erec_put` as a call. -/
theorem callW_erecPut {p : Prog} (hp : p.lookup "erec_put" = some erecPut) {n : Nat} {a v : Word}
    {m m' : Mem} {r : List Word} (h : callW p n "erec_put" [a, v] m = some (r, m')) :
    m' = erecPutMem m a v := by
  obtain ⟨s', rfl, -, h1, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (erecPut_specW p hp n _ a v) h
  exact h1

theorem word_add21 (d : Word) : d + 2 + 1 = d + 3 := by rw [UInt64.add_assoc]; rfl

theorem c129_coreErecC : (129 : Word) ∉ coreErecC := by
  intro hmem
  simp only [coreErecC, List.mem_map, List.mem_filter, List.mem_range] at hmem
  obtain ⟨x, ⟨hx, hne⟩, e⟩ := hmem
  have := congrArg UInt64.toNat e
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', decide_eq_true_eq] at this hne
  have h129 : (129 : Word).toNat = 129 := rfl
  have h130 : (130 : Word).toNat = 130 := rfl
  omega
theorem c130_coreErecC : (130 : Word) ∉ coreErecC := by
  intro hmem
  simp only [coreErecC, List.mem_map, List.mem_filter, List.mem_range] at hmem
  obtain ⟨x, ⟨hx, hne⟩, e⟩ := hmem
  have := congrArg UInt64.toNat e
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', decide_eq_true_eq] at this hne
  have h129 : (129 : Word).toNat = 129 := rfl
  have h130 : (130 : Word).toNat = 130 := rfl
  omega

theorem instLp_core : "inst_lp" ∈ coreFns := List.elem_iff.mp (by decide)
theorem instLp_stageCore : "inst_lp" ∈ stageCoreFns :=
  mem_stageCoreFns (List.mem_append_right _ instLp_core) (by simp [coreLeafOnly])

section cv
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`cv_at_lps(d, c + 1, po, pl)` refines `cv.atLps ps`** (`cv` the record `c`'s constant value,
`ps` the name slice `(po, pl)` at a base state `m₀` whose top is at or below `d`): `StageT` after,
the growth and the frame from the base, the written value at `d`, every other address as before. -/
theorem cvAtLps_sim {p : Prog} (hP : QuotAtProg p) (n : Nat) {m₀ m : Mem} {a₀ a : AState}
    (h₀ : StageR vis fe m₀ a₀) (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a)
    (hf : MemFrame quotA quotC m₀ m) (hg : IWGrow m₀ m)
    {d c po pl : Word} {cv : IConstantVal} {ps : List NIdx} {psv : List ConLeche.Name}
    (hd0 : erTopOf m₀ d ≤ erOff d) (hdt : erOff d + 4 ≤ erTopOf m d) (hd41 : d.toNat < 2 ^ 41)
    (hcv : decCV (erecP m) (c.toNat + CI.cv.toNat) = some cv)
    (hps : hslice? (erecP m₀) po.toNat pl.toNat = some ps)
    (hden : ConRon.Arena.Frontend.denoteNList a.store.ns ps = some psv) :
    Sim (callW p n "cv_at_lps" [d, c + CI.cv, po, pl] m) (cv.atLps ps) a
      (fun _ cv' m' a' => StageT dn vis fe m' a' ∧ IWGrow m₀ m' ∧ MemFrame quotA quotC m₀ m' ∧
        decCV (erecP m') d.toNat = some cv' ∧
        (∀ i, (∀ j < 4, i % 2 ^ 41 ≠ (d.toNat + j) % 2 ^ 41) → erecP m' i = erecP m i) ∧
        erecP m' (d.toNat + 1) = some po ∧ erecP m' (d.toNat + 2) = some pl ∧
        ∀ x, erTopOf m' x = erTopOf m x) := by
  intro r m' h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (cvAtLps_specW p hP.cvAt n _ d (c + CI.cv) po pl) h
  cases n with
  | zero => simp [cvAtLpsW] at hW
  | succ n =>
  -- a whole-record writer (`cv_at_lps`): the offsets as numbers (`rec_unfold`)
  simp only [cvAtLpsW, rec_unfold, UInt64.reduceAdd] at hW
  -- `er_to_iw(po, pl)`
  cases h1 : callW p n "er_to_iw" [po, pl] m with
  | none => rw [h1] at hW; simp [cvAtLpsW.k_er_to_iw] at hW
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at hW; simp only [cvAtLpsW.k_er_to_iw] at hW
  have hps' : hslice? (erecP m) po.toNat pl.toNat = some ps := ArrExt.hslice? hg.erecGrow.ext hps
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erToIw_specW p hP.iwAlloc hP.erCopy hP.erToIw n _ po pl) h1
  obtain ⟨hS1, hg1, hdl1, htop1, -⟩ := erToIwW_stage hW1 hT.stage hps'
  have hT1 : StageT dn vis fe s1.mem a := StageT.of_iw hT hS1 (erToIwW_iwFr hW1)
  obtain ⟨hpf1, he1⟩ := callW_plFrame hP.plc (by decide) h1
  have hqf1 := callW_quotFrame hP.quot (by decide) h1
  -- `param_levels(io, il)`
  cases h2 : callW p n "param_levels" [r1.headD 0, r1.tail.headD 0] s1.mem with
  | none => rw [h2] at hW; simp [cvAtLpsW.k_param_levels] at hW
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2] at hW; simp only [cvAtLpsW.k_param_levels] at hW
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (plW_spec p hP.iwAlloc hP.iwCopy hP.slCons hP.slGet hP.paramFind hP.paramPush hP.internParam
      hP.plGo hP.pl hP.il n _ _ _) h2
  obtain ⟨us, a1, hrun1, hH, hus, hS2, hg2⟩ := plW_sim (k := n) hS1 hdl1 (by omega) r2 s2.mem hW2
  obtain ⟨hpf2, he2⟩ := callW_plFrame hP.plc (by decide) h2
  have hqf2 := callW_quotFrame hP.quot (by decide) h2
  obtain ⟨hst1, -⟩ := ConRon.Bridge.paramLevels_run hok hden hrun1
  have hT2 : StageT dn vis fe s2.mem a1 := StageT.of_pl hT1 hS2 hst1 hpf2
  -- `inst_lp(EREC⦃c + 2⦄, EREC⦃c + 3⦄, us, EREC⦃c + 4⦄)`, the record words unchanged so far
  have hpf12 := hpf1.trans hpf2
  have hr2 := erRd_congr (m := m) (m' := s2.mem) (hpf12.arr _ (plA_not (by simp [plBad])) (by decide))
    (hpf12.arr _ (plA_not (by simp [plBad])) (by decide))
  have he12 : erecP s2.mem = erecP m := by rw [he2, he1]
  simp only [hr2, L.add_one_add_one, word_add12, word_add13] at hW
  obtain ⟨-, -, hlps, -, hty32, hty⟩ := decCV_rd_ci (erRdOK m) hcv
  cases h3 : callW p n "inst_lp" [erRd m (c + 2), erRd m (c + 3), r2.headD 0, erRd m (c + 4)] s2.mem with
  | none => rw [h3] at hW; simp [cvAtLpsW.k_inst_lp] at hW
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3] at hW; simp only [cvAtLpsW.k_inst_lp] at hW
  obtain ⟨M, hC⟩ := hT2.core
  obtain ⟨s3, rfl, -, hok3, ⟨M', hC', -, -⟩, hres3, hrh3⟩ :=
    triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
      (hP.instLP n ⟨s2.mem, Locals.init []⟩ a1 dn vis fe M 0 _ _ (r2.headD 0) _ cv.levelParams hC
        hty32 hH (by rw [he12]; exact hlps)) h3
  obtain ⟨hT3, hg3⟩ := StageT.of_core hP.core instLp_stageCore h3 hT2 hC'
  obtain ⟨hE3, hE13, hrd3, he3⟩ := callW_erec_closedT hP.coreErec instLp_core h3
  have hqf3 := callW_quotFrame hP.quot (by decide) h3
  have hr3 := fun x => (erRd_congr (m := s2.mem) (m' := s3.mem) hE3 hE13 x).trans (hr2 x)
  simp only [hr3] at hW
  -- the four words
  cases h4 : callW p n "erec_put" [d, erRd m (c + 1)] s3.mem with
  | none => rw [h4] at hW; simp [cvAtLpsW.k_erec_put] at hW
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [h4] at hW; simp only [cvAtLpsW.k_erec_put] at hW
  cases h5 : callW p n "erec_put" [d + 1, po] m4 with
  | none => rw [h5] at hW; simp [cvAtLpsW.k_erec_put_2] at hW
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  rw [h5] at hW; simp only [cvAtLpsW.k_erec_put_2] at hW
  cases h6 : callW p n "erec_put" [d + 2, pl] m5 with
  | none => rw [h6] at hW; simp [cvAtLpsW.k_erec_put_3] at hW
  | some x6 =>
  obtain ⟨r6, m6⟩ := x6
  rw [h6] at hW; simp only [cvAtLpsW.k_erec_put_3] at hW
  cases h7 : callW p n "erec_put" [d + 3, r3.headD 0] m6 with
  | none => rw [h7] at hW; simp [cvAtLpsW.k_erec_put_4] at hW
  | some x7 =>
  obtain ⟨r7, m7⟩ := x7
  rw [h7] at hW; simp only [cvAtLpsW.k_erec_put_4, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨-, rfl⟩ := hW
  rw [callW_erecPut hP.erPut h4] at h5
  rw [callW_erecPut hP.erPut h5] at h6
  rw [callW_erecPut hP.erPut h6] at h7
  rw [callW_erecPut hP.erPut h7]
  have hwr : erecPutMem (erecPutMem (erecPutMem (erecPutMem s3.mem d (erRd m (c + 1))) (d + 1) po)
      (d + 2) pl) (d + 3) (r3.headD 0) = wrER s3.mem d [erRd m (c + 1), po, pl, r3.headD 0] := by
    simp only [wrER, L.add_one_add_one, word_add21]
  rw [hwr]
  -- the region and the words
  have hg3' : IWGrow m₀ s3.mem := hg.trans (hg1.trans (hg2.trans hg3))
  have hf3' : MemFrame quotA quotC m₀ s3.mem := ((hf.trans hqf1).trans hqf2).trans hqf3
  have htop : erTopOf m d ≤ erTopOf s3.mem d := by
    have hgm := hg1.trans (hg2.trans hg3)
    unfold erTopOf; split
    · exact hgm.er
    · exact hgm.er1
  obtain ⟨hSw, hgw, hfw, hrd, hout⟩ := wrER_fresh h₀ [erRd m (c + 1), po, pl, r3.headD 0] s3.mem _ d
    hT3.stage hf3' hg3' hd0 (by simp only [List.length_cons, List.length_nil]; omega) hd41
  obtain ⟨⟨w0, hw0, hw0l, hname⟩, -, -⟩ := decCV_words hcv
  have e0 : erRd m (c + 1) = w0 := (erRdOK m).at CI.cv rfl hw0
  have hrun3 := L.Arena.AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  refine ⟨⟨cv.name, ps, decH r3⟩, _, ?_, StageT.of_wrER hT3 hSw, hgw, hfw, ?_, fun i hi => ?_,
    by simpa using hrd 1 (by simp), by simpa using hrd 2 (by simp), fun x => ?_⟩
  · simp only [IConstantVal.atLps, StateT.run_bind, hrun1, ← hus, hty, ← decE_eq, L.Arena.except_ok_bind, hrun3,
      StateT.run_pure]
    rfl
  · rw [hname, e0]
    rw [e0] at hrd hgw
    exact decCV_of_wr4 hrd hw0l (ArrExt.hslice? hgw.erecGrow.ext hps) hrh3
  · rw [hout i hi, he3, he12]
  · have hc3 := (run_memFrame hP.coreErec instLp_core (run_of_callW h3)).1
    have e129 : rdW (s3.mem.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := by
      rw [hc3.ctl 129 c129_coreErecC, hpf2.ctl 129 (plC_not (by simp [plBadC])),
        hpf1.ctl 129 (plC_not (by simp [plBadC]))]
    have e130 : rdW (s3.mem.arr64 CTL) 130 = rdW (m.arr64 CTL) 130 := by
      rw [hc3.ctl 130 c130_coreErecC, hpf2.ctl 130 (plC_not (by simp [plBadC])),
        hpf1.ctl 130 (plC_not (by simp [plBadC]))]
    simp only [erTopOf, erTop, erecTop1, wrER_ctl, e129, e130]

end cv


section alloc
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`erec_alloc(k)` under `StageT`**: the tops moved, nothing else. -/
theorem erAlloc_stageT {m m' : Mem} {a : AState} {k q : Word} (h : erAllocW m k = some (q, m'))
    (hT : StageT dn vis fe m a) :
    StageT dn vis fe m' a ∧ IWGrow m m' ∧ erOff q = erTopOf m q ∧
      erTopOf m' q = erTopOf m q + k.toNat ∧ q.toNat < 2 ^ 41 := by
  obtain ⟨hg, hf, hoff, htop, -, -, hq41, hW⟩ := erAllocW_spec h hT.stage.iw
  have hI : m'.arr64 IW = m.arr64 IW := hf.arr IW (by simp) (by decide)
  have hgI : IWGrow m m' :=
    { iw := by simp only [iwTop]; rw [hf.ctl 200 (by decide)]; exact Nat.le_refl _
      er := hg.top, iwGet := fun i _ => by rw [hI], erGet := hg.get, er1 := hg.top1
      er1Get := hg.get1 }
  have hfe : MemFrame [EREC, tier1 EREC] [129, 130] m m' := hf.mono (by simp) (fun _ h => h)
  refine ⟨⟨⟨CheckR.erGrow hT.stage.check hfe hg, hW⟩,
    hT.twin.frame hf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_⟩,
    hgI, hoff, htop, hq41⟩
  have hP : m'.arr64 PINS = m.arr64 PINS := hf.arr PINS (by simp) (by decide)
  simp only [pinW, hP]; exact hT.flag

theorem callW_erecAlloc {p : Prog} (hp : p.lookup "erec_alloc" = some erecAlloc) {n : Nat} {k : Word}
    {m m' : Mem} {r : List Word} (h : callW p n "erec_alloc" [k] m = some (r, m')) :
    erAllocW m k = some (r.headD 0, m') := by
  obtain ⟨s', rfl, -, h1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (erecAlloc_specW p hp n _ k) h
  exact h1

end alloc

/-! ## `quot_pin_hit(k, q)` -/

/-- **The pinned quotient package's slot** (`quot_pin(k)`, the reader of the ROM's block 4) under
`StageT`: the record of the slot after it. The reader's statement is the pipeline's (lane
`ronsync2`, p3q); taken as a hypothesis here. -/
structure QuotPinSim (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop where
  qp : ∀ (n : Nat) (vis : Word) (fe : IFEnv) (m : Mem) (a : AState) (k : ConLeche.QuotKind),
    StageT dn vis fe m a → ConRon.Bridge.StateOK a →
    Sim (callW p n "quot_pin" [UInt64.ofNat k.slot] m) (ConRon.Arena.quotPin k) a
      (fun r ci m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧
        decCI (erecP m') (r.headD 0).toNat = some ci)

/-- **`Quot`'s `sortZ` name has a handle** under the record pool's name decoder `dn` (a fact about
the startup store, state-free; the loop threads it from its start). -/
def QuotDn (dn : NIdx → Option ConLeche.Name) : Prop := ∃ k, dn k = some (.str .anonymous "u")

/-- The quotient readers' precondition from `QuotDn` and the decoder's agreement with the twin's
name store (`TwinMem.dnN`, i.e. `TwinOK.den.dnN`). -/
theorem QuotDn.namesDn {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState}
    (hq : QuotDn dn) (hT : TwinMem dn m a) : L.Rom.NamesDn dn a L.Rom.quotNames := by
  intro x hx
  simp only [L.Rom.quotNames, List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  obtain ⟨k, hk⟩ := hq
  exact ⟨k, hk, hT.dnN k _ hk⟩

/-- **`StageT` across a leaf** whose twin op is an interning step (`IStepS`): its `StageR` post, the
leaves' frame (the pins and the core memos kept). -/
theorem StageT.of_leafI {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a a' : AState} (hT : StageT dn vis fe m a) (hS : StageR vis fe m' a')
    (hs : ConRon.Bridge.Frontend.IStepS a a') (hf : MemFrame leafA leafC m m') :
    StageT dn vis fe m' a' := by
  refine ⟨hS, hT.twin.of_istep hs (by rw [hf.size]; exact hT.twin.erec)
    (by rw [hf.size]; exact hT.twin.spn) (by rw [hf.size]; exact hT.twin.bstk)
    (hT.twin.memos.frame hf leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp leafA_hb leafC_hb), ?_⟩
  have hP : m'.arr64 PINS = m.arr64 PINS := hf.arr PINS leafA_pins (by decide)
  simp only [pinW, hP]; exact hT.flag

/-- **The slot reader refines `quotPin`**, from the quotient block reader's refinement
(`RomQuotRef`, `RomRefs.quot`), the leaves' write set (`rom_basis_decls` is a leaf) and `QuotDn`. -/
theorem quotPinSim_of {p : Prog} {dn : NIdx → Option ConLeche.Name}
    (hp : p.lookup "quot_pin" = some quotPin) (hR : ∀ vis fe, L.Rom.RomQuotRef p dn vis fe)
    (hcl : LeafClosed p) (hq : QuotDn dn) : QuotPinSim p dn where
  qp n vis fe m a k hT hok := by
    intro r m' h
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (quotPin_specW p hp n _ (UInt64.ofNat k.slot)) h
    cases n with
    | zero => simp [quotPinW] at hW
    | succ n =>
    simp only [quotPinW] at hW
    cases h1 : callW p n "rom_basis_decls" [4] m with
    | none => rw [h1] at hW; simp [quotPinW.k_rom_basis_decls] at hW
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1] at hW
    obtain ⟨blk, a1, hrun1, hS1, hg1, hD1⟩ :=
      hR vis fe n m a r1 m1 ⟨hT.stage, hok, hq.namesDn hT.twin.mem⟩ h1
    have hrun1' : ConRon.Arena.BasisKind.decls .quotK a = .ok (blk, a1) := hrun1
    obtain ⟨hs1, hden1⟩ := ConRon.Bridge.BasisKind.decls_run hok hrun1'
    have hf1 : MemFrame leafA leafC m m1 :=
      (run_memFrame hcl (leaf_mem _ rfl) (run_of_callW h1)).1
    have hT1 := hT.of_leafI hS1 hs1 hf1
    have hlen : blk.length = 5 := by
      rw [denoteCIList_length _ _ hden1]; decide
    have hk5 : k.slot < 5 := by cases k <;> decide
    obtain ⟨hDp, hbd⟩ := decRBlk_canon hD1 (by omega)
    have hl : (r1.tail.headD 0).toNat = 5 := by rw [← decPL_length m1 hDp, hlen]
    obtain ⟨v, hv, hx, hci⟩ := decPL_get' hDp k.slot (by omega)
    simp only [quotPinW.k_rom_basis_decls] at hW
    have hl5 : r1.tail.headD 0 = 5 := UInt64.toNat_inj.mp (by rw [hl]; rfl)
    have hks : (UInt64.ofNat k.slot : Word).toNat = k.slot := by
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    rw [ite_eq_right (by rw [hl5, UInt64.le_iff_toNat_le, hks]; simp; omega), Option.some.injEq,
      Prod.mk.injEq] at hW
    obtain ⟨rfl, hm⟩ := hW
    rw [← hm]
    obtain ⟨w, hw, rfl⟩ : ∃ w, iwA m1 ((r1.headD 0).toNat + k.slot) = some w ∧ w.toNat = v := by
      simp only [iwN, nat?, Option.map_eq_some_iff] at hv; exact hv
    have htop : iwTop m1 < 2 ^ 64 := UInt64.toNat_lt_size _
    have hidx : (r1.headD 0 + UInt64.ofNat k.slot).toNat = (r1.headD 0).toNat + k.slot := by
      rw [UInt64.toNat_add, hks]; omega
    have ew : rdW (m1.arr64 IW) (r1.headD 0 + UInt64.ofNat k.slot) = w := by
      simp only [iwA, aread_apply] at hw; simp only [rdW, hidx, hw, Option.getD_some]
    refine ⟨blk[k.slot], a1, ?_, hT1, hg1, by rw [ew]; exact hci⟩
    have : blk.getD k.slot default = blk[k.slot] := by simp [List.getD, hx]
    simp only [ConRon.Arena.quotPin, StateT.run_bind]
    rw [show StateT.run (BasisKind.decls ConLeche.BasisKind.quotK) a = .ok (blk, a1) from hrun1',
      ← this]; rfl

section qph
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`quot_pin_hit(k, q)` refines `quotPinHit k cv`**: the slot's pin, `cv`'s names
(`cv_lps`, `sl_nodup`), their count against the pin's, the pin at them (`erec_alloc`,
`cv_at_lps`) and the comparison (`cv_eq`). -/
theorem quotPinHit_sim {p : Prog} (hP : QuotAtProg p) (hQ : QuotPinSim p dn) (n : Nat) {m : Mem}
    {a : AState} {q : Word} {cv : IConstantVal} {c : ConLeche.ConstantVal} (k : ConLeche.QuotKind)
    (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a)
    (hq : decCV (erecP m) q.toNat = some cv)
    (hden : ConRon.Arena.Frontend.denoteCV a.store cv = some c) :
    Sim (callW p n "quot_pin_hit" [UInt64.ofNat k.slot, q] m) (ConRon.Arena.quotPinHit k cv) a
      (fun r b m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0 ≠ 0 ↔ b = true)) := by
  intro r m' h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (quotPinHit_specW p hP.qph n _ (UInt64.ofNat k.slot) q) h
  cases n with
  | zero => simp [quotPinHitW] at hW
  | succ n =>
  simp only [quotPinHitW] at hW
  -- `quot_pin(k)`
  cases h1 : callW p n "quot_pin" [UInt64.ofNat k.slot] m with
  | none => rw [h1] at hW; simp [quotPinHitW.k_quot_pin] at hW
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at hW; simp only [quotPinHitW.k_quot_pin] at hW
  obtain ⟨ci, a1, hrun1, hT1, hg1, hci⟩ := hQ.qp n vis fe m a k hT hok r1 m1 h1
  obtain ⟨hst1, -⟩ := ConRon.Bridge.quotPin_run (s' := a1) hok hrun1
  have hpcv : decCV (erecP m1) ((r1.headD 0).toNat + CI.cv.toNat) = some ci.toConstantVal := decCI_cv hci
  have hq1 : decCV (erecP m1) q.toNat = some cv := ArrExt.decCV hg1.erecGrow.ext hq
  -- `cv_lps(q)`
  cases h2 : callW p n "cv_lps" [q] m1 with
  | none => rw [h2] at hW; simp [quotPinHitW.k_cv_lps] at hW
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2] at hW; simp only [quotPinHitW.k_cv_lps] at hW
  obtain ⟨s2, rfl, -, hW2, hr2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (cvLps_specW p hP.iwAlloc hP.erCopy hP.erToIw hP.cvLps n _ q) h2
  cases n with
  | zero => exact absurd hW2 (by simp [L.Arena.cvLpsW])
  | succ n0 =>
  rw [L.Arena.cvLpsW_step] at hW2
  obtain ⟨-, -, hsl1, hlen1, -⟩ := decCV_rd (erRdOK m1) hq1
  obtain ⟨hS2, hg2, hdl2, htop2, -⟩ := erToIwW_stage hW2 hT1.stage hsl1
  have hT2 : StageT dn vis fe s2.mem a1 := StageT.of_iw hT1 hS2 (erToIwW_iwFr hW2)
  have hf2 := erToIwW_iwFr hW2
  have hrd2 := erRd_congr (m := m1) (m' := s2.mem) (hf2.arr _ (by decide) (by decide))
    (hf2.arr _ (by decide) (by decide))
  have he2 : erecP s2.mem = erecP m1 := erecP_frame hf2 (by decide) (by decide) (by decide) (by decide)
  -- `sl_nodup(io, il)`
  obtain ⟨ws, hws, hwsd, hwH⟩ := slR_of_decHL s2.mem _ _ _ hdl2
    (by have := (rdW (s2.mem.arr64 CTL) 200).toNat_lt; simp only [iwTop] at htop2; omega)
  simp only [UInt64.ofNat_toNat] at hws
  cases h3 : callW p (n0 + 1) "sl_nodup" [r2.headD 0, r2.tail.headD 0] s2.mem with
  | none => rw [h3] at hW; simp [quotPinHitW.k_sl_nodup] at hW
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  obtain ⟨s3, rfl, -, hm3, hnd⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (slNodup_refines p hP.slContains hP.slNodup (n0 + 1) _ _ _ ws hws hwH) h3
  rw [h3] at hW; simp only [quotPinHitW.k_sl_nodup] at hW
  simp only [hm3, hrd2] at hW
  rw [← hwsd] at hnd
  obtain ⟨-, -, -, hplen, -, -⟩ := decCV_rd_ci (erRdOK m1) hpcv
  have hlen2 : cv.levelParams.length = (r2.tail.headD 0).toNat := hslice?_lenR hdl2
  have hcond : (r3.headD 0 ≠ 0 ∧ r2.tail.headD 0 = erRd m1 (r1.headD 0 + (CI.cv + CV.lpsLen))) ↔
      (nameNodup cv.levelParams && cv.levelParams.length == ci.toConstantVal.levelParams.length) = true := by
    rw [Bool.and_eq_true, ← hnd, beq_iff_eq, hlen2, hplen, bne_iff_ne, ne_eq]
    exact and_congr_right fun _ => ⟨fun e => by rw [e], fun e => UInt64.toNat_inj.mp e⟩
  have hrunP : ∀ b a', (ConRon.Arena.quotPinHit k cv).run a = .ok (b, a') ↔
      (if (nameNodup cv.levelParams && cv.levelParams.length == ci.toConstantVal.levelParams.length)
        then (do let x ← ci.toConstantVal.atLps cv.levelParams; pure (cv == x) : AM Bool)
        else pure false).run a1 = .ok (b, a') := by
    intro b a'
    simp only [ConRon.Arena.quotPinHit, StateT.run_bind, hrun1, L.Arena.except_ok_bind]
  by_cases hc : r3.headD 0 ≠ 0 ∧ r2.tail.headD 0 = erRd m1 (r1.headD 0 + (CI.cv + CV.lpsLen))
  case neg =>
    rw [ite_eq_right hc] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, e⟩ := hW
    have e2 : s'.mem = s2.mem := by
      first | exact e.symm.trans hm3 | exact e.trans hm3 | exact e | exact e.symm
    have hc' := mt hcond.mpr hc
    refine ⟨false, a1, (hrunP _ _).mpr (by simp [hc']; rfl), ?_, ?_, by simp⟩
    · rw [e2]; exact hT2
    · rw [e2]; exact hg1.trans hg2
  rw [ite_eq_left_iff.mpr (fun h => absurd hc h)] at hW
  -- `erec_alloc(4)`
  cases h4 : callW p (n0 + 1) "erec_alloc" [4] s2.mem with
  | none => rw [h4] at hW; simp [quotPinHitW.k_erec_alloc] at hW
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [h4] at hW; simp only [quotPinHitW.k_erec_alloc] at hW
  have hA := callW_erecAlloc hP.erAlloc h4
  obtain ⟨hT4, hg4, hoff4, htop4, hq41⟩ := erAlloc_stageT hA hT2
  obtain ⟨-, hf4, -⟩ := erAllocW_spec hA hT2.stage.iw
  have hqf4 := callW_quotFrame hP.quot (by decide) h4
  have hrd4 := fun x => (erRd_congr (m := s2.mem) (m' := m4) (hf4.arr _ (by simp) (by decide))
    (hf4.arr _ (by simp) (by decide)) x).trans (hrd2 x)
  simp only [hrd4] at hW
  -- `cv_at_lps(a, c + 1, EREC⦃q + 1⦄, EREC⦃q + 2⦄)`
  cases h5 : callW p (n0 + 1) "cv_at_lps" [r4.headD 0, r1.headD 0 + CI.cv, erRd m1 (q + CV.lpsOff), erRd m1 (q + CV.lpsLen)] m4 with
  | none => rw [h5] at hW; simp [quotPinHitW.k_cv_at_lps] at hW
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  rw [h5] at hW; simp only [quotPinHitW.k_cv_at_lps] at hW
  obtain ⟨cv', a2, hrun2, hT5, hg5, -, hdec5, -, -, -, -⟩ := cvAtLps_sim hP (n0 + 1) hT2.stage hT4 hst1.ok hqf4 hg4
    (d := r4.headD 0) (c := r1.headD 0) (by rw [hoff4]; exact Nat.le_refl _) (by rw [htop4, hoff4]; simp) hq41
    (ArrExt.decCV (hg2.trans hg4).erecGrow.ext hpcv) (by rw [he2]; exact hsl1)
    (ConRon.Bridge.denoteNListE_ext hst1.ext _ _ (ConRon.Bridge.denoteCV_inv hden).2.1) r5 m5 h5
  -- `cv_eq(q, a)`
  cases h6 : callW p (n0 + 1) "cv_eq" [q, r4.headD 0] m5 with
  | none => rw [h6] at hW; simp [quotPinHitW.k_cv_eq] at hW
  | some x6 =>
  obtain ⟨r6, m6⟩ := x6
  obtain ⟨s6, rfl, -, hm6, hr6⟩ := triple_of_callW (s₀ := ⟨m5, Locals.init []⟩)
    (cvEq_spec' p hP.canon (n0 + 1) _ q (r4.headD 0)) h6
  rw [h6] at hW; simp only [quotPinHitW.k_cv_eq, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, e⟩ := hW
  have e2 : s'.mem = m5 := by
    first | exact e.symm.trans hm6 | exact e.trans hm6 | exact (hm6.symm.trans e).symm | exact hm6.symm.trans e
  have hq5 : decCV (erecP m5) q.toNat = some cv :=
    ArrExt.decCV hg5.erecGrow.ext (ArrExt.decCV hg2.erecGrow.ext hq1)
  have hb := cvEqB_ok (erRdOK m5) hq5 hdec5
  refine ⟨cv == cv', a2, (hrunP _ _).mpr ?_, ?_, ?_, ?_⟩
  · simp only [hcond.mp hc, ite_true, StateT.run_bind, hrun2, L.Arena.except_ok_bind, StateT.run_pure]
    rfl
  · rw [e2]; exact hT5
  · rw [e2]; exact hg1.trans (hg2.trans hg5)
  · simp only [List.headD_cons, hr6, hb, beq_iff_eq]
    by_cases hcc : cv = cv' <;> simp [hcc]


end qph

/-! ## `quot_at(k, q)` and the two simulations `check_quot_record` takes -/

/-- **A pin at a stream's names** (`ci_at_lps(c, po, pl)` refines `ci.atLps ps`) under `StageT`:
the fresh record after it. Open: its six kinds (`cv_at_lps` by `cvAtLps_sim`, a definition's
value by `inst_lp`, a recursor's rules by `rules_at_lps_go`/`fire_levels_at`). -/
structure CiAtLpsSim (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop where
  ci : ∀ (n : Nat) (vis : Word) (fe : IFEnv) (m : Mem) (a : AState) (c po pl : Word)
    (ci : IConstantInfo) (ps : List NIdx) (psv : List ConLeche.Name) (cc : ConLeche.ConstantInfo),
    StageT dn vis fe m a → ConRon.Bridge.StateOK a → ConRon.Bridge.ReadOK a →
    decCI (erecP m) c.toNat = some ci → ConRon.Arena.Frontend.denoteCI a.store ci = some cc →
    hslice? (erecP m) po.toNat pl.toNat = some ps →
    ConRon.Arena.Frontend.denoteNList a.store.ns ps = some psv →
    Sim (callW p n "ci_at_lps" [c, po, pl] m) (ci.atLps ps) a
      (fun r ci' m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧
        decCI (erecP m') (r.headD 0).toNat = some ci')

section qat
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`quot_at(k, q)` refines `quotAt k cv`**: the slot's pin, then the pin at `cv`'s names. -/
theorem quotAt_sim {p : Prog} (hP : QuotAtProg p) (hQ : QuotPinSim p dn) (hC : CiAtLpsSim p dn)
    (n : Nat) {m : Mem} {a : AState} {q : Word} {cv : IConstantVal} {c : ConLeche.ConstantVal}
    (k : ConLeche.QuotKind) (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a)
    (hr : ConRon.Bridge.ReadOK a) (hq : decCV (erecP m) q.toNat = some cv)
    (hden : ConRon.Arena.Frontend.denoteCV a.store cv = some c) :
    Sim (callW p n "quot_at" [UInt64.ofNat k.slot, q] m) (ConRon.Arena.quotAt k cv) a
      (fun r ci m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧
        decCI (erecP m') (r.headD 0).toNat = some ci) := by
  intro r m' h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (quotAt_specW p hP.qat n _ (UInt64.ofNat k.slot) q) h
  cases n with
  | zero => simp [quotAtW] at hW
  | succ n =>
  simp only [quotAtW] at hW
  cases h1 : callW p n "quot_pin" [UInt64.ofNat k.slot] m with
  | none => rw [h1] at hW; simp [quotAtW.k_quot_pin] at hW
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at hW; simp only [quotAtW.k_quot_pin] at hW
  obtain ⟨ci, a1, hrun1, hT1, hg1, hci⟩ := hQ.qp n vis fe m a k hT hok r1 m1 h1
  obtain ⟨hst1, hpin⟩ := ConRon.Bridge.quotPin_run (s' := a1) hok hrun1
  have hq1 : decCV (erecP m1) q.toNat = some cv := ArrExt.decCV hg1.erecGrow.ext hq
  obtain ⟨-, -, hsl1, -, -⟩ := decCV_rd (erRdOK m1) hq1
  simp only [L.Ind.erRd_foldN] at hW
  cases h2 : callW p n "ci_at_lps" [r1.headD 0, erRd m1 (q + CV.lpsOff), erRd m1 (q + CV.lpsLen)] m1 with
  | none => rw [h2] at hW; simp [quotAtW.k_ci_at_lps] at hW
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2] at hW; simp only [quotAtW.k_ci_at_lps, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨ci', a2, hrun2, hT2, hg2, hdec2⟩ := hC.ci n vis fe m1 a1 _ _ _ ci cv.levelParams
    c.levelParams _ hT1 hst1.ok (ConRon.Bridge.RStep.of_istep hst1 hr).read hci hpin hsl1
    (ConRon.Bridge.denoteNListE_ext hst1.ext _ _ (ConRon.Bridge.denoteCV_inv hden).2.1) r2 m2 h2
  obtain ⟨rfl, rfl⟩ := hW
  refine ⟨ci', a2, ?_, hT2, hg1.trans hg2, hdec2⟩
  simp only [ConRon.Arena.quotAt, StateT.run_bind, hrun1, L.Arena.except_ok_bind, hrun2]

/-- **The simulations `check_quot_record` takes**, from the slot reader's and `ci_at_lps`'s. -/
theorem quotSims_of {p : Prog} (hP : QuotAtProg p) (hQ : QuotPinSim p dn) (hC : CiAtLpsSim p dn) :
    QuotSims p dn :=
  ⟨fun n _ _ _ _ _ _ _ k hT hok _ hq hden => quotPinHit_sim hP hQ n k hT hok hq hden,
   fun n _ _ _ _ _ _ _ k hT hok hr hq hden => quotAt_sim hP hQ hC n k hT hok hr hq hden⟩

end qat

end L.Ind
