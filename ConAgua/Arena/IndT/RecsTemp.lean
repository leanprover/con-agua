module

public import ConAgua.Arena.RecGenSpec.ClassFeR
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Checker.NoVerdictFns
import ConAgua.Arena.RecClassSpec.CrW
import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import all ConAgua.Arena.IndInstall
import ConAgua.Arena.RecClassSpec.MjProg
public import ConAgua.L.ErrSpec
import ConAgua.L.WordOff
import ConAgua.Arena.Verdict

@[expose] public section

/-!
# `cons_block_recs_temp`: the generated family pushed in place (lane `ronsync2`, stage 3)

`cons_block_recs_temp(infos.off, infos.len, vis, prevs.off, prevs.len)` (`IndInstall.lean`) is
con-ron's `consBlockRecsTemp`: each record pushed (`env_push`), the row it displaced (`env_row_get`,
a `rec3` record) appended (`sl_snoc`). The refinement (`cbrt_ok`) gives what
`gen_rec_check_pop_all` takes (`genRecCheckPopAll_refines`): the displaced rows as a stable slice of
`decPrev`/`decPrevC` records and `PopOK` (template: `RecGenSpec/ClassFeR`'s `ferW_ok`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `cons_block_recs_temp`. -/
structure CbrtLook (p : Prog) : Prop where
  cbrt : p.lookup "cons_block_recs_temp" = some consBlockRecsTemp

set_option experimental.vcgen true in
/-- **`cons_block_recs_temp`'s unified model**: the callees lifted. -/
l_model cbrtE_spec (p : Prog) (hP : CbrtLook p)
  fns [hP.cbrt ↦ cbrtE]
  specs [callW_spec p n "env_row_get", callW_spec p n "rec3", callW_spec p n "env_push",
    callW_spec p n "sl_snoc"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## The appended displaced rows -/

theorem FA2.append' {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β} {as' : List α} {bs' : List β},
      FA2 R as bs → FA2 R as' bs' → FA2 R (as ++ as') (bs ++ bs')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h1 h2, h => .cons h1 (FA2.append' h2 h)

/-- `sl_snoc` of a stably decoding pointer onto a stable slice. -/
theorem SPL.snoc {α : Type} {dec : Mem → Nat → Option α} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} {xs : List α} {y : α}
    (h : snocW n m o l x = some (r, m')) (hS : StageR vis fe m a) (hl : SPL dec m o.toNat l.toNat xs)
    (hy : StabD (fun m => dec m x.toNat) m y) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
      SPL dec m' (r.headD 0).toNat (r.tail.headD 0).toNat (xs ++ [y]) := by
  obtain ⟨hb, ps, hps, hf⟩ := hl
  obtain ⟨hr, hd, hg, hfr, -, ht⟩ := snocW_decN h hS.iw.iwSize hS.iw.ctl hb hps
  have hroom := snocW_room h hS.iw.iwSize hS.iw.ctl hb hps
  subst hr
  refine ⟨⟨CheckR.frame_iw hfr hS.check, IWOK.of_iw hfr hS.iw hroom⟩, hg, hfr, by simp only [List.headD_cons, List.tail_cons]; omega,
    ps ++ [x.toNat], by simpa using hd, FA2.append' (FA2.imp (fun _ _ hq => hq.grow hg) hf) (.cons (hy.grow hg) .nil)⟩

/-! ## `cons_block_recs_temp` under the stage relation -/

/-- **`cons_block_recs_temp` is `consBlockRecsTemp`**: from a stage at `vis`, the records a slice of
`EREC` pointers below the top, and the displaced rows so far (`prevs`, their counters `cs`) a
stable slice popping as a stack; the result's view the pushed environment's, the displaced rows
appended (`decPrev`, `decPrevC`), still a stack. -/
theorem cbrt_ok {p : Prog} (hrs : p.lookup "env_row_set" = some envRowSetL)
    (hpu : p.lookup "env_push" = some envPushL) (hrg : p.lookup "env_row_get" = some envRowGetL)
    (hia : p.lookup "iw_alloc" = some iwAlloc) (hr3 : p.lookup "rec3" = some rec3)
    (hcp : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc) :
    ∀ (n : Nat) (m m' : Mem) (a : AState) (vis : Word) (fe : IFEnv) (io il po pl : Word)
      (infos : List IConstantInfo) (prevs : List (NIdx × Option IConstantInfo))
      (cs : List (NIdx × Word)) (r : List Word),
    cbrtE p n m io il vis po pl = .ok (r, m') → StageR vis fe m a →
    decPL m (decCI (erecP m)) io.toNat il.toNat = some infos → io.toNat + il.toNat ≤ iwTop m →
    SPL decPrev m po.toNat pl.toNat prevs → SPL decPrevC m po.toNat pl.toNat cs →
    PopOK (ownC m) vis cs.reverse →
    StageR (r.headD 0) (ConRon.Arena.consBlockRecsTemp infos fe prevs).1 m' a ∧ IWGrow m m' ∧
      SPL decPrev m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat
        (ConRon.Arena.consBlockRecsTemp infos fe prevs).2 ∧
      ∃ cs', SPL decPrevC m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat cs' ∧
        PopOK (ownC m') (r.headD 0) cs'.reverse := by
  intro n
  induction n with
  | zero => intro m m' a vis fe io il po pl infos prevs cs r h; rw [cbrtE.eq_1] at h; cases h
  | succ n ih =>
  intro m m' a vis fe io il po pl infos prevs cs r h hS hd hb hsp hspc hPop
  have hsz := hS.iw.iwSize
  by_cases hz : il = 0
  · rw [cbrtE.arm1 _ _ _ _ _ _ _ _ hz] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    have : infos = [] := by
      have := decPL_length _ hd; rw [hz] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst this
    exact ⟨by simpa [ConRon.Arena.consBlockRecsTemp] using hS, IWGrow.refl m,
      by simpa [ConRon.Arena.consBlockRecsTemp] using hsp, cs, by simpa using hspc, by simpa using hPop⟩
  have hl0 : il.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp (by simpa using e))
  obtain ⟨j, hj⟩ : ∃ j, il.toNat = j + 1 := ⟨il.toNat - 1, by omega⟩
  obtain ⟨cq, ci, infos', rfl, hcq, hci, hrest⟩ := decPL_cons (by rw [← hj]; exact hd)
  obtain ⟨e0, t0⟩ := rec2RdN (w := io) (k := 0) (by simpa using hcq) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at e0
  obtain ⟨w, hw, hw32, hwnm⟩ := decCI_name hci
  have hq1 : (UInt64.ofNat cq + 1 : Word).toNat = cq + 1 := by
    have := L.Arena.erecP_lt64 hw; rw [UInt64.toNat_add, t0]; simp; omega
  have ew : rdW (m.arr64 (tierA EREC ((UInt64.ofNat cq + 1 : Word) >>> 40)))
      ((UInt64.ofNat cq + 1 : Word) &&& 1099511627775) = w :=
    (erRd_of_erecP (a := UInt64.ofNat cq + 1) (by rw [hq1]; exact hw)).1
  rw [cbrtE.arm2 _ _ _ _ _ _ _ _ hz, e0, ew] at h
  -- `env_row_get`
  rcases h1 : callW p n "env_row_get" [w] m with _ | ⟨r1, m1⟩
  · rw [h1, liftE_none, cbrtE.k_env_row_get.none] at h; cases h
  rw [h1, liftE_some, cbrtE.k_env_row_get.arm1] at h
  obtain ⟨s1, hs1, hm1, -, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envRowGet_spec p hrg n ⟨m, Locals.init []⟩ w) h1
  have em1 : m1 = m := hs1 ▸ hm1
  subst hr1
  rw [em1] at h
  simp only [List.headD_cons, List.tail_cons] at h
  -- `rec3`
  rcases h2 : callW p n "rec3" [w, (ownRaw m w).1, (ownRaw m w).2] m with _ | ⟨r2, m2⟩
  · rw [h2, liftE_none, cbrtE.k_rec3.none] at h; cases h
  rw [h2, liftE_some, cbrtE.k_rec3.arm1] at h
  obtain ⟨s2, hs2, -, h2'⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (rec3_specW p hia n hr3 ⟨m, Locals.init []⟩ _ _ _) h2
  subst hs2
  obtain ⟨hS2, hg2, hre, hget2, htop2⟩ := recW_stage h2' hS rfl
  have hO2 : ownC s2.mem = ownC m := ownC_iw (recW_post h2' hS.iw.ctl hS.iw.iwSize rfl).2.2.2.1
  -- `env_push`
  rcases h3 : callW p n "env_push" [vis, UInt64.ofNat cq] s2.mem with _ | ⟨r3, m3⟩
  · rw [h3, liftE_none, cbrtE.k_env_push.none] at h; cases h
  rw [h3, liftE_some, cbrtE.k_env_push.arm1] at h
  have hci2 : decCI (erecP s2.mem) (UInt64.ofNat cq : Word).toNat = some ci := by
    rw [t0]; exact (IWGrow.ext hg2).decCI hci
  obtain ⟨hS3, hg3⟩ := envPush_stage hrs hpu h3 hS2 hci2
  obtain ⟨hO3, hr3', hv3⟩ := envPush_ownC hrs hpu h3 hS2.check.env hci2
  -- the displaced row's records
  have hg02 := hg2
  have hprev := rec3PrevD hS.check.env hw32
  have hent : decPrev s2.mem (r2.headD 0).toNat = some (ci.name, fe.idx[ci.name]?) := by
    rw [hre]
    simp only [List.headD_cons, decPrev, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
    have g0 := hget2 0 (by simp); have g1 := hget2 1 (by simp); have g2 := hget2 2 (by simp)
    simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ] at g0 g1 g2
    refine ⟨decI w, ?_, (ownRaw m w).1, by simpa [iwA, aread_apply] using g1, (ownRaw m w).2,
      by simpa [iwA, aread_apply] using g2, _, rec3PrevD_grow hg02 hprev, by rw [hwnm]⟩
    simp only [iwH, hd?, iwA, aread_apply, g0]; simp [hw32]
  have hroom2 : (r2.headD 0).toNat + 3 ≤ iwTop s2.mem := by
    have := htop2; simp only [List.length_cons, List.length_nil, iwTop] at this
    rw [hre]; simp only [List.headD_cons, iwTop]; omega
  have hentS := rec3DecPrev_stab hent hroom2
  have hentC : StabD (fun m => decPrevC m (r2.headD 0).toNat) s2.mem (ci.name, (ownRaw m w).1) := by
    refine rec3DecPrevC_stab ?_ hroom2
    rw [hre]
    simp only [List.headD_cons, decPrevC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
    have g0 := hget2 0 (by simp); have g1 := hget2 1 (by simp)
    simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ] at g0 g1
    refine ⟨decI w, ?_, (ownRaw m w).1, by simpa [iwA, aread_apply] using g1, by rw [hwnm]⟩
    simp only [iwH, hd?, iwA, aread_apply, g0]; simp [hw32]
  -- `sl_snoc`
  rcases h4 : callW p n "sl_snoc" [po, pl, r2.headD 0] m3 with _ | ⟨r4, m4⟩
  · rw [h4, liftE_none, cbrtE.k_sl_snoc.none] at h; cases h
  rw [h4, liftE_some, cbrtE.k_sl_snoc.arm1] at h
  obtain ⟨s4, hs4, -, h4'⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (slSnoc_specW p hia hcp hsn n ⟨m3, Locals.init []⟩ _ _ _) h4
  subst hs4
  have hg03 := hg2.trans hg3
  obtain ⟨hS4, hg4, hfr4, hsp4⟩ := SPL.snoc h4' hS3 (hsp.grow hg03) (hentS.grow hg3)
  obtain ⟨-, -, -, hspc4⟩ := SPL.snoc h4' hS3 (hspc.grow hg03) (hentC.grow hg3)
  have hO4 : ownC s4.mem = ownC m3 := ownC_iw hfr4
  -- the stack grows by the push
  have hcC : (ownRaw m w).1 = ownC m ci.name := by rw [hwnm]; simp only [ownC, decI_word_self w hw32]
  have hvis1 : (vis + 1).toNat = vis.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hE := hS.check.env
  have hcm : (ownRaw m ci.name.word.toUInt64).1 = (ownRaw m w).1 := by rw [hcC]; rfl
  have hO3' : ownC m3 = updC (ownC s2.mem) ci.name (vis + 1) := hO3
  have hPop4 : PopOK (ownC s4.mem) (r3.headD 0) ((cs ++ [(ci.name, (ownRaw m w).1)]).reverse) := by
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append, hO4, hO3', hO2, hr3',
      List.headD_cons]
    refine ⟨by simp [updC], fun e => by have := congrArg UInt64.toNat e; rw [hvis1] at this; simp at this,
      ownRaw_fst_lt m w, fun hc0 => ?_, fun hc0 n' hn' => ?_, ?_⟩
    · have := hE.fresh ci.name (by rw [hcm]; exact hc0)
      rw [hcm] at this; rw [hvis1]; omega
    · simp only [updC, ite_eq_right hn']
      intro e
      have hn1 : (ownRaw m n'.word.toUInt64).1 = ownC m n' := rfl
      exact hn' (hE.uniq n' ci.name (by rw [hn1, e]; exact hc0) (by rw [hn1, e, hcm]))
    · rw [updC_idem, hcC, updC_self rfl, show vis + 1 - 1 = vis by simp]
      exact hPop
  -- the rest
  have hio1 := rec2ToNat_succ (o := io) (i := io.toNat) (Nat.le_refl _) (by have : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt; omega)
  have hil1 := L.toNat_sub_one_of_ne hz
  have hg04 := hg03.trans hg4
  rcases h5 : cbrtE p n s4.mem (io + 1) (il - 1) (r3.headD 0) (r4.headD 0) (r4.tail.headD 0) with e | ⟨r5, m5⟩
  · rw [h5, cbrtE.k_cons_block_recs_temp.none] at h; cases h
  rw [h5, cbrtE.k_cons_block_recs_temp.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
  have hb' : io.toNat + 1 + j ≤ iwTop m := by omega
  obtain ⟨hS5, hg5, hsp5, cs', hspc5, hPop5⟩ := ih s4.mem m5 a (r3.headD 0) (fe.push ci) (io + 1) (il - 1)
    (r4.headD 0) (r4.tail.headD 0) infos' (prevs ++ [(ci.name, fe.idx[ci.name]?)])
    (cs ++ [(ci.name, (ownRaw m w).1)]) r5 h5 hS4
    (by rw [hio1, hil1, hj]; exact decPL_ci_grow hg04 hb' hrest)
    (by rw [hio1, hil1, hj]; have : iwTop m ≤ iwTop s4.mem := hg04.iw; omega) hsp4 hspc4 hPop4
  simp only [List.headD_cons, List.tail_cons, ConRon.Arena.consBlockRecsTemp]
  exact ⟨hS5, hg04.trans hg5, hsp5, cs', hspc5, hPop5⟩

/-- **`cons_block_recs_temp(io, il, vis, 0, 0)`'s call**: `cbrt_ok` from the empty displaced rows. -/
theorem cbrt_call {p : Prog} (hP : CbrtLook p) (hrs : p.lookup "env_row_set" = some envRowSetL)
    (hpu : p.lookup "env_push" = some envPushL) (hrg : p.lookup "env_row_get" = some envRowGetL)
    (hia : p.lookup "iw_alloc" = some iwAlloc) (hr3 : p.lookup "rec3" = some rec3)
    (hcp : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
    {n : Nat} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} {io il : Word} {r : List Word}
    {infos : List IConstantInfo}
    (hc : callW p n "cons_block_recs_temp" [io, il, vis, 0, 0] m = some (r, m'))
    (hS : StageR vis fe m a) (hd : decPL m (decCI (erecP m)) io.toNat il.toNat = some infos)
    (hb : io.toNat + il.toNat ≤ iwTop m) :
    StageR (r.headD 0) (ConRon.Arena.consBlockRecsTemp infos fe []).1 m' a ∧ IWGrow m m' ∧
      SPL decPrev m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat
        (ConRon.Arena.consBlockRecsTemp infos fe []).2 ∧
      ∃ cs, SPL decPrevC m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat cs ∧
        PopOK (ownC m') (r.headD 0) cs.reverse := by
  obtain ⟨s', hs', -, hx⟩ := triple_of_callE (cbrtE_spec p hP n ⟨m, Locals.init []⟩ io il vis 0 0)
    (callE_of_callW hc)
  subst hs'
  exact cbrt_ok hrs hpu hrg hia hr3 hcp hsn n m s'.mem a vis fe io il 0 0 infos [] [] r hx hS hd hb
    (by simpa using SPL.nil (dec := decPrev) (m := m) 0 (Nat.zero_le _))
    (by simpa using SPL.nil (dec := decPrevC) (m := m) 0 (Nat.zero_le _)) trivial

end L.Ind

end
