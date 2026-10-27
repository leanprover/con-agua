import ConAgua.Arena.RecGenSpec6
import ConAgua.Arena.Verdict
import ConAgua.Checker.NoVerdictFns

/-!
# Error refinement of `class_fields_of(_go)` (lane `verdicts-b`, helper `ib`)

Mirrors `cfgW_sim` / `cfoW_sim` (`RecGenSpec6`): the callees are all `closedNV`, so an error comes
from the single abort (`R_GENERATED_RECURSOR_THE_INDUCTIVE`, the twin's `fail`) or is a callee's.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model cfgE_spec (p : Prog) (hf : p.lookup "class_fields_of_go" = some classFieldsOfGo)
  fns [hf ↦ cfgE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

l_model cfoE_spec (p : Prog) (hf : p.lookup "class_fields_of" = some classFieldsOfL)
  fns [hf ↦ cfoE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
variable {p : Prog} (P : CfoProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true)

include P hnv in
/-- **`class_fields_of_go`' model error claim** (`cfgW_sim`'s hypotheses). -/
theorem cfgE_claim (bsh : BlockShape) (ihs : List (Nat × Nat)) (n : Nat) :
    ∀ (m : Mem) (a : AState) (mo ml io il i fo fl : Word) (fs : List EIdx)
    (mp0 : Std.HashMap EIdx Bool),
    StageR dn vis fe m a →
    decHL m mo.toNat ml.toNat = some bsh.memberNames → mo.toNat + ml.toNat ≤ iwTop m →
    StabD (fun m => decPL m (decNN m) io.toNat il.toNat) m ihs → io.toNat + il.toNat < 2 ^ 64 →
    decHL m fo.toNat fl.toNat = some fs → fo.toNat + fl.toNat ≤ iwTop m →
    i.toNat + fl.toNat < 2 ^ 64 → noMR m mp0 →
    ∀ e, cfgE p n m mo ml io il i fo fl = .error e →
      ErrClaim (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a e := by
  induction n with
  | zero =>
    intro m a mo ml io il i fo fl fs mp0 hS hmn hmb hih hib hfs hfb hi hM e he
    rw [cfgE.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a mo ml io il i fo fl fs mp0 hS hmn hmb hih hib hfs hfb hi hM e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hsz := hS.2.2.2.1
  have htop := hS.2.1
  by_cases hfl : fl = 0
  · rw [cfgE.arm1 p n m mo ml io il i fo fl hfl] at he
    cases he
  rw [cfgE.arm2 p n m mo ml io il i fo fl hfl] at he
  obtain ⟨w0, fs', rfl, hw0, hw0H, hfs'⟩ := decHL_cons hfs hfl (by omega)
  subst hw0
  obtain ⟨hsum, hfo1⟩ := toNat_succ_of_lt (o := fo) (l := fl) (by omega) hfl
  have hfl1 : (fl - 1).toNat + 1 = fl.toNat := by omega
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [ConRon.Arena.classFieldsOf]
  -- `fvar_type_d`
  cases h1 : callE p n "fvar_type_d" [rdW (m.arr64 IW) fo] m with
  | error e1 =>
    rw [h1, cfgE.k_fvar_type_d.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, cfgE.k_fvar_type_d.arm1] at he
  obtain ⟨s1, hs1, -, hw1⟩ := triple_of_callW (ftdF_spec0 p P.ftd n ⟨m, Locals.init []⟩ [rdW (m.arr64 IW) fo])
    (callW_of_callE h1)
  subst hs1
  dsimp only at hw1
  obtain ⟨w, a1, hrun1, hS1, hg1, hwH, hwd⟩ := simFvarTypeD hS hw0H (r1, s1.mem) hw1
  dsimp only at hS1 hg1 hwH hwd
  subst hwd
  refine ErrClaim.bind_right hrun1 ?_
  have hM1 := rec2NoMR_ftd hw1 hM
  -- `nest_occ`
  cases h2 : callE p n "nest_occ" [mo, ml, 0, 0, r1.headD 0] s1.mem with
  | error e2 =>
    rw [h2, cfgE.k_nest_occ.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, cfgE.k_nest_occ.arm1] at he
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (nestOcc_spec' p P.no n ⟨s1.mem, Locals.init []⟩ mo ml 0 0
    (r1.headD 0)) (callW_of_callE h2)
  subst hs2
  dsimp only at hw2
  obtain ⟨occ, a2, hrun2, ha2, hob, hM2, hS2, hg2, hf2⟩ :=
    rec2SimNestOcc hS1 hwH (by rw [decHL_grow hg1 hmb]; exact hmn) (by omega) hM1 n
      (r2.headD 0, s2.mem) hw2
  subst ha2
  dsimp only at hob hM2 hS2 hg2 hf2
  refine ErrClaim.bind_right hrun2 ?_
  have hf12 : MFr [NOM] [204, 205] m s2.mem :=
    (MFr.of_frame (ftdF_frame hw1) (by simp) (by simp)).up.trans hf2
  have hg12 := hg1.trans hg2
  -- `class_fields_of_hits`
  cases h3 : callE p n "class_fields_of_hits" [io, il, i] s2.mem with
  | error e3 =>
    rw [h3, cfgE.k_class_fields_of_hits.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨s3, hs3, -, hm3, hw3⟩ := triple_of_callW (classFieldsOfHits_spec p P.hits n ⟨s2.mem, Locals.init []⟩
    io il i) (callW_of_callE h3)
  subst hs3
  dsimp only at hm3 hw3
  obtain ⟨hcnt, hcls⟩ := cfhW_ok n s2.mem io il i _ _ ihs hw3 (hih s2.mem hg12) hib hS2.2.2.2.1
  have hrest : ∀ m5 (ce : Err), StageR dn vis fe m5 a2 → IWGrow s2.mem m5 → noMR m5 ∅ →
      cfgE p n m5 mo ml io il (i + 1) (fo + 1) (fl - 1) = .error ce →
      ErrClaim (ConRon.Arena.classFieldsOf bsh ihs (i.toNat + 1) fs') a2 ce := by
    intro m5 ce hS5 hg5 hM5 hce
    have hg := hg12.trans hg5
    have := ih m5 a2 mo ml io il (i + 1) (fo + 1) (fl - 1) fs' ∅ hS5
      (by rw [decHL_grow hg hmb]; exact hmn) (Nat.le_trans hmb hg.1) (hih.grow hg) hib
      (by rw [decHL_grow hg (by omega)]; exact hfs') (by have := hg.1; omega) (by omega) hM5 ce hce
    rwa [hi1] at this
  have htail : ∀ (m5 : Mem) (cf : Word) (X : ConRon.Arena.ClassField),
      StageR dn vis fe m5 a2 → IWGrow s2.mem m5 → noMR m5 ∅ →
      cfgE.j1 p n mo ml io il i (fo) fl cf m5 = .error e →
      ErrClaim (do let rest ← ConRon.Arena.classFieldsOf bsh ihs (i.toNat + 1) fs'; pure (X :: rest)) a2 e := by
    intro m5 cf X hS5 hg5 hM5 hj
    rw [cfgE.j1.arm1] at hj
    cases h6 : cfgE p n m5 mo ml io il (i + 1) (fo + 1) (fl - 1) with
    | error e6 =>
      rw [h6, cfgE.k_class_fields_of_go.none] at hj
      cases hj
      exact ErrClaim.bind_left (hrest m5 _ hS5 hg5 hM5 h6)
    | ok q6 =>
      obtain ⟨r6, m6⟩ := q6
      rw [h6, cfgE.k_class_fields_of_go.arm1] at hj
      cases h7 : callE p n "sl_cons" [cf, r6.headD 0, r6.tail.headD 0] m6 with
      | error e7 =>
        rw [h7, cfgE.k_sl_cons.none] at hj
        cases hj
        exact ErrClaim.of_callE_nv hnv (by decide +kernel) h7
      | ok q7 =>
        rw [h7, cfgE.k_sl_cons.arm1] at hj
        cases hj
  by_cases hA : r2.headD 0 = 0 ∧ r3.headD 0 = 0
  · rw [h3, cfgE.k_class_fields_of_hits.arm1 p n _ _ _ _ _ _ _ _ _ _ _ hA, hm3] at he
    obtain rfl : occ = false := by rw [← hob, hA.1]; rfl
    have hlen : (List.filter (fun h => h.1 == i.toNat) ihs).length = 0 := by rw [← hcnt, hA.2]; rfl
    simp only [hlen, Bool.not_false, Bool.true_and, beq_self_eq_true, ite_true]
    cases h4 : callE p n "iw_alloc" [1] s2.mem with
    | error e4 =>
      rw [h4, cfgE.k_iw_alloc.none] at he
      cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
    | ok q4 =>
      obtain ⟨r4, m4⟩ := q4
      rw [h4, cfgE.k_iw_alloc.arm1] at he
      obtain ⟨s4, hs4, -, hal⟩ := triple_of_callW (iwAlloc_specW p P.alloc n ⟨s2.mem, Locals.init []⟩ 1)
        (callW_of_callE h4)
      subst hs4
      dsimp only at hal
      have h5 : recW s2.mem 1 [0] = some ([r4.headD 0], s4.mem.set64 IW (r4.headD 0) 0) := by
        simp [recW, hal, wrIW]
      obtain ⟨hr5, -, hg5, hf5, htop5, hroom5⟩ := recW_post h5 hS2.2.2.2.2.2 hS2.2.2.2.1 rfl
      exact htail _ _ _ (stage_frame_iw hS2 hf5 (by omega)) hg5 (rec2NoMR_iw hf5 hM2) he
  by_cases hB : r2.headD 0 ≠ 0 ∧ r3.headD 0 = 1
  · rw [h3, cfgE.k_class_fields_of_hits.arm2 p n _ _ _ _ _ _ _ _ _ _ _ hA hB, hm3] at he
    obtain rfl : occ = true := by rw [← hob]; simpa using hB.1
    have hlen : (List.filter (fun h => h.1 == i.toNat) ihs).length = 1 := by rw [← hcnt, hB.2]; rfl
    obtain ⟨hh, hhs⟩ := List.length_eq_one_iff.mp hlen
    obtain ⟨hcl, hcl64⟩ := hcls hh hhs
    simp only [hhs, Bool.not_true, Bool.false_and, Bool.true_and,
      ite_false, Bool.false_eq_true]
    cases h4 : callE p n "pi_binders" [CWF, r1.headD 0] s2.mem with
    | error e4 =>
      rw [h4, cfgE.k_pi_binders.none] at he
      cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
    | ok q4 =>
      obtain ⟨r4, m4⟩ := q4
      rw [h4, cfgE.k_pi_binders.arm1] at he
      obtain ⟨s4, hs4, -, hpb⟩ := triple_of_callW (piBinders_spec' p P.alloc P.copy P.no.hv P.cons P.pb n
        ⟨s2.mem, Locals.init []⟩ CWF (r1.headD 0)) (callW_of_callE h4)
      subst hs4
      dsimp only at hpb
      obtain ⟨⟨bsx, ex⟩, a4, hrun4, rfl, hS4, hg4, hf4, hd4⟩ := rec2SimPiBinders n hS2 hwH (r4, s4.mem) hpb
      dsimp only at hS4 hg4 hf4 hd4
      refine ErrClaim.bind_right hrun4 ?_
      cases h5 : callE p n "rec3" [1, r3.tail.headD 0, r4.tail.headD 0] s4.mem with
      | error e5 =>
        rw [h5, cfgE.k_rec3.none] at he
        cases he
        exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
      | ok q5 =>
        obtain ⟨r5, m5⟩ := q5
        rw [h5, cfgE.k_rec3.arm1] at he
        obtain ⟨s5, hs5, -, hrc⟩ := triple_of_callW (rec3_specW p P.alloc n P.r3 ⟨s4.mem, Locals.init []⟩ 1
          (r3.tail.headD 0) (r4.tail.headD 0)) (callW_of_callE h5)
        subst hs5
        dsimp only at hrc
        obtain ⟨hr5, -, hg5, hf5, htop5, hroom5⟩ := recW_post hrc hS4.2.2.2.2.2 hS4.2.2.2.1 rfl
        exact htail _ _ _ (stage_frame_iw hS4 hf5 (by omega)) (hg4.trans hg5)
          (rec2NoMR_iw hf5 (rec2NoMR_iw hf4 hM2)) he
  rw [h3, cfgE.k_class_fields_of_hits.abort1 p n _ _ _ _ _ _ _ _ _ _ _ hA hB] at he
  cases he
  have hc0 := hcnt
  cases occ with
  | false =>
    have h20 : r2.headD 0 = 0 := by simpa using hob
    have h30 : (r3.headD 0).toNat ≠ 0 := fun h =>
      hA ⟨h20, UInt64.toNat_inj.mp (by simpa using h)⟩
    simp only [← hc0, h30, Bool.not_false, Bool.true_and, beq_iff_eq, Bool.false_and, ite_false]
    simp only [Bool.false_eq_true, ite_false]
    exact ErrClaim.fail _ _ (by decide)
  | true =>
    have h20 : r2.headD 0 ≠ 0 := by simpa using hob
    have h30 : (r3.headD 0).toNat ≠ 1 := fun h =>
      hB ⟨h20, UInt64.toNat_inj.mp (by simpa using h)⟩
    simp only [← hc0, h30, Bool.not_true, Bool.false_and, Bool.true_and, beq_iff_eq, ite_false]
    simp only [Bool.false_eq_true, ite_false]
    exact ErrClaim.fail _ _ (by decide)

include P hnv in
/-- **`class_fields_of_go`' error claim** (every fuel). -/
theorem classFieldsOfGo_claim (n : Nat) (s₀ : St) (a₀ : AState) (mo ml io il i fo fl : Word)
    (bsh : BlockShape) (ihs : List (Nat × Nat)) (fs : List EIdx) (mp0 : Std.HashMap EIdx Bool)
    (hS : StageR dn vis fe s₀.mem a₀)
    (hmn : decHL s₀.mem mo.toNat ml.toNat = some bsh.memberNames) (hmb : mo.toNat + ml.toNat ≤ iwTop s₀.mem)
    (hih : StabD (fun m => decPL m (decNN m) io.toNat il.toNat) s₀.mem ihs) (hib : io.toNat + il.toNat < 2 ^ 64)
    (hfs : decHL s₀.mem fo.toNat fl.toNat = some fs) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem)
    (hi : i.toNat + fl.toNat < 2 ^ 64) (hM : noMR s₀.mem mp0) :
    CoreSpecE p n "class_fields_of_go" [mo, ml, io, il, i, fo, fl]
      (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) s₀ a₀ :=
  CoreSpecE.of_runs fun e hc => by
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact cfgE_claim P hnv bsh ihs n s₀.mem a₀ mo ml io il i fo fl fs mp0 hS hmn hmb hih hib hfs hfb hi hM e
      (triple_of_callE_err (cfgE_spec p P.go n s₀ mo ml io il i fo fl) hc (Err.code_ne_of_cls hk0))

include P hnv in
/-- **`class_fields_of`' error claim** (every fuel). -/
theorem classFieldsOf_claim (n : Nat) (s₀ : St) (a₀ : AState) (q io il i fo fl : Word)
    (bsh : BlockShape) (ihs : List (Nat × Nat)) (fs : List EIdx) (mp0 : Std.HashMap EIdx Bool)
    (hS : StageR dn vis fe s₀.mem a₀) (hb : BSOK s₀.mem q.toNat bsh)
    (hih : StabD (fun m => decPL m (decNN m) io.toNat il.toNat) s₀.mem ihs) (hib : io.toNat + il.toNat < 2 ^ 64)
    (hfs : decHL s₀.mem fo.toNat fl.toNat = some fs) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem)
    (hi : i.toNat + fl.toNat < 2 ^ 64) (hM : noMR s₀.mem mp0) :
    CoreSpecE p n "class_fields_of" [q, io, il, i, fo, fl]
      (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) s₀ a₀ := by
  refine CoreSpecE.of_runs fun e hc => ?_
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have he := triple_of_callE_err (cfoE_spec p P.cfo n s₀ q io il i fo fl) hc (Err.code_ne_of_cls hk0)
  cases n with
  | zero =>
    simp only [cfoE] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n =>
  rw [cfoE.arm1] at he
  cases h1 : callE p n "block_shape_member_names" [q] s₀.mem with
  | error e1 =>
    rw [h1, cfoE.k_block_shape_member_names.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, cfoE.k_block_shape_member_names.arm1] at he
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW (blockShapeMemberNames_spec p P.alloc P.mnc P.mn n s₀ q)
    (callW_of_callE h1)
  subst hs1
  have ht := hb.ptop
  have hsz := hS.2.2.2.1
  have hts : iwTop s₀.mem ≤ (s₀.mem.arr64 IW).size := hS.2.1
  have hf1 := (memberNamesW_dec h1m hsz hS.2.2.2.2.2 hb.dec (by omega) hb.2.1 hb.2.2).2.2.2.1
  obtain ⟨hS1, hg1, -, hd1, ht1⟩ := memberNamesW_stage h1m hS hb
  cases h2 : callE p n "class_fields_of_go" [r1.headD 0, r1.tail.headD 0, io, il, i, fo, fl] s1.mem with
  | error e2 =>
    rw [h2, cfoE.k_class_fields_of_go.none] at he
    cases he
    exact CoreSpecE.of_callE (classFieldsOfGo_claim P hnv n ⟨s1.mem, Locals.init []⟩ a₀ _ _ io il i fo fl bsh ihs fs mp0 hS1 hd1
      (by dsimp only; omega) (hih.grow hg1) hib (by rw [decHL_grow hg1 hfb]; exact hfs) (Nat.le_trans hfb hg1.1) hi
      (rec2NoMR_iw hf1 hM)) h2
  | ok q2 =>
    rw [h2, cfoE.k_class_fields_of_go.arm1] at he
    cases he

end sims

end L.Ind
