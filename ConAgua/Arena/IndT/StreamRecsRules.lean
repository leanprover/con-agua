module

public import ConAgua.Arena.IndT.StreamRecsTy
import ConAgua.Arena.RefWalk
import ConAgua.Arena.IndT.Lift
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Inductives.StreamRecs
import ConRon.Bridge.Checker.Canon
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclCanonRules
import ConAgua.Arena.IndPosSpec.NestKeyMap
import ConAgua.Arena.IndSumSpec.TsrW
import ConAgua.Arena.IndInstallSpec.DomsW
import all ConAgua.Arena.IndStream

@[expose] public section

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups of the stored recursors' checks. -/
structure StrProg (p : Prog) : Prop extends StrTyProg p where
  srs : p.lookup "stream_rules_shape" = some streamRulesShapeL
  srk : p.lookup "stream_rules_check" = some streamRulesCheckL
  src : p.lookup "stream_rec_compare" = some streamRecCompareL
  sr1 : p.lookup "stream_rec_check" = some streamRecCheckL
  srsc : p.lookup "stream_recs_check" = some streamRecsCheckL

set_option experimental.vcgen true in
/-- **`stream_rules_shape`'s unified model** (reads only). -/
l_model srsE_spec (p : Prog) (hP : StrProg p)
  fns [hP.srs ↦ srsE]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`stream_rules_check`'s unified model**: `rule_agree` through its model, the recursion
through the model. -/
l_model srkE_spec (p : Prog) (hP : StrProg p)
  fns [hP.srk ↦ srkE]
  specs [raE_spec p hP.toStrTyProg n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- A word the record pool decodes as a number. -/
theorem erRd_natA {m : Mem} {a : Word} {k : Nat} (h : nat? (erA m) a.toNat = some k) :
    (erRd m a).toNat = k := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  rw [erRd_of_erA hw]

/-- A word the record pool decodes as a handle. -/
theorem erRd_hd {k : IdxKind} {m : Mem} {a : Word} {x : Idx k} (h : hd? (erA m) a.toNat = some x) :
    H (erRd m a) ∧ x = decI (erRd m a) := by
  obtain ⟨w, hw, hl, rfl⟩ := hd?_some h
  rw [erRd_of_erA hw]; exact ⟨hl, rfl⟩

theorem erA_lt {m : Mem} {i : Nat} {v : Word} (h : erA m i = some v) : i < 2 ^ 64 :=
  (erRdOK m).lt i v h

section sims
variable {p : Prog}

/-- **`stream_rules_shape` refines `streamRulesShape`, both outcomes** (it reads only; twin side
con-ron's `streamRulesShape_run`): per rule, its constructor's name and field count against the
class's constructor record. -/
theorem srs_ref {G : Prop} (N : Nat) : ∀ (m : Mem) (a : AState) (ro rl co cl : Word)
    (rs : List IRecRule) (cs : List (IConstantVal × Nat)),
    (m.arr64 IW).size < 2 ^ 64 → decRules (erA m) ro.toNat rl.toNat = some rs →
    decPL m (decCN m) co.toNat cl.toNat = some cs → co.toNat + cl.toNat ≤ (m.arr64 IW).size →
    RefE G (srsE p N m ro rl co cl) (ConRon.Arena.streamRulesShape rs cs) a
      (fun v _ a' => v.2 = m ∧ a' = a) := by
  induction N with
  | zero => intros; rw [srsE.eq_1]; exact RefE.of_cls0 rfl
  | succ N ih =>
  intro m a ro rl co cl rs cs hsz hrs hcs hcb
  have hrl := decRules_length hrs
  have hcl := decPL_length m hcs
  by_cases h0 : rl = 0 ∧ cl = 0
  · rw [srsE.arm1 _ _ _ _ _ _ _ h0]
    obtain ⟨e1, e2⟩ := h0
    subst e1 e2
    rw [List.eq_nil_of_length_eq_zero (l := rs) (by simpa using hrl),
      List.eq_nil_of_length_eq_zero (l := cs) (by simpa using hcl)]
    exact RefE.ret rfl ⟨rfl, rfl⟩
  by_cases h1 : rl = 0 ∨ cl = 0
  · rw [srsE.abort1 _ _ _ _ _ _ _ h0 h1]
    rcases h1 with e | e <;> subst e
    · rw [List.eq_nil_of_length_eq_zero (l := rs) (by simpa using hrl)]
      obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
        cases cs with
        | nil => exact absurd ⟨rfl, UInt64.toNat_inj.mp (by simpa using hcl.symm)⟩ h0
        | cons c cs' => exact ⟨c, cs', rfl⟩
      exact fun _ => ErrClaim.fail _ _ rfl
    · rw [List.eq_nil_of_length_eq_zero (l := cs) (by simpa using hcl)]
      obtain ⟨r, rs', rfl⟩ : ∃ r rs', rs = r :: rs' := by
        cases rs with
        | nil => exact absurd ⟨UInt64.toNat_inj.mp (by simpa using hrl.symm), rfl⟩ h0
        | cons r rs' => exact ⟨r, rs', rfl⟩
      exact fun _ => ErrClaim.fail _ _ rfl
  have hrl0 : rl.toNat ≠ 0 := fun h => h1 (.inl (UInt64.toNat_inj.mp (by simpa using h)))
  have hcl0 : cl.toNat ≠ 0 := fun h => h1 (.inr (UInt64.toNat_inj.mp (by simpa using h)))
  obtain ⟨rl', hrl'⟩ : ∃ k, rl.toNat = k + 1 := ⟨rl.toNat - 1, by omega⟩
  obtain ⟨cl', hcl'⟩ : ∃ k, cl.toNat = k + 1 := ⟨cl.toNat - 1, by omega⟩
  rw [hrl', decRules_succ] at hrs
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hrs
  obtain ⟨r, hr, rs', hrs', rfl⟩ := hrs
  have hcl0' : cl ≠ 0 := fun h => h1 (.inr h)
  obtain ⟨q, c, cs', hq, hc, hcs'', rfl, eq0, hqb⟩ := decPL_step hsz hcs hcl0'
  obtain ⟨hrc, hrn, -⟩ := decRule_fields hr
  -- the rule's words
  obtain ⟨hwH, hwc⟩ := erRd_hd hrc
  have hro1 : ro.toNat + 1 < 2 ^ 64 := by
    simp only [nat?, Option.map_eq_some_iff] at hrn
    obtain ⟨w, hw, -⟩ := hrn
    exact erA_lt hw
  have e1 : (ro + 1).toNat = ro.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hwn : (erRd m (ro + 1)).toNat = r.nfields := erRd_natA (by rw [e1]; exact hrn)
  -- the constructor record's words
  simp only [decCN, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hc
  obtain ⟨cvp, hcvp, cv, hcv, nf, hnf, rfl⟩ := hc
  obtain ⟨eq1, hcvpb⟩ := iwN_rdW hcvp hqb
  obtain ⟨eq2, hnfb⟩ := iwN_rdW hnf (by
    simp only [iwN, nat?, iwA, aread_apply, Option.map_eq_some_iff] at hnf
    obtain ⟨w, hw, -⟩ := hnf
    have := (Array.getElem?_eq_some_iff.mp hw).1
    omega)
  obtain ⟨wn, hwn', hwnH, hname⟩ := decCV_name hcv
  have ecv : (UInt64.ofNat cvp : Word).toNat = cvp := UInt64.toNat_ofNat_of_lt' hcvpb
  have eN : erRd m (UInt64.ofNat cvp) = wn := erRd_of_erA (by rw [ecv]; exact hwn')
  have eq2' : rdW (m.arr64 IW) (UInt64.ofNat q + 1) = UInt64.ofNat nf := by
    rw [show (UInt64.ofNat q + 1 : Word) = UInt64.ofNat (q + 1) by simp [UInt64.ofNat_add]]
    exact eq2
  -- the guard
  have key : (erRd m ro = wn ∧ erRd m (ro + 1) = UInt64.ofNat nf) ↔
      (r.ctor == (cv, nf).1.name && r.nfields == (cv, nf).2) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq]
    rw [hwc, hname, decI_inj_iff hwH hwnH, ← hwn]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; exact UInt64.toNat_ofNat_of_lt' hnfb⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← h2]; simp⟩
  simp only [ConRon.Arena.streamRulesShape]
  refine RefE.ofArms (fun h => srsE.abort2 _ _ _ _ _ _ _ h0 h1 h)
    (fun h => srsE.arm2 _ _ _ _ _ _ _ h0 h1 h) ?_
  simp only [eq0, eq1, eq2']
  change RefE G (if (erRd m ro ≠ erRd m (UInt64.ofNat cvp) ∨ erRd m (ro + 1) ≠ UInt64.ofNat nf) then _
    else _) _ a _
  simp only [eN]
  refine RefE.guard (jp := fun _ => ConRon.Arena.streamRulesShape rs' cs') rfl (fun h => by
      cases hb : (r.ctor == (cv, nf).1.name && r.nfields == (cv, nf).2)
      · rfl
      · rcases h with h | h
        · exact absurd (key.mpr hb).1 h
        · exact absurd (key.mpr hb).2 h)
    (fun h => Classical.byContradiction fun hc => by
      have h2 := not_or.mp hc
      have := key.mp ⟨Classical.not_not.mp h2.1, Classical.not_not.mp h2.2⟩
      rw [h] at this; exact absurd this (by decide)) fun _ _ => ?_
  -- the rest
  have hcb' : (co + 1).toNat + (cl - 1).toNat ≤ (m.arr64 IW).size := by
    have e3 : (co + 1).toNat = co.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have e4 : (cl - 1).toNat = cl' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    omega
  have hrs'' : decRules (erA m) (ro + 11).toNat (rl - 1).toNat = some rs' := by
    have e4 : (rl - 1).toNat = rl' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    rw [e4]
    cases rl' with
    | zero => simp [decRules] at hrs' ⊢; exact hrs'
    | succ k =>
      have hb : ro.toNat + 11 < 2 ^ 64 := by
        rw [decRules_succ] at hrs'
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hrs'
        obtain ⟨r2, hr2, -⟩ := hrs'
        obtain ⟨hc2, -⟩ := decRule_fields hr2
        obtain ⟨w, hw, -⟩ := hd?_some hc2
        exact erA_lt hw
      rw [show (ro + 11).toNat = ro.toNat + 11 by rw [UInt64.toNat_add]; simp; omega]
      exact hrs'
  exact RefE.lastE (K := srsE.k_stream_rules_shape p) (f := fun v => (0, v.2)) (fun _ => rfl)
    (fun _ => rfl) id (ih m a (ro + 11) (rl - 1) (co + 1) (cl - 1) rs' cs' hsz hrs'' hcs'' hcb')
    fun _ _ _ _ h => h

end sims

/-- A handle slice at `l + 1`: its head and its tail. -/
theorem decHL_succ_inv {m : Mem} {o l : Nat} {xs : List EIdx}
    (h : decHL m o (l + 1) = some xs) :
    ∃ x xs', xs = x :: xs' ∧ iwH m o = some x ∧ decHL m (o + 1) l = some xs' := by
  simp only [decHL] at h
  rw [hslice?_succ] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨x, hx, xs', hxs', rfl⟩ := h
  exact ⟨x, xs', rfl, hx, hxs'⟩

section sims2
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env}

open ConRon.Bridge.Inductives.SR (denoteRules_cons_inv denoteRules_nil_inv) in
open ConRon.Bridge (denoteRule_inv) in
/-- **`stream_rules_check` refines `streamRulesCheck`, both outcomes** (twin side con-ron's
`streamRulesCheck_spec`): per rule, its right-hand side against the generated one's word, and
`rule_agree` (`ra_ref`) where they differ; the rest by induction. -/
theorem srk_ref (hq : KnotStageProg p) (henv : ConLeche.EnvWF env)
    (hApd : ApdF p) (hCrf : CrfF p) (N : Nat) (hN : N ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (lo ll ro rl go gl : Word) (lps : List NIdx)
      (lpsP : List ConLeche.Name) (rs : List IRecRule) (rsP : List ConLeche.RecRule)
      (gs : List EIdx) (gsP : List ConLeche.Expr),
    StageC dn vis fe env m a → AbsOK m →
    decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    Frontend.denoteNList a.store.ns lps = some lpsP →
    decRules (erA m) ro.toNat rl.toNat = some rs → Frontend.denoteRules a.store rs = some rsP →
    decHL m go.toNat gl.toNat = some gs → (go.toNat + gl.toNat ≤ iwTop m ∨ gl.toNat = 0) →
    Frontend.denoteEList a.store gs = some gsP →
    RefE (VerdictCtxU p) (srkE p N m vis lo ll ro rl go gl)
      (ConRon.Arena.streamRulesCheck V fe lps rs gs) a
      (fun v _ a' => SrPost dn vis fe env m a v.2 a') := by
  induction N with
  | zero => intros; rw [srkE.eq_1]; exact RefE.of_cls0 rfl
  | succ N ih =>
  intro m a lo ll ro rl go gl lps lpsP rs rsP gs gsP hC hA hl hlb hlps hrs hrsP hg hgb hgsP
  have hrl := decRules_length hrs
  have hgl := decHL_length m hg
  by_cases h0 : rl = 0 ∧ gl = 0
  · rw [srkE.arm1 _ _ _ _ _ _ _ _ _ _ h0]
    obtain ⟨e1, e2⟩ := h0
    subst e1 e2
    rw [List.eq_nil_of_length_eq_zero (l := rs) (by simpa using hrl),
      List.eq_nil_of_length_eq_zero (l := gs) (by simpa using hgl),
      ConRon.Arena.streamRulesCheck.eq_2]
    exact RefE.ret rfl (SrPost.refl hC hA)
  by_cases h1 : rl = 0 ∨ gl = 0
  · rw [srkE.abort1 _ _ _ _ _ _ _ _ _ _ h0 h1]; exact RefE.of_cls0 rfl
  have hrl0 : rl.toNat ≠ 0 := fun h => h1 (.inl (UInt64.toNat_inj.mp (by simpa using h)))
  have hgl0 : gl.toNat ≠ 0 := fun h => h1 (.inr (UInt64.toNat_inj.mp (by simpa using h)))
  replace hgb := hgb.resolve_right hgl0
  obtain ⟨rl', hrl'⟩ : ∃ k, rl.toNat = k + 1 := ⟨rl.toNat - 1, by omega⟩
  obtain ⟨gl', hgl'⟩ : ∃ k, gl.toNat = k + 1 := ⟨gl.toNat - 1, by omega⟩
  rw [hrl', decRules_succ] at hrs
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hrs
  obtain ⟨r, hr, rs', hrs', rfl⟩ := hrs
  have hg' := hg
  rw [hgl'] at hg'
  obtain ⟨x, gs', rfl, hx, hgs'⟩ := decHL_succ_inv hg'
  obtain ⟨y, ysP, rfl, hy, hysP⟩ := denoteRules_cons_inv hrsP
  obtain ⟨-, -, hyr, -⟩ := denoteRule_inv hy
  simp only [Frontend.denoteEList] at hgsP
  rcases hxd : denoteE a.store x with _ | xP
  · rw [hxd] at hgsP; simp at hgsP
  rcases hgsd : Frontend.denoteEList a.store gs' with _ | gsP'
  · rw [hxd, hgsd] at hgsP; simp at hgsP
  -- the words
  obtain ⟨-, -, hrh⟩ := decRule_fields hr
  have hro8 : ro.toNat + 8 < 2 ^ 64 := by
    obtain ⟨w, hw, -⟩ := hd?_some hrh
    exact erA_lt hw
  have e8 : (ro + 8).toNat = ro.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hsH, hsr⟩ := erRd_hd (a := ro + 8) (by rw [e8]; exact hrh)
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hC.stage.iw.iwSize
  obtain ⟨w0, ew0, hw0H, hw0⟩ := decHL_word hg hsz 0 (by omega)
  rw [show (0 : Nat).toUInt64 = (0 : Word) from rfl, UInt64.add_zero] at ew0
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hw0
  subst hw0
  have hgo1 : (go + 1).toNat = go.toNat + 1 := by
    have := hC.stage.iw.iw; rw [UInt64.toNat_add]; simp; omega
  have hgl1 : (gl - 1).toNat = gl' := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  have hrl1 : (rl - 1).toNat = rl' := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  have hrs'' : decRules (erA m) (ro + 11).toNat (rl - 1).toNat = some rs' := by
    rw [hrl1]; exact decRules_shift hrs' (erRdOK m).lt
  have hgs'' : decHL m (go + 1).toNat (gl - 1).toNat = some gs' := by rw [hgo1, hgl1]; exact hgs'
  have hgb' : (go + 1).toNat + (gl - 1).toNat ≤ iwTop m := by omega
  rw [ConRon.Arena.streamRulesCheck.eq_1]
  have key : (r.rhs == decI w0) = true ↔ erRd m (ro + 8) = w0 := by
    rw [beq_iff_eq, hsr, decI_inj_iff hsH hw0H]
  by_cases heq : erRd m (ro + 8) = w0
  · rw [srkE.arm3 _ _ _ _ _ _ _ _ _ _ h0 h1 (by rw [ew0]; exact heq), ite_eq_left (key.mpr heq),
      srkE.j1.eq_1]
    refine RefE.lastE (K := srkE.k_stream_rules_check p) (f := fun v => (0, v.2)) (fun _ => rfl)
      (fun _ => rfl) id (ih (by omega) m a lo ll (ro + 11) (rl - 1) (go + 1) (gl - 1) lps lpsP rs'
        ysP gs' gsP' hC hA hl hlb hlps hrs'' hysP hgs'' (.inl hgb') hgsd) fun _ _ _ _ h => h
  rw [srkE.arm2 _ _ _ _ _ _ _ _ _ _ h0 h1 (by rw [ew0]; exact heq),
    ite_eq_right (fun h => heq (key.mp h))]
  rw [ew0, hsr]
  change RefE _ (srkE.k_rule_agree p N vis lo ll ro rl go gl (raE p N m vis lo ll (erRd m (ro + 8)) w0))
    _ a _
  refine RefE.bindE (fun _ => srkE.k_rule_agree.none ..) id
    (ra_ref (s := erRd m (ro + 8)) (g := w0) hq henv hApd hCrf N (by omega) hC hA hsH hw0H hl hlb
      hlps (by rw [← hsr]; exact hyr) hxd) fun ⟨r1, m1⟩ _ a1 _ hR1 => ?_
  rw [srkE.k_rule_agree.arm1, srkE.j1.eq_1]
  refine RefE.lastE (K := srkE.k_stream_rules_check p) (f := fun v => (0, v.2)) (fun _ => rfl)
    (fun _ => rfl) id (ih (by omega) m1 a1 lo ll (ro + 11) (rl - 1) (go + 1) (gl - 1) lps lpsP rs'
      ysP gs' gsP' hR1.stage hR1.abs (by rw [decHL_grow hR1.grow hlb]; exact hl)
      (Nat.le_trans hlb hR1.grow.iw)
      (ConRon.Bridge.denoteNList_ext hR1.core.ext.lss.ls.ns _ _ hlps)
      (ArrExt.decRules hR1.grow.ext hrs'') (ConRon.Bridge.denoteRules_ext hR1.core.ext _ _ hysP)
      (by rw [decHL_grow hR1.grow hgb']; exact hgs'') (.inl (Nat.le_trans hgb' hR1.grow.iw))
      (ConRon.Bridge.denoteEList_ext hR1.core.ext _ _ hgsd)) fun _ _ _ _ h => hR1.trans h

end sims2
set_option experimental.vcgen true in
/-- **`stream_rec_compare`'s unified model**: `cv_lps` lifted, `rec_ty_check` and
`stream_rules_check` through their models. -/
l_model srcE_spec (p : Prog) (hP : StrProg p)
  fns [hP.src ↦ srcE]
  specs [cvLps_specW p hP.cvg.alloc hP.cvg.copy hP.cvg.eti hP.cvg.lps n, rtycE_spec p hP.toStrTyProg n,
    srkE_spec p hP n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`stream_rec_check`'s unified model**: `stream_rules_shape` and `stream_rec_compare` through
their models, `generated_fire` and `stream_nested_ok` lifted. -/
l_model sr1E_spec (p : Prog) (hP : StrProg p)
  fns [hP.sr1 ↦ sr1E]
  specs [srsE_spec p hP n, callW_spec p n "generated_fire", callW_spec p n "stream_nested_ok",
    srcE_spec p hP n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`stream_recs_check`'s unified model**: `stream_rec_check` through its model, the recursion
through the model. -/
l_model srscE_spec (p : Prog) (hP : StrProg p)
  fns [hP.srsc ↦ srscE]
  specs [sr1E_spec p hP n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Ind

end
