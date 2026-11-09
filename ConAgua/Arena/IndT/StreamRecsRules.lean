module

public import ConAgua.Arena.IndT.StreamRecsTy
import ConAgua.Arena.RefWalk
import ConAgua.Arena.IndT.Lift
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Inductives.StreamRecs
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

end L.Ind

end
