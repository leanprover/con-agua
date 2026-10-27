import ConAgua.Arena.DeclArmT
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecClassSpec.CrW
import ConAgua.Arena.RecGenSpec.ClassFeR
import ConAgua.Arena.RecGenSpec.ClassMinorSlot
import ConAgua.Arena.RecGenSpec.Rec3TmdWDecB

/-!
# `classStreamRecs` under `StageC` (lane `indstaget`)

`class_stream_recs`' model at `realCall p`: each recursor constant checked by the program's own
`check_constant_val` (`checkConstantVal_refinesT`, `StageT`; `CheckOK` after from con-ron's
`checkConstantVal_bridge`), the walk memos across it by `AbsKeep`.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dRec dRec_ext dExt_denoteCV mapM_option_cons_inv dRec_inv)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {dn : NIdx → Option ConLeche.Name} {env : ConLeche.Env}
variable {p : Prog} (hq : KnotStageProg p) (henv : ConLeche.EnvWF env) (hV : ValProg p)
 
  (hApd : ApdF p) (hCrk : CrKeep p)

include hq henv hV hApd hCrk in
/-- **`class_stream_recs` under `StageC`** (`csrW_ok`'s; twin side con-ron's `classStreamRecs_spec`). -/
theorem csrW_okC (fe : IFEnv) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m m' : Mem) (a : AState) (vis rcso rcsl : Word) (r : List Word) (recs : List RecShape)
      (recsP : List ConLeche.RecShape),
    csrW (realCall p) n m vis rcso rcsl = some (r, m') → StageC dn vis fe env m a → AbsOK m →
    RecsOK m rcso.toNat rcsl.toNat (recs.map (·.cvR)) → recs.mapM (dRec a.store) = some recsP →
    ∃ cvs a', (ConRon.Arena.classStreamRecs V fe recs).run a = .ok (cvs, a') ∧
      cvs = recs.map (·.cvR) ∧ StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ CsRes m' r cvs ∧
      AbsOK m' ∧ ConRon.Bridge.CoreStep V env fe a a' := by
  induction n with
  | zero => intro m m' a vis rcso rcsl r recs recsP h; simp [csrW] at h
  | succ n ih =>
    intro m m' a vis rcso rcsl r recs recsP h hC hA hOK hrecsP
    have hS := hC.stage
    by_cases hrl : rcsl = 0
    · rw [csrW_nil (realCall p) n m vis rcso rcsl hrl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hz : rcsl.toNat = 0 := by rw [hrl]; rfl
      have hlen := hOK.2.1
      rw [hz] at hlen
      have hnil : recs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hnil
      refine ⟨[], a, rfl, rfl, hC, IWGrow.refl m, ?_, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
      exact ⟨[], by simp [decNL], by simp [decPL], by simp, by simp⟩
    · have hpos : 1 ≤ rcsl.toNat := by
        rcases Nat.eq_zero_or_pos rcsl.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hrl
        · omega
      obtain ⟨l1, hl1⟩ : ∃ l1, rcsl.toNat = l1 + 1 := ⟨rcsl.toNat - 1, by omega⟩
      have hlen := hOK.2.1
      obtain ⟨rc, rest, rfl⟩ : ∃ rc rest, recs = rc :: rest := by
        cases recs with
        | nil => simp at hlen; omega
        | cons rc rest => exact ⟨rc, rest, rfl⟩
      obtain ⟨rcP, restP, rfl, hrcP, hrestP⟩ := mapM_option_cons_inv hrecsP
      have hcvR := (dRec_inv hrcP).1
      rw [hl1] at hOK
      obtain ⟨⟨p0, q, hp0, hp1, hq', hcv, hext⟩, hOKt⟩ := RecsOK_cons (by simpa using hOK)
      have e0 : UInt64.ofNat rcso.toNat = rcso := UInt64.ofNat_toNat
      have hIW64 : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
      have hrd0 := iwN_rdW hp0 (by have := iwN_lt hp0; omega)
      rw [e0] at hrd0
      have hrdq := iwN_rdW hq' (by omega)
      have hqb : q < 2 ^ 64 := hrdq.2
      rw [csrW_cons (realCall p) n m vis rcso rcsl hrl, hrd0.1, hrdq.1] at h
      have hqt : (UInt64.ofNat q).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
      cases hs : realCall p n "check_constant_val" [vis, UInt64.ofNat q] m with
      | none => rw [hs] at h; simp [csK1] at h
      | some r0m =>
        obtain ⟨r0, m1⟩ := r0m
        rw [hs, csK1_some] at h
        have hqb3 : (UInt64.ofNat q : Word).toNat + 3 < 2 ^ 64 := by
          rw [hqt]; exact rec3CVExt_lt hS hext
        obtain ⟨s1, hs1, -, hok1, hT1, hg1, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
          (checkConstantVal_refinesT p hV hq hApd hCrk n (by omega) _ a dn fe vis (UInt64.ofNat q) rc.cvR
            hC.stageT (by rw [hqt]; exact rec2DecCV_erecP hcv hext) hqb3 (denoteCV_lps hcvR)
            hA.crMemo.crOK) hs
        simp only at hs1 hT1 hg1
        subst hs1
        have hrun1 := AM.run_of_ok _ a hok1
        generalize ha1 : AM.st (ConRon.Arena.checkConstantVal V fe rc.cvR) a = a1 at hrun1 hT1
        have hA1 := checkConstantVal_absOK p hV hq hApd hCrk (by omega) hC.stageT
          (by rw [hqt]; exact rec2DecCV_erecP hcv hext) hqb3 (denoteCV_lps hcvR) hA.crMemo.crOK hs hA
        obtain ⟨c1, -⟩ := ConRon.Bridge.checkConstantVal_bridge rfl (ConRon.Bridge.CoreSpec.of_core rfl)
          hC.check henv hcvR hrun1
        have hC1 : StageC dn vis fe env s1.mem a1 := StageC.of_T hT1 c1.ok
        have hOK1 : RecsOK s1.mem (rcso + 1).toNat (rcsl - 1).toNat (rest.map (·.cvR)) := by
          have htopsz : iwTop m ≤ (m.arr64 IW).size := hS.2.1
          have hOKb := hOK.1
          have hro1 : (rcso + 1).toNat = rcso.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
          have hrl1 : (rcsl - 1).toNat = l1 := by
            rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
          rw [hro1, hrl1]
          exact RecsOK_grow hg1 hOKt
        cases hr : csrW (realCall p) n s1.mem vis (rcso + 1) (rcsl - 1) with
        | none => rw [hr] at h; simp [csK2] at h
        | some r2m =>
          obtain ⟨r2, m2⟩ := r2m
          rw [hr, csK2_some] at h
          obtain ⟨cvs2, a2, hrun2, hcvs2, hC2, hg2, ⟨ptrs2, hdn2, hdp2, hext2, htop2⟩, hA2, c2⟩ :=
            ih (by omega) s1.mem m2 a1 vis (rcso + 1) (rcsl - 1) r2 rest restP hr hC1 hA1 hOK1
              (dRec_ext.list c1.ext _ _ hrestP)
          cases hcw : consW n m2 (UInt64.ofNat q) (r2.headD 0) (r2.tail.headD 0) with
          | none => rw [hcw] at h; simp [csK3] at h
          | some r3m =>
            obtain ⟨r3, m3⟩ := r3m
            rw [hcw, csK3_some] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hS3, hg3, hdn3, ht3⟩ := consW_stageN hcw hC2.stage htop2 hdn2
            have hA3 := consW_afr hcw hA2
            have hg13 := (hg1.trans hg2).trans hg3
            have hg23 := hg2.trans hg3
            have hextm3 : CVExt m3 q := CVExt_grow hg13 hext
            refine ⟨rc.cvR :: cvs2, a2, ?_, by rw [hcvs2]; rfl,
              hC2.of_check hS3 hA3 hC2.check (Ext.refl _), hg13, ?_, hA3, c1.trans c2⟩
            · simp only [ConRon.Arena.classStreamRecs, StateT.run_bind]
              rw [hrun1]
              simp only [bind, Except.bind]
              rw [hrun2]
              rfl
            · refine ⟨q :: ptrs2, by simpa [hqt] using hdn3, ?_, ?_, by simpa using Nat.le_of_eq ht3⟩
              · have hdn3' : decNL m3 (r3.headD 0).toNat (r3.tail.headD 0).toNat = some (q :: ptrs2) := by
                  simpa [hqt] using hdn3
                rw [decPL_eq_bind]
                simp only [List.headD_cons, List.tail_cons]
                rw [hdn3']
                simp only [Option.bind_some, List.mapM_cons]
                rw [decCVp_grow_r hg13 hext, hcv]
                have h2 : ptrs2.mapM (decCVp m2) = some cvs2 := by
                  rw [decPL_eq_bind, hdn2] at hdp2; simpa using hdp2
                rw [mapM_decCVp_grow hg3 ptrs2 hext2, h2]
                rfl
              · intro q' hq''
                simp only [List.mem_cons] at hq''
                rcases hq'' with rfl | hq''
                · exact hextm3
                · exact CVExt_grow hg3 (hext2 q' hq'')

include hq henv hV hApd hCrk in
/-- **`class_stream_recs` refines `classStreamRecs .verified`** under `StageC` (the program's own
`check_constant_val`): the result slice holds the recursors' constant pointers, in order. -/
@[refines ConRon.Arena.classStreamRecs]
theorem classStreamRecs_refinesC (hc : p.lookup "iw_copy" = some iwCopy)
    (ha : p.lookup "iw_alloc" = some iwAlloc) (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "class_stream_recs" = some classStreamRecsL) (n : Nat) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (fe : IFEnv) (vis rcso rcsl : Word) (recs : List RecShape)
    (recsP : List ConLeche.RecShape) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hOK : RecsOK s₀.mem rcso.toNat rcsl.toNat (recs.map (·.cvR)))
    (hrecsP : recs.mapM (dRec a₀.store) = some recsP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_stream_recs" [vis, rcso, rcsl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classStreamRecs V fe recs) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.classStreamRecs V fe recs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ CsRes s'.mem r (AM.res (ConRon.Arena.classStreamRecs V fe recs) a₀) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (classStreamRecs_spec p hc ha hsc hp (realCall p) (realCall_spec p) n s₀ vis rcso
    rcsl) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨cvs, a', hrun, -, hC', hg, hres, hA', -⟩ :=
    csrW_okC hq henv hV hApd hCrk fe n hn _ _ a₀ vis rcso rcsl r recs recsP hm hC hA hOK hrecsP
  obtain ⟨hok, hst, hrs⟩ := AM.of_run_ok (ConRon.Arena.classStreamRecs V fe recs) a₀ a' cvs hrun
  exact ⟨hl, hok, by rw [hst]; exact hC', hg, by rw [hrs]; exact hres, hA'⟩

end sims

end L.Ind
