import ConAgua.Arena.IndInstallSpec25

/-!
# Refinements of `IndInstall`, part 26 (lane `indproofs3`, helper `tail`): `checkBlockTables`,
the relation

`check_struct_proj_table` as a callee keeping the memos (`tblW_okM`: lane `indproofs2`'s
`tblW_ok` with the memo frame threaded through; the frame of its last step, `env_push`, needs the
table name a handle, which only the twin side of the proof provides), `struct_proj_guards` as a
callee keeping its memo well formed (`tabSimSpg`), then one member (`ctoW_sim`) and the loop (`ctbW_sim`).

**Hypotheses beyond the stage relation and the decodings**: `HbMemo m` (the `has_loose_bvar_b` memo
well formed in the memory at hand; `struct_proj_guards` needs it) — returned for the memory after.
-/

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_struct_proj_table`, keeping the memos -/

/-- **`tblW_ok` with the memo frame**: the install writes outside the memo region. -/
theorem tblW_okM {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (p : Prog) (hP : TblProg p)
    (n : Nat) (m : Mem) (a : AState) (T C lo ll nP nF rs go gl off cvCaw : Word) (lps : List NIdx)
    (guards : List LIdx) (cvCa : IConstantVal) (hS : StageR dn vis fe m a) (hT : H T) (hC : H C)
    (hrs : H rs) (hnP : nP.toNat + 1 < 2 ^ 64)
    (hlps : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hgs : decHL m go.toNat gl.toNat = some guards) (hgb : go.toNat + gl.toNat ≤ iwTop m)
    (hcv : DecB (fun m => decCVp m cvCaw.toNat) m cvCa) :
    Sim (tblW p n m T C lo ll nP nF rs go gl off cvCaw vis)
      (checkStructProjTable (decI T) (decI C) lps nP.toNat nF.toNat (decI rs) guards off.toNat cvCa fe) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ MFr [] [] m m') := by
  unfold tblW checkStructProjTable
  obtain ⟨w, hw, hwl, hwd⟩ := sumTypeWord (DecB.get (OMono.decCVp _) hcv) hS.2.2.2.2.1
  rw [hw, ← hwd]
  -- `struct_proj_bodies`
  refine Sim.bindK (K := tblK1 p n vis T lo ll nP C nF rs off go gl) rfl (fun _ _ => rfl)
    (Q := fun rb ob m1 a1 => (StageR dn vis fe m1 a1 ∧ IWGrow m m1 ∧ PBDecA m1 rb ob) ∧ MFr [] [] m m1)
    (fun r m' e => by
      obtain ⟨x, a', h1, h2⟩ := spbW_ok dn vis fe (n + 1) m m' a T nP nF w r e hS hwl (by omega)
        nF.toNat_lt
      exact ⟨x, a', h1, h2, spbW_mfr e⟩) fun rb ob m1 a1 hQ => ?_
  obtain ⟨⟨hS1, hg1, hdec1⟩, hf1⟩ := hQ
  by_cases h10 : rb.headD 0 = 0
  · rw [tblK1_no (h := h10)]; exact Sim.of_none
  rw [tblK1_yes (h := h10)]
  cases ob with
  | none => exact absurd hdec1 h10
  | some bodies =>
  obtain ⟨-, hbd, hbb⟩ := hdec1
  refine Sim.bind_twin (x := bodies) (a₁ := a1) rfl ?_
  have hlps1 : decHL m1 lo.toNat ll.toNat = some lps := by rw [decHL_grow hg1 hlb]; exact hlps
  have hlb1 : lo.toNat + ll.toNat ≤ iwTop m1 := by have := hg1.1; omega
  -- the scoping
  refine Sim.bindK (K := tblK2 p n vis T lo ll nP C nF rs off go gl _ _) rfl (fun _ _ => rfl)
    (Sim.withFr (F := fun m2 => MFr [] [] m1 m2)
      (sctW_ok nP lo ll lps hnP (n + 1) m1 a1 _ _ bodies.toList hS1 hlps1 hlb1 hbd hbb)
      (fun _ _ e => sctW_mfr _ _ _ _ _ _ _ _ _ _ e))
    fun rs' sok m2 a2 hQ => ?_
  obtain ⟨⟨hS2, hg2, hsok, hsl⟩, hf2⟩ := hQ
  by_cases hlen0 : rb.tail.tail.headD 0 ≠ nF
  · rw [tblK2_len (h := hlen0)]; exact Sim.of_none
  have hlen : rb.tail.tail.headD 0 = nF := Decidable.of_not_not hlen0
  by_cases h10' : rs'.headD 0 ≠ 1
  · rw [tblK2_bad (h := hlen) (h1 := h10')]; exact Sim.of_none
  have h1 : rs'.headD 0 = 1 := Decidable.of_not_not h10'
  rw [tblK2_ok (h := hlen) (h1 := h1)]
  have hsz : bodies.size = nF.toNat := by
    rw [← Array.length_toList, decHL_length m1 hbd, hlen]
  have hsok' : sok = true := (sumB01 hsok hsl).1.mp h1
  subst hsok'
  simp only [hsz, and_self, ite_true]
  -- `proj_table_name`
  refine Sim.bindK (K := tblK3 p n vis T lo ll nP C nF rs off go gl _ _) rfl (fun _ _ => rfl)
    (Sim.withFr (F := fun m3 => MFr [] [] m2 m3) (sumSim_of_relW (ptF_ok dn vis fe T hT) hS2)
      (fun _ _ e => MFr.of_frame (ptF_frame e) (by simp [POOL, NSREC, NSSLOT, NNREC, NNSLOT]) (by simp))) fun rt tn m3 a3 hQ => ?_
  obtain ⟨⟨hS3, hg3, htnl, htn⟩, hf3⟩ := hQ
  subst htn
  rw [tblK3_some]
  -- `env_find`
  cases hf : envFindW m3 (rt.headD 0) vis with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨rf, m4⟩ := y
  by_cases hf0 : rf.headD 0 ≠ 0
  · rw [tblK4_found (h := hf0)]; exact Sim.of_none
  have hf0' : rf.headD 0 = 0 := Decidable.of_not_not hf0
  rw [tblK4_free (h := hf0')]
  obtain ⟨hm43, hmiss⟩ := envFindW_miss hf hS3.1.env htnl hf0'
  rw [hm43]
  simp only [hmiss, Option.isNone_none, ite_true]
  -- the three copies
  have hg13 := (hg1.trans hg2).trans hg3
  cases h5 : efW n m3 lo ll with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨rl, m5⟩ := y
  obtain ⟨hS5, hg5, hrl1, hrl0, hsl5, ht5⟩ := efW_stage n h5 hS3
    (by rw [decHL_grow hg13 hlb]; exact hlps) (by have := hg13.1; omega)
  rw [tblK5_some]
  have hg25 := (hg2.trans hg3).trans hg5
  cases h6 : efW n m5 (rb.tail.headD 0) (rb.tail.tail.headD 0) with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨rb2, m6⟩ := y
  obtain ⟨hS6, hg6, hrb1, hrb0, hsl6, ht6⟩ := efW_stage n h6 hS5
    (by rw [decHL_grow hg25 hbb]; exact hbd) (by have := hg25.1; omega)
  rw [tblK6_some]
  have hg06 := (((hg1.trans hg2).trans hg3).trans hg5).trans hg6
  cases h7 : efW n m6 go gl with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨rg, m7⟩ := y
  obtain ⟨hS7, hg7, hrg1, hrg0, hsl7, ht7⟩ := efW_stage n h7 hS6
    (by rw [decHL_grow hg06 hgb]; exact hgs) (by have := hg06.1; omega)
  rw [tblK7_some]
  -- the record
  cases h8 : erAllocW m7 14 with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨q, m8⟩ := y
  rw [tblK8_some, tblMem_eq]
  obtain ⟨hSM, hgM, hq, htM, hget⟩ := erRec_stage h8 hS7
    [6, rt.headD 0, T, rl.headD 0, rl.tail.headD 0, nP, C, nF, rs, rb2.headD 0, rb2.tail.headD 0,
      rg.headD 0, rg.tail.headD 0, off] rfl
  have hfM : MFr [] [] m7 (wrER m8 q [6, rt.headD 0, T, rl.headD 0, rl.tail.headD 0, nP, C, nF, rs,
      rb2.headD 0, rb2.tail.headD 0, rg.headD 0, rg.tail.headD 0, off]) :=
    (erAllocW_mfr h8).trans (wrER_mfr _ _ _)
  generalize hM : wrER m8 q _ = M at hSM hgM htM hget hfM
  have hPE : ∀ i < 14, (erecP M)[q.toNat + i]? = (M.arr64 EREC)[q.toNat + i]? :=
    fun i hi => erecP_getE (by simp at htM; omega)
  have he6 := IWGrow.erecPExtR (hg6.trans hg7 |>.trans hgM)
  have he7 := IWGrow.erecPExtR (hg7.trans hgM)
  have he5 := IWGrow.erecPExtR ((hg6.trans hg7).trans hgM)
  have hci := sumDecTbl (a := erecP M) (dn := dn) (q := q.toNat)
    (fun i hi => by rw [hPE i hi, hget i (by simpa using hi)]) htnl hT hC hrs
    (by rw [hrl1]; exact ArrExt.hslice? he5 hsl5) (by rw [hrb1]; exact ArrExt.hslice? he7 hsl6)
    (by rw [hrg1]; exact ArrExt.hslice? (IWGrow.erecPExtR hgM) hsl7)
  -- `env_push`
  have hq1 : (rdW (M.arr64 EREC) (q + 1)).toNat < 2 ^ 32 := by
    have h1 := hget 1 (by simp)
    have hlt : q.toNat + 1 < (M.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp (by simpa using h1)).1
    rw [rdW_of_get? (by rw [sumToNat_succ (by have := hSM.2.2.2.2.1; omega)]) (by simpa using h1)]
    simpa using htnl
  cases hc : callW p (n + 1) "env_push" [vis, q] M with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨rv, m9⟩ := y
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨M, Locals.init []⟩)
    (envPush_specW p hP.hrec (n + 1) ⟨M, Locals.init []⟩ vis q hq1) hc
  subst hs4
  obtain ⟨hS9, hg9⟩ := envPushW_ok hW4 hSM hci
  rw [tblK9_some]
  refine Sim.ret ⟨by simpa using hS9, ?_, ?_⟩
  · exact ((((((hg1.trans hg2).trans hg3).trans hg5).trans hg6).trans hg7).trans hgM).trans hg9
  · exact ((((((hf1.trans hf2).trans hf3).trans (efW_mfr h5)).trans (efW_mfr h6)).trans (efW_mfr h7)).trans
      hfM).trans (envPushW_mfr hW4)

/-! ## The `hb` memo in the memory at hand -/

/-- **The `has_loose_bvar_b` memo is well formed** (at some twin map). -/
def HbMemo (m : Mem) : Prop := ∃ mp, hbMR m mp

theorem HbMemo.fr {m m' : Mem} (h : HbMemo m) (hf : MFr [] [] m m') : HbMemo m' := by
  obtain ⟨mp, hmp⟩ := h; exact ⟨mp, hbMR_mfr hf (by simp) (by simp) hmp⟩

theorem PosMR.hbOK {m : Mem} (h : PosMR m) : HbMemo m := h.hb

/-! ## The program -/

/-- The lookups of `check_block_tables`. -/
structure TabsProg (p : Prog) : Prop where
  tbl : TblProg p
  hf : p.lookup "hb_find" = some (memoFindG hbSch)
  hput : p.lookup "hb_put" = some (memoPutG hbSch)
  hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL
  hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL
  hbp : BvbProg p
  hst : StripProg p
  hsg : p.lookup "struct_used_later_go" = some structUsedLaterGoL
  hul : p.lookup "struct_used_later_list" = some structUsedLaterListL
  hgd : p.lookup "sl_getd" = some slGetD
  hmf : p.lookup "max_find" = some maxFind
  hmp : p.lookup "max_push" = some maxPush
  him : p.lookup "intern_max" = some internMax
  hcol : p.lookup "struct_proj_guards_col" = some structProjGuardsColL
  hrow : p.lookup "struct_proj_guards_row" = some structProjGuardsRowL
  hpw : p.lookup "pin_word" = some pinWordL
  hcl : p.lookup "hb_clear" = some (memoClearG hbSch)
  hspg : p.lookup "struct_proj_guards" = some structProjGuardsL
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  one : p.lookup "check_block_tables_one" = some checkBlockTablesOne
  tabs : p.lookup "check_block_tables" = some checkBlockTables

/-! ## `struct_proj_guards` as a callee -/

theorem getDW_len0 (m : Mem) (o i d : Word) : getDW m o 0 i d = d := by simp [getDW]

theorem colW_sl0 (n : Nat) : ∀ (m : Mem) (uo ul so z j k acc : Word),
    colW n m uo ul so 0 z j k acc = colW n m uo ul 0 0 z j k acc := by
  induction n with
  | zero => intros; simp [colW]
  | succ n ih => intros; simp only [colW, getDW_len0, colK.eq_def, colK2.eq_def, ih]

theorem rowW_sl0 (n : Nat) : ∀ (m : Mem) (uo ul so z i k : Word),
    rowW n m uo ul so 0 z i k = rowW n m uo ul 0 0 z i k := by
  induction n with
  | zero => intros; simp [rowW]
  | succ n ih => intros; simp only [rowW, getDW_len0, colW_sl0, rowK1.eq_def, rowK2.eq_def, ih]

/-- With an empty sorts slice the model does not read its offset. -/
theorem spgW_sl0 (n : Nat) (m : Mem) (cty nP nF so : Word) :
    spgW n m cty nP nF so 0 = spgW n m cty nP nF 0 0 := by
  simp only [spgW, spgK1.eq_def, spgK2.eq_def, rowW_sl0]

/-- **`struct_proj_guards` as a `Sim`, keeping its memo well formed.** -/
theorem tabSimSpg {p : Prog} (hP : TabsProg p) (k : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState} (cty nP nF so sl : Word) (sorts : List LIdx)
    (hc' : H cty) (hb : nP.toNat + nF.toNat + 1 < 2 ^ 64)
    (hS : StageR dn vis fe m a) (hM : HbMemo m) (hs : decHL m so.toNat sl.toNat = some sorts)
    (hst : sl = 0 ∨ so.toNat + sl.toNat ≤ iwTop m) :
    Sim (callW p (k + 1) "struct_proj_guards" [cty, nP, nF, so, sl] m)
      (structProjGuards (decI cty) nP.toNat nF.toNat sorts) a
      (fun r gs m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some gs ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' ∧ HbMemo m') := by
  intro r m' e
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (spg_spec p hP.tbl.hv hP.hf hP.hput hP.hins hP.hgo hP.hbp hP.hst hP.hsg hP.tbl.ha hP.tbl.hc hP.tbl.hsc hP.hul
      hP.hgd hP.hmf hP.hmp hP.him hP.hcol hP.hrow hP.hpw hP.hcl hP.hspg k _ cty nP nF so sl) e
  obtain ⟨mp, hmp⟩ := hM
  have hM' : HbMemo s'.mem := spgW_hb k hc' hb hS hmp hW
  rcases hst with h0 | hst
  · subst h0
    rw [spgW_sl0] at hW
    have hs0 : sorts = [] := by simpa [decHL, hslice?] using hs.symm
    subst hs0
    obtain ⟨x, a', h1, hS', hg, hd, ht⟩ := spgW_ok k m a cty nP nF 0 0 [] mp hc' hb hS hmp
      (by simp [decHL, hslice?]) (by simp) r s'.mem hW
    exact ⟨x, a', h1, hS', hg, hd, ht, hM'⟩
  · obtain ⟨x, a', h1, hS', hg, hd, ht⟩ := spgW_ok k m a cty nP nF so sl sorts mp hc' hb hS hmp hs hst
      r s'.mem hW
    exact ⟨x, a', h1, hS', hg, hd, ht, hM'⟩

end L.Ind
