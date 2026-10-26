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


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_struct_proj_table`, keeping the memos -/

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
