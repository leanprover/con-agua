module

public import ConAgua.Arena.IndT.BlockC
public import ConAgua.Arena.IndDeclConstsFrame
public import ConAgua.Arena.IndDeclConstsTable
public import ConAgua.Arena.CoreCaches
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.RecGenSpec.FlushStage
import ConAgua.Arena.ScratchRefine
import ConAgua.Checker.NoVerdictTree

@[expose] public section

/-!
# `check_block`'s callees' contracts: the ones outside the checks (lane `ronsync2`, stage 3)

`flush_caches` (`flushCaches_spec`, `flush_stage`, con-ron's `ReadOK.flush`), `block_recs`
(`brsW_ok`) and `block_tables` (`btsW_ok`); their memos by the stream index's write set
(`dc_keep`, `dc0_keepI1`: both are in `decl_constants`/`decl_tables`' closure).
-/

noncomputable section

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

section contracts
variable {G : Prop} {p : Prog} {dn : NIdx → Option ConLeche.Name}

/-- `BkMem` from the stream index's memos and `I1Memo`. -/
theorem BkMem.ofDc {m : Mem} (h : DcMem m) (hi : I1Memo m) : BkMem m :=
  ⟨⟨h.stage, hi, h.cr⟩, h.core, ⟨h.ab, hi, L.Stubs.CrOK.crMemo h.cr, h.il, h.wk⟩⟩

theorem BkMem.dc {m : Mem} (h : BkMem m) : DcMem m :=
  ⟨h.core, h.ind.stage, h.ind.cr, h.abs.ab, h.abs.il, h.abs.wk⟩

/-- **`flush_caches`' contract.** -/
theorem flushRefS_of (hF : FlushProg p) (hGnv : G → closedNV p _root_.L.Checker.nvFns = true) :
    FlushRefS G p dn := by
  intro n vis fe env m a hB
  rcases c : callE p n "flush_caches" [] m with e | ⟨r, m'⟩
  · exact fun hG => ErrClaim.of_callE_nv (hGnv hG) (_root_.L.Checker.nv_mem (by decide +kernel)) c
  obtain ⟨s', rfl, -, hfok, hfm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (flushCaches_spec p hF n _) (callW_of_callE c)
  simp only at hfok hfm
  obtain ⟨cf, i1, -⟩ := ConRon.Bridge.Inductives.ReadOK.flush hB.c.check.toR
    (show ConRon.Arena.flushCaches a = .ok ((), { a with caches := Caches.empty }) from rfl)
  obtain ⟨hS', hg⟩ := flush_stage hB.c.stage hfok
  rw [← hfm] at hS' hg
  have hA' : AbsOK s'.mem := by
    rw [hfm]; exact AFr.of_frame (flushMem_frame m) (by decide) (by decide) hB.abs
  have hI' : IndMemos s'.mem := by
    rw [hfm]
    exact hB.ind.frame (flushMem_frame m) (by simp) (fun x hx => by
      have := flushCtl_lt x hx; have := flushCtl_ge x hx; omega)
  exact ⟨(), _, rfl, ⟨StageC.of_check hB.c hS' hA' cf (ConRon.Arena.Ext.refl _), hI', hA'⟩, hg, i1⟩

theorem dcF_brs : "block_recs" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dc0F_brs : "block_recs" ∈ dc0Fns := List.elem_iff.mp (by decide)
theorem dcF_btsC : "block_tables" ∈ dcFns := List.elem_iff.mp (by decide)

/-- **`block_recs`' contract** (`brsW_ok`). -/
theorem brRefS_of (hP : RecsProg p) (hL : DcLeafProg p)
    (hGnv : G → closedNV p _root_.L.Checker.nvFns = true) : BrRefS G p := by
  intro n vis fe m a pp ro rl bs rcs hS hM hq hrcs
  rcases c : callE p n "block_recs" [pp, ro, rl] m with e | ⟨r, m'⟩
  · exact fun hG => ErrClaim.of_callE_nv (hGnv hG) (_root_.L.Checker.nv_mem (by decide +kernel)) c
  have d := callW_of_callE c
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (dbrs_spec hP n _ pp ro rl) d
  obtain ⟨cis, a', hrun, hd, hb, hS', hg⟩ := brsW_ok hP pp bs vis fe n m s'.mem a ro rl rcs r hS hq hrcs hW
  obtain ⟨hDM, -⟩ := dc_keep hL dcF_brs d hM.dc
  exact ⟨cis, a', hrun, hS', BkMem.ofDc hDM (dc0_keepI1 hL dc0F_brs d hM.ind.i1), hg, hd, hb⟩

/-- **`block_tables`' contract** (`btsW_ok`). -/
theorem btRefS_of (hP : TablesProg p) (hL : DcLeafProg p)
    (hGnv : G → closedNV p _root_.L.Checker.nvFns = true) : BtRefS G p := by
  intro n vis fe m a pp mo ml bs mss hS hM hnP hq hmss
  rcases c : callE p n "block_tables" [pp, mo, ml] m with e | ⟨r, m'⟩
  · exact fun hG => ErrClaim.of_callE_nv (hGnv hG) (_root_.L.Checker.nv_mem (by decide +kernel)) c
  have d := callW_of_callE c
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (bts_spec hP n _ pp mo ml) d
  obtain ⟨ts, a', hrun, hd, hb, hS', hg, hA'⟩ := btsW_ok hP pp bs vis fe (by omega) n m s'.mem a mo ml mss r
    hS hM.abs hq hmss hW
  obtain ⟨hDM, -⟩ := dc_keep hL dcF_btsC d hM.dc
  exact ⟨ts, a', hrun, hS', BkMem.ofDc hDM hA'.i1, hg, hd, hb⟩

end contracts

end L.Ind

end
