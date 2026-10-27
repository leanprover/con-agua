import ConAgua.Arena.IndPosSpec.EntryW
import ConAgua.Arena.IndPosSpec.InstW
import ConAgua.Arena.IndPosSpec.MentionsAnyGo
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# CloseTelescope: `ConRon.Arena.closeTelescope`, `ConRon.Arena.instPisWith`, `ConRon.Arena.nestBlockOf`, `ConRon.Arena.nestCtorEntry`, `ConRon.Arena.nestFrameMates.go`, `ConRon.Arena.nestFrameMates`, `ConRon.Arena.nestResHead`

The refinement theorems `nestBlockOf_refines`, `nestCtorEntry_refines`, `nestResHead_refines`, `instPisWith_refines`, `closeTelescope_refines`, `nestFrameMatesGo_refines`, `nestFrameMates_refines` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `env_find`, with: a found row decodes. -/
theorem envFind_refines' (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hp : p.lookup "env_find" = some envFindL)
    (n : Nat) (s₀ : St) {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} (vis w : Word)
    (hE : EnvR dn s₀.mem vis fe) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_find" [w, vis]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      fe.find? (decI w) = decFound dn s₀.mem (r.headD 0) (r.tail.headD 0) ∧
      (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP s₀.mem) dn (r.tail.headD 0).toNat = some ci); ⊤⦄ := by
  have key := EnvR.find?_eq hE w hw
  have key2 := EnvR.row_dec hE w hw
  simp only [invoke_eq _ hp, callFn, envFindL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, envRowGet_spec p hx hg n] <;>
      finish [decFound]

theorem blk_none {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = decFound dn m found q) (h0 : found = 0) :
    hslice? (erA m) (0 : Word).toNat (0 : Word).toNat = some (nestBlockOf fe (decI c)) := by
  have : fe.find? (decI c) = none := by rw [hfound]; simp [decFound, h0]
  simp [nestBlockOf, this, hslice?]

theorem blk_k3' {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = decFound dn m found q) (h0 : found ≠ 0)
    (hex : ∃ ci, decCI (erecP m) dn q.toNat = some ci) (hk : rdW (m.arr64 EREC) q = 3)
    (h15 : (q + 15).toNat < (m.arr64 EREC).size) (h16 : (q + 16).toNat < (m.arr64 EREC).size) :
    hslice? (erA m) ((m.arr64 EREC)[(q + 15).toNat]'h15).toNat ((m.arr64 EREC)[(q + 16).toNat]'h16).toNat =
      some (nestBlockOf fe (decI c)) := by
  have := blk_k3 found q hfound h0 hex hk
  rwa [rdW_eq _ _ _ rfl h15, rdW_eq _ _ _ rfl h16] at this

section blockof
variable (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hf : p.lookup "env_find" = some envFindL)
    (hp : p.lookup "nest_block_of" = some nestBlockOfL)
include hx hg hf hp

/-- **`nest_block_of` refines `nestBlockOf`**: the result is the `IndCaps.all` slice of `EREC`. -/
@[refines ConRon.Arena.nestBlockOf]
theorem nestBlockOf_refines (n : Nat) (s₀ : St) {dn : NIdx → Option ConLeche.Name} {fe : IFEnv}
    (vis c : Word) (hE : EnvR dn s₀.mem vis fe) (hc : c.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_block_of" [vis, c]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      hslice? (erA s₀.mem) (r.headD 0).toNat (r.tail.headD 0).toNat = some (nestBlockOf fe (decI c));
      ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestBlockOfL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_refines' p hx hg hf n (dn := dn) (fe := fe)] <;> finish (gen := 20) [blk_none, blk_nok3, blk_k3', rdW_eq]

end blockof

section census
variable (p : Prog) (hs : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip)
    (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "nest_ctor_entry" = some nestCtorEntry) (hst : StripProg p) (had : AdF p)
include hs hv hp hst had

/-- **`nest_ctor_entry` refines `nestCtorEntry`** (through the `get_app_fn` stub; L aborts where the
parameter and field counts' sum wraps, a capacity guard). -/
@[refines ConRon.Arena.nestCtorEntry]
theorem nestCtorEntry_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis C ciq : Word) (ci : IConstantInfo) (hC : H C)
    (hS : StageR dn vis fe s₀.mem a₀) (hci : decCI (erecP s₀.mem) dn ciq.toNat = some ci) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctor_entry" [C, ciq]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestCtorEntry (decI C) ci) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestCtorEntry (decI C) ci) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      EntryOut s'.mem r ciq (AM.res (ConRon.Arena.nestCtorEntry (decI C) ci) a₀); ⊤⦄ := by
  refine triple_post (nestCtorEntry_spec p hs hv hp hst had n s₀ C ciq) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := entryW_ok hC hm hS hci
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

/-- **`nest_res_head` refines `nestResHead`** (through the `get_app_fn` stub). -/
@[refines ConRon.Arena.nestResHead]
theorem nestResHead_refines (p : Prog) (hg : p.lookup "nest_res_head" = some nestResHeadL) (had : AdF p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis e : Word)
    (he : H e) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_res_head" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestResHead (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestResHead (decI e)) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      (r.headD 0 != 0) = AM.res (ConRon.Arena.nestResHead (decI e)) a₀; ⊤⦄ := by
  refine triple_post (nestResHead_spec p hg had n s₀ e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hS', hgr⟩ := resHeadW_ok dn fe vis _ _ a₀ e r he hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hgr, hres.symm⟩

section arms
variable (n : Nat) (m m1 m2 : Mem) (ao al e : Word) (v rb r : List Word)
theorem instK1_abort (h : v = []) : instK1 n m ao al v = none := by simp [instK1, h]
end arms
grind_pattern [ind_grind] instK1_abort => instK1 n m ao al v
section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "inst_pis_with" = some instPisWith) (hi1 : I1Prog p)
include hv hp hi1

/-- **`inst_pis_with` refines `instPisWith`** (no stub left). -/
@[refines ConRon.Arena.instPisWith]
theorem instPisWith_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis ao al e : Word) (args : List EIdx) (he : H e)
    (hS : StageR dn vis fe s₀.mem a₀) (hdec : decHL s₀.mem ao.toNat al.toNat = some args)
    (hb : ao.toNat + al.toNat < 2 ^ 64) (hit : ao.toNat + al.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_pis_with" [ao, al, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.instPisWith args (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.instPisWith args (decI e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decOE s'.mem r (AM.res (ConRon.Arena.instPisWith args (decI e)) a₀); ⊤⦄ := by
  refine triple_post (instPisWith_spec p hv hp hi1 n s₀ ao al e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := instW_ok n dn fe vis _ _ a₀ ao al e args r hm hS he hdec hb hit
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

section census
variable (p : Prog) (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "forall_find" = some forallFind)
  (hpp : p.lookup "forall_push" = some forallPush) (hpi : p.lookup "intern_forall" = some internForallL)
  (hmk : p.lookup "mk_forall" = some mkForall)
  (hp : p.lookup "close_telescope" = some closeTelescope) (hab : AbF p)
include hd hpf hpp hpi hmk hp hab

/-- **`close_telescope` refines `closeTelescope`** (through the `abstract1_fast` stub and master's
`mk_forall`). -/
@[refines ConRon.Arena.closeTelescope]
theorem closeTelescope_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis dO dl i body : Word) (ds : List EIdx) (hbody : H body)
    (hS : StageR dn vis fe s₀.mem a₀) (hdec : decHL s₀.mem dO.toNat dl.toNat = some ds)
    (hb : dO.toNat + dl.toNat < 2 ^ 64) (hit : dO.toNat + dl.toNat ≤ iwTop s₀.mem)
    (hib : i.toNat + dl.toNat < 2 ^ 64) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "close_telescope" [dO, dl, i, body]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.closeTelescope ds i.toNat (decI body)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.closeTelescope ds i.toNat (decI body)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decW0E s'.mem r (AM.res (ConRon.Arena.closeTelescope ds i.toNat (decI body)) a₀) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (closeTelescope_spec p hd hpf hpp hpi hmk hp hab n s₀ dO dl i body) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout, hA'⟩ :=
    closeW_ok n dn fe vis _ _ a₀ dO dl i body ds r hm hS hbody hdec hb hit hib hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout, hA'⟩

end census

end L.Ind

end

end

section


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section census
variable (p : Prog) (hc : p.lookup "sl_contains" = some slContains) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hcp : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
  (hp : p.lookup "nest_frame_mates_go" = some nestFrameMatesGoL)
include hc ha hcp hsn hp

/-- **`nest_frame_mates_go` refines `nestFrameMates.go`**: the block is an `EREC` slice, the
accumulator an `IW` slice. -/
@[refines ConRon.Arena.nestFrameMates.go]
theorem nestFrameMatesGo_refines (n : Nat) (s₀ : St) (c off l oO oL : Word) (block out : List NIdx)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hc200 : 200 < (s₀.mem.arr64 CTL).size)
    (hEs : (s₀.mem.arr64 EREC).size < 2 ^ 64) (hcH : H c)
    (hblock : hslice? (erA s₀.mem) off.toNat l.toNat = some block)
    (hout : decHL s₀.mem oO.toNat oL.toNat = some out)
    (hit : oO.toNat + oL.toNat ≤ iwTop s₀.mem) (hb : oO.toNat + oL.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_mates_go" [c, off, l, oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (ConRon.Arena.nestFrameMates.go (decI c) block out) ∧ IWGrow s₀.mem s'.mem ∧
      s'.mem.arr64 EREC = s₀.mem.arr64 EREC ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  refine triple_post (nestFrameMatesGo_spec p hc ha hcp hsn hp n s₀ c off l oO oL) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨h1, h2, h3, h4⟩ := matesW_ok n _ _ c off l oO oL block out r hm hsz hc200 hEs hcH hblock hout hit hb
  exact ⟨hl, h1, h2, h3, h4⟩

end census

theorem decHL_zero_zero {k : IdxKind} (m : Mem) : (decHL m 0 0 : Option (List (Idx k))) = some [] := by
  simp [decHL, hslice?]

section census2
variable (p : Prog) (hc : p.lookup "sl_contains" = some slContains) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hcp : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
  (hgo : p.lookup "nest_frame_mates_go" = some nestFrameMatesGoL)
  (hx : p.lookup "env_ix" = some envIxL) (hg : p.lookup "env_row_get" = some envRowGetL)
  (hf : p.lookup "env_find" = some envFindL) (hbo : p.lookup "nest_block_of" = some nestBlockOfL)
  (hp : p.lookup "nest_frame_mates" = some nestFrameMatesL)
include hc ha hcp hsn hgo hx hg hf hbo hp

/-- **`nest_frame_mates` refines `nestFrameMates`**. -/
@[refines ConRon.Arena.nestFrameMates]
theorem nestFrameMates_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis c : Word) (hcH : H c) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_frame_mates" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (ConRon.Arena.nestFrameMates fe (decI c)) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  obtain ⟨hOK1, hOK2, hOK3, hOK4, hOK5⟩ := hS.2
  have hE := hS.1.env
  simp only [invoke_eq _ hp, callFn, nestFrameMatesL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      nestBlockOf_refines p hx hg hf hbo n (dn := dn) (fe := fe),
      nestFrameMatesGo_refines p hc ha hcp hsn hgo n (block := ConRon.Arena.nestBlockOf fe (decI c)) (out := [])] <;> finish (gen := 20) [ConRon.Arena.nestFrameMates, decHL_zero_zero]

end census2

end L.Ind

end

end
