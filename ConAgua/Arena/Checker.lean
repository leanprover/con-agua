import ConAgua.Arena.DeclCheckLoop
import ConAgua.Arena.CheckerL
import ConAgua.Arena.PromoteCIRef.PromoteNew
import ConAgua.Arena.DeclAndPin
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

/-!
# The declaration loop in L, top down: `installFold`, `checkPendingList`

The twin's two-phase fold (`vendor/con-ron/ConRon/Arena/Checker.lean`): phase A installs every
declaration record (`installFold` → `installDeclStep` → `installStep`, the per-declaration
bracket `flushCaches; enterScratch; installStepGo; promote…; dropScratch`), recording the value
groups to check; phase B checks each against the prefix view it was installed at
(`checkPendingList` → `checkPending`). This file has that structure in L, with the callees that
are not translated yet as **stubs** (L bodies `abort`, no census tags) whose refinement specs are
stated here and proved with `sorry` (each listed in DESIGN.md). The skeleton functions are real L
code; their refinements are proved from the stub specs and tagged `@[refines …]`, so the census
counts the skeleton as proven with `sorry` (the stub specs). A refinement modulo `sorry` gives its
callees no coverage (scripts/census.py), so the targets below `installFold` keep their own status.
The L functions themselves are in `Arena/CheckerL.lean`. The twin's `installThenCheck` has no L function: the entries run the two phases separately
(`check_a` calls `install_fold_go`, `check_b` calls `check_pending_go`, `Checker/Entry.lean`).

* The declarations are the front's records (`DECL`/`DLP`, `DeclsF`, `Front/StateDR.lean`); record
  `i` is the fold position `i`.
* The pending checks are `PEND` (137), three words each (the value group's record pointer in
  `EREC`, `pos`, `vis`), `CTL[130]` of them: `PendR`.
* Errors: the twin's error results (`.error (e, i)`) are `abort` (L recovers nowhere; a reject or
  decline site aborts with the twin's message as its reason, `Arena/Reasons.lean`); a returning run
  is an accepting one.
* The relation the loop keeps, `LoopR`: `CheckR` (arena, caches, pins, the environment at a view),
  `PendR` and `DeclsF`.
* The bracket (`flush_caches`, `scratch_enter`, `scratch_drop`) is lane `whnf`'s real code,
  lifted to `LoopR` here (`flush_loop`, `enter_loop`, `drop_loop`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Front (DECL DLP DeclsF)

/-- The translated callees of the loop (`Decl*.lean`), as program lookups. -/
structure DeclCallees (dn : NIdx → Option ConLeche.Name) (p : Prog) : Prop where
  and_pin_ok : p.lookup "and_pin_ok" = some andPinOkL
  /-- `check_value_group`'s text (its write set, `DeclCvg.lean`). -/
  cvg : CvgProg p
  /-- `install_step_go`'s body and `install_value`'s text (`DeclStepGo.lean`). -/
  istg : IstgProg p
  iv : IvProg p
  /-- `check_decl`, its arms and their texts (`DeclCheckLoop.lean`). -/
  cd : CheckDeclProg p
  /-- The name decoding is injective (the comparisons of constant records read `PropWhen`'s names
  through it); the top level's `dn` is the store's `denoteN`. -/
  dninj : L.Ind.DnInj dn

section stubs
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-! ## The stubs and their specs

Each stub is a not-yet-translated callee; the spec is what the real code will have to prove. -/

/-- The promotion's two entries are `Promote.lean`'s `promote_vg(g, vis)` and
`promote_new(k, kt, vis, fresh)` (program: `PromoteProg`). `promote_vg` refines `promoteVG
PMemo.empty coreWalkFuel` under the loop's relation (`PromoteRecRef.lean`'s `vg_rel`). -/
@[refines ConRon.Arena.promoteVG]
theorem promoteVG_spec (hpr : PromoteProg p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (g : Word) (vg : ValueGroup), decVG (erecP s₀.mem) g.toNat = some vg →
      LoopR pins dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "promote_vg" [g, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (promoteVG PMemo.empty coreWalkFuel vg) a₀ ∧
      LoopR pins dn s'.mem (AM.st (promoteVG PMemo.empty coreWalkFuel vg) a₀) vis fe pend ds ∧
      PMemoR s'.mem (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).1 ∧
      decVG (erecP s'.mem) (r.headD 0).toNat =
        some (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).2; ⊤⦄ := by
  intro n s₀ a₀ vis fe pend g vg hvg hR
  refine triple_post (callW_spec p n "promote_vg" [g, vis] s₀) fun r s' ⟨hl, hc⟩ => ?_
  obtain ⟨pm₀, hP⟩ := hR.pmemo
  obtain ⟨hiw1, hiw2, hiw3, hiw4, hiw5⟩ := hR.iw
  obtain ⟨a', pm', vg', hrun, hD, hP', hdec, hg, hts, hcp, hf, htk⟩ :=
    vg_rel p hpr n s₀.mem a₀ pm₀ g vis vg r s'.mem hR.check.arena hP hvg hiw4 hc
  have hok : AM.ok (promoteVG PMemo.empty coreWalkFuel vg) a₀ := by simp [AM.ok, hrun]
  have hst : AM.st (promoteVG PMemo.empty coreWalkFuel vg) a₀ = a' := by simp [AM.st, hrun]
  have hres : AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀ = (pm', vg') := by
    simp [AM.res, hrun]
  rw [hst, hres]
  have hcA : a'.caches = a₀.caches := congrArg Prod.fst hcp
  have hpA : a'.pins = a₀.pins := congrArg Prod.snd hcp
  have hA := vg_arrs
  have hC := vg_ctl
  have hIW : s'.mem.arr64 L.Ind.IW = s₀.mem.arr64 L.Ind.IW :=
    hf.1 _ (fun h => by have := hA _ h; revert this; decide) (by decide)
  refine ⟨hl, hok, ⟨⟨hD, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ⟨pm', hP'⟩, ?_⟩, hP', hdec⟩
  · rw [hcA]
    exact hR.check.core.frame (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
      (fun x hx => by have := hC x hx; omega) hf
  · rw [hpA]
    exact hR.check.pins.frame (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega) hf
  · exact hR.check.env.grow (fun b h1 h2 h3 => hf.1 b (fun h => by
        have := hA b h; simp only [ArrId] at *; omega)
      (by simp only [CTL, ArrId]; omega)) (hf.2.1 128 (fun h => by have := hC _ h; simp at this))
      hg (TblSame.of_frame (fun b hb => by have := hA b hb; simp only [ArrId] at *; omega)
        (fun b hb => by have := hA b hb; simp only [ArrId] at *; omega)
        (fun h => by have := hA _ h; simp only [ETAB, ArrId] at *; omega)
        (fun h => by have := hC _ h; simp at this) hf)
  · exact ModeOK.of_keep hR.check.mode (hf.2.1 1 (by decide)) htk
  · exact hR.pend.ext (hf.1 _ (fun h => by have := hA _ h; revert this; decide) (by decide))
      (hf.2.1 130 (fun h => by have := hC _ h; simp at this)) hg.ext
  · rw [hf.1 DECL (fun h => by have := hA _ h; revert this; decide) (by decide),
      hf.1 DLP (fun h => by have := hA _ h; revert this; decide) (by decide)]
    exact hR.decls
  · refine ⟨?_, hts, ?_, by rw [hf.2.2.1]; exact hiw4, by rw [hf.2.2.1]; exact hiw5⟩
    · simp only [L.Ind.iwTop, hIW]
      rw [hf.2.1 200 (fun h => by have := hC _ h; simp at this)]; exact hiw1
    · rw [hIW]; exact hiw3
  · exact PinSetsR.grow hR.pinsets ⟨hg.1, hg.2.1⟩
      (hf.2.1 150 (fun h => by have := hC _ h; simp at this))
      (hf.2.1 151 (fun h => by have := hC _ h; simp at this))

/-- `tbl_grown(nt)` under the loop's relation: the tables list's length minus `nt`. -/
theorem tblGrown_loop (hpr : PromoteProg p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (nt : Word), LoopR pins dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "tbl_grown" [nt]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      (r.headD 0).toNat = fe.env.tables.length - nt.toNat; ⊤⦄ := by
  intro n s₀ a₀ vis fe pend nt hR
  refine triple_post (tblGrown_spec p hpr n s₀ nt) fun r s' ⟨h1, h2, h3⟩ => ⟨h1, h2, ?_⟩
  rw [h3, hR.check.env.tables_length]

theorem promoteNew_spec (hpr : PromoteProg p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (k kt fresh : Word) (pm : PMemo), (if fresh = 0 then PMemoR s₀.mem pm else pm = PMemo.empty) →
      LoopR pins dn s₀.mem a₀ vis fe pend ds → k.toNat ≤ vis.toNat →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "promote_new" [k, kt, vis, fresh]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (promoteNew pm coreWalkFuel k.toNat kt.toNat fe) a₀ ∧
      LoopR pins dn s'.mem (AM.st (promoteNew pm coreWalkFuel k.toNat kt.toNat fe) a₀) vis
        (AM.res (promoteNew pm coreWalkFuel k.toNat kt.toNat fe) a₀).2 pend ds; ⊤⦄ := by
  intro n s₀ a₀ vis fe pend k kt fresh pm hpm hR hk
  refine triple_post (callW_spec p n "promote_new" [k, kt, vis, fresh] s₀) fun r s' ⟨hl, hc⟩ => ?_
  obtain ⟨a', pm', fe', hrun, hLoop⟩ :=
    promoteNew_rel p hpr dn n s₀.mem a₀ pm k kt vis fresh fe pend ds r s'.mem hpm hR hk hc
  have hok : AM.ok (promoteNew pm coreWalkFuel k.toNat kt.toNat fe) a₀ := by simp [AM.ok, hrun]
  have hst : AM.st (promoteNew pm coreWalkFuel k.toNat kt.toNat fe) a₀ = a' := by simp [AM.st, hrun]
  have hres : AM.res (promoteNew pm coreWalkFuel k.toNat kt.toNat fe) a₀ = (pm', fe') := by
    simp [AM.res, hrun]
  rw [hst, hres]
  exact ⟨hl, hok, hLoop⟩

end stubs

/-! ## The bracket: lane `whnf`'s `flush_caches`, `scratch_enter`, `scratch_drop` under `LoopR`

They refine `flushCaches`/`enterScratch`/`dropScratch` under `CheckR` (`CoreRefine.lean`,
`ScratchRefine.lean`) and write `CTL` words below 128 only, so the pending checks and the
declaration records ride along. -/

/-- The bracket's functions in a program. -/
structure BracketProg (p : Prog) : Prop where
  fl : FlushProg p
  se : p.lookup "scratch_enter" = some scratchEnter
  sd : p.lookup "scratch_drop" = some scratchDrop
  sr : p.lookup "scratch_reset" = some scratchReset
  bm : p.lookup "bm_clear" = some (memoClearG bmSch)
  lf : p.lookup "lf_clear" = some (memoClearG lfSch)
  im : p.lookup "if_clear" = some (memoClearG imSch)
  fm : p.lookup "fm_clear" = some (memoClearG frSch)
  /-- The promotion (`promote_vg`, `promote_new` and their callees). -/
  pr : PromoteProg p

theorem PendR.frameLo {m m' : Mem} {pend : Array PendingCheck} {C : List Word}
    (hf : MemFrame scrArrs C m m') (hC : ∀ x ∈ C, x.toNat < 128) (h : PendR m pend) : PendR m' pend := by
  have hP : m'.arr64 PEND = m.arr64 PEND := hf.1 _ (by decide) (by decide)
  have hE : erecP m' = erecP m := erecP_congr (hf.1 _ (by decide) (by decide))
    (hf.2.1 129 (fun h' => by have := hC _ h'; simp at this))
  have hc : rdW (m'.arr64 CTL) 130 = rdW (m.arr64 CTL) 130 :=
    hf.2.1 130 (fun h' => by have := hC _ h'; simp at this)
  refine ⟨by simp only [pendCount, hc]; exact h.count, fun j hj => ?_,
    by simp only [pendCount, hc]; exact h.bound⟩
  rw [← h.recs j hj]; simp only [decPend, hP, hE]

theorem LoopR.of_lo {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration} {C : List Word}
    (h : LoopR pins dn m a vis fe pend ds) (hC' : CheckR dn m' a' vis fe) (hf : MemFrame scrArrs C m m')
    (hC : ∀ x ∈ C, x.toNat < 128) : LoopR pins dn m' a' vis fe pend ds := by
  have h1 : m'.arr64 DECL = m.arr64 DECL := hf.1 _ (by decide) (by decide)
  have h2 : m'.arr64 DLP = m.arr64 DLP := hf.1 _ (by decide) (by decide)
  exact ⟨hC', h.pend.frameLo hf hC, by rw [h1, h2]; exact h.decls,
    IWOK.frame hf (by decide) (by decide) (fun h' => by have := hC _ h'; simp at this)
      (fun h' => by have := hC _ h'; simp at this) h.iw,
    h.pmemo.imp fun _ hp => hp.frame (by decide) (fun x hx => .inl (by have := hC x hx; omega)) hf,
    PinSetsR.grow h.pinsets (RecGrow.of_eq (hf.1 _ (by decide) (by decide))
        (hf.2.1 129 (fun h' => by have := hC _ h'; simp at this)))
      (hf.2.1 150 (fun h' => by have := hC _ h'; simp at this))
      (hf.2.1 151 (fun h' => by have := hC _ h'; simp at this))⟩

section bracket
variable (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration) (p : Prog)
  (hb : BracketProg p)
include hb

theorem flush_loop {pins : List INatOpPinSet} (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "flush_caches" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok flushCaches a₀ ∧
      LoopR pins dn s'.mem (AM.st flushCaches a₀) vis fe pend ds; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hC⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (flushCaches_refinesC p hb.fl a₀ n s₀ dn vis fe hR.check)
  obtain ⟨-, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun (flushCaches_spec p hb.fl n s₀)
  subst hs
  exact ⟨hloc, hok, hR.of_lo hC (by rw [hm]; exact (flushMem_frame _).mono (by simp) (by simp))
    flushCtl_lt⟩

theorem enter_loop {pins : List INatOpPinSet} (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "scratch_enter" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok enterScratch a₀ ∧
      LoopR pins dn s'.mem (AM.st enterScratch a₀) vis fe pend ds; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hC⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchEnter_refinesC p hb.se hb.sr hb.bm hb.lf hb.im hb.fm a₀ n s₀ dn vis fe hR.check)
  obtain ⟨-, -, -, -, -, -, -, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchEnter_spec p hb.se hb.sr hb.bm hb.lf hb.im hb.fm n s₀)
  subst hs
  exact ⟨hloc, hok, hR.of_lo hC (by rw [hm]; exact enterMem_frame _)
    (fun x h => Nat.lt_trans (resetCtl_lt x h) (by decide))⟩

theorem drop_loop {pins : List INatOpPinSet} (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "scratch_drop" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok dropScratch a₀ ∧
      LoopR pins dn s'.mem (AM.st dropScratch a₀) vis fe pend ds; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hC⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchDrop_refinesC p hb.sd hb.sr hb.fl a₀ n s₀ dn vis fe hR.check)
  obtain ⟨-, -, -, -, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchDrop_spec p hb.sd hb.sr hb.fl n s₀)
  subst hs
  have hf : MemFrame scrArrs (flushCtl ++ (0 :: resetCtl)) s.mem s'.mem := by
    rw [hm]
    exact ((flushMem_frame _).mono (by simp) (fun x h => List.mem_append_left _ h)).trans
      ((resetMemP_frame _ 0).mono (by simp) (fun x h => List.mem_append_right _ h))
  refine ⟨hloc, hok, hR.of_lo hC hf fun x h => ?_⟩
  rcases List.mem_append.mp h with h | h
  · exact flushCtl_lt x h
  · exact Nat.lt_trans (resetCtl_lt x (List.mem_append_left _ h)) (by decide)

end bracket

theorem LoopR.restrict {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (h : LoopR pins dn m a vis fe pend ds) (v : Word) : LoopR pins dn m a v (fe.restrictTo v.toNat) pend ds :=
  ⟨⟨h.check.arena, h.check.core, h.check.pins, h.check.env.restrictTo v, h.check.mode⟩, h.pend, h.decls, h.iw,
    h.pmemo, h.pinsets⟩

theorem LoopR.unrestrict {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {v vis : Word}
    {fe : IFEnv} {k : Nat} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (h : LoopR pins dn m a v (fe.restrictTo k) pend ds) (hv : fe.visibleBelow = vis.toNat) :
    LoopR pins dn m a vis fe pend ds := by
  have := h.restrict vis
  have e : (fe.restrictTo k).restrictTo vis.toNat = fe := by
    cases fe; simp only [IFEnv.restrictTo] at hv ⊢; rw [hv]
  rwa [e] at this

/-- Pending check `j` (a plain function, as `dsAt`). -/
def pdAt (pend : Array PendingCheck) (j : Word) : PendingCheck := pend.getD j.toNat default

/-- The pending checks after pushing `(g, i, vis)`. -/
def pendPushMem (m : Mem) (g i vis : Word) : Mem :=
  let c := rdW (m.arr64 CTL) 130
  (((m.set64 PEND (3 * c) g).set64 PEND (3 * c + 1) i).set64 PEND (3 * c + 2) vis).set64 CTL 130
    (c + 1)

theorem pendPushMem_frame (m : Mem) (g i v : Word) : MemFrame [PEND] [130] m (pendPushMem m g i v) := by
  simp only [pendPushMem]
  have fP : ∀ (m₁ : Mem) (k x : Word), MemFrame [PEND] [130] m₁ (m₁.set64 PEND k x) :=
    fun m₁ k x => MemFrame.mono (MemFrame.set64 m₁ PEND (by decide) k x) (by simp) (by simp)
  have fC : ∀ (m₁ : Mem) (x : Word), MemFrame [PEND] [130] m₁ (m₁.set64 CTL 130 x) :=
    fun m₁ x => MemFrame.mono (MemFrame.setCtl m₁ 130 x) (by simp) (by simp)
  exact (((fP _ _ _).trans (fP _ _ _)).trans (fP _ _ _)).trans (fC _ _)

/-- Pushing a pending check keeps the promotion memo (`PEND`, `CTL[130]` are not its). -/
theorem PMemoR.pendPush {m : Mem} {pm : PMemo} (h : PMemoR m pm) (g i v : Word) :
    PMemoR (pendPushMem m g i v) pm :=
  h.frame (by simp; decide) (by simp) (pendPushMem_frame m g i v)

theorem LoopR.vis {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {v : Word}
    {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (h : LoopR pins dn m a v fe pend ds) : fe.visibleBelow = v.toNat := h.check.env.vis

/-- **Pushing a pending check** keeps the loop's relation. -/
theorem LoopR.pendPush {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (h : LoopR pins dn m a vis fe pend ds) (g i v : Word) (vg : ValueGroup)
    (hg : decVG (erecP m) g.toNat = some vg)
    (hb : 3 * (rdW (m.arr64 CTL) 130).toNat + 2 < (m.arr64 PEND).size)
    (hc : 130 < (m.arr64 CTL).size) (h1 : (rdW (m.arr64 CTL) 130).toNat < 2 ^ 62) :
    LoopR pins dn (pendPushMem m g i v) a vis fe (pend.push ⟨vg, i.toNat, v.toNat⟩) ds := by
  have hc' := h.pend.count
  simp only [pendCount] at hc'
  generalize hcw : rdW (m.arr64 CTL) 130 = c at hb h1 hc'
  have hf : MemFrame [PEND] [130] m (pendPushMem m g i v) := by
    simp only [pendPushMem, hcw]
    have fP : ∀ (m₁ : Mem) (k x : Word), MemFrame [PEND] [130] m₁ (m₁.set64 PEND k x) :=
      fun m₁ k x => MemFrame.mono (MemFrame.set64 m₁ PEND (by decide) k x) (by simp) (by simp)
    have fC : ∀ (m₁ : Mem) (x : Word), MemFrame [PEND] [130] m₁ (m₁.set64 CTL 130 x) :=
      fun m₁ x => MemFrame.mono (MemFrame.setCtl m₁ 130 x) (by simp) (by simp)
    exact (((fP _ _ _).trans (fP _ _ _)).trans (fP _ _ _)).trans (fC _ _)
  have hE : erecP (pendPushMem m g i v) = erecP m := erecP_congr (hf.1 _ (by decide) (by decide))
    (hf.2.1 129 (by decide))
  have hD1 : (pendPushMem m g i v).arr64 DECL = m.arr64 DECL := hf.1 _ (by decide) (by decide)
  have hD2 : (pendPushMem m g i v).arr64 DLP = m.arr64 DLP := hf.1 _ (by decide) (by decide)
  have hc1 : (c + 1).toNat = c.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have h30 : (3 * c).toNat = 3 * c.toNat := by rw [UInt64.toNat_mul]; simp; omega
  have h31 : (3 * c + 1).toNat = 3 * c.toNat + 1 := by
    rw [UInt64.toNat_add, h30]; simp; omega
  have h32 : (3 * c + 2).toNat = 3 * c.toNat + 2 := by
    rw [UInt64.toNat_add, h30]; simp; omega
  have hP : (pendPushMem m g i v).arr64 PEND =
      (((m.arr64 PEND).set! (3 * c.toNat) g).set! (3 * c.toNat + 1) i).set! (3 * c.toNat + 2) v := by
    simp only [pendPushMem, hcw, Mem.arr64_set64_ne _ _ _ _ _ (show PEND ≠ CTL by decide),
      Mem.arr64_set64_same, h30, h31, h32]
  have hC : (pendPushMem m g i v).arr64 CTL = (m.arr64 CTL).set! 130 (c + 1) := by
    simp only [pendPushMem, hcw, Mem.arr64_set64_same,
      Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ PEND by decide)]
    rfl
  have hcnt : pendCount (pendPushMem m g i v) = c.toNat + 1 := by
    simp only [pendCount, hC, rdW_set!]
    simp [hc, hc1]
  refine ⟨h.check.frame_hi (by decide) (by simp) hf, ⟨?_, ?_, by rw [hcnt]; omega⟩,
    by rw [hD1, hD2]; exact h.decls,
    IWOK.frame hf (by decide) (by decide) (by decide) (by decide) h.iw,
    h.pmemo.imp fun _ hp => hp.pendPush g i v,
    PinSetsR.grow h.pinsets (RecGrow.of_eq (hf.1 _ (by decide) (by decide)) (hf.2.1 129 (by decide)))
      (hf.2.1 150 (by decide)) (hf.2.1 151 (by decide))⟩
  · rw [hcnt, hc']; simp
  · intro j hj
    simp only [Array.size_push] at hj
    simp only [decPend, hP, hE, nat?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hjs : j < pend.size
    · have := h.pend.recs j hjs
      simp only [decPend, nat?] at this
      simp only [Array.getElem_push, hjs, dite_true]
      rw [← this]
      have e1 : ¬ 3 * c.toNat + 2 = 3 * j := by omega
      have e2 : ¬ 3 * c.toNat + 1 = 3 * j := by omega
      have e3 : ¬ 3 * c.toNat = 3 * j := by omega
      have e4 : ¬ 3 * c.toNat + 2 = 3 * j + 1 := by omega
      have e5 : ¬ 3 * c.toNat + 1 = 3 * j + 1 := by omega
      have e6 : ¬ 3 * c.toNat = 3 * j + 1 := by omega
      have e7 : ¬ 3 * c.toNat + 2 = 3 * j + 2 := by omega
      have e8 : ¬ 3 * c.toNat + 1 = 3 * j + 2 := by omega
      have e9 : ¬ 3 * c.toNat = 3 * j + 2 := by omega
      simp [e1, e2, e3, e4, e6, e9]
    · have hj' : j = pend.size := by omega
      subst hj'
      simp only [Array.getElem_push, Nat.lt_irrefl, dite_false, ← hc']
      have : 3 * c.toNat + 2 < (m.arr64 PEND).size := hb
      simp [this, show 3 * c.toNat < (m.arr64 PEND).size by omega,
        show 3 * c.toNat + 1 < (m.arr64 PEND).size by omega, hg]

@[simp] theorem exc_ok_bind {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

section twin
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet)

/-- `installStep`'s `none` arm, named (`nt` the table count before the step). -/
def isNoneT (vis nt : Nat) (fe' : IFEnv) (pend : Array PendingCheck) :
    AM (IFEnv × Array PendingCheck) := do
  let r ← promoteNew PMemo.empty coreWalkFuel (fe'.visibleBelow - vis)
    (fe'.env.tables.length - nt) fe'
  dropScratch
  pure (r.2, pend)

/-- `installStep`'s `some` arm, named. -/
def isSomeT (i vis nt : Nat) (fe' : IFEnv) (pend : Array PendingCheck) (vg : ValueGroup) :
    AM (IFEnv × Array PendingCheck) := do
  let r ← promoteVG PMemo.empty coreWalkFuel vg
  let r2 ← promoteNew r.1 coreWalkFuel (fe'.visibleBelow - vis) (fe'.env.tables.length - nt) fe'
  dropScratch
  pure (r2.2, pend.push ⟨r.2, i, vis⟩)

/-- `installStep` after `installStepGo`, named. -/
def installStepK (i vis nt : Nat) (pend : Array PendingCheck) (r : IFEnv × Option ValueGroup) :
    AM (IFEnv × Array PendingCheck) :=
  match r.2 with
  | none => isNoneT vis nt r.1 pend
  | some vg => isSomeT i vis nt r.1 pend vg

theorem installStep_eq (i : Nat) (fe : IFEnv) (pend : Array PendingCheck) (pd : IDeclaration) :
    installStep mode pins i fe pend pd = (do
      flushCaches
      enterScratch
      let r ← installStepGo mode pins fe pd
      installStepK i fe.visibleBelow fe.env.tables.length pend r) := by
  simp only [installStep, installStepK, isNoneT, isSomeT]; rfl

theorem installStepK_none (i v nt : Nat) (pend : Array PendingCheck) (r : IFEnv × Option ValueGroup)
    (h : r.2 = none) : installStepK i v nt pend r = isNoneT v nt r.1 pend := by
  simp [installStepK, h]

theorem installStepK_some (i v nt : Nat) (pend : Array PendingCheck) (r : IFEnv × Option ValueGroup)
    (vg : ValueGroup) (h : r.2 = some vg) : installStepK i v nt pend r = isSomeT i v nt r.1 pend vg := by
  simp [installStepK, h]

/-- `installStep` from its pieces, in `AM.ok`/`AM.st`/`AM.res` terms. -/
theorem installStep_ok (i : Nat) (fe : IFEnv) (pend : Array PendingCheck) (pd : IDeclaration)
    (a0 : AState) (h1 : AM.ok flushCaches a0) (h2 : AM.ok enterScratch (AM.st flushCaches a0))
    (h3 : AM.ok (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0))) (h4 : AM.ok (installStepK i fe.visibleBelow fe.env.tables.length pend (AM.res (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0)))) (AM.st (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0)))) :
    AM.ok (installStep mode pins i fe pend pd) a0 ∧ AM.st (installStep mode pins i fe pend pd) a0 = AM.st (installStepK i fe.visibleBelow fe.env.tables.length pend (AM.res (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0)))) (AM.st (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0))) ∧ AM.res (installStep mode pins i fe pend pd) a0 = AM.res (installStepK i fe.visibleBelow fe.env.tables.length pend (AM.res (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0)))) (AM.st (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0))) := by
  have r1 := AM.run_of_ok _ _ h1
  have r2 := AM.run_of_ok _ _ h2
  have r3 := AM.run_of_ok _ _ h3
  have r4 := AM.run_of_ok _ _ h4
  apply AM.of_run_ok
  rw [installStep_eq]
  simp only [StateT.run_bind, exc_ok_bind, r1, r2, r3, r4]

/-- `installDeclStep` from its pieces (the `And` pin passed, the step went through). -/
theorem installDeclStep_ok (p : Nat × IFEnv × Array PendingCheck) (pd : IDeclaration) (a0 : AState)
    (h1 : AM.ok (andPinOk pd) a0) (hb : AM.res (andPinOk pd) a0 = true)
    (h2 : AM.ok (installStep mode pins p.1 p.2.1 p.2.2 pd) (AM.st (andPinOk pd) a0)) :
    AM.ok (installDeclStep mode pins p pd) a0 ∧ AM.st (installDeclStep mode pins p pd) a0 = AM.st (installStep mode pins p.1 p.2.1 p.2.2 pd) (AM.st (andPinOk pd) a0) ∧
    AM.res (installDeclStep mode pins p pd) a0 = .ok (p.1 + 1, (AM.res (installStep mode pins p.1 p.2.1 p.2.2 pd) (AM.st (andPinOk pd) a0)).1, (AM.res (installStep mode pins p.1 p.2.1 p.2.2 pd) (AM.st (andPinOk pd) a0)).2) := by
  have r1 := AM.run_of_ok _ _ h1
  rw [hb] at r1
  have r2 := AM.run_of_ok _ _ h2
  apply AM.of_run_ok
  simp only [installDeclStep, StateT.run] at r1 r2 ⊢
  rw [r1]; simp only; rw [r2]

/-- `installFold` past a successful step. -/
theorem installFold_cons (p p' : Nat × IFEnv × Array PendingCheck) (d : IDeclaration)
    (rest : List IDeclaration) (a0 : AState)
    (h1 : AM.ok (installDeclStep mode pins p d) a0)
    (hr : AM.res (installDeclStep mode pins p d) a0 = .ok p') :
    (installFold mode pins p (d :: rest)).run a0 =
      (installFold mode pins p' rest).run (AM.st (installDeclStep mode pins p d) a0) := by
  have r1 := AM.run_of_ok _ _ h1
  rw [hr] at r1
  simp only [installFold, StateT.run_bind, r1, exc_ok_bind]

theorem installFold_cons_ok (p p' : Nat × IFEnv × Array PendingCheck) (d : IDeclaration)
    (rest : List IDeclaration) (a0 : AState)
    (h1 : AM.ok (installDeclStep mode pins p d) a0)
    (hr : AM.res (installDeclStep mode pins p d) a0 = .ok p')
    (h2 : AM.ok (installFold mode pins p' rest) (AM.st (installDeclStep mode pins p d) a0)) :
    AM.ok (installFold mode pins p (d :: rest)) a0 ∧
    AM.st (installFold mode pins p (d :: rest)) a0 =
      AM.st (installFold mode pins p' rest) (AM.st (installDeclStep mode pins p d) a0) ∧
    AM.res (installFold mode pins p (d :: rest)) a0 =
      AM.res (installFold mode pins p' rest) (AM.st (installDeclStep mode pins p d) a0) := by
  have e := installFold_cons mode pins p p' d rest a0 h1 hr
  have r2 := AM.run_of_ok _ _ h2
  exact AM.of_run_ok _ _ _ _ (e.trans r2)

theorem installFold_nil_ok (p : Nat × IFEnv × Array PendingCheck) (a0 : AState) :
    AM.ok (installFold mode pins p []) a0 ∧ AM.st (installFold mode pins p []) a0 = a0 ∧
    AM.res (installFold mode pins p []) a0 = .ok p :=
  AM.of_run_ok _ _ _ _ rfl

theorem checkPending_ok (fe : IFEnv) (pc : PendingCheck) (a0 : AState)
    (h1 : AM.ok enterScratch a0)
    (h2 : AM.ok (checkValueGroup mode (fe.restrictTo pc.vis) pc.vg) (AM.st enterScratch a0))
    (h3 : AM.ok dropScratch
      (AM.st (checkValueGroup mode (fe.restrictTo pc.vis) pc.vg) (AM.st enterScratch a0))) :
    AM.ok (checkPending mode fe pc) a0 ∧ AM.st (checkPending mode fe pc) a0 =
      AM.st dropScratch
        (AM.st (checkValueGroup mode (fe.restrictTo pc.vis) pc.vg) (AM.st enterScratch a0)) := by
  have r1 := AM.run_of_ok _ _ h1
  have r2 := AM.run_of_ok _ _ h2
  have r3 := AM.run_of_ok _ _ h3
  have := AM.of_run_ok (checkPending mode fe pc) a0
    (AM.st dropScratch
      (AM.st (checkValueGroup mode (fe.restrictTo pc.vis) pc.vg) (AM.st enterScratch a0))) ()
    (by simp only [checkPending, StateT.run_bind, exc_ok_bind, r1, r2, r3])
  exact ⟨this.1, this.2.1⟩

theorem checkPendingList_cons_ok (fe : IFEnv) (pc : PendingCheck) (rest : List PendingCheck)
    (a0 : AState) (h1 : AM.ok (checkPending mode fe pc) a0)
    (h2 : AM.ok (checkPendingList mode fe rest) (AM.st (checkPending mode fe pc) a0)) :
    AM.ok (checkPendingList mode fe (pc :: rest)) a0 ∧
    AM.st (checkPendingList mode fe (pc :: rest)) a0 =
      AM.st (checkPendingList mode fe rest) (AM.st (checkPending mode fe pc) a0) ∧
    AM.res (checkPendingList mode fe (pc :: rest)) a0 =
      AM.res (checkPendingList mode fe rest) (AM.st (checkPending mode fe pc) a0) := by
  have r1 := AM.run_of_ok _ _ h1
  have r2 := AM.run_of_ok _ _ h2
  apply AM.of_run_ok
  simp only [checkPendingList, StateT.run] at r1 r2 ⊢
  rw [r1]; exact r2

theorem checkPendingList_nil_ok (fe : IFEnv) (a0 : AState) :
    AM.ok (checkPendingList mode fe []) a0 ∧ AM.st (checkPendingList mode fe []) a0 = a0 ∧
    AM.res (checkPendingList mode fe []) a0 = .ok () :=
  AM.of_run_ok _ _ _ _ rfl

end twin

section skel
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

theorem isNone_refines (hb : BracketProg p) (hp : p.lookup "is_none" = some isNoneL) (n : Nat) (s₀ : St) (a₀ : AState)
    (vis v2 nt : Word) (fe' : IFEnv) (pend : Array PendingCheck)
    (hR : LoopR pins dn s₀.mem a₀ v2 fe' pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "is_none" [vis, v2, nt]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (isNoneT vis.toNat nt.toNat fe' pend) a₀ ∧
      LoopR pins dn s'.mem (AM.st (isNoneT vis.toNat nt.toNat fe' pend) a₀) v2
        (AM.res (isNoneT vis.toNat nt.toNat fe' pend) a₀).1
        (AM.res (isNoneT vis.toNat nt.toNat fe' pend) a₀).2 ds; ⊤⦄ := by
  have hv := hR.vis
  rw [invoke_eq _ hp]
  simp only [callFn, isNoneL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        (tblGrown_loop pins dn ds p hb.pr n · a₀ v2 fe' pend ·),
        (promoteNew_spec pins dn ds p hb.pr n · a₀ · fe' pend · · · PMemo.empty),
        (drop_loop (pins := pins) dn ds p hb n · (AM.st (promoteNew PMemo.empty coreWalkFuel
          (fe'.visibleBelow - vis.toNat) (fe'.env.tables.length - nt.toNat) fe') a₀) v2
          (AM.res (promoteNew PMemo.empty coreWalkFuel (fe'.visibleBelow - vis.toNat)
            (fe'.env.tables.length - nt.toNat) fe') a₀).2
          pend)] <;>
      finish [isNoneT]

theorem pendPush_spec (hp : p.lookup "pend_push" = some pendPushL) (n : Nat) (s₀ : St)
    (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (g i v : Word)
    (vg : ValueGroup) (hg : decVG (erecP s₀.mem) g.toNat = some vg)
    (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds) (pm : PMemo) (hPM : PMemoR s₀.mem pm) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pend_push" [g, i, v]
    ⦃fun _ s' => LocEq s' s₀ ∧
      LoopR pins dn s'.mem a₀ vis fe (pend.push ⟨vg, i.toNat, v.toNat⟩) ds ∧ PMemoR s'.mem pm; ⊤⦄ := by
  have key := hR.pendPush g i v vg hg
  have key2 := hPM.pendPush g i v
  have hrd : ∀ (h : 130 < (s₀.mem.arr64 CTL).size),
      rdW (s₀.mem.arr64 CTL) 130 = (s₀.mem.arr64 CTL)[130] := fun h => rdW_eq _ _ 130 rfl h
  rw [invoke_eq _ hp]
  simp only [callFn, pendPushL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [pendPushMem]

set_option maxHeartbeats 1000000 in
theorem isSome_refines (hb : BracketProg p) (hpp : p.lookup "pend_push" = some pendPushL)
    (hp : p.lookup "is_some" = some isSomeL) (n : Nat) (s₀ : St) (a₀ : AState)
    (i vis v2 nt g : Word) (fe' : IFEnv) (pend : Array PendingCheck) (vg : ValueGroup)
    (hg : decVG (erecP s₀.mem) g.toNat = some vg)
    (hR : LoopR pins dn s₀.mem a₀ v2 fe' pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "is_some" [i, vis, v2, nt, g]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (isSomeT i.toNat vis.toNat nt.toNat fe' pend vg) a₀ ∧
      LoopR pins dn s'.mem (AM.st (isSomeT i.toNat vis.toNat nt.toNat fe' pend vg) a₀) v2
        (AM.res (isSomeT i.toNat vis.toNat nt.toNat fe' pend vg) a₀).1
        (AM.res (isSomeT i.toNat vis.toNat nt.toNat fe' pend vg) a₀).2 ds; ⊤⦄ := by
  have hv := hR.vis
  rw [invoke_eq _ hp]
  simp only [callFn, isSomeL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        (tblGrown_loop pins dn ds p hb.pr n · a₀ v2 fe' pend ·),
        (promoteVG_spec pins dn ds p hb.pr n · a₀ · fe' pend · vg),
        (pendPush_spec pins dn ds p hpp n · (AM.st (promoteVG PMemo.empty coreWalkFuel vg) a₀) v2 fe' pend ·
          · · (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).2 · · (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).1),
        (promoteNew_spec pins dn ds p hb.pr n · (AM.st (promoteVG PMemo.empty coreWalkFuel vg) a₀) · fe' (pend.push ⟨(AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).2, i.toNat, vis.toNat⟩) · · · (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).1),
        (drop_loop (pins := pins) dn ds p hb n · (AM.st (promoteNew (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).1 coreWalkFuel (fe'.visibleBelow - vis.toNat) (fe'.env.tables.length - nt.toNat) fe') (AM.st (promoteVG PMemo.empty coreWalkFuel vg) a₀)) v2 (AM.res (promoteNew (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).1 coreWalkFuel (fe'.visibleBelow - vis.toNat) (fe'.env.tables.length - nt.toNat) fe') (AM.st (promoteVG PMemo.empty coreWalkFuel vg) a₀)).2 (pend.push ⟨(AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).2, i.toNat, vis.toNat⟩))] <;>
      finish [isSomeT]

theorem pend_words (m : Mem) (pend : Array PendingCheck) (hP : PendR m pend) (j : Word)
    (hj : j.toNat < pend.size) (hj62 : j.toNat < 2 ^ 62) :
    (∀ (h : (3 * j).toNat < (m.arr64 PEND).size),
      decVG (erecP m) ((m.arr64 PEND)[(3 * j).toNat]).toNat = some (pdAt pend j).vg) ∧
    (∀ (h : (3 * j + 2).toNat < (m.arr64 PEND).size),
      ((m.arr64 PEND)[(3 * j + 2).toNat]).toNat = (pdAt pend j).vis) := by
  have hr := hP.recs j.toNat hj
  have e0 : (3 * j).toNat = 3 * j.toNat := by rw [UInt64.toNat_mul]; simp; omega
  have e2 : (3 * j + 2).toNat = 3 * j.toNat + 2 := by rw [UInt64.toNat_add, e0]; simp; omega
  have hpd : pdAt pend j = pend[j.toNat] := by simp [pdAt, hj]
  simp only [decPend, nat?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at hr
  obtain ⟨g, ⟨w0, hw0, rfl⟩, vg, hvg, x, ⟨w1, hw1, rfl⟩, y, ⟨w2, hw2, rfl⟩, he⟩ := hr
  rw [hpd, ← Option.some.inj he]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [e0] at h ⊢
    have : (m.arr64 PEND)[3 * j.toNat] = w0 := by simpa [h] using hw0
    rw [this]; exact hvg
  · simp only [e2] at h ⊢
    have : (m.arr64 PEND)[3 * j.toNat + 2] = w2 := by simpa [h] using hw2
    rw [this]

section phaseB
variable (fe : IFEnv) (pend : Array PendingCheck)

/-- What `check_pending_go` from check `k` ends with: phase B over the checks from `k` accepts,
related to the memory `m` at view `v`. -/
def PendPost (m : Mem) (a : AState) (v : Word) (k : Nat) : Prop :=
  AM.ok (checkPendingList mode fe (pend.toList.drop k)) a ∧
    AM.res (checkPendingList mode fe (pend.toList.drop k)) a = .ok () ∧
    LoopR pins dn m (AM.st (checkPendingList mode fe (pend.toList.drop k)) a) v fe pend ds

theorem drop_cons_pdAt (j : Word) (hj : j.toNat < pend.size) (h1 : (j + 1).toNat = j.toNat + 1) :
    pend.toList.drop j.toNat = pdAt pend j :: pend.toList.drop (j + 1).toNat := by
  rw [h1, List.drop_eq_getElem_cons (by simpa using hj)]
  simp [pdAt, hj]

end phaseB

end skel

end L.Arena
