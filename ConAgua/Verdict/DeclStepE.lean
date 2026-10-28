import ConAgua.Arena.CheckerT
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# The verdict claims of `install_step_go`, `install_step`, `install_decl_step`
(lane `verdicts-b`, helper `d`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt DeclAtF IndDeclAt CVAt dw decCIs)
open ConRon.Bridge (FoldOK PinsDenote CheckOK StepOK PersDecl PersPinSets PExt)

local notation "V" => ConLeche.CheckMode.verified

l_model installStep_specE (p : Prog) (hf : p.lookup "install_step" = some installStepL)
  fns [hf ↦ installStepE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model installDeclStep_specE (p : Prog) (hf : p.lookup "install_decl_step" = some installDeclStepL)
  fns [hf ↦ installDeclStepE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

section istg
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- **What `install_step_go` claims on failure under `StageT`** (the error half of
`installStepGo_specT`). -/
def InstallStepGoSpecE : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (i : Word), i.toNat < ds.size → ConRon.Bridge.StateOK a →
    (∃ env, FoldOK V env fe a) →
    LoopR pins dn m a vis fe pend ds → TwinOK dn m a fe → pinW m 0 ≠ 0 →
    (∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x) →
    (∃ pinsP, PinsDenote a.store pins pinsP) → IndMemos m →
    ∀ e, callE p n "install_step_go" [i, vis] m = .error e →
    ErrClaim (installStepGo V pins fe (dsAt ds i)) a e

/-- **`install_step_go` fails only where `installStepGo` does**: the error half of `istg_ref`
(`check_decl`'s arms' and inductive arm's claims, `install_value`'s). -/
theorem installStepGo_errT {p : Prog} (hdc : LoopCallees dn p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
    (hnv : closedNV p L.Checker.nvFns = true) (hG : IstgG pins dn ds p) : InstallStepGoSpecE pins dn ds p := by
  intro n hn m a vis fe pend i hi hok0 hFo hR hTw hfl hden hPD hIM e hc
  exact RefE.run_err (installStepGo_specE p hdc.istg hdc.cd.cd n ⟨m, Locals.init []⟩ i vis) hnv hG
    (istg_ref hdc hFD hLD (by omega) hi hok0 hFo hR hTw hfl hden hPD hIM) hc

end istg

section ist
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- **What `install_step` claims on failure under `StageT`** (the error half of
`installStep_pieces`'s hypotheses). -/
def InstallStepSpecE : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (i vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck), i.toNat < ds.size → ConRon.Bridge.StateOK a →
    a.store.scratchOn = false → LoopR pins dn m a vis fe pend ds → TwinOK dn m a fe →
    pinW m 0 ≠ 0 → (∃ env, FoldOK V env fe a) →
    (∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x) → PersDecl (dsAt ds i) →
    (∃ pinsP, PinsDenote a.store pins pinsP) → PersPinSets pins → IndMemos m →
    ∀ e, callE p n "install_step" [i, vis] m = .error e →
    ErrClaim (installStep V pins i.toNat fe pend (dsAt ds i)) a e

/-- **`install_step` fails only where `installStep` does**: the bracket's openings and the
promotions claim nothing; `install_step_go` by its claim. -/
theorem installStep_errT {p : Prog} (hb : BracketProg p) (hp : p.lookup "install_step" = some installStepL)
    (hnv : closedNV p L.Checker.nvFns = true)
    (hGo : InstallStepGoSpecE pins dn ds p) : InstallStepSpecE pins dn ds p := by
  intro n hn m a i vis fe pend hi hok hoff hR hTw hfl hF hden hpd hPD hpps hIM e hc
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (installStep_specE p hp n ⟨m, Locals.init []⟩ i vis) hc
    (Err.code_ne_of_cls hk0)
  have hwf' : StoreWF (AM.st flushCaches a).store := by rw [flushCaches_st]; exact hok.wf
  have hoff' : (AM.st flushCaches a).store.scratchOn = false := by rw [flushCaches_st]; exact hoff
  have hFe : ∃ env, FoldOK V env fe (AM.st enterScratch (AM.st flushCaches a)) := by
    obtain ⟨env, h⟩ := hF
    exact ⟨env, by rw [enterScratch_st, flushCaches_st]; exact h.enter⟩
  have hde : ∃ x, Frontend.denoteDecl (AM.st enterScratch (AM.st flushCaches a)).store
      (dsAt ds i) = some x := by
    obtain ⟨x, h⟩ := hden
    exact ⟨x, by
      rw [enterScratch_st, flushCaches_st]
      exact ConRon.Bridge.denoteDecl_pext (PExt.enterScratch hok.wf) hpd h⟩
  have hPDe : ∃ pinsP, PinsDenote (AM.st enterScratch (AM.st flushCaches a)).store pins pinsP := by
    obtain ⟨q, h⟩ := hPD
    exact ⟨q, by
      rw [enterScratch_st, flushCaches_st]
      exact PinsDenote.pmono (PExt.enterScratch hok.wf) _ _ hpps h⟩
  cases n with
  | zero => rw [installStepE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [installStepE.arm1] at hW
  simp only [installStep]
  cases h0 : callE p n "tbl_cnt" [] m with
  | error e0 =>
    rw [h0, installStepE.k_tbl_cnt.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h0
  | ok q0 =>
  obtain ⟨r0, m0⟩ := q0
  rw [h0, installStepE.k_tbl_cnt.arm1] at hW
  obtain ⟨s0, hs0, hm0, -⟩ := triple_of_callE (tblCnt_spec p (hb.pr.get "tbl_cnt") n ⟨m, Locals.init []⟩) h0
  have hm0' : m0 = m := hs0.symm.trans hm0
  subst hm0'
  cases h1 : callE p n "flush_caches" [] m0 with
  | error e1 =>
    rw [h1, installStepE.k_flush_caches.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, installStepE.k_flush_caches.arm1] at hW
  obtain ⟨s1, hs1, -, hokF, hLF, hTF, hflF, hIMF⟩ := triple_of_callE
    (flush_loopW (pins := pins) dn ds p hb n ⟨m0, Locals.init []⟩ a vis fe pend hR hTw hfl hIM) h1
  subst hs1
  refine ErrClaim.bind_right (AM.run_of_ok _ _ hokF) ?_
  cases h2 : callE p n "scratch_enter" [] s1.mem with
  | error e2 =>
    rw [h2, installStepE.k_scratch_enter.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, installStepE.k_scratch_enter.arm1] at hW
  obtain ⟨s2, hs2, -, hokE, hLE, hTE, hflE, hIME⟩ := triple_of_callE
    (enter_loopW (pins := pins) dn ds p hb n ⟨s1.mem, Locals.init []⟩ (AM.st flushCaches a) vis fe pend
      hwf' hoff' hLF hTF hflF hIMF) h2
  subst hs2
  refine ErrClaim.bind_right (AM.run_of_ok _ _ hokE) ?_
  cases h3 : callE p n "install_step_go" [i, vis] s2.mem with
  | error e3 =>
    rw [h3, installStepE.k_install_step_go.none] at hW; cases hW
    exact ErrClaim.bind_left (hGo n hn' s2.mem _ vis fe pend i hi (TwinFold.enterAM hok) hFe hLE hTE
      hflE hde hPDe hIME _ h3)
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3] at hW
  by_cases hf : r3.tail.headD 0 = 0
  · rw [installStepE.k_install_step_go.arm1 p _ _ _ _ _ _ hf] at hW
    cases h4 : callE p n "is_none" [vis, r3.headD 0, r0.headD 0] m3 with
    | error e4 =>
      rw [h4, installStepE.k_is_none.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h4
    | ok q4 =>
      obtain ⟨r4, m4⟩ := q4
      rw [h4, installStepE.k_is_none.arm1, installStepE.j1.arm1] at hW; cases hW
  · rw [installStepE.k_install_step_go.arm2 p _ _ _ _ _ _ hf] at hW
    cases h4 : callE p n "is_some" [i, vis, r3.headD 0, r0.headD 0, r3.tail.tail.headD 0] m3 with
    | error e4 =>
      rw [h4, installStepE.k_is_none.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h4
    | ok q4 =>
      obtain ⟨r4, m4⟩ := q4
      rw [h4, installStepE.k_is_none.arm1, installStepE.j1.arm1] at hW; cases hW

end ist

section ids
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- **What `install_decl_step` claims on failure under `StageT`**: the twin's step reports
failures as values. -/
def InstallDeclStepSpecE : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (i vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck), i.toNat < ds.size → TwinFold pins ds fe pend a →
    LoopR pins dn m a vis fe pend ds → TwinOK dn m a fe → pinW m 0 ≠ 0 → IndMemos m →
    ∀ e, callE p n "install_decl_step" [i, vis] m = .error e →
    ErrClaimV (installDeclStep V pins (i.toNat, fe, pend) (dsAt ds i)) a e

/-- **`install_decl_step` fails only where `installDeclStep` does**: a rejected `And` pin is the
twin's value failure at the position, `install_step`'s failure the same. -/
theorem installDeclStep_errT {p : Prog} (hdc : LoopCallees dn p) (hFD : FrontDecls ds)
    (hnv : closedNV p L.Checker.nvFns = true)
    (hp : p.lookup "install_decl_step" = some installDeclStepL)
    (hSt : InstallStepSpecE pins dn ds p) : InstallDeclStepSpecE pins dn ds p := by
  intro n hn m a i vis fe pend hi hT hR hTw hfl hIM e hc hk0
  have hW := triple_of_callE_err (installDeclStep_specE p hp n ⟨m, Locals.init []⟩ i vis) hc
    (Err.code_ne_of_cls hk0)
  have hpk : ConRon.Bridge.PinsOK a := by obtain ⟨_, hF, _⟩ := hT.fold; exact hF.check.pins
  have hF0 : ∃ env, FoldOK V env fe a := by obtain ⟨env, hF, _⟩ := hT.fold; exact ⟨env, hF⟩
  have e0 : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  have hden0 : ∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x := by
    rw [e0]; exact hT.denote hi
  have hpd : PersDecl (dsAt ds i) := by rw [e0]; exact hT.pd _ (by simp)
  have hPD0 : ∃ pinsP, PinsDenote a.store pins pinsP := hT.pinsD
  have hpps : PersPinSets pins := hT.pp
  cases n with
  | zero => rw [installDeclStepE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [installDeclStepE.arm1] at hW
  cases h0 : callE p n "and_pin_ok" [i] m with
  | error e0' =>
    rw [h0, installDeclStepE.k_and_pin_ok.none] at hW; cases hW
    exact absurd (callE_nv hnv (declNv_mem _ (by decide +kernel)) _ _ _ h0) hk0
  | ok q0 =>
  obtain ⟨r0, m0⟩ := q0
  rw [h0] at hW
  obtain ⟨s0, hs0, -, hokA, hLA, hresA, hTwA, hflA, hoffA, hFA, hdenA, hPDA, hIMA⟩ := triple_of_callE
    (andPinOk_refinesT pins dn ds p hdc.leaf hdc.and_pin_ok hdc.andInd hdc.cd.crp.red.rom hdc.indIn
      hFD n ⟨m, Locals.init []⟩ a vis fe pend i hi hT.stateOK hpk hT.off hF0 hR hTw hfl hden0 hpd hPD0
      hpps hdc.indMemo hdc.crf hIM) h0
  subst hs0
  have hrunA := AM.run_of_ok _ _ hokA
  by_cases hz : r0.headD 0 = 0
  · rw [installDeclStepE.k_and_pin_ok.abort1 p _ _ _ _ _ hz] at hW; cases hW
    have hres : AM.res (andPinOk (dsAt ds i)) a = false := by rw [hresA, hz]; rfl
    rw [hres] at hrunA
    refine .inr ⟨.invalid "`And` must be the standard `And`", i.toNat, AState.abandoned, ?_, rfl⟩
    show (match (andPinOk (dsAt ds i)).run a with
      | .ok (true, s₁) => _
      | .ok (false, _) => _
      | .error e => _) = _
    rw [hrunA]
  rw [installDeclStepE.k_and_pin_ok.arm1 p _ _ _ _ _ hz] at hW
  have hres : AM.res (andPinOk (dsAt ds i)) a = true := by rw [hresA]; exact bne_iff_ne.mpr hz
  rw [hres] at hrunA
  have hokA' : ConRon.Bridge.StateOK (AM.st (andPinOk (dsAt ds i)) a) := by
    rw [e0]; exact hT.andPinAM hi (by rw [← e0]; exact hokA)
  cases h1 : callE p n "install_step" [i, vis] s0.mem with
  | error e1 =>
    rw [h1, installDeclStepE.k_install_step.none] at hW; cases hW
    obtain ⟨ce, hce, hcl⟩ := hSt n hn' s0.mem (AM.st (andPinOk (dsAt ds i)) a) i vis fe pend hi hokA'
      hoffA hLA hTwA hflA hFA hdenA hpd hPDA hpps hIMA _ h1 hk0
    refine .inr ⟨ce, i.toNat, AState.abandoned, ?_, hcl⟩
    show (match (andPinOk (dsAt ds i)).run a with
      | .ok (true, s₁) => _
      | .ok (false, _) => _
      | .error e => _) = _
    rw [hrunA]
    simp only [StateT.run] at hce ⊢
    show (match installStep V pins i.toNat fe pend (dsAt ds i) (AM.st (andPinOk (dsAt ds i)) a) with
      | .ok ((fe', pend'), s') => _
      | .error e => _) = _
    rw [hce]
  | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, installDeclStepE.k_install_step.arm1] at hW; cases hW

end ids

end L.Arena
