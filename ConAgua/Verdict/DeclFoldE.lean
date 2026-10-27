import ConAgua.Verdict.DeclStepE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
set_option linter.unusedSectionVars false

/-!
# Phase A's fold fails only where the twin does (lane `verdicts-b`, helper `d`)

`install_fold_go` / `install_fold_next` (`Arena/Checker.lean`) is phase A's loop, a pair of
mutually recursive functions; its twin `installFold` reports a record's failure as the value
`.ok (.error (ce, pos))`. The error claim (`installFoldGo_refinesE`): from the hypotheses of the ok
refinement (`installFoldGo_refines`, `CheckerT.lean`), a failing run of class `≠ 0` means
`TwinFailsV (installFold … (ds.toList.drop i))` from the start state. By induction on the fuel,
both functions at once: `install_decl_step`'s failure is the twin's step failure
(`InstallDeclStepSpecE`), its ok run the twin's step (`installDeclStep_refines`) before the rest's
failure (the induction hypothesis).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)
open ConRon.Bridge (FoldOK PinsDenote CheckOK StepOK PersDecl PersPinSets PExt)

local notation "V" => ConLeche.CheckMode.verified

l_model installFoldGo_specE (p : Prog) (hf : p.lookup "install_fold_go" = some installFoldGoL)
  fns [hf ↦ installFoldGoE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model installFoldNext_specE (p : Prog) (hf : p.lookup "install_fold_next" = some installFoldNextL)
  fns [hf ↦ installFoldNextE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

/-! ## The twin side -/

/-- A record's step failure (in the monad or as a value) is the fold's failure. -/
theorem installFold_fails_head {mode : ConLeche.CheckMode} {pins : List INatOpPinSet}
    {q : Nat × IFEnv × Array PendingCheck} {d : IDeclaration} {rest : List IDeclaration}
    {a : AState} {c : Word} (h : TwinFailsV (installDeclStep mode pins q d) a c) :
    TwinFailsV (installFold mode pins q (d :: rest)) a c := by
  rcases h with ⟨ce, hce, hc⟩ | ⟨ce, k, a', hce, hc⟩
  · refine .inl ⟨ce, ?_, hc⟩
    simp only [installFold, StateT.run_bind, hce]; rfl
  · refine .inr ⟨ce, k, a', ?_, hc⟩
    simp only [installFold, StateT.run_bind, hce, exc_ok_bind]; rfl

/-- A record that steps ok: the fold fails as the rest does. -/
theorem installFold_fails_tail {mode : ConLeche.CheckMode} {pins : List INatOpPinSet}
    {q q' : Nat × IFEnv × Array PendingCheck} {d : IDeclaration} {rest : List IDeclaration}
    {a : AState} {c : Word} (h1 : AM.ok (installDeclStep mode pins q d) a)
    (hr : AM.res (installDeclStep mode pins q d) a = .ok q')
    (h : TwinFailsV (installFold mode pins q' rest) (AM.st (installDeclStep mode pins q d) a) c) :
    TwinFailsV (installFold mode pins q (d :: rest)) a c := by
  have e := installFold_cons mode pins q q' d rest a h1 hr
  unfold TwinFailsV at h ⊢
  rw [e]; exact h

/-! ## The loop -/

section fold
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- `install_fold_go`'s error claim at fuel `n` (the hypotheses of `FoldGoSpec`). -/
def FoldGoSpecE (n : Nat) : Prop :=
  ∀ (m : Mem) (a₀ : AState) (i cnt vis : Word) (fe : IFEnv) (pend : Array PendingCheck),
    i.toNat ≤ ds.size → cnt.toNat = ds.size → TwinFold pins ds fe pend a₀ →
    LoopR pins dn m a₀ vis fe pend ds → LoopMem dn m a₀ → CoreMemos m → IndMemos m →
    ∀ e, callE p n "install_fold_go" [i, cnt, vis] m = .error e →
      ErrClaimV (installFold V pins (i.toNat, fe, pend) (ds.toList.drop i.toNat)) a₀ e

/-- `install_fold_next`'s error claim at fuel `n` (the hypotheses of `FoldNextSpec`). -/
def FoldNextSpecE (n : Nat) : Prop :=
  ∀ (m : Mem) (a₀ : AState) (i cnt vis : Word) (fe : IFEnv) (pend : Array PendingCheck),
    i.toNat < ds.size → cnt.toNat = ds.size → TwinFold pins ds fe pend a₀ →
    LoopR pins dn m a₀ vis fe pend ds → LoopMem dn m a₀ → CoreMemos m → IndMemos m →
    ∀ e, callE p n "install_fold_next" [i, cnt, vis] m = .error e →
      ErrClaimV (installFold V pins (i.toNat, fe, pend) (ds.toList.drop i.toNat)) a₀ e

variable (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hpi : p.lookup "install_step" = some installStepL)
    (hpd : p.lookup "install_decl_step" = some installDeclStepL)
    (hpg : p.lookup "install_fold_go" = some installFoldGoL)
    (hpx : p.lookup "install_fold_next" = some installFoldNextL) (hsz : ds.size < 2 ^ 63)
    (hb : BracketProg p) (hdc : LoopCallees dn p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
    (hSt : InstallDeclStepSpecE pins dn ds p)
include hpp hpn hps hpi hpd hpg hpx hsz hb hdc hFD hLD hSt

theorem foldGoE_step (n : Nat) (ih : FoldNextSpecE pins dn ds p n) :
    FoldGoSpecE pins dn ds p (n + 1) := by
  intro m a₀ i cnt vis fe pend hi hc hT hR hM hcm him e he hk0
  have hW := triple_of_callE_err (installFoldGo_specE p hpg (n + 1) ⟨m, Locals.init []⟩ i cnt vis)
    he (Err.code_ne_of_cls hk0)
  by_cases g1 : i = cnt
  · rw [installFoldGoE.arm1 p n m i cnt vis g1] at hW; cases hW
  rw [installFoldGoE.arm2 p n m i cnt vis g1] at hW
  have hlt : i.toNat < ds.size := by
    have : i.toNat ≠ cnt.toNat := fun e => g1 (UInt64.toNat_inj.mp e)
    omega
  cases h1 : callE p n "install_fold_next" [i, cnt, vis] m with
  | error e1 =>
    rw [h1, installFoldGoE.k_install_fold_next.none] at hW; cases hW
    exact ih m a₀ i cnt vis fe pend hlt hc hT hR hM hcm him _ h1 hk0
  | ok q =>
    obtain ⟨r, m₁⟩ := q
    rw [h1, installFoldGoE.k_install_fold_next.arm1] at hW; cases hW

theorem foldNextE_step (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (ih : FoldGoSpecE pins dn ds p n) :
    FoldNextSpecE pins dn ds p (n + 1) := by
  intro m a₀ i cnt vis fe pend hi hc hT hR hM hcm him e he hk0
  have hn' : n ≤ 2 ^ 62 := by omega
  have hW := triple_of_callE_err (installFoldNext_specE p hpx (n + 1) ⟨m, Locals.init []⟩ i cnt vis)
    he (Err.code_ne_of_cls hk0)
  have h1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [installFoldNextE.arm1] at hW
  have hTw : TwinOK dn m a₀ fe := by
    obtain ⟨_, hF, _⟩ := hT.fold
    exact TwinOK.of_check hF.check ⟨hM.erec, hM.spn, hM.bstk, hcm, fun k x e => (hM.dnP k x e).2⟩
  rw [drop_cons_dsAt ds i hi h1, h1]
  cases hc1 : callE p n "install_decl_step" [i, vis] m with
  | error e1 =>
    rw [hc1, installFoldNextE.k_install_decl_step.none] at hW; cases hW
    exact installFold_fails_head (hSt n hn' m a₀ i vis fe pend hi hT hR hTw hM.flag him _ hc1 hk0)
  | ok q =>
    obtain ⟨r, m₁⟩ := q
    rw [hc1, installFoldNextE.k_install_decl_step.arm1] at hW
    obtain ⟨s', hs', -, hok, hres, hR', hM', hcm', him'⟩ := triple_of_callE
      (installDeclStep_refines V pins dn ds p rfl hb hdc hFD hLD hpp hpn hps hpi hpd n hn'
        ⟨m, Locals.init []⟩ a₀ i vis fe pend hi hT hR hM hcm him) hc1
    subst hs'
    have hstep : TwinFold pins ds (AM.res (installStep V pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1
        (AM.res (installStep V pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2
        (AM.st (installDeclStep V pins (i.toNat, fe, pend) (dsAt ds i)) a₀) := by
      have e : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
      rw [e]
      exact hT.stepAM hi (by rw [← e]; exact hok) (by rw [← e]; exact hres)
    cases hc2 : callE p n "install_fold_go" [i + 1, cnt, r.headD 0] s'.mem with
    | error e2 =>
      rw [hc2, installFoldNextE.k_install_fold_go.none] at hW; cases hW
      have := ih s'.mem _ (i + 1) cnt (r.headD 0) _ _ (by omega) hc hstep hR' hM' hcm' him' _ hc2 hk0
      rw [h1] at this
      exact installFold_fails_tail hok hres this
    | ok q2 =>
      obtain ⟨r2, m2⟩ := q2
      rw [hc2, installFoldNextE.k_install_fold_go.arm1] at hW; cases hW

/-- **`install_fold_go` fails only where `installFold` does** (and `install_fold_next`): from the
hypotheses of `installFoldGo_refines` at the fold's start, a failing run of class `≠ 0` means the
twin's phase A over the records from `i` fails with that class (a record's failure, as a value). -/
theorem installFoldGo_refinesE (n : Nat) (hn : n ≤ 2 ^ 62) :
    FoldGoSpecE pins dn ds p n ∧ FoldNextSpecE pins dn ds p n := by
  induction n with
  | zero =>
    constructor
    · intro m a₀ i cnt vis fe pend _ _ _ _ _ _ _ e he
      obtain ⟨e', he', h0⟩ := callE_zero p "install_fold_go" [i, cnt, vis] m
      rw [he] at he'; cases he'
      exact ErrClaimV.of_cls0 h0
    · intro m a₀ i cnt vis fe pend _ _ _ _ _ _ _ e he
      obtain ⟨e', he', h0⟩ := callE_zero p "install_fold_next" [i, cnt, vis] m
      rw [he] at he'; cases he'
      exact ErrClaimV.of_cls0 h0
  | succ n ih =>
    have ih := ih (by omega)
    exact ⟨foldGoE_step pins dn ds p hpp hpn hps hpi hpd hpg hpx hsz hb hdc hFD hLD hSt n ih.2,
      foldNextE_step pins dn ds p hpp hpn hps hpi hpd hpg hpx hsz hb hdc hFD hLD hSt n hn ih.1⟩

end fold

end L.Arena
