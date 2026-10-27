import ConAgua.Verdict.DeclValE
import ConAgua.Verdict.IndsE1
import ConAgua.Arena.IndT.Lift
import ConAgua.Checker.NoVerdictTree

/-!
# `check_block_doms_at`'s error refinement (lane `verdicts-b`, helper `ia2-inds`)

`cbdaE_claim`: the model `cbdaE`'s error is the twin's `checkBlockDomsAt` failing with that class
(`domsW_simC`'s proof on the error model): the bounds aborts and `fvar_type_d` claim nothing,
`is_def_eq_core` by `CoreStubsE`, a `false` comparison is the twin's reject, the recursion by
induction on the fuel.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)


namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The claim moves along a twin computation whose failures are another's (from another state). -/
theorem ErrClaim.of_twin {α β : Type} {T : AM α} {T' : AM β} {a a' : AState} {e : Err}
    (h' : ErrClaim T' a' e) (h : ∀ ce, T'.run a' = .error ce → T.run a = .error ce) :
    ErrClaim T a e :=
  fun hk => let ⟨ce, h1, h2⟩ := h' hk; ⟨ce, h ce h1, h2⟩

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv hnv hcE in
/-- **`check_block_doms_at`'s error claim** (the model at L fuel `n`, `domsW_simC`'s hypotheses). -/
theorem cbdaE_claim (hftd : FtdF p) (n : Nat) (hn : n ≤ 2 ^ 62) : ∀ (m : Mem) (a : AState)
    (off fo fl dO dl j : Word) (fvs doms : List EIdx) (fvsP domsP : List ConLeche.Expr),
    StageC dn vis fe env m a → AbsOK m →
    decHL m fo.toNat fl.toNat = some fvs → decHL m dO.toNat dl.toNat = some doms →
    fo.toNat + fl.toNat < 2 ^ 64 → dO.toNat + dl.toNat < 2 ^ 64 → fo.toNat + fl.toNat ≤ iwTop m →
    dO.toNat + dl.toNat ≤ iwTop m → off.toNat + fl.toNat < 2 ^ 64 →
    Frontend.denoteEList a.store fvs = some fvsP → Frontend.denoteEList a.store doms = some domsP →
    (∀ i, i < j.toNat → ∀ x y, fvsP[i]? = some x → domsP[i]? = some y →
      ConLeche.Expr.WScoped (off.toNat + i) x.fvarTypeD ∧ ConLeche.Expr.WScoped (off.toNat + i) y) →
    ∀ e, cbdaE p n m vis off fo fl dO dl j = .error e →
      ErrClaim (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms j.toNat) a e := by
  induction n with
  | zero =>
    intro m a off fo fl dO dl j fvs doms fvsP domsP _ _ _ _ _ _ _ _ _ _ _ _ e he
    rw [cbdaE.eq_1] at he; cases he; exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
    intro m a off fo fl dO dl j fvs doms fvsP domsP hC hA hfvs hdoms hfob hdob hfot hdot hoob
      hfP hdP hws e he
    have hStage := hC.stage
    have hfvl := decHL_length m hfvs
    have hdol := decHL_length m hdoms
    by_cases hj : j = 0
    · rw [cbdaE.arm1 p n m vis off fo fl dO dl j hj] at he; cases he
    have hjpos : 1 ≤ j.toNat := Nat.pos_of_ne_zero fun h0 => hj (UInt64.toNat_inj.mp (by simpa using h0))
    have hj1 : (j - 1).toNat = j.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hjpos))]
      simp
    by_cases hfl : fl ≤ j - 1
    · rw [cbdaE.abort1 p n m vis off fo fl dO dl j hj hfl] at he; cases he; exact ErrClaim.of_cls0 rfl
    by_cases hdl : dl ≤ j - 1
    · rw [cbdaE.abort2 p n m vis off fo fl dO dl j hj hfl hdl] at he; cases he; exact ErrClaim.of_cls0 rfl
    rw [cbdaE.arm2 p n m vis off fo fl dO dl j hj hfl hdl] at he
    have hjm1f : j.toNat - 1 < fl.toNat := by
      have : ¬ fl.toNat ≤ (j - 1).toNat := by rw [← UInt64.le_iff_toNat_le]; exact hfl
      omega
    have hjm1d : j.toNat - 1 < dl.toNat := by
      have : ¬ dl.toNat ≤ (j - 1).toNat := by rw [← UInt64.le_iff_toNat_le]; exact hdl
      omega
    have hfoeq : fo + (j - 1) = UInt64.ofNat (fo.toNat + (j.toNat - 1)) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, hj1]; simp
    have hdoeq : dO + (j - 1) = UInt64.ofNat (dO.toNat + (j.toNat - 1)) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, hj1]; simp
    obtain ⟨wa, hwa_eq, hwa_lt, hwa_dec⟩ := decHL_get' hfvs (j.toNat - 1) hjm1f hfob
    obtain ⟨wb, hwb_eq, hwb_lt, hwb_dec⟩ := decHL_get' hdoms (j.toNat - 1) hjm1d hdob
    rw [hfoeq, hdoeq, hwa_eq, hwb_eq] at he
    have hfvsij : fvs[j.toNat - 1]? = some (decI wa) := by
      rw [List.getElem?_eq_getElem (by omega : j.toNat - 1 < fvs.length)]
      exact congrArg some hwa_dec
    have hdomsij : doms[j.toNat - 1]? = some (decI wb) := by
      rw [List.getElem?_eq_getElem (by omega : j.toNat - 1 < doms.length)]
      exact congrArg some hwb_dec
    obtain ⟨aP, haP, hda⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? fvs fvsP hfP _ _ hfvsij
    obtain ⟨bP, hbP, hdb⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? doms domsP hdP _ _ hdomsij
    obtain ⟨hwx, hwy⟩ := hws (j.toNat - 1) (by omega) aP bP haP hbP
    have hjeq : j.toNat = (j.toNat - 1) + 1 := by omega
    cases h1 : callE p n "fvar_type_d" [wa] m with
    | error e1 =>
      rw [h1, cbdaE.k_fvar_type_d.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
    | ok q1 =>
    obtain ⟨ra, m1⟩ := q1
    rw [h1, cbdaE.k_fvar_type_d.arm1] at he
    have hra : ftdF m [wa] = some (ra, m1) := by
      obtain ⟨s', hs, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (ftdF_spec0 p hftd n _ [wa])
        (callW_of_callE h1)
      rw [← hs]; exact hW
    obtain ⟨x1, a1, hrun1, hStage1, hg1, hw1lt, hw1eq⟩ :=
      ftdF_ok dn vis fe wa hwa_lt m m1 a ra hra hStage
    obtain ⟨ha1, hx1d⟩ := ConRon.Bridge.Inductives.fvarTypeD_run hC.check.state hda hrun1
    rw [ha1] at hrun1 hStage1
    have hA1 := ftdF_afr hra hA
    have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hStage1 hA1 (PStep.refl hC.check.state)
    have hdep : (off + (j - 1)).toNat = off.toNat + (j.toNat - 1) := by
      rw [UInt64.toNat_add, hj1]; exact Nat.mod_eq_of_lt (by omega)
    have hdx : denoteE a.store (decI (ra.headD 0)) = some aP.fvarTypeD := by rw [hw1eq]; exact hx1d
    -- the twin's run up to the comparison
    have hpre : ∀ {β : Type} (k : Bool → AM β),
        ((do
          let a ← unwrapOr fvs[j.toNat - 1]? (.internal "block: domain index")
          let b ← unwrapOr doms[j.toNat - 1]? (.internal "block: domain index")
          let aT ← fvarTypeD a
          let c ← isDefEqCore V fe checkFuel (off.toNat + (j.toNat - 1)) aT b
          k c) : AM β).run a =
        ((isDefEqCore V fe checkFuel (off.toNat + (j.toNat - 1)) (decI (ra.headD 0)) (decI wb)) >>= k).run a := by
      intro β k
      simp only [unwrapOr, hfvsij, hdomsij, pure_bind, StateT.run_bind]
      rw [hrun1]
      simp only [bind, Except.bind]
      rw [← hw1eq]
    have htw : (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms j.toNat).run a =
        ((isDefEqCore V fe checkFuel (off.toNat + (j.toNat - 1)) (decI (ra.headD 0)) (decI wb)) >>= fun c =>
          (do
            unless c do
              ConRon.Arena.fail (.invalid "parameters of all inductive datatypes must match")
            ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms (j.toNat - 1) : AM Unit)).run a := by
      rw [hjeq]
      simp only [ConRon.Arena.checkBlockDomsAt, Nat.add_sub_cancel]
      exact hpre _
    cases h2 : callE p n "is_def_eq_core" [vis, off + (j - 1), ra.headD 0, wb] m1 with
    | error e2 =>
      rw [h2, cbdaE.k_is_def_eq_core.none] at he; cases he
      have hcl := hcE.isDefEqCore n (by omega) hC1.stageT (off + (j - 1)) (ra.headD 0) wb hw1lt hwb_lt e h2
      rw [hdep] at hcl
      exact ErrClaim.of_twin (ErrClaim.bind_left hcl) fun ce hce => by rw [htw]; exact hce
    | ok q2 =>
    obtain ⟨rb, m2⟩ := q2
    rw [h2] at he
    obtain ⟨x2, a2, hrun2, hC2, hg2, hb2eq, hA2, hcs2⟩ :=
      isDefEqC_rsim hq henv n (by omega) hC1 hA1 (off + (j - 1)) (ra.headD 0) wb hw1lt hwb_lt hdx hdb
        (by rw [hdep]; exact hwx) (by rw [hdep]; exact hwy) _ (callW_of_callE h2)
    dsimp only at hC2 hg2 hb2eq hA2
    rw [hdep] at hrun2
    by_cases heq0 : rb.headD 0 = 0
    · rw [cbdaE.k_is_def_eq_core.abort1 p n vis off fo fl dO dl (j - 1) rb m2 heq0] at he; cases he
      have hv2 : x2 = false := by rw [← hb2eq, decBool, heq0]; rfl
      subst hv2
      refine ErrClaim.of_twin (ErrClaim.fail (α := Unit) a2
        (.invalid "parameters of all inductive datatypes must match") (by decide)) fun ce hce => ?_
      rw [htw]
      simp only [StateT.run_bind, hrun2]
      exact hce
    · rw [cbdaE.k_is_def_eq_core.arm1 p n vis off fo fl dO dl (j - 1) rb m2 heq0] at he
      have hv2 : x2 = true := by rw [← hb2eq]; simpa [decBool] using heq0
      subst hv2
      have hg12 := hg1.trans hg2
      have hrec := ih (by omega) m2 a2 off fo fl dO dl (j - 1) fvs doms fvsP domsP hC2 hA2
        (by rw [decHL_grow hg12]; exact hfvs; omega) (by rw [decHL_grow hg12]; exact hdoms; omega)
        hfob hdob (by have := hg12.1; omega) (by have := hg12.1; omega) hoob
        (ConRon.Bridge.denoteEList_ext hcs2.ext _ _ hfP) (ConRon.Bridge.denoteEList_ext hcs2.ext _ _ hdP)
        (fun i hi => hws i (by omega)) e he
      rw [hj1] at hrec
      refine ErrClaim.of_twin hrec fun ce hce => ?_
      rw [htw]
      simp only [StateT.run_bind, hrun2]
      exact hce

end sims

end L.Ind
