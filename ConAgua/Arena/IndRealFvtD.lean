import ConAgua.Arena.CallF
import ConAgua.Arena.IndStubs
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.IndView
import ConAgua.Arena.TeleLift
import ConAgua.Arena.StripTeleSpec
import ConAgua.Arena.StageInst1
import ConAgua.Arena.WhnfSpineRefine

/-!
# `fvar_type_d`: the stub contract discharged (lane `indproofs4`, helper `fvt`)

The program- and fuel-free model `ftdF := callF ftdProg "fvar_type_d"` (`CallF.lean`, the recipe
of `IndReal.lean`) and `ftdF_ok`, the `IndStubs` contract's relational fact under `StageR`: the
tag test, then `e_view`'s third word (`viewFVarTy` of the `fvar` view). Writes nothing; the twin's
state is unchanged (`ftdW_ok`). Kept apart from `IndRealFvt.lean` (`fvar_type_ds`,
`get_app_args_f`) with imports below `IndInstallSpec`, which calls `fvar_type_d`
(`check_block_doms_at`): `IndRealFvt.lean` needs `DeclNatBase`, which sits above it.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `fvar_type_d` -/

/-- The model of `fvar_type_d(e)` over `e_view`. -/
def ftdW (m : Mem) (e : Word) : Option (List Word × Mem) :=
  if e >>> 28 ≠ 1 then some ([e], m)
  else if eViewW m e = [] then none
  else some ([(eViewW m e).tail.tail.headD 0], m)

theorem ftdAd_spec (p : Prog) (hp : p.lookup "fvar_type_d" = some fvarTypeDL)
    (hv : p.lookup "e_view" = some eView) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fvar_type_d" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ ftdW s₀.mem e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, fvarTypeDL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, eView_spec p hv n] <;>
      finish [ftdW]

/-- `fvar_type_d` and its callee. -/
def ftdProg : Prog := [("fvar_type_d", fvarTypeDL), ("e_view", eView)]

def ftdFns : List FnName := ftdProg.map (·.1)

/-- `fvar_type_d` writes nothing. -/
theorem ftdProg_closed : closedA ftdProg [] [] ftdFns = true := by decide +kernel

/-- The program bundle. -/
abbrev FtdF (p : Prog) : Prop := ProgHas p ftdProg

/-- **The model of `fvar_type_d`.** -/
noncomputable def ftdF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF ftdProg "fvar_type_d" m args

theorem ftdF_spec0 (p : Prog) (hp : FtdF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fvar_type_d" args
    ⦃fun r s' => LocEq s' s₀ ∧ ftdF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec ftdProg_closed (hp.agree ftdFns) (by decide) n s₀ args

theorem ftdF_eq {m m' : Mem} {e : Word} {r : List Word} (h : ftdF m [e] = some (r, m')) :
    ftdW m e = some (r, m') := by
  obtain ⟨n, hc⟩ := callF_run h
  cases n with
  | zero => simp [callW_zero] at hc
  | succ k =>
    obtain ⟨s', rfl, -, hM⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (ftdAd_spec ftdProg rfl rfl (k + 1) _ e) hc
    exact hM

theorem viewFVarTy_run' (h : EIdx) (a : AState) :
    (ConRon.Arena.viewFVarTy h).run a = .ok (a.store.viewFVarTy h, a) := rfl

theorem ETables.getFVarTy_of_get (t : ETables) (i : EIdx) (k : Nat) (ty : EIdx)
    (h : t.get i = some (.fvar k ty)) : t.getFVarTy i = some ty := by
  unfold ETables.get at h
  unfold ETables.getFVarTy
  split at h
  · simp at h
  split at h
  · cases hn : t.fvars.node? i.idxNat <;> simp [hn] at h ⊢
    exact h.2
  all_goals (repeat' (first | (simp at h; done) | split at h))

theorem EStore.viewFVarTy_of_view (st : EStore) (i : EIdx) (k : Nat) (ty : EIdx)
    (h : st.view i = some (.fvar k ty)) : st.viewFVarTy i = some ty := by
  unfold EStore.view at h
  unfold EStore.viewFVarTy EStore.persGetFVarTy
  split at h
  · simp only [*, ite_true]; exact ETables.getFVarTy_of_get _ _ _ _ h
  · split at h
    · simp only [*, ite_true]; split <;> simp_all [ETables.getFVarTy_of_get _ _ _ _ h]
    · simp at h

theorem eViewW_head1 (m : Mem) (w : Word) (hne : eViewW m w ≠ []) (hg : w >>> 28 = 1) :
    (eViewW m w).headD 0 = 1 := by
  unfold eViewW at hne ⊢
  simp (config := {decide := true}) only [hg, ite_true, ite_false] at hne ⊢
  by_cases c1 : 4294967295 < w
  · simp [c1] at hne
  by_cases c2 : tierW w ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [c1, c2] at hne
  by_cases c3 : tcnt m FVAR (tierW w) ≤ idxW w
  · simp [c1, c2, c3] at hne
  simp [c1, c2, c3]


/-- **`fvar_type_d`'s word model refines `fvarTypeD`**, the twin's state unchanged. -/
theorem ftdW_ok (m m' : Mem) (a : AState) (hR : ArenaR m a) (e : Word) (he : H e) (r : List Word)
    (h : ftdW m e = some (r, m')) :
    m' = m ∧ (fvarTypeD (decI e)).run a = .ok (decI (r.headD 0), a) ∧ (r.headD 0).toNat < 2 ^ 32 := by
  simp only [ftdW] at h
  by_cases hf : e >>> 28 ≠ 1
  · rw [if_pos hf] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have htag : ¬ (decE e).tag = ETag.fvar := by
      intro hc; exact hf ((decE_tag_eq e he 1 (by decide)).mp hc)
    refine ⟨rfl, ?_, he⟩
    simp only [fvarTypeD]
    have : (decI e : EIdx) = decE e := rfl
    rw [this]
    have htag' : ((decE e).tag == ETag.fvar) = false := by simpa using htag
    simp only [htag', Bool.false_eq_true, ite_false, List.headD_cons]
    rfl
  rw [if_neg hf] at h
  have hf' : e >>> 28 = 1 := Decidable.not_not.mp hf
  obtain ⟨hne, h⟩ := of_ite_none h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨v, hv, hV⟩ := eViewW_ok m a hR e hne
  have htag : (decE e).tag = ETag.fvar := (decE_tag_eq e he 1 (by decide)).mpr hf'
  have e2 : (eViewW m e).tail.tail.headD 0 = (eViewW m e).getD 2 0 := by
    cases eViewW m e with
    | nil => simp
    | cons x xs => cases xs with
      | nil => simp
      | cons y ys => cases ys <;> simp
  cases v with
  | fvar k ty =>
    simp only [ViewR] at hV
    have hk := EStore.viewFVarTy_of_view _ _ _ _ hv
    refine ⟨rfl, ?_, by simp only [List.headD_cons, e2]; exact hV.2.2.1⟩
    simp only [fvarTypeD]
    have : (decI e : EIdx) = decE e := rfl
    rw [this]
    simp only [htag, beq_self_eq_true, ite_true]
    have e1 : (ConRon.Arena.viewFVarTy (decE e)).run a = .ok (some ty, a) := by
      rw [viewFVarTy_run', hk]
    simp only [StateT.run] at e1 ⊢
    simp only [StateT.bind, e1, bind, Except.bind, List.headD_cons, e2, ← hV.2.2.2]
    rfl
  | bvar i => have := eViewW_head1 m e hne hf'; simp only [ViewR] at hV; first | exact absurd (this.symm.trans hV) (by decide) | exact absurd (this.symm.trans hV.1) (by decide)
  | sort u => have := eViewW_head1 m e hne hf'; simp only [ViewR] at hV; first | exact absurd (this.symm.trans hV) (by decide) | exact absurd (this.symm.trans hV.1) (by decide)
  | const n us => have := eViewW_head1 m e hne hf'; simp only [ViewR] at hV; first | exact absurd (this.symm.trans hV) (by decide) | exact absurd (this.symm.trans hV.1) (by decide)
  | app f x => have := eViewW_head1 m e hne hf'; simp only [ViewR] at hV; first | exact absurd (this.symm.trans hV) (by decide) | exact absurd (this.symm.trans hV.1) (by decide)
  | lam f x => have := eViewW_head1 m e hne hf'; simp only [ViewR] at hV; first | exact absurd (this.symm.trans hV) (by decide) | exact absurd (this.symm.trans hV.1) (by decide)
  | forallE f x => have := eViewW_head1 m e hne hf'; simp only [ViewR] at hV; first | exact absurd (this.symm.trans hV) (by decide) | exact absurd (this.symm.trans hV.1) (by decide)
  | letE f x y => have := eViewW_head1 m e hne hf'; simp only [ViewR] at hV; first | exact absurd (this.symm.trans hV) (by decide) | exact absurd (this.symm.trans hV.1) (by decide)
  | lit l => have := eViewW_head1 m e hne hf'; simp only [ViewR] at hV; first | exact absurd (this.symm.trans hV) (by decide) | exact absurd (this.symm.trans hV.1) (by decide)
  | proj f x y => have := eViewW_head1 m e hne hf'; simp only [ViewR] at hV; first | exact absurd (this.symm.trans hV) (by decide) | exact absurd (this.symm.trans hV.1) (by decide)

/-- **`fvar_type_d`'s model refines `fvarTypeD`** (replaces `IndStubs.fvarTypeD_spec`): memory and
twin state unchanged. -/
theorem ftdF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (e : Word) (he : H e) :
    RelW ftdF [e] (StageR dn vis fe) (fvarTypeD (decI e)) (KeepPost dn vis fe decW0E) := by
  intro m m' a r h hS
  obtain ⟨rfl, hrun, hlt⟩ := ftdW_ok m m' a hS.1.arena.1 e he r (ftdF_eq h)
  exact ⟨_, a, hrun, hS, IWGrow.refl _, hlt, rfl⟩

/-- `fvar_type_d` writes nothing. -/
theorem ftdF_frame {m m' : Mem} {args r : List Word} (h : ftdF m args = some (r, m')) :
    MemFrame [] [] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame ftdProg_closed (by decide) (run_of_callW hc)).1

end L.Ind
