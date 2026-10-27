import ConAgua.Arena.StageInst1
import ConAgua.Arena.CoreWalks
import ConAgua.Arena.StubNames
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# The walk reads `bvar_b`, `fvar_b`, `has_fvar_fast`, `loose_bvars_bounded_fast` under the stage relation (lane `indproofs4`)

`IndStubs.lean`'s contracts `bvarB_spec`, `fvarB_spec`, `hasFvarFast_spec` and
`looseBVarsBoundedFast_spec`, discharged by the walks' arena-level refinements (the recipe of
`IndReal.lean`, precedent `StageInst1.lean`):

* `bvar_b`, `loose_bvars_bounded_fast` (`BvarB.lean`): call-closed in `bvbProg`, writing the
  `bvarB` memo only (`bvbProg_closed`: `walkA`, `walkC`); `bvarB_refines`, `lbbFast_refines` give
  `ArenaD` after.
* `fvar_b` (`StubNames.lean`, the adapter `ab_fvb(e, f)`) and `has_fvar_fast` (`HasFvar.lean`):
  call-closed in `hfProg` (the two over the `abstract1` walk's program, which `ab_fvb`'s spec
  asks for), writing the `fvarRange` memo only (`frA`, `frC`); `fvbW_okD` (`CoreWalks.lean`) is
  `ab_fvb` under `ArenaD`.

Every one refines its twin at the fuel word's value (`f.toNat`, any `f`). The twin side keeps
caches and pins (`keepsW_bvarB`, `keepsW_fvarB`), the write sets are below array 64 and `CTL[64]`,
and the memos written are `ArenaR`'s, so `StageR.of_walk` gives the stage relation after.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `cpl` determines `cp`. -/
theorem _root_.L.Arena.Keeps.cp_of_cpl {α : Type} {op : AM α} (h : Keeps cpl op) : Keeps cp op :=
  h.map fun x => (x.1, x.2.1)

/-! ## `bvar_b`, `loose_bvars_bounded_fast` -/

/-- **The model of `bvar_b`** (program- and fuel-free). -/
noncomputable def bvbF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF bvbProg "bvar_b" m args

/-- **The model of `loose_bvars_bounded_fast`.** -/
noncomputable def lbbF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF bvbProg "loose_bvars_bounded_fast" m args

theorem lbbF_spec (p : Prog) (hp : BvbProg p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "loose_bvars_bounded_fast" args
    ⦃fun r s' => LocEq s' s₀ ∧ lbbF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec bvbProg_closed (hp.agree bvbFns) (by decide) n s₀ args

/-- `loose_bvars_bounded_fast` writes only the `bvarB` memo. -/
theorem lbbF_frame {m m' : Mem} {args r : List Word} (h : lbbF m args = some (r, m')) :
    MemFrame walkA walkC m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame bvbProg_closed (by decide) (run_of_callW hc)).1

/-- **`loose_bvars_bounded_fast`'s model refines `looseBVarsBoundedFast` under the stage relation**
(replaces `IndStubs.looseBVarsBoundedFast_spec`). -/
theorem lbbF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f k e : Word)
    (he : H e) :
    RelW lbbF [f, k, e] (StageR dn vis fe) (looseBVarsBoundedFast f.toNat k.toNat (decI e))
      (KeepPost dn vis fe decW0B) := by
  intro m m' a r h hS
  have hfr := lbbF_frame h
  obtain ⟨n, hc⟩ := callF_run h
  rcases n with _ | n
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hok, hD, hres, hle⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lbbFast_refines bvbProg bvbProg_ok n _ a hS.1.arena f k e he) hc
  rw [hs'] at hD
  have hrun := AM.run_of_ok _ a hok
  have hk : Keeps cp (looseBVarsBoundedFast f.toNat k.toNat (decE e)) :=
    (Keeps.bind (keepsW_bvarB _ _) fun _ => Keeps.pure _).cp_of_cpl
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hD hfr (lt64A_of_all rfl) (lt64_of_all rfl) (hk.run hrun)
  exact ⟨_, _, hrun, hS', hg, hres.symm, UInt64.le_iff_toNat_le.mp hle⟩

/-! ## `fvar_b`, `has_fvar_fast` -/

/-- `fvar_b` and `has_fvar_fast` over the `abstract1` walk's program. -/
def hfProg : Prog := [("fvar_b", L.Stubs.fvarBL), ("has_fvar_fast", hasFvarFastL)] ++ absWalkProg

/-- The functions they reach. -/
def hfFns : List FnName := ["fvar_b", "has_fvar_fast", "ab_fvb", "der_b"] ++ frFns

/-- They write only the `fvarRange` memo. -/
theorem hfProg_closed : closedA hfProg frA frC hfFns = true := by decide +kernel

/-- The program bundle. -/
abbrev HfF (p : Prog) : Prop := ProgHas p hfProg

theorem hfProg_abs : AbsProg hfProg := ProgHas.right (l₁ := [_, _]) (ProgHas.refl _)

/-- **The model of `fvar_b`.** -/
noncomputable def fvbF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF hfProg "fvar_b" m args

/-- **The model of `has_fvar_fast`.** -/
noncomputable def hffF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF hfProg "has_fvar_fast" m args

theorem fvbF_spec (p : Prog) (hp : HfF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fvar_b" args
    ⦃fun r s' => LocEq s' s₀ ∧ fvbF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec hfProg_closed (hp.agree hfFns) (by decide) n s₀ args

theorem hffF_spec (p : Prog) (hp : HfF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "has_fvar_fast" args
    ⦃fun r s' => LocEq s' s₀ ∧ hffF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec hfProg_closed (hp.agree hfFns) (by decide) n s₀ args

/-- `fvar_b` writes only the `fvarRange` memo. -/
theorem fvbF_frame {m m' : Mem} {args r : List Word} (h : fvbF m args = some (r, m')) :
    MemFrame frA frC m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame hfProg_closed (by decide) (run_of_callW hc)).1

/-- `has_fvar_fast` writes only the `fvarRange` memo. -/
theorem hffF_frame {m m' : Mem} {args r : List Word} (h : hffF m args = some (r, m')) :
    MemFrame frA frC m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame hfProg_closed (by decide) (run_of_callW hc)).1

/-- `fvar_b(f, e)` is `ab_fvb(e, f)`. -/
theorem fvarBL_spec (p : Prog) (hp : AbsProg p) (hpf : p.lookup "fvar_b" = some L.Stubs.fvarBL)
    (n : Nat) (s₀ : St) (f e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "fvar_b" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ fvbW n s₀.mem e f = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpf]
  simp only [callFn, L.Stubs.fvarBL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, abFvb_spec p hp n] <;>
    finish

/-- **`fvar_b`'s model refines `fvarB` under the stage relation** (replaces
`IndStubs.fvarB_spec`). -/
theorem fvbF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f e : Word)
    (he : H e) :
    RelW fvbF [f, e] (StageR dn vis fe) (fvarB f.toNat (decI e)) (KeepPost dn vis fe decW0Nat) := by
  intro m m' a r h hS
  obtain ⟨n, hc⟩ := callF_run h
  rcases n with _ | n
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (fvarBL_spec hfProg hfProg_abs rfl n _ f e) hc
  rw [hs'] at hm
  obtain ⟨a', hrun, hD, hfr⟩ := fvbW_okD n m m' a hS.1.arena e f _ he hm
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hD hfr (lt64A_of_all rfl) (lt64_of_all rfl)
    ((keepsW_fvarB _ _).cp_of_cpl.run hrun)
  exact ⟨_, _, hrun, hS', hg, rfl⟩

/-- **`has_fvar_fast`'s model refines `hasFvarFast` under the stage relation** (replaces
`IndStubs.hasFvarFast_spec`). -/
theorem hffF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f e : Word)
    (he : H e) :
    RelW hffF [f, e] (StageR dn vis fe) (hasFvarFast f.toNat (decI e)) (KeepPost dn vis fe decW0B) := by
  intro m m' a r h hS
  obtain ⟨n, hc⟩ := callF_run h
  rcases n with _ | n
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (hasFvarFastL_spec hfProg hfProg_abs rfl n _ f e) hc
  rw [hs'] at hI
  rcases hw : fvbW n m e f with _ | ⟨x, m₁⟩
  · rw [hw] at hI; cases hI
  have hle := hfK_le _ _ _ hI
  rw [hw, hfK_some] at hI
  obtain ⟨hr0, rfl⟩ := Prod.mk.inj (Option.some.inj hI)
  obtain ⟨a', ha', hD, hfr⟩ := fvbW_okD n m _ a hS.1.arena e f x he hw
  have hrun : (hasFvarFast f.toNat (decE e)).run a = .ok (x.toNat != 0, a') := by
    simp only [hasFvarFast, StateT.run_bind, ha']; rfl
  have hk : Keeps cp (hasFvarFast f.toNat (decE e)) :=
    (Keeps.bind (keepsW_fvarB _ _) fun _ => Keeps.pure _).cp_of_cpl
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hD hfr (lt64A_of_all rfl) (lt64_of_all rfl) (hk.run hrun)
  refine ⟨_, _, hrun, hS', hg, ?_, ?_⟩
  · rw [← hr0]
    by_cases h0 : x = 0
    · subst h0; rfl
    · have h0' : x.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp e)
      simp [h0, h0']
  · exact UInt64.le_iff_toNat_le.mp hle

end L.Ind
