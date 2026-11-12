module

public import ConAgua.Arena.ProjGuardRowsCI
public import ConAgua.Arena.IndSumSpec.HlbiWalk
import ConAgua.Arena.IndSumSpec.StructProjArgP
import ConAgua.Arena.IndRealWalkT
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.StripTele
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.BvarB
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.Walk
import all ConAgua.Arena.MemoLib
import ConAgua.Arena.WalkLiftRefine
import ConAgua.Arena.DeclBase

@[expose] public section

/-!
# The projection guard's two walk queries under `CoreS` (lane `ronsync3`)

`has_loose_bvar_in` (the window query of `projGuardFast`) and `has_loose_b_var_b_fast` (the
field loop's use test, `projGuardRowsGo`) under the core tier's relation, as `ustW_okC` lifts
`struct_used_later` (`ProjGuardRowsCI.lean`): the stage refinement at the swapped caches, the
twin's run back at the real caches (`CI`), `CoreS` after by the walks' write set (`usA`/`usC`:
the `hb` memo and the bound walk's).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem ci_hlbiGo (F : Nat) : ∀ (memo : Std.HashMap (EIdx × Nat) Bool) (w d : Nat) (h : EIdx),
    CI (hasLooseBVarInGo memo w d F h) := by
  induction F with
  | zero => intro memo w d h; rw [hasLooseBVarInGo]; exact CI.fail _
  | succ F ih =>
    intro memo w d h; rw [hasLooseBVarInGo]
    refine CI.bind (ci_bvarB _ _) fun bb => ?_
    ci_auto [] using ih
    all_goals exact ih _ _ _ _

theorem ci_hlbi (d w : Nat) (e : EIdx) : CI (hasLooseBVarIn d w e) := by
  unfold hasLooseBVarIn
  split
  · exact CI.pure _
  · exact CI.bind (ci_hlbiGo _ _ _ _ _) fun _ => CI.pure _

theorem keepsSp_hlbiGo (F : Nat) : ∀ (memo : Std.HashMap (EIdx × Nat) Bool) (w d : Nat) (h : EIdx),
    Keeps sp (hasLooseBVarInGo memo w d F h) := by
  induction F with
  | zero => intro memo w d h; rw [hasLooseBVarInGo]; exact Keeps.fail _
  | succ F ih =>
    intro memo w d h; rw [hasLooseBVarInGo]
    refine Keeps.bind (L.Ind.keeps_bvarB_sp _ _) fun bb => ?_
    keeps_auto [] using (ih _), sp_blind
    all_goals exact ih _ _ _ _

theorem keepsSp_hlbi (d w : Nat) (e : EIdx) : Keeps sp (hasLooseBVarIn d w e) := by
  unfold hasLooseBVarIn
  split
  · exact Keeps.pure _
  · exact Keeps.bind (keepsSp_hlbiGo _ _ _ _ _) fun _ => Keeps.pure _

theorem keepsSp_hbFast (i : Nat) (e : EIdx) : Keeps sp (hasLooseBVarBFast i e) := by
  unfold hasLooseBVarBFast
  exact Keeps.bind (keepsSp_hbGo _ _ _ _) fun _ => Keeps.pure _

end L.Arena

namespace L.Ind

open L.Arena

/-! ## The program and its write set -/

/-- The two queries' functions, beside `struct_used_later`'s. -/
def hlP : Prog :=
  [("has_loose_bvar_in", hasLooseBVarInL), ("has_loose_bvar_in_go", hasLooseBVarInGoL)] ++ usP

/-- The functions the two queries reach. -/
def hlFns : List FnName := ["has_loose_bvar_in", "has_loose_bvar_in_go"] ++ usFns

theorem hlP_closed : closedA hlP usA usC hlFns = true := by decide +kernel

/-- The program bundle. -/
abbrev HlF (p : Prog) : Prop := ProgHas p hlP

theorem HlF.closed {p : Prog} (hp : HlF p) : closedA p usA usC hlFns = true :=
  closedW_of_agree hlP_closed (hp.agree hlFns)

theorem HlF.us {p : Prog} (hp : HlF p) : UsF p := ProgHas.right (l₁ := [_, _]) hp

/-- The lift of a stage refinement of a walk with `usA`/`usC` frame to `CoreS`. -/
theorem coreS_of_usFrame {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {m m' : Mem} {a a1 : AState} (hS : CoreS dn m a vis fe M eb)
    (hS1 : StageR vis fe m' a1) (hst : a1.store = a.store) (hpi : a1.pins = a.pins)
    (hf : MemFrame usA usC m m') (hM' : ∃ mp, hbMR m' mp) :
    CoreS dn m' { a1 with caches := a.caches } vis fe M eb := by
  have hcpl : cpl { a1 with caches := a.caches } = cpl a := by simp only [cpl, hst, hpi]
  exact hS.arena_frameHb (hS1.check.arena.caches_irrel _) hcpl hf (hiw := hS1.iw) (hhb := hM')
    (by intro b hb; simp only [usA, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl <;> decide)
    (by simp only [usA]; decide)
    (by intro b hb; simp only [usA, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl <;> decide)
    (by intro x hx; simp only [usC, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by intro x hx; simp only [usC, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)

/-- **`has_loose_bvar_in` refines `hasLooseBVarIn` under `CoreS`** (the pool's `IWOK` and the `hb`
memo given). -/
theorem hlbi_okC {p : Prog} (hp : HlF p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} (n : Nat) {m m' : Mem} {a : AState} {d w e : Word} {r : List Word}
    (he : H e) (hS : CoreS dn m a vis fe M eb) (hI : IWOK m) (hM : ∃ mp, hbMR m mp)
    (h : callW p n "has_loose_bvar_in" [d, w, e] m = some (r, m')) :
    ∃ b a', (hasLooseBVarIn d.toNat w.toNat (decE e)).run a = .ok (b, a') ∧
      r.headD 0 = (if b then 1 else 0) ∧ (∃ mp, hbMR m' mp) ∧ CoreS dn m' a' vis fe M eb ∧
      StackKept m m' ∧ IWOK m' ∧ IWGrow m m' ∧ a'.store = a.store := by
  obtain ⟨mp, hM⟩ := hM
  have hf : MemFrame usA usC m m' := (run_memFrame hp.closed (by decide) (run_of_callW h)).1
  rcases n with _ | n
  · rw [callW_zero] at h; cases h
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (hlbiF_spec p (hp.get _) (hp.get _) (hp.get _) (hp.get _) (hp.get _) (ProgHas.right hp.us)
      (hp.get _) (hp.get _) n _ d w e) h
  rw [hs'] at hW
  obtain ⟨b, a1, hrun, hb, hM', hS1, hg⟩ := hlbiFW_ok (vis := vis) (fe := fe) n m m'
    { a with caches := swapC a.caches M } d w e _ mp he ⟨hS.swapCheck, hI⟩ hM hW
  have hrun' := (ci_hlbi _ _ _).back hrun
  have hk := (keepsSp_hlbi _ _ _).run hrun
  simp only [sp, Prod.mk.injEq] at hk
  obtain ⟨hst, -, hpi⟩ := hk
  exact ⟨b, _, hrun', hb, hM', coreS_of_usFrame hS hS1 hst hpi hf hM', StackKept.of_frame hf, hS1.iw, hg, hst⟩

/-- **`has_loose_b_var_b_fast` refines `hasLooseBVarBFast` under `CoreS`** (the pool's `IWOK` and
the `hb` memo given). -/
theorem hbFast_okC {p : Prog} (hp : HlF p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} (n : Nat) {m m' : Mem} {a : AState} {i e : Word} {r : List Word}
    (he : H e) (hS : CoreS dn m a vis fe M eb) (hI : IWOK m) (hM : ∃ mp, hbMR m mp)
    (h : callW p n "has_loose_b_var_b_fast" [i, e] m = some (r, m')) :
    ∃ b a', (hasLooseBVarBFast i.toNat (decE e)).run a = .ok (b, a') ∧
      r.headD 0 = (if b then 1 else 0) ∧ (∃ mp, hbMR m' mp) ∧ CoreS dn m' a' vis fe M eb ∧
      StackKept m m' ∧ IWOK m' ∧ IWGrow m m' ∧ a'.store = a.store := by
  obtain ⟨mp, hM⟩ := hM
  have hf : MemFrame usA usC m m' := (run_memFrame hp.closed (by decide) (run_of_callW h)).1
  rcases n with _ | n
  · rw [callW_zero] at h; cases h
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (hbFast_spec p (hp.get _) (hp.get _) (hp.get _) (hp.get _) (hp.get _) (ProgHas.right hp.us)
      (hp.get _) (hp.get _) n _ i e) h
  rw [hs'] at hW
  obtain ⟨b, a1, hrun, hb, hM', hS1, hg⟩ := hbFastW_ok (vis := vis) (fe := fe) n m m'
    { a with caches := swapC a.caches M } i e _ mp he ⟨hS.swapCheck, hI⟩ hM hW
  have hrun' := (ci_hbFast _ _).back hrun
  have hk := (keepsSp_hbFast _ _).run hrun
  simp only [sp, Prod.mk.injEq] at hk
  obtain ⟨hst, -, hpi⟩ := hk
  exact ⟨b, _, hrun', hb, hM', coreS_of_usFrame hS hS1 hst hpi hf hM', StackKept.of_frame hf, hS1.iw, hg, hst⟩

end L.Ind
