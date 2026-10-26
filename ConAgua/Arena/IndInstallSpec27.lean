import ConAgua.Arena.IndInstallSpec26
import ConAgua.Arena.RecCheckSpec5

/-!
# Refinements of `IndInstall`, part 27 (lane `indproofs3`, helper `tail`): `checkBlockTables`

One structure-like member (`ctoW_sim`) and the walk over the three lists (`ctbW_sim`), then the
census theorem.

**Hypotheses beyond the stage relation and the decodings** (each is the caller's):
* `HbMemo s₀.mem`: the `has_loose_bvar_b` memo well formed in the memory at hand (for
  `struct_proj_guards`); returned for the memory after.
-/

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- One structure-like member's install, as the twin runs it. -/
def tabOne (fe : IFEnv) (bs : BlockShape) (msh : MemberShape) (cA : IConstantVal) (nF : Nat)
    (sorts : List LIdx) : AM IFEnv := do
  let guards ← structProjGuards cA.type bs.nP nF sorts
  checkStructProjTable msh.cvT.name cA.name bs.lps bs.nP nF bs.resSort guards cA fe

theorem cbt_one (bs : BlockShape) (msh : MemberShape) (ms : List MemberShape)
    (css : List (List (IConstantVal × Nat))) (sss : List (List (List LIdx))) (fe : IFEnv)
    (cA : IConstantVal) (nF : Nat) (sorts : List LIdx) (h : msh.nIdx = 0) :
    ConRon.Arena.checkBlockTables bs (msh :: ms) ([(cA, nF)] :: css) ([sorts] :: sss) fe =
      tabOne fe bs msh cA nF sorts >>= fun fe₂ => ConRon.Arena.checkBlockTables bs ms css sss fe₂ := by
  simp [ConRon.Arena.checkBlockTables, h, tabOne, bind_assoc]

theorem cbt_skip (bs : BlockShape) (msh : MemberShape) (ms : List MemberShape)
    (cs : List (IConstantVal × Nat)) (css : List (List (IConstantVal × Nat))) (ss : List (List LIdx))
    (sss : List (List (List LIdx))) (fe : IFEnv) (h : ¬ (cs.length = 1 ∧ ss.length = 1 ∧ msh.nIdx = 0)) :
    ConRon.Arena.checkBlockTables bs (msh :: ms) (cs :: css) (ss :: sss) fe = ConRon.Arena.checkBlockTables bs ms css sss fe := by
  rcases cs with _ | ⟨⟨cA, nF⟩, _ | ⟨c2, cs⟩⟩ <;> rcases ss with _ | ⟨s1, _ | ⟨s2, ss⟩⟩ <;>
    simp_all [ConRon.Arena.checkBlockTables]

theorem cbt_nil (bs : BlockShape) (ms : List MemberShape) (css : List (List (IConstantVal × Nat)))
    (sss : List (List (List LIdx))) (fe : IFEnv) (h : ms = [] ∨ css = [] ∨ sss = []) :
    ConRon.Arena.checkBlockTables bs ms css sss fe = pure fe := by
  rcases ms with _ | ⟨m, ms⟩ <;> rcases css with _ | ⟨c, css⟩ <;> rcases sss with _ | ⟨s, sss⟩ <;>
    simp_all [ConRon.Arena.checkBlockTables]

/-- `struct_proj_guards` at fuel `1` does not return. -/
theorem spgW_zero (m : Mem) (cty nP nF so sl : Word) : spgW 0 m cty nP nF so sl = none := by
  simp only [spgW, spgK1]
  split
  · rfl
  · split
    · rfl
    · simp [ulW, spgK2]

/-- The tables' callees outside the walk-memo cascade (`AbsKeep`, a program fact). -/
def tablesKeepCallees : List FnName := ["struct_proj_guards"]

theorem nPnF_bound {x y : Word} (h : ¬ x + y + 1 ≤ x) : x.toNat + y.toNat + 1 < 2 ^ 64 := by
  have h' : x.toNat < (x + y + 1).toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h)
  rw [UInt64.toNat_add, UInt64.toNat_add] at h'
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  simp only [UInt64.toNat_one] at h'
  omega

end L.Ind
