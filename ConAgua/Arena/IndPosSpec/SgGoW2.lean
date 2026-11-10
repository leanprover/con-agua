module

public import ConAgua.Arena.IndPosSpec.RpGoStep
public import ConAgua.Arena.IndPosSpec.RxMapW
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.Arena.IndPosSpec.CrLook
public import ConAgua.Arena.IndPos2
import ConAgua.Arena.IndPosSpec.Rx
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2

@[expose] public section

/-!
# SgGoW2

`posRpW`, `posRp_spec`, the model and spec of `nest_seed_of_go` (generated), `sgW` and the lemmas only
they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `replace_apps` at any exec fuel. -/
def posRpW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, no, nl, us, b, nn, e => rpConstW k m no nl us b nn e

theorem posRp_spec (p : Prog) (C : CrLook p) (k : Nat) (s₀ : St) (no nl us b nn e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "replace_apps" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧ posRpW k s₀.mem no nl us b nn e = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases k with
  | zero => rw [invoke_eq _ C.ra]; simp only [callFn, replaceApps]; vcgen [exec] <;> grind
  | succ k => exact replaceApps_spec p C.rx.hl C.rx.hk C.raf C.rap C.rgo C.rnd C.rcl C.ra k s₀ no nl us b nn e

l_model sgGo_spec (p : Prog) (hC : CrLook p) (hgo : p.lookup "nest_seed_of_go" = some nestSeedOfGoL)
  fns [hgo ↦ sgGoW void]
  specs [posRp_spec p hC n, (rxSpec_all p hC.rx n).2.2.2.2.2.2.2]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

/-- The continuation after the recursive call passes its memory on. -/
theorem sgGoW.k_nest_seed_of_go_id (x : Option Mem) : sgGoW.k_nest_seed_of_go x = x := by
  cases x <;> rfl

def sgC (nPc : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (key, m4) => some ([key, nPc], m4)
def sgB (k : Nat) (ctx f ind us dO dL nPc : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m2) => match sgGoW k m2 ctx f dO dL q 0 with
    | none => none
    | some m3 => sgC nPc (posRecW m3 [ind, us, q, dL])
def sgA (k : Nat) (ctx ind us dO dL nPc : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (f, m1) => sgB k ctx f ind us dO dL nPc (allocW m1 dL)
/-- The model of `nest_seed_of` at exec fuel `k + 1`. -/
def sgW (k : Nat) (m : Mem) (ctx hO hL ind us dO dL nPc : Word) : Option (List Word × Mem) :=
  sgA k ctx ind us dO dL nPc (posRecW m [1, rdW (m.arr64 IW) (ctx + 7), rdW (m.arr64 IW) (ctx + 8), hO, hL])

end L.Ind

end
