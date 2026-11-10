module

public import ConAgua.Arena.StrLitBase
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.L.ModelGen
import ConAgua.Arena.InferLeaves
import all ConAgua.Arena.StrLit

@[expose] public section

/-!
# `str_cv`: `IConstantInfo.toConstantVal` under `CoreS` (helper `defeq2-str`)

`str_cv(q)` answers `(lo, ll, ty)`: every record holds its constant value at `q + 1` (`decCV`),
the twin's pure `toConstantVal`. `cv_call`: the memory unchanged, and the words.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

theorem strRdW {a : Array Word} {q w : Word} (h : a[q.toNat]? = some w) : rdW a q = w := by simp [rdW, h]

/-- The model of `str_cv`. -/
l_model strCv_spec (p : Prog) (hp : p.lookup "str_cv" = some strCvL)
  fns [hp ↦ strCvW]
  grind [arena_grind]

section calls
variable (p : Prog) (hp : StrLitProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
  {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
include hp

/-- **`str_cv` under `CoreS`**: the twin's `toConstantVal` at the decoded record, the memory
unchanged, and the words of the constant value. -/
theorem cv_call (_hS : CoreS dn m a vis fe M eb) {q : Word} {ci : IConstantInfo}
    (hci : decCI (erecP m) q.toNat = some ci)
    (h : callW p n "str_cv" [q] m = some (r, m')) :
    m' = m ∧
      hslice? (erecP m) (r.headD 0).toNat (r.tail.headD 0).toNat =
        some ci.toConstantVal.levelParams ∧
      ci.toConstantVal.levelParams.length = (r.tail.headD 0).toNat ∧
      ci.toConstantVal.type = decI (r.tail.tail.headD 0) ∧ HW (r.tail.tail.headD 0) := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (strCv_spec p hp.strCv n _ q) h
  simp only [strCvW, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, hm⟩ := hW
  simp only [erRdT_congr rfl rfl, List.headD_cons, List.tail_cons]
  obtain ⟨hsl, hlen, hty, hhw⟩ := decCV_rd (erRdOK m) (decCI_cvA hci)
  exact ⟨hm.symm, hsl, hlen, hty, hhw⟩

end calls

end L.Arena
