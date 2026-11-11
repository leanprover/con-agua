module

public import ConAgua.Arena.InstLPWalk
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.LdRd
public import Std.Tactic.BVDecide.Normalize.Prop
import all ConAgua.Arena.InstLP

@[expose] public section

/-!
# The `instLP` walk: the arm `lp_let`

The third child and the rebuild are `lp_let_tail`'s (`lpLetTail_spec`), so that this function has
the two-child arms' shape. Its model and spec are generated (`pfuel`: the spec at `exec p (n + 1)`,
the model at `n`); the model is the shape `ilwLetS` the refinement takes apart (`ilwLetW_eq`).
Split from `InstLPWalk.lean` for build parallelism.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model lpLet_spec (p : Prog) (hp : ILWProg p)
  fns [hp.le ↦ ilwLetW]
  specs [memoFindG_spec lpSch p _ hp.ilpf n, memoPutG_spec lpSch p _ hp.ilpp n,
    callW_spec p n "lp_go", callW_spec p n "lp_let_tail"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rd_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] pfuel

theorem ilwLetW_eq (p : Prog) (n : Nat) (m : Mem) (h ko kc vo vc fu : Word) :
    ilwLetW p n m h ko kc vo vc fu = ilwLetS p n m h (tfld m LET (tierW h) (idxW h) 0)
      (tfld m LET (tierW h) (idxW h) 1) (tfld m LET (tierW h) (idxW h) 2) ko kc vo vc fu := by
  rw [ilwLetW.eq_1]; unfold ilwLetS ilwProbe
  split <;> try rfl
  split <;> try rfl
  cases callW p n "lp_go" [tfld m LET (tierW h) (idxW h) 0, ko, kc, vo, vc, fu] m with
  | none => rfl
  | some q =>
    obtain ⟨x, m₁⟩ := q
    simp only [ilwLetW.k_lp_go]
    cases callW p n "lp_go" [tfld m LET (tierW h) (idxW h) 1, ko, kc, vo, vc, fu] m₁ with
    | none => rfl
    | some q =>
      obtain ⟨y, m₂⟩ := q
      simp only [ilwLetW.k_lp_go_2]
      cases callW p n "lp_let_tail" [h, tfld m LET (tierW h) (idxW h) 0, tfld m LET (tierW h) (idxW h) 1,
          tfld m LET (tierW h) (idxW h) 2, x.headD 0, y.headD 0, ko, kc, vo, vc, fu] m₂ with
      | none => rfl
      | some q =>
        obtain ⟨z, m₃⟩ := q
        simp only [ilwLetW.k_lp_let_tail, ilwLetW.k_ilp_put, ilwHd]
        exact ilwSetK_j1 h _ m₃

end L.Arena
