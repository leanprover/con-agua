module

import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.LdRd
public import Std.Tactic.BVDecide.Normalize.Prop
public import ConAgua.Arena.InstLPWalk
import all ConAgua.Arena.InstLP

@[expose] public section

/-!
# The `instLP` walk: the arms `lp_app`, `lp_lam`, `lp_forall`

Their models and specs are generated (`pfuel`: the spec at `exec p (n + 1)`, the model at `n`); each
model is the shape `ilwBinS` the refinement takes apart (`ilwAppW_eq`, `ilwLamW_eq`,
`ilwForallW_eq`). Split from `InstLPWalk.lean` for build parallelism.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model lpApp_spec (p : Prog) (hp : ILWProg p)
  fns [hp.app ↦ ilwAppW]
  specs [memoFindG_spec lpSch p _ hp.ilpf n, memoPutG_spec lpSch p _ hp.ilpp n,
    callW_spec p n "lp_go", callW_spec p n "mk_app"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rd_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] pfuel

theorem ilwAppW_eq (p : Prog) (n : Nat) (m : Mem) (h ko kc vo vc fu : Word) :
    ilwAppW p n m h ko kc vo vc fu = ilwBinS p n "mk_app" m h (tfld m APP (tierW h) (idxA h) 0)
      (tfld m APP (tierW h) (idxA h) 1) ko kc vo vc fu := by
  rw [ilwAppW.eq_1]; unfold ilwBinS ilwProbe
  split <;> try rfl
  split <;> try rfl
  cases callW p n "lp_go" [tfld m APP (tierW h) (idxA h) 0, ko, kc, vo, vc, fu] m with
  | none => rfl
  | some q =>
    obtain ⟨x, m₁⟩ := q
    simp only [ilwAppW.k_lp_go]
    cases callW p n "lp_go" [tfld m APP (tierW h) (idxA h) 1, ko, kc, vo, vc, fu] m₁ with
    | none => rfl
    | some q =>
      obtain ⟨y, m₂⟩ := q
      simp only [ilwAppW.k_lp_go_2, ilwRb]
      split
      · simp only [ilwAppW.j1, ilwAppW.k_ilp_put]; exact ilwSetK_j1 h h m₂
      · cases callW p n "mk_app" [x.headD 0, y.headD 0] m₂ with
        | none => rfl
        | some q =>
          obtain ⟨z, m₃⟩ := q
          simp only [ilwAppW.k_mk_app, ilwChk]
          split
          · rfl
          · simp only [ilwAppW.j1, ilwAppW.k_ilp_put]; exact ilwSetK_j1 h _ m₃

l_model lpLam_spec (p : Prog) (hp : ILWProg p)
  fns [hp.lam ↦ ilwLamW]
  specs [memoFindG_spec lpSch p _ hp.ilpf n, memoPutG_spec lpSch p _ hp.ilpp n,
    callW_spec p n "lp_go", callW_spec p n "mk_lam"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rd_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] pfuel

theorem ilwLamW_eq (p : Prog) (n : Nat) (m : Mem) (h ko kc vo vc fu : Word) :
    ilwLamW p n m h ko kc vo vc fu = ilwBinS p n "mk_lam" m h (tfld m LAM (tierW h) (idxW h) 0)
      (tfld m LAM (tierW h) (idxW h) 1) ko kc vo vc fu := by
  rw [ilwLamW.eq_1]; unfold ilwBinS ilwProbe
  split <;> try rfl
  split <;> try rfl
  cases callW p n "lp_go" [tfld m LAM (tierW h) (idxW h) 0, ko, kc, vo, vc, fu] m with
  | none => rfl
  | some q =>
    obtain ⟨x, m₁⟩ := q
    simp only [ilwLamW.k_lp_go]
    cases callW p n "lp_go" [tfld m LAM (tierW h) (idxW h) 1, ko, kc, vo, vc, fu] m₁ with
    | none => rfl
    | some q =>
      obtain ⟨y, m₂⟩ := q
      simp only [ilwLamW.k_lp_go_2, ilwRb]
      split
      · simp only [ilwLamW.j1, ilwLamW.k_ilp_put]; exact ilwSetK_j1 h h m₂
      · cases callW p n "mk_lam" [x.headD 0, y.headD 0] m₂ with
        | none => rfl
        | some q =>
          obtain ⟨z, m₃⟩ := q
          simp only [ilwLamW.k_mk_lam, ilwChk]
          split
          · rfl
          · simp only [ilwLamW.j1, ilwLamW.k_ilp_put]; exact ilwSetK_j1 h _ m₃

l_model lpForall_spec (p : Prog) (hp : ILWProg p)
  fns [hp.fa ↦ ilwForallW]
  specs [memoFindG_spec lpSch p _ hp.ilpf n, memoPutG_spec lpSch p _ hp.ilpp n,
    callW_spec p n "lp_go", callW_spec p n "mk_forall"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rd_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] pfuel

theorem ilwForallW_eq (p : Prog) (n : Nat) (m : Mem) (h ko kc vo vc fu : Word) :
    ilwForallW p n m h ko kc vo vc fu = ilwBinS p n "mk_forall" m h (tfld m FORALL (tierW h) (idxW h) 0)
      (tfld m FORALL (tierW h) (idxW h) 1) ko kc vo vc fu := by
  rw [ilwForallW.eq_1]; unfold ilwBinS ilwProbe
  split <;> try rfl
  split <;> try rfl
  cases callW p n "lp_go" [tfld m FORALL (tierW h) (idxW h) 0, ko, kc, vo, vc, fu] m with
  | none => rfl
  | some q =>
    obtain ⟨x, m₁⟩ := q
    simp only [ilwForallW.k_lp_go]
    cases callW p n "lp_go" [tfld m FORALL (tierW h) (idxW h) 1, ko, kc, vo, vc, fu] m₁ with
    | none => rfl
    | some q =>
      obtain ⟨y, m₂⟩ := q
      simp only [ilwForallW.k_lp_go_2, ilwRb]
      split
      · simp only [ilwForallW.j1, ilwForallW.k_ilp_put]; exact ilwSetK_j1 h h m₂
      · cases callW p n "mk_forall" [x.headD 0, y.headD 0] m₂ with
        | none => rfl
        | some q =>
          obtain ⟨z, m₃⟩ := q
          simp only [ilwForallW.k_mk_forall, ilwChk]
          split
          · rfl
          · simp only [ilwForallW.j1, ilwForallW.k_ilp_put]; exact ilwSetK_j1 h _ m₃

end L.Arena
