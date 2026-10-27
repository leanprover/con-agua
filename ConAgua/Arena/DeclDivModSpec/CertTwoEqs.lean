import ConAgua.Arena.DeclDivModSpec.EqAt1
import ConAgua.Census.Attr

/-!
# CertTwoEqs: `ConRon.Arena.certEq`, `ConRon.Arena.certGuard`, `ConRon.Arena.certHalves`, `ConRon.Arena.certTwoEqs`

The refinement theorems `certGuard_refines`, `certEq_refines`, `certHalves_refines`, `certTwoEqs_refines` and the lemmas only they use.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section nat
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

theorem StmtL.grow {m m' : Mem} {o l : Nat} {ss : List (List EIdx × EIdx)} (h : StmtL m o l ss)
    (hg : IWGrow m m') : StmtL m' o l ss := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.le_trans h1 hg.1, h2, fun j hj => ?_⟩
  obtain ⟨p, hp, hs⟩ := h3 j hj
  refine ⟨p, ?_, hs.grow hg⟩
  simp only [iwA] at hp ⊢; rw [hg.2.2.1 _ (by omega)]; exact hp

@[refines ConRon.Arena.certGuard]
theorem certGuard_refines (hD : DmProg2 p) (cx a b rv : Word) (cc : CertCtxA) :
    RefAM p "cert_guard" [cx, a, b, rv] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H a ∧ H b ∧ H rv)
      (certGuard cc (decE a) (decE b) (decE rv)) (KeepPost dn vis fe decW0E) :=
  (certGuard_ref hD cx a b rv cc).refAM

@[refines ConRon.Arena.certEq]
theorem certEq_refines (hD : DmProg2 p) (cx c rhs : Word) (cc : CertCtxA) :
    RefAM p "cert_eq" [cx, c, rhs] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H rhs)
      (certEq cc (decI c) (decE rhs)) (KeepPost dn vis fe decW0E) :=
  (certEq_ref hD cx c rhs cc).refAM

@[refines ConRon.Arena.certHalves]
theorem certHalves_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_halves" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certHalves cc (decI c)) (KeepPost dn vis fe decW0E) :=
  (certHalves_ref hD cx c cc).refAM

@[refines ConRon.Arena.certTwoEqs]
theorem certTwoEqs_refines (hD : DmProg2 p) (cx c h1 h2 r1 r2 : Word) (cc : CertCtxA) :
    RefAM p "cert_two_eqs" [cx, c, h1, h2, r1, r2]
      (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H h1 ∧ H h2 ∧ H r1 ∧ H r2)
      (certTwoEqs cc (decI c) (decE h1) (decE h2) (decE r1) (decE r2))
      (KeepPost dn vis fe decStmtL) :=
  (certTwoEqs_ref hD cx c h1 h2 r1 r2 cc).refAM

end nat

end L.Ind
