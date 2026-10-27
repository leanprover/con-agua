import ConAgua.Arena.DeclDivModSpec.EqAt1
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# CertDivModEqs: `ConRon.Arena.certDivModEqs`, `ConRon.Arena.certDivModGuards`, `ConRon.Arena.certDivMod`, `ConRon.Arena.certGcd`, `ConRon.Arena.certLand`, `ConRon.Arena.certLorRhs`, `ConRon.Arena.certLor`, `ConRon.Arena.certRecRhs`, `ConRon.Arena.certShiftLeft`, `ConRon.Arena.certShiftRight`, `ConRon.Arena.certXorRhs`, `ConRon.Arena.certXor`, `ConRon.Arena.divModCertStmtsAt`, `ConRon.Arena.divModCertStmts`

The refinement theorems `certLorRhs_refines`, `certXorRhs_refines`, `certGcd_refines`, `certShiftLeft_refines`, `certShiftRight_refines`, `certLand_refines`, `certLor_refines`, `certXor_refines`, `certRecRhs_refines`, `certDivModEqs_refines`, `certDivModGuards_refines`, `certDivMod_refines`, `divModCertStmtsAt_refines`, `divModCertStmts_refines` and the lemmas only they use.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section nat
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-! ## `div_mod_cert_stmts` -/

/-- **`div_mod_cert_stmts` is its model `divModCertStmtsW`** (generated). -/
l_model divModCertStmts_specW (p : Prog) (hp : p.lookup "div_mod_cert_stmts" = some divModCertStmtsL)
  fns [hp ↦ divModCertStmtsW list]
  specs [callW_spec p n "cert_ctx", callW_spec p n "div_mod_cert_stmts_at"]
  grind [arena_grind] finish [ntBW] gen 20 heartbeats 1600000 bind ntBW instances 10000

theorem divModCertStmts_ref (hD : DmProg2 p) (c : Word) :
    CallRef p "div_mod_cert_stmts" [c] (fun m s => StageR dn vis fe m s ∧ H c)
      (divModCertStmts (decI c)) (KeepPost dn vis fe decStmtL) := by
  refine CallRef.of_sim (M := fun k mq => divModCertStmtsW p (k + 1) mq c)
    (fun k s₀ => divModCertStmts_specW p hD.lDivModCertStmts (k + 1) s₀ c) fun k m s ⟨hS, hc⟩ => ?_
  rw [divModCertStmtsW.arm1]; unfold divModCertStmts
  refine Sim.ntB ((certCtx_ref hD).sim hS) fun r1 x1 m1 a1 ⟨hS1, hg1, hctx⟩ => ?_
  exact (divModCertStmtsAt_ref hD (r1.headD 0) c x1).simPair ⟨hS1, hctx, hc⟩ hg1

@[refines ConRon.Arena.certLorRhs]
theorem certLorRhs_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_lor_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certLorRhs cc (decI c)) (KeepPost dn vis fe decW0E) :=
  (certLorRhs_ref hD cx c cc).refAM

@[refines ConRon.Arena.certXorRhs]
theorem certXorRhs_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_xor_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certXorRhs cc (decI c)) (KeepPost dn vis fe decW0E) :=
  (certXorRhs_ref hD cx c cc).refAM

@[refines ConRon.Arena.certGcd]
theorem certGcd_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_gcd" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certGcd cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certGcd_ref hD cx c cc).refAM

@[refines ConRon.Arena.certShiftLeft]
theorem certShiftLeft_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_shift_left" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certShiftLeft cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certShiftLeft_ref hD cx c cc).refAM

@[refines ConRon.Arena.certShiftRight]
theorem certShiftRight_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_shift_right" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certShiftRight cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certShiftRight_ref hD cx c cc).refAM

@[refines ConRon.Arena.certLand]
theorem certLand_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_land" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certLand cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certLand_ref hD cx c cc).refAM

@[refines ConRon.Arena.certLor]
theorem certLor_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_lor" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certLor cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certLor_ref hD cx c cc).refAM

@[refines ConRon.Arena.certXor]
theorem certXor_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_xor" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certXor cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certXor_ref hD cx c cc).refAM

@[refines ConRon.Arena.certRecRhs]
theorem certRecRhs_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_rec_rhs" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certRecRhs cc (decI c)) (KeepPost dn vis fe decW0E) :=
  (certRecRhs_ref hD cx c cc).refAM

@[refines ConRon.Arena.certDivModEqs]
theorem certDivModEqs_refines (hD : DmProg2 p) (cx c h1 h2 h3 h4 recRhs baseRhs : Word) (cc : CertCtxA) :
    RefAM p "cert_div_mod_eqs" [cx, c, h1, h2, h3, h4, recRhs, baseRhs]
      (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H h1 ∧ H h2 ∧ H h3 ∧ H h4 ∧
        H recRhs ∧ H baseRhs)
      (certDivModEqs cc (decI c) (decE h1) (decE h2) (decE h3) (decE h4) (decE recRhs) (decE baseRhs))
      (KeepPost dn vis fe decStmtL) :=
  (certDivModEqs_ref hD cx c h1 h2 h3 h4 recRhs baseRhs cc).refAM

@[refines ConRon.Arena.certDivModGuards]
theorem certDivModGuards_refines (hD : DmProg2 p) (cx c recRhs baseRhs : Word) (cc : CertCtxA) :
    RefAM p "cert_div_mod_guards" [cx, c, recRhs, baseRhs] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c ∧ H recRhs ∧ H baseRhs)
      (certDivModGuards cc (decI c) (decE recRhs) (decE baseRhs)) (KeepPost dn vis fe decStmtL) :=
  (certDivModGuards_ref hD cx c recRhs baseRhs cc).refAM

@[refines ConRon.Arena.certDivMod]
theorem certDivMod_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "cert_div_mod" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (certDivMod cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (certDivMod_ref hD cx c cc).refAM

@[refines ConRon.Arena.divModCertStmtsAt]
theorem divModCertStmtsAt_refines (hD : DmProg2 p) (cx c : Word) (cc : CertCtxA) :
    RefAM p "div_mod_cert_stmts_at" [cx, c] (fun m s => StageR dn vis fe m s ∧ CertCtxR m cx cc ∧ H c)
      (divModCertStmtsAt cc (decI c)) (KeepPost dn vis fe decStmtL) :=
  (divModCertStmtsAt_ref hD cx c cc).refAM

@[refines ConRon.Arena.divModCertStmts]
theorem divModCertStmts_refines (hD : DmProg2 p) (c : Word) :
    RefAM p "div_mod_cert_stmts" [c] (fun m s => StageR dn vis fe m s ∧ H c)
      (divModCertStmts (decI c)) (KeepPost dn vis fe decStmtL) :=
  (divModCertStmts_ref hD c).refAM

end nat

end L.Ind
