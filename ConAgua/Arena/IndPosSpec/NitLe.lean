import ConAgua.Arena.IndPosSpec.NestOccAny

/-!
# NitLe

`NitLe`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_inst_type` refines `nestInstType` -/

/-- **What `nest_inst_type`'s `lvl_eq_fueled` call (read through `cR`) must do**, from the
start `(m, a)`: given the calls and the twin's steps before it (`nest_inst_type_ty`, `pi_binders`,
`nest_occ_any`; `stripPis`, `instLPFast`, `instPisWith`, `piBinders`, the result's sort), refine
`liftFueled (← lvlEq? s ctx.sort)` and establish `Q` (the stubs: `nitLe_stub`; the real call
under `StageC`: `IndT/PosNit.lean`). -/
def NitLe (cR : CallM) (k : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (ctx hi key : Word) (c : NestCtx) (kk : NestKey) (Q : Mem → AState → Prop) (m : Mem) (a : AState) :
    Prop :=
  ∀ (m1 m2 m3 m4 : Mem) (r1 rs r3 r4 : List Word) (cv : IConstantVal) (caps : IIndCaps)
    (q : List EIdx × EIdx) (a3 a4 a5 : AState) (tl ty : EIdx) (bs : List EIdx) (e : EIdx) (uw : Word),
    ntyWf cR k m vis key = some (r1, m1) → AFr m m1 → piBW k m1 CWF (r1.headD 0) = some (rs, m2) →
    noaW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi
      (rs.headD 0) (rs.getD 1 0) = some (r3, m3) →
    fe.find? kk.cname = some (.indInfo cv caps) →
    (stripPis kk.ds.length cv.type).run a = .ok (some q, a3) →
    (instLPFast coreWalkFuel cv.levelParams kk.lvls cv.type).run a3 = .ok (tl, a4) →
    (ConRon.Arena.instPisWith kk.ds tl).run a4 = .ok (some ty, a5) →
    (ConRon.Arena.piBinders coreWalkFuel ty).run a5 = .ok ((bs, e), a5) →
    (view e).run a5 = .ok (.sort (decI uw), a5) →
    StageR dn vis fe m3 a5 → IWGrow m m3 → H uw → H (rdW (m3.arr64 IW) (ctx + 9)) →
    decI (rdW (m3.arr64 IW) (ctx + 9)) = c.sort →
    lveC cR k m3 uw (rdW (m3.arr64 IW) (ctx + 9)) = some (r4, m4) →
    ∃ b a6, (lvlEq? (decI uw) c.sort).run a5 = .ok (some b, a6) ∧ StageR dn vis fe m4 a6 ∧
      IWGrow m3 m4 ∧ MFr [] [] m3 m4 ∧ r4.headD 0 = (if b then 1 else 0) ∧ Q m4 a6

end L.Ind

end
