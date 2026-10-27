import ConAgua.Arena.IndPosSpec.UCtx

/-!
# WCtx

`WCtx`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The walk's fixed context -/

/-- The walk's fixed context at a memory: the block's context record, the frame stack, its
`hiAt` below `2^64`. -/
structure WCtx (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (ctx po pl : Word)
    (c : NestCtx) (prog : List NestHole) : Prop where
  u : UCtx dn vis fe m ctx c
  hs : HSl m po.toNat pl.toNat prog
  hb : c.hiAt pl.toNat < 2 ^ 64

end L.Ind

end
