import ConAgua.Verdict.WhnfIotaRecE
/-!
# `iota_index_ok`'s and `iota_rec_cmp`'s verdict claims

The error halves of `io_ref` (`Arena/WhnfIotaRefine2`) and `irCmp_ref` (`Arena/WhnfIotaRecRefine`):
`defeq_list`'s verdicts, that is the `defeq` slot's (`KnotUpToE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **`IotaIndexOkE`**: `iota_index_ok`'s verdicts are `defeq_list`'s. -/
theorem iotaIndexOkE_of (p : Prog) (hp : IotaProg' p) (hi1 : IotaInst1OK p)
    (hnv : closedNV p L.Checker.nvFns = true) : IotaIndexOkE p :=
  fun n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d mI rP cnP tyCtor mo mn xo xn margs idx hS hm4
      hebm hty hsm hsx htm htx =>
    RefE.coreSpecE (ioE_spec p hp.iotaIndexOk hp.defeqList (n + 1) s₀ mode vis d mI rP cnP tyCtor mo mn
      xo xn) hnv hkE (io_ref p hp hi1 n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d mI rP cnP tyCtor mo
      mn xo xn margs idx hS hm4 hebm hty hsm hsx htm htx)

/-- **`IotaRecCmpE`**: `iota_rec_cmp`'s verdicts are `defeq_list`'s. -/
theorem iotaRecCmpE_of (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p) (hw : WhnfCallees p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hnv : closedNV p L.Checker.nvFns = true) :
    IotaRecCmpE p :=
  fun n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so rl mo mn sn lps rule args margs hS
      hm4 hebm hus hlps hrule hsa hsat hmI hsm hsmt hcpm =>
    RefE.coreSpecE (irCmpE_spec p hp.cmp (n + 1) s₀ mode vis d us recP so rl mo) hnv hkE
      (irCmp_ref p hp hc hw hEI hER n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so rl mo mn sn
        lps rule args margs hS hm4 hebm hus hlps hrule hsa hsat hmI hsm hsmt hcpm)

end L.Arena
