import ConAgua.Verdict.WhnfModels7E

/-!
# The generated models of `stuck_irrel`, `stuck_str` and `defeq_body`

Generated `unified` models only, apart from their refinements (`DefEqStuckIrrel.lean`,
`DefEqStuckStr.lean`, `DefEqBody.lean`): they need the code and their callees' models
(`Verdict/WhnfModels7E.lean`), not the knot's refinements, so they build beside the `defeq` chain
instead of on it.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **`stuck_irrel`'s model, both outcomes** (generated; `struct_eta_cert` and `struct_unit_cert`
by their unified models, `proof_irrel` through its run). -/
l_model siE_spec (p : Prog) (hf : p.lookup "stuck_irrel" = some stuckIrrelL)
    (hc : p.lookup "struct_eta_cert" = some structEtaCertL)
    (hw : p.lookup "struct_eta_cert_with" = some structEtaCertWithL)
    (hb : p.lookup "struct_eta_cert_wtb" = some structEtaCertWtbL)
    (hg : p.lookup "struct_eta_cert_go" = some structEtaCertGoL)
    (ht : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL)
    (hu : p.lookup "struct_unit_cert" = some structUnitCertL)
    (hh : p.lookup "struct_unit_head" = some structUnitHeadL)
    (hut : p.lookup "struct_unit_tail" = some structUnitTailL)
  fns [hf ↦ siE list]
  specs [secE_spec p hc hw hb hg ht n, sucE_spec p hu hh hut n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`stuck_str`'s model, both outcomes** (generated; the pins and the string-literal callees
lifted, `stuck_irrel` by its unified model, the `defeq` slot through its run). -/
l_model strE_spec (p : Prog) (hf : p.lookup "stuck_str" = some stuckStrL)
    (hi : p.lookup "stuck_irrel" = some stuckIrrelL)
    (hc : p.lookup "struct_eta_cert" = some structEtaCertL)
    (hw : p.lookup "struct_eta_cert_with" = some structEtaCertWithL)
    (hb : p.lookup "struct_eta_cert_wtb" = some structEtaCertWtbL)
    (hg : p.lookup "struct_eta_cert_go" = some structEtaCertGoL)
    (ht : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL)
    (hu : p.lookup "struct_unit_cert" = some structUnitCertL)
    (hh : p.lookup "struct_unit_head" = some structUnitHeadL)
    (hut : p.lookup "struct_unit_tail" = some structUnitTailL)
  fns [hf ↦ strE list]
  specs [callW_spec p n "pin_word", callW_spec p n "pin_at", callW_spec p n "str_lit_supported",
    callW_spec p n "str_lit_ctor", siE_spec p hi hc hw hb hg ht hu hh hut n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_tagE] heartbeats 1000000
  unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`defeq_body`'s model, both outcomes** (generated; `is_bool_true` and `has_fvar` lifted, the
other callees through their runs). -/
l_model bodyE_spec (p : Prog) (hf : p.lookup "defeq_body" = some defeqBodyL)
  fns [hf ↦ bodyE list]
  specs [callW_spec p n "is_bool_true", callW_spec p n "has_fvar"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
