import ConAgua.Arena.Knot
import ConAgua.Arena.IndIface
import ConAgua.Arena.ExprMk
import ConAgua.Arena.Abs1Spec
import ConAgua.Arena.ArRangeSpec
import ConAgua.Arena.InstListSpec
import ConAgua.Arena.HasFvar
import ConAgua.Arena.InferFieldSort
import ConAgua.Arena.PropRead
import ConAgua.Arena.StrLit

/-!
# Phases 6–7 close over their callees (lane `defeq`)

`defeqInferFns` and every function it calls: the real L functions where they exist (the
callees' own decls, so the arity check is against the real parameter counts), `abort` stubs of
the right arity for the callees with no L code yet. `FunDecl.wf` checks every call resolves with
the right number of arguments, at most six results, frame sizes; the names are distinct.
-/

namespace L.Arena

open L.Ind in
/-- The callees outside this lane: real decls, or stubs (`L.Ind.stub k`, `abort`). -/
def defeqExtFns : Prog :=
  [("const_e", constEL), ("const_ty_at", constTyAtL), ("env_find", envFindL),
   ("eta_projs", etaProjsL), ("e_view", eView), ("get_app_args", getAppArgsL),
   ("get_app_fn", stub 1), ("head_and_args", headAndArgsL),
   ("in_find", memoFindG inSch), ("in_put", memoPutG inSch),
   ("io_find", memoFindG ioSch), ("io_put", memoPutG ioSch),
   ("de_find", memoFindG deSch), ("de_put", memoPutG deSch),
   ("intern_fvar", internFVar), ("intern_imax", internImax), ("intern_sort", internSort),
   ("intern_succ", internSucc), ("limbs_eq", limbsEq), ("ls_node", lsNode),
   ("lvl_eq_c", lvlEqCL), ("lv_node", lvNode), ("lvls_eq_c", lvlsEqCL), ("mk_app", mkApp), ("mk_forall", mkForall),
   ("nat_lit_supported", natLitSupportedL), ("nat_pred_lit", natPredLit), ("pin_at", pinAtL),
   ("pin_word", pinWordL), ("proof_irrel", proofIrrelL), ("reduce_nat", reduceNatL),
   ("reduce_proj_core", reduceProjCoreL), ("reserved_contains_w", reservedContainsL),
   ("tower_slots_all", towerSlotsAllL), ("unfold_definition", unfoldDefinitionL),
   ("whnf", whnfL), ("whnf_core", whnfCoreL),
   -- no L code yet
   ("abs_entry", absEntry), ("ar_entry", arEntry), ("inst_list", instListL), ("has_fvar", hasFvarL),
   ("field_sort_zero", fieldSortZeroL),
   ("find_proj", stub 3), ("inst1", instEntry),
   ("inst_lp", stub 4), ("is_proof_fast", isProofFastL), ("not_proof_fast", notProofFastL),
   ("str_lit_ctor", strLitCtorL), ("str_lit_supported", strLitSupportedL)]

/-- Every function of phases 6–7 is well formed in the program of it and its callees: every
call resolves, with the right arity (the callees' own bodies are checked in their lanes); the
names are distinct. -/
theorem defeqInferFns_wf :
    (defeqInferFns.all fun (_, fd) =>
      L.Compiler.FunDecl.wf (defeqInferFns ++ defeqExtFns) L.Ind.indTab fd) = true ∧
    decide ((defeqInferFns ++ defeqExtFns).map (·.1)).Nodup = true :=
  L.Compiler.Prog.funsWf_of_fast (by decide +kernel)

end L.Arena
