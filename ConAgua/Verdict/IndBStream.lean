import ConAgua.Arena.IndT.StreamRecs
/-!
# Error claim of `class_stream_recs`

`csr_ref`'s error half (`Arena/IndT/StreamRecs.lean`) as the `CoreSpecE` claim
`gen_rec_check_prep`'s error refinement takes.
-/

open ConRon.Arena
open ConRon.Bridge.Inductives (dRec)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`class_stream_recs`' error claim** (the hypotheses of `classStreamRecs_refinesC`). -/
theorem classStreamRecs_claim {p : Prog} {dn : NIdx → Option ConLeche.Name} {env : ConLeche.Env}
    (hq : KnotStageProg p) (henv : ConLeche.EnvWF env) (hV : ValProg p) (hApd : ApdF p)
    (hCrk : CrKeep p) (hG : VerdictCtxU p) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "class_stream_recs" = some classStreamRecsL) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (fe : IFEnv) (vis rcso rcsl : Word) (recs : List RecShape)
    (recsP : List ConLeche.RecShape) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hOK : RecsOK s₀.mem rcso.toNat rcsl.toNat (recs.map (·.cvR)))
    (hrecsP : recs.mapM (dRec a₀.store) = some recsP) :
    CoreSpecE p n "class_stream_recs" [vis, rcso, rcsl] (ConRon.Arena.classStreamRecs V fe recs) s₀ a₀ :=
  RefE.coreSpecE (csrE_spec p hV ha hc hsc hp n s₀ vis rcso rcsl) hG.nv hG
    (csr_ref hq henv hApd hCrk fe n hn s₀.mem a₀ vis rcso rcsl recs recsP hC hA hOK hrecsP)

end L.Ind
