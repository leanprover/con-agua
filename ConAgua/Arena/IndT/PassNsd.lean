module

public import ConAgua.Arena.IndT.PassCS
public import ConAgua.Arena.IndT.PosAll
public import ConAgua.Verdict.PosTopE4
import ConAgua.Arena.BasisBlockC

@[expose] public section

/-!
# `nest_seeds`' contract from the verdict area's `nsd_ref` (lane `ronsync2`, stage 3)

`nsdRefS_of`: `NsdRefS` from `Verdict/PosTopE4`'s `nsd_ref` through the call, the block's
refinements by `nbRef_all`; the memos by `IndMemos.ofCall`.
-/

noncomputable section

open ConRon.Arena

namespace L.Ind

open L.Arena

section
variable {p : Prog} {dn : NIdx → Option ConLeche.Name}

/-- **`nest_seeds`' contract** (`NsdRefS`): `nsd_ref` through the call (its errors under `NbG`,
from `VerdictCtxU` and `whnf_top`'s claim), the block's refinements by `nbRef_all`. -/
theorem nsdRefS_of (L : RsLook p) (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p)
    (hF : FtProg p) (hFk : FkcProg p) (hWt : WhnfTopE p) (hK : WmKeep p "nest_seeds") : NsdRefS (VerdictCtxU p) p dn := by
  intro n hn vis fe env m a ctx so sl nsw c ctxP seeds ksP ns nsP hB henv hU hhi hsd hns hctx hc hks hnsP hw
  have h := RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩) (G := VerdictCtxU p)
    (nsdE_spec p L n _ vis ctx so sl nsw) (fun hG => hG.nv)
    (RefE.weakenG (fun hG => (⟨hG.nv, hG.core, hWt⟩ : NbG p))
      (nsd_ref L hq hIlpf hLC dn vis fe henv hF (nbRef_all L.nb hq hIlpf hLC hF hFk henv) ctx c hc n hn m a so sl
        nsw seeds ns ksP nsP hB.c hU hhi hsd.2.1 hsd.2.2.2 hns hB.ind.stage.pos hB.abs hctx hks hnsP hw))
  refine RefE.callOk h fun ⟨r, m'⟩ x a' hc' hR => ?_
  obtain ⟨s', hs', -, hR⟩ := hR
  simp only at hs'; subst hs'
  exact ⟨⟨hR.stage, IndMemos.ofCall hK (callW_of_callE hc') hB.ind hR.pos hR.abs, hR.abs⟩, hR.grow, hR.ns⟩

end

end L.Ind

end
