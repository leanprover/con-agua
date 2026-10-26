import ConAgua.Verdict.IndA3
import ConAgua.Verdict.IndA4
import ConAgua.Verdict.IndA5
import ConAgua.Verdict.IndA7

/-!
# `check_ind_decl`'s error refinement, assembled (lane `verdicts-b`, helper `ia`)

`cid_claim`: the inductive arm of `checkDecl`, a failing call of `check_ind_decl` of class `1`/`2`
claims the twin's `checkDecl` fails with that class, under the hypotheses of `cidW_okC` and the
error claims of the leaves of the arm that are not proved here (the callee hypotheses below, each
in the shape of the callee's ok refinement): `check_basis_decl`, `check_constant_val`,
`check_block_idx_sorts`, `gen_rec_check`, `check_block_tables`, `check_block_inds`,
`check_block_ctors`, `check_block_classes`, `check_block_positivity`, `nest_seeds`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hkp : KnotStageProg p) (hV : ValProg p)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p) (hLz : LzcF p)

include hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz in
/-- **`check_ind_decl`'s error refinement** (the shape of `cidW_okC`; the callees' claims as
hypotheses). -/
theorem cid_claim (P : CidProg p) {fs fs2 fsR fsT fsC : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC)
    (hkP : ∀ f ∈ passKeepCalleesC, AbsKeep p f) (hkt : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hkr : AbsKeep p "block_raw_rec")
    (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hCBD : CheckBasisDeclE p) (eCcv : CheckConstantValE p) (eIdx : CheckBlockIdxSortsE p)
    (eGrc : GenRecCheckE p) (eTab : CheckBlockTablesE p) (eInds : CheckBlockIndsE p)
    (eCtors : CheckBlockCtorsE p) (eCls : CheckBlockClassesE p) (ePos : CheckBlockPositivityE p)
    (eSeeds : NestSeedsE p)
    {n : Nat} (hn : n ≤ 2 ^ 62)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} {o l w : Word} {block : List IConstantInfo}
    {pins : List INatOpPinSet}
    {env : ConLeche.Env} {e : Err}
    (he : callE p n "check_ind_decl" [vis, o, l, w] m = .error e) (hT : StageT dn vis fe m a)
    (hfold : ConRon.Bridge.FoldOK V env fe a)
    (hblk : DecB (fun m => decEBlk dn m o.toNat l.toNat) m block) (hb : o.toNat + l.toNat ≤ erTop m)
    (hden : ∃ x, Frontend.denoteDecl a.store (.indDecl block w.toNat) = some x) (hM : IndMemos m)
    (hfB : "check_basis_decl" ∈ fsC) (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR)
    {fsH fsM : List FnName} (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true)
    (hfH : "check_block_tables" ∈ fsH) (hclM : closedA p maFreeA maFreeC fsM = true)
    (hfM : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ fsM)
    (hlpd : BlockLpsDn dn block) :
    ErrClaim (checkDecl V pins fe (.indDecl block w.toNat)) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (cidE_spec p P.cid n ⟨m, Locals.init []⟩ vis o l w) he
    (Err.code_ne_of_cls hk0)
  simp only at he
  exact cidE_claim hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz P hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT hclC hfC hkP hkt hkr
    hnv hCBD
    (checkBlockE_claim hnv (checkBlockPassE_claim hnv eInds eCtors eCls ePos eSeeds)
      (checkBlockTailE_claim hnv eIdx (checkBlockRecE_claim eGrc) eTab))
    (checkShapelessE_claim eCcv) hn hdn he hT hfold hblk hb hden hM hfB hfRc hclH hfH hclM hfM hlpd

end sims

end L.Ind
