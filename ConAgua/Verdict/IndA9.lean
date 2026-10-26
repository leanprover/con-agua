import ConAgua.Verdict.IndA6
import ConAgua.Verdict.PosAllE
import ConAgua.Verdict.PosTopE5
import ConAgua.Verdict.IndsE7
import ConAgua.Verdict.BlkE1
import ConAgua.Verdict.BlkE2
import ConAgua.Verdict.BlkE3
import ConAgua.Verdict.BlkE4
import ConAgua.Verdict.KnotAllE

/-!
# `check_ind_decl`'s error refinement with the pass's and the tail's callees discharged (lane
`verdicts-b`, helper `ia2`)

`cid_claim2`: `cid_claim` with `check_block_inds`, `check_block_ctors`, `check_block_classes`,
`check_block_positivity`, `nest_seeds`, `check_block_idx_sorts`, `check_block_tables` proved
(`IndsE*`, `BlkE*`, `PosTopE*`, the positivity walk `nbOKE_all`; the core stubs and `whnf_top`
from the error knot). Left: `gen_rec_check` (`GenRecCheckE`), the `indB` callees (`IndBE.lean`,
`CheckStructProjTableRE`), and `check_basis_decl`/`check_constant_val` (`IndA8.lean` discharges
them; it waits for `DeclHdrE`).
-/

open ConRon.Arena


namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The positivity walk's claims for every well-formed environment, from the program. -/
theorem nbOKE_prog {p : Prog} (P : CidProg p) (hkp : KnotStageProg p) (hIlpf : IlpfF p)
    (hLC : LvlCacheProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true) :
    ∀ dn vis fe env, ConLeche.EnvWF env → ∀ n, n ≤ 2 ^ 62 → NbOKE p dn vis fe env n :=
  fun _ _ _ _ henv => nbOKE_all P.cb.pass.pos.rs.nb hkp hIlpf hLC hnv
    (hkp.toKnotTopProg.coreStubsE hnv)
    (whnfTop_stageE hkp.whnfTop (KnotAllProg.knotE_all hkp.knot hnv)) henv

/-- **`check_ind_decl`'s error refinement**, the pass and the tail discharged. -/
theorem cid_claim2 {p : Prog} (hkp : KnotStageProg p) (hV : ValProg p)
    (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
    (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p) (hLz : LzcF p)
    (P : CidProg p) {fs fs2 fsR fsT fsC : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC)
    (hkP : ∀ f ∈ passKeepCalleesC, AbsKeep p f) (hkt : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hkr : AbsKeep p "block_raw_rec")
    (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hCBD : CheckBasisDeclE p) (eCcv : CheckConstantValE p) (eGrc : GenRecCheckE p)
    (eSum : CheckSumTeleE p) (eSC : CheckSumCtorsE p) (eSF : CheckStructFieldSortsIE p)
    (eTbl : CheckStructProjTableRE p) (eKey : ClassKeyOfE p) (eClm : ClassMajorsE p)
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
  have hcE : CoreStubsE p := hkp.toKnotTopProg.coreStubsE hnv
  have hNbE := nbOKE_prog P hkp hIlpf hLC hnv
  have hNit : ∀ dn vis fe env, ConLeche.EnvWF env → NitE p dn vis fe env :=
    fun dn vis fe env _ => nitE_all P.cb.pass.pos.rs.nb hkp hIlpf hLC hnv dn vis fe env
  exact cid_claim hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz P hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT hclC hfC
    hkP hkt hkr hnv hCBD eCcv (checkBlockIdxSortsE_claim hnv eSF) eGrc (checkBlockTablesE_claim hnv eTbl)
    (checkBlockIndsE_claim hnv hcE eCcv eSum) (checkBlockCtorsE_claim hnv eSC)
    (checkBlockClassesE_claim hnv eKey eClm) (checkBlockPositivityE_claim hnv hNbE eSF)
    (nestSeedsE_claim hnv hNbE hNit) hn hdn he hT hfold hblk hb hden hM hfB hfRc hclH hfH hclM hfM hlpd

end L.Ind
