import ConAgua.Verdict.IndA6
import ConAgua.Verdict.PosKnotE
import ConAgua.Verdict.PosTopE5
import ConAgua.Verdict.IndsE7
import ConAgua.Verdict.BlkE1
import ConAgua.Verdict.BlkE4
import ConAgua.Verdict.KnotAllE

/-!
# `check_ind_decl`'s error refinement with the pass's and the tail's callees discharged (lane
`verdicts-b`, helper `ia2`)

`cid_claim2`: `cid_claim` with `check_block_inds`, `check_block_ctors`, `check_block_classes`,
`check_block_positivity`, `nest_seeds` and the tail (`TailG`) proved
(`IndsE*`, `BlkE*`, `PosTopE*`, the positivity walk `nbRef_all`; the core stubs and `whnf_top`
from the error knot). Left: `classes_nfs` (`ClassesNfsE`), the `indB` callees (`IndBE.lean`,
`CheckStructProjTableRE`), and `check_basis_decl`/`check_constant_val` (`IndA8.lean` discharges
them; it waits for `DeclHdrE`).
-/

open ConRon.Arena


namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- What the positivity walk's error claims assume, from the program. -/
theorem nbG_prog {p : Prog} (hkp : KnotStageProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true) : NbG p :=
  ⟨hnv, hkp.toKnotTopProg.coreStubsE hnv, whnfTop_stageE hkp.whnfTop hkp.knotOK (KnotAllProg.knotE_all hkp.knot hnv)⟩

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
    (hCBD : CheckBasisDeclE p) (eCcv : CheckConstantValE p) (hU : UceProg p)
    (hNfs : ∀ dn vis fe env, ConLeche.EnvWF env → ClassesNfsE p dn vis fe env)
    (eSum : CheckSumTeleE p) (eSC : CheckSumCtorsE p) (eSF : CheckStructFieldSortsIE p)
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
    {fsH fsM fsMc : List FnName} (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true)
    (hfH : "check_block_tables" ∈ fsH) (hclM : closedA p maFreeA maFreeC fsM = true)
    (hfM : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ fsM)
    (hclMc : closedA p mcFreeA mcFreeC fsMc = true) (hfMc : "check_block" ∈ fsMc)
    (hlpd : BlockLpsDn dn block) :
    ErrClaim (checkDecl V pins fe (.indDecl block w.toNat)) a e := by
  have hcE : CoreStubsE p := hkp.toKnotTopProg.coreStubsE hnv
  have hG := nbG_prog hkp hnv
  exact cid_claim hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz P hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT hclC hfC
    hkP hkt hkr hnv hCBD ⟨⟨⟨hnv, hcE⟩, hU⟩, hNfs, eSF⟩
    (checkBlockIndsE_claim ⟨hnv, hcE, eCcv, eSum⟩) (checkBlockCtorsE_claim hnv eSC)
    (checkBlockClassesE_claim ⟨hnv, hcE⟩) (checkBlockPositivityE_claim hG eSF)
    (nestSeedsE_claim hG) hn hdn he hT hfold hblk hb hden hM hfB hfRc hclH hfH hclM hfM hclMc hfMc hlpd

end L.Ind
