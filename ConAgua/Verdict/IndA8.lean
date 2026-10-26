import ConAgua.Verdict.IndA9
import ConAgua.Verdict.DeclBasisE
import ConAgua.Verdict.DeclValsE

/-!
# `check_ind_decl`'s leaf hypotheses `CheckBasisDeclE`, `CheckConstantValE` discharged (lane
`verdicts-b`, helper `ia2`)

From `cbdE_okT` (DeclBasisE.lean) and `ccvE_okT` (DeclValsE.lean, under `CoreStubsE`). `cid_claim3`:
`check_ind_decl`'s claim from `GenRecCheckE` and the `indB` callees' claims only.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

theorem checkBasisDeclE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) :
    CheckBasisDeclE p :=
  fun hB hC hR hpa hp _n _m _a _dn hdn _fe _vis _k hk hS hQ _e hc =>
    cbdE_okT hB hC hR hnv hpa hp hdn hk hS hQ hc

theorem checkConstantValE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hcE : CoreStubsE p) (hUL : UceLookups p) : CheckConstantValE p := by
  intro hp hq hap hkp s₀ a₀ dn fe vis q cv hS hqd hqb hlps hCr F hF e hc
  exact ccvE_okT hq hp hap hkp hnv hcE hUL hF hc hS hqd hqb hlps hCr

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_ind_decl`'s error refinement**, every `indA` callee discharged: left are
`gen_rec_check` and the `indB` callees. -/
theorem cid_claim3 {p : Prog} (hkp : KnotStageProg p) (hV : ValProg p)
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
    (hnv : closedNV p _root_.L.Checker.nvFns = true) (hUL : UceLookups p) (eGrc : GenRecCheckE p)
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
    ErrClaim (checkDecl V pins fe (.indDecl block w.toNat)) a e :=
  cid_claim2 hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz P hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT hclC hfC hkP hkt
    hkr hnv (checkBasisDeclE_of hnv) (checkConstantValE_of hnv (hkp.toKnotTopProg.coreStubsE hnv) hUL) eGrc eSum
    eSC eSF eTbl eKey eClm hn hdn he hT hfold hblk hb hden hM hfB hfRc hclH hfH hclM hfM hlpd

end L.Ind
