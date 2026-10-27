import ConAgua.Verdict.IndBTbl
import ConAgua.Verdict.BlkE3
import ConAgua.Verdict.DeclValsE
import ConAgua.Verdict.IndA7
import ConAgua.Verdict.IndBClm
import ConAgua.Verdict.IndBE
import ConAgua.Verdict.IndBGrp
import ConAgua.Verdict.IndBSum4

/-!
# Part B's claims in the shapes `check_ind_decl`'s claim takes (lane `verdicts-b`, helper `fin`)

`cid_claim3` (IndA8.lean) takes the `indB` callees' claims as the generated statements of
IndBE.lean (`err_stmt`: every fuel `F ≤ 2 ^ 62`, the error of a `callE`), `CheckStructProjTableRE`
(BlkE3.lean, under `StageR`) and `GenRecCheckE` (IndA7.lean); part B proved them as `CoreSpecE`s
(`classMajors_claim`, `checkSumTele_claim`, …, `genRecCheck_claim'`). The bridges below restate
them, discharging the fuels part B's statements leave out (`0`, `1`: the calls run out of fuel).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- `check_constant_val`'s claim in the shape part B takes (`CcvE`), from `ccvE_okT`. -/
theorem ccvE_of {p : Prog} (hq : KnotStageProg p) (hp : ValProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p) (hUL : UceLookups p) :
    CcvE p :=
  fun _n hn _s₀ _a₀ _q _cv hS hqd hqb hlps hCr =>
    CoreSpecE.of_runs fun _e hc => ccvE_okT hq hp hap hkp hnv hcE hUL hn hc hS hqd hqb hlps hCr

theorem classMajorsE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hcE : CoreStubsE p) : ClassMajorsE p :=
  fun {_dn _vis _fe _env} hkp hIlpf hLC henv P s₀ a₀ pp cao cal pfo pfl ko kl bs css pfvs ks hC hA hbs hss hcss hpf hpfb
      hks hP {_pP _cssP _pfvsP _ksP} hpw hkd hsh hcssP hpfP hksP F hF _e hc =>
    CoreSpecE.of_callE (classMajors_claim hkp hIlpf hLC henv hnv hcE P F hF s₀ a₀ pp cao cal pfo pfl
      ko kl bs css pfvs ks hC hA hbs hss hcss hpf hpfb hks hP hpw hkd hsh hcssP hpfP hksP) hc

theorem checkStructProjTableRE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) :
    CheckStructProjTableRE p :=
  fun hT hApd F _hF {_dn _vis _fe} m a _T _C _lo _ll _nP _nF _rs _go _gl _cvCaw _lps _guards _cvCa hS hTH hCH hrs hnP
      hlps hlpsb hg hgb hcv hA hst hks _TP hTP _ctyP hcty _e hc =>
    CoreSpecE.of_callE (checkStructProjTable_claim (s₀ := ⟨m, Locals.init []⟩) hT hApd hnv F a hS hTH
      hCH hrs hnP hlps hlpsb hg hgb hcv hA hst hks hTP hcty) hc

theorem checkSumTeleE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) (hW : WtE p)
    (hCcv : CcvE p) : CheckSumTeleE p :=
  fun hkp {_dn _vis _fe _env} henv hV hApd hCrk h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
      hI1 hAb hcst hst s₀ a₀ cv n cvTa0 cvv cvTa hC hcv hcvb hcvs hta htab htas hA {_cvP _cvTaP} hcvP hcvTaP hws hfe
      F hF _e hc =>
    CoreSpecE.of_callE (checkSumTele_claim hkp henv hV hApd hCrk hnv hW hCcv h1 h2 h3 h4 h5 h6 h7 h8 h9
      h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hI1 hAb hcst hst F hF s₀ a₀ cv n cvTa0 cvv cvTa hC
      hcv hcvb hcvs hta htab htas hA hcvP hcvTaP hws hfe) hc

theorem checkSumCtorsE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hcE : CoreStubsE p) (hCcv : CcvE p) : CheckSumCtorsE p :=
  fun hkp {_dn _vis _fe _env} henv hV hOpf hLC hLT hApd hCrk P s₀ a₀ vis0 T lo ll nP nIdx rs isP lg cvTaw cO cL lps cvTa cs
      hC hT hrs hlps hlpsb hcv hcs hA {_env₀ _TP _lpsP _rsP _cvTaP _csP} hTP hlpsP hrsP hcvP hws hcsP hie hfe F hF _e hc =>
    CoreSpecE.of_callE (checkSumCtors_claim hkp henv hV hOpf hLC hLT hApd hCrk hnv hcE hCcv P F hF s₀
      a₀ vis0 T lo ll nP nIdx rs isP lg cvTaw cO cL lps cvTa cs hC hT hrs hlps hlpsb hcv hcs hA hTP
      hlpsP hrsP hcvP hws hcsP hie hfe) hc

theorem checkStructFieldSortsIE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hcE : CoreStubsE p) : CheckStructFieldSortsIE p := by
  intro hkp _ _ _ _ henv hLC hLT hg hpw het hsc hcfs hgo hia hcsf hftd s₀ a₀ isProp large s nP fo fl io il
    nW fvs idxArgs hC hA hfv hfvb hix hixb hs _ hsP hnW _ hfvsP hws F hF e hc
  cases F with
  | zero =>
    obtain ⟨e', h0, hk⟩ := callE_zero p _ _ s₀.mem
    rw [h0] at hc; cases hc
    exact ErrClaim.of_cls0 hk
  | succ F =>
    exact CoreSpecE.of_callE (checkStructFieldSortsI_claim hkp henv hLC hLT hnv hcE hg hpw het hsc hcfs
      hgo hia hcsf hftd F (by omega) s₀ a₀ isProp large s nP fo fl io il nW fvs idxArgs hC hA hfv hfvb
      hix hixb hs hsP hnW hfvsP hws) hc

theorem classKeyOfE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) :
    ClassKeyOfE p := by
  intro L dn fe vis s₀ a₀ nP po pl key pfvs ck hS hpf hpfb hk hP F _hF e hc
  match F with
  | 0 =>
    obtain ⟨e', h0, hk0⟩ := callE_zero p _ _ s₀.mem
    rw [h0] at hc; cases hc
    exact ErrClaim.of_cls0 hk0
  | 1 =>
    refine ErrClaim.of_cls0 (Classical.byContradiction fun hk0 => ?_)
    have hW := triple_of_callE_err (classKeyOfE_spec p L.kof 1 ⟨s₀.mem, Locals.init []⟩ nP po pl key)
      hc (Err.code_ne_of_cls hk0)
    rw [classKeyOfE.arm1] at hW
    obtain ⟨e', h0, hk1⟩ := callE_zero p "class_key_canon" [po, pl, key] s₀.mem
    rw [h0, classKeyOfE.k_class_key_canon.none] at hW
    cases hW
    exact hk0 hk1
  | k + 2 =>
    exact CoreSpecE.of_callE (classKeyOf_claim L dn fe vis hnv k s₀ a₀ nP po pl key pfvs ck hS hpf hpfb
      hk hP) hc

/-- **`gen_rec_check`'s claim in the generated shape** (`GenRecCheckE`), from `genRecCheck_claim'`
and the claims of `classes_nfs`, `target_k53_args` at every stage. -/
theorem genRecCheckE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hcE : CoreStubsE p) (hU : UceProg p) (hCcv : CcvE p)
    (hNfs : ∀ dn vis fe env, ConLeche.EnvWF env → ClassesNfsE p dn vis fe env)
    (hTka : ∀ dn vis fe env, ConLeche.EnvWF env → TkaE p dn vis fe env) : GenRecCheckE p :=
  fun hkp {_env} henv hV hApd hCrk hIlpf P {_fsR} hclR hfR s₀ a₀ {_dn _vis _fe _pp _nested _pO _pL _tO _tL _rd
      _mO _mL _cO _cL _bO _bL _bs _params _tbl _rdv _ms _cvTas _block} hC hbs hrb hpar hparb htbl hrd hms
      hcv hblk hlp hP hA hkeep hcoh hfe {_pP _paramsP _tblP _rdP _MsP _cvTasP _blockP} hsh hparP htblP
      hrdP hmsP hcvTP hblkP hMs hT hfRc F hF _e hc =>
    CoreSpecE.of_callE (genRecCheck_claim' hkp henv hV hApd hCrk hIlpf hnv hcE hU hCcv P hclR hfR F hF
      s₀ a₀ hC hbs hrb hpar hparb htbl hrd hms hcv hblk hlp hP hA hkeep hcoh hfe hsh hparP htblP hrdP
      hmsP hcvTP hblkP hMs hT hfRc (hNfs _ _ _ _ henv) (hTka _ _ _ _ henv)) hc

end L.Ind
